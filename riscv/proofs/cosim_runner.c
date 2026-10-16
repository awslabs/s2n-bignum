/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * Persistent RV32IM cosimulation monitor for the HOL-side sematest driver.
 *
 * This program is a persistent instruction-execution backend for the RV32IM
 * cosimulation tests. It receives one test case at a time over standard
 * input, executes the supplied straight-line instruction sequence from the
 * supplied machine state, and returns the resulting machine state over
 * standard output.
 *
 * The line protocol is:
 *
 *   READY 1 rv32im 95
 *     Sent once at startup. The 95 state words are x0, x1, x3..x31 followed
 *     by 64 words of scratch memory. That memory is the private 256-byte
 *     buffer through which the HOL-side test harness exercises loads and
 *     stores. SP is not transported.
 *
 *   RUN <hex instruction bytes> <state-word> ...
 *     Loads one straight-line instruction sequence into the private code
 *     slot, initializes the transported registers and scratch-memory words,
 *     sets SP to the private scratch buffer, and executes until the monitor
 *     trap.
 *
 *   OK <state-word> ...
 *     Returned when execution reaches the expected trap. The payload has the
 *     same 95-word shape as the RUN input.
 *
 *   TRAP mcause-<mcause> mtval-<mtval>
 *     Returned for an unexpected trap while executing the test case.
 *
 *   ERROR <message>
 *     Returned for malformed input or internal monitor failures.
 *
 *   QUIT
 *     Requests clean termination through semihosting.
 *
 * The current implementation runs freestanding under `qemu-system-riscv32`.
 * It uses semihosting for stdin/stdout, keeps one 256-byte scratch buffer
 * and one code slot private to the backend, and fixes SP to that scratch
 * buffer rather than transporting it through the protocol.
 */

#include <stddef.h>
#include <stdint.h>

#define RV32_STATE_WORDS 95
#define RV32_SCRATCH_WORDS 64
#define RV32_LINE_SIZE 4096
#define RV32_RESPONSE_SIZE 4096

#define SEMIHOST_SYS_WRITE0 0x04
#define SEMIHOST_SYS_READC 0x07
#define SEMIHOST_SYS_EXIT 0x18
#define SEMIHOST_APPLICATION_EXIT 0x20026

/* Linker-defined start of the executable code slot used for injected tests. */
extern unsigned char rv32_code_slot[];
/* Linker-defined end of the executable code slot used for injected tests. */
extern unsigned char rv32_code_slot_end[];
/* Assembly entry point that loads state, runs the test code, and traps back. */
extern uint32_t rv32_run(uint32_t *state);

/* Current transport-state array passed to and updated by the trap handler. */
uint32_t *rv32_current_state;
/* Address of the synthetic terminating EBREAK appended after the test code. */
uint32_t rv32_expected_break0;
/* Trap cause reported by an unexpected exception while running test code. */
uint32_t rv32_trap_cause;
/* Trap value reported by an unexpected exception while running test code. */
uint32_t rv32_trap_value;
/* Zero for the expected terminating trap, nonzero for an unexpected trap. */
uint32_t rv32_trap_status;

/*
 * State words contain x0, x1, x3--x31 followed by 64 scratch words.
 * SP is private to the monitor and points at rv32_scratch.
 */
static uint32_t state[RV32_STATE_WORDS];
uint32_t rv32_scratch[RV32_SCRATCH_WORDS] __attribute__((aligned(16)));
static unsigned char code_buffer[512];
static char input_line[RV32_LINE_SIZE];
static char response[RV32_RESPONSE_SIZE];
static size_t response_length;

/*
 * Issue one semihosting call through the standard three-instruction trap
 * sequence recognized by QEMU/OpenOCD-style RISC-V semihosting stubs.
 *
 * The call number is passed in `a0` and the argument block pointer in `a1`.
 * The surrounding shifts on `x0` are marker instructions: together with the
 * middle `ebreak`, they distinguish a host semihosting request from an
 * ordinary breakpoint trap taken by the test program itself.
 */
static uintptr_t semihost_call(uintptr_t operation, uintptr_t parameter)
{
    register uintptr_t a0 __asm__("a0") = operation;
    register uintptr_t a1 __asm__("a1") = parameter;

    __asm__ volatile(
        /* Semihosting marker sequence: slli x0,x0,0x1f; ebreak;
           srai x0,x0,0x7. */
        ".option push\n"
        ".option norvc\n"
        "slli x0,x0,0x1f\n"
        "ebreak\n"
        "srai x0,x0,0x7\n"
        ".option pop\n"
        : "+r"(a0)
        : "r"(a1)
        : "memory");
    return a0;
}

/* Read one character from semihosted stdin. */
static int semihost_readc(void)
{
    return (int)semihost_call(SEMIHOST_SYS_READC, 0);
}

/* Write one NUL-terminated string to semihosted stdout. */
static void semihost_write0(const char *text)
{
    (void)semihost_call(SEMIHOST_SYS_WRITE0, (uintptr_t)text);
}

/* Terminate the monitor through semihosting and stop if it returns. */
static void semihost_exit(void)
{
    (void)semihost_call(SEMIHOST_SYS_EXIT, SEMIHOST_APPLICATION_EXIT);
    for (;;) {
        __asm__ volatile("wfi");
    }
}

/* Compare two NUL-terminated strings for exact equality. */
static int string_equal(const char *left, const char *right)
{
    while (*left != '\0' && *left == *right) {
        left++;
        right++;
    }
    return *left == *right;
}

/* Decode one hexadecimal digit, or return -1 for invalid input. */
static int hex_digit(int character)
{
    if (character >= '0' && character <= '9') {
        return character - '0';
    }
    if (character >= 'a' && character <= 'f') {
        return character - 'a' + 10;
    }
    if (character >= 'A' && character <= 'F') {
        return character - 'A' + 10;
    }
    return -1;
}

/* Read one input line into `input_line`, stripping CR and trailing LF. */
static int read_line(void)
{
    size_t length = 0;

    for (;;) {
        int character = semihost_readc();
        if (character < 0) {
            return -1;
        }
        if (character == '\r') {
            continue;
        }
        if (character == '\n') {
            input_line[length] = '\0';
            return 0;
        }
        if (length + 1 >= sizeof(input_line)) {
            input_line[0] = '\0';
            return -1;
        }
        input_line[length++] = (char)character;
    }
}

/* Split the next space-delimited token in place from `cursor`. */
static char *next_token(char **cursor)
{
    char *token;

    while (**cursor == ' ' || **cursor == '\t') {
        (*cursor)++;
    }
    if (**cursor == '\0') {
        return NULL;
    }
    token = *cursor;
    while (**cursor != '\0' && **cursor != ' ' && **cursor != '\t') {
        (*cursor)++;
    }
    if (**cursor != '\0') {
        **cursor = '\0';
        (*cursor)++;
    }
    return token;
}

/* Parse one unsigned decimal word into a 32-bit state value. */
static int parse_u32(const char *text, uint32_t *result)
{
    uint32_t value = 0;

    if (*text == '\0') {
        return -1;
    }
    while (*text != '\0') {
        uint32_t digit;
        if (*text < '0' || *text > '9') {
            return -1;
        }
        digit = (uint32_t)(*text - '0');
        if (value > (UINT32_MAX - digit) / 10) {
            return -1;
        }
        value = value * 10 + digit;
        text++;
    }
    *result = value;
    return 0;
}

/* Decode the hex instruction payload into the private code buffer. */
static int decode_code(const char *hex, size_t *code_size)
{
    size_t length = 0;
    size_t i;

    while (hex[length] != '\0') {
        length++;
    }
    if (length == 0 || (length & 7) != 0 ||
        length / 2 > sizeof(code_buffer)) {
        return -1;
    }
    for (i = 0; i < length; i += 2) {
        int high = hex_digit((unsigned char)hex[i]);
        int low = hex_digit((unsigned char)hex[i + 1]);
        if (high < 0 || low < 0) {
            return -1;
        }
        code_buffer[i / 2] = (unsigned char)((high << 4) | low);
    }
    *code_size = length / 2;
    return 0;
}

/* Start a fresh output line in `response`. */
static void response_reset(void)
{
    response_length = 0;
}

/* Append one character if the response buffer still has room. */
static void response_character(char character)
{
    if (response_length + 1 < sizeof(response)) {
        response[response_length++] = character;
    }
}

/* Append one NUL-terminated string to the response buffer. */
static void response_string(const char *text)
{
    while (*text != '\0') {
        response_character(*text++);
    }
}

/* Append one 32-bit word in unsigned decimal form. */
static void response_u32(uint32_t value)
{
    char digits[10];
    size_t count = 0;

    do {
        digits[count++] = (char)('0' + value % 10);
        value /= 10;
    } while (value != 0);
    while (count != 0) {
        response_character(digits[--count]);
    }
}

/* Finish the current response line and write it to stdout. */
static void response_send(void)
{
    response_character('\n');
    response[response_length] = '\0';
    semihost_write0(response);
}

/* Return one protocol ERROR line with the supplied reason token. */
static void response_error(const char *reason)
{
    response_reset();
    response_string("ERROR ");
    response_string(reason);
    response_send();
}

/* Store one word in little-endian byte order. */
static void store_u32_le(unsigned char *destination, uint32_t value)
{
    destination[0] = (unsigned char)value;
    destination[1] = (unsigned char)(value >> 8);
    destination[2] = (unsigned char)(value >> 16);
    destination[3] = (unsigned char)(value >> 24);
}

/* Install the decoded code bytes and append the terminating EBREAK. */
static int install_code(size_t code_size)
{
    size_t slot_size = (size_t)(rv32_code_slot_end - rv32_code_slot);
    size_t i;

    /* Reserve one extra word for the synthetic terminating `ebreak`. */
    if (code_size + 4 > slot_size) {
        return -1;
    }
    for (i = 0; i < code_size; i++) {
        rv32_code_slot[i] = code_buffer[i];
    }
    /* Append one terminating `ebreak` so the injected sequence returns to the
       monitor through the expected trap path after its last instruction. */
    store_u32_le(rv32_code_slot + code_size, UINT32_C(0x00100073));
    /* Remember the PC of that synthetic `ebreak` so the trap handler can
       recognize the expected end-of-sequence trap. */
    rv32_expected_break0 = (uint32_t)(uintptr_t)(rv32_code_slot + code_size);
    /* The monitor has just rewritten executable bytes in the code slot. Make
       those stores visible to instruction fetch before `rv32_run` enters it. */
    __asm__ volatile("fence.i" ::: "memory");
    return 0;
}

/* Advertise the protocol version, architecture, and state size. */
static void send_ready(void)
{
    response_reset();
    response_string("READY 1 rv32im 95");
    response_send();
}

/* Return the post-execution state in protocol order. */
static void send_state(void)
{
    size_t i;

    response_reset();
    response_string("OK");
    for (i = 0; i < RV32_STATE_WORDS; i++) {
        response_character(' ');
        response_u32(state[i]);
    }
    response_send();
}

/* Return the trap metadata for an unexpected backend exception. */
static void send_trap(void)
{
    response_reset();
    response_string("TRAP mcause-");
    response_u32(rv32_trap_cause);
    response_string(" mtval-");
    response_u32(rv32_trap_value);
    response_send();
}

/* Parse, execute, and answer one RUN request. */
static void execute_request(char *cursor)
{
    char *code = next_token(&cursor);
    size_t code_size;
    size_t i;

    if (code == NULL || decode_code(code, &code_size) != 0) {
        response_error("malformed-code");
        return;
    }
    for (i = 0; i < RV32_STATE_WORDS; i++) {
        char *word = next_token(&cursor);
        if (word == NULL || parse_u32(word, &state[i]) != 0) {
            response_error("malformed-input-state");
            return;
        }
    }
    if (next_token(&cursor) != NULL) {
        response_error("wrong-input-state-size");
        return;
    }
    if (state[0] != 0) {
        response_error("invalid-initial-state");
        return;
    }
    if (install_code(code_size) != 0) {
        response_error("unsupported-code");
        return;
    }

    for (i = 0; i < RV32_SCRATCH_WORDS; i++) {
        rv32_scratch[i] = state[31 + i];
    }
    rv32_current_state = state;
    rv32_trap_status = rv32_run(state);
    for (i = 0; i < RV32_SCRATCH_WORDS; i++) {
        state[31 + i] = rv32_scratch[i];
    }

    if (rv32_trap_status == 0) {
        send_state();
    } else {
        send_trap();
    }
}

/* Serve the line protocol until EOF or QUIT terminates the monitor. */
int main(void)
{
    send_ready();
    for (;;) {
        char *cursor;
        char *command;

        if (read_line() != 0) {
            semihost_exit();
        }
        cursor = input_line;
        command = next_token(&cursor);
        if (command == NULL) {
            response_error("empty-command");
        } else if (string_equal(command, "QUIT")) {
            semihost_exit();
        } else if (string_equal(command, "RUN")) {
            execute_request(cursor);
        } else {
            response_error("unknown-command");
        }
    }
}
