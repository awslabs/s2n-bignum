/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
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

extern unsigned char rv32_code_slot[];
extern unsigned char rv32_code_slot_end[];
extern uint32_t rv32_run(uint32_t *state);

uint32_t *rv32_current_state;
uint32_t rv32_expected_break0;
uint32_t rv32_trap_cause;
uint32_t rv32_trap_value;
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

static uintptr_t semihost_call(uintptr_t operation, uintptr_t parameter)
{
    register uintptr_t a0 __asm__("a0") = operation;
    register uintptr_t a1 __asm__("a1") = parameter;

    __asm__ volatile(
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

static int semihost_readc(void)
{
    return (int)semihost_call(SEMIHOST_SYS_READC, 0);
}

static void semihost_write0(const char *text)
{
    (void)semihost_call(SEMIHOST_SYS_WRITE0, (uintptr_t)text);
}

static void semihost_exit(void)
{
    (void)semihost_call(SEMIHOST_SYS_EXIT, SEMIHOST_APPLICATION_EXIT);
    for (;;) {
        __asm__ volatile("wfi");
    }
}

static int string_equal(const char *left, const char *right)
{
    while (*left != '\0' && *left == *right) {
        left++;
        right++;
    }
    return *left == *right;
}

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

static void response_reset(void)
{
    response_length = 0;
}

static void response_character(char character)
{
    if (response_length + 1 < sizeof(response)) {
        response[response_length++] = character;
    }
}

static void response_string(const char *text)
{
    while (*text != '\0') {
        response_character(*text++);
    }
}

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

static void response_send(void)
{
    response_character('\n');
    response[response_length] = '\0';
    semihost_write0(response);
}

static void response_error(const char *reason)
{
    response_reset();
    response_string("ERROR ");
    response_string(reason);
    response_send();
}

static void store_u32_le(unsigned char *destination, uint32_t value)
{
    destination[0] = (unsigned char)value;
    destination[1] = (unsigned char)(value >> 8);
    destination[2] = (unsigned char)(value >> 16);
    destination[3] = (unsigned char)(value >> 24);
}

static int install_code(size_t code_size)
{
    size_t slot_size = (size_t)(rv32_code_slot_end - rv32_code_slot);
    size_t i;

    if (code_size + 4 > slot_size) {
        return -1;
    }
    for (i = 0; i < code_size; i++) {
        rv32_code_slot[i] = code_buffer[i];
    }
    store_u32_le(rv32_code_slot + code_size, UINT32_C(0x00100073));
    rv32_expected_break0 = (uint32_t)(uintptr_t)(rv32_code_slot + code_size);
    __asm__ volatile("fence.i" ::: "memory");
    return 0;
}

static void send_ready(void)
{
    response_reset();
    response_string("READY 1 rv32im 95");
    response_send();
}

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

static void send_trap(void)
{
    response_reset();
    response_string("TRAP mcause-");
    response_u32(rv32_trap_cause);
    response_string(" mtval-");
    response_u32(rv32_trap_value);
    response_send();
}

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
