/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

#define _GNU_SOURCE

#include <errno.h>
#include <inttypes.h>
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#define COSIM_MAX_STATE_WORDS 256

extern const char cosim_arch_name[];
extern const size_t cosim_state_words;
extern unsigned char cosim_code_slot[];
extern unsigned char cosim_code_slot_end[];
extern unsigned char cosim_capture[];
extern uint64_t harness(uint64_t *state);

extern size_t cosim_arch_tail_size(void);
extern int cosim_arch_validate_code(size_t code_size);
extern int cosim_arch_write_tail(unsigned char *tail);
extern void cosim_arch_signal_cleanup(void);

static uint64_t state[COSIM_MAX_STATE_WORDS];
static sigjmp_buf trap_return;
static volatile sig_atomic_t executing;
static volatile sig_atomic_t trapped_signal;

static void trap_handler(int signal_number)
{
    if (!executing) {
        _exit(128 + signal_number);
    }

    trapped_signal = signal_number;
    siglongjmp(trap_return, 1);
}

static int install_trap_handlers(void)
{
    const int signals[] = { SIGILL, SIGSEGV, SIGBUS, SIGFPE, SIGTRAP };
    struct sigaction action;
    stack_t alternate_stack;
    size_t i;

    alternate_stack.ss_sp = malloc((size_t)SIGSTKSZ * 4);
    if (alternate_stack.ss_sp == NULL) {
        return -1;
    }
    alternate_stack.ss_size = (size_t)SIGSTKSZ * 4;
    alternate_stack.ss_flags = 0;
    if (sigaltstack(&alternate_stack, NULL) != 0) {
        return -1;
    }

    memset(&action, 0, sizeof(action));
    sigemptyset(&action.sa_mask);
    action.sa_handler = trap_handler;
    action.sa_flags = SA_ONSTACK;

    for (i = 0; i < sizeof(signals) / sizeof(signals[0]); i++) {
        if (sigaction(signals[i], &action, NULL) != 0) {
            return -1;
        }
    }
    return 0;
}

static int prepare_code_slot(void)
{
    long page_size_long = sysconf(_SC_PAGESIZE);
    uintptr_t page_size;
    uintptr_t first_page;
    uintptr_t last_page;

    if (page_size_long <= 0) {
        return -1;
    }
    page_size = (uintptr_t)page_size_long;
    first_page = (uintptr_t)cosim_code_slot & ~(page_size - 1);
    last_page = ((uintptr_t)cosim_code_slot_end + page_size - 1) &
                ~(page_size - 1);

    if (mprotect((void *)first_page, last_page - first_page,
                 PROT_READ | PROT_WRITE | PROT_EXEC) != 0) {
        return -1;
    }
    return 0;
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

static int decode_code(const char *hex, unsigned char *code,
                       size_t capacity, size_t *code_size)
{
    size_t length = strlen(hex);
    size_t i;

    if (length == 0 || (length & 1) != 0 || length / 2 > capacity) {
        return -1;
    }
    for (i = 0; i < length; i += 2) {
        int high = hex_digit((unsigned char)hex[i]);
        int low = hex_digit((unsigned char)hex[i + 1]);
        if (high < 0 || low < 0) {
            return -1;
        }
        code[i / 2] = (unsigned char)((high << 4) | low);
    }
    *code_size = length / 2;
    return 0;
}

static int parse_state_word(const char *text, uint64_t *word)
{
    char *end;
    unsigned long long value;

    if (*text == '\0' || *text == '-') {
        return -1;
    }
    errno = 0;
    value = strtoull(text, &end, 10);
    if (errno != 0 || *end != '\0') {
        return -1;
    }
    *word = (uint64_t)value;
    return 0;
}

static int install_code(const unsigned char *code, size_t code_size)
{
    size_t slot_size = (size_t)(cosim_code_slot_end - cosim_code_slot);
    size_t tail_size = cosim_arch_tail_size();
    unsigned char *tail;

    if (tail_size > slot_size || code_size > slot_size - tail_size ||
        cosim_arch_validate_code(code_size) != 0) {
        return -1;
    }

    memcpy(cosim_code_slot, code, code_size);
    tail = cosim_code_slot + code_size;
    if (cosim_arch_write_tail(tail) != 0) {
        return -1;
    }
    __builtin___clear_cache((char *)cosim_code_slot,
                            (char *)(tail + tail_size));
    return 0;
}

static void print_state(void)
{
    size_t i;

    fputs("OK", stdout);
    for (i = 0; i < cosim_state_words; i++) {
        printf(" %" PRIu64, state[i]);
    }
    putchar('\n');
}

static void execute_request(char *arguments, unsigned char *code,
                            size_t code_capacity)
{
    char *save = NULL;
    char *code_hex = strtok_r(arguments, " \t\r\n", &save);
    size_t code_size;
    size_t i;

    if (code_hex == NULL ||
        decode_code(code_hex, code, code_capacity, &code_size) != 0) {
        puts("ERROR malformed-code");
        return;
    }

    for (i = 0; i < cosim_state_words; i++) {
        char *word = strtok_r(NULL, " \t\r\n", &save);
        if (word == NULL || parse_state_word(word, &state[i]) != 0) {
            puts("ERROR malformed-input-state");
            return;
        }
    }
    if (strtok_r(NULL, " \t\r\n", &save) != NULL) {
        puts("ERROR wrong-input-state-size");
        return;
    }
    if (install_code(code, code_size) != 0) {
        puts("ERROR unsupported-code");
        return;
    }

    trapped_signal = 0;
    if (sigsetjmp(trap_return, 1) == 0) {
        executing = 1;
        (void)harness(state);
        executing = 0;
        print_state();
    } else {
        executing = 0;
        cosim_arch_signal_cleanup();
        printf("TRAP signal-%d\n", (int)trapped_signal);
    }
}

int main(void)
{
    size_t code_capacity;
    unsigned char *code;
    char *line = NULL;
    size_t line_capacity = 0;

    if (cosim_state_words > COSIM_MAX_STATE_WORDS ||
        install_trap_handlers() != 0 || prepare_code_slot() != 0) {
        fprintf(stderr, "cosim runner initialization failed: %s\n",
                strerror(errno));
        return 2;
    }

    code_capacity = (size_t)(cosim_code_slot_end - cosim_code_slot);
    code = malloc(code_capacity);
    if (code == NULL) {
        fputs("cosim runner code allocation failed\n", stderr);
        return 2;
    }

    setvbuf(stdout, NULL, _IOLBF, 0);
    printf("READY 1 %s %zu slot-size=%zu\n",
           cosim_arch_name, cosim_state_words, code_capacity);

    while (getline(&line, &line_capacity, stdin) >= 0) {
        char *save = NULL;
        char *command = strtok_r(line, " \t\r\n", &save);

        if (command == NULL) {
            puts("ERROR empty-command");
        } else if (strcmp(command, "QUIT") == 0) {
            break;
        } else if (strcmp(command, "RUN") == 0) {
            execute_request(save, code, code_capacity);
        } else {
            puts("ERROR unknown-command");
        }
    }

    free(line);
    free(code);
    return 0;
}
