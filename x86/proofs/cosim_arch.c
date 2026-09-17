/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

#include <limits.h>
#include <stdint.h>
#include <stddef.h>
#include <string.h>

const char cosim_arch_name[] = "x86_64";
const size_t cosim_state_words = 112;

extern unsigned char cosim_capture[];

size_t cosim_arch_tail_size(void)
{
    return 5;
}

int cosim_arch_validate_code(size_t code_size)
{
    return code_size == 0 ? -1 : 0;
}

int cosim_arch_write_tail(unsigned char *tail)
{
    uintptr_t target = (uintptr_t)cosim_capture;
    uintptr_t next = (uintptr_t)tail + 5;
    uint64_t distance;
    int32_t relative;

    if (target >= next) {
        distance = (uint64_t)(target - next);
        if (distance > (uint64_t)INT32_MAX) {
            return -1;
        }
        relative = (int32_t)distance;
    } else {
        distance = (uint64_t)(next - target);
        if (distance > (uint64_t)INT32_MAX + 1) {
            return -1;
        }
        relative = distance == (uint64_t)INT32_MAX + 1
                   ? INT32_MIN : -(int32_t)distance;
    }

    tail[0] = UINT8_C(0xe9);
    memcpy(tail + 1, &relative, sizeof(relative));
    return 0;
}

void cosim_arch_signal_cleanup(void)
{
    __asm__ volatile("cld" ::: "cc");
}
