/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

#include <stdint.h>
#include <stddef.h>
#include <string.h>

const char cosim_arch_name[] = "aarch64";
const size_t cosim_state_words = 128;

extern unsigned char cosim_capture[];

size_t cosim_arch_tail_size(void)
{
    return 4;
}

int cosim_arch_validate_code(size_t code_size)
{
    return (code_size == 0 || (code_size & 3) != 0) ? -1 : 0;
}

int cosim_arch_write_tail(unsigned char *tail)
{
    uintptr_t target = (uintptr_t)cosim_capture;
    uintptr_t source = (uintptr_t)tail;
    uint64_t distance;
    int64_t immediate;
    uint32_t branch;

    if (target >= source) {
        distance = (uint64_t)(target - source);
        if ((distance & 3) != 0 || distance >= (UINT64_C(1) << 27)) {
            return -1;
        }
        immediate = (int64_t)(distance / 4);
    } else {
        distance = (uint64_t)(source - target);
        if ((distance & 3) != 0 || distance > (UINT64_C(1) << 27)) {
            return -1;
        }
        immediate = -(int64_t)(distance / 4);
    }

    branch = UINT32_C(0x14000000) |
             ((uint32_t)immediate & UINT32_C(0x03ffffff));
    memcpy(tail, &branch, sizeof(branch));
    return 0;
}

void cosim_arch_signal_cleanup(void)
{
    __asm__ volatile("" ::: "memory");
}
