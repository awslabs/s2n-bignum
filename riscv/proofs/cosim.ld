OUTPUT_ARCH(riscv)
ENTRY(_start)

MEMORY
{
  ram (rwx) : ORIGIN = 0x80000000, LENGTH = 16M
}

SECTIONS
{
  . = ORIGIN(ram);

  .text : ALIGN(4)
  {
    KEEP(*(.init))
    *(.text .text.*)
  } > ram

  .rodata : ALIGN(4)
  {
    *(.rodata .rodata.*)
  } > ram

  .data : ALIGN(4)
  {
    *(.data .data.*)
  } > ram

  .sdata : ALIGN(4)
  {
    *(.sdata .sdata.*)
  } > ram

  PROVIDE(__global_pointer$ = . + 0x800);

  .bss (NOLOAD) : ALIGN(16)
  {
    __bss_start = .;
    *(.sbss .sbss.*)
    *(.bss .bss.*)
    *(COMMON)
    __bss_end = ALIGN(16);
  } > ram

  .cosim_code : ALIGN(4096)
  {
    KEEP(*(.cosim_code))
  } > ram

  .stack (NOLOAD) : ALIGN(16)
  {
    . += 4096;
    rv32_monitor_stack_top = .;
    . += 4096;
    rv32_trap_stack_top = .;
  } > ram

  /DISCARD/ :
  {
    *(.comment)
    *(.note*)
  }
}
