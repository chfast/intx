/* The image of the functions with calls or data (see scripts/rv_gen.py): the code at 0 and the
   read-only data after it aligned to 8 bytes. The pointers to the functions are the roots that
   scripts/rv_gen.py keeps, with what the functions call and read. */
SECTIONS
{
  . = 0;
  .text : { *(.text .text.*) }
  . = ALIGN(8);
  .rodata : { *(.rodata .rodata.*) }
  /* ROOTS */
  /DISCARD/ : { *(.comment) *(.note*) *(.riscv.attributes) }
}
