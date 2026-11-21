/* The image of the functions with calls or data (see scripts/rv_gen.py): the code at 0 and the
   read-only data after it aligned to 8 bytes. The pointers to the functions are the roots that
   scripts/rv_gen.py keeps, with what the functions call and read. The functions are in the order
   of their names, not of the object file, so that the order of the instances in IntxRV/Api.cpp
   does not change the images. */
SECTIONS
{
  . = 0;
  .text : { *(.text) *(SORT_BY_NAME(.text.*)) }
  . = ALIGN(8);
  .rodata : { *(.rodata .rodata.*) }
  /* ROOTS */
  /* The unwind tables of functions that clang does not mark nounwind: the code does not unwind. */
  /DISCARD/ : { *(.comment) *(.note*) *(.riscv.attributes) *(.eh_frame) }
}
