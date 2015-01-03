#define SETH \
__asm__ __volatile__ ("addi $zero, $zero, 1"); \
__asm__ __volatile__ ("nop"); \
__asm__ __volatile__ ("nop");

#define SETL \
__asm__ __volatile__ ("addi $zero, $zero, 0"); \
__asm__ __volatile__ ("nop"); \
__asm__ __volatile__ ("nop");
