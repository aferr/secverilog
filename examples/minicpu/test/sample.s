	.file	1 "hello.c"
	.section .mdebug.abi32
	.previous
	.rdata
	.text
	.align	2
	.globl	main
	.ent	main
	.type	main, @function
main:
	.frame	$fp,32,$31		# vars= 8, regs= 2/0, args= 16, gp= 0
	.mask	0xc0000000,-4
	.fmask	0x00000000,0
	.set	noreorder
	.set	nomacro
	# Your code goes here
	# If the assembler gives error messages, delete any trailing spaces after each instruction
	
		
	#  testing lui
	lui $15, 24600	#  $15 gets 0x60180000
	lui $15, 65512	#  $15 gets 0xffe80000

	# Your code ends here
	li	$4,0			# 0x0
	jal	exit
	nop

	.set	macro
	.set	reorder
	.end	main
	.ident	"GCC: (GNU) 3.4.4 20050120 (prerelease)"
