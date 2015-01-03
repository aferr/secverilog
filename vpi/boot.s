.text
.=0
.set noreorder
.set noat
	lui     $28,0xdead
	ori     $28,$gp,0xbeef
	lui     $1,0xdead
	ori     $1,$at,0xbeef
	li      $2,0
	li      $3,0
	li      $4,0
	li      $5,0
	li      $6,0
	li      $7,0
	li      $8,0
	li      $9,0
	li      $10,0
	li      $11,0
	li      $12,0
	li      $13,0
	li      $14,0
	li      $15,0
	li      $16,0
	li      $17,0
	li      $18,0
	li      $19,0
	li      $20,0
	li      $21,0
	li      $22,0
	li      $23,0
	li      $24,0
	li      $25,0
	li      $26,0
	li      $27,0
	lui     $29,0x7fff
	ori     $29,$sp,0xf000
	li      $30,0
	li      $31,0
	sw	$0, 0($sp)
	sw	$0, 4($sp)
	sw	$0, 8($sp)
	jr      $1
	li      $0,0
