// Tag fields
`define D_BO_WIDTH	2


//---------------------------------------------------------------------------
//
// Data Cache
//
//---------------------------------------------------------------------------
// If you change the number of words in a $ line you must change
// *all* of the following defines, as well as the memory system
// in mips.v
`define D_WO_WIDTH	3
`define D_MAX_OFFSET	7
`define MAX_OFFSET	7

`define D_INDEX_WIDTH	8
`define D_TAG_WIDTH	19

`define D_BO		1:0
`define D_WO		4:2
`define D_INDEX 	12:5
`define D_TAG		31:13

// State fields
`define D_VALID		0
`define D_DIRTY		1


//---------------------------------------------------------------------------
//
// Instruction Cache
//
//---------------------------------------------------------------------------
// If you change the number of words in a $ line you must change
// *all* of the following defines, as well as the memory system
// in mips.v
`define I_WO_WIDTH	3
`define I_MAX_OFFSET	7

`define I_INDEX_WIDTH	8
`define I_TAG_WIDTH	19

`define I_BO		1:0
`define I_WO		4:2
`define I_INDEX 	12:5
`define I_TAG		31:13

// State fields
`define I_VALID		0
