// This file is part of www.nand2tetris.org
// and the book "The Elements of Computing Systems"
// by Nisan and Schocken, MIT Press.
// File name: projects/04/Mult.asm

// Multiplies R0 and R1 and stores the result in R2.
// (R0, R1, R2 refer to RAM[0], RAM[1], and RAM[2], respectively.)

@R2	// R2 = 0
D=0
M=D

@16000
D=A
@R0
M=D
@R1
M=D

// R0 is added to R2 until R1 reaches -1. R1 is decremented in each step
(BWHILE)
	@R1		  // R1--
	MD = M-1
	@EWHILE	  // if R1 < 0, goto EWHILE
	D;JLT
	
	@R2	      // R2 = R2 + R0
	D=M
	@R0
	D=D+M
	@R2
	M=D
	
	@BWHILE
	0;JMP
	
(EWHILE)

@EWHILE	// infinite loop
0;JMP