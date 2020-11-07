`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    17:06:18 07/28/2020 
// Design Name: 
// Module Name:    int2float 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
module int2float(d,a,p_lost);
	input [31:0] d; 					// integer
	output [31:0] a; 					// float
	output p_lost; 					// precision lost
	
	wire sign = d[31];									 // sign
	wire [31:0] f5 = sign? (~d)+1: d;					 // absolute
	wire [63:0] f4,f3,f2,f1,f0;
	wire [4:0] sa;											 // shift amount (to 1.f)
	
	assign sa[4]=|f5[31:16];
	assign f4 =sa[4] ? {16'b0, f5[31:16]} : f5 ;
	
	assign sa[3]=|f4[31:8];
	assign f3 =sa[3] ? {8'b0, f4[31:16]} : f4 ;
	
	assign sa[2]=|f3[31:4];
	assign f2 =sa[2] ? {4'b0, f3[31:16]} : f3 ;
	
	assign sa[1]=|f2[31:2];
	assign f1 =sa[1] ? {2'b0, f2[31:16]} : f2 ;
	
	assign sa[0]=|f1[31:1];
	assign f0 =sa[0] ? {1'b0, f1[31:16]} : f1 ;
	
	
	wire [22:0] fraction = nf[31:8]; 				 // f0[31] = 1, hidden bit
	wire [7:0] exponent = {3'b0, sa} + 8'b01111111 ; 		 // 0x9e = 158 = 127 + 31

	assign a = (d == 0)? 0 : {sign,exponent,fraction};
	

endmodule

module i2f (d,a,p_lost); 			// convert integer to float
	input [31:0] d; 					// integer
	output [31:0] a; 					// float
	output p_lost; 					// precision lost
	
	wire sign = d[31];									 // sign
	wire [31:0] f5 = sign? -d : d;					 // absolute
	wire [31:0] f4,f3,f2,f1,f0;
	wire [4:0] sa;											 // shift amount (to 1.f)
	
	assign sa[4] = ~|f5[31:16];						 // 16-bit 0
	assign f4 = sa[4]? {f5[15:0],16'b0} : f5;
	assign sa[3] = ~|f4[31:24]; 						 // 8-bit 0
	assign f3 = sa[3]? {f4[23:0], 8'b0} : f4;
	assign sa[2] = ~|f3[31:28];						 // 4-bit 0
	assign f2 = sa[2]? {f3[27:0], 4'b0} : f3;
	assign sa[1] = ~|f2[31:30];						 // 2-bit 0
	assign f1 = sa[1]? {f2[29:0], 2'b0} : f2;
	assign sa[0] = ~f1[31];								 // 1-bit 0
	assign f0 = sa[0]? {f1[30:0], 1'b0} : f1;
	assign p_lost = |f0[7:0];							 // not 0
	wire [22:0] fraction = f0[30:8]; 				 // f0[31] = 1, hidden bit
	wire [7:0] exponent = 8'h9e - {3'h0,sa}; 		 // 0x9e = 158 = 127 + 31
	assign a = (d == 0)? 0 : {sign,exponent,fraction};
endmodule 