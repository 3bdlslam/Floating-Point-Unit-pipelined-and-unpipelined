`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    23:01:26 07/27/2020 
// Design Name: 
// Module Name:    float2int 
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
module float2int(a,d,p_lost,denorm,invalid);
	input [31:0] a; 					// float
	output [31:0] d; 					// integer
	output p_lost; 					// precision lost
	output denorm; 					// denormalized
	output invalid; 					// inf,nan,out_of_range

	reg [31:0] d; 						// will be combinational
	reg p_lost; 						// will be combinational
	reg invalid; 						// will be combinational
	
	wire hidden_bit = |a[30:23]; 						// hidden bit =0 when its the representation(power=-127=b00000000) of 0 and 1 otherwise
	wire frac_is_not_0 = |a[22:0];
	assign denorm = ~hidden_bit & frac_is_not_0; // mean it exponent is -127 this means no nead for clculate 
	wire is_zero = ~hidden_bit & ~frac_is_not_0;
	wire sign = a[31]; 																// sign of floating point num

	wire [8:0] shift_right_bits = 9'd158 - {1'b0,a[30:23]}; 				// shift right amount =127 + 31 - exp  
	                                                                       // 9 bit used to detect if it became -ve
	wire [55:0] frac0 = {exp_is_not_0,a[22:0],32'h0}; 						// 32 + 24 = 56 bits  (finaly we take most 32-bits)
																								 // we extend it to detect the precesion loss if we neglect a fraction(down casting)
	wire sh_out;																// shift
	right_shifter56 sh1 (frac0,sh_out,shift_right_bits[4:0]);	//mux
	wire [55:0] f_abs = ($signed(shift_right_bits) > 9'd32)? 			
								frac0 >> 6'd32 : sh_out;
	wire lost_bits = |f_abs[23:0]; 												// if != 0, p_lost = 1 
	wire [31:0] int32 = sign? ~f_abs[55:24] + 32'd1 : f_abs[55:24];   //if -ve clc 2's complement

	always @ * begin
		if (denorm) begin 									  //denormalized (e=00000000 power=-127 and  f !=000...00)
			p_lost = 1;													// so output is already =0
			invalid = 0;
			d = 32'h00000000;
		end else begin 								  // not denormalized
			if (shift_right_bits[8]) begin 		  // too big  (this mead the subtraction result is -ve 
				p_lost = 0;										// and that means it should shifted to left and lose mist bits so result is invalid )
				invalid = 1;
				d = 32'h80000000;
			end else begin										  // shift right
				if (shift_right_bits[7:0] > 8'h1f) begin // too small (less than 1 or exact 0)
					if (is_zero) p_lost = 0;						
					else p_lost = 1;
					invalid = 0;
					d = 32'h00000000;
				end else begin
					if (sign != int32[31]) begin 				// out of range (if the sign changed this means overflow=invalid)
						p_lost = 0;
						invalid = 1;
						d = 32'h80000000;
					end else begin 								// normal case
						if (lost_bits) p_lost = 1;				   //if theire are fraction part will be neglected (down cast)
						else p_lost = 0;
						invalid = 0;
						d = int32;
					end
				end
			end
		end
	end

endmodule

module right_shifter56(unshifted,shifted,SA);
input [55:0] unshifted;
input [4:0] SA;
output [55:0] shifted;

wire [55:0] t0 = SA[4]?{16'b0 ,unshifted[55:16]}:unshifted;
wire [55:0] t1 = SA[3]?{8'b0 ,t0[55:8]}:t0;
wire [55:0] t2 = SA[2]?{4'b0 ,t1[55:4]}:t1;
wire [55:0] t3 = SA[1]?{2'b0 ,t2[55:2]}:t2;
wire [55:0] t4 = SA[0]?{1'b0 ,t3[55:1]}:t3;

assign shifted =t4;
endmodule 

module f2i (a,d,p_lost,denorm,invalid); // convert float to integer
	input [31:0] a; 					// float
	output [31:0] d; 					// integer
	output p_lost; 					// precision lost
	output denorm; 					// denormalized
	output invalid; 					// inf,nan,out_of_range

	reg [31:0] d; 						// will be combinational
	reg p_lost; 						// will be combinational
	reg invalid; 						// will be combinational
	wire hidden_bit = |a[30:23]; 													// hidden bit
	wire frac_is_not_0 = |a[22:0];
	assign denorm = ~hidden_bit & frac_is_not_0;
	wire is_zero = ~hidden_bit & ~frac_is_not_0;
	wire sign = a[31]; 																// sign
	wire [8:0] shift_right_bits = 9'd158 - {1'b0,a[30:23]}; 				// 127 + 31
	wire [55:0] frac0 = {hidden_bit,a[22:0],32'h0}; 						// 32 + 24 = 56 bits
	wire [55:0] f_abs = ($signed(shift_right_bits) > 9'd32)? 			// shift
								frac0 >> 6'd32 : frac0 >> shift_right_bits;
	wire lost_bits = |f_abs[23:0]; 												// if != 0, p_lost = 1
	wire [31:0] int32 = sign? ~f_abs[55:24] + 32'd1 : f_abs[55:24];

	always @ * begin
		if (denorm) begin 									  //denormalized
			p_lost = 1;
			invalid = 0;
			d = 32'h00000000;
		end else begin 										  // not denormalized
			if (shift_right_bits[8]) begin 				  // too big
				p_lost = 0;
				invalid = 1;
				d = 32'h80000000;
			end else begin										  // shift right
				if (shift_right_bits[7:0] > 8'h1f) begin // too small
					if (is_zero) p_lost = 0;
					else p_lost = 1;
					invalid = 0;
					d = 32'h00000000;
				end else begin
					if (sign != int32[31]) begin 				// out of range 
						p_lost = 0;
						invalid = 1;
						d = 32'h80000000;
					end else begin 								// normal case
						if (lost_bits) p_lost = 1;
						else p_lost = 0;
						invalid = 0;
						d = int32;
					end
				end
			end
		end
	end
endmodule 
