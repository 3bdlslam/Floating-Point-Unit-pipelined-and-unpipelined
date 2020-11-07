`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/06/2020 02:02:02 PM
// Design Name: 
// Module Name: fsqrt_newton
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module fsqrt_newton (d,rm,fsqrt,ena,clk,clrn, s,busy,stall,count,reg_x);
    input clk, clrn; // clock and reset
    input [31:0] d; // fp s = root(d)
    input [1:0] rm; // round mode
    input fsqrt; // ID stage: fsqrt = i_fsqrt
    input ena; // enable
    output [31:0] s; // fp output
    output [25:0] reg_x; // x_i
    output [4:0] count; // for iteration control
    output busy; // for generating stall
    output stall; // for pipeline stall
    
    parameter ZERO = 32'h00000000;
    parameter INF = 32'h7f800000;
    parameter NaN = 32'h7fc00000;
    
    wire d_expo_is_00 = ~|d[30:23]; // d_expo = 00
    wire d_expo_is_ff = &d[30:23]; // d_expo = ff
    wire d_frac_is_00 = ~|d[22:0]; // d_frac = 00
    wire sign = d[31];
    // e_q = (e_d >> 1) + 63 + (e_d % 2)
    wire [7:0] exp_8 = {1'b0,d[30:24]} + 8'd63 + d[23]; // normalized
    // = 0 + 63 + 0 = 63 // denormalized
    // d_f24 = denormalized? .f_d,0 : .1,f_d // shifted 1 bit
    wire [23:0] d_f24 = d_expo_is_00? {d[22:0],1'b0} : {1'b1,d[22:0]};
    // tmp = e_d is odd? shift one more bit : 1 bit, no change
    wire [23:0] d_temp24 = d[23]? {1'b0,d_f24[23:1]} : d_f24;
    wire [23:0] d_frac24; // .1xx...x or .01x...x for denormalized number
    wire [4:0] shamt_d; // shift amount, even number
    shift_even_bits shift_d (d_temp24,d_frac24,shamt_d);
    // denormalized: e_q = 63 - shamt_d / 2
    // normalized: e_q = exp_8 - 0
    wire [7:0] exp0 = exp_8 - {4'h0,shamt_d[4:1]};
    reg e1_sign,e1_e00,e1_eff,e1_f00;
    reg e2_sign,e2_e00,e2_eff,e2_f00;
    reg e3_sign,e3_e00,e3_eff,e3_f00;
    reg [1:0] e1_rm,e2_rm,e3_rm;
    reg [7:0] e1_exp,e2_exp,e3_exp;

    always @ (negedge clrn or posedge clk)
        if (!clrn) begin // 3 pipeline registers: reg_e1, reg_e2, and reg_e3
            // reg_e1 reg_e2 reg_e3
            e1_sign <= 0; e2_sign <= 0; e3_sign <= 0;
            e1_rm <= 0; e2_rm <= 0; e3_rm <= 0;
            e1_exp <= 0; e2_exp <= 0; e3_exp <= 0;
            e1_e00 <= 0; e2_e00 <= 0; e3_e00 <= 0;
            e1_eff <= 0; e2_eff <= 0; e3_eff <= 0;
            e1_f00 <= 0; e2_f00 <= 0; e3_f00 <= 0;
        end else if (ena) begin
            e1_sign <= sign; e2_sign <= e1_sign; e3_sign <= e2_sign;
            e1_rm <= rm; e2_rm <= e1_rm; e3_rm <= e2_rm;
            e1_exp <= exp0; e2_exp <= e1_exp; e3_exp <= e2_exp;
            e1_e00 <= d_expo_is_00; e2_e00 <= e1_e00; e3_e00 <= e2_e00;
            e1_eff <= d_expo_is_ff; e2_eff <= e1_eff; e3_eff <= e2_eff;
            e1_f00 <= d_frac_is_00; e2_f00 <= e1_f00; e3_f00 <= e2_f00;
        end
    
    wire [31:0] frac0; // root = 1.xxxx...x
    root_newton24 frac_newton (d_frac24,fsqrt,ena,clk,clrn,
    frac0,busy,count,reg_x,stall);
    wire [26:0] frac = {frac0[31:6],|frac0[5:0]}; // sticky
    wire frac_plus_1 =
    ~e3_rm[1] & ~e3_rm[0] & frac[3] & frac[2] & ~frac[1] & ~frac[0] |
    ~e3_rm[1] & ~e3_rm[0] & frac[2] & (frac[1] | frac[0]) |
    ~e3_rm[1] & e3_rm[0] & (frac[2] | frac[1] | frac[0]) & e3_sign |
    e3_rm[1] & ~e3_rm[0] & (frac[2] | frac[1] | frac[0]) & ~e3_sign;
    wire [24:0] frac_rnd = {1'b0,frac[26:3]} + frac_plus_1;
    wire [7:0] expo_new = frac_rnd[24]? e3_exp + 8'h1 : e3_exp;
    wire [22:0] frac_new = frac_rnd[24]? frac_rnd[23:1]: frac_rnd[22:0];
    assign s = final_result(e3_sign,e3_e00,e3_eff,e3_f00,
    {e3_sign,expo_new,frac_new});
    
    function [31:0] final_result;
        input d_sign,d_e00,d_eff,d_f00;
        input [31:0] calc;
        casex ({d_sign,d_e00,d_eff,d_f00})
            4'b1xxx : final_result = NaN; // -
            4'b000x : final_result = calc; // nor
            4'b0100 : final_result = calc; // den
            4'b0010 : final_result = NaN; // nan
            4'b0011 : final_result = INF; // inf
            default : final_result = ZERO; // 0
        endcase
    endfunction
endmodule

module shift_even_bits (a,b,sa); // shift even bits until msb is 1x or 01
    input [23:0] a; // shift a = xxx...x by even bits
    output [23:0] b; // to b = 1xx...x or 01x...x
    output [4:0] sa; // shift amount, even number
    
    wire [23:0] a5,a4,a3,a2,a1;
    assign a5 = a;
    assign sa[4] = ~|a5[23:08]; // 16-bit 0
    assign a4 = sa[4]? {a5[07:00],16'b0} : a5;
    assign sa[3] = ~|a4[23:16]; // 8-bit 0
    assign a3 = sa[3]? {a4[15:00], 8'b0} : a4;
    assign sa[2] = ~|a3[23:20]; // 4-bit 0
    assign a2 = sa[2]? {a3[19:00], 4'b0} : a3;
    assign sa[1] = ~|a2[23:22]; // 2-bit 0
    assign a1 = sa[1]? {a2[21:00], 2'b0} : a2;
    assign sa[0] = 0;
    assign b = a1;
endmodule

module root_newton24 (d,fsqrt,ena,clk,clrn,q,busy,count,reg_x,stall);
    input [23:0] d; // radicand: .1xx...x .01x...x
    input fsqrt; // ID stage: fsqrt = i_fsqrt
    input clk, clrn; // clock and reset
    input ena; // enable, save partial product
    output [31:0] q; // root: .1xxx...x
    output busy; // cannot receive new div
    output stall; // stall to save result
    output [4:0] count; // for sim test only
    output [25:0] reg_x; // for sim test only 01.xx...x
    reg [31:0] q; // root: .1xxx...x
    reg [23:0] reg_d; // 24-bit: .xxxx...xx
    reg [25:0] reg_x; // 26-bit: xx.1xxx...xx
    reg [4:0] count; // 3 iterations * 7 cycles
    reg busy; // cannot receive new fsqrt
    wire [7:0] x0 = rom(d[23:19]); // x0: from rom table
    wire [51:0] x_2,x2d,x52; // xxxx.xxxxx...x
    
    always @ (posedge clk or negedge clrn) begin
        if (!clrn) begin
            count <= 0;
            busy <= 0;
            reg_x <= 0;
        end else begin
            if (fsqrt & (count == 0)) begin // do once only
                count <= 5'b1; // set count
                busy <= 1'b1; // set to busy
            end else begin // 3 iterations
                if (count == 5'h01) begin
                    reg_x <= {2'b1,x0,16'b0}; // 01.xxxx0...0
                    reg_d <= d; // .1xxxx...x
                end
                if (count != 0) count <= count + 5'b1; // count++
                    if (count == 5'h15) busy <= 0; // ready for next
                        if (count == 5'h16) count <= 0; // reset count
                            if ((count == 5'h08) || // save result of 1st iteration
                                (count == 5'h0f) || // save result of 2nd iteration
                                (count == 5'h16)) // no need to save here actually
                                reg_x <= x52[50:25]; // /2 = xx.xxxxx...x
            end
        end
    end
    
    assign stall = fsqrt & (count == 0) | busy;
    // wallace_26x26_product (a, b, z);
    wallace_26x26_product x2 (reg_x,reg_x,x_2); // xi(3-xi*xi*d)/2
    wallace_24x28_product xd (reg_d,x_2[51:24],x2d);
    wire [25:0] b26 = 26'h3000000 - x2d[49:24]; // xx.xxxxx...x
    wallace_26x26_product xip1 (reg_x,b26,x52);
    reg [25:0] reg_de_x; // pipeline register in between id and e1, x
    reg [23:0] reg_de_d; // pipeline register in between id and e1, d
    wire [49:0] m_s; // sum: 41+8= 49-bit
    wire [49:8] m_c; // carry: 42-bit
    // wallace_24x26 (a, b, x, y, z);
    wallace_24x26 wt (reg_de_d,reg_de_x,m_s[49:8],m_c,m_s[7:0]); //d*x
    reg [49:0] a_s; // pipeline register in between e1 and e2, sum
    reg [49:8] a_c; // pipeline register in between e1 and e2, carry
    wire [49:0] d_x = {1'b0,a_s} + {a_c,8'b0}; // 0x.xxxxx...x
    wire [31:0] e2p = {d_x[47:17],|d_x[16:0]}; // sticky
    
    always @ (negedge clrn or posedge clk)
        if (!clrn) begin // pipeline registers
            reg_de_x <= 0; reg_de_d <= 0; // id-e1
            a_s <= 0; a_c <= 0; // e1-e2
            q <= 0; // e2-e3
        end else if (ena) begin // x52[50:25]: the result of 3rd iteration
            reg_de_x <= x52[50:25]; reg_de_d <= reg_d; // id-e1
            a_s <= m_s; a_c <= m_c; // e1-e2
            q <= e2p; // e2-e3
        end
    
    function [7:0] rom; // a rom table: 1/d ̂ {1/2}
        input [4:0] d;
        case (d)
            5'h08: rom = 8'hff; 5'h09: rom = 8'he1;
            5'h0a: rom = 8'hc7; 5'h0b: rom = 8'hb1;
            5'h0c: rom = 8'h9e; 5'h0d: rom = 8'h9e;
            5'h0e: rom = 8'h7f; 5'h0f: rom = 8'h72;
            5'h10: rom = 8'h66; 5'h11: rom = 8'h5b;
            5'h12: rom = 8'h51; 5'h13: rom = 8'h48;
            5'h14: rom = 8'h3f; 5'h15: rom = 8'h37;
            5'h16: rom = 8'h30; 5'h17: rom = 8'h29;
            5'h18: rom = 8'h23; 5'h19: rom = 8'h1d;
            5'h1a: rom = 8'h17; 5'h1b: rom = 8'h12;
            5'h1c: rom = 8'h0d; 5'h1d: rom = 8'h08;
            5'h1e: rom = 8'h04; 5'h1f: rom = 8'h00;
            default: rom = 8'hff; // 0 - 7: not be accessed
        endcase
    endfunction
endmodule

module wallace_24x28_product (a,b,z); // 24*28 wt product
    input [23:00] a; // 24 bits
    input [27:00] b; // 28 bits
    output [51:00] z; // product
    
    wire [51:08] x; // sum high
    wire [51:08] y; // carry high
    wire [51:08] z_high; // product high
    wire [07:00] z_low; // product low
    
    wallace_24x28 wt_partial (a, b, x, y, z_low); // partial product
    assign z_high = x + y;
    assign z = {z_high,z_low}; // product
endmodule