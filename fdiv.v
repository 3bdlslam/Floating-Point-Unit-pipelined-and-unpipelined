`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/06/2020 02:02:02 PM
// Design Name: 
// Module Name: fdiv_newton
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

module fdiv_newton (a,b,rm,fdiv,ena,clk,clrn, s,busy,stall,count,reg_x);
    input [31:0] a,b; // fps=a/b
    input [1:0] rm; // round mode
    input fdiv; // ID stage: fdiv = i_fdiv
    input ena; // enable
    input clk, clrn; // clock and reset
    
    output [31:0] s; // fp output
    output [25:0] reg_x; // x_i
    output [4:0] count; // for iteration control
    output busy; // for generating stall
    output stall; // for pipeline stall
    
    parameter ZERO = 31'h00000000;
    parameter INF = 31'h7f800000;
    parameter NaN = 31'h7fc00000;
    parameter MAX = 31'h7f7fffff;
    
    wire a_expo_is_00 = ~|a[30:23]; // a_expo = 00
    wire b_expo_is_00 = ~|b[30:23]; // b_expo = 00
    wire a_expo_is_ff = &a[30:23]; // a_expo = ff
    wire b_expo_is_ff = &b[30:23]; // b_expo = ff
    wire a_frac_is_00 = ~|a[22:0]; // a_frac = 00
    wire b_frac_is_00 = ~|b[22:0]; // b_frac = 00
    wire sign = a[31] ^ b[31];
    wire [9:0] exp_10 = {2'h0,a[30:23]} - {2'h0,b[30:23]} + 10'h7f;
    wire [23:0] a_temp24 = a_expo_is_00? {a[22:0],1'b0} : {1'b1,a[22:0]};
    wire [23:0] b_temp24 = b_expo_is_00? {b[22:0],1'b0} : {1'b1,b[22:0]};
    wire [23:0] a_frac24,b_frac24; // to 1xx...x for denormalized number
    wire [4:0] shamt_a,shamt_b; // how many bits shifted
    shift_to_msb_equ_1 shift_a (a_temp24,a_frac24,shamt_a); // to 1xx...xx
    shift_to_msb_equ_1 shift_b (b_temp24,b_frac24,shamt_b); // to 1xx...xx
    wire [9:0] exp10 = exp_10 - shamt_a + shamt_b;
    reg e1_sign,e1_ae00,e1_aeff,e1_af00,e1_be00,e1_beff,e1_bf00;
    reg e2_sign,e2_ae00,e2_aeff,e2_af00,e2_be00,e2_beff,e2_bf00;
    reg e3_sign,e3_ae00,e3_aeff,e3_af00,e3_be00,e3_beff,e3_bf00;
    reg [1:0] e1_rm,e2_rm,e3_rm;
    reg [9:0] e1_exp10,e2_exp10,e3_exp10;
    
    always @ (negedge clrn or posedge clk)
        if (!clrn) begin // 3 pipeline registers: reg_e1, reg_e2, and reg_e3
            // reg_e1 // reg_e2 // reg_e3
            e1_sign <= 0; e2_sign <= 0; e3_sign <= 0;
            e1_rm <= 0; e2_rm <= 0; e3_rm <= 0;
            e1_exp10<= 0; e2_exp10<= 0; e3_exp10<= 0;
            e1_ae00 <= 0; e2_ae00 <= 0; e3_ae00 <= 0;
            e1_aeff <= 0; e2_aeff <= 0; e3_aeff <= 0;
            e1_af00 <= 0; e2_af00 <= 0; e3_af00 <= 0;
            e1_be00 <= 0; e2_be00 <= 0; e3_be00 <= 0;
            e1_beff <= 0; e2_beff <= 0; e3_beff <= 0;
            e1_bf00 <= 0; e2_bf00 <= 0; e3_bf00 <= 0;
        end else if (ena) begin
            e1_sign <= sign; e2_sign <= e1_sign; e3_sign <= e2_sign;
            e1_rm <= rm; e2_rm <= e1_rm; e3_rm <= e2_rm;
            e1_exp10<= exp10; e2_exp10<= e1_exp10; e3_exp10<= e2_exp10;
            e1_ae00 <= a_expo_is_00; e2_ae00 <= e1_ae00; e3_ae00 <= e2_ae00;
            e1_aeff <= a_expo_is_ff; e2_aeff <= e1_aeff; e3_aeff <= e2_aeff;
            e1_af00 <= a_frac_is_00; e2_af00 <= e1_af00; e3_af00 <= e2_af00;
            e1_be00 <= b_expo_is_00; e2_be00 <= e1_be00; e3_be00 <= e2_be00;
            e1_beff <= b_expo_is_ff; e2_beff <= e1_beff; e3_beff <= e2_beff;
            e1_bf00 <= b_frac_is_00; e2_bf00 <= e1_bf00; e3_bf00 <= e2_bf00;
        end
        
    wire [31:0] q; // af24 / bf24 = 1.xxxxx...x or 0.1xxxx...x
    newton24 frac_newton (a_frac24,b_frac24,fdiv,ena,clk,clrn,
    q,busy,count,reg_x,stall);
    wire [31:0] z0 = q[31]?q: {q[30:0],1'b0}; // 1.xxxxx...x
    wire [9:0] exp_adj = q[31] ? e3_exp10 : e3_exp10 - 10'b1;
    reg [9:0] exp0;
    reg [31:0] frac0;
    
    always @ * begin
        if (exp_adj[9]) begin // exp is negative
            exp0 = 0;
            if (z0[31]) // 1.xx...x
                frac0 = z0 >> (10'b1 - exp_adj); // denormalized (-126)
            else frac0 = 0;
        end else if (exp_adj == 0) begin // exp is 0
            exp0 = 0;
            frac0 = {1'b0,z0[31:2],|z0[1:0]}; // denormalized (-126)
        end else begin // exp > 0
            if (exp_adj > 254) begin // inf
                exp0 = 10'hff;
                frac0 = 0;
            end else begin // normalized
                exp0 = exp_adj;
                frac0 = z0;
            end
        end
    end
    
    wire [26:0] frac = {frac0[31:6],|frac0[5:0]}; // sticky
    wire frac_plus_1 =
    ~e3_rm[1] & ~e3_rm[0] & frac[3] & frac[2] & ~frac[1] & ~frac[0] |
    ~e3_rm[1] & ~e3_rm[0] & frac[2] & (frac[1] | frac[0]) |
    ~e3_rm[1] & e3_rm[0] & (frac[2] | frac[1] | frac[0]) & e3_sign |
    e3_rm[1] & ~e3_rm[0] & (frac[2] | frac[1] | frac[0]) & ~e3_sign;
    wire [24:0] frac_round = {1'b0,frac[26:3]} + frac_plus_1;
    wire [9:0] exp1 = frac_round[24]? exp0 + 10'h1 : exp0;
    wire overflow = (exp1 >= 10'h0ff); // overflow
    wire [7:0] exponent;
    wire [22:0] fraction;
    
    assign {exponent,fraction} = final_result(overflow,e3_rm,e3_sign,e3_ae00,
                                                e3_aeff,e3_af00,e3_be00,e3_beff,
                                                e3_bf00,{exp1[7:0],frac_round[22:0]});
    assign s = {e3_sign,exponent,fraction};
    
    function [30:0] final_result;
        input overflow;
        input [1:0] e3_rm;
        input e3_sign;
        input a_e00,a_eff,a_f00, b_e00,b_eff,b_f00;
        input [30:0] calc;
        
        casex ({overflow,e3_rm,e3_sign,a_e00,a_eff,a_f00,b_e00,b_eff,b_f00})
            10'b100x_xxx_xxx : final_result = INF; // overflow
            10'b1010_xxx_xxx : final_result = MAX; // overflow
            10'b1011_xxx_xxx : final_result = INF; // overflow
            10'b1100_xxx_xxx : final_result = INF; // overflow
            10'b1101_xxx_xxx : final_result = MAX; // overflow
            10'b111x_xxx_xxx : final_result = MAX; // overflow
            10'b0xxx_010_xxx : final_result = NaN; // NaN / any
            10'b0xxx_011_010 : final_result = NaN; // inf / NaN
            10'b0xxx_100_010 : final_result = NaN; // den / NaN
            10'b0xxx_101_010 : final_result = NaN; // 0 / NaN
            10'b0xxx_00x_010 : final_result = NaN; // nor / NaN
            10'b0xxx_011_011 : final_result = NaN; // inf / inf
            10'b0xxx_100_011 : final_result = ZERO; // den / inf
            10'b0xxx_101_011 : final_result = ZERO; // 0 / inf
            10'b0xxx_00x_011 : final_result = ZERO; // nor / inf
            10'b0xxx_011_101 : final_result = INF; // inf / 0
            10'b0xxx_100_101 : final_result = INF; // den / 0
            10'b0xxx_101_101 : final_result = NaN; // 0 / 0
            10'b0xxx_00x_101 : final_result = INF; // nor / 0
            10'b0xxx_011_100 : final_result = INF; // inf / den
            10'b0xxx_100_100 : final_result = calc; // den / den
            10'b0xxx_101_100 : final_result = ZERO; // 0 / den
            10'b0xxx_00x_100 : final_result = calc; // nor / den
            10'b0xxx_011_00x : final_result = INF; // inf / nor
            10'b0xxx_100_00x : final_result = calc; // den / nor
            10'b0xxx_101_00x : final_result = ZERO; // 0 / nor
            10'b0xxx_00x_00x : final_result = calc; // nor / nor
            default : final_result = ZERO;
        endcase
    endfunction
endmodule

module shift_to_msb_equ_1 (a,b,sa); // shift left until msb = 1
    input [23:0] a; // shift a = xxx...xx
    output [23:0] b; // to b = 1xx...xx
    output [4:0] sa; // how many bits shifted
    
    wire [23:0] a5,a4,a3,a2,a1,a0;
    
    assign a5 = a;
    assign sa[4] = ~|a5[23:08]; // 16-bit 0
    assign a4 = sa[4]? {a5[07:00],16'b0} : a5;
    assign sa[3] = ~|a4[23:16]; // 8-bit 0
    assign a3 = sa[3]? {a4[15:00], 8'b0} : a4;
    assign sa[2] = ~|a3[23:20]; // 4-bit 0
    assign a2 = sa[2]? {a3[19:00], 4'b0} : a3;
    assign sa[1] = ~|a2[23:22]; // 2-bit 0
    assign a1 = sa[1]? {a2[21:00], 2'b0} : a2;
    assign sa[0] = ~a1[23]; // 1-bit 0
    assign a0 = sa[0]? {a1[22:00], 1'b0} : a1;
    assign b = a0;
endmodule


module newton24 (a,b,fdiv,ena,clk,clrn,q,busy,count,reg_x,stall);
    input [23:0] a; // dividend: .1xxx...x
    input [23:0] b; // divisor: .1xxx...x
    input fdiv; // ID stage: i_fdiv
    input clk, clrn; // clock and reset
    input ena; // enable, save partial product
    output [31:0] q; // quotient: x.xxxxx...x
    output reg busy; // cannot receive new div
    output [4:0] count; // counter
    output [25:0] reg_x; // for sim test only 01.xx...x
    output stall; // for pipeline stall
    
    reg [31:0] q; // 32-bit: x.xxxxx...x
    reg [25:0] reg_x; // 26-bit: xx.xxxxx...x
    reg [23:0] reg_a; // 24-bit: .1xxxx...x
    reg [23:0] reg_b; // 24-bit: .1xxxx...x
    reg [4:0] count; // 3 iterations * 5 cycles
    wire [49:0] bxi; // xx.xxxxx...x
    wire [51:0] x52; // xxx.xxxxx...x
    wire [49:0] d_x; // 0x.xxxxx...x
    wire [31:0] e2p; // sticky
    wire [7:0] x0 = rom(b[22:19]); // x0: from rom table
    
    always @ (posedge clk or negedge clrn) begin
        if (!clrn) begin
        busy <= 0;
        count <= 0;
        reg_x <= 0;
        end else begin
            if (fdiv & (count == 0)) begin // do once only
                count <= 5'b1; // set count
                busy <= 1'b1; // set to busy
            end else begin // 3 iterations
                if (count == 5'h01) begin
                    reg_a <= a; // .1xxxx...x
                    reg_b <= b; // .1xxxx...x
                    reg_x <= {2'b1,x0,16'b0}; // 01.xxxx0...0
                end
                if (count != 0) count <= count + 5'b1; // count++
                    if (count == 5'h0f) busy <= 0; // ready for next
                        if (count == 5'h10) count <= 5'b0; // reset count
                            if ((count == 5'h06) || // save result of 1st iteration
                                (count == 5'h0b) || // save result of 2nd iteration
                                (count == 5'h10)) // no need to save here actually
                                reg_x <= x52[50:25]; // xx.xxxxx...x
            end
        end
    end
    
    assign stall = fdiv & (count == 0) | busy;
    // wallace_26x24_product (a, b, z);
    wallace_26x24_product bxxi (reg_b,reg_x,bxi); // xi * b
    wire [25:0] b26 = ~bxi[48:23] + 1'b1; // 2 - xi * b
    wallace_26x26_product xip1 (reg_x,b26,x52); // xi * (2 - xi * b)
    reg [25:0] reg_de_x; // pipeline register in between id and e1, x
    reg [23:0] reg_de_a; // pipeline register in between id and e1, a
    wire [49:0] m_s; // sum
    wire [49:8] m_c; // carry
    // wallace_24x26 (a, b, x, y, z);
    wallace_24x26 wt (reg_de_a,reg_de_x,m_s[49:8],m_c,m_s[7:0]); // a * xn
    reg [49:0] a_s; // pipeline register in between e1 and e2, sum
    reg [49:8] a_c; // pipeline register in between e1 and e2, carry
    
    assign d_x = {1'b0,a_s} + {a_c,8'b0}; // 0x.xxxxx...x
    assign e2p = {d_x[48:18],|d_x[17:0]}; // sticky
    
    always @ (negedge clrn or posedge clk)
        if (!clrn) begin // pipeline registers
            reg_de_x <= 0; reg_de_a <= 0; // id-e1
            a_s <= 0; a_c <= 0; // e1-e2
            q <= 0; // e2-e3
        end else if (ena) begin // x52[50:25]: the result of 3rd iteration
            reg_de_x <= x52[50:25]; reg_de_a <= reg_a; // id-e1
            a_s <= m_s; a_c <= m_c; // e1-e2
            q <= e2p; // e2-e3
        end
    
    function [7:0] rom; // a rom table
        input [3:0] b;
        case (b)
            4'h0: rom = 8'hff; 4'h1: rom = 8'hdf;
            4'h2: rom = 8'hc3; 4'h3: rom = 8'haa;
            4'h4: rom = 8'h93; 4'h5: rom = 8'h7f;
            4'h6: rom = 8'h6d; 4'h7: rom = 8'h5c;
            4'h8: rom = 8'h4d; 4'h9: rom = 8'h3f;
            4'ha: rom = 8'h33; 4'hb: rom = 8'h27;
            4'hc: rom = 8'h1c; 4'hd: rom = 8'h12;
            4'he: rom = 8'h08; 4'hf: rom = 8'h00;
        endcase
    endfunction
endmodule

module wallace_26x24_product (a,b,z); // 26*24 wt product
    input [25:00] b; // 26 bits
    input [23:00] a; // 24 bits
    output [49:00] z; // product
    
    wire [49:08] x; // sum high
    wire [49:08] y; // carry high
    wire [49:08] z_high; // product high
    wire [07:00] z_low; // product low
    
    wallace_26x24 wt_partial (a, b, x, y, z_low); // partial product
    assign z_high = x + y;
    assign z = {z_high,z_low}; // product
endmodule

module wallace_26x26_product (a,b,z); // 26*26 wt product
    input [25:00] a; // 26 bits
    input [25:00] b; // 26 bits
    output [51:00] z; // product
    
    wire [51:08] x; // sum high
    wire [51:08] y; // carry high
    wire [51:08] z_high; // product high
    wire [07:00] z_low; // product low
    
    wallace_26x26 wt_partial (a, b, x, y, z_low); // partial product
    assign z_high = x + y;
    assign z = {z_high,z_low}; // product
endmodule