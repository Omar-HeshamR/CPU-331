`timescale 1ns / 1ps

module testbench();

    reg clk_tb;
    wire [31:0] pc;
    wire [31:0] dinstOut;
    wire [31:0] ealu;
    wire [31:0] mr;    
    wire [31:0] wbData; 

    data_path dut (
    
        .clk(clk_tb),
        .pc(pc),
        .dinstOut(dinstOut),
        .ealu(ealu),
        .mr(mr),
        .wbData(wbData)
    );
        
    initial begin
        clk_tb = 0;
    end
    always begin 
        #5 clk_tb = !clk_tb; 
    end
endmodule
