//=====================================================================
// Project: 4 core MESI cache design
// File Name: cpu_lv1_interface.sv
// Description: Basic CPU-LV1 interface with assertions
// Designers: Venky & Suru
//=====================================================================


interface cpu_lv1_interface(input clk);

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    parameter DATA_WID_LV1           = `DATA_WID_LV1       ;
    parameter ADDR_WID_LV1           = `ADDR_WID_LV1       ;

    reg   [DATA_WID_LV1 - 1   : 0] data_bus_cpu_lv1_reg    ;

    wire  [DATA_WID_LV1 - 1   : 0] data_bus_cpu_lv1        ;
    logic [ADDR_WID_LV1 - 1   : 0] addr_bus_cpu_lv1        ;
    logic                          cpu_rd                  ;
    logic                          cpu_wr                  ;
    logic                          cpu_wr_done             ;
    logic                          data_in_bus_cpu_lv1     ;

    assign data_bus_cpu_lv1 = data_bus_cpu_lv1_reg ;

//Assertions
//ASSERTION1: cpu_wr and cpu_rd should not be asserted at the same clock cycle
    property prop_simult_cpu_wr_rd;
        @(posedge clk)
          not(cpu_rd && cpu_wr);
    endproperty

    assert_simult_cpu_wr_rd: assert property (prop_simult_cpu_wr_rd)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_simult_cpu_wr_rd Failed: cpu_wr and cpu_rd asserted simultaneously"))

//LAB5 : TO DO: Add 4 assertions at this interface


//ASSERTION 2: Writes to Instruction Cache is Invalid. If write requests are asserted, then the address can never be less than 32’h 4000_0000.

property prop_write_instn_cache; 
     @(posedge clk)
         (cpu_wr == 1) |-> ((addr_bus_cpu_lv1 > 32'h 4000_0000) && cpu_wr);  
endproperty 
assert_write_instn_cache : assert property (prop_write_instn_cache)
else
    `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_write_instn_cache Failed: An attempt to write into the instruction cache was done"))



//ASSERTION 3: write done signal should be deasserted 1 clock cycle after write signal is deasserted. 
property prop_write_deassert;
   @(posedge clk)
         $fell(cpu_wr) |=> $fell(cpu_wr_done);
endproperty
assert_prop_write_deassert : assert property (prop_write_deassert) 
else
    `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_prop_write_deassert Failed: Write done signal is still asserted even after write signal is deasserted in the previous clock"))


//ASSERTION 4: Write signal should be deasserted after write to cache is completed. 
property prop_write_deassert_1;
  @(posedge clk)
     $rose(cpu_wr_done) |=> $fell(cpu_wr);
endproperty
assert_prop_write_deassert_1 : assert property (prop_write_deassert_1)
else
    `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_prop_write_deassert_1 Failed: Write signal continues to be asserted"))


//ASSERTION 5: data in bus should not have unknowns (X) while data_in_bus is asserted.
property prop_data_in_bus_is_real_data;
        @(posedge clk)
            (data_in_bus_cpu_lv1 == (^data_bus_cpu_lv1 !== 1'bx));
endproperty
assert_data_in_bus_is_real_data: assert property (prop_data_in_bus_is_real_data)
else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_data_in_bus_is_real_data Failed: data in bus has unknowns while data_in_bus asserted"))

endinterface