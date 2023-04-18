//=====================================================================
// Project: 4 core MESI cache design
// File Name: system_bus_interface.sv
// Description: Basic system bus interface including arbiter
// Designers: Venky & Suru
//=====================================================================

interface system_bus_interface(input clk);

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    parameter DATA_WID_LV1        = `DATA_WID_LV1       ;
    parameter ADDR_WID_LV1        = `ADDR_WID_LV1       ;
    parameter NO_OF_CORE            = 4;

    wire [DATA_WID_LV1 - 1 : 0] data_bus_lv1_lv2     ;
    wire [ADDR_WID_LV1 - 1 : 0] addr_bus_lv1_lv2     ;
    wire                        bus_rd               ;
    wire                        bus_rdx              ;
    wire                        lv2_rd               ;
    wire                        lv2_wr               ;
    wire                        lv2_wr_done          ;
    wire                        cp_in_cache          ;
    wire                        data_in_bus_lv1_lv2  ;

    wire                        shared               ;
    wire                        all_invalidation_done;
    wire                        invalidate           ;

    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_gnt_proc ;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_req_proc ;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_gnt_snoop;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_req_snoop;
    logic                       bus_lv1_lv2_gnt_lv2  ;
    logic                       bus_lv1_lv2_req_lv2  ;

//Assertions
//property that checks that signal_1 is asserted in the previous cycle of signal_2 assertion
    property prop_sig1_before_sig2(signal_1,signal_2);
    @(posedge clk)
        signal_2 |-> $past(signal_1);
    endproperty

//ASSERTION 1: lv2_wr_done should not be asserted without lv2_wr being asserted in previous cycle
    assert_lv2_wr_done: assert property (prop_sig1_before_sig2(lv2_wr,lv2_wr_done))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv2_wr_done Failed: lv2_wr not asserted before lv2_wr_done goes high"))

//LAB5: TO DO: Add 4 assertions at this interface

//ASSERTION 2: data_in_bus_lv1_lv2 and cp_in_cache should not be asserted without lv2_rd being asserted in previous cycle
assert_lv2_rd : assert property (prop_sig1_before_sig2(lv2_rd, data_in_bus_lv1_lv2 && cp_in_cache))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv2_rd Failed: lv2_rd not asserted before data_in_bus_lv1_lv2 && cp_in_cache high"))


//ASSERTION 3: Once access granted (bus_lv1_lv2_gnt_proc = 1), only then bus_rd and lv2_rd is raised/asserted.
assert_bus_rd_lv2_rd : assert property (prop_sig1_before_sig2(bus_lv1_lv2_gnt_proc, bus_rd && lv2_rd))
else 
   `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_rd_lv2_rd Failed : bus_rd and lv2_rd is asserted even before bus_lv1_lv2_gnt_proc"))


//General Property Definition 
property prop_gnt_onehot(signal_one_hot); 
      @(posedge clk)
                $onehot0(signal_one_hot);
endproperty

// ASSERTION 4: The grant signal (for the proc side) is one hot. 
assert_lv1_gnt_proc_onehot : assert property (prop_gnt_onehot(bus_lv1_lv2_gnt_proc))
else 
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv1_gnt_proc_onehot Failed: the bus_lv1_lv2_gnt_proc is not a onehot signal"))

//ASSERTION 5: The grant signal (for the snoop side) is one hot.
assert_lv1_gnt_snoop_onehot : assert property (prop_gnt_onehot(bus_lv1_lv2_gnt_snoop))
else 
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv1_gnt_snoop_onehot Failed: the bus_lv1_lv2_gnt_snoop is not a onehot signal"))


// ASSERTION 6: After bus_lv1_lv2_gnt_snoop is asserted in a particular clock cycle, from the next clock cycle or in the later clock cycles, the signals 'shared' and 'data_in_bus_lv1_lv2' will be asserted at the same time. 

property prop_bus_gnt_snoop_shared (int core0123);
@(posedge clk)
(bus_lv1_lv2_gnt_snoop[core0123]) |=> ##[0:$] (shared && data_in_bus_lv1_lv2);
endproperty

assert_bus_gnt_snoop_shared_0 : assert property (prop_bus_gnt_snoop_shared(0))
else
  `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_gnt_snoop_shared Failed for core/proc0: shared and data_in_bus_lv1_lv2 not asserted after the bus_lv1_lv2_gnt_snoop"))

assert_bus_gnt_snoop_shared_1 : assert property (prop_bus_gnt_snoop_shared(1))
else
  `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_gnt_snoop_shared Failed for core/proc1: shared and data_in_bus_lv1_lv2 not asserted after the bus_lv1_lv2_gnt_snoop"))

assert_bus_gnt_snoop_shared_2 : assert property (prop_bus_gnt_snoop_shared(2))
else
  `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_gnt_snoop_shared Failed for core/proc2: shared and data_in_bus_lv1_lv2 not asserted after the bus_lv1_lv2_gnt_snoop"))

assert_bus_gnt_snoop_shared_3 : assert property (prop_bus_gnt_snoop_shared(3))
else
  `uvm_error("system_bus_interface",$sformatf("Assertion assert_bus_gnt_snoop_shared Failed for core/proc3: shared and data_in_bus_lv1_lv2 not asserted after the bus_lv1_lv2_gnt_snoop"))

endinterface
