//=====================================================================
// Project: 4 core MESI cache design
// File Name: cpu_sequencer_c.sv
// Description: cpu sequencer component
// Designers: Venky & Suru
//=====================================================================

//Extend cpu_sequence_c class from uvm_sequencer, with parameter cpu_transaction_c
class cpu_sequencer_c extends uvm_sequencer #(cpu_transaction_c);
//Component Utility Macto
    `uvm_component_utils(cpu_sequencer_c)

//Constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

endclass : cpu_sequencer_c
