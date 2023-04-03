//=====================================================================
// Project: 4 core MESI cache design
// File Name: base_test.sv
// Description: Base test class
// Designers: Venky & Suru
//=====================================================================

class base_test extends uvm_test;

    //component macro
    `uvm_component_utils(base_test)

    //components of the environment
    cpu_agent_c         agent;

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this,"agent.sequencer.run_phase","default_sequence",cpu_base_seq::type_id::get());
        super.build_phase(phase);
        agent = new("agent",this);
    endfunction : build_phase

    function void end_of_elaboration_phase(uvm_phase phase);
        uvm_top.print_topology();
    endfunction : end_of_elaboration_phase
endclass : base_test
