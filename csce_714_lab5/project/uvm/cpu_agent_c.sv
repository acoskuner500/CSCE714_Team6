//=====================================================================
// Project: 4 core MESI cache design
// File Name: cpu_agent_c.sv
// Description: cpu agent component
// Designers: Venky & Suru
//=====================================================================

//Extend cpu_agent_c class from uvm_agent
class cpu_agent_c extends uvm_agent;

//Declare a protected field is_active of type uvm_active_passive_enum
//this field determines whether an agent is active or passive
    protected uvm_active_passive_enum is_active = UVM_ACTIVE;

//LAB5: TO DO: Declare handles for monitor, driver and sequencer
    cpu_driver_c driver;
    cpu_sequencer_c sequencer;

//Declare component utility macro for cpu_agent_c and set flag as UVM_ALL_ON for the field is_active which is of type uvm_active_passive_enum
    `uvm_component_utils_begin(cpu_agent_c)
        `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_ALL_ON)
    `uvm_component_utils_end

//Constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

//Define build_phase()
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
//LAB5: TO DO: Create a Monitor
	
	if(is_active == UVM_ACTIVE) begin
            sequencer = cpu_sequencer_c::type_id::create("sequencer", this);
            driver = cpu_driver_c::type_id::create("driver", this);
        end
    endfunction : build_phase

//Define connect_phase()
    function void connect_phase(uvm_phase phase);
        if(is_active == UVM_ACTIVE)
            driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction : connect_phase

endclass: cpu_agent_c
