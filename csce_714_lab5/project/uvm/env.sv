//=====================================================================
// Project: 4 core MESI cache design
// File Name: env.sv
// Description: test bench component
// Designers: Venky & Suru
//=====================================================================

//include the system bus monitor
`include "system_bus_monitor_c.sv"
//include the scoreboard
`include "cache_scoreboard_c.sv"

class env extends uvm_env;

//component macro
    `uvm_component_utils(env)

//Declare handles of components within the tb, that we have created till now
    cpu_agent_c                 cpu[0:3];
    system_bus_monitor_c      sbus_monitor;
    cache_scoreboard_c          sb;

//Constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

//UVM build phase method
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
//LAB5: TO DO: Create 4 agents "cpu[0], cpu[1], cpu[2], cpu[3]"
	       //Create System bus monitor "sbus_monitor"
	       //Create Scoreboard "sb"

				cpu[0] = cpu_agent_c::type_id::create("cpu[0]", this);   // HINT
    
    endfunction : build_phase

//UVM connect phase method
    function void connect_phase(uvm_phase phase);
//Connect monitor and scoreboard
        cpu[0].monitor.mon_out.connect(sb.sb_cpu0m);
        cpu[1].monitor.mon_out.connect(sb.sb_cpu1m);
        cpu[2].monitor.mon_out.connect(sb.sb_cpu2m);
        cpu[3].monitor.mon_out.connect(sb.sb_cpu3m);
        sbus_monitor.sbus_out.connect(sb.sb_sbus);
    endfunction : connect_phase

endclass: env
