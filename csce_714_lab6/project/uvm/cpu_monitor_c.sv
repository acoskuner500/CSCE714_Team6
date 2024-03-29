//=====================================================================
// Project: 4 core MESI cache design
// File Name: cpu_monitor_c.sv
// Description: cpu monitor component
// Designers: Venky & Suru
//=====================================================================

class cpu_monitor_c extends uvm_monitor;
    //component macro
    `uvm_component_utils(cpu_monitor_c)
    cpu_mon_packet_c packet;
    uvm_analysis_port #(cpu_mon_packet_c) mon_out;

    // Virtual interface of used to drive and observe CPU-LV1 interface signals
    virtual interface cpu_lv1_interface vi_cpu_lv1_if;

    covergroup cover_cpu_packet;
        option.per_instance = 1;
        option.name = "cover_cpu_packets";
        REQUEST: coverpoint packet.request_type;

    //LAB6: TO DO: Add coverpoints for Data, Address, etc.
    CP_ADDRESS_TYPE : coverpoint packet.addr_type;
    CP_DATA : coverpoint packet.dat {
        option.auto_bin_max = 20;
    }
    CP_ADDRESS : coverpoint packet.address {
             option.auto_bin_max = 20;
    }
    CP_ILLEGAL : coverpoint packet.illegal;

    //Crossing REQUEST with all other coverpoints.
    X_REQUEST_CP_ADDRESS_TYPE : cross REQUEST, CP_ADDRESS_TYPE;
    X_REQUEST_CP_DATA : cross REQUEST, CP_DATA;
    X_REQUEST_CP_ADDRESS : cross REQUEST, CP_ADDRESS;
    X_REQUEST_CP_ILLEGAL : cross REQUEST, CP_ILLEGAL;

   //Crossing CP_ADDRESS_TYPE with all other cover points
   X_CP_ADDRESS_TYPE_CP_DATA : cross CP_ADDRESS_TYPE, CP_DATA;
   X_CP_ADDRESS_TYPE_CP_ADDRESS : cross CP_ADDRESS_TYPE, CP_ADDRESS ;
   X_CP_ADDRESS_TYPE_CP_ILLEGAL : cross CP_ADDRESS_TYPE, CP_ILLEGAL;

   //Crossing CP_DATA with all other cover points. 
   X_CP_DATA_CP_ADDRESS : cross CP_DATA, CP_ADDRESS; 
   X_CP_DATA_CP_ILLEGAL : cross CP_DATA, CP_ILLEGAL;

   //Crossing CP_ADDRESS with all other cover points. 
   X_CP_ADDRESS_CP_ILLEGAL : cross CP_ADDRESS, CP_ILLEGAL;


    endgroup


    //constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
        mon_out = new ("mon_out", this);
	this.cover_cpu_packet = new();
    endfunction : new

    //UVM build phase ()
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // throw error if virtual interface is not set
        if (!uvm_config_db#(virtual cpu_lv1_interface)::get(this, "","vif", vi_cpu_lv1_if))
            `uvm_fatal("NO_VIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
    endfunction: build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "RUN Phase", UVM_LOW)
        forever begin
            @(posedge vi_cpu_lv1_if.cpu_rd or posedge vi_cpu_lv1_if.cpu_wr)
            packet = cpu_mon_packet_c::type_id::create("packet", this);
            if(vi_cpu_lv1_if.cpu_rd === 1'b1) begin
                packet.request_type = READ_REQ;
            end
            packet.address = vi_cpu_lv1_if.addr_bus_cpu_lv1;
            @(posedge vi_cpu_lv1_if.data_in_bus_cpu_lv1 or posedge vi_cpu_lv1_if.cpu_wr_done)
            packet.dat = vi_cpu_lv1_if.data_bus_cpu_lv1;
            @(negedge vi_cpu_lv1_if.cpu_rd or negedge vi_cpu_lv1_if.cpu_wr)
            mon_out.write(packet);
	    cover_cpu_packet.sample();
        end
    endtask : run_phase

endclass : cpu_monitor_c
