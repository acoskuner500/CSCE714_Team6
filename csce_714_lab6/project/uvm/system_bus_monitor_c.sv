//=====================================================================
// Project: 4 core MESI cache design
// File Name: system_bus_monitor_c.sv
// Description: system bus monitor component
// Designers: Venky & Suru
//=====================================================================

`include "sbus_packet_c.sv"

class system_bus_monitor_c extends uvm_monitor;
    //component macro
    `uvm_component_utils(system_bus_monitor_c)

    uvm_analysis_port #(sbus_packet_c) sbus_out;
    sbus_packet_c       s_packet;

    //Covergroup to monitor all the points within sbus_packet
    covergroup cover_sbus_packet;
        option.per_instance = 1;
        option.name = "cover_system_bus";
        REQUEST_TYPE: coverpoint  s_packet.bus_req_type;
        REQUEST_PROCESSOR: coverpoint s_packet.bus_req_proc_num;
        REQUEST_ADDRESS: coverpoint s_packet.req_address{
            option.auto_bin_max = 20;
        }
        READ_DATA: coverpoint s_packet.rd_data{
            option.auto_bin_max = 20;
        }
//LAB6: TO DO: Add coverage for other fields of sbus_mon_packet

       REQUEST_SERVICED_BY: coverpoint s_packet.req_serviced_by;
       REQUEST_BUS_SNOOP: coverpoint s_packet.bus_req_snoop;
       WRITE_DATA_SNOOP: coverpoint s_packet.wr_data_snoop {
        option.auto_bin_max = 20;
       }
       SNOOP_WRITE_REQUEST: coverpoint s_packet.snoop_wr_req_flag;
       COPY_IN_CACHE: coverpoint s_packet.cp_in_cache;
       SHARED_DATA: coverpoint s_packet.shared;
       PROC_EVICT_DIRTY_BLOCK_ADDRESS: coverpoint s_packet.proc_evict_dirty_blk_addr{
        option.auto_bin_max = 20;
       }
       PROC_EVICT_DIRTY_BLOCK_DATA: coverpoint s_packet.proc_evict_dirty_blk_data{
        option.auto_bin_max = 20;
       }
       PROC_EVICT_DIRTY_BLOCK_FLAG: coverpoint s_packet.proc_evict_dirty_blk_flag;
    
    
    //cross coverage
        //ensure each processor has read miss, write miss, invalidate, etc.
        X_PROC__REQ_TYPE: cross REQUEST_TYPE, REQUEST_PROCESSOR;
        X_PROC__ADDRESS: cross REQUEST_PROCESSOR, REQUEST_ADDRESS;
        X_PROC__DATA: cross REQUEST_PROCESSOR, READ_DATA;

//LAB6: TO DO: Add relevant cross coverage (examples shown above)

    X_REQ_TYPE_ADDRESS : cross REQUEST_TYPE, REQUEST_ADDRESS;
    X_REQ_ADDRESS_DATA : cross REQUEST_ADDRESS, READ_DATA;
    X_REQ_TYPE_READ_DATA: cross REQUEST_TYPE, READ_DATA;

    //Crossing REQUEST_SERVICED_BY with all other cover points.
    X_REQUEST_SERVICED_BY_TYPE: cross REQUEST_SERVICED_BY, REQUEST_TYPE;
    X_REQUEST_SERVICED_BY_PROCESSOR: cross REQUEST_SERVICED_BY, REQUEST_PROCESSOR;
    X_REQUEST_SERVICED_BY_ADDRESS: cross REQUEST_SERVICED_BY, REQUEST_ADDRESS;
    X_REQUEST_SERVICED_BY_READ_DATA: cross REQUEST_SERVICED_BY, READ_DATA;
    X_REQUEST_SERVICED_BY_BUS_SNOOP: cross REQUEST_SERVICED_BY, REQUEST_BUS_SNOOP;
    X_REQUEST_SERVICED_BY_WRITE_DATA_SNOOP: cross REQUEST_SERVICED_BY, WRITE_DATA_SNOOP;
    X_REQUEST_SERVICED_BY_SNOOP_WRITE_REQUEST: cross REQUEST_SERVICED_BY, SNOOP_WRITE_REQUEST;
    X_REQUEST_SERVICED_BY_COPY_IN_CACHE: cross REQUEST_SERVICED_BY, COPY_IN_CACHE;
    X_REQUEST_SERVICED_BY_SHARED_DATA: cross REQUEST_SERVICED_BY, SHARED_DATA;
    X_REQUEST_SERVICED_BY_PROC_EVICT_DIRTY_BLOCK_ADDRESS: cross REQUEST_SERVICED_BY, PROC_EVICT_DIRTY_BLOCK_ADDRESS;
    X_REQUEST_SERVICED_BY_PROC_EVICT_DIRTY_BLOCK_DATA: cross REQUEST_SERVICED_BY, PROC_EVICT_DIRTY_BLOCK_DATA;
    X_REQUEST_SERVICED_BY_PROC_EVICT_DIRTY_BLOCK_FLAG: cross REQUEST_SERVICED_BY, PROC_EVICT_DIRTY_BLOCK_FLAG;
    

    //Crossing BUS_SNOOP_REQUEST with all other cover points.
    X_REQUEST_BUS_SNOOP_REQUEST_TYPE :cross REQUEST_BUS_SNOOP, REQUEST_TYPE ;
    X_REQUEST_BUS_SNOOP_REQUEST_PROCESSOR :cross REQUEST_BUS_SNOOP, REQUEST_PROCESSOR ;
    X_REQUEST_BUS_SNOOP_REQUEST_ADDRESS :cross REQUEST_BUS_SNOOP, REQUEST_ADDRESS ;
    X_REQUEST_BUS_SNOOP_READ_DATA :cross REQUEST_BUS_SNOOP, READ_DATA ;
    X_REQUEST_BUS_SNOOP_WRITE_DATA_SNOOP :cross REQUEST_BUS_SNOOP, WRITE_DATA_SNOOP;
    X_REQUEST_BUS_SNOOP_SNOOP_WRITE_REQUEST :cross REQUEST_BUS_SNOOP, SNOOP_WRITE_REQUEST ;
    X_REQUEST_BUS_SNOOP_COPY_IN_CACHE :cross REQUEST_BUS_SNOOP, COPY_IN_CACHE;
    X_REQUEST_BUS_SNOOP_SHARED_DATA :cross REQUEST_BUS_SNOOP, SHARED_DATA ;
    X_REQUEST_BUS_SNOOP_PROC_EVICT_DIRTY_BLOCK_ADDRESS :cross REQUEST_BUS_SNOOP, PROC_EVICT_DIRTY_BLOCK_ADDRESS;
    X_REQUEST_BUS_SNOOP_PROC_EVICT_DIRTY_BLOCK_DATA :cross REQUEST_BUS_SNOOP, PROC_EVICT_DIRTY_BLOCK_DATA;
    X_REQUEST_BUS_SNOOP_PROC_EVICT_DIRTY_BLOCK_FLAG :cross REQUEST_BUS_SNOOP, PROC_EVICT_DIRTY_BLOCK_FLAG;


    //Crossing WRITE_DATA_SNOOP with all the other coverpoints. 
    X_WRITE_DATA_SNOOP_REQUEST_TYPE : cross WRITE_DATA_SNOOP, REQUEST_TYPE;
    X_WRITE_DATA_SNOOP_REQUEST_PROCESSOR : cross WRITE_DATA_SNOOP, REQUEST_PROCESSOR;
    X_WRITE_DATA_SNOOP_REQUEST_ADDRESS : cross WRITE_DATA_SNOOP, REQUEST_ADDRESS;
    X_WRITE_DATA_SNOOP_READ_DATA : cross WRITE_DATA_SNOOP, READ_DATA;
    X_WRITE_DATA_SNOOP_SNOOP_WRITE_REQUEST : cross WRITE_DATA_SNOOP, SNOOP_WRITE_REQUEST;
    X_WRITE_DATA_SNOOP_COPY_IN_CACHE : cross WRITE_DATA_SNOOP, COPY_IN_CACHE;
    X_WRITE_DATA_SNOOP_SHARED_DATA : cross WRITE_DATA_SNOOP, SHARED_DATA;
    X_WRITE_DATA_SNOOP_PROC_EVICT_DIRTY_BLOCK_ADDRESS : cross WRITE_DATA_SNOOP, PROC_EVICT_DIRTY_BLOCK_ADDRESS;
    X_WRITE_DATA_SNOOP_PROC_EVICT_DIRTY_BLOCK_DATA : cross WRITE_DATA_SNOOP, PROC_EVICT_DIRTY_BLOCK_DATA;
    X_WRITE_DATA_SNOOP_PROC_EVICT_DIRTY_BLOCK_FLAG : cross WRITE_DATA_SNOOP, PROC_EVICT_DIRTY_BLOCK_FLAG;
    
       //Crossing SNOOP_WRITE_REQUEST with all other coverpoints.
        X_SNOOP_WRITE_REQUEST__REQUEST_TYPE:    cross SNOOP_WRITE_REQUEST, REQUEST_TYPE;
        X_SNOOP_WRITE_REQUEST__REQUEST_PROCESSOR:    cross SNOOP_WRITE_REQUEST, REQUEST_PROCESSOR;
        X_SNOOP_WRITE_REQUEST__REQUEST_ADDRESS:    cross SNOOP_WRITE_REQUEST, REQUEST_ADDRESS;
        X_SNOOP_WRITE_REQUEST__READ_DATA:    cross SNOOP_WRITE_REQUEST, READ_DATA;
        X_SNOOP_WRITE_REQUEST__COPY_IN_CACHE: cross SNOOP_WRITE_REQUEST, COPY_IN_CACHE;
        X_SNOOP_WRITE_REQUEST__SHARED_DATA: cross SNOOP_WRITE_REQUEST, SHARED_DATA;
        X_SNOOP_WRITE_REQUEST__PROC_EVICT_DIRTY_BLOCK_ADDRESS: cross SNOOP_WRITE_REQUEST, PROC_EVICT_DIRTY_BLOCK_ADDRESS;
        X_SNOOP_WRITE_REQUEST__PROC_EVICT_DIRTY_BLOCK_DATA: cross SNOOP_WRITE_REQUEST, PROC_EVICT_DIRTY_BLOCK_DATA;
        X_SNOOP_WRITE_REQUEST__PROC_EVICT_DIRTY_BLOCK_FLAG: cross SNOOP_WRITE_REQUEST, PROC_EVICT_DIRTY_BLOCK_FLAG;
        
        //Crossing COPY_IN_CACHE with all other coverpoints.
        X_COPY_IN_CACHE__REQUEST_TYPE: cross COPY_IN_CACHE, REQUEST_TYPE;
        X_COPY_IN_CACHE__REQUEST_PROCESSOR: cross COPY_IN_CACHE, REQUEST_PROCESSOR;
        X_COPY_IN_CACHE__REQUEST_ADDRESS: cross COPY_IN_CACHE, REQUEST_ADDRESS;
        X_COPY_IN_CACHE__READ_DATA: cross COPY_IN_CACHE, READ_DATA;
        X_COPY_IN_CACHE__SHARED_DATA: cross COPY_IN_CACHE, SHARED_DATA;
        X_COPY_IN_CACHE__PROC_EVICT_DIRTY_BLOCK_ADDRESS: cross COPY_IN_CACHE, PROC_EVICT_DIRTY_BLOCK_ADDRESS;
        X_COPY_IN_CACHE__PROC_EVICT_DIRTY_BLOCK_DATA: cross COPY_IN_CACHE, PROC_EVICT_DIRTY_BLOCK_DATA;
        X_COPY_IN_CACHE__PROC_EVICT_DIRTY_BLOCK_FLAG: cross COPY_IN_CACHE, PROC_EVICT_DIRTY_BLOCK_FLAG;
        
        //Crossing SHARED_DATA  with all other cover points.
        X_SHARED_DATA__REQUEST_TYPE: cross SHARED_DATA, REQUEST_TYPE;
        X_SHARED_DATA__REQUEST_PROCESSOR: cross SHARED_DATA, REQUEST_PROCESSOR;
        X_SHARED_DATA__REQUEST_ADDRESS: cross SHARED_DATA, REQUEST_ADDRESS;
        X_SHARED_DATA__READ_DATA: cross SHARED_DATA, READ_DATA;
        X_SHARED_DATA__PROC_EVICT_DIRTY_BLOCK_ADDRESS: cross SHARED_DATA, PROC_EVICT_DIRTY_BLOCK_ADDRESS;
        X_SHARED_DATA__PROC_EVICT_DIRTY_BLOCK_DATA: cross SHARED_DATA, PROC_EVICT_DIRTY_BLOCK_DATA;
        X_SHARED_DATA__PROC_EVICT_DIRTY_BLOCK_FLAG: cross SHARED_DATA, PROC_EVICT_DIRTY_BLOCK_FLAG;

        //Crossing PROC_EVICT_DIRTY_BLOCK_ADDRESS with all other cover points.
        X_PROC_EVICT_DIRTY_BLOCK_ADDRESS__REQUEST_TYPE: cross PROC_EVICT_DIRTY_BLOCK_ADDRESS, REQUEST_TYPE;
        X_PROC_EVICT_DIRTY_BLOCK_ADDRESS__REQUEST_PROCESSOR: cross PROC_EVICT_DIRTY_BLOCK_ADDRESS, REQUEST_PROCESSOR;
        X_PROC_EVICT_DIRTY_BLOCK_ADDRESS__REQUEST_ADDRESS: cross PROC_EVICT_DIRTY_BLOCK_ADDRESS, REQUEST_ADDRESS;
        X_PROC_EVICT_DIRTY_BLOCK_ADDRESS__READ_DATA: cross PROC_EVICT_DIRTY_BLOCK_ADDRESS, READ_DATA;
        X_PROC_EVICT_DIRTY_BLOCK_ADDRESS__PROC_EVICT_DATA : cross PROC_EVICT_DIRTY_BLOCK_ADDRESS, PROC_EVICT_DIRTY_BLOCK_DATA;
        X_PROC_EVICT_DIRTY_BLOCK_ADDRESS__PROC_EVICT_FLAG : cross PROC_EVICT_DIRTY_BLOCK_ADDRESS, PROC_EVICT_DIRTY_BLOCK_FLAG;

        //Crossing PROC_EVICT_DIRTY_BLOCK_DATA with all other cover points.
        X_PROC_EVICT_DIRTY_BLOCK_DATA__REQUEST_TYPE: cross PROC_EVICT_DIRTY_BLOCK_DATA, REQUEST_TYPE;
        X_PROC_EVICT_DIRTY_BLOCK_DATA__REQUEST_PROCESSOR: cross PROC_EVICT_DIRTY_BLOCK_DATA, REQUEST_PROCESSOR;
        X_PROC_EVICT_DIRTY_BLOCK_DATA__REQUEST_ADDRESS: cross PROC_EVICT_DIRTY_BLOCK_DATA, REQUEST_ADDRESS;
        X_PROC_EVICT_DIRTY_BLOCK_DATA__READ_DATA: cross PROC_EVICT_DIRTY_BLOCK_DATA, READ_DATA;
        X_PROC_EVICT_DIRTY_BLOCK_DATA__PROC_EVICT_FLAG : cross PROC_EVICT_DIRTY_BLOCK_DATA, PROC_EVICT_DIRTY_BLOCK_FLAG;

        //Crossing PROC_EVICT_DIRTY_BLOCK_FLAG with all other coverpoints
        X_PROC_EVICT_DIRTY_BLOCK_FLAG__REQUEST_TYPE: cross PROC_EVICT_DIRTY_BLOCK_FLAG, REQUEST_TYPE;
        X_PROC_EVICT_DIRTY_BLOCK_FLAG__REQUEST_PROCESSOR: cross PROC_EVICT_DIRTY_BLOCK_FLAG, REQUEST_PROCESSOR;
        X_PROC_EVICT_DIRTY_BLOCK_FLAG__REQUEST_ADDRESS: cross PROC_EVICT_DIRTY_BLOCK_FLAG, REQUEST_ADDRESS;
        X_PROC_EVICT_DIRTY_BLOCK_FLAG__READ_DATA: cross PROC_EVICT_DIRTY_BLOCK_FLAG, READ_DATA;
    
    //

    endgroup


    // Virtual interface of used to observe system bus interface signals
    virtual interface system_bus_interface vi_sbus_if;

    //constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
        sbus_out = new("sbus_out", this);
        this.cover_sbus_packet = new();
    endfunction : new

    //UVM build phase ()
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // throw error if virtual interface is not set
        if (!uvm_config_db#(virtual system_bus_interface)::get(this, "","v_sbus_if", vi_sbus_if))
            `uvm_fatal("NO_VIF",{"virtual interface must be set for: ",get_full_name(),".vi_sbus_if"})
    endfunction: build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "RUN Phase", UVM_LOW)
        forever begin
            // trigger point for creating the packet
            @(posedge (|vi_sbus_if.bus_lv1_lv2_gnt_proc));
            `uvm_info(get_type_name(), "Packet creation triggered", UVM_LOW)
            s_packet = sbus_packet_c::type_id::create("s_packet", this);

            // wait for assertion of either bus_rd, bus_rdx or invalidate before monitoring other bus activities
            // lv2_rd for I-cache cases
            @(posedge(vi_sbus_if.bus_rd | vi_sbus_if.bus_rdx | vi_sbus_if.invalidate | vi_sbus_if.lv2_rd));
            fork
                begin: cp_in_cache_check
                    // check for cp_in_cache assertion
                    @(posedge vi_sbus_if.cp_in_cache) s_packet.cp_in_cache = 1;
                end : cp_in_cache_check
                begin: shared_check
                    // check for shared signal assertion when data_in_bus_lv1_lv2 is also high
                    wait(vi_sbus_if.shared & vi_sbus_if.data_in_bus_lv1_lv2) s_packet.shared = 1;
                end : shared_check
            join_none

            // bus request type
            if (vi_sbus_if.bus_rd === 1'b1)
                s_packet.bus_req_type = BUS_RD;

            // proc which requested the bus access
            case (1'b1)
                vi_sbus_if.bus_lv1_lv2_gnt_proc[0]: s_packet.bus_req_proc_num = REQ_PROC0;
                vi_sbus_if.bus_lv1_lv2_gnt_proc[1]: s_packet.bus_req_proc_num = REQ_PROC1;
                vi_sbus_if.bus_lv1_lv2_gnt_proc[2]: s_packet.bus_req_proc_num = REQ_PROC2;
                vi_sbus_if.bus_lv1_lv2_gnt_proc[3]: s_packet.bus_req_proc_num = REQ_PROC3;
            endcase

            // address requested
            s_packet.req_address = vi_sbus_if.addr_bus_lv1_lv2;

            // fork and call tasks
            fork: update_info

                // to determine which of snoops or L2 serviced read miss
                begin: req_service_check
                    if (s_packet.bus_req_type == BUS_RD)
                    begin
                        @(posedge vi_sbus_if.data_in_bus_lv1_lv2);
                        `uvm_info(get_type_name(), "Bus read or bus readX successful", UVM_LOW)
                        s_packet.rd_data = vi_sbus_if.data_bus_lv1_lv2;
                        // check which had grant asserted
                        case (1'b1)
                            vi_sbus_if.bus_lv1_lv2_gnt_snoop[0]: s_packet.req_serviced_by = SERV_SNOOP0;
                            vi_sbus_if.bus_lv1_lv2_gnt_snoop[1]: s_packet.req_serviced_by = SERV_SNOOP1;
                            vi_sbus_if.bus_lv1_lv2_gnt_snoop[2]: s_packet.req_serviced_by = SERV_SNOOP2;
                            vi_sbus_if.bus_lv1_lv2_gnt_snoop[3]: s_packet.req_serviced_by = SERV_SNOOP3;
                            vi_sbus_if.bus_lv1_lv2_gnt_lv2     : s_packet.req_serviced_by = SERV_L2;
                        endcase
                    end
                end: req_service_check

            join_none : update_info

            // wait until request is processed and send data
            @(negedge vi_sbus_if.bus_lv1_lv2_req_proc[0] or negedge vi_sbus_if.bus_lv1_lv2_req_proc[1] or negedge vi_sbus_if.bus_lv1_lv2_req_proc[2] or negedge vi_sbus_if.bus_lv1_lv2_req_proc[3]);

            `uvm_info(get_type_name(), "Packet to be written", UVM_LOW)

            // disable all spawned child processes from fork
            disable fork;

            // write into scoreboard after population of the packet fields
            sbus_out.write(s_packet);
            cover_sbus_packet.sample();
       end
    endtask : run_phase

endclass : system_bus_monitor_c
