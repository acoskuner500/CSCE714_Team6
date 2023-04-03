//=====================================================================
// Project: 4 core MESI cache design
// File Name: cpu_driver_c.sv
// Description: cpu driver component
// Designers: Venky & Suru
//=====================================================================

`define TIME_OUT_VAL 110

//Extend cpu_driver_c from uvm_driver, and paramterize the class with cpu_transaction_c 
class cpu_driver_c extends uvm_driver #(cpu_transaction_c);

    parameter DATA_WID_LV1           = `DATA_WID_LV1       ;
    parameter ADDR_WID_LV1           = `ADDR_WID_LV1       ;

//Declare the utility macro, driver is a component, so component utility macro
    `uvm_component_utils(cpu_driver_c)

//Virtual interface of used to drive and observe CPU-LV1 interface signals
    virtual interface cpu_lv1_interface vi_cpu_lv1_if;

//constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

//declare tasks & functions
    extern function void build_phase(uvm_phase phase);
    extern task run_phase(uvm_phase phase);
    extern protected task get_and_drive();
    extern task send_to_dut(cpu_transaction_c transaction);
    extern protected task drv_rd_trans(bit [ADDR_WID_LV1-1:0] addr, bit [DATA_WID_LV1-1:0] exp_data);

//TO DO: LAB4: HOMEWORK PART B: Declare write task
    extern protected task drv_wr_trans(bit [ADDR_WID_LV1-1:0] addr, bit [DATA_WID_LV1-1:0] wrt_data);

endclass : cpu_driver_c

//Defining functions & tasks outside the class

//TO DO:LAB 4: HOMEWORK PART A: Define build_phase()
function void cpu_driver_c::build_phase(uvm_phase phase);
    super.build_phase(phase);

//Get Virtual Interface in build_phase method of driver, and throw error if virtual interface is not set
    if (!uvm_config_db#(virtual cpu_lv1_interface)::get(this, "","vif", vi_cpu_lv1_if))
        `uvm_fatal("NO_VIF",{"virtual interface must be set for: ",get_full_name(),".vif"});

endfunction: build_phase

//TO DO:LAB 4: HOMEWORK PART A: Define run_phase()
task cpu_driver_c::run_phase(uvm_phase phase);
    `uvm_info(get_type_name(), "RUN Phase", UVM_LOW)
    get_and_drive();
endtask: run_phase

//TO DO:LAB 4: HOMEWORK PART A: Define get_and_drive():gets packets from the sequencer and passes them to the driver.
task cpu_driver_c::get_and_drive();
    //In forever begin
    forever begin
	    // Get new item from the sequencer
        seq_item_port.get_next_item(req); 
	    // Drive the item
        send_to_dut(req);
	    // Communicate item done to the sequencer
        seq_item_port.item_done();
    end
endtask: get_and_drive

task cpu_driver_c::send_to_dut(cpu_transaction_c transaction);
    `uvm_info(get_type_name(), $sformatf("Input Data to Send:\n%s", transaction.sprint()),UVM_LOW);

    // wait time before start of the transaction
    repeat(transaction.wait_cycles) @(posedge vi_cpu_lv1_if.clk);

    vi_cpu_lv1_if.data_bus_cpu_lv1_reg  <= {DATA_WID_LV1{1'bz}};
    vi_cpu_lv1_if.addr_bus_cpu_lv1      <= {ADDR_WID_LV1{1'bz}};
    vi_cpu_lv1_if.cpu_rd                <= 1'b0;
    vi_cpu_lv1_if.cpu_wr                <= 1'b0;

//TO DO:LAB 4: HOMEWORK PART A: Define send_to_dut(): Based on request type, call drv_rd_trans or drv_wr_trans

    if (transaction.request_type == READ_REQ)
        drv_rd_trans(transaction.address, transaction.data);
    if (transaction.request_type == WRITE_REQ)
        drv_wr_trans(transaction.address, transaction.data);

    `uvm_info(get_type_name(), $sformatf("Ended Driving transaction"), UVM_LOW)

endtask : send_to_dut

//TO DO:LAB 4: HOMEWORK PART B: Define task to drive a read transaction to the DUT
task cpu_driver_c::drv_rd_trans(bit [ADDR_WID_LV1-1:0] addr, bit [DATA_WID_LV1-1:0] exp_data);
    reg timeout, got;
    timeout = 1'b0;
    got = 1'b0;

    @(posedge vi_cpu_lv1_if.clk);

//Drive address and cpu_rd
    vi_cpu_lv1_if.cpu_rd <= 1'b1;
    vi_cpu_lv1_if.addr_bus_cpu_lv1 <= addr;

//start timer and wait for data_in_bus_cpu_lv1 till TIME_OUT_VAL is hit
    fork: timeout_check_rd
        begin
            @(posedge vi_cpu_lv1_if.data_in_bus_cpu_lv1)
            //disable timeout check
            got = 1'b1;
        end
        begin
            repeat(`TIME_OUT_VAL) begin
                @(posedge vi_cpu_lv1_if.clk);
                if(got == 1) break;
            end
            if(got == 1) begin
                if(vi_cpu_lv1_if.data_bus_cpu_lv1 !== exp_data) begin
                    $error("TBCHK: at time %t CPU read to addr %h data is %h : expected %h ",$time(),addr,vi_cpu_lv1_if.data_bus_cpu_lv1,exp_data);
                end
            end
            if(got == 0) begin
                timeout = 1;
                $error("TBCHK: timeout of cpu read request");
            end
        end
    join_any

// Release the address bus and cpu_rd,(Other internal signals)
//wait till data_in_bus_cpu_lv1 goes low to indicate end of transaction
//or for another clock if the transaction timed out
    disable fork;
    @(posedge vi_cpu_lv1_if.clk);
    
    vi_cpu_lv1_if.cpu_rd <= 1'b0;
    vi_cpu_lv1_if.data_bus_cpu_lv1_reg <= 32'hz;
    vi_cpu_lv1_if.addr_bus_cpu_lv1 <= 32'hz;

endtask: drv_rd_trans

//TO DO:LAB 4: HOMEWORK PART B: Define task to drive a write transaction to the DUT
task cpu_driver_c::drv_wr_trans(bit [ADDR_WID_LV1-1:0] addr, bit [DATA_WID_LV1-1:0] wrt_data);
    reg timeout, got;
    timeout = 1'b0;
    got = 1'b0;

    @(posedge vi_cpu_lv1_if.clk);

//Drive address, data and cpu_wr
    vi_cpu_lv1_if.cpu_wr <= 1'b1;
    vi_cpu_lv1_if.addr_bus_cpu_lv1 <= addr;
    vi_cpu_lv1_if.data_bus_cpu_lv1_reg <= wrt_data;

//start timer and wait for data_in_bus_cpu_lv1 till TIME_OUT_VAL is hit
    fork: timeout_check_wr
        begin
            @(posedge vi_cpu_lv1_if.data_in_bus_cpu_lv1)
            //disable timeout check
            got = 1'b1;
        end
        begin
            repeat(`TIME_OUT_VAL) begin
                @(posedge vi_cpu_lv1_if.clk);
                if(got == 1) break;
            end
            if(got == 1) begin
                if(vi_cpu_lv1_if.data_bus_cpu_lv1 !== wrt_data) begin
                    $error("TBCHK: at time %t CPU write to addr %h data is %h : expected %h ",$time(),addr,vi_cpu_lv1_if.data_bus_cpu_lv1,wrt_data);
                end
            end
            if(got == 0) begin
                timeout = 1;
                $error("TBCHK: timeout of cpu write request");
            end
        end
    join_any

// Release the address bus and cpu_wr,(Other internal signals)
//wait till data_in_bus_cpu_lv1 goes low to indicate end of transaction
//or for another clock if the transaction timed out
    disable fork;
    @(posedge vi_cpu_lv1_if.clk);
    
    vi_cpu_lv1_if.cpu_wr <= 1'b0;
    vi_cpu_lv1_if.data_bus_cpu_lv1_reg <= 32'hz;
    vi_cpu_lv1_if.addr_bus_cpu_lv1 <= 32'hz;

endtask: drv_wr_trans
