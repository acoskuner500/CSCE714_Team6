//=====================================================================
// Project: 4 core MESI cache design
// File Name: top.sv
// Description: testbench for cache top with environment
// Designers: Venky & Suru
//=====================================================================
// Notable Change History:
// Date By   Version Change Description
// 2016/12/01  1.0     Initial Release
// 2016/12/02  2.0     Added CPU MESI and LRU interface
//=====================================================================

    `define INST_TOP_CORE inst_cache_lv1_multicore
    `define READ_TIMEOUT 80
    `define WRITE_TIMEOUT 80
    
module top;

    parameter DATA_WID_LV1           = `DATA_WID_LV1       ;
    parameter ADDR_WID_LV1           = `ADDR_WID_LV1       ;
    parameter DATA_WID_LV2           = `DATA_WID_LV2       ;
    parameter ADDR_WID_LV2           = `ADDR_WID_LV2       ;

    reg                           clk;
    wire [DATA_WID_LV2 - 1   : 0] data_bus_lv2_mem;
    wire [ADDR_WID_LV2 - 1   : 0] addr_bus_lv2_mem;
    wire                          data_in_bus_lv2_mem;
    wire                          mem_rd;
    wire                          mem_wr;
    wire                          mem_wr_done;

    wire [3:0]                    cpu_lv1_if_cpu_rd;
    wire [3:0]                    cpu_lv1_if_cpu_wr;
    wire [3:0]                    cpu_lv1_if_cpu_wr_done;
    wire [3:0]                    cpu_lv1_if_data_in_bus_cpu_lv1;

    // Instantiate the interfaces
    cpu_lv1_interface       inst_cpu_lv1_if[0:3](clk);
    system_bus_interface    inst_system_bus_if(clk);

    // Assign internal signals of the interface
    assign inst_system_bus_if.data_bus_lv1_lv2      = inst_cache_top.data_bus_lv1_lv2;
    assign inst_system_bus_if.addr_bus_lv1_lv2      = inst_cache_top.addr_bus_lv1_lv2;
    assign inst_system_bus_if.data_in_bus_lv1_lv2   = inst_cache_top.data_in_bus_lv1_lv2;
    assign inst_system_bus_if.lv2_rd                = inst_cache_top.lv2_rd;
    assign inst_system_bus_if.lv2_wr                = inst_cache_top.lv2_wr;
    assign inst_system_bus_if.lv2_wr_done           = inst_cache_top.lv2_wr_done;
    assign inst_system_bus_if.cp_in_cache           = inst_cache_top.cp_in_cache;
    assign inst_system_bus_if.shared                = inst_cache_top.`INST_TOP_CORE.shared;
    assign inst_system_bus_if.all_invalidation_done = inst_cache_top.`INST_TOP_CORE.all_invalidation_done;
    assign inst_system_bus_if.invalidate            = inst_cache_top.`INST_TOP_CORE.invalidate;
    assign inst_system_bus_if.bus_rd                = inst_cache_top.`INST_TOP_CORE.bus_rd;
    assign inst_system_bus_if.bus_rdx               = inst_cache_top.`INST_TOP_CORE.bus_rdx;

    // instantiate memory golden model
    memory #(
            .DATA_WID(DATA_WID_LV2),
            .ADDR_WID(ADDR_WID_LV2)
            )
             inst_memory (
                            .clk                (clk                ),
                            .data_bus_lv2_mem   (data_bus_lv2_mem   ),
                            .addr_bus_lv2_mem   (addr_bus_lv2_mem   ),
                            .mem_rd             (mem_rd             ),
                            .mem_wr             (mem_wr             ),
                            .mem_wr_done        (mem_wr_done        ),
                            .data_in_bus_lv2_mem(data_in_bus_lv2_mem)
                         );

    // instantiate arbiter golden model
    lrs_arbiter  inst_arbiter (
                                    .clk(clk),
                                    .bus_lv1_lv2_gnt_proc (inst_system_bus_if.bus_lv1_lv2_gnt_proc ),
                                    .bus_lv1_lv2_req_proc (inst_system_bus_if.bus_lv1_lv2_req_proc ),
                                    .bus_lv1_lv2_gnt_snoop(inst_system_bus_if.bus_lv1_lv2_gnt_snoop),
                                    .bus_lv1_lv2_req_snoop(inst_system_bus_if.bus_lv1_lv2_req_snoop),
                                    .bus_lv1_lv2_gnt_lv2  (inst_system_bus_if.bus_lv1_lv2_gnt_lv2  ),
                                    .bus_lv1_lv2_req_lv2  (inst_system_bus_if.bus_lv1_lv2_req_lv2  )
                               );
    assign cpu_lv1_if_cpu_rd                = {inst_cpu_lv1_if[3].cpu_rd,inst_cpu_lv1_if[2].cpu_rd,inst_cpu_lv1_if[1].cpu_rd,inst_cpu_lv1_if[0].cpu_rd};
    assign cpu_lv1_if_cpu_wr                = {inst_cpu_lv1_if[3].cpu_wr,inst_cpu_lv1_if[2].cpu_wr,inst_cpu_lv1_if[1].cpu_wr,inst_cpu_lv1_if[0].cpu_wr};
    assign {inst_cpu_lv1_if[3].cpu_wr_done,inst_cpu_lv1_if[2].cpu_wr_done,inst_cpu_lv1_if[1].cpu_wr_done,inst_cpu_lv1_if[0].cpu_wr_done} = cpu_lv1_if_cpu_wr_done;
    assign {inst_cpu_lv1_if[3].data_in_bus_cpu_lv1,inst_cpu_lv1_if[2].data_in_bus_cpu_lv1,inst_cpu_lv1_if[1].data_in_bus_cpu_lv1,inst_cpu_lv1_if[0].data_in_bus_cpu_lv1} = cpu_lv1_if_data_in_bus_cpu_lv1;

    // instantiate DUT (L1 and L2)
    cache_top inst_cache_top (
                                .clk(clk),
                                .data_bus_cpu_lv1_0     (inst_cpu_lv1_if[0].data_bus_cpu_lv1              ),
                                .addr_bus_cpu_lv1_0     (inst_cpu_lv1_if[0].addr_bus_cpu_lv1              ),
                                .data_bus_cpu_lv1_1     (inst_cpu_lv1_if[1].data_bus_cpu_lv1              ),
                                .addr_bus_cpu_lv1_1     (inst_cpu_lv1_if[1].addr_bus_cpu_lv1              ),
                                .data_bus_cpu_lv1_2     (inst_cpu_lv1_if[2].data_bus_cpu_lv1              ),
                                .addr_bus_cpu_lv1_2     (inst_cpu_lv1_if[2].addr_bus_cpu_lv1              ),
                                .data_bus_cpu_lv1_3     (inst_cpu_lv1_if[3].data_bus_cpu_lv1              ),
                                .addr_bus_cpu_lv1_3     (inst_cpu_lv1_if[3].addr_bus_cpu_lv1              ),
                                .cpu_rd                 (cpu_lv1_if_cpu_rd                          ),
                                .cpu_wr                 (cpu_lv1_if_cpu_wr                          ),
                                .cpu_wr_done            (cpu_lv1_if_cpu_wr_done                     ),
                                .bus_lv1_lv2_gnt_proc   (inst_system_bus_if.bus_lv1_lv2_gnt_proc    ),
                                .bus_lv1_lv2_req_proc   (inst_system_bus_if.bus_lv1_lv2_req_proc    ),
                                .bus_lv1_lv2_gnt_snoop  (inst_system_bus_if.bus_lv1_lv2_gnt_snoop   ),
                                .bus_lv1_lv2_req_snoop  (inst_system_bus_if.bus_lv1_lv2_req_snoop   ),
                                .data_in_bus_cpu_lv1    (cpu_lv1_if_data_in_bus_cpu_lv1             ),
                                .data_bus_lv2_mem       (data_bus_lv2_mem                           ),
                                .addr_bus_lv2_mem       (addr_bus_lv2_mem                           ),
                                .mem_rd                 (mem_rd                                     ),
                                .mem_wr                 (mem_wr                                     ),
                                .mem_wr_done            (mem_wr_done                                ),
                                .bus_lv1_lv2_gnt_lv2    (inst_system_bus_if.bus_lv1_lv2_gnt_lv2     ),
                                .bus_lv1_lv2_req_lv2    (inst_system_bus_if.bus_lv1_lv2_req_lv2     ),
                                .data_in_bus_lv2_mem    (data_in_bus_lv2_mem                        )
                            );

    // System clock generation
    initial begin
        clk = 1'b0;
        forever
            #5 clk = ~clk;
    end

    //Initial begin to run both drive() and check() in parallel.
    initial begin
        fork
            drive();
            check();
        join_none
    end
	
    //Definition of drive() task
    task drive();
        inst_cpu_lv1_if[0].addr_bus_cpu_lv1 <= 32'h0;
        inst_cpu_lv1_if[0].data_bus_cpu_lv1_reg <= 32'hz;
        inst_cpu_lv1_if[0].cpu_rd <= 1'b0;
        inst_cpu_lv1_if[0].cpu_wr <= 1'b0;
        inst_cpu_lv1_if[1].addr_bus_cpu_lv1 <= 32'h0;
        inst_cpu_lv1_if[1].data_bus_cpu_lv1_reg <= 32'hz;
        inst_cpu_lv1_if[1].cpu_rd <= 1'b0;
        inst_cpu_lv1_if[1].cpu_wr <= 1'b0;
        inst_cpu_lv1_if[2].addr_bus_cpu_lv1 <= 32'h0;
        inst_cpu_lv1_if[2].data_bus_cpu_lv1_reg <= 32'hz;
        inst_cpu_lv1_if[2].cpu_rd <= 1'b0;
        inst_cpu_lv1_if[2].cpu_wr <= 1'b0;
        inst_cpu_lv1_if[3].addr_bus_cpu_lv1 <= 32'h0;
        inst_cpu_lv1_if[3].data_bus_cpu_lv1_reg <= 32'hz;
        inst_cpu_lv1_if[3].cpu_rd <= 1'b0;
        inst_cpu_lv1_if[3].cpu_wr <= 1'b0;

        `ifdef TEST1
            //single cpu read miss
            cpu_read_0(32'h4000_1110, 32'haaaa_5555);
            $display("Test Case 1 finished at time %t", $time());
        `endif

        `ifdef TEST2
            //single cpu write miss followed by read on processor0
            cpu_write_0(32'h4000_2110, 32'habcd_0000);
            cpu_read_0(32'h4000_2110, 32'habcd_0000);
            $display("Test Case 2 finished at time %t", $time());
        `endif

        `ifdef TEST3
            //single cpu read miss followed by a write followed by a read on processor0
            cpu_read_0(32'h4000_2115, 32'habcd_8000);
            cpu_write_0(32'h4000_2115,32'habcd_8000);
            cpu_read_0(32'h4000_2115, 32'habcd_8000);
            $display("Test Case 3 finished at time %t", $time());
        `endif     

         `ifdef TEST4
            //Write on Processor 0, followed  by Write on Processor 1, followed by read on processor 0, followed by read on processor 1.
            cpu_write(32'h4000_5555,32'hffff_ffff,inst_cpu_lv1_if[0]);
            cpu_write(32'h4000_5555,32'hcccc_cccc,inst_cpu_lv1_if[1]); 
            cpu_read(32'h4000_5555,32'hcccc_cccc,inst_cpu_lv1_if[0]);
            cpu_read(32'h4000_5555,32'hcccc_cccc,inst_cpu_lv1_if[1]);           

            $display("Test Case 4 finished at time %t", $time());
        `endif 

            

        
	@(posedge clk);
        $finish;
    endtask


    
    //Definition of cpu_read_0() task
    task automatic cpu_read_0(bit [ADDR_WID_LV1-1:0] addr_task, bit [DATA_WID_LV1-1:0] data_task);
       reg timeout, got;
       timeout = 1'b0;
       got = 1'b0;
       @(posedge inst_cpu_lv1_if[0].clk);
       inst_cpu_lv1_if[0].cpu_rd <= 1'b1;
       inst_cpu_lv1_if[0].addr_bus_cpu_lv1 <= addr_task;

       fork: timeout_check_0
           begin
               @(posedge inst_cpu_lv1_if[0].data_in_bus_cpu_lv1)
               //disable timeout check
               got = 1'b1;
           end
           begin
               repeat(`READ_TIMEOUT) begin
                   @(posedge inst_cpu_lv1_if[0].clk);
                   if(got == 1) break;
               end
               if(got == 1) begin
                   if(inst_cpu_lv1_if[0].data_bus_cpu_lv1 !== data_task) begin
                       $error("TBCHK: at time %t CPU0 read to addr %h data is %h : expected %h ",$time(),addr_task,inst_cpu_lv1_if[0].data_bus_cpu_lv1,data_task);
                   end
               end
               if(got == 0) begin
                   timeout = 1;
                   $error("TBCHK: timeout of cpu read request");
               end
           end
       join_any

       @(posedge inst_cpu_lv1_if[0].clk);
       inst_cpu_lv1_if[0].cpu_rd <= 1'b0;
       inst_cpu_lv1_if[0].data_bus_cpu_lv1_reg <= 32'hz;
    endtask

    
    //Definition of cpu_write_0() task
    task automatic cpu_write_0(bit [ADDR_WID_LV1-1:0] addr_task, bit [DATA_WID_LV1-1:0] data_task);
       reg timeout, got;
       timeout = 1'b0;
       got = 1'b0;
       @(posedge inst_cpu_lv1_if[0].clk);
       inst_cpu_lv1_if[0].cpu_wr <= 1'b1;
       inst_cpu_lv1_if[0].addr_bus_cpu_lv1 <= addr_task;
       inst_cpu_lv1_if[0].data_bus_cpu_lv1_reg <=data_task;

       fork: timeout_check_0
           begin
               @(posedge inst_cpu_lv1_if[0].data_in_bus_cpu_lv1)
               //disable timeout check
               got = 1'b1;
           end
           begin
               repeat(`WRITE_TIMEOUT) begin
                   @(posedge inst_cpu_lv1_if[0].clk);
                   if(got == 1) break;
               end
               if(got == 1) begin
                   if(inst_cpu_lv1_if[0].data_bus_cpu_lv1 !== data_task) begin
                       $error("TBCHK: at time %t CPU0 wrote to addr; %h data is %h : expected %h ",$time(),addr_task,inst_cpu_lv1_if[0].data_bus_cpu_lv1,data_task);
                   end
               end
               if(got == 0) begin
                   timeout = 1;
                   $error("TBCHK: timeout of cpu write request");
               end
           end
       join_any

       @(posedge inst_cpu_lv1_if[0].clk);
       inst_cpu_lv1_if[0].cpu_wr <= 1'b0;
       inst_cpu_lv1_if[0].data_bus_cpu_lv1_reg <= 32'hz;
    endtask






    //Definition of cpu_read() task
    task automatic cpu_read(bit [ADDR_WID_LV1-1:0] addr_task, bit [DATA_WID_LV1-1:0] data_task, virtual interface cpu_lv1_interface vif);
       reg timeout, got;
       timeout = 1'b0;
       got = 1'b0;
       @(posedge vif.clk);
       vif.cpu_rd <= 1'b1;
       vif.addr_bus_cpu_lv1 <= addr_task;

       fork: timeout_check_0
           begin
               @(posedge vif.data_in_bus_cpu_lv1)
               //disable timeout check
               got = 1'b1;
           end
           begin
               repeat(`READ_TIMEOUT) begin
                   @(posedge vif.clk);
                   if(got == 1) break;
               end
               if(got == 1) begin
                   if(vif.data_bus_cpu_lv1 !== data_task) begin
                       $error("TBCHK: at time %t CPU0 read to addr %h data is %h : expected %h ",$time(),addr_task,vif.data_bus_cpu_lv1,data_task);
                   end
               end
               if(got == 0) begin
                   timeout = 1;
                   $error("TBCHK: timeout of cpu read request");
               end
           end
       join_any

       @(posedge vif.clk);
       vif.cpu_rd <= 1'b0;
       vif.data_bus_cpu_lv1_reg <= 32'hz;
    endtask


//Definition of cpu_write() task
    task automatic cpu_write(bit [ADDR_WID_LV1-1:0] addr_task, bit [DATA_WID_LV1-1:0] data_task, virtual interface cpu_lv1_interface vif);
       reg timeout, got;
       timeout = 1'b0;
       got = 1'b0;
       @(posedge vif.clk);
       vif.cpu_wr <= 1'b1;
       vif.addr_bus_cpu_lv1 <= addr_task;
       vif.data_bus_cpu_lv1_reg <=data_task;

       fork: timeout_check_0
           begin
               @(posedge vif.data_in_bus_cpu_lv1)
               //disable timeout check
               got = 1'b1;
           end
           begin
               repeat(`WRITE_TIMEOUT) begin
                   @(posedge vif.clk);
                   if(got == 1) break;
               end
               if(got == 1) begin
                   if(vif.data_bus_cpu_lv1 !== data_task) begin
                       $error("TBCHK: at time %t CPU0 write to addr %h data is %h : expected %h ",$time(),addr_task,vif.data_bus_cpu_lv1,data_task);
                   end
               end
               if(got == 0) begin
                   timeout = 1;
                   $error("TBCHK: timeout of cpu write request");
               end
           end
       join_any

       @(posedge vif.clk);
       vif.cpu_wr <= 1'b0;
       vif.data_bus_cpu_lv1_reg <= 32'hz;
    endtask        



    //Definition of check() task
    task check();
        $display("MSG: checker starts");
        forever begin
            @(posedge clk);
            if(!($onehot0(inst_system_bus_if.bus_lv1_lv2_gnt_proc)))
                $error("TBCHK: multiple proc grants");

            if(inst_cpu_lv1_if[0].cpu_rd && inst_cpu_lv1_if[0].cpu_wr)
                    $error("CPU_RD and CPU_WR asserted simultaneously for CPU0");
            if(inst_cpu_lv1_if[1].cpu_rd && inst_cpu_lv1_if[1].cpu_wr)
                    $error("CPU_RD and CPU_WR asserted simultaneously for CPU1");
            if(inst_cpu_lv1_if[2].cpu_rd && inst_cpu_lv1_if[2].cpu_wr)
                    $error("CPU_RD and CPU_WR asserted simultaneously for CPU2");
            if(inst_cpu_lv1_if[3].cpu_rd && inst_cpu_lv1_if[3].cpu_wr)
                    $error("CPU_RD and CPU_WR asserted simultaneously for CPU3");
                    
            //There should not be a request to L2 cache while data is inflight L1 Cache 
            if(inst_cpu_lv1_if[0].data_in_bus_cpu_lv1 && inst_system_bus_if.bus_lv1_lv2_req_proc == 1)
                    $error("Request to L2 while there is data on bus for L1");   
            if(inst_cpu_lv1_if[1].data_in_bus_cpu_lv1 && inst_system_bus_if.bus_lv1_lv2_req_proc == 1)
                    $error("Request to L2 while there is data on bus for L1");   
            if(inst_cpu_lv1_if[2].data_in_bus_cpu_lv1 && inst_system_bus_if.bus_lv1_lv2_req_proc == 1)
                    $error("Request to L2 while there is data on bus for L1");   
            if(inst_cpu_lv1_if[3].data_in_bus_cpu_lv1 && inst_system_bus_if.bus_lv1_lv2_req_proc == 1)
                    $error("Request to L2 while there is data on bus for L1");       
                    
                    
            /* //No data will be written into the Instruction Cache.
            if(inst_cpu_lv1_if[0].addr_bus_cpu_lv1 < 32'h4000_0000 && inst_cpu_lv1_if[0].cpu_wr == 1)
                 $error("An attempt to place/write the data in the Instruction Cache is made.");
            if(inst_cpu_lv1_if[1].addr_bus_cpu_lv1 < 32'h4000_0000 && inst_cpu_lv1_if[0].cpu_wr == 1)
                 $error("An attempt to place/write the data in the Instruction Cache is made.");
            if(inst_cpu_lv1_if[2].addr_bus_cpu_lv1 < 32'h4000_0000 && inst_cpu_lv1_if[0].cpu_wr == 1)
                 $error("An attempt to place/write the data in the Instruction Cache is made.");
            if(inst_cpu_lv1_if[3].addr_bus_cpu_lv1 < 32'h4000_0000 && inst_cpu_lv1_if[0].cpu_wr == 1)
                 $error("An attempt to place/write the data in the Instruction Cache is made."); */
                 
            
            //cpu_wr_done and request to L2 can never be asserted simulatenously (When write to L1 is finished).
            if(inst_cpu_lv1_if[0].cpu_wr_done && inst_system_bus_if.bus_lv1_lv2_req_proc == 1 )
               $error("Request to L2 when L1 write is finished.");
            if(inst_cpu_lv1_if[1].cpu_wr_done && inst_system_bus_if.bus_lv1_lv2_req_proc == 1 )
               $error("Request to L2 when L1 write is finished.");
            if(inst_cpu_lv1_if[2].cpu_wr_done && inst_system_bus_if.bus_lv1_lv2_req_proc == 1 )
               $error("Request to L2 when L1 write is finished.");
            if(inst_cpu_lv1_if[3].cpu_wr_done && inst_system_bus_if.bus_lv1_lv2_req_proc == 1 )
               $error("Request to L2 when L1 write is finished.");
         
        
        end
   endtask

endmodule
