//=====================================================================
// Project: 4 core MESI cache design
// File Name: cpu_seqs_c.sv
// Description: cpu sequences for a single core cpu component
// Designers: Venky & Suru
//=====================================================================

class cpu_base_seq extends uvm_sequence #(cpu_transaction_c);
    `uvm_object_utils(cpu_base_seq)
    
    function new (string name = "cpu_base_seq");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "executing 1 cpu transaction", UVM_LOW)
//TO DO:LAB 4: HOMEWORK PART C: Complete this sequence to do a read operation
        `uvm_do_with(req, {request_type == READ_REQ;});
    endtask

    task pre_body();
        if(starting_phase != null) begin
            starting_phase.raise_objection(this, get_type_name());
            `uvm_info(get_type_name(), "raise_objection", UVM_LOW)
        end
    endtask : pre_body

    task post_body();
        if(starting_phase != null) begin
            starting_phase.drop_objection(this, get_type_name());
            `uvm_info(get_type_name(), "drop_objection", UVM_LOW)
        end
    endtask : post_body

endclass : cpu_base_seq

class five_trans_seq extends uvm_sequence #(cpu_transaction_c);
//TO DO:LAB 4: HOMEWORK PART C: Write a new sequence to do 5 read transactions
`uvm_object_utils(five_trans_seq)
    
    function new (string name = "five_trans_seq");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "executing 5 cpu transactions", UVM_LOW)
        repeat (5)
            `uvm_do_with(req, {request_type == READ_REQ; address < 32'h4000_0000; access_cache_type == ICACHE_ACC;});
    endtask

    task pre_body();
        if(starting_phase != null) begin
            starting_phase.raise_objection(this, get_type_name());
            `uvm_info(get_type_name(), "raise_objection", UVM_LOW)
        end
    endtask : pre_body

    task post_body();
        if(starting_phase != null) begin
            starting_phase.drop_objection(this, get_type_name());
            `uvm_info(get_type_name(), "drop_objection", UVM_LOW)
        end
    endtask : post_body

endclass : five_trans_seq
