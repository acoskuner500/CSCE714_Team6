//include directories
    -incdir ../uvm
    -incdir ../test

//compile design files
    ../design/lv2/def_lv2.svp
    ../design/common/addr_segregator_proc.svp
    ../design/lv2/lru_block_lv2.svp
    ../design/common/blk_hit_proc_md.svp
    ../design/common/access_blk_proc_md.svp
    ../design/common/free_blk_md.svp
    ../design/common/blk_to_be_accessed_md.svp
    ../design/lv2/main_func_lv2.svp
    ../design/lv2/cache_block_lv2.svp
    ../design/lv2/cache_controller_lv2.svp
    ../design/lv2/cache_wrapper_lv2.svp

    ../design/lv1/def_lv1.svp
    ../design/lv1/access_blk_snoop_md.svp
    ../design/lv1/addr_segregator_snoop.svp
    ../design/lv1/blk_hit_snoop_md.svp
    ../design/lv1/blk_to_be_accessed_snoop_md.svp
    ../design/lv1/lru_block_lv1.svp
    ../design/lv1/mesi_fsm_lv1.svp
    ../design/lv1/main_func_lv1_il.svp
    ../design/lv1/main_func_lv1_dl.svp
    ../design/lv1/cache_controller_lv1_il.svp
    ../design/lv1/cache_controller_lv1_dl.svp
    ../design/lv1/cache_block_lv1_il.svp
    ../design/lv1/cache_block_lv1_dl.svp
    ../design/lv1/cache_wrapper_lv1_il.svp
    ../design/lv1/cache_wrapper_lv1_dl.svp
    ../design/lv1/cache_lv1_unicore.svp
    ../design/lv1/cache_lv1_multicore.svp
    ../design/cache_top.sv

//golden arbiter and memory files
    ../gold/memory.sv
    ../gold/lrs_arbiter.sv

//compile testbench files
    ../uvm/cpu_lv1_interface.sv
    ../uvm/system_bus_interface.sv
    ../uvm/cpu_pkg.sv
    ../uvm/top.sv
