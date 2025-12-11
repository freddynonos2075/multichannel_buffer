onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_axi_s2/clk
add wave -noupdate /tb_axi_s2/resetn
add wave -noupdate /tb_axi_s2/s_axis_tdata
add wave -noupdate /tb_axi_s2/s_axis_tvalid
add wave -noupdate /tb_axi_s2/s_axis_tready
add wave -noupdate /tb_axi_s2/s_axis_tlast
add wave -noupdate /tb_axi_s2/s_axis_tsideband
add wave -noupdate /tb_axi_s2/m_axis_tdata
add wave -noupdate /tb_axi_s2/m_axis_tvalid
add wave -noupdate /tb_axi_s2/m_axis_tready
add wave -noupdate /tb_axi_s2/m_axis_tlast
TreeUpdate [SetDefaultTree]
quietly WaveActivateNextPane
add wave -noupdate /tb_axi_s2/DUT/data_in
add wave -noupdate /tb_axi_s2/DUT/valid_in
add wave -noupdate /tb_axi_s2/DUT/buffer_wr_addr
add wave -noupdate /tb_axi_s2/DUT/buffer_rd_addr
add wave -noupdate /tb_axi_s2/DUT/buffer_dout
add wave -noupdate -divider {New Divider}
add wave -noupdate /tb_axi_s2/DUT/buffer_read/clk
add wave -noupdate /tb_axi_s2/DUT/buffer_read/rstn
add wave -noupdate /tb_axi_s2/DUT/buffer_read/used_pointer
add wave -noupdate /tb_axi_s2/DUT/buffer_read/used_pointer_valid
add wave -noupdate /tb_axi_s2/DUT/buffer_read/used_pointer_flow
add wave -noupdate /tb_axi_s2/DUT/buffer_read/s_rready
add wave -noupdate /tb_axi_s2/DUT/buffer_read/s_rvalid
add wave -noupdate /tb_axi_s2/DUT/buffer_read/s_rlast
add wave -noupdate /tb_axi_s2/DUT/buffer_read/freed_pointer
add wave -noupdate /tb_axi_s2/DUT/buffer_read/freed_pointer_valid
add wave -noupdate /tb_axi_s2/DUT/buffer_read/p_tready
add wave -noupdate /tb_axi_s2/DUT/buffer_read/b_raddr
add wave -noupdate /tb_axi_s2/DUT/buffer_read/pointers_rd_req
add wave -noupdate /tb_axi_s2/DUT/buffer_read/pointers_current
add wave -noupdate /tb_axi_s2/DUT/buffer_read/pointer_valid
add wave -noupdate /tb_axi_s2/DUT/buffer_read/pointers_emtpy
add wave -noupdate /tb_axi_s2/DUT/buffer_read/pointers_rd_req_r
add wave -noupdate /tb_axi_s2/DUT/buffer_read/location_counter
add wave -noupdate /tb_axi_s2/DUT/buffer_read/location_counter_r
add wave -noupdate /tb_axi_s2/DUT/buffer_read/current_flow_valid
add wave -noupdate /tb_axi_s2/DUT/buffer_read/current_selected_flow
add wave -noupdate /tb_axi_s2/DUT/buffer_read/next_flow_valid
add wave -noupdate /tb_axi_s2/DUT/buffer_read/next_selected_flow
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dwrr_init_done
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dwrr_next_credit_req
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dwrr_next_credit_value
add wave -noupdate /tb_axi_s2/DUT/buffer_read/rr_counter
add wave -noupdate /tb_axi_s2/DUT/buffer_read/flow_credits
TreeUpdate [SetDefaultTree]
quietly WaveActivateNextPane
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dww_credits/DEPTH_W
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dww_credits/FLOW_W
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dww_credits/MAX_CREDIT_W
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dww_credits/FIFO_DEPTH
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dww_credits/clk
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dww_credits/rstn
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dww_credits/rd_req
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dww_credits/rd_out
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dww_credits/init_done
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dww_credits/pointer_counter
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dww_credits/fifo_wr_req
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dww_credits/fifo_wr_din
add wave -noupdate /tb_axi_s2/DUT/buffer_read/dww_credits/ram_inst/altera_syncram_inst/mem_data
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {626020 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 293
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 2
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {1664250 ps}
