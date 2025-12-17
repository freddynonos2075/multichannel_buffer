onerror {resume}
quietly virtual function -install {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers} -env /tb_axi_s2 { &{/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_dout[2], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_dout[1], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_dout[0] }} location_counter
quietly virtual function -install {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers} -env /tb_axi_s2 { &{/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_dout[4], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_dout[3], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_dout[2], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_dout[1], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_dout[0] }} pointer_number
quietly virtual function -install {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers} -env /tb_axi_s2 { &{/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_dout[7], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_dout[6], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_dout[5] }} used_locations_in_segment
quietly virtual signal -install {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers} {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_dout[8]  } last_segment_for_packet
quietly virtual function -install /tb_axi_s2/DUT/buffer_read -env /tb_axi_s2 { &{/tb_axi_s2/DUT/buffer_read/b_raddr[7], /tb_axi_s2/DUT/buffer_read/b_raddr[6], /tb_axi_s2/DUT/buffer_read/b_raddr[5], /tb_axi_s2/DUT/buffer_read/b_raddr[4], /tb_axi_s2/DUT/buffer_read/b_raddr[3] }} segment_number
quietly virtual function -install {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers} -env /tb_axi_s2 { &{/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/rd_dout[4], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/rd_dout[3], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/rd_dout[2], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/rd_dout[1], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/rd_dout[0] }} pointer_number_2
quietly virtual function -install {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers} -env /tb_axi_s2 { &{/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/rd_dout[7], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/rd_dout[6], /tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/rd_dout[5] }} used_locations_in_segment_2
quietly virtual signal -install {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers} {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/rd_dout[8]  } lsat_segment_for_packet_2
quietly virtual signal -install /tb_axi_s2 {/tb_axi_s2/m_axis_tdata[31]  } rcvd_sop
quietly virtual signal -install /tb_axi_s2 {/tb_axi_s2/m_axis_tdata[30]  } rcvd_flow
quietly virtual signal -install /tb_axi_s2 {/tb_axi_s2/m_axis_tdata[29]  } rcvd_data
quietly virtual function -install /tb_axi_s2 -env /tb_axi_s2 { &{/tb_axi_s2/m_axis_tdata[15], /tb_axi_s2/m_axis_tdata[14], /tb_axi_s2/m_axis_tdata[13], /tb_axi_s2/m_axis_tdata[12], /tb_axi_s2/m_axis_tdata[11], /tb_axi_s2/m_axis_tdata[10], /tb_axi_s2/m_axis_tdata[9], /tb_axi_s2/m_axis_tdata[8] }} pkt_number
quietly virtual function -install /tb_axi_s2 -env /tb_axi_s2 { &{/tb_axi_s2/m_axis_tdata[23], /tb_axi_s2/m_axis_tdata[22], /tb_axi_s2/m_axis_tdata[21], /tb_axi_s2/m_axis_tdata[20], /tb_axi_s2/m_axis_tdata[19], /tb_axi_s2/m_axis_tdata[18], /tb_axi_s2/m_axis_tdata[17], /tb_axi_s2/m_axis_tdata[16] }} flow_number
quietly virtual function -install /tb_axi_s2 -env /tb_axi_s2 { &{/tb_axi_s2/m_axis_tdata[23], /tb_axi_s2/m_axis_tdata[22], /tb_axi_s2/m_axis_tdata[21], /tb_axi_s2/m_axis_tdata[20], /tb_axi_s2/m_axis_tdata[19], /tb_axi_s2/m_axis_tdata[18], /tb_axi_s2/m_axis_tdata[17], /tb_axi_s2/m_axis_tdata[16] }} pkt_length
quietly virtual function -install /tb_axi_s2 -env /tb_axi_s2 { &{/tb_axi_s2/m_axis_tdata[27], /tb_axi_s2/m_axis_tdata[26], /tb_axi_s2/m_axis_tdata[25], /tb_axi_s2/m_axis_tdata[24] }} pkt__flow
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_axi_s2/clk
add wave -noupdate /tb_axi_s2/resetn
add wave -noupdate /tb_axi_s2/s_axis_tdata
add wave -noupdate /tb_axi_s2/s_axis_tvalid
add wave -noupdate /tb_axi_s2/s_axis_tready
add wave -noupdate /tb_axi_s2/s_axis_tlast
add wave -noupdate /tb_axi_s2/s_axis_tsideband
add wave -noupdate /tb_axi_s2/rcvd_sop
add wave -noupdate /tb_axi_s2/rcvd_flow
add wave -noupdate /tb_axi_s2/rcvd_data
add wave -noupdate -color gold /tb_axi_s2/pkt_number
add wave -noupdate -color gold /tb_axi_s2/pkt_length
add wave -noupdate -color gold /tb_axi_s2/pkt__flow
add wave -noupdate /tb_axi_s2/m_axis_tdata
add wave -noupdate /tb_axi_s2/m_axis_tvalid
add wave -noupdate /tb_axi_s2/m_axis_tready
add wave -noupdate /tb_axi_s2/m_axis_tlast
TreeUpdate [SetDefaultTree]
quietly WaveActivateNextPane
add wave -noupdate /tb_axi_s2/DUT/skid_buffer/WIDTH
add wave -noupdate /tb_axi_s2/DUT/skid_buffer/clk
add wave -noupdate /tb_axi_s2/DUT/skid_buffer/rst_n
add wave -noupdate /tb_axi_s2/DUT/skid_buffer/in_rd_en
add wave -noupdate /tb_axi_s2/DUT/skid_buffer/in_rd_data
add wave -noupdate /tb_axi_s2/DUT/skid_buffer/out_rd_en
add wave -noupdate /tb_axi_s2/DUT/skid_buffer/out_rd_data
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
add wave -noupdate /tb_axi_s2/DUT/buffer_read/segment_number
add wave -noupdate /tb_axi_s2/DUT/buffer_read/b_raddr
add wave -noupdate /tb_axi_s2/DUT/buffer_read/pointers_rd_req
add wave -noupdate /tb_axi_s2/DUT/buffer_read/pointers_current
add wave -noupdate /tb_axi_s2/DUT/buffer_read/pointer_valid
add wave -noupdate /tb_axi_s2/DUT/buffer_read/pointers_emtpy
add wave -noupdate /tb_axi_s2/DUT/buffer_read/rcvd_state
add wave -noupdate /tb_axi_s2/DUT/buffer_read/data_valid
add wave -noupdate /tb_axi_s2/DUT/buffer_read/s_rvalid
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
add wave -noupdate /tb_axi_s2/DUT/buffer_read/SEGMENT_SIZE_W
add wave -noupdate -divider {pointers[2]}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/rd_req}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/pointer_number_2}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/used_locations_in_segment_2}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/lsat_segment_for_packet_2}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/rd_dout}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/fifo_empty}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[2]/used_pointers/init_done}
add wave -noupdate -divider {pointers[7]}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_req}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/pointer_number}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/used_locations_in_segment}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/last_segment_for_packet}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/rd_dout}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[7]/used_pointers/fifo_empty}
add wave -noupdate -divider {pointers[1]}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[1]/used_pointers/rd_req}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[1]/used_pointers/pointer_number}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[1]/used_pointers/used_locations_in_segment}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[1]/used_pointers/last_segment_for_packet}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[1]/used_pointers/rd_dout}
add wave -noupdate {/tb_axi_s2/DUT/buffer_read/GEN_USED_POINTERS[1]/used_pointers/fifo_empty}
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
WaveRestoreCursors {{Cursor 1} {31322283 ps} 0}
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
WaveRestoreZoom {31016203 ps} {31807159 ps}
