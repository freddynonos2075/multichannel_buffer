
set env(BASE_LOC) C:/Users/macmini4/github/multichannel_buffer/buffer


vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact     $env(BASE_LOC)/rtl/buffer_elem.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact     $env(BASE_LOC)/rtl/pointers.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact     $env(BASE_LOC)/rtl/scfifo.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact     $env(BASE_LOC)/rtl/buffer_top.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact     $env(BASE_LOC)/rtl/buffer_read.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact     $env(BASE_LOC)/rtl/dwrr_credits.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact     $env(BASE_LOC)/rtl/buffer_read_multi_flow.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact     $env(BASE_LOC)/rtl/rd_latency1_to_0.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact     $env(BASE_LOC)/sim/tb_axi_stream.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact -sv $env(BASE_LOC)/sim/tb_axi_s2.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact     $env(BASE_LOC)/rtl/axi4lite_if.sv

#vsim -onfinish stop -L altera_mf_ver -L work tb_axi_stream
vsim -onfinish stop -L altera_mf_ver -L work tb_axi_s2
do wave.do
run 2us

