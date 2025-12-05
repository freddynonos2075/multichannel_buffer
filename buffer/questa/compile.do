vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact C:/Users/macmini4/Perforce/systemverilog/buffer/rtl/buffer_elem.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact C:/Users/macmini4/Perforce/systemverilog/buffer/rtl/pointers.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact C:/Users/macmini4/Perforce/systemverilog/buffer/rtl/scfifo.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact C:/Users/macmini4/Perforce/systemverilog/buffer/rtl/buffer_top.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact C:/Users/macmini4/Perforce/systemverilog/buffer/rtl/buffer_read.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact C:/Users/macmini4/Perforce/systemverilog/buffer/sim/tb_axi_stream.sv
vlog +acc -L mtiAvm -L mtiRnm -L mtiOvm -L mtiUvm -L mtiUPF -L infact -sv C:/Users/macmini4/Perforce/systemverilog/buffer/sim/tb_axi_s2.sv

#vsim -onfinish stop -L altera_mf_ver -L work tb_axi_stream
vsim -onfinish stop -L altera_mf_ver -L work tb_axi_s2
do wave.do
run 2us

