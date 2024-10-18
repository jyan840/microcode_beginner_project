import pyrtl

# memory
# memory = pyrtl.MemBlock(bitwidth=16, addrwidth=16, max_read_ports=1, max_write_ports=1, name='memory', asynchronous=True)
i_mem = pyrtl.MemBlock(bitwidth=16, addrwidth=16, name='i_mem') # instruction memory
d_mem = pyrtl.MemBlock(bitwidth=16, addrwidth=16, name='d_mem', max_read_ports=4, max_write_ports=3, asynchronous=True) # data memory

# registers
pc = pyrtl.Register(16, 'pc')
ir = pyrtl.Register(16, 'ir')
mar = pyrtl.Register(16, 'mar')
mdr = pyrtl.Register(16, 'mdr')
acc = pyrtl.Register(16, 'acc')
temp = pyrtl.Register(16, 'temp')
str_index = pyrtl.Register(bitwidth=16, name='str_index')
bus = pyrtl.WireVector(16, 'bus')

# control signals
acc_in = pyrtl.WireVector(1, 'acc_in')
acc_out = pyrtl.WireVector(1, 'acc_out')
aluadd = pyrtl.WireVector(1, 'aluadd')
ir_in = pyrtl.WireVector(1, 'ir_in')
ir_out = pyrtl.WireVector(1, 'ir_out')
mar_in = pyrtl.WireVector(1, 'mar_in')
mdr_in = pyrtl.WireVector(1, 'mdr_in')
mdr_out = pyrtl.WireVector(1, 'mdr_out')
pc_in = pyrtl.WireVector(1, 'pc_in')
pc_out = pyrtl.WireVector(1, 'pc_out')
pcincr = pyrtl.WireVector(1, 'pcincr')
read = pyrtl.WireVector(1, 'read')
reset = pyrtl.WireVector(1, 'reset')
temp_out = pyrtl.WireVector(1, 'temp_out')
write = pyrtl.WireVector(1, 'write')

# new
read_d = pyrtl.WireVector(bitwidth=1, name="read_d")

#########_additional_signals_for_microcode_#########
next_address = pyrtl.WireVector(bitwidth=5, name='next_address')
branch_via_table = pyrtl.WireVector(bitwidth=1, name="branch_via_table")
or_address_with_accbeq = pyrtl.WireVector(bitwidth=1, name='or_address_with_accbeq')
start_addr_out = pyrtl.WireVector(bitwidth=1, name='start_addr_out')
dest_addr_out = pyrtl.WireVector(bitwidth=1, name='dest_addr_out')
str_index_incr = pyrtl.WireVector(bitwidth=1, name='str_index_incr')
check_end_str = pyrtl.WireVector(bitwidth=1, name='check_end_str')
str_index_out = pyrtl.WireVector(bitwidth=1, name='str_index_out')
check_end_strn = pyrtl.WireVector(bitwidth=1, name='check_end_strn')

#########_end_additional_signals_for_microcode_#########

# time step
T = pyrtl.Register(bitwidth=16, name='T')

# decode
op = pyrtl.WireVector(3, 'op')
addr = pyrtl.WireVector(8, 'addr')
str_start_addr = pyrtl.WireVector(bitwidth=6, name='str_start_addr')
str_dest_addr = pyrtl.WireVector(bitwidth=7, name='str_dest_addr')

# strncpy
strn_start_addr = pyrtl.WireVector(bitwidth=4, name='strn_start_addr')
strn_dest_addr = pyrtl.WireVector(bitwidth=5, name='strn_dest_addr')
str_len = pyrtl.WireVector(bitwidth=4, name='str_len')

# additional wirevectors for 16 bits address
source_addr = pyrtl.WireVector(bitwidth=16, name='source_addr')
dest_addr = pyrtl.WireVector(bitwidth=16, name='dest_addr')

op <<= ir[0:3]
addr <<= ir[8:] # address used in load and store

str_start_addr <<= ir[3:9]
str_dest_addr <<= ir[9:]

str_len <<= ir[3:7]
strn_dest_addr <<= ir[11:]
strn_start_addr <<= ir[7:11]

with pyrtl.conditional_assignment:
    with op == 0b100:
        source_addr |= str_start_addr.zero_extended(16)
        dest_addr |= str_dest_addr.zero_extended(16)
    with pyrtl.otherwise:
        source_addr |= strn_start_addr.zero_extended(16)
        dest_addr |= strn_dest_addr.zero_extended(16)




# control
# acc_in_o, acc_out_o, aluadd_o, ir_in_o, ir_out_o, mar_in_o, mdr_in_o, mdr_out_o, pc_in_o, pc_out_o, pcincr_o, read_o, reset_o, temp_out_o, write_o = Control(op, acc, T)

#########_start_microcode_implementation_#########
control_store_init = {0:0b0000010001000000001000000000,
                        1:0b0000100010000000000000000000,
                        2:0b0000000000110000001100000000,
                        3:0b0001000100000000010000000000,
                        4:0b0000000000000010000000000000,
                        5:0b0000110000000000011000000000,
                        6:0b0000000000000000011100000001,
                        7:0b1000000100000000000000000000,
                        8:0b0000110000000000100100000000,
                        9:0b0000000000000000101000000001,
                        10:0b0110000000000000101100000000,
                        11:0b1000000000001000000000000000,
                        12:0b0000110000000000110100000000,
                        13:0b0100001000000000111000000000,
                        14:0b0000000000000100000000000000,
                        15:0b0000000000000000000010000000,
                        16:0b0000010000000001000101000000,
                        17:0b0000000000000001001000000001,
                        18:0b1000000100000001001100000000,
                        19:0b0000010000000001010000100000,
                        20:0b0100001000000001010100000000,
                        21:0b0000000000000101011000010000,
                        22:0b0000000000000000000000001000,
                        23:0b0000010000000001100001000000,
                        24:0b0000000000000001100100000001,
                        25:0b1000000100000001101000000000,
                        26:0b0000010000000001101100100000,
                        27:0b0100001000000001110000000000,
                        28:0b0000000000000101110100010000,
                        29:0b1000000000000001111000000100,
                        30:0b0000000000000000000000000010,
                      }

CSAR = pyrtl.Register(bitwidth=5, name="CSAR")
CSIR = pyrtl.WireVector(bitwidth=28, name="CSIR")
control_store = pyrtl.RomBlock(bitwidth=28, addrwidth=5, romdata=control_store_init, max_read_ports=1, name='control_store', asynchronous=True)


# hardcoded instruction selection
with pyrtl.conditional_assignment:
    # selection between 6 instructions
    with branch_via_table == 1:
        with op == 0:
            next_address |= 0b00101
        with op == 1:
            next_address |= 0b01000
        with op == 2:
            next_address |= 0b01100
        with op == 3:
            next_address |= 0b01111
        with op == 4:
            next_address |= 0b10000
        with op == 5:
            next_address |= 0b10111

    # brz condition is true
    with or_address_with_accbeq == 1:
        with acc == 0:
            next_address |= 0b00001

    # strcpy loop
    with check_end_str == 1:
        with acc != 0:
            next_address |= 0b10000

    # strncpy loop
    with check_end_strn == 1:
        with acc != str_len:
            next_address |= 0b10111

    with pyrtl.otherwise:
        next_address |= CSIR[8:13]

# microinstruction value update
CSAR.next <<= next_address
CSIR <<= control_store[CSAR]


acc_in <<= CSIR[27]
acc_out <<= CSIR[26]
aluadd <<= CSIR[25]
ir_in <<= CSIR[24]
ir_out <<= CSIR[23]
mar_in <<= CSIR[22]
mdr_in <<= CSIR[21]
mdr_out <<= CSIR[20]
pc_in <<= CSIR[19]
pc_out <<= CSIR[18]
pcincr <<= CSIR[17]
read <<= CSIR[16]

# reset value setup
with pyrtl.conditional_assignment:
    with next_address == 0:
        reset |= 1
    with pyrtl.otherwise:
        reset |= 0


temp_out <<= CSIR[15]
write <<= CSIR[14]
branch_via_table <<= CSIR[13]
or_address_with_accbeq <<= CSIR[7]
start_addr_out <<= CSIR[6]
dest_addr_out <<= CSIR[5]
str_index_incr <<= CSIR[4]
check_end_str <<= CSIR[3]
str_index_out <<= CSIR[2]
check_end_strn <<= CSIR[1]

# new
read_d <<= CSIR[0]

# update str_index
with pyrtl.conditional_assignment:
    with str_index_incr:
        str_index.next |= str_index + 1
    # When any instr is finished, we set str_index to zero
    with next_address == 0:
        str_index.next |= 0
    with pyrtl.otherwise:
        str_index.next |= str_index


#########_end_microcode_implementation_#########

# register-enabling signals (sending)
with pyrtl.conditional_assignment:
    with acc_out:
        bus |= acc
    with ir_out:
        bus |= addr.zero_extended(16)
    with mdr_out:
        bus |= mdr
    with pc_out:
        bus |= pc
    with temp_out:
        bus |= temp
    with str_index_out:
        bus |= str_index
    with start_addr_out:
        bus |= source_addr + str_index
    with dest_addr_out:
        bus |= dest_addr + str_index

# register-enabling signals (receiving)
with pyrtl.conditional_assignment:
    with acc_in:
        acc.next |= bus
    with ir_in:
        ir.next |= bus
    with mar_in:
        mar.next |= bus
    with mdr_in:
        mdr.next |= bus
    with read:
        mdr.next |= i_mem[mar]#[0:8]]
    with read_d:
        mdr.next |= d_mem[mar]

# operation-selection signals
with pyrtl.conditional_assignment:
    with aluadd:
        temp.next |= bus + mdr

# PC update
with pyrtl.conditional_assignment:
    with pcincr:
        pc.next |= pc + 1
    with pc_in:
        pc.next |= bus

# write out to memory
d_mem[mar] <<= pyrtl.MemBlock.EnabledWrite(mdr, write)

# reset step counter
with pyrtl.conditional_assignment:
    with reset:
        T.next |= 0
    with pyrtl.otherwise:
        T.next |= T + 1


# pyrtl.optimize()
# print(pyrtl.working_block())

# Start a simulation trace
sim_trace = pyrtl.SimulationTrace()

# Initialize the i_mem with your instructions.
i_mem_init = {}
with open('test-acc2-imem.txt', 'r') as fin:
    i = 0
    for line in fin.readlines():
        i_mem_init[i] = int(line, 16)
        i += 1

d_mem_init = {}
with open('test-acc2-dmem.txt', 'r') as fin:
    i = 0
    for line in fin.readlines():
        d_mem_init[i] = int(line, 16)
        i += 1


pyrtl.core.set_debug_mode(debug=True)

sim = pyrtl.Simulation(tracer=sim_trace, memory_value_map={
    i_mem : i_mem_init,
    d_mem : d_mem_init
})

# Run for an arbitrarily large number of cycles.
for cycle in range(54):
    sim.step({})

# Use render_trace() to debug if your code doesn't work.
sim_trace.render_trace(symbol_len=10, segment_size=1)

# You can also print out the register file or memory like so if you want to debug:
# print(list(map(lambda p: hex(p[1]), sim.inspect_mem(memory).items())))
print(list(map(lambda p: hex(p[1]), sim.inspect_mem(i_mem).items())))
print(list(map(lambda p: hex(p[1]), sim.inspect_mem(d_mem).items())))


# Test Case: test-acc1_imem.txt, test-acc2_dmem.txt; num_cycle = 75
# assert(sim.inspect(acc) == 0x2)
# assert(sim.inspect_mem(d_mem)[2] == 0x2543)
# assert(sim.inspect_mem(d_mem)[4] == 0x2340)
# assert(sim.inspect_mem(d_mem)[5] == 0x203)
# assert(sim.inspect_mem(d_mem)[6] == 0x2543)
# assert(sim.inspect_mem(d_mem)[7] == 0x0)
# assert(sim.inspect_mem(d_mem)[8] == 0x2543)
# assert(sim.inspect_mem(d_mem)[9] == 0x0)
# print("passed!")

# Test Case: test-acc2_imem.txt, test-acc2_dmem.txt; num_cycle = 54
assert(sim.inspect(acc) == 0x0)
assert(sim.inspect_mem(d_mem)[0] == 0x1111)
assert(sim.inspect_mem(d_mem)[1] == 0x2222)
assert(sim.inspect_mem(d_mem)[2] == 0x0000)
assert(sim.inspect_mem(d_mem)[3] == 0x0000)
assert(sim.inspect_mem(d_mem)[4] == 0x1111)
assert(sim.inspect_mem(d_mem)[5] == 0x2222)
assert(sim.inspect_mem(d_mem)[6] == 0x0000)
print("passed!")










