import pyrtl

# memory
memory = pyrtl.MemBlock(bitwidth=16, addrwidth=16, max_read_ports=1, max_write_ports=1, name='memory', asynchronous=True)

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
control_store_init = {0:0b000001000100000000100000000,
                        1:0b000010001000000000000000000,
                        2:0b000000000011000000110000000,
                        3:0b000100010000000001000000000,
                        4:0b000000000000001000000000000,
                        5:0b000011000000000001100000000,
                        6:0b000000000001000001110000000,
                        7:0b100000010000000000000000000,
                        8:0b000011000000000010010000000,
                        9:0b000000000001000010100000000,
                        10:0b011000000000000010110000000,
                        11:0b100000000000100000000000000,
                        12:0b000011000000000011010000000,
                        13:0b010000100000000011100000000,
                        14:0b000000000000010000000000000,
                        15:0b000000000000000000001000000,
                        16:0b000001000000000100010100000,
                        17:0b000000000001000100100000000,
                        18:0b100000010000000100110000000,
                        19:0b000001000000000101000010000,
                        20:0b010000100000000101010000000,
                        21:0b000000000000010101100001000,
                        22:0b000000000000000000000000100,
                        23:0b000001000000000110000100000,
                        24:0b000000000001000110010000000,
                        25:0b100000010000000110100000000,
                        26:0b000001000000000110110010000,
                        27:0b010000100000000111000000000,
                        28:0b000000000000010111010000000,
                        29:0b100000000000000111100000010,
                        30:0b000000000000000000000001001,
                      }

CSAR = pyrtl.Register(bitwidth=5, name="CSAR")
CSIR = pyrtl.WireVector(bitwidth=27, name="CSIR")
control_store = pyrtl.RomBlock(bitwidth=27, addrwidth=5, romdata=control_store_init, max_read_ports=1, name='control_store', asynchronous=True)


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
        with acc != str_len - 1:
            next_address |= 0b10111

    with pyrtl.otherwise:
        next_address |= CSIR[7:12]

# microinstruction value update
CSAR.next <<= next_address
CSIR <<= control_store[CSAR]


acc_in <<= CSIR[26]
acc_out <<= CSIR[25]
aluadd <<= CSIR[24]
ir_in <<= CSIR[23]
ir_out <<= CSIR[22]
mar_in <<= CSIR[21]
mdr_in <<= CSIR[20]
mdr_out <<= CSIR[19]
pc_in <<= CSIR[18]
pc_out <<= CSIR[17]
pcincr <<= CSIR[16]
read <<= CSIR[15]

# reset value setup
with pyrtl.conditional_assignment:
    with next_address == 0:
        reset |= 1
    with pyrtl.otherwise:
        reset |= 0


temp_out <<= CSIR[14]
write <<= CSIR[13]
branch_via_table <<= CSIR[12]
or_address_with_accbeq <<= CSIR[6]
start_addr_out <<= CSIR[5]
dest_addr_out <<= CSIR[4]
str_index_incr <<= CSIR[3]
check_end_str <<= CSIR[2]
str_index_out <<= CSIR[1]
check_end_strn <<= CSIR[0]

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
        mdr.next |= memory[mar]#[0:8]]

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
memory[mar] <<= pyrtl.MemBlock.EnabledWrite(mdr, write)

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
with open('test-acc1_strncpy.txt', 'r') as fin:
    i = 0
    for line in fin.readlines():
        i_mem_init[i] = int(line, 16)
        i += 1


pyrtl.core.set_debug_mode(debug=True)

sim = pyrtl.Simulation(tracer=sim_trace, memory_value_map={
    memory : i_mem_init,
})

# Run for an arbitrarily large number of cycles.
for cycle in range(13):
    sim.step({})

# Use render_trace() to debug if your code doesn't work.
sim_trace.render_trace(symbol_len=10, segment_size=1)

# You can also print out the register file or memory like so if you want to debug:
print(list(map(lambda p: hex(p[1]), sim.inspect_mem(memory).items())))
print(sim.inspect_mem(memory))
print(sim.inspect_mem(control_store))

# Test Case: test-acc1_add.txt; num_cycle = 25
# assert(sim.inspect(acc) == 0x152)
# print("passed!")

# Test Case: test-acc2_add.txt; num_cycle = 41
# assert(sim.inspect(acc) == 0x2603)
# print("passed!")

# Test Case: test-acc1_load.txt; num_cycle = 16*7+1
# assert(sim.inspect(acc) == 0x0000)
# print("passed!")

# Test Case: test-acc2_load.txt; num_cycle = 15
# assert(sim.inspect(acc) == 0xabc0)
# print("passed!")

# Test Case: test-acc1_store.txt;
# assert(sim.inspect_mem(memory)[0] == 0x91)
# assert(sim.inspect_mem(memory)[1] == 0x282)
# assert(sim.inspect_mem(memory)[2] == 0x1ea)
# print("passed!")

# Test Case: test-acc2_store(m).txt;
# assert(sim.inspect_mem(memory)[0] == 0xc8)
# assert(sim.inspect_mem(memory)[1] == 0x1d9)
# assert(sim.inspect_mem(memory)[2] == 0x211)
# assert(sim.inspect_mem(memory)[3] == 0x4b2)
# print("passed!")

# Test Case: test-acc1_brz(m).txt; num_cycle=28
# assert(sim.inspect(acc) == 0x602)
# print("passed!")

# Test Case: test-acc2_brz.txt; num_cycle=22
# assert(sim.inspect(acc) == 0x206)
# print("passed!")

# Test Case: test-acc1.txt
# assert(sim.inspect(acc) == 0x1001)
# print("passed!")

# Test Case: test-acc2.txt
# assert(sim.inspect(acc) == 0x0622)
# assert(sim.inspect_mem(memory)[0] == 0x0622)
# print("passed!")

# Test Case: test-acc1_strcpy.txt; num_cycle=22
# assert(sim.inspect_mem(memory)[0] == 0xabab)
# assert(sim.inspect_mem(memory)[1] == 0x0)
# assert(sim.inspect(ir) == 0x0)
# print("passed!")



# Test Case: test-acc2_strcpy.txt; num_cycle=50
# assert(sim.inspect_mem(memory)[8] == 0x1004)
# assert(sim.inspect_mem(memory)[9] == 0x1234)
# assert(sim.inspect_mem(memory)[10] == 0x5678)
# assert(sim.inspect_mem(memory)[11] == 0x9abc)
# assert(sim.inspect_mem(memory)[12] == 0xdef0)
# assert(sim.inspect_mem(memory)[13] == 0x0000)
# assert(sim.inspect(ir) == 0x1234)
# print("passed!")

# Test Case: test-acc3.txt; num_cycle=78
# assert(sim.inspect_mem(memory)[5] == 0x01e9)
# assert(sim.inspect_mem(memory)[6] == 0x0000)
# assert(sim.inspect(acc) == 0x0901)
# print("passed!")

# Test Case: test-acc4.txt; num_cycle=134
# assert(sim.inspect_mem(memory)[7] == 0x0001)
# assert(sim.inspect_mem(memory)[8] == 0x0001)
# assert(sim.inspect_mem(memory)[9] == 0x0daa)
# assert(sim.inspect_mem(memory)[10] == 0x0200)
# assert(sim.inspect_mem(memory)[11] == 0x0001)
# assert(sim.inspect_mem(memory)[12] == 0x0000)
# assert(sim.inspect_mem(memory)[13] == 0x0702)
# assert(sim.inspect(acc) == 0x0001)
# print("passed!")

# Test Case: test-acc5.txt; num_cycle=81
# assert(sim.inspect_mem(memory)[2] == 0x07c1)
# assert(sim.inspect_mem(memory)[3] == 0x0201)
# assert(sim.inspect_mem(memory)[4] == 0x0902)
# assert(sim.inspect_mem(memory)[5] == 0x0000)
# assert(sim.inspect_mem(memory)[9] == 0x1475)
# assert(sim.inspect(acc) == 0x04f3)
# print("passed!")

# Test Case: test-acc1_strncpy.txt; num_cycle =13
assert(sim.inspect_mem(memory)[1] == 0x080d)
print("passed!")

# Test Case: test-acc2_strncpy.txt; num_cycle=36
# assert(sim.inspect_mem(memory)[0] == 0x0350)
# assert(sim.inspect_mem(memory)[1] == 0x0441)
# assert(sim.inspect_mem(memory)[2] == 0x0195)
# assert(sim.inspect_mem(memory)[3] == 0x0350)
# assert(sim.inspect_mem(memory)[4] == 0x0441)
# print("passed!")

# Test Case: test-acc3_strncpy.txt; num_cycle=89
# assert(sim.inspect_mem(memory)[5] == 0x0168)
# assert(sim.inspect_mem(memory)[6] == 0x0041)
# assert(sim.inspect_mem(memory)[7] == 0x0302)
# assert(sim.inspect(acc) == 0x0311)
# print("passed!")

# Test Case: test-acc4_strncpy.txt; num_cycle=179
# assert(sim.inspect_mem(memory)[0] == 0x002c)
# assert(sim.inspect_mem(memory)[1] == 0x0688)
# assert(sim.inspect_mem(memory)[2] == 0x539d)
# assert(sim.inspect_mem(memory)[3] == 0x0303)
# assert(sim.inspect_mem(memory)[4] == 0x0000)
# assert(sim.inspect_mem(memory)[10] == 0x539d)
# assert(sim.inspect_mem(memory)[11] == 0x0303)
# assert(sim.inspect_mem(memory)[12] == 0x0000)
# assert(sim.inspect(acc) == 0x002c)
# print("passed!")