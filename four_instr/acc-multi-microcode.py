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
next_address = pyrtl.WireVector(bitwidth=4, name='next_address')
branch_via_table = pyrtl.WireVector(bitwidth=1, name="branch_via_table")
or_address_with_accbeq = pyrtl.WireVector(bitwidth=1, name='or_address_with_accbeq')

#########_end_additional_signals_for_microcode_#########

# time step
T = pyrtl.Register(bitwidth=3, name='T')

# decode
op = pyrtl.WireVector(2, 'op')
addr = pyrtl.WireVector(8, 'addr')
op <<= ir[0:2]
addr <<= ir[8:]

# control
# acc_in_o, acc_out_o, aluadd_o, ir_in_o, ir_out_o, mar_in_o, mdr_in_o, mdr_out_o, pc_in_o, pc_out_o, pcincr_o, read_o, reset_o, temp_out_o, write_o = Control(op, acc, T)

#########_start_microcode_implementation_#########
control_store_init = {0:0b00000100010000000100,
            1:0b00001000100000000000,
            2:0b00000000001100000110,
            3:0b00010001000000001000,
            4:0b00000000000000100000,
            5:0b00001100000000001100,
            6:0b00000000000100001110,
            7:0b10000001000000000000,
            8:0b00001100000000010010,
            9:0b00000000000100010100,
            10:0b01100000000000010110,
            11:0b10000000000010000000,
            12:0b00001100000000011010,
            13:0b01000010000000011100,
            14:0b00000000000001000000,
            15:0b00000000000000000001}

CSAR = pyrtl.Register(bitwidth=4, name="CSAR")
CSIR = pyrtl.WireVector(bitwidth=20, name="CSIR")
control_store = pyrtl.RomBlock(bitwidth=20, addrwidth=4, romdata=control_store_init, max_read_ports=1, name='control_store', asynchronous=True)


# hardcoded instruction selection
with pyrtl.conditional_assignment:
    # selection between 4 instructions
    with branch_via_table == 1:
        with op == 0:
            next_address |= 5 #0101
        with op == 1:
            next_address |= 8 #1000
        with op == 2:
            next_address |= 12 #1100
        with op == 3:
            next_address |= 15 #1111

    # brz condition is true
    with or_address_with_accbeq == 1:
        with acc == 0:
            next_address |= 1 #0001

    with pyrtl.otherwise:
        next_address |= CSIR[1:5]

# values update
CSAR.next <<= next_address
CSIR <<= control_store[CSAR]


acc_in <<= CSIR[19]
acc_out <<= CSIR[18]
aluadd <<= CSIR[17]
ir_in <<= CSIR[16]
ir_out <<= CSIR[15]
mar_in <<= CSIR[14]
mdr_in <<= CSIR[13]
mdr_out <<= CSIR[12]
pc_in <<= CSIR[11]
pc_out <<= CSIR[10]
pcincr <<= CSIR[9]
read <<= CSIR[8]

# reset value setup
with pyrtl.conditional_assignment:
    with (next_address == 0) & (or_address_with_accbeq == 0):
        reset |= 1
    with pyrtl.otherwise:
        reset |= 0


temp_out <<= CSIR[7]
write <<= CSIR[6]
branch_via_table <<= CSIR[5]
or_address_with_accbeq <<= CSIR[0]



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
memory[mar[0:8]] <<= pyrtl.MemBlock.EnabledWrite(mdr, write)

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
with open('test-acc1.txt', 'r') as fin:
    i = 0
    for line in fin.readlines():
        i_mem_init[i] = int(line, 16)
        i += 1


pyrtl.core.set_debug_mode(debug=True)

sim = pyrtl.Simulation(tracer=sim_trace, memory_value_map={
    memory : i_mem_init,
})

# Run for an arbitrarily large number of cycles.
for cycle in range(100):
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

# Test Case: test-acc2_store.txt;
# assert(sim.inspect_mem(memory)[0] == 0xc8)
# assert(sim.inspect_mem(memory)[1] == 0x1d9)
# assert(sim.inspect_mem(memory)[2] == 0x215)
# assert(sim.inspect_mem(memory)[3] == 0x4b6)
# print("passed!")

# Test Case: test-acc1_brz.txt; num_cycle=28
# assert(sim.inspect(acc) == 0x602)
# print("passed!")

# Test Case: test-acc2_brz.txt; num_cycle=22
# assert(sim.inspect(acc) == 0x206)
# print("passed!")

# Test Case: test-acc1.txt
assert(sim.inspect(acc) == 0x1001)
print("passed!")

# Test Case: test-acc2.txt
# assert(sim.inspect(acc) == 0x0622)
# assert(sim.inspect_mem(memory)[0] == 0x0622)
# print("passed!")


