import pyrtl
# from generate_ir import generate_ir

# memory
# memory = pyrtl.MemBlock(bitwidth=16, addrwidth=16, name='i_mem')
i_mem = pyrtl.MemBlock(bitwidth=16, addrwidth=16, name='i_mem')
d_mem = pyrtl.MemBlock(bitwidth=16, addrwidth=16, name='d_mem', max_write_ports=2, max_read_ports=3, asynchronous=True)

# registers
pc = pyrtl.Register(16, 'pc')
acc = pyrtl.Register(16, 'acc')

# new registers for strcpy & strncpy
T = pyrtl.Register(bitwidth=16, name='T')
str_index = pyrtl.Register(bitwidth=16, name='str_index')
mar = pyrtl.Register(bitwidth=16, name='mar')
mdr = pyrtl.Register(bitwidth=16, name='mdr')

# control signals
load = pyrtl.WireVector(bitwidth=1, name='load')
add = pyrtl.WireVector(1, 'add')
branch = pyrtl.WireVector(1, 'branch')
write_mem = pyrtl.WireVector(1, 'write_mem')

# new control signals
start_addr_out = pyrtl.WireVector(bitwidth=1, name='start_addr_out')
dest_addr_out = pyrtl.WireVector(bitwidth=1, name='dest_addr_out')
mar_in = pyrtl.WireVector(bitwidth=1, name='mar_in')
mdr_in = pyrtl.WireVector(bitwidth=1, name='mdr_in')
mdr_out = pyrtl.WireVector(bitwidth=1, name='mdr_out')
acc_in = pyrtl.WireVector(bitwidth=1, name='acc_in')
acc_out = pyrtl.WireVector(bitwidth=1, name='acc_out')
read = pyrtl.WireVector(bitwidth=1, name='read')
write = pyrtl.WireVector(bitwidth=1, name='write')
str_index_incr = pyrtl.WireVector(bitwidth=1, name='str_index_incr')
str_index_out = pyrtl.WireVector(bitwidth=1, name='str_index_out')
check_end_str = pyrtl.WireVector(bitwidth=1, name='check_end_str')
check_end_strn = pyrtl.WireVector(bitwidth=1, name='check_end_strn')
inloop = pyrtl.WireVector(bitwidth=1, name='inloop')
reset = pyrtl.WireVector(bitwidth=1, name='reset')

# wires
ir = pyrtl.WireVector(16, 'ir')
op = pyrtl.WireVector(3, 'op')
addr = pyrtl.WireVector(8, 'addr')
bus = pyrtl.WireVector(bitwidth=16, name='bus')

# strcpy
str_start_addr = pyrtl.WireVector(bitwidth=6, name='str_start_addr')
str_dest_addr = pyrtl.WireVector(bitwidth=7, name='str_dest_addr')

# strncpy
strn_start_addr = pyrtl.WireVector(bitwidth=4, name='strn_start_addr')
strn_dest_addr = pyrtl.WireVector(bitwidth=5, name='strn_dest_addr')
str_len = pyrtl.WireVector(bitwidth=4, name='str_len')

# additional wirevectors for 16 bits address
source_addr = pyrtl.WireVector(bitwidth=16, name='source_addr')
dest_addr = pyrtl.WireVector(bitwidth=16, name='dest_addr')

# fetch
ir <<= i_mem[pc]

# decode
op <<= ir[0:3]
addr <<= ir[8:]

# new decode
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

def control(op, timestep):
    load = pyrtl.WireVector(1)
    add = pyrtl.WireVector(1)
    branch = pyrtl.WireVector(1)
    write_mem = pyrtl.WireVector(1)

    start_addr_out = pyrtl.WireVector(1)
    dest_addr_out = pyrtl.WireVector(1)
    mar_in = pyrtl.WireVector(1)
    mdr_in = pyrtl.WireVector(1)
    mdr_out = pyrtl.WireVector(1)
    acc_in = pyrtl.WireVector(1)
    acc_out = pyrtl.WireVector(1)
    read = pyrtl.WireVector(1)
    write = pyrtl.WireVector(1)
    str_index_incr = pyrtl.WireVector(1)
    str_index_out = pyrtl.WireVector(1)
    check_end_str = pyrtl.WireVector(1)
    check_end_strn = pyrtl.WireVector(1)

    inloop = pyrtl.WireVector(1)
    reset = pyrtl.WireVector(1)

    load <<= (op == 0b000)
    add <<= (op == 0b001)
    branch <<= (op == 0b011)
    write_mem <<= (op == 0b010)

    # strcpy & strncpy
    # timestep 0 - 5
    start_addr_out <<= ((op == 0b100) ^ (op == 0b101)) & (timestep == 0)
    mar_in <<= ((op == 0b100) ^ (op == 0b101)) & ((timestep == 0) ^ (timestep == 3))
    read <<= ((op == 0b100) ^ (op == 0b101)) & (timestep == 1)
    mdr_out <<= ((op == 0b100) ^(op == 0b101)) & (timestep == 2)
    acc_in <<= (((op == 0b100) ^ (op == 0b101)) & (timestep == 2)) ^ ((op == 0b101) & (timestep == 6))
    dest_addr_out <<= ((op == 0b100) ^ (op == 0b101)) & (timestep == 3)
    acc_out <<= ((op == 0b100) ^ (op == 0b101)) & (timestep == 4)
    mdr_in <<= ((op == 0b100) ^ (op == 0b101)) & (timestep == 4)
    write <<= ((op == 0b100) ^ (op == 0b101)) & (timestep == 5)
    str_index_incr <<= ((op == 0b100) ^(op == 0b101)) & (timestep == 5)

    # timestep 6 - 7
    check_end_str <<= (op == 0b100) & (timestep == 6)
    str_index_out <<= (op == 0b101) & (timestep == 6)
    check_end_strn <<= (op == 0b101) & (timestep == 7)

    inloop <<= (op == 0b100) ^ (op == 0b101)
    reset <<= ((op != 0b100) & (op != 0b101)) ^ ((op == 0b100) & (timestep == 6)) ^ ((op == 0b101) & (timestep == 7))

    return load, add, branch, write_mem, start_addr_out, mar_in, read, mdr_out, acc_in, dest_addr_out, acc_out, mdr_in, write, str_index_incr, check_end_str, str_index_out, check_end_strn, inloop, reset

load_o, add_o, branch_o, write_mem_o, start_addr_out_o, mar_in_o, read_o, mdr_out_o, acc_in_o, dest_addr_out_o, acc_out_o, mdr_in_o, write_o, str_index_incr_o, check_end_str_o, str_index_out_o, check_end_strn_o, inloop_o, reset_o = control(op, T)

load <<= load_o
add <<= add_o
branch <<= branch_o
write_mem <<= write_mem_o
start_addr_out <<= start_addr_out_o
mar_in <<= mar_in_o
read <<= read_o
mdr_out <<= mdr_out_o
acc_in <<= acc_in_o
dest_addr_out <<= dest_addr_out_o
acc_out <<= acc_out_o
mdr_in <<= mdr_in_o
write <<= write_o
str_index_incr <<= str_index_incr_o
check_end_str <<= check_end_str_o
str_index_out <<= str_index_out_o
check_end_strn <<= check_end_strn_o
inloop <<= inloop_o
reset <<= reset_o

# execute
# register-enabling signals(sending)
with pyrtl.conditional_assignment:
    with start_addr_out:
        bus |= source_addr + str_index
    with dest_addr_out:
        bus |= dest_addr + str_index
    with mdr_out:
        bus |= mdr
    with acc_out:
        bus |= acc
    with str_index_out:
        bus |= str_index

# register-enabling signals(receiving)(not include acc_in)
with pyrtl.conditional_assignment:
    with mar_in:
        mar.next |= bus
    with mdr_in:
        mdr.next |= bus
    with read:
        mdr.next |= d_mem[mar]

# acc
with pyrtl.conditional_assignment:
    with load:
        acc.next |= d_mem[addr]
    with add:
        acc.next |= d_mem[addr] + acc
    with acc_in:
        acc.next |= bus

# pc
with pyrtl.conditional_assignment:
    with branch:
        with (acc == pyrtl.Const(0, bitwidth=16)):
            pc.next |= addr

    # In strcpy and strncpy, pc should not update unless the check condition is true
    with inloop:
        with ((~check_end_str) & (~check_end_strn)) ^ (check_end_str & (acc != 0))  ^ (check_end_strn & (acc != str_len)):
            pc.next |= pc
        with pyrtl.otherwise:
            pc.next |= pc + 1
    with pyrtl.otherwise:
        pc.next |= pc + 1

# timestep
with pyrtl.conditional_assignment:
    with reset:
        T.next |= 0
    with pyrtl.otherwise:
        T.next |= T + 1

# memory write
d_mem[addr] <<= pyrtl.MemBlock.EnabledWrite(acc, write_mem) # store instruction
d_mem[mar] <<= pyrtl.MemBlock.EnabledWrite(mdr, write) # write micro-operation

# update str_index
with pyrtl.conditional_assignment:
    with str_index_incr:
        str_index.next |= str_index + 1
    with ((check_end_str) & (acc == 0)) ^ ((check_end_strn) & (acc == str_len)):
        str_index.next |= 0
    with pyrtl.otherwise:
        str_index.next |= str_index

#pyrtl.optimize()
#print(pyrtl.working_block())
#ir = generate_ir('acc-cpu', pyrtl.working_block())
#print(ir)

# Start a simulation trace
sim_trace = pyrtl.SimulationTrace()

# Initialize the i_mem with your instructions.
i_mem_init = {}
with open('test-acc1-imem.txt', 'r') as fin:
    i = 0
    for line in fin.readlines():
        i_mem_init[i] = int(line, 16)
        i += 1

d_mem_init = {}
with open('test-acc1-dmem.txt', 'r') as fin:
    i = 0
    for line in fin.readlines():
        d_mem_init[i] = int(line, 16)
        i += 1

sim = pyrtl.Simulation(tracer=sim_trace, memory_value_map={
    i_mem : i_mem_init,
    d_mem : d_mem_init
})

# Run for an arbitrarily large number of cycles.
for cycle in range(50):
    sim.step({})

# Use render_trace() to debug if your code doesn't work.
sim_trace.render_trace(symbol_len=10, segment_size=1)

# You can also print out the register file or memory like so if you want to debug:
print(list(map(lambda p: hex(p[1]), sim.inspect_mem(d_mem).items())))
print(sim.inspect(acc))
