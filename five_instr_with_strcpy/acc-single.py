import pyrtl
# from generate_ir import generate_ir

# memory
i_mem = pyrtl.MemBlock(bitwidth=16, addrwidth=16, name='i_mem') # instruction memory
d_mem = pyrtl.MemBlock(bitwidth=16, addrwidth=16, name='d_mem', max_read_ports=4, max_write_ports=3, asynchronous=True) # data memory

# registers
pc = pyrtl.Register(8, 'pc')
acc = pyrtl.Register(16, 'acc')
str_index = pyrtl.Register(bitwidth=16, name='str_index')
fetch = pyrtl.Register(bitwidth=1, name='fetch', reset_value=1)

# control signals
load = pyrtl.WireVector(bitwidth=1, name='load')
add = pyrtl.WireVector(1, 'add')
branch = pyrtl.WireVector(1, 'branch')
write_mem = pyrtl.WireVector(1, 'write_mem')

strcpy = pyrtl.WireVector(bitwidth=1, name='strcpy')
strncpy = pyrtl.WireVector(bitwidth=1, name='strncpy')

temp = pyrtl.WireVector(bitwidth=16, name='temp')

# wires
ir = pyrtl.WireVector(16, 'ir')
op = pyrtl.WireVector(3, 'op')
addr = pyrtl.WireVector(8, 'addr')

# wires for strcpy & strncpy
str_start_addr = pyrtl.WireVector(bitwidth=6, name='str_start_addr')
str_dest_addr = pyrtl.WireVector(bitwidth=7, name='str_dest_addr')

strn_start_addr = pyrtl.WireVector(bitwidth=4, name='strn_start_addr')
strn_dest_addr = pyrtl.WireVector(bitwidth=5, name='strn_dest_addr')
str_len = pyrtl.WireVector(bitwidth=4, name='str_len')

instr_incr = pyrtl.WireVector(bitwidth=1, name="instr_incr")

# additional wirevectors for 16 bits address
source_addr = pyrtl.WireVector(bitwidth=16, name='source_addr')
dest_addr = pyrtl.WireVector(bitwidth=16, name='dest_addr')

schar_addr = pyrtl.WireVector(bitwidth=16, name="schar_addr")
dchar_addr = pyrtl.WireVector(bitwidth=16, name="dchar_addr")

# fetch
# with pyrtl.conditional_assignment:
#     with fetch:
ir <<= i_mem[pc]

# decode
op <<= ir[0:3]
addr <<= ir[8:]

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

with pyrtl.conditional_assignment:
    # with fetch:
    with op == 0b000: # LOAD addr: ACC <- Mem[addr]
        load |= 1
        write_mem |= 0
        add |= 0
        branch |= 0
        strcpy |= 0
        strncpy |= 0
    with op == 0b001: # ADD addr: ACC <- ACC + Mem[addr]
        load |= 0
        write_mem |= 0
        add |= 1
        branch |= 0
        strcpy |= 0
        strncpy |= 0
    with op == 0b010: # STORE addr: Mem[addr] <- ACC
        load |= 0
        write_mem |= 1
        add |= 0
        branch |= 0
        strcpy |= 0
        strncpy |= 0
    with op == 0b011: # BRZ addr: if (ACC==0) PC <- addr
        load |= 0
        write_mem |= 0
        add |= 0
        branch |= 1
        strcpy |= 0
        strncpy |= 0
    with op == 0b100: # STRCPY: memory[ dest ] <- memory[ source .. \0 ]
        load |= 0
        write_mem |= 0
        add |= 0
        branch |= 0
        strcpy |= 1
        strncpy |= 0
    with op == 0b101: # memory[ dest ] <- memory[ source: source + n ]
        load |= 0
        write_mem |= 0
        add |= 0
        branch |= 0
        strcpy |= 0
        strncpy |= 1

# execute
fetch.next <<= instr_incr

with pyrtl.conditional_assignment:
    with (fetch & (strcpy ^ strncpy)):
        instr_incr |= 0
    with ((~fetch) & strcpy & (temp != 0)):
        instr_incr |= 0
    with ((~fetch) & strncpy & (str_index != str_len - 1)):
        instr_incr |= 0
    with pyrtl.otherwise:
        instr_incr |= 1

schar_addr <<= source_addr + str_index
dchar_addr <<= dest_addr + str_index

with pyrtl.conditional_assignment:
    with (strcpy & ~fetch):
        temp |= d_mem[schar_addr]
        d_mem[dchar_addr] |= temp
        with (temp != 0):
            str_index.next |= str_index + 1
        with pyrtl.otherwise:
            str_index.next |= 0
    with (strncpy & ~fetch):
        temp |= d_mem[schar_addr]
        d_mem[dchar_addr] |= temp
        with (str_index != str_len - 1):
            str_index.next |= str_index + 1
        with pyrtl.otherwise:
            str_index.next |= 0

with pyrtl.conditional_assignment(
        defaults={
            pc: (pc + pyrtl.Const(1, bitwidth=8))[:8],
            acc: acc
        }
):
    with (strcpy & instr_incr):
        acc.next |= 0
    with (strncpy & instr_incr):
        acc.next |= str_len
    with (load & instr_incr):
        acc.next |= d_mem[addr]
    with (add & instr_incr):
        acc.next |= d_mem[addr] + acc
    with (branch & instr_incr):
        with (acc == pyrtl.Const(0, bitwidth=16)):
            pc.next |= addr
    with (~instr_incr):
        pc.next |= pc

# memory write
d_mem[addr] <<= pyrtl.MemBlock.EnabledWrite(acc, write_mem)

#pyrtl.optimize()
#print(pyrtl.working_block())
#ir = generate_ir('acc-cpu', pyrtl.working_block())
#print(ir)

# Start a simulation trace
sim_trace = pyrtl.SimulationTrace()

# Initialize the i_mem with your instructions.
i_mem_init = {}
with open('test-acc1-strncpy-imem.txt', 'r') as fin:
    i = 0
    for line in fin.readlines():
        i_mem_init[i] = int(line, 16)
        i += 1

d_mem_init = {}
with open('test-acc1-strncpy-dmem.txt', 'r') as fin:
    i = 0
    for line in fin.readlines():
        d_mem_init[i] = int(line, 16)
        i += 1

sim = pyrtl.Simulation(tracer=sim_trace, memory_value_map={
    i_mem : i_mem_init,
    d_mem : d_mem_init
})

# Run for an arbitrarily large number of cycles.
for cycle in range(22):
    sim.step({})

# Use render_trace() to debug if your code doesn't work.
sim_trace.render_trace(symbol_len=10, segment_size=1)

# You can also print out the register file or memory like so if you want to debug:
print(list(map(lambda p: hex(p[1]), sim.inspect_mem(d_mem).items())))
print(sim.inspect_mem(d_mem))

# Test Case: test-acc1_imem.txt, test-acc1_dmem.txt; num_cycle = 12
# assert(sim.inspect(acc) == 0x2)
# assert(sim.inspect_mem(d_mem)[2] == 0x2543)
# assert(sim.inspect_mem(d_mem)[4] == 0x2340)
# assert(sim.inspect_mem(d_mem)[5] == 0x203)
# assert(sim.inspect_mem(d_mem)[6] == 0x2543)
# assert(sim.inspect_mem(d_mem)[7] == 0x0)
# assert(sim.inspect_mem(d_mem)[8] == 0x2543)
# assert(sim.inspect_mem(d_mem)[9] == 0x0)
# print("passed!")

# Test Case: test-acc2_imem.txt, test-acc2_dmem.txt; num_cycle = 9
# assert(sim.inspect(acc) == 0x0)
# assert(sim.inspect_mem(d_mem)[0] == 0x1111)
# assert(sim.inspect_mem(d_mem)[1] == 0x2222)
# assert(sim.inspect_mem(d_mem)[2] == 0x0000)
# assert(sim.inspect_mem(d_mem)[3] == 0x0000)
# assert(sim.inspect_mem(d_mem)[4] == 0x1111)
# assert(sim.inspect_mem(d_mem)[5] == 0x2222)
# assert(sim.inspect_mem(d_mem)[6] == 0x0000)
# print("passed!")

# Test Case: test-acc1-load-imem.txt, test-acc1-load-dmem.txt; num_cycle = 11
# There is no assert for this test because it is verified by checking the value of registers in simulation trace.

# Test Case: test-acc1-store-imem.txt, test-acc1-store-dmem.txt; num_cycle = 9
# To verify the in acc, need to go back to the trace
# assert(sim.inspect_mem(d_mem)[2] == 0x5f0e)
# assert(sim.inspect_mem(d_mem)[3] == 0x1432)
# assert(sim.inspect_mem(d_mem)[5] == 0x5abc)
# assert(sim.inspect_mem(d_mem)[9] == 0x0000)
# print("passed!")

# Test Case: test-acc1-add-imem.txt, test-acc1-add-dmem.txt; num_cycle = 12
# assert(sim.inspect_mem(d_mem)[1] == 0x7654)
# assert(sim.inspect_mem(d_mem)[4] == 0xc978)
# assert(sim.inspect(acc) == 0xefea)
# print("passed!")

# Test Case: test-acc1-brz-imem.txt, test-acc1-brz-dmem.txt; num_cycle = 12
# assert(sim.inspect_mem(d_mem)[1] == 0x0101)
# assert(sim.inspect(ir) == 0x01ba)
# assert(sim.inspect(acc) == 0x0101)
# print("passed!")

# Test Case: test-acc1-strcpy-imem.txt, test-acc1-strcpy-dmem.txt.txt; num_cycle = 12
# assert(sim.inspect_mem(d_mem)[0] == 0xab12)
# assert(sim.inspect_mem(d_mem)[1] == 0x3415)
# assert(sim.inspect_mem(d_mem)[2] == 0x2231)
# assert(sim.inspect_mem(d_mem)[3] == 0x0000)
# assert(sim.inspect_mem(d_mem)[4] == 0x0213)
# assert(sim.inspect_mem(d_mem)[5] == 0xab12)
# assert(sim.inspect_mem(d_mem)[6] == 0x2231)
# assert(sim.inspect_mem(d_mem)[7] == 0x0000)
# assert(sim.inspect_mem(d_mem)[8] == 0x0000)
# assert(sim.inspect_mem(d_mem)[9] == 0x0000)
# assert(sim.inspect(acc) == 0x2231)
# print("passed!")

# Test Case: test-acc1-strncpy-imem.txt, test-acc1-strncpy-dmem.txt; num_cycle = 22
assert(sim.inspect_mem(d_mem)[0] == 0x0213)
assert(sim.inspect_mem(d_mem)[1] == 0xa1d4)
assert(sim.inspect_mem(d_mem)[2] == 0x323d)
assert(sim.inspect_mem(d_mem)[3] == 0x0213)
assert(sim.inspect_mem(d_mem)[4] == 0x0000)
assert(sim.inspect_mem(d_mem)[5] == 0x0000)
assert(sim.inspect_mem(d_mem)[6] == 0x0000)
assert(sim.inspect_mem(d_mem)[7] == 0x0000)
assert(sim.inspect_mem(d_mem)[8] == 0x0000)
assert(sim.inspect_mem(d_mem)[9] == 0x0000)
print("passed!")