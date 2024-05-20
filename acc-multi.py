import pyrtl

def Control(op, acc, timestep):
    acc_in = pyrtl.WireVector(1)
    acc_out = pyrtl.WireVector(1)
    aluadd = pyrtl.WireVector(1)
    ir_in = pyrtl.WireVector(1)
    ir_out = pyrtl.WireVector(1)
    mar_in = pyrtl.WireVector(1)
    mdr_in = pyrtl.WireVector(1)
    mdr_out = pyrtl.WireVector(1)
    pc_in = pyrtl.WireVector(1)
    pc_out = pyrtl.WireVector(1)
    pcincr = pyrtl.WireVector(1)
    read = pyrtl.WireVector(1)
    reset = pyrtl.WireVector(1)
    temp_out = pyrtl.WireVector(1)
    write = pyrtl.WireVector(1)

    # ACC_in = (load & T6) + (add & T7)
    acc_in <<= ((op==0) & (timestep==5)) ^ ((op==1) & (timestep==6))
    # ACC_out = (store & T5) + (add & T6)
    acc_out <<= ((op==2) & (timestep==4)) ^ ((op==1) & (timestep==5))
    # aluadd = add & T6
    aluadd <<= (op==1) & (timestep==5)
    # IR_in = T2
    ir_in <<= timestep==2
    # IR_out(addr part) = (load & T4) + (add & T4) + (store & T4) + (brz & acceq0 & T4)
    ir_out <<= ((op==0) & (timestep==3)) ^ ((op==1) & (timestep==3)) ^ ((op==2) & (timestep==3)) ^ ((op==3) & (timestep==3) & (acc==0))
    # MAR_in = T0 + (load & T4) + (add & T4) + (store & T4)
    mar_in <<= (timestep==0) ^ ((op==0) & (timestep==3)) ^ ((op==1) & (timestep==3)) ^ ((op==2) & (timestep==3))
    # MDR_in = store & T5
    mdr_in <<= ((op==2) & (timestep==4))
    # MDR_out = T2 + (load & T6)
    mdr_out <<= (timestep==2) ^ ((op==0) & (timestep==5))
    # PC_in = brz & acceq0 & T4
    pc_in <<= ((op==3) & (timestep==3) & (acc==0))
    # PC_out = T0
    pc_out <<= timestep==0
    # pcincr = T1
    pcincr <<= timestep==1
    # read = T1 + (load & T5) + (add & T5)
    read <<= (timestep==1) ^ ((op==0) & (timestep==4)) ^ ((op==1) & (timestep==4))
    # reset = (load & T6) + (add & T7) + (store & T6) + (brz & T4)
    reset <<= ((op==0) & (timestep==5)) ^ ((op==1) & (timestep==6)) ^ ((op==2) & (timestep==5)) ^ ((op==3) & (timestep==3))
    # TEMP_out = add & T7
    temp_out <<= (op==1) & (timestep==6)
    # write = store & T6
    write <<= (op==2) & (timestep==5)

    return acc_in, acc_out, aluadd, ir_in, ir_out, mar_in, mdr_in, mdr_out, pc_in, pc_out, pcincr, read, reset, temp_out, write

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

# time step
T = pyrtl.Register(3, 'T')

# decode 
op = pyrtl.WireVector(2, 'op')
addr = pyrtl.WireVector(8, 'addr')
op <<= ir[0:2]
addr <<= ir[8:]

# control
acc_in_o, acc_out_o, aluadd_o, ir_in_o, ir_out_o, mar_in_o, mdr_in_o, mdr_out_o, pc_in_o, pc_out_o, pcincr_o, read_o, reset_o, temp_out_o, write_o = Control(op, acc, T)

acc_in <<= acc_in_o
acc_out <<= acc_out_o
aluadd <<= aluadd_o
ir_in <<= ir_in_o
ir_out <<= ir_out_o
mar_in <<= mar_in_o
mdr_in <<= mdr_in_o
mdr_out <<= mdr_out_o
pc_in <<= pc_in_o
pc_out <<= pc_out_o
pcincr <<= pcincr_o
read <<= read_o
reset <<= reset_o
temp_out <<= temp_out_o
write <<= write_o

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


pyrtl.optimize()
# print(pyrtl.working_block())

# Start a simulation trace
sim_trace = pyrtl.SimulationTrace()

# Initialize the i_mem with your instructions.
i_mem_init = {}
with open('test-acc1_add.txt', 'r') as fin:
    i = 0
    for line in fin.readlines():
        i_mem_init[i] = int(line, 16)
        i += 1

sim = pyrtl.Simulation(tracer=sim_trace, memory_value_map={
    memory : i_mem_init
})

# Run for an arbitrarily large number of cycles.
for cycle in range(22):
    sim.step({})

# Use render_trace() to debug if your code doesn't work.
sim_trace.render_trace(symbol_len=10, segment_size=1)

# You can also print out the register file or memory like so if you want to debug:
print(list(map(lambda p: hex(p[1]), sim.inspect_mem(memory).items())))
#print(sim.inspect_mem(memory))
