#include <iostream>
#include <fstream>
#include <ilang/ilang++.h>
#include <ilang/util/log.h>

using namespace std;
using namespace ilang;

Ila BuildModel() {
    // build the ila
    auto acc_multi = Ila("acc-multi");
    auto inst = acc_multi.NewBvInput("inst", 16);
    auto acc = acc_multi.NewBvState("r0", 16);
    auto pc = acc_multi.NewBvState("pc", 16);
    auto memory = acc_multi.NewMemState("memory", 16, 16);

    // states used in strcpy
    auto step_strcpy = acc_multi.NewBvState("step_strcpy", 2);
    auto curr_char = acc_multi.NewBvState("load_strcpy", 16);
    auto index = acc_multi.NewBvState("index", 16);

    acc_multi.AddInit(step_strcpy == BvConst(0, 2));
    acc_multi.AddInit(index == BvConst(0, 16));

    auto op  = inst(2, 0);
    auto str_start_addr = ZExt(inst(8, 3), 16);
    auto str_dest_addr = ZExt(inst(15, 9), 16);
    auto addr = ZExt(inst(15, 8), 16);

    auto LOAD = acc_multi.NewInstr("LOAD");
    {
        LOAD.SetDecode(op == BvConst(0, 3));
        auto load_result = Load(memory, addr);
        LOAD.SetUpdate(acc, load_result);
        LOAD.SetUpdate(pc, pc + 1);
    }

    auto ADD = acc_multi.NewInstr("ADD");
    {
        ADD.SetDecode(op == BvConst(1, 3));
        auto add_result = acc + Load(memory, addr);
        ADD.SetUpdate(acc, add_result);
        ADD.SetUpdate(pc, pc + 1);
    }

    auto STORE = acc_multi.NewInstr("STORE");
    {
        STORE.SetDecode(op == BvConst(2, 3));
        auto store_value = acc;
        STORE.SetUpdate(memory, Store(memory, addr, store_value));
        STORE.SetUpdate(pc, pc + 1);        
    }

    auto BRZ = acc_multi.NewInstr("BRZ");
    {
        BRZ.SetDecode(op == BvConst(3, 3));
        BRZ.SetUpdate(pc, Ite(acc == 0, addr, pc + 1));
    }

    auto LS_STRCPY = acc_multi.NewInstr("LS_STRCPY");
    {
        LS_STRCPY.SetDecode(op == BvConst(4, 3) & step_strcpy == BvConst(0, 1));
        auto curr_char_result = Load(memory, str_start_addr + index);
        auto store_char = Store(memory, str_dest_addr + index, curr_char_result);
        LS_STRCPY.SetUpdate(memory, store_char);
        LS_STRCPY.SetUpdate(curr_char, curr_char_result);
        LS_STRCPY.SetUpdate(step_strcpy, BvConst(1, 1));
    }

    auto CHECK_STRCPY = acc_multi.NewInstr("CHECK_STRCPY");
    {
        CHECK_STRCPY.SetDecode(op = BvConst(4, 3) & step_strcpy == BvConst(1, 1));
        auto is_null = (curr_char == BvConst(0, 16));
        CHECK_STRCPY.SetUpdate(index, Ite(is_null, BvConst(0, 16), index + 1));
        CHECK_STRCPY.SetUpdate(pc, Ite(is_null, pc + 1, pc));
        CHECK_STRCPY.SetUpdate(step_strcpy, BvConst(0, 0));
    }

    return acc_multi;
}

int main() {
    return 0;
}


    
