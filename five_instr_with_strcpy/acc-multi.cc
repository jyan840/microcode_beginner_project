#include <iostream>
#include <fstream>
#include <ilang/ilang++.h>
#include <ilang/verilog-out/verilog_gen.h>
#include "../ila-include/acc-multi.h"

//#include <ilang/util/log.h>
using namespace std;
using namespace ilang;

ACC_MULTI::ACC_MULTI() : model(BuildModel()) {
}

Ila ACC_MULTI::BuildModel() {
    // build the ila
    auto acc_multi = Ila("acc_multi");

    auto acc = acc_multi.NewBvState("acc", 16);
    auto pc = acc_multi.NewBvState("pc", 16);
    auto memory = acc_multi.NewMemState("memory", 16, 16);
    auto inst = Load(memory, pc);

    auto op  = inst(2, 0);
    auto addr = ZExt(inst(15, 8), 16);

    // strcpy 
    auto str_start_addr = ZExt(inst(8, 3), 16);
    auto str_dest_addr = ZExt(inst(15, 9), 16);

    // strncpy
    auto str_len = ZExt(inst(6, 3), 16); // four bits for length
    auto str_start_addr_n = ZExt(inst(10, 7), 16); // four bits for start_address
    auto str_dest_addr_n = ZExt(inst(15, 11), 16); // five bits for dest_address

    acc_multi.SetValid(BoolConst(true));

    {
        auto LOAD = acc_multi.NewInstr("LOAD");
        LOAD.SetDecode(op == BvConst(0, 3));
        auto load_result = Load(memory, addr);
        LOAD.SetUpdate(acc, load_result);
        LOAD.SetUpdate(pc, pc + 1);
    }

    {
        auto ADD = acc_multi.NewInstr("ADD");
        ADD.SetDecode(op == BvConst(1, 3));
        auto add_result = acc + Load(memory, addr);
        ADD.SetUpdate(acc, add_result);
        ADD.SetUpdate(pc, pc + 1);
    }

    
    {   
        auto STORE = acc_multi.NewInstr("STORE");
        STORE.SetDecode(op == BvConst(2, 3));
        auto store_value = acc;
        STORE.SetUpdate(memory, Store(memory, addr, store_value));
        STORE.SetUpdate(pc, pc + 1);        
    }

    
    {   
        auto BRZ = acc_multi.NewInstr("BRZ");
        BRZ.SetDecode(op == BvConst(3, 3));
        BRZ.SetUpdate(pc, Ite(acc == 0, addr, pc + 1));
    }

    {
        auto STRCPY = acc_multi.NewInstr("STRCPY");
        STRCPY.SetDecode(op == BvConst(4, 3));

        auto strcpy_child = acc_multi.NewChild("strcpy_child");

        auto strcpy_step = strcpy_child.NewBvState("strcpy_step", 1);
        auto index = strcpy_child.NewBvState("index", 16);
        auto curr_char = strcpy_child.NewBvState("curr_char", 16);

        strcpy_child.SetValid(op == BvConst(4, 3));
        strcpy_child.SetFetch(strcpy_step);

        strcpy_child.AddInit(index == 0);
        strcpy_child.AddInit(curr_char == 0);

        {
            auto ls_strcpy = strcpy_child.NewInstr("ls_strcpy"); 
            ls_strcpy.SetDecode(strcpy_step == BvConst(0, 1));
            auto curr_char_result = Load(memory, str_start_addr + index);
            auto store_char = Store(memory, str_dest_addr + index, curr_char_result);
            ls_strcpy.SetUpdate(memory, store_char);
            ls_strcpy.SetUpdate(curr_char, curr_char_result);
            ls_strcpy.SetUpdate(strcpy_step, BvConst(1, 1));
        }

        {
            auto check_strcpy = strcpy_child.NewInstr("check_strcpy");
            check_strcpy.SetDecode(strcpy_step == BvConst(1, 1));
            auto is_null = (curr_char == BvConst(0, 16));
            check_strcpy.SetUpdate(index, Ite(is_null, BvConst(0, 16), index + 1));
            check_strcpy.SetUpdate(pc, Ite(is_null, pc + 1, pc));
            check_strcpy.SetUpdate(strcpy_step, BvConst(0, 1));
        }   

        STRCPY.SetProgram(strcpy_child);

    }
    {
        auto STRNCPY = acc_multi.NewInstr("STRNCPY");
        STRNCPY.SetDecode(op == BvConst(5, 3));

        auto strncpy_child = acc_multi.NewChild("strncpy_child");

        auto strncpy_step = strncpy_child.NewBvState("strncpy_step", 1);
        auto index = strncpy_child.NewBvState("index", 16);
        
        strncpy_child.SetValid(op == BvConst(5, 3));
        strncpy_child.SetFetch(strncpy_step);

        strncpy_child.AddInit(index == 0);

        {   
            auto ls_strncpy = strncpy_child.NewInstr("ls_strncpy"); 
            ls_strncpy.SetDecode(strncpy_step == BvConst(0, 1));
            auto curr_char_result = Load(memory, str_start_addr_n + index);
            auto store_char = Store(memory, str_dest_addr_n + index, curr_char_result);
            ls_strncpy.SetUpdate(memory, store_char);
            ls_strncpy.SetUpdate(strncpy_step, BvConst(1, 1));
        }

        
        {   
            auto check_strncpy = strncpy_child.NewInstr("check_strncpy");
            check_strncpy.SetDecode(strncpy_step == BvConst(1, 1));
            auto check_end = (index == str_len - 1);
            check_strncpy.SetUpdate(index, Ite(check_end, BvConst(0, 16), index + 1));
            check_strncpy.SetUpdate(pc, Ite(check_end, pc + 1, pc));
            check_strncpy.SetUpdate(check_end, BvConst(0, 1));
        }   

        STRNCPY.SetProgram(strncpy_child);

    }
    return acc_multi;
}

// void GenerateVerilogModel(const Ila & a) {
// 	ofstream fout("acc_multi.v");
//     if (!fout.is_open()) {
//         cerr << "Failed to open file for writing: acc_multi.v" << endl;
//         return;
//     }
//     a.ExportToVerilog(fout);
//     // VerilogGenerator vgen(VerilogGenerator::VlgGenConfig(
//     //   false));
//     // // vgen.ExportTopLevelInstr(ptr_)
//     // vgen.ExportIla(a);
//     // vgen.DumpToFile(fout);
// }

// int main() {
//     ACC_MULTI acc_multi_instance;
//     GenerateVerilogModel(acc_multi_instance.model);
//     // GenerateVerilogModel(BuildModel());
//     return 0;
// }


    
