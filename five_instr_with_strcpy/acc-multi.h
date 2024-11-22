#ifndef ACC_MULTI_H
#define ACC_MULTI_H

#include <iostream>
#include <fstream>
#include <ilang/ilang++.h>
#include <ilang/verilog-out/verilog_gen.h>
//#include <ilang/util/log.h>

using namespace std;
using namespace ilang;

class ACC_MULTI {
    public:
        ACC_MULTI();
        Ila model;
    
    private:
        Ila BuildModel();
};


// int main() {
//     ACC_MULTI acc_multi_instance;
//     GenerateVerilogModel(acc_multi_instance.model);
//     // GenerateVerilogModel(BuildModel());
//     return 0;
// }

#endif 


    
