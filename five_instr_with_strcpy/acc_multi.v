module acc_multi(
__ILA_acc_multi_grant__,
clk,
rst,
__ILA_acc_multi_acc_decode__,
__ILA_acc_multi_decode_of_ADD__,
__ILA_acc_multi_decode_of_BRZ__,
__ILA_acc_multi_decode_of_LOAD__,
__ILA_acc_multi_decode_of_STORE__,
__ILA_acc_multi_decode_of_STRCPY__,
__ILA_acc_multi_decode_of_STRNCPY__,
__ILA_acc_multi_valid__,
memory_data_n1,
memory_data_n19,
memory_data_n22,
memory_addr_n0,
memory_addr_n18,
memory_addr_n21,
memory_addr0,
memory_data0,
memory_wen0,
acc,
pc
);
input      [5:0] __ILA_acc_multi_grant__;
input            clk;
input            rst;
input     [15:0] memory_data_n1;
input     [15:0] memory_data_n19;
input     [15:0] memory_data_n22;
output      [5:0] __ILA_acc_multi_acc_decode__;
output            __ILA_acc_multi_decode_of_ADD__;
output            __ILA_acc_multi_decode_of_BRZ__;
output            __ILA_acc_multi_decode_of_LOAD__;
output            __ILA_acc_multi_decode_of_STORE__;
output            __ILA_acc_multi_decode_of_STRCPY__;
output            __ILA_acc_multi_decode_of_STRNCPY__;
output            __ILA_acc_multi_valid__;
output     [15:0] memory_addr_n0;
output     [15:0] memory_addr_n18;
output     [15:0] memory_addr_n21;
output     [15:0] memory_addr0;
output     [15:0] memory_data0;
output            memory_wen0;
output reg     [15:0] acc;
output reg     [15:0] pc;
wire      [5:0] __ILA_acc_multi_acc_decode__;
wire            __ILA_acc_multi_decode_of_ADD__;
wire            __ILA_acc_multi_decode_of_BRZ__;
wire            __ILA_acc_multi_decode_of_LOAD__;
wire            __ILA_acc_multi_decode_of_STORE__;
wire            __ILA_acc_multi_decode_of_STRCPY__;
wire            __ILA_acc_multi_decode_of_STRNCPY__;
wire      [5:0] __ILA_acc_multi_grant__;
wire            __ILA_acc_multi_valid__;
wire     [15:0] bv_16_0_n29;
wire     [15:0] bv_16_1_n25;
wire      [2:0] bv_3_0_n4;
wire      [2:0] bv_3_1_n6;
wire      [2:0] bv_3_2_n8;
wire      [2:0] bv_3_3_n10;
wire      [2:0] bv_3_4_n12;
wire      [2:0] bv_3_5_n14;
wire            clk;
wire     [15:0] memory_addr0;
wire     [15:0] memory_addr_n0;
wire     [15:0] memory_addr_n18;
wire     [15:0] memory_addr_n21;
wire     [15:0] memory_data0;
wire     [15:0] memory_data_n1;
wire     [15:0] memory_data_n19;
wire     [15:0] memory_data_n22;
wire            memory_wen0;
wire            n11;
wire            n13;
wire            n15;
wire      [7:0] n16;
wire     [15:0] n17;
wire     [15:0] n2;
wire     [15:0] n20;
wire     [15:0] n23;
wire     [15:0] n24;
wire     [15:0] n26;
wire     [15:0] n27;
wire     [15:0] n28;
wire      [2:0] n3;
wire            n30;
wire     [15:0] n31;
wire     [15:0] n32;
wire            n33;
wire            n34;
wire            n35;
wire            n5;
wire            n7;
wire            n9;
wire            rst;
assign __ILA_acc_multi_valid__ = 1'b1 ;
assign memory_addr_n0 = pc ;
assign n2 = memory_data_n1 ;
assign n3 = n2[2:0] ;
assign bv_3_0_n4 = 3'h0 ;
assign n5 =  ( n3 ) == ( bv_3_0_n4 )  ;
assign __ILA_acc_multi_decode_of_LOAD__ = n5 ;
assign __ILA_acc_multi_acc_decode__[0] = __ILA_acc_multi_decode_of_LOAD__ ;
assign bv_3_1_n6 = 3'h1 ;
assign n7 =  ( n3 ) == ( bv_3_1_n6 )  ;
assign __ILA_acc_multi_decode_of_ADD__ = n7 ;
assign __ILA_acc_multi_acc_decode__[1] = __ILA_acc_multi_decode_of_ADD__ ;
assign bv_3_2_n8 = 3'h2 ;
assign n9 =  ( n3 ) == ( bv_3_2_n8 )  ;
assign __ILA_acc_multi_decode_of_STORE__ = n9 ;
assign __ILA_acc_multi_acc_decode__[2] = __ILA_acc_multi_decode_of_STORE__ ;
assign bv_3_3_n10 = 3'h3 ;
assign n11 =  ( n3 ) == ( bv_3_3_n10 )  ;
assign __ILA_acc_multi_decode_of_BRZ__ = n11 ;
assign __ILA_acc_multi_acc_decode__[3] = __ILA_acc_multi_decode_of_BRZ__ ;
assign bv_3_4_n12 = 3'h4 ;
assign n13 =  ( n3 ) == ( bv_3_4_n12 )  ;
assign __ILA_acc_multi_decode_of_STRCPY__ = n13 ;
assign __ILA_acc_multi_acc_decode__[4] = __ILA_acc_multi_decode_of_STRCPY__ ;
assign bv_3_5_n14 = 3'h5 ;
assign n15 =  ( n3 ) == ( bv_3_5_n14 )  ;
assign __ILA_acc_multi_decode_of_STRNCPY__ = n15 ;
assign __ILA_acc_multi_acc_decode__[5] = __ILA_acc_multi_decode_of_STRNCPY__ ;
assign n16 = n2[15:8] ;
assign n17 =  {8'd0 , n16}  ;
assign memory_addr_n18 = n17 ;
assign n20 = memory_data_n19 ;
assign memory_addr_n21 = n17 ;
assign n23 = memory_data_n22 ;
assign n24 =  ( acc ) + ( n23 )  ;
assign bv_16_1_n25 = 16'h1 ;
assign n26 =  ( pc ) + ( bv_16_1_n25 )  ;
assign n27 =  ( pc ) + ( bv_16_1_n25 )  ;
assign n28 =  ( pc ) + ( bv_16_1_n25 )  ;
assign bv_16_0_n29 = 16'h0 ;
assign n30 =  ( acc ) == ( bv_16_0_n29 )  ;
assign n31 =  ( pc ) + ( bv_16_1_n25 )  ;
assign n32 =  ( n30 ) ? ( n17 ) : ( n31 ) ;
assign n33 = ~ ( n9 )  ;
assign n34 =  ( 1'b1 ) & (n33 )  ;
assign n35 =  ( 1'b1 ) & (n9 )  ;
assign memory_addr0 = n35 ? (n17) : (0) ;
assign memory_data0 = n35 ? (acc) : ('d0) ;
assign memory_wen0 = (n35) ? ( 1'b1 ) : (1'b0) ;
always @(posedge clk) begin
   if(rst) begin
   end
   else if(__ILA_acc_multi_valid__) begin
       if ( __ILA_acc_multi_decode_of_LOAD__ && __ILA_acc_multi_grant__[0] ) begin
           acc <= n20;
       end else if ( __ILA_acc_multi_decode_of_ADD__ && __ILA_acc_multi_grant__[1] ) begin
           acc <= n24;
       end
       if ( __ILA_acc_multi_decode_of_LOAD__ && __ILA_acc_multi_grant__[0] ) begin
           pc <= n26;
       end else if ( __ILA_acc_multi_decode_of_ADD__ && __ILA_acc_multi_grant__[1] ) begin
           pc <= n27;
       end else if ( __ILA_acc_multi_decode_of_STORE__ && __ILA_acc_multi_grant__[2] ) begin
           pc <= n28;
       end else if ( __ILA_acc_multi_decode_of_BRZ__ && __ILA_acc_multi_grant__[3] ) begin
           pc <= n32;
       end
   end
end
endmodule
