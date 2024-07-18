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
__ILA_acc_multi_decode_of_check_strcpy__,
__ILA_acc_multi_decode_of_check_strncpy__,
__ILA_acc_multi_valid__,
memory_data_n1,
memory_data_n22,
memory_data_n25,
memory_addr_n0,
memory_addr_n21,
memory_addr_n24,
memory_addr0,
memory_data0,
memory_wen0,
acc,
pc
);
input      [7:0] __ILA_acc_multi_grant__;
input            clk;
input            rst;
input     [15:0] memory_data_n1;
input     [15:0] memory_data_n22;
input     [15:0] memory_data_n25;
output      [7:0] __ILA_acc_multi_acc_decode__;
output            __ILA_acc_multi_decode_of_ADD__;
output            __ILA_acc_multi_decode_of_BRZ__;
output            __ILA_acc_multi_decode_of_LOAD__;
output            __ILA_acc_multi_decode_of_STORE__;
output            __ILA_acc_multi_decode_of_STRCPY__;
output            __ILA_acc_multi_decode_of_STRNCPY__;
output            __ILA_acc_multi_decode_of_check_strcpy__;
output            __ILA_acc_multi_decode_of_check_strncpy__;
output            __ILA_acc_multi_valid__;
output     [15:0] memory_addr_n0;
output     [15:0] memory_addr_n21;
output     [15:0] memory_addr_n24;
output     [15:0] memory_addr0;
output     [15:0] memory_data0;
output            memory_wen0;
output reg     [15:0] acc;
output reg     [15:0] pc;
wire      [7:0] __ILA_acc_multi_acc_decode__;
wire            __ILA_acc_multi_decode_of_ADD__;
wire            __ILA_acc_multi_decode_of_BRZ__;
wire            __ILA_acc_multi_decode_of_LOAD__;
wire            __ILA_acc_multi_decode_of_STORE__;
wire            __ILA_acc_multi_decode_of_STRCPY__;
wire            __ILA_acc_multi_decode_of_STRNCPY__;
wire            __ILA_acc_multi_decode_of_check_strcpy__;
wire            __ILA_acc_multi_decode_of_check_strncpy__;
wire      [7:0] __ILA_acc_multi_grant__;
wire            __ILA_acc_multi_valid__;
wire     [15:0] bv_16_0_n32;
wire     [15:0] bv_16_1_n28;
wire            bv_1_1_n14;
wire      [2:0] bv_3_0_n4;
wire      [2:0] bv_3_1_n6;
wire      [2:0] bv_3_2_n8;
wire      [2:0] bv_3_3_n10;
wire      [2:0] bv_3_4_n12;
wire      [2:0] bv_3_5_n16;
wire            clk;
wire     [15:0] memory_addr0;
wire     [15:0] memory_addr_n0;
wire     [15:0] memory_addr_n21;
wire     [15:0] memory_addr_n24;
wire     [15:0] memory_data0;
wire     [15:0] memory_data_n1;
wire     [15:0] memory_data_n22;
wire     [15:0] memory_data_n25;
wire            memory_wen0;
wire            n11;
wire            n13;
wire            n15;
wire            n17;
wire            n18;
wire      [7:0] n19;
wire     [15:0] n2;
wire     [15:0] n20;
wire     [15:0] n23;
wire     [15:0] n26;
wire     [15:0] n27;
wire     [15:0] n29;
wire      [2:0] n3;
wire     [15:0] n30;
wire     [15:0] n31;
wire            n33;
wire     [15:0] n34;
wire     [15:0] n35;
wire            n36;
wire     [15:0] n37;
wire     [15:0] n38;
wire      [3:0] n39;
wire     [15:0] n40;
wire     [15:0] n41;
wire            n42;
wire     [15:0] n43;
wire     [15:0] n44;
wire            n45;
wire            n46;
wire            n47;
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
assign bv_1_1_n14 = 1'h1 ;
assign n15 =  ( strcpy_step ) == ( bv_1_1_n14 )  ;
assign __ILA_acc_multi_decode_of_check_strcpy__ = n15 ;
assign __ILA_acc_multi_acc_decode__[5] = __ILA_acc_multi_decode_of_check_strcpy__ ;
assign bv_3_5_n16 = 3'h5 ;
assign n17 =  ( n3 ) == ( bv_3_5_n16 )  ;
assign __ILA_acc_multi_decode_of_STRNCPY__ = n17 ;
assign __ILA_acc_multi_acc_decode__[6] = __ILA_acc_multi_decode_of_STRNCPY__ ;
assign n18 =  ( strncpy_step ) == ( bv_1_1_n14 )  ;
assign __ILA_acc_multi_decode_of_check_strncpy__ = n18 ;
assign __ILA_acc_multi_acc_decode__[7] = __ILA_acc_multi_decode_of_check_strncpy__ ;
assign n19 = n2[15:8] ;
assign n20 =  {8'd0 , n19}  ;
assign memory_addr_n21 = n20 ;
assign n23 = memory_data_n22 ;
assign memory_addr_n24 = n20 ;
assign n26 = memory_data_n25 ;
assign n27 =  ( acc ) + ( n26 )  ;
assign bv_16_1_n28 = 16'h1 ;
assign n29 =  ( pc ) + ( bv_16_1_n28 )  ;
assign n30 =  ( pc ) + ( bv_16_1_n28 )  ;
assign n31 =  ( pc ) + ( bv_16_1_n28 )  ;
assign bv_16_0_n32 = 16'h0 ;
assign n33 =  ( acc ) == ( bv_16_0_n32 )  ;
assign n34 =  ( pc ) + ( bv_16_1_n28 )  ;
assign n35 =  ( n33 ) ? ( n20 ) : ( n34 ) ;
assign n36 =  ( curr_char ) == ( bv_16_0_n32 )  ;
assign n37 =  ( pc ) + ( bv_16_1_n28 )  ;
assign n38 =  ( n36 ) ? ( n37 ) : ( pc ) ;
assign n39 = n2[6:3] ;
assign n40 =  {12'd0 , n39}  ;
assign n41 =  ( n40 ) - ( bv_16_1_n28 )  ;
assign n42 =  ( index ) == ( n41 )  ;
assign n43 =  ( pc ) + ( bv_16_1_n28 )  ;
assign n44 =  ( n42 ) ? ( n43 ) : ( pc ) ;
assign n45 = ~ ( n9 )  ;
assign n46 =  ( 1'b1 ) & (n45 )  ;
assign n47 =  ( 1'b1 ) & (n9 )  ;
assign memory_addr0 = n47 ? (n20) : (0) ;
assign memory_data0 = n47 ? (acc) : ('d0) ;
assign memory_wen0 = (n47) ? ( 1'b1 ) : (1'b0) ;
always @(posedge clk) begin
   if(rst) begin
   end
   else if(__ILA_acc_multi_valid__) begin
       if ( __ILA_acc_multi_decode_of_LOAD__ && __ILA_acc_multi_grant__[0] ) begin
           acc <= n23;
       end else if ( __ILA_acc_multi_decode_of_ADD__ && __ILA_acc_multi_grant__[1] ) begin
           acc <= n27;
       end
       if ( __ILA_acc_multi_decode_of_LOAD__ && __ILA_acc_multi_grant__[0] ) begin
           pc <= n29;
       end else if ( __ILA_acc_multi_decode_of_ADD__ && __ILA_acc_multi_grant__[1] ) begin
           pc <= n30;
       end else if ( __ILA_acc_multi_decode_of_STORE__ && __ILA_acc_multi_grant__[2] ) begin
           pc <= n31;
       end else if ( __ILA_acc_multi_decode_of_BRZ__ && __ILA_acc_multi_grant__[3] ) begin
           pc <= n35;
       end else if ( __ILA_acc_multi_decode_of_check_strcpy__ && __ILA_acc_multi_grant__[5] ) begin
           pc <= n38;
       end else if ( __ILA_acc_multi_decode_of_check_strncpy__ && __ILA_acc_multi_grant__[7] ) begin
           pc <= n44;
       end
   end
end
endmodule
