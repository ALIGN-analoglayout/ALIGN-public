
#include <gtest/gtest.h>
#include "PnRdatabase.h"

#include <sstream>
#include <algorithm>

TEST(PnRDBTest, True) {
    EXPECT_TRUE( 1);
};

// These three all take about the same abount of time
TEST(PnRDBTest, Pushback) {
  vector<int> a;
  for (unsigned int i=0; i<1000000; ++i) {
    a.push_back( 0);
  }
}

TEST(PnRDBTest, Resize) {
  vector<int> a;
  for (unsigned int i=0; i<1000000; ++i) {
    a.resize(a.size()+1);
    a.back() = 0;
  }
}

TEST(PnRDBTest, Emplace) {
  vector<int> a;
  for (unsigned int i=0; i<1000000; ++i) {
    a.emplace_back( 0);
  }
}

TEST(PnRDBTest, PnRdatabase_Constructor) {
  PnRdatabase foo;
  EXPECT_EQ( foo.get_unitScale(), 2000);
  EXPECT_EQ( foo.get_maxNode(), 0);
}

TEST(PnRDBTest, get_number) {
  PnRdatabase foo;
  EXPECT_EQ( foo.get_number( "23"), 23);
  EXPECT_EQ( foo.get_number( "457"), 457);
  EXPECT_EQ( foo.get_number( "10000000000000"), 10000000000000ULL);
}

TEST(PnRDBTest, Lexer) {
  string str =
"//Verilog block level netlist file for telescopic_ota\n"
"//Generated by UMN for ALIGN project\n" 
"\n"
"\n"
"module telescopic_ota ( voutn, vss, vinp, vbiasp1, vbiasnd, vbiasn, voutp, vbiasp2, vinn, d1, vdd ); \n"
"input voutn, vss, vinp, vbiasp1, vbiasnd, vbiasn, voutp, vbiasp2, vinn, d1, vdd; \n"
"\n"
"CMC_PMOS_S_n12_X1_Y1 m2_m1 ( .DA(net012), .G(vbiasp1), .DB(net06), .S(vdd) ); \n"
"DP_NMOS_n12_X3_Y3 m3_m0 ( .DA(net014), .GA(vinn), .S(net10), .DB(net8), .GB(vinp) ); \n"
"CMFB_NMOS_n12_X3_Y1 m5_m4 ( .DA(d1), .S(vss), .DB(net10), .GB(vbiasnd) ); \n"
"CMC_PMOS_n12_X2_Y1 m6_m7 ( .DA(voutn), .G(vbiasp2), .DB(voutp), .SA(net06), .SB(net012) ); \n"
"CMC_NMOS_n12_X3_Y1 m9_m8 ( .DA(voutn), .G(vbiasn), .DB(voutp), .SA(net8), .SB(net014) ); \n"
"\n"
"endmodule\n";

  std::istringstream is(str);
  Lexer l(is);

  while ( !l.have( TokenType::EndOfFile)) {
    std::cout << l.current_token << std::endl;
    l.get_token();
  }
}

TEST(PnRDBTest, Lexer_leading_number) {
  string str =
"//Verilog block level netlist file for telescopic_ota\n"
"//Generated by UMN for ALIGN project\n" 
"\n"
"\n"
"module telescopic_ota ( voutn, vss, vinp, vbiasp1, vbiasnd, vbiasn, voutp, vbiasp2, vinn, d1, vdd ); \n"
"input voutn, vss, vinp, vbiasp1, vbiasnd, vbiasn, voutp, vbiasp2, vinn, d1, vdd; \n"
"\n"
"2CMC_PMOS_S_n12_X1_Y1 m2_m1 ( .DA(net012), .G(vbiasp1), .DB(net06), .S(vdd) ); \n"
"DP_NMOS_n12_X3_Y3 m3_m0 ( .DA(net014), .GA(vinn), .S(net10), .DB(net8), .GB(vinp) ); \n"
"CMFB_NMOS_n12_X3_Y1 m5_m4 ( .DA(d1), .S(vss), .DB(net10), .GB(vbiasnd) ); \n"
"CMC_PMOS_n12_X2_Y1 m6_m7 ( .DA(voutn), .G(vbiasp2), .DB(voutp), .SA(net06), .SB(net012) ); \n"
"CMC_NMOS_n12_X3_Y1 m9_m8 ( .DA(voutn), .G(vbiasn), .DB(voutp), .SA(net8), .SB(net014) ); \n"
"\n"
"endmodule\n";

  std::istringstream is(str);
  Lexer l(is);

  while ( !l.have( TokenType::EndOfFile)) {
    std::cout << l.current_token << std::endl;
    l.get_token();
  }
}

TEST(PnRDBTest, Lexer2) {
  string str =
"//Verilog block level netlist file for telescopic_ota\n"
"//Generated by UMN for ALIGN project\n" 
"\n"
"\n"
"module telescopic_ota ( voutn, vss, vinp, vbiasp1, vbiasnd, vbiasn, voutp, vbiasp2, vinn, d1, vdd ); \n"
"input voutn, vss, vinp, vbiasp1, vbiasnd, vbiasn, voutp, vbiasp2, vinn, d1, vdd; \n"
"\n"
"CMC_PMOS_S_n12_X1_Y1 m2_m1 ( .DA(net012), .G(vbiasp1), .DB(net06), .S(vdd) ); \n"
"DP_NMOS_n12_X3_Y3 m3_m0 ( .DA(net014), .GA(vinn), .S(net10), .DB(net8), .GB(vinp) ); \n"
"CMFB_NMOS_n12_X3_Y1 m5_m4 ( .DA(d1), .S(vss), .DB(net10), .GB(vbiasnd) ); \n"
"CMC_PMOS_n12_X2_Y1 m6_m7 ( .DA(voutn), .G(vbiasp2), .DB(voutp), .SA(net06), .SB(net012) ); \n"
"CMC_NMOS_n12_X3_Y1 m9_m8 ( .DA(voutn), .G(vbiasn), .DB(voutp), .SA(net8), .SB(net014) ); \n"
"\n"
"endmodule\n";

  std::istringstream is(str);
  Lexer l(is,1);

  while ( !l.have( TokenType::EndOfFile)) {
    std::cout << l.current_token << std::endl;
    EXPECT_NE( l.current_token.tt, TokenType::EndOfLine);
    l.get_token();
  }
}

TEST( PnRDBTest, AngleBrackets)
{
  string str =
R"foo(//Verilog block level netlist file for _sub19
//Generated by UMN for ALIGN project 

//module _sub19 ( A, vrp, vrn, B);
module _sub19 ( n<4>, nb<6>, p<7>, nb<1>, n<3>, nb<5>, pb<6>, p<6>, n<2>, pb<2>, pb<7>, p<5>, n<7>, p<3>, p<2>, n<6>, vdacn, nb<2>, vrp, vdacp, n<5>, vrn, pb<4>, pb<5>, nb<4>, nb<3>, p<4>, pb<3>, p<1>, nb<7> ); 
input n<4>, nb<6>, p<7>, nb<1>, n<3>, nb<5>, pb<6>, p<6>, n<2>, pb<2>, pb<7>, p<5>, n<7>, p<3>, p<2>, n<6>, vdacn, nb<2>, vrp, vdacp, n<5>, vrn, pb<4>, pb<5>, nb<4>, nb<3>, p<4>, pb<3>, p<1>, nb<7>;
//input A;

cdac1 XI1 ( .n<2>(n<2>), .n<3>(n<3>), .n<4>(n<4>), .n<5>(n<5>), .n<6>(n<6>), .n<7>(n<7>), .vdac(vdacn), .vrn(vrn), .vrp(vrp) ); 
//INV_LVT xi11 ( .i(A), .vdd(vrp), .vss(vrn), .zn(B) ); 
cdac2 XI2 ( .n<1>(nb<1>), .n<2>(nb<2>), .n<3>(nb<3>), .n<4>(nb<4>), .n<5>(nb<5>), .n<6>(nb<6>), .n<7>(nb<7>), .vdac(vdacp), .vrn(vrn), .vrp(vrp) ); 
cdac2 XI3 ( .n<1>(p<1>), .n<2>(p<2>), .n<3>(p<3>), .n<4>(p<4>), .n<5>(p<5>), .n<6>(p<6>), .n<7>(p<7>), .vdac(vdacp), .vrn(vrn), .vrp(vrp) ); 
cdac1 XI4 ( .n<2>(pb<2>), .n<3>(pb<3>), .n<4>(pb<4>), .n<5>(pb<5>), .n<6>(pb<6>), .n<7>(pb<7>), .vdac(vdacn), .vrn(vrn), .vrp(vrp) ); 

endmodule

module cdac1 ( n<2>, n<3>, n<4>, n<5>, n<6>, n<7>, vdac, vrn, vrp ); 
input n<2>, n<3>, n<4>, n<5>, n<6>, n<7>, vdac, vrn, vrp;

Cap_200fF C74<0> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<1> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<2> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<3> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<4> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<5> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<6> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<7> ( .MINUS(vdac), .PLUS(net42) ); 
//Cap_200fF C75 ( .MINUS(vdac), .PLUS(net49) ); 
//Cap_200fF C76<0> ( .MINUS(vdac), .PLUS(net44) ); 
//Cap_200fF C76<1> ( .MINUS(vdac), .PLUS(net44) ); 
//Cap_200fF C87<0> ( .MINUS(vdac), .PLUS(net43) ); 
//Cap_200fF C87<1> ( .MINUS(vdac), .PLUS(net43) ); 
//Cap_200fF C87<2> ( .MINUS(vdac), .PLUS(net43) ); 
//Cap_200fF C87<3> ( .MINUS(vdac), .PLUS(net43) ); 
//Cap_200fF C92<0> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<10> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<11> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<12> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<13> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<14> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<15> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<16> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<17> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<18> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<19> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<1> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<20> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<21> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<22> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<23> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<24> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<25> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<26> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<27> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<28> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<29> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<2> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<30> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<31> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<3> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<4> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<5> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<6> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<7> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<8> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<9> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C95<0> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<10> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<11> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<12> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<13> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<14> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<15> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<1> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<2> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<3> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<4> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<5> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<6> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<7> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<8> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<9> ( .MINUS(vdac), .PLUS(n6<1>) ); 
INV_LVT xi11 ( .i(n<2>), .vdd(vrp), .vss(vrn), .zn(net49) ); 
INV_LVT xi13 ( .i(n<3>), .vdd(vrp), .vss(vrn), .zn(net44) ); 
INV_LVT xi66 ( .i(n<5>), .vdd(vrp), .vss(vrn), .zn(net42) ); 
INV_LVT xi67 ( .i(n<4>), .vdd(vrp), .vss(vrn), .zn(net43) ); 
INV_LVT xi90<0> ( .i(n<7>), .vdd(vrp), .vss(vrn), .zn(n7<0>) ); 
INV_LVT xi90<1> ( .i(n<7>), .vdd(vrp), .vss(vrn), .zn(n7<1>) ); 
INV_LVT xi90<2> ( .i(n<7>), .vdd(vrp), .vss(vrn), .zn(n7<2>) ); 
INV_LVT xi90<3> ( .i(n<7>), .vdd(vrp), .vss(vrn), .zn(n7<3>) ); 
INV_LVT xi93<0> ( .i(n<6>), .vdd(vrp), .vss(vrn), .zn(n6<0>) ); 
INV_LVT xi93<1> ( .i(n<6>), .vdd(vrp), .vss(vrn), .zn(n6<1>) ); 

endmodule

module INV_LVT ( i, vss, vdd, zn ); 
input i, vss, vdd, zn;

Switch_NMOS_n3_X1_Y1 xm0 ( .D(zn), .G(i), .S(vss) ); 
Switch_PMOS_n3_X1_Y1 xm1 ( .D(zn), .G(i), .S(vdd) ); 

endmodule

module cdac2 ( n<1>, n<2>, n<3>, n<4>, n<5>, n<6>, n<7>, vdac, vrn, vrp ); 
input n<1>, n<2>, n<3>, n<4>, n<5>, n<6>, n<7>, vdac, vrn, vrp;

Cap_200fF C74<0> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<1> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<2> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<3> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<4> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<5> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<6> ( .MINUS(vdac), .PLUS(net42) ); 
Cap_200fF C74<7> ( .MINUS(vdac), .PLUS(net42) ); 
//Cap_200fF C75 ( .MINUS(vdac), .PLUS(net49) ); 
//Cap_200fF C76<0> ( .MINUS(vdac), .PLUS(net44) ); 
//Cap_200fF C76<1> ( .MINUS(vdac), .PLUS(net44) ); 
//Cap_200fF C82 ( .MINUS(vdac), .PLUS(net30) ); 
//Cap_200fF C87<0> ( .MINUS(vdac), .PLUS(net43) ); 
//Cap_200fF C87<1> ( .MINUS(vdac), .PLUS(net43) ); 
//Cap_200fF C87<2> ( .MINUS(vdac), .PLUS(net43) ); 
//Cap_200fF C87<3> ( .MINUS(vdac), .PLUS(net43) ); 
//Cap_200fF C92<0> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<10> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<11> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<12> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<13> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<14> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<15> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<16> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<17> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<18> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<19> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<1> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<20> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<21> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<22> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<23> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<24> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<25> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<26> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<27> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<28> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<29> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<2> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<30> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<31> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<3> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<4> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<5> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C92<6> ( .MINUS(vdac), .PLUS(n7<2>) ); 
//Cap_200fF C92<7> ( .MINUS(vdac), .PLUS(n7<3>) ); 
//Cap_200fF C92<8> ( .MINUS(vdac), .PLUS(n7<0>) ); 
//Cap_200fF C92<9> ( .MINUS(vdac), .PLUS(n7<1>) ); 
//Cap_200fF C95<0> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<10> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<11> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<12> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<13> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<14> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<15> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<1> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<2> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<3> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<4> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<5> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<6> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<7> ( .MINUS(vdac), .PLUS(n6<1>) ); 
//Cap_200fF C95<8> ( .MINUS(vdac), .PLUS(n6<0>) ); 
//Cap_200fF C95<9> ( .MINUS(vdac), .PLUS(n6<1>) ); 
INV_LVT xi11 ( .i(n<2>), .vdd(vrp), .vss(vrn), .zn(net49) ); 
INV_LVT xi13 ( .i(n<3>), .vdd(vrp), .vss(vrn), .zn(net44) ); 
INV_LVT xi30 ( .i(n<1>), .vdd(vrp), .vss(vrn), .zn(net30) ); 
INV_LVT xi66 ( .i(n<5>), .vdd(vrp), .vss(vrn), .zn(net42) ); 
INV_LVT xi67 ( .i(n<4>), .vdd(vrp), .vss(vrn), .zn(net43) ); 
INV_LVT xi90<0> ( .i(n<7>), .vdd(vrp), .vss(vrn), .zn(n7<0>) ); 
INV_LVT xi90<1> ( .i(n<7>), .vdd(vrp), .vss(vrn), .zn(n7<1>) ); 
INV_LVT xi90<2> ( .i(n<7>), .vdd(vrp), .vss(vrn), .zn(n7<2>) ); 
INV_LVT xi90<3> ( .i(n<7>), .vdd(vrp), .vss(vrn), .zn(n7<3>) ); 
INV_LVT xi93<0> ( .i(n<6>), .vdd(vrp), .vss(vrn), .zn(n6<0>) ); 
INV_LVT xi93<1> ( .i(n<6>), .vdd(vrp), .vss(vrn), .zn(n6<1>) ); 

endmodule

)foo";

  PnRdatabase db;
  ReadVerilogHelper rvh(db);
  std::istringstream is(str);

  rvh.parse_top( is);

}

TEST( PnRDBTest, Telescopic_OTA)
{
  string str =
R"foo(//Verilog block level netlist file for telescopic_ota
//Generated by UMN for ALIGN project

module telescopic_ota ( voutn, vss, vinp, vbiasp1, vbiasnd, vbiasn, voutp, vbiasp2, vinn, d1, vdd ); 
input voutn, vss, vinp, vbiasp1, vbiasnd, vbiasn, voutp, vbiasp2, vinn, d1, vdd; 

CMC_PMOS_S_n12_X1_Y1 m2_m1 ( .DA(net012), .G(vbiasp1), .DB(net06),.S(vdd) ); 
DP_NMOS_n12_X3_Y3 m3_m0 ( .DA(net014), .GA(vinn), .S(net10), .DB(net8), .GB(vinp) ); 
CMFB_NMOS_n12_X3_Y1 m5_m4 ( .DA(d1), .S(vss), .DB(net10), .GB(vbiasnd) ); 
CMC_PMOS_n12_X2_Y1 m6_m7 ( .DA(voutn), .G(vbiasp2), .DB(voutp), .SA(net06), .SB(net012) ); 
CMC_NMOS_n12_X3_Y1 m9_m8 ( .DA(voutn), .G(vbiasn), .DB(voutp), .SA(net8), .SB(net014) ); 

endmodule
)foo";

  PnRdatabase db;
  ReadVerilogHelper rvh(db);
  std::istringstream is(str);

  rvh.parse_top( is);

  EXPECT_EQ( db.hierTree.size(), 1);

  const auto& ht = db.hierTree[0];

  EXPECT_EQ( ht.Terminals.size(), 11);

  EXPECT_EQ( ht.Blocks.size(), 5);
  EXPECT_EQ( ht.Nets.size(), 16);
  EXPECT_EQ( ht.Terminals.size(), 11);

  cout << "Nets:";
  for( auto p = ht.Nets.begin(); p != ht.Nets.end(); ++p) {
    cout << " " << p->name;
  }
  cout << endl;

  EXPECT_FALSE( ht.isCompleted);
  EXPECT_FALSE( ht.isTop);

  EXPECT_EQ( ht.width, 0);
  EXPECT_EQ( ht.height, 0);
}

TEST( PnRDBTest, Switched_Capacitor_Filter)
{
  string str =
R"foo(//Verilog block level netlist file for switched_capacitor_filter
//Generated by UMN for ALIGN project 


module switched_capacitor_combination ( Vin, agnd, Vin_ota, Voutn, phi1, phi2 ); 
input Vin, agnd, Vin_ota, Voutn, phi1, phi2;

Cap_60fF c0 ( .MINUS(net63), .PLUS(net72) ); 
Switch_NMOS_n12_X1_Y1 m4 ( .D(net72), .G(phi2), .S(agnd) ); 
Switch_NMOS_n12_X1_Y1 m6 ( .D(net72), .G(phi1), .S(Vin) ); 
DP_NMOS_n12_X1_Y1 m7_m5 ( .DA(Vin_ota), .GA(phi1), .S(net63), .DB(agnd), .GB(phi2) ); 
DP_NMOS_n12_X1_Y1 m0_m3 ( .DA(Voutn), .GA(phi1), .S(net67), .DB(agnd), .GB(phi2) ); 

Cap_30fF_Cap_60fF c1_c3 ( .MINUS1(net67), .PLUS1(net63), .MINUS2(Voutn), .PLUS2(Vin_ota) );
endmodule

module switched_capacitor_filter ( id, voutn, vinn, vss, agnd, vinp, voutp ); 
input id, voutn, vinn, vss, agnd, vinp, voutp;

telescopic_ota xi0 ( .d1(id), .vbiasn(vbiasn), .vbiasnd(vbiasnd), .vbiasp1(vbiasp1), .vbiasp2(vbiasp2), .vdd(vdd), .vinn(net64), .vinp(net66), .voutn(voutn), .voutp(voutp), .vss(vss) ); 
switched_capacitor_combination m6_c0_m4_m3_m5_c1_m7_c3_m0 ( .Vin(vinn), .agnd(agnd), .Vin_ota(net66), .Voutn(voutn), .phi1(phi1), .phi2(phi2) ); 
switched_capacitor_combination m12_c4_m8_m11_m9_c7_m10_c6_m14 ( .Vin(vinp), .agnd(agnd), .Vin_ota(net64), .Voutn(voutp), .phi1(phi1), .phi2(phi2) ); 

Cap_30fF_Cap_30fF c2_c5 ( .MINUS1(net66), .PLUS1(vinp), .MINUS2(net64), .PLUS2(vinn) );
Cap_60fF_Cap_60fF c8_c9 ( .MINUS1(vss), .PLUS1(voutn), .MINUS2(vss), .PLUS2(voutp) );
endmodule

module CMFB_NMOS ( DA, S, DB, GB ); 
input DA, S, DB, GB;

DCL_NMOS_n12_X2_Y1 M0 ( .D(DA), .S(S) ); 
Switch_NMOS_n12_X3_Y1 M1 ( .D(DB), .G(GB), .S(S) ); 

endmodule

module telescopic_ota ( d1, vbiasn, vbiasnd, vbiasp1, vbiasp2, vdd, vinn, vinp, voutn, voutp, vss ); 
input d1, vbiasn, vbiasnd, vbiasp1, vbiasp2, vdd, vinn, vinp, voutn, voutp, vss;

CMC_PMOS_S_n12_X1_Y1 m2_m1 ( .DA(net012), .G(vbiasp1), .DB(net06), .S(vdd) ); 
DP_NMOS_n12_X3_Y2 m3_m0 ( .DA(net014), .GA(vinn), .S(net10), .DB(net8), .GB(vinp) ); 
CMFB_NMOS m5_m4 ( .DA(d1), .S(vss), .DB(net10), .GB(vbiasnd) ); 
CMC_PMOS_n12_X2_Y1 m6_m7 ( .DA(voutn), .G(vbiasp2), .DB(voutp), .SA(net06), .SB(net012) ); 
CMC_NMOS_n12_X3_Y1 m9_m8 ( .DA(voutn), .G(vbiasn), .DB(voutp), .SA(net8), .SB(net014) ); 

endmodule
)foo";

  PnRdatabase db;
  ReadVerilogHelper rvh(db);
  std::istringstream is(str);

  rvh.parse_top( is);
}

TEST( PnRDBTest, VGA)
{
  string str =
R"foo(//Verilog block level netlist file for vga
//Generated by UMN for ALIGN project 


module vga (vps,vgnd,vin1,vin2,vmirror,s0,s1,s2,vga_out1,vga_out2); 
inout vps,vgnd,vin1,vin2,vmirror,s0,s1,s2,vga_out1,vga_out2;

Cap_10f C1 ( .MINUS(vgnd), .PLUS(vga_out1) ); 
Cap_10f C2 ( .MINUS(vgnd), .PLUS(vga_out2) ); 
Switch_NMOS_n10_X4_Y4 Nsw0 ( .D(net5), .G(s0), .S(net5p) ); 
Switch_NMOS_n10_X4_Y4 Nsw1 ( .D(net4), .G(s1), .S(net4p) ); 
Switch_NMOS_n10_X4_Y4 Nsw2 ( .D(net6), .G(s2), .S(net6p) ); 
Res_400 R0 ( .MINUS(vga_out1), .PLUS(vps) ); 
Res_400 R1 ( .MINUS(vga_out2), .PLUS(vps) ); 
CMB_4_n10_A1_B1_C2_D4 xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0 ( .D0(vmirror), .D1(net3), .D2(net6p), .D3(net5p), .D4(net4p), .S(vgnd) ); 
DP_NMOS_n10_X5_Y4 xM20|MN0_xM21|MN0 ( .D1(vga_out1), .G1(vin1), .S(net4), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X8_Y5 xM30|MN0_xM31|MN0 ( .D1(vga_out1), .G1(vin1), .S(net6), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X5_Y2 xM10|MN0_xM11|MN0 ( .D1(vga_out1), .G1(vin1), .S(net5), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X5_Y2 xM00|MN0_xM01|MN0 ( .D1(vga_out1), .G1(vin1), .S(net3), .D2(vga_out2), .G2(vin2) ); 

endmodule


// End HDL models
// Global nets module
`celldefine
module cds_globals;

supply0 vdd!;
supply1 0;

endmodule
`endcelldefine
)foo";

  PnRdatabase db;

  ReadVerilogHelper rvh(db);
  std::istringstream is(str);

  rvh.parse_top( is);
}

TEST( PnRDBTest, Specify)
{
  string str =
R"foo(//Verilog block level netlist file for vga
//Generated by UMN for ALIGN project 


specify
module vga (vps,vgnd,vin1,vin2,vmirror,s0,s1,s2,vga_out1,vga_out2); 
inout vps,vgnd,vin1,vin2,vmirror,s0,s1,s2,vga_out1,vga_out2;

Cap_10f C1 ( .MINUS(vgnd), .PLUS(vga_out1) ); 
Cap_10f C2 ( .MINUS(vgnd), .PLUS(vga_out2) ); 
Switch_NMOS_n10_X4_Y4 Nsw0 ( .D(net5), .G(s0), .S(net5p) ); 
Switch_NMOS_n10_X4_Y4 Nsw1 ( .D(net4), .G(s1), .S(net4p) ); 
Switch_NMOS_n10_X4_Y4 Nsw2 ( .D(net6), .G(s2), .S(net6p) ); 
Res_400 R0 ( .MINUS(vga_out1), .PLUS(vps) ); 
Res_400 R1 ( .MINUS(vga_out2), .PLUS(vps) ); 
CMB_4_n10_A1_B1_C2_D4 xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0 ( .D0(vmirror), .D1(net3), .D2(net6p), .D3(net5p), .D4(net4p), .S(vgnd) ); 
DP_NMOS_n10_X5_Y4 xM20|MN0_xM21|MN0 ( .D1(vga_out1), .G1(vin1), .S(net4), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X8_Y5 xM30|MN0_xM31|MN0 ( .D1(vga_out1), .G1(vin1), .S(net6), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X5_Y2 xM10|MN0_xM11|MN0 ( .D1(vga_out1), .G1(vin1), .S(net5), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X5_Y2 xM00|MN0_xM01|MN0 ( .D1(vga_out1), .G1(vin1), .S(net3), .D2(vga_out2), .G2(vin2) ); 

endmodule

module vga (vps,vgnd,vin1,vin2,vmirror,s0,s1,s2,vga_out1,vga_out2); 
inout vps,vgnd,vin1,vin2,vmirror,s0,s1,s2,vga_out1,vga_out2;

Cap_10f C1 ( .MINUS(vgnd), .PLUS(vga_out1) ); 
Cap_10f C2 ( .MINUS(vgnd), .PLUS(vga_out2) ); 
Switch_NMOS_n10_X4_Y4 Nsw0 ( .D(net5), .G(s0), .S(net5p) ); 
Switch_NMOS_n10_X4_Y4 Nsw1 ( .D(net4), .G(s1), .S(net4p) ); 
Switch_NMOS_n10_X4_Y4 Nsw2 ( .D(net6), .G(s2), .S(net6p) ); 
Res_400 R0 ( .MINUS(vga_out1), .PLUS(vps) ); 
Res_400 R1 ( .MINUS(vga_out2), .PLUS(vps) ); 
CMB_4_n10_A1_B1_C2_D4 xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0 ( .D0(vmirror), .D1(net3), .D2(net6p), .D3(net5p), .D4(net4p), .S(vgnd) ); 
DP_NMOS_n10_X5_Y4 xM20|MN0_xM21|MN0 ( .D1(vga_out1), .G1(vin1), .S(net4), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X8_Y5 xM30|MN0_xM31|MN0 ( .D1(vga_out1), .G1(vin1), .S(net6), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X5_Y2 xM10|MN0_xM11|MN0 ( .D1(vga_out1), .G1(vin1), .S(net5), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X5_Y2 xM00|MN0_xM01|MN0 ( .D1(vga_out1), .G1(vin1), .S(net3), .D2(vga_out2), .G2(vin2) ); 

endmodule
endspecify

// End HDL models
)foo";

  PnRdatabase db;

  ReadVerilogHelper rvh(db);
  std::istringstream is(str);

  rvh.parse_top( is);

  EXPECT_EQ( db.hierTree.size(), 0);


}

TEST( PnRDBTest, SpecifyMixed)
{
  string str =
R"foo(//Verilog block level netlist file for vga
//Generated by UMN for ALIGN project 


specify
module vga (vps,vgnd,vin1,vin2,vmirror,s0,s1,s2,vga_out1,vga_out2); 
inout vps,vgnd,vin1,vin2,vmirror,s0,s1,s2,vga_out1,vga_out2;

Cap_10f C1 ( .MINUS(vgnd), .PLUS(vga_out1) ); 
Cap_10f C2 ( .MINUS(vgnd), .PLUS(vga_out2) ); 
Switch_NMOS_n10_X4_Y4 Nsw0 ( .D(net5), .G(s0), .S(net5p) ); 
Switch_NMOS_n10_X4_Y4 Nsw1 ( .D(net4), .G(s1), .S(net4p) ); 
Switch_NMOS_n10_X4_Y4 Nsw2 ( .D(net6), .G(s2), .S(net6p) ); 
Res_400 R0 ( .MINUS(vga_out1), .PLUS(vps) ); 
Res_400 R1 ( .MINUS(vga_out2), .PLUS(vps) ); 
CMB_4_n10_A1_B1_C2_D4 xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0 ( .D0(vmirror), .D1(net3), .D2(net6p), .D3(net5p), .D4(net4p), .S(vgnd) ); 
DP_NMOS_n10_X5_Y4 xM20|MN0_xM21|MN0 ( .D1(vga_out1), .G1(vin1), .S(net4), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X8_Y5 xM30|MN0_xM31|MN0 ( .D1(vga_out1), .G1(vin1), .S(net6), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X5_Y2 xM10|MN0_xM11|MN0 ( .D1(vga_out1), .G1(vin1), .S(net5), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X5_Y2 xM00|MN0_xM01|MN0 ( .D1(vga_out1), .G1(vin1), .S(net3), .D2(vga_out2), .G2(vin2) ); 

endmodule

endspecify

module telescopic_ota ( voutn, vss, vinp, vbiasp1, vbiasnd, vbiasn, voutp, vbiasp2, vinn, d1, vdd ); 
input voutn, vss, vinp, vbiasp1, vbiasnd, vbiasn, voutp, vbiasp2, vinn, d1, vdd; 

CMC_PMOS_S_n12_X1_Y1 m2_m1 ( .DA(net012), .G(vbiasp1), .DB(net06),.S(vdd) ); 
DP_NMOS_n12_X3_Y3 m3_m0 ( .DA(net014), .GA(vinn), .S(net10), .DB(net8), .GB(vinp) ); 
CMFB_NMOS_n12_X3_Y1 m5_m4 ( .DA(d1), .S(vss), .DB(net10), .GB(vbiasnd) ); 
CMC_PMOS_n12_X2_Y1 m6_m7 ( .DA(voutn), .G(vbiasp2), .DB(voutp), .SA(net06), .SB(net012) ); 
CMC_NMOS_n12_X3_Y1 m9_m8 ( .DA(voutn), .G(vbiasn), .DB(voutp), .SA(net8), .SB(net014) ); 

endmodule

specify
module vga (vps,vgnd,vin1,vin2,vmirror,s0,s1,s2,vga_out1,vga_out2); 
inout vps,vgnd,vin1,vin2,vmirror,s0,s1,s2,vga_out1,vga_out2;

Cap_10f C1 ( .MINUS(vgnd), .PLUS(vga_out1) ); 
Cap_10f C2 ( .MINUS(vgnd), .PLUS(vga_out2) ); 
Switch_NMOS_n10_X4_Y4 Nsw0 ( .D(net5), .G(s0), .S(net5p) ); 
Switch_NMOS_n10_X4_Y4 Nsw1 ( .D(net4), .G(s1), .S(net4p) ); 
Switch_NMOS_n10_X4_Y4 Nsw2 ( .D(net6), .G(s2), .S(net6p) ); 
Res_400 R0 ( .MINUS(vga_out1), .PLUS(vps) ); 
Res_400 R1 ( .MINUS(vga_out2), .PLUS(vps) ); 
CMB_4_n10_A1_B1_C2_D4 xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0 ( .D0(vmirror), .D1(net3), .D2(net6p), .D3(net5p), .D4(net4p), .S(vgnd) ); 
DP_NMOS_n10_X5_Y4 xM20|MN0_xM21|MN0 ( .D1(vga_out1), .G1(vin1), .S(net4), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X8_Y5 xM30|MN0_xM31|MN0 ( .D1(vga_out1), .G1(vin1), .S(net6), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X5_Y2 xM10|MN0_xM11|MN0 ( .D1(vga_out1), .G1(vin1), .S(net5), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X5_Y2 xM00|MN0_xM01|MN0 ( .D1(vga_out1), .G1(vin1), .S(net3), .D2(vga_out2), .G2(vin2) ); 

endmodule

endspecify


// End HDL models
)foo";

  PnRdatabase db;

  ReadVerilogHelper rvh(db);
  std::istringstream is(str);

  rvh.parse_top( is);

  EXPECT_EQ( db.hierTree.size(), 1);

  const auto& ht = db.hierTree[0];

  EXPECT_EQ( ht.Terminals.size(), 11);

  EXPECT_EQ( ht.Blocks.size(), 5);
  EXPECT_EQ( ht.Nets.size(), 16);
  EXPECT_EQ( ht.Terminals.size(), 11);

  cout << "Nets:";
  for( auto p = ht.Nets.begin(); p != ht.Nets.end(); ++p) {
    cout << " " << p->name;
  }
  cout << endl;

  EXPECT_FALSE( ht.isCompleted);
  EXPECT_FALSE( ht.isTop);

  EXPECT_EQ( ht.width, 0);
  EXPECT_EQ( ht.height, 0);

}


TEST( PnRDBTest, SpecifyCelldefine)
{
  string str =
R"foo(//Verilog block level netlist file for switched_capacitor_filter
//Generated by UMN for ALIGN project 


module switched_capacitor_combination ( Vin, Vin_ota, Voutn, phi1, phi2 ); 
input Vin, Vin_ota, Voutn, phi1, phi2;

Cap_60fF c0 ( .MINUS(net63), .PLUS(net72) ); 
Cap_30fF c1 ( .MINUS(net67), .PLUS(net63) ); 
Cap_60fF c3 ( .MINUS(Voutn), .PLUS(Vin_ota) ); 
Switch_NMOS_n12_X2_Y1 m4 ( .D(net72), .G(phi2), .S(analog_gnd) ); 
Switch_NMOS_n12_X2_Y1 m6 ( .D(net72), .G(phi1), .S(Vin) ); 
DP_NMOS_n12_X2_Y1 m7_m5 ( .DA(Vin_ota), .GA(phi1), .S(net63), .DB(analog_gnd), .GB(phi2) ); 
DP_NMOS_n12_X2_Y1 m0_m3 ( .DA(Voutn), .GA(phi1), .S(net67), .DB(analog_gnd), .GB(phi2) ); 

endmodule


module switched_capacitor_filter ( voutn, voutp, vinp, vinn, id ); 
telescopic_ota xi0 ( .d1(id), .vbiasn(vbiasn), .vbiasnd(vbiasnd), .vbiasp1(vbiasp1), .vbiasp2(vbiasp2), .vinn(net64), .vinp(net66), .voutn(voutn), .voutp(voutp) ); 
switched_capacitor_combination m6_c0_m4_m3_m5_c1_m7_c3_m0 ( .Vin(vinn), .Vin_ota(net66), .Voutn(voutn), .phi1(phi1), .phi2(phi2) ); 
switched_capacitor_combination m12_c4_m8_m11_m9_c7_m10_c6_m14 ( .Vin(vinp), .Vin_ota(net64), .Voutn(voutp), .phi1(phi1), .phi2(phi2) ); 

endmodule

module telescopic_ota ( d1, vbiasn, vbiasnd, vbiasp1, vbiasp2, vinn, vinp, voutn, voutp ); 
input d1, vbiasn, vbiasnd, vbiasp1, vbiasp2, vinn, vinp, voutn, voutp;
specify
    specparam CDS_LIBNAME = "pcell";
    specparam CDS_CELLNAME = "telescopic_ota";
    specparam CDS_VIEWNAME = "schematic";
endspecify
CMC_PMOS_S_n12_X2_Y1 m2_m1 ( .DA(net012), .G(vbiasp1), .DB(net06), .S(analog_vdd) ); 
DP_NMOS_n12_X2_Y1 m3_m0 ( .DA(net014), .GA(vinn), .S(net10), .DB(net8), .GB(vinp) ); 
CMFB_NMOS_n12_X2_Y1 m5_m4 ( .DA(d1), .S(analog_gnd), .DB(net10), .GB(vbiasnd) ); 
CMC_PMOS_n12_X2_Y1 m6_m7 ( .DA(voutn), .G(vbiasp2), .DB(voutp), .SA(net06), .SB(net012) ); 
CMC_NMOS_n12_X2_Y1 m9_m8 ( .DA(voutn), .G(vbiasn), .DB(voutp), .SA(net8), .SB(net014) ); 

endmodule

`celldefine
module analog_power;
supply0 analog_gnd;
supply1 analog_vdd;
endmodule
`endcelldefine
)foo";

  PnRdatabase db;

  ReadVerilogHelper rvh(db);
  std::istringstream is(str);

  rvh.parse_top( is);

  EXPECT_EQ( db.hierTree.size(), 3);

  EXPECT_EQ( rvh.get_Supply_node().Blocks.size(), 2);
  EXPECT_EQ( rvh.get_Supply_node().Blocks.at(0).instance.at(0).name, "analog_gnd");
  EXPECT_EQ( rvh.get_Supply_node().Blocks.at(1).instance.at(0).name, "analog_vdd");

}
