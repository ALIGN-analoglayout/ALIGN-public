* simulator lang = spectre
* global 0
.param Fs=2G VDD=1
* include "/home/techfile/IBM65nm/IBM_PDK/cmos10lpe/V1.6.0.0RF/Spectre/models/design.scs"
.model dgnfet nmos l=1 w=1 nfin=1 nf=1
.model dgpfet pmos l=1 w=1 nfin=1 nf=1
.model vncap cap w=23.9u l=24.0u botlev=1 toplev=1 setind=-1 rsx=50 botcap=-1 dtemp=0
.subckt Delay_Unit CN CP EN\<1\> EN\<2\> EN\<3\> EN\<4\> EX\<1\> EX\<2\> EX\<3\> EX\<4\> IN OUT VDD VSS
	M29 net0142 VDD VDD VDD pfet l=100n w=800n nf=1
	M33 net136 CP net0142 VDD pfet l=100n w=800n nf=1
	M34 net0142 EN\<4\> VDD VDD pfet l=200n w=800n nf=1
	M25 net136 VDD VDD VDD pfet l=100n w=800n nf=1
	M32 net136 CP VDD VDD pfet l=100n w=800n nf=1
	M27 VDD VDD VDD VDD pfet l=100n w=800n nf=1
	M16 net125 IN net180 VSS lvtnfet l=100n w=400n nf=1
	M15 net180 VSS EN\<1\> VSS lvtnfet l=60n w=400n nf=1
	M24 EN\<1\> net125 EN\<1\> VSS lvtnfet l=60n w=400n nf=1
	M14 EN\<1\> VSS EN\<2\> VSS lvtnfet l=60n w=400n nf=1
	M23 EN\<2\> net125 EN\<2\> VSS lvtnfet l=60n w=400n nf=1
	M17 EN\<3\> net125 EN\<3\> VSS lvtnfet l=60n w=400n nf=1
	M13 EN\<2\> VSS EN\<3\> VSS lvtnfet l=60n w=400n nf=1
	M12 EN\<3\> VSS VSS VSS lvtnfet l=60n w=400n nf=1
	M22 OUT net125 VSS VSS lvtnfet l=60n w=800n nf=1
	M6 EX\<3\> VDD VDD VDD lvtpfet l=60n w=800n nf=1
	M11 EX\<3\> net125 EX\<3\> VDD lvtpfet l=60n w=800n nf=1
	M8 EX\<2\> net125 EX\<2\> VDD lvtpfet l=60n w=800n nf=1
	M4 EX\<1\> VDD EX\<2\> VDD lvtpfet l=60n w=800n nf=1
	M9 EX\<1\> net125 EX\<1\> VDD lvtpfet l=60n w=800n nf=1
	M3 net136 VDD EX\<1\> VDD lvtpfet l=60n w=800n nf=1
	M5 EX\<2\> VDD EX\<3\> VDD lvtpfet l=60n w=800n nf=1
	M7 net125 IN net136 VDD lvtpfet l=100n w=800n nf=1
	M10 OUT net125 VDD VDD lvtpfet l=60n w=800n nf=1
	M38 VSS VSS VSS VSS nfet l=100n w=400n nf=1
	M35 net180 CN VSS VSS nfet l=100n w=400n nf=1
	M42 net180 VSS VSS VSS nfet l=100n w=400n nf=1
	M37 net193 EX\<4\> VSS VSS nfet l=200n w=400n nf=1
	M39 net193 VSS VSS VSS nfet l=100n w=400n nf=1
	M36 net180 CN net193 VSS nfet l=100n w=400n nf=1
.ends Delay_Unit
.subckt INV2 I ZN VDD VSS
	M2 ZN I VSS VSS lvtnfet l=60n w=390.0n nf=1
	M0 ZN I VDD VDD lvtpfet l=60n w=520.0n nf=1
.ends INV2
.subckt Delay_Chain CP ENB1\<1\> ENB1\<2\> ENB1\<3\> ENB1\<4\> ENB2\<1\> ENB2\<2\> ENB2\<3\> ENB2\<4\> ENB3\<1\> ENB3\<2\> ENB3\<3\> ENB3\<4\> ENB4\<1\> ENB4\<2\> ENB4\<3\> ENB4\<4\> ENB5\<1\> ENB5\<2\> ENB5\<3\> ENB5\<4\> ENB6\<1\> ENB6\<2\> ENB6\<3\> ENB6\<4\> ENB7\<1\> ENB7\<2\> ENB7\<3\> ENB7\<4\> ENB8\<1\> ENB8\<2\> ENB8\<3\> ENB8\<4\> O\<0\> O\<1\> O\<2\> O\<3\> O\<4\> O\<5\> O\<6\> O\<7\> O\<8\> VDD VSS CN
	xI8 CN CP EN8\<1\> EN8\<2\> EN8\<3\> EN8\<4\> EX8\<1\> EX8\<2\> EX8\<3\> EX8\<4\> O\<7\> O\<8\> VDD VSS Delay_Unit
	xI7 CN CP EN7\<1\> EN7\<2\> EN7\<3\> EN7\<4\> EX7\<1\> EX7\<2\> EX7\<3\> EX7\<4\> O\<6\> O\<7\> VDD VSS Delay_Unit
	xI6 CN CP EN6\<1\> EN6\<2\> EN6\<3\> EN6\<4\> EX6\<1\> EX6\<2\> EX6\<3\> EX6\<4\> O\<5\> O\<6\> VDD VSS Delay_Unit
	xI5 CN CP EN5\<1\> EN5\<2\> EN5\<3\> EN5\<4\> EX5\<1\> EX5\<2\> EX5\<3\> EX5\<4\> O\<4\> O\<5\> VDD VSS Delay_Unit
	xI4 CN CP EN4\<1\> EN4\<2\> EN4\<3\> EN4\<4\> EX4\<1\> EX4\<2\> EX4\<3\> EX4\<4\> O\<3\> O\<4\> VDD VSS Delay_Unit
	xI3 CN CP EN3\<1\> EN3\<2\> EN3\<3\> EN3\<4\> EX3\<1\> EX3\<2\> EX3\<3\> EX3\<4\> O\<2\> O\<3\> VDD VSS Delay_Unit
	xI2 CN CP EN2\<1\> EN2\<2\> EN2\<3\> EN2\<4\> EX2\<1\> EX2\<2\> EX2\<3\> EX2\<4\> O\<1\> O\<2\> VDD VSS Delay_Unit
	xI1 CN CP EN1\<1\> EN1\<2\> EN1\<3\> EN1\<4\> EX1\<1\> EX1\<2\> EX1\<3\> EX1\<4\> O\<0\> O\<1\> VDD VSS Delay_Unit
	M1 VSS CN VSS VSS dgnfet l=280.0n w=1.125u nf=1
	xI81 EN8\<4\> EX8\<4\> VDD VSS INV2
	xI80 EN7\<4\> EX7\<4\> VDD VSS INV2
	xI79 EN6\<4\> EX6\<4\> VDD VSS INV2
	xI78 EN5\<4\> EX5\<4\> VDD VSS INV2
	xI77 EN4\<4\> EX4\<4\> VDD VSS INV2
	xI76 EN3\<4\> EX3\<4\> VDD VSS INV2
	xI75 EN2\<4\> EX2\<4\> VDD VSS INV2
	xI74 EN1\<4\> EX1\<4\> VDD VSS INV2
	xI73 ENB8\<4\> EN8\<4\> VDD VSS INV2
	xI72 ENB8\<3\> EN8\<3\> VDD VSS INV2
	xI71 EN8\<3\> EX8\<3\> VDD VSS INV2
	xI70 ENB8\<2\> EN8\<2\> VDD VSS INV2
	xI69 EN8\<2\> EX8\<2\> VDD VSS INV2
	xI68 ENB8\<1\> EN8\<1\> VDD VSS INV2
	xI67 EN8\<1\> EX8\<1\> VDD VSS INV2
	xI65 EN7\<1\> EX7\<1\> VDD VSS INV2
	xI64 ENB7\<1\> EN7\<1\> VDD VSS INV2
	xI63 EN7\<2\> EX7\<2\> VDD VSS INV2
	xI62 ENB7\<2\> EN7\<2\> VDD VSS INV2
	xI61 EN7\<3\> EX7\<3\> VDD VSS INV2
	xI60 ENB7\<3\> EN7\<3\> VDD VSS INV2
	xI59 ENB7\<4\> EN7\<4\> VDD VSS INV2
	xI57 ENB6\<1\> EN6\<1\> VDD VSS INV2
	xI56 ENB6\<2\> EN6\<2\> VDD VSS INV2
	xI55 ENB6\<3\> EN6\<3\> VDD VSS INV2
	xI54 EN6\<1\> EX6\<1\> VDD VSS INV2
	xI53 EN6\<2\> EX6\<2\> VDD VSS INV2
	xI52 EN6\<3\> EX6\<3\> VDD VSS INV2
	xI50 ENB6\<4\> EN6\<4\> VDD VSS INV2
	xI49 ENB5\<4\> EN5\<4\> VDD VSS INV2
	xI47 EN5\<3\> EX5\<3\> VDD VSS INV2
	xI46 EN5\<2\> EX5\<2\> VDD VSS INV2
	xI45 EN5\<1\> EX5\<1\> VDD VSS INV2
	xI44 ENB5\<3\> EN5\<3\> VDD VSS INV2
	xI43 ENB5\<2\> EN5\<2\> VDD VSS INV2
	xI42 ENB5\<1\> EN5\<1\> VDD VSS INV2
	xI41 ENB4\<1\> EN4\<1\> VDD VSS INV2
	xI40 ENB4\<2\> EN4\<2\> VDD VSS INV2
	xI39 ENB4\<3\> EN4\<3\> VDD VSS INV2
	xI38 EN4\<1\> EX4\<1\> VDD VSS INV2
	xI37 EN4\<2\> EX4\<2\> VDD VSS INV2
	xI36 EN4\<3\> EX4\<3\> VDD VSS INV2
	xI34 ENB4\<4\> EN4\<4\> VDD VSS INV2
	xI33 ENB3\<4\> EN3\<4\> VDD VSS INV2
	xI31 EN3\<3\> EX3\<3\> VDD VSS INV2
	xI30 EN3\<2\> EX3\<2\> VDD VSS INV2
	xI29 EN3\<1\> EX3\<1\> VDD VSS INV2
	xI28 ENB3\<3\> EN3\<3\> VDD VSS INV2
	xI27 ENB3\<2\> EN3\<2\> VDD VSS INV2
	xI26 ENB3\<1\> EN3\<1\> VDD VSS INV2
	xI25 ENB2\<1\> EN2\<1\> VDD VSS INV2
	xI24 ENB2\<2\> EN2\<2\> VDD VSS INV2
	xI23 ENB2\<3\> EN2\<3\> VDD VSS INV2
	xI22 EN2\<1\> EX2\<1\> VDD VSS INV2
	xI21 EN2\<2\> EX2\<2\> VDD VSS INV2
	xI20 EN2\<3\> EX2\<3\> VDD VSS INV2
	xI18 ENB2\<4\> EN2\<4\> VDD VSS INV2
	xI15 ENB1\<4\> EN1\<4\> VDD VSS INV2
	xI14 EN1\<3\> EX1\<3\> VDD VSS INV2
	xI13 ENB1\<3\> EN1\<3\> VDD VSS INV2
	xI12 EN1\<2\> EX1\<2\> VDD VSS INV2
	xI11 ENB1\<2\> EN1\<2\> VDD VSS INV2
	xI10 EN1\<1\> EX1\<1\> VDD VSS INV2
	xI9 ENB1\<1\> EN1\<1\> VDD VSS INV2
	C1 CN VSS vncap w=23.9u l=24.0u botlev=1 toplev=1 setind=-1 rsx=50 botcap=-1 dtemp=0
	C0 CP VSS vncap w=23.9u l=24.0u botlev=1 toplev=1 setind=-1 rsx=50 botcap=-1 dtemp=0
	M0 VDD CP VDD VDD dgpfet l=280.0n w=1.125u nf=1
.ends Delay_Chain
.subckt INV6 I ZN VDD VSS
	M2 ZN I VSS VSS lvtnfet l=60n w=390.0n nf=1
	M0 ZN I VDD VDD lvtpfet l=60n w=520.0n nf=1
.ends INV6
.subckt Trans_Gate I O VDD VSS
	M2 I VDD O VSS lvtnfet l=60n w=390.0n nf=1
	M0 I VSS O VDD lvtpfet l=60n w=520.0n nf=1
.ends Trans_Gate
.subckt BUFF6 I Z VDD VSS
	M14 Z net6 VDD VDD lvtpfet l=60n w=520.0n nf=1
	M12 net6 I VDD VDD lvtpfet l=60n w=520.0n nf=1
	M15 Z net6 VSS VSS lvtnfet l=60n w=390.0n nf=1
	M13 net6 I VSS VSS lvtnfet l=60n w=390.0n nf=1
.ends BUFF6
.subckt BUFF20 I Z VDD VSS
	M14 Z net8 VDD VDD lvtpfet l=60n w=520.0n nf=1
	M12 net8 I VDD VDD lvtpfet l=60n w=520.0n nf=1
	M1 Z net8 VSS VSS lvtnfet l=60n w=370.0n nf=1
	M15 Z net8 VSS VSS lvtnfet l=60n w=390.0n nf=1
	M0 net8 I VSS VSS lvtnfet l=60n w=300n nf=1
	M13 net8 I VSS VSS lvtnfet l=60n w=390.0n nf=1
.ends BUFF20
.subckt Phase_Detector CKI CK_DLL CK_REF DN DP UN UP VDD VSS
	xI53 net112 DP VDD VSS INV6
	xI48 net111 UP VDD VSS INV6
	xI0 net104 net112 VDD VSS Trans_Gate
	xI1 net103 net111 VDD VSS Trans_Gate
	xI52 net104 DN VDD VSS BUFF6
	xI38 net103 UN VDD VSS BUFF6
	xI2 CKI CK_REF VDD VSS BUFF20
	M1 net104 CK_DLL net114 VSS lvtnfet l=60n w=800n nf=1
	M33 net114 net98 VSS VSS lvtnfet l=60n w=800n nf=1
	M39 net98 CK_REF VSS VSS lvtnfet l=60n w=800n nf=1
	M35 net103 CK_REF net113 VSS lvtnfet l=60n w=800n nf=1
	M31 net113 net97 VSS VSS lvtnfet l=60n w=800n nf=1
	M29 net97 CK_DLL VSS VSS lvtnfet l=60n w=800n nf=1
	M3 net115 CK_REF VDD VDD lvtpfet l=60n w=450.0n nf=1
	M2 net98 CK_DLL net115 VDD lvtpfet l=60n w=450.0n nf=1
	M0 net104 net98 VDD VDD lvtpfet l=60n w=450.0n nf=1
	M32 net103 net97 VDD VDD lvtpfet l=60n w=450.0n nf=1
	M34 net116 CK_DLL VDD VDD lvtpfet l=60n w=450.0n nf=1
	M0 net97 CK_REF net116 VDD lvtpfet l=60n w=450.0n nf=1
.ends Phase_Detector
.subckt Charge_Pump CN CP DN DP IBS UN UP VDD VSS
	M0 VDD IBS VDD VDD dgpfet l=280.0n w=1.18u nf=1
	M14 Nz IBS VDD VDD pfet l=200n w=800n nf=1
	M10 net0128 net38 VSS VSS nfet l=200n w=800n nf=1
	M3 Ny IBS VDD VDD pfet l=200n w=800n nf=1
	M13 Nz IBS VDD VDD pfet l=200n w=800n nf=1
	M18 CP CP VDD VDD pfet l=100n w=800n nf=1
	M7 net0121 IBS VDD VDD pfet l=200n w=800n nf=1
	M6 IBS IBS VDD VDD pfet l=200n w=800n nf=1
	M16 net38 net38 VSS VSS nfet l=200n w=800n nf=1
	M26 CP CN VSS VSS nfet l=100n w=800n nf=1
	M1 Nx net0121 VSS VSS nfet l=200n w=400n nf=1
	M8 net0121 net0121 VSS VSS nfet l=200n w=400n nf=1
	M4 CN DP Nx VSS lvtnfet l=60n w=400n nf=1
	M9 net0128 DN Nx VSS lvtnfet l=60n w=400n nf=1
	M11 net0128 net0128 Nz VDD lvtpfet l=60n w=800n nf=1
	M12 net38 CN Nz VDD lvtpfet l=60n w=800n nf=1
	M17 net0128 UP Ny VDD lvtpfet l=60n w=800n nf=1
	M2 CN UN Ny VDD lvtpfet l=60n w=800n nf=1
.ends Charge_Pump
.subckt GF65_DLL_sanitized CKI CK_REF ENB1\<1\> ENB1\<2\> ENB1\<3\> ENB1\<4\> ENB2\<1\> ENB2\<2\> ENB2\<3\> ENB2\<4\> ENB3\<1\> ENB3\<2\> ENB3\<3\> ENB3\<4\> ENB4\<1\> ENB4\<2\> ENB4\<3\> ENB4\<4\> ENB5\<1\> ENB5\<2\> ENB5\<3\> ENB5\<4\> ENB6\<1\> ENB6\<2\> ENB6\<3\> ENB6\<4\> ENB7\<1\> ENB7\<2\> ENB7\<3\> ENB7\<4\> ENB8\<1\> ENB8\<2\> ENB8\<3\> ENB8\<4\> IBS O\<1\> O\<2\> O\<3\> O\<4\> O\<5\> O\<6\> O\<7\> O\<8\> VDD VSS V_CTRLn V_CTRLp
	xI54 V_CTRLp ENB1\<1\> ENB1\<2\> ENB1\<3\> ENB1\<4\> ENB2\<1\> ENB2\<2\> ENB2\<3\> ENB2\<4\> ENB3\<1\> ENB3\<2\> ENB3\<3\> ENB3\<4\> ENB4\<1\> ENB4\<2\> ENB4\<3\> ENB4\<4\> ENB5\<1\> ENB5\<2\> ENB5\<3\> ENB5\<4\> ENB6\<1\> ENB6\<2\> ENB6\<3\> ENB6\<4\> ENB7\<1\> ENB7\<2\> ENB7\<3\> ENB7\<4\> ENB8\<1\> ENB8\<2\> ENB8\<3\> ENB8\<4\> CK_REF O\<1\> O\<2\> O\<3\> O\<4\> O\<5\> O\<6\> O\<7\> O\<8\> VDD VSS V_CTRLn Delay_Chain
	xI5 CKI O\<8\> CK_REF DN DP UN UP VDD VSS Phase_Detector
	xI52 V_CTRLn V_CTRLp DN DP IBS UN UP VDD VSS Charge_Pump
.ends GF65_DLL_sanitized
	* V3 net08 0 vsource dc=0 type=pulse val0=0 val1=VDD period=1/Fs delay=10n rise=10p fall=10p width=0.5/Fs
	* xI6 net08 CK_REF VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD VDD net07 CK\<1\> CK\<2\> CK\<3\> CK\<4\> CK\<5\> CK\<6\> CK\<7\> CK\<8\> VDD VSS V_CTRLn V_CTRLp GF65_DLL_sanitized
	* V28 VSS 0 vsource dc=0 type=dc
	* V26 VDD 0 vsource dc=VDD type=dc
	* xI8 net07 0 isource dc=20u type=dc
