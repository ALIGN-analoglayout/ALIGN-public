import textwrap


def comparator(name):
    netlist = textwrap.dedent(f"""\
        .subckt {name} clk vccx vin vip von vop vssx
        mn0 vcom clk vssx vssx n w=2.88e-6 m=1 nf=16
        mn1 vin_d vin vcom vssx n w=360e-9 m=18 nf=2
        mn2 vip_d vip vcom vssx n w=360e-9 m=18 nf=2
        mn3 vin_o vip_o vin_d vssx n w=360e-9 m=8 nf=2
        mn4 vip_o vin_o vip_d vssx n w=360e-9 m=8 nf=2
        mp5 vin_o vip_o vccx vccx p w=360e-9 m=6 nf=2
        mp6 vip_o vin_o vccx vccx p w=360e-9 m=6 nf=2
        mp7 vin_d clk vccx vccx p w=360e-9 m=1 nf=2
        mp8 vip_d clk vccx vccx p w=360e-9 m=1 nf=2
        mp9 vin_o clk vccx vccx p w=360e-9 m=2 nf=2
        mp10 vip_o clk vccx vccx p w=360e-9 m=2 nf=2
        mn11 von vin_o vssx vssx n w=360e-9 m=1 nf=2
        mn12 vop vip_o vssx vssx n w=360e-9 m=1 nf=2
        mp13 von vin_o vccx vccx p w=360e-9 m=1 nf=2
        mp14 vop vip_o vccx vccx p w=360e-9 m=1 nf=2
        .ends {name}
    """)
    return netlist


def ota_six(name):
    netlist = textwrap.dedent(f"""\
        .subckt {name} ibias vccx vssx  von vin vip
        //mn1 ibias ibias vssx vssx n w=360e-9 nf=2 m=1
        mn1 ibias ibias vssx vssx n w=360e-9 nf=2 m=8
        mn2 tail  ibias vssx vssx n w=360e-9 nf=2 m=8
        mn3 vop vip tail vssx n w=360e-9 nf=2 m=16
        mn4 von vin tail vssx n w=360e-9 nf=2 m=16
        mp5 vop vop vccx vccx p w=360e-9 nf=2 m=4
        mp6 von vop vccx vccx p w=360e-9 nf=2 m=4
        .ends {name}
    """)
    return netlist


def common_source(name):
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vccx vssx
        mp0 vop vop vccx vccx p w=720e-9 nf=4 m=4
        mn0 vop vin vssx vssx n w=720e-9 nf=4 m=4
        .ends {name}
    """)
    return netlist


def common_source_mini(name):
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vccx vssx
        mp0 vop vop vccx vccx p w=360e-9 nf=2 m=1
        mn0 vop vin vssx vssx n w=360e-9 nf=2 m=1
        .ends {name}
    """)
    return netlist


def tia(name):
    netlist = textwrap.dedent(f"""\
        .subckt pcell_mos d g s b
        M0 d g s b n w=720e-9 nf=4 m=4
        .ends pcell_mos
        .subckt pcell_tfr_0 a b
        xi0 a b tfr_prim w=1e-6 l=1e-6
        .ends pcell_tfr_0
        .subckt {name} vin vop vccx vssx
        mp0 vop vin vccx vccx p w=720e-9 nf=4 m=4
        mn0 vop vin vssx vssx n w=720e-9 nf=4 m=4
        xi0 vin vop pcell_tfr_0
        xi1 vin vop vssx vssx pcell_mos
        .ends {name}
    """)
    return netlist


def ldo_amp(name):
    netlist = textwrap.dedent(f"""\
        .model nlplvt nmos l=1 w=1 nf=1 m=1 stack=1 parallel=1
        .model plplvt pmos l=1 w=1 nf=1 m=1 stack=1 parallel=1
        .subckt nlplvt_s_pcell_0 d g s b
        .param m=1
        mi1 d g inet1 b nlplvt w=180e-9 m=1 nf=1
        mi2 inet1 g inet2 b nlplvt w=180e-9 m=1 nf=1
        mi3 inet2 g inet3 b nlplvt w=180e-9 m=1 nf=1
        mi4 inet3 g s b nlplvt w=180e-9 m=1 nf=1
        .ends nlplvt_s_pcell_0

        .subckt nlplvt_s_pcell_1 d g s b
        .param m=1
        mi1 d g inet1 b nlplvt w=180e-9 m=1 nf=1
        mi2 inet1 g s b nlplvt w=180e-9 m=1 nf=1
        .ends nlplvt_s_pcell_1

        .subckt nlplvt_s_pcell_2 d g s b
        .param m=1
        mi1 d g inet1 b nlplvt w=180e-9 m=1 nf=1
        mi2 inet1 g s b nlplvt w=180e-9 m=1 nf=1
        .ends nlplvt_s_pcell_2

        .subckt nlplvt_s_pcell_3 d g s b
        .param m=1
        mi1 d g inet1 b nlplvt w=180e-9 m=1 nf=1
        mi2 inet1 g s b nlplvt w=180e-9 m=1 nf=1
        .ends nlplvt_s_pcell_3

        .subckt nlplvt_s_pcell_4 d g s b
        .param m=1
        mi1 d g inet1 b nlplvt w=180e-9 m=1 nf=1
        mi2 inet1 g inet2 b nlplvt w=180e-9 m=1 nf=1
        mi3 inet2 g inet3 b nlplvt w=180e-9 m=1 nf=1
        mi4 inet3 g s b nlplvt w=180e-9 m=1 nf=1
        .ends nlplvt_s_pcell_4

        .subckt plplvt_s_pcell_5 d g s b
        .param m=1
        mi2 inet1 g s b plplvt w=180e-9 m=1 nf=1
        mi1 d g inet1 b plplvt w=180e-9 m=1 nf=1
        .ends plplvt_s_pcell_5

        .subckt plplvt_s_pcell_6 d g s b
        .param m=1
        mi2 inet1 g s b plplvt w=180e-9 m=1 nf=1
        mi1 d g inet1 b plplvt w=180e-9 m=1 nf=1
        .ends plplvt_s_pcell_6

        .subckt plplvt_s_pcell_7 d g s b
        .param m=1
        mi2 inet1 g s b plplvt w=180e-9 m=1 nf=1
        mi1 d g inet1 b plplvt w=180e-9 m=1 nf=1
        .ends plplvt_s_pcell_7

        .subckt {name} vbias_an vccx vfb vg v1 vref vssx vbias_bf en
        xmn56 vbias6 vbias_bf vssx vssx nlplvt_s_pcell_0 m=4
        xmn20 v5 v4 vssx vssx nlplvt_s_pcell_1 m=8
        xmn40 vssx vbias_bf vssx vssx nlplvt_s_pcell_0 m=4
        xmn41 vbias4 vbias_an vssx vssx nlplvt_s_pcell_0 m=4
        xmn21 vbias2 vbias1 vbias3 vssx nlplvt_s_pcell_2 m=4
        xmn37 v6 v4 vssx vssx nlplvt_s_pcell_1 m=8
        xmn22 v1 vref vcom1 vssx nlplvt_s_pcell_3 m=20
        xmn23 v2 vfb vcom1 vssx nlplvt_s_pcell_3 m=20
        xmn38 v4 vbias3 v6 vssx nlplvt_s_pcell_1 m=8
        xmn39 v3 vbias3 v5 vssx nlplvt_s_pcell_1 m=8
        xmn55 v3_d vbias_bf vssx vssx nlplvt_s_pcell_4 m=8
        xmn3 vssx vbias_an vssx vssx nlplvt_s_pcell_0 m=4
        xmn2 vcom1 vbias_an vssx vssx nlplvt_s_pcell_4 m=8
        mp23 vg en vccx vccx plplvt w=360e-9 m=1 nf=2
        mp221 v3 en vccx vccx plplvt w=360e-9 m=1 nf=2
        mp24 enb en vccx vccx plplvt w=360e-9 m=1 nf=2
        mp5 vg vg vccx vccx plplvt w=720e-9 m=1 nf=4
        mp29 v4 vbias2 v2 vccx plplvt w=2.16e-6 m=1 nf=12
        mp30 v3 vbias2 v1 vccx plplvt w=2.16e-6 m=1 nf=12
        mp33 vbias2 vbias2 vbias1 vccx plplvt w=1.44e-6 m=1 nf=8
        mp1 v3_d v3 vg vccx plplvt w=1.44e-6 m=1 nf=8
        xmp41 vbias6 vbias6 vccx vccx plplvt_s_pcell_5 m=4
        xmp4 vg vbias6 vccx vccx plplvt_s_pcell_6 m=8
        xmp22 v1 vbias1 vccx vccx plplvt_s_pcell_7 m=12
        xmp34 vbias1 vbias1 vccx vccx plplvt_s_pcell_5 m=4
        xmp28 v2 vbias1 vccx vccx plplvt_s_pcell_7 m=12
        mn11 v3_d enb vssx vssx nlplvt w=360e-9 m=1 nf=2
        mn12 enb en vssx vssx nlplvt w=360e-9 m=1 nf=2
        mn322 vg v3_d vssx vssx nlplvt w=720e-9 m=1 nf=4
        mn42 vbias3 vbias3 vbias4 vssx nlplvt w=1.44e-6 m=2 nf=8
        .ends {name}
    """)
    return netlist


def ro_simple(name):
    netlist = textwrap.dedent(f"""\
        .subckt ro_stage vi vo vccx vssx
        mp0 vo vi vccx vccx p w=360e-9 m=1 nf=2
        mn0 vo vi vssx vssx n w=360e-9 m=1 nf=2
        .ends
        .subckt {name} vo vccx vssx
        xi0 vo v1 vccx vssx ro_stage
        xi1 v1 v2 vccx vssx ro_stage
        xi2 v2 v3 vccx vssx ro_stage
        xi3 v3 v4 vccx vssx ro_stage
        xi4 v4 vo vccx vssx ro_stage
        .ends {name}
    """)
    return netlist


def two_stage_ota_differential(name):
    netlist = textwrap.dedent(f"""\
        .subckt p_s_pcell_3 d g s b
        .param m=1
        mi2 inet1 g s b p w=180e-9 m=1 nf=1
        mi1 d g inet1 b p w=180e-9 m=1 nf=1
        .ends p_s_pcell_3

        .subckt p_s_pcell_4 d g s b
        .param m=1
        mi2 inet1 g s b p w=180e-9 m=1 nf=1
        mi1 d g inet1 b p w=180e-9 m=1 nf=1
        .ends p_s_pcell_4

        .subckt p_s_pcell_5 d g s b
        .param m=1
        mi2 inet1 g s b p w=180e-9 m=1 nf=1
        mi1 d g inet1 b p w=180e-9 m=1 nf=1
        .ends p_s_pcell_5

        .subckt n_s_pcell_6 d g s b
        .param m=1
        mi1 d g inet1 b n w=180e-9 m=1 nf=1
        mi2 inet1 g s b n w=180e-9 m=1 nf=1
        .ends n_s_pcell_6

        .subckt n_s_pcell_7 d g s b
        .param m=1
        mi1 d g inet1 b n w=180e-9 m=1 nf=1
        mi2 inet1 g s b n w=180e-9 m=1 nf=1
        .ends n_s_pcell_7

        .subckt n_s_pcell_8 d g s b
        .param m=1
        mi1 d g inet1 b n w=180e-9 m=1 nf=1
        mi2 inet1 g s b n w=180e-9 m=1 nf=1
        .ends n_s_pcell_8

        .subckt {name} id vccx vg vinn vinp voutn voutp vssx
        xmp4 vpbias vpbias vccx vccx p_s_pcell_3 m=6
        xmp3 voutn vx vccx vccx p_s_pcell_4 m=16
        xmp0 vy vpbias vccx vccx p_s_pcell_5 m=3
        xmp1 voutp vy vccx vccx p_s_pcell_4 m=16
        xmp2 vx vpbias vccx vccx p_s_pcell_5 m=3
        xmn6 vpbias id vssx vssx n_s_pcell_6 m=1
        xmn5 voutn id vssx vssx n_s_pcell_7 m=4
        xmn1 vx vinp net023 vssx n_s_pcell_8 m=10
        xmn2 net023 vg vssx vssx n_s_pcell_6 m=1
        xmn3 voutp id vssx vssx n_s_pcell_7 m=4
        xmn4 id id vssx vssx n_s_pcell_6 m=1
        xmn0 vy vinn net023 vssx n_s_pcell_8 m=10
        .ends {name}
        .END
    """)
    return netlist


def charge_pump_switch(name, size=16):
    netlist = textwrap.dedent(f"""\
    .subckt switch ng pg t1 t2 vccx vssx
    qp0 t1 pg t2 vccx p m=1 nf=2 w=90e-9
    qn0 t1 ng t2 vssx n m=1 nf=2 w=90e-9
    .ends
    .subckt {name} en enb in out vccx vssx
    """)
    for i in range(size):
        netlist += f"isw<{i}> en enb in out vccx vssx switch\n"
    netlist += textwrap.dedent(f"""\
    .ends {name}
    .END
    """)
    return netlist


def niwc_opamp_split(name):
    netlist = textwrap.dedent(f"""\
    .subckt {name} vtail vbn vbp1 vbp2 vin vip out vccx vssx
    m1 cas1 vin tail vssx n w=360e-9 m=8 nf=1 stack=4
    m2 cas2 vip tail vssx n w=360e-9 m=8 nf=1 stack=4
    mtail tail vtail vssx vssx n w=360e-9 m=32 nf=1 stack=8
    m7a y x vssx vssx n w=360e-9 m=8 nf=1 stack=8
    m7b y x vssx vssx n w=360e-9 m=8 nf=1 stack=8
    m8a z x vssx vssx n w=360e-9 m=8 nf=1 stack=8
    m8b z x vssx vssx n w=360e-9 m=8 nf=1 stack=8
    m5a x   vbn y vssx n w=360e-9 m=4 nf=1 stack=4
    m5b x   vbn y vssx n w=360e-9 m=4 nf=1 stack=4
    m6a out vbn z vssx n w=360e-9 m=4 nf=1 stack=4
    m6b out vbn z vssx n w=360e-9 m=4 nf=1 stack=4
    m3a x vbp1 cas1 vccx p w=360e-9 m=4 nf=1 stack=4
    m3b x vbp1 cas1 vccx p w=360e-9 m=4 nf=1 stack=4
    m4a x vbp1 cas2 vccx p w=360e-9 m=4 nf=1 stack=4
    m4b x vbp1 cas2 vccx p w=360e-9 m=4 nf=1 stack=4
    m11 cas1 vbp2 vccx vccx p w=360e-9 m=32 nf=1 stack=8
    m12 cas2 vbp2 vccx vccx p w=360e-9 m=32 nf=1 stack=8
    .ends {name}
    .END
    """)
    return netlist


def opamp_poor(name):
    netlist = textwrap.dedent(f"""\
    .subckt ps4 d g s b
    .param m=1
    i0 d0 g s  b p m=1 w=180e-9 m=1 nf=1
    i1 d1 g d0 b p m=1 w=180e-9 m=1 nf=1
    i2 d2 g d1 b p m=1 w=180e-9 m=1 nf=1
    i3 d  g d2 b p m=1 w=180e-9 m=1 nf=1
    .ends
    .subckt ns4 d g s b
    .param m=1
    i0 d0 g s  b n m=1 w=180e-9 m=1 nf=1
    i1 d1 g d0 b n m=1 w=180e-9 m=1 nf=1
    i2 d2 g d1 b n m=1 w=180e-9 m=1 nf=1
    i3 d  g d2 b n m=1 w=180e-9 m=1 nf=1
    .ends
    .subckt cascode_p d g s b
    i0 d0 g s  b ps4  m=2
    i1 d  g d0 b plvt w=720e-9 m=1 nf=8
    .ends
    .subckt cascode_n d g s b
    i1 d  g d0 b nlvt w=720e-9 m=1 nf=8
    i0 d0 g s  b ns4  m=2
    .ends
    .subckt {name} vplus vminus vout fbin fbout ibias vccx vssx
    iloadl<0> voutb voutb vccx vccx cascode_p
    iloadl<1> voutb voutb vccx vccx cascode_p
    iloadr<0> vout  vout  vccx vccx cascode_p
    iloadr<1> vout  vout  vccx vccx cascode_p

    idiffl<0> voutb vplus  vtail vssx cascode_n
    idiffl<1> voutb vplus  vtail vssx cascode_n
    idiffr<0> vout  vminus vtail vssx cascode_n
    idiffr<1> vout  vminus vtail vssx cascode_n

    ibias<0> ibias ibias  vssx vssx cascode_n
    ibias<1> ibias ibias  vssx vssx cascode_n
    ibias<2> ibias ibias  vssx vssx cascode_n
    ibias<3> ibias ibias  vssx vssx cascode_n
    ibias<4> ibias ibias  vssx vssx cascode_n
    itail    vtail ibias  vssx vssx cascode_n

    i0 fbout fbin  vccx vssx n w=720e-9 m=1 nf=8
    i1 fbout ibias vssx vssx cascode_n
    .ends {name}
    .END
    """)
    return netlist


def comparator_analog(name):
    netlist = textwrap.dedent(f"""\
    .subckt {name} vminus vplus vout en vccx vssx
    invp1 enn en  vccx vccx p m=1 nf=2 w=180e-9
    invn1 enn en  vssx vssx n m=1 nf=2 w=180e-9
    invp2 enp enn vccx vccx p m=1 nf=2 w=180e-9
    invn2 enp enn vssx vssx n m=1 nf=2 w=180e-9
    mpbias pbias pbias vccx vccx p stack=4  m=4 nf=1 w=360e-9
    nres1  pbias enp   vmid vssx n stack=12 m=1 nf=1 w=360e-9
    nres0  vmid  hi    vssx vssx n stack=40 m=1 nf=1 w=360e-9
    mp_hi  hi    vssx  vccx vccx p m=1 nf=4 w=360e-9
    decap0 vssx vminus vssx vssx n m=24 nf=4 w=360e-9
    decap1 vccx pbias  vccx vccx p m=18 nf=4 w=360e-9
    ptail vcm pbias vccx vccx p stack=4 m=48 nf=1 w=360e-9
    pinp vo1p vminus vcm vccx p stack=2 m=48 nf=1 w=180e-9
    pinn vo1n vplus  vcm vccx p stack=2 m=48 nf=1 w=180e-9
    nldl vo1p vo1p  vssx vssx n stack=4 m=24 nf=1 w=360e-9
    nldr vo1n vo1p  vssx vssx n stack=4 m=24 nf=1 w=360e-9
    p2 vout pbias vccx vccx p stack=4 m=8 nf=1 w=360e-9
    n2 vout vo1n  vssx vssx n stack=2 m=4 nf=1 w=180e-9
    sw_pullup_enb vout  enp vccx vccx p stack=4 m=2 nf=1 w=360e-9
    sw_pbias_en   pbias enp vccx vccx p stack=4 m=2 nf=1 w=360e-9
    sw_pulldn_en  vo1n  enn vssx vssx n stack=4 m=2 nf=1 w=360e-9
    sw_pulldn_en1 vo1p  enn vssx vssx n stack=4 m=2 nf=1 w=360e-9
    .ends {name}
    .END
    """)
    return netlist
