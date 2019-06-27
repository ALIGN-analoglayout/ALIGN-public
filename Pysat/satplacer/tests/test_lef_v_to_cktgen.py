
from satplacer.lef_v_to_cktgen import *

import json

def test_one():
    lef_str = """
MACRO CMB_2_n10_A1_B1
  ORIGIN 0 0 ;
  FOREIGN CMB_2_n10_A1_B1 0 0 ;
  SIZE 3.8400 BY 3.4440 ;
  PIN S
    DIRECTION INOUT ;
    USE SIGNAL ;
    PORT
      LAYER M2 ;
        RECT 0.2040 0.2360 3.6360 0.2680 ;
      LAYER M2 ;
        RECT 0.2040 1.0760 3.6360 1.1080 ;
      LAYER M2 ;
        RECT 0.2040 1.9160 3.6360 1.9480 ;
      LAYER M2 ;
        RECT 0.2040 2.7560 3.6360 2.7880 ;
    END
  END S
  PIN D0
    DIRECTION INOUT ;
    USE SIGNAL ;
    PORT
      LAYER M2 ;
        RECT 0.2040 0.3200 3.6360 0.3520 ;
      LAYER M2 ;
        RECT 0.2040 1.1600 3.6360 1.1920 ;
      LAYER M2 ;
        RECT 0.2040 2.0000 3.6360 2.0320 ;
      LAYER M2 ;
        RECT 0.2040 2.8400 3.6360 2.8720 ;
    END
  END D0
  PIN D1
    DIRECTION INOUT ;
    USE SIGNAL ;
    PORT
      LAYER M2 ;
        RECT 0.2040 0.4040 3.6360 0.4360 ;
      LAYER M2 ;
        RECT 0.2040 1.2440 3.6360 1.2760 ;
      LAYER M2 ;
        RECT 0.2040 2.0840 3.6360 2.1160 ;
      LAYER M2 ;
        RECT 0.2040 2.9240 3.6360 2.9560 ;
    END
  END D1
  PIN D2
    DIRECTION INOUT ;
    USE SIGNAL ;
    PORT
      LAYER M2 ;
        RECT 0.2040 0.4880 3.6360 0.5200 ;
      LAYER M2 ;
        RECT 0.2040 1.3280 3.6360 1.3600 ;
      LAYER M2 ;
        RECT 0.2040 2.1680 3.6360 2.2000 ;
      LAYER M2 ;
        RECT 0.2040 3.0080 3.6360 3.0400 ;
    END
  END D2
  OBS
    LAYER M3 ;
      RECT 0.2240 0.2160 0.2560 2.8080 ;
    LAYER M3 ;
      RECT 0.3040 0.1320 0.3360 2.7240 ;
    LAYER M3 ;
      RECT 0.3840 0.3000 0.4160 2.8920 ;
    LAYER M2 ;
      RECT 0.2040 0.1520 3.6360 0.1840 ;
    LAYER M2 ;
      RECT 0.2040 0.9920 3.6360 1.0240 ;
    LAYER M2 ;
      RECT 0.2040 1.8320 3.6360 1.8640 ;
    LAYER M2 ;
      RECT 0.2040 2.6720 3.6360 2.7040 ;
    LAYER M3 ;
      RECT 0.9440 0.3840 0.9760 2.9760 ;
    LAYER M3 ;
      RECT 1.0240 0.4680 1.0560 3.0600 ;
    LAYER M1 ;
      RECT 0.2240 0.1320 0.2560 0.7080 ;
    LAYER M1 ;
      RECT 2.1440 0.1320 2.1760 0.7080 ;
    LAYER M1 ;
      RECT 2.7840 0.1320 2.8160 0.7080 ;
    LAYER M1 ;
      RECT 0.8640 0.1320 0.8960 0.7080 ;
    LAYER M1 ;
      RECT 1.5040 0.1320 1.5360 0.7080 ;
    LAYER M1 ;
      RECT 3.4240 0.1320 3.4560 0.7080 ;
    LAYER M1 ;
      RECT 0.3840 0.1320 0.4160 0.7080 ;
    LAYER M1 ;
      RECT 2.3040 0.1320 2.3360 0.7080 ;
    LAYER M1 ;
      RECT 2.9440 0.1320 2.9760 0.7080 ;
    LAYER M1 ;
      RECT 1.0240 0.1320 1.0560 0.7080 ;
    LAYER M1 ;
      RECT 1.6640 0.1320 1.6960 0.7080 ;
    LAYER M1 ;
      RECT 3.5840 0.1320 3.6160 0.7080 ;
    LAYER M1 ;
      RECT 0.3040 0.1320 0.3360 0.7080 ;
    LAYER M1 ;
      RECT 2.2240 0.1320 2.2560 0.7080 ;
    LAYER M1 ;
      RECT 2.8640 0.1320 2.8960 0.7080 ;
    LAYER M1 ;
      RECT 0.9440 0.1320 0.9760 0.7080 ;
    LAYER M1 ;
      RECT 1.5840 0.1320 1.6160 0.7080 ;
    LAYER M1 ;
      RECT 3.5040 0.1320 3.5360 0.7080 ;
    LAYER M1 ;
      RECT 0.2240 0.9720 0.2560 1.5480 ;
    LAYER M1 ;
      RECT 2.1440 0.9720 2.1760 1.5480 ;
    LAYER M1 ;
      RECT 2.7840 0.9720 2.8160 1.5480 ;
    LAYER M1 ;
      RECT 0.8640 0.9720 0.8960 1.5480 ;
    LAYER M1 ;
      RECT 1.5040 0.9720 1.5360 1.5480 ;
    LAYER M1 ;
      RECT 3.4240 0.9720 3.4560 1.5480 ;
    LAYER M1 ;
      RECT 0.3840 0.9720 0.4160 1.5480 ;
    LAYER M1 ;
      RECT 2.3040 0.9720 2.3360 1.5480 ;
    LAYER M1 ;
      RECT 2.9440 0.9720 2.9760 1.5480 ;
    LAYER M1 ;
      RECT 1.0240 0.9720 1.0560 1.5480 ;
    LAYER M1 ;
      RECT 1.6640 0.9720 1.6960 1.5480 ;
    LAYER M1 ;
      RECT 3.5840 0.9720 3.6160 1.5480 ;
    LAYER M1 ;
      RECT 0.3040 0.9720 0.3360 1.5480 ;
    LAYER M1 ;
      RECT 2.2240 0.9720 2.2560 1.5480 ;
    LAYER M1 ;
      RECT 2.8640 0.9720 2.8960 1.5480 ;
    LAYER M1 ;
      RECT 0.9440 0.9720 0.9760 1.5480 ;
    LAYER M1 ;
      RECT 1.5840 0.9720 1.6160 1.5480 ;
    LAYER M1 ;
      RECT 3.5040 0.9720 3.5360 1.5480 ;
    LAYER M1 ;
      RECT 0.2240 1.8120 0.2560 2.3880 ;
    LAYER M1 ;
      RECT 2.1440 1.8120 2.1760 2.3880 ;
    LAYER M1 ;
      RECT 2.7840 1.8120 2.8160 2.3880 ;
    LAYER M1 ;
      RECT 0.8640 1.8120 0.8960 2.3880 ;
    LAYER M1 ;
      RECT 1.5040 1.8120 1.5360 2.3880 ;
    LAYER M1 ;
      RECT 3.4240 1.8120 3.4560 2.3880 ;
    LAYER M1 ;
      RECT 0.3840 1.8120 0.4160 2.3880 ;
    LAYER M1 ;
      RECT 2.3040 1.8120 2.3360 2.3880 ;
    LAYER M1 ;
      RECT 2.9440 1.8120 2.9760 2.3880 ;
    LAYER M1 ;
      RECT 1.0240 1.8120 1.0560 2.3880 ;
    LAYER M1 ;
      RECT 1.6640 1.8120 1.6960 2.3880 ;
    LAYER M1 ;
      RECT 3.5840 1.8120 3.6160 2.3880 ;
    LAYER M1 ;
      RECT 0.3040 1.8120 0.3360 2.3880 ;
    LAYER M1 ;
      RECT 2.2240 1.8120 2.2560 2.3880 ;
    LAYER M1 ;
      RECT 2.8640 1.8120 2.8960 2.3880 ;
    LAYER M1 ;
      RECT 0.9440 1.8120 0.9760 2.3880 ;
    LAYER M1 ;
      RECT 1.5840 1.8120 1.6160 2.3880 ;
    LAYER M1 ;
      RECT 3.5040 1.8120 3.5360 2.3880 ;
    LAYER M1 ;
      RECT 0.2240 2.6520 0.2560 3.2280 ;
    LAYER M1 ;
      RECT 2.1440 2.6520 2.1760 3.2280 ;
    LAYER M1 ;
      RECT 2.7840 2.6520 2.8160 3.2280 ;
    LAYER M1 ;
      RECT 0.8640 2.6520 0.8960 3.2280 ;
    LAYER M1 ;
      RECT 1.5040 2.6520 1.5360 3.2280 ;
    LAYER M1 ;
      RECT 3.4240 2.6520 3.4560 3.2280 ;
    LAYER M1 ;
      RECT 0.3840 2.6520 0.4160 3.2280 ;
    LAYER M1 ;
      RECT 2.3040 2.6520 2.3360 3.2280 ;
    LAYER M1 ;
      RECT 2.9440 2.6520 2.9760 3.2280 ;
    LAYER M1 ;
      RECT 1.0240 2.6520 1.0560 3.2280 ;
    LAYER M1 ;
      RECT 1.6640 2.6520 1.6960 3.2280 ;
    LAYER M1 ;
      RECT 3.5840 2.6520 3.6160 3.2280 ;
    LAYER M1 ;
      RECT 0.3040 2.6520 0.3360 3.2280 ;
    LAYER M1 ;
      RECT 2.2240 2.6520 2.2560 3.2280 ;
    LAYER M1 ;
      RECT 2.8640 2.6520 2.8960 3.2280 ;
    LAYER M1 ;
      RECT 0.9440 2.6520 0.9760 3.2280 ;
    LAYER M1 ;
      RECT 1.5840 2.6520 1.6160 3.2280 ;
    LAYER M1 ;
      RECT 3.5040 2.6520 3.5360 3.2280 ;
  END
END CMB_2_n10_A1_B1

END LIBRARY
"""

    verilog_str = """
module vga ( vps, vgnd, vmirror, x, y);
output vps, vgnd, vmirror, x, y;

CMB_2_n10_A1_B1 u0 ( .D0(vmirror), .D1(x), .D2(y), .S(vgnd) ); 

endmodule

"""

    d = convert( lef_str, verilog_str)

    assert d['nm'] == 'vga'
    assert d['instances'][0]['instance_name'] == 'u0'
    assert len(d['instances'][0]['formal_actual_map']) == 4
    assert d['leaves'][0]['bbox'][0] == 0
    assert d['leaves'][0]['bbox'][1] == 0
    assert d['leaves'][0]['bbox'][2] == 38400
    assert d['leaves'][0]['bbox'][3] == 34440

    print( json.dumps( d, indent=2) + '\n')

def test_two():
    with open( 'tests/merged.lef', 'rt') as fp:
        lef_str = fp.read()

    with open( 'tests/vga.v', 'rt') as fp:
        verilog_str = fp.read()

    d = convert( lef_str, verilog_str)

    if False:
        assert d['nm'] == 'vga'
        assert d['instances'][0]['instance_name'] == 'u0'
        assert len(d['instances'][0]['formal_actual_map']) == 4
        assert d['leaves'][0]['bbox'][0] == 0
        assert d['leaves'][0]['bbox'][1] == 0
        assert d['leaves'][0]['bbox'][2] == 38400
        assert d['leaves'][0]['bbox'][3] == 34440

    print( json.dumps( d, indent=2) + '\n')
