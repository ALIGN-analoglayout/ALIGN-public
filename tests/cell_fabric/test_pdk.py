from align.cell_fabric import pdk

def test_A():
    p = pdk.Pdk()
    p.pdk['M2'] = { 'Direction': 'H', 'Width': 60}
    p.pdk['M3'] = { 'Direction': 'V', 'Width': 50}

    p.pdk['V2'] = { 'Stack': ['M2', 'M3'],
                'WidthX': 50,
                'WidthY': 60,
                'VencA_L': 12,
                'VencA_H': 16,
                'VencP_L': 0,
                'VencP_H': 0
    }
    kk, bar = p.get_via_table()['V2']
    assert kk == 'V2'
    assert 'V2' in bar
    assert 'M2' in bar
    assert 'M3' in bar

    assert all( [x%40 == 0 for x in bar['M2']])
    assert all( [x%40 == 0 for x in bar['M3']])
    assert all( [x%40 == 0 for x in bar['V2']])

    rM2 = [ x//40 for x in bar['M2']]
    rM3 = [ x//40 for x in bar['M3']]
    rV2 = [ x//40 for x in bar['V2']]

    assert rM3[2]-rM3[0] == p.pdk['M3']['Width']
    assert rM2[3]-rM2[1] == p.pdk['M2']['Width']

    assert rM3[3]-rM3[1] == p.pdk['V2']['WidthY'] + 2*p.pdk['V2']['VencA_H']
    assert rM2[2]-rM2[0] == p.pdk['V2']['WidthX'] + 2*p.pdk['V2']['VencA_L']

    print(rM2,rM3,rV2)

def test_B():
    p = pdk.Pdk()
    p.pdk['M2'] = { 'Direction': 'H', 'Width': 40}
    p.pdk['M3'] = { 'Direction': 'V', 'Width': 60}

    p.pdk['V2'] = { 'Stack': ['M2', 'M3'],
                'WidthX': 60,
                'WidthY': 80,
                'VencA_L': 0,
                'VencA_H': 30,
                'VencP_L': -20,
                'VencP_H': 0
    }
    kk, bar = p.get_via_table()['V2']
    assert kk == 'V2'
    assert 'V2' in bar
    assert 'M2' in bar
    assert 'M3' in bar

    assert all( [x%40 == 0 for x in bar['M2']])
    assert all( [x%40 == 0 for x in bar['M3']])
    assert all( [x%40 == 0 for x in bar['V2']])

    rM2 = [ x//40 for x in bar['M2']]
    rM3 = [ x//40 for x in bar['M3']]
    rV2 = [ x//40 for x in bar['V2']]

    assert rM3[2]-rM3[0] == p.pdk['M3']['Width']
    assert rM2[3]-rM2[1] == p.pdk['M2']['Width']

    assert rM3[3]-rM3[1] == p.pdk['V2']['WidthY'] + 2*p.pdk['V2']['VencA_H']
    assert rM2[2]-rM2[0] == p.pdk['V2']['WidthX'] + 2*p.pdk['V2']['VencA_L']

    print(rM2,rM3,rV2)
