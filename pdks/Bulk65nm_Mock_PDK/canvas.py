from align.cell_fabric import Via, Region, Wire, Pdk, DefaultCanvas
from align.cell_fabric import CenterLineGrid, ColoredCenterLineGrid, UncoloredCenterLineGrid
from align.cell_fabric import EnclosureGrid, SingleGrid, CenteredGrid

from pathlib import Path
pdkfile = (Path(__file__).parent / 'layers.json').resolve()

class Bulk65nm_Mock_PDK_Canvas(DefaultCanvas):

    def __init__( self, fin, finDummy, gate, gateDummy,
                  pdkfile=pdkfile):

        p = Pdk().load(pdkfile)
        super().__init__(p)
        assert   3*p['Fin']['Pitch'] < 2*p['M2']['Pitch']

######### Derived Parameters ############
        self.gatesPerUnitCell = gate + 2*gateDummy
        self.finsPerUnitCell = fin + 2*finDummy
        self.finDummy = finDummy
        self.lFin = 16 ## need to be added in the PDK JSON
        # Should be a multiple of 4 for maximum utilization
        assert self.finsPerUnitCell % 4 == 0
        assert fin > 3, "number of fins in the transistor must be more than 2"
        assert finDummy % 2 == 0
        assert gateDummy > 0
        self.m2PerUnitCell = self.finsPerUnitCell//2 + 0
        self.unitCellHeight = self.m2PerUnitCell* p['M2']['Pitch']
        unitCellLength = self.gatesPerUnitCell* p['Poly']['Pitch']
        activeWidth =  p['Fin']['Pitch']*fin
        activeOffset = activeWidth//2 + finDummy*p['Fin']['Pitch']-p['Fin']['Pitch']//2
        activePitch = self.unitCellHeight
        RVTWidth = activeWidth + 2*p['Active']['active_enclosure']

        #stoppoint = activeWidth +  p['Active']['PolyActiveHang']
        self.pl = self.addGen( Wire( 'pl', 'Poly', 'v',
                                     clg=UncoloredCenterLineGrid( pitch= p['Poly']['Pitch'], width= p['Poly']['Width'], offset= p['Poly']['Offset']),
                                     spg=SingleGrid( offset= p['M2']['Offset'], pitch=self.unitCellHeight)))

        self.fin = self.addGen( Wire( 'fin', 'Fin', 'h',
                                      clg=UncoloredCenterLineGrid( pitch= p['Fin']['Pitch'], width= p['Fin']['Width'], offset= p['Fin']['Offset']),
                                      spg=SingleGrid( offset=0, pitch=unitCellLength)))

        
        stoppoint = (gateDummy-1)* p['Poly']['Pitch'] +  p['Poly']['Offset']
        self.active = self.addGen( Wire( 'active', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=activeWidth, offset=activeOffset),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.RVT = self.addGen( Wire( 'RVT', 'Rvt', 'h',
                                      clg=UncoloredCenterLineGrid( pitch=activePitch, width=RVTWidth, offset=activeOffset),
                                      spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))
        
        stoppoint = gateDummy*p['Poly']['Pitch']+p['Poly']['Offset']-p['Pc']['PcExt']-p['Poly']['Width']//2
        self.pc = self.addGen( Wire( 'pc', 'Pc', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=p['Pc']['PcWidth'], offset=p['M2']['Pitch']),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.nselect = self.addGen( Region( 'nselect', 'Nselect',
                                            v_grid=CenteredGrid( offset= p['Poly']['Pitch']//2, pitch= p['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.pselect = self.addGen( Region( 'pselect', 'Pselect',
                                            v_grid=CenteredGrid( offset= p['Poly']['Pitch']//2, pitch= p['Poly']['Pitch']),
                                            h_grid=self.fin.clg))
        self.nwell = self.addGen( Region( 'nwell', 'Nwell',
                                            v_grid=CenteredGrid( offset= p['Poly']['Pitch']//2, pitch= p['Poly']['Pitch']),
                                            h_grid=self.fin.clg))

        stoppoint = unitCellLength//2-p['Active']['activebWidth_H']//2
        offset_active_body = (self.lFin//2)*p['Fin']['Pitch']+self.unitCellHeight-p['Fin']['Pitch']//2
        self.activeb = self.addGen( Wire( 'activeb', 'Active', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=p['Active']['activebWidth'], offset= offset_active_body),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        stoppoint = unitCellLength//2-p['Pb']['pbWidth_H']//2
        self.pb = self.addGen( Wire( 'pb', 'Pb', 'h',
                                         clg=UncoloredCenterLineGrid( pitch=activePitch, width=p['Pb']['pbWidth'], offset= offset_active_body),
                                         spg=EnclosureGrid( pitch=unitCellLength, offset=0, stoppoint=stoppoint, check=True)))

        self.LISDb = self.addGen( Wire( 'LISDb', 'Lisd', 'v',
                                     clg=UncoloredCenterLineGrid( pitch=   p['M1']['Pitch'], width= p['Lisd']['LisdWidth'], offset= p['M1']['Offset']),
                                     spg=EnclosureGrid( pitch=p['M2']['Pitch'], offset=0, stoppoint= p['M2']['Width']//2+p['V1']['VencA_L'], check=True)))
 
        self.va = self.addGen( Via( 'va', 'V0',
                                    h_clg=self.m2.clg,
                                    v_clg=self.m1.clg))

        self.v0 = self.addGen( Via( 'v0', 'V0',
                                    h_clg=CenterLineGrid(),
                                    v_clg=self.m1.clg))

        self.v0.h_clg.addCenterLine( 0,                 p['V0']['WidthY'], False)
        v0pitch = activeWidth//(2*p['M2']['Pitch']) * p['Fin']['Pitch']
        for i in range(activeWidth // v0pitch + 1):
            self.v0.h_clg.addCenterLine(i*v0pitch,    p['V0']['WidthY'], True)
        self.v0.h_clg.addCenterLine( self.unitCellHeight,    p['V0']['WidthY'], False)

        # CAP Layers
        # TODO: Generalize these !!!
        self.m1n = self.addGen( Wire( 'm1n', 'M1', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['Cap']['m1Pitch'], width=p['Cap']['m1Width']),
                                     spg=EnclosureGrid( pitch=p['M2']['Pitch'], stoppoint=p['V1']['VencA_L'] +p['M2']['Width']//2, check=False)))
        self.m2n = self.addGen( Wire( 'm2n', 'M2', 'h',
                                      clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['Cap']['m2Pitch'], width=p['Cap']['m2Width']),
                                      spg=EnclosureGrid( pitch=p['M1']['Pitch'], stoppoint=p['V1']['VencA_H'] + p['M1']['Width']//2, check=False)))

        self.m3n = self.addGen( Wire( 'm3n', 'M3', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['Cap']['m3Pitch'], width=p['Cap']['m3Width']),
                                     spg=EnclosureGrid(pitch=p['M2']['Pitch'], stoppoint=p['V2']['VencA_H'] + p['M2']['Width']//2, check=False)))

        self.boundary = self.addGen( Region( 'boundary', 'Boundary', h_grid=self.m2.clg, v_grid=self.m1.clg))

        self.v1_xn = self.addGen( Via( 'v1_xn', 'V1', h_clg=self.m2n.clg, v_clg=self.m1.clg))
        self.v1_nx = self.addGen( Via( 'v1_nx', 'V1', h_clg=self.m2.clg, v_clg=self.m1n.clg))
        self.v2_xn = self.addGen( Via( 'v2_xn', 'V2', h_clg=self.m2n.clg, v_clg=self.m3.clg))
        self.v2_nx = self.addGen( Via( 'v2_nx', 'V2', h_clg=self.m2.clg, v_clg=self.m3n.clg))

        # Resistor Layers
        # TODO: Generalize these
        self.m1res = self.addGen( Wire( 'm1res', 'M1', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['Cap']['m1Pitch'], width=p['Cap']['m1Width']),
                                     spg=EnclosureGrid( pitch=p['M2']['Pitch'], stoppoint=p['V1']['VencA_L'] +p['Cap']['m2Width']//2, check=True)))

        self.m1res2 = self.addGen( Wire( 'm1res2', 'M1', 'h',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['M2']['Pitch'], width=p['Cap']['m1Width']),
                                     spg=EnclosureGrid( pitch=p['Cap']['m1Pitch'], stoppoint=p['Cap']['m1Width']//2, check=False)))

        self.m2res = self.addGen( Wire( 'm2res', 'M2', 'h',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['M2']['Pitch'], width=p['Cap']['m2Width']),
                                     spg=EnclosureGrid( pitch=p['Cap']['m1Pitch'], stoppoint=p['V1']['VencA_H'] + p['Cap']['m1Width']//2, check=False)))

        self.m2res2 = self.addGen( Wire( 'm2res2', 'M2', 'h',
                                      clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['Cap']['m2Pitch'], width=p['Cap']['m2Width']),
                                      spg=EnclosureGrid( pitch=p['Cap']['m1Pitch'], stoppoint=p['V1']['VencA_H'] + p['Cap']['m1Width']//2)))

        self.m3res = self.addGen( Wire( 'm3res', 'M3', 'v',
                                     clg=ColoredCenterLineGrid( colors=['c1','c2'], pitch=p['Cap']['m3Pitch'], width=p['Cap']['m3Width']),
                                     spg=EnclosureGrid(pitch=p['M2']['Pitch'], stoppoint=p['V2']['VencA_H'] + p['Cap']['m2Width']//2, check=True)))

        self.v1res = self.addGen( Via( 'v1res', 'V1', h_clg=self.m2res.clg, v_clg=self.m1res.clg))
        self.v2res = self.addGen( Via( 'v2res', 'V2', h_clg=self.m2res.clg, v_clg=self.m3res.clg))
