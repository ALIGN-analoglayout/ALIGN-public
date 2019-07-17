from primitive import CanvasNMOS

class UnitCell(CanvasNMOS):

    def unit( self, x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing):
        (SA, GA, DA, SB, GB, DB) = SDG
        (S, D, G) = (SA+SB, DA+DB, GA+GB)
        #####   This part generats locations of S/D/G   #####
        gu = self.gatesPerUnitCell
        h = self.m2PerUnitCell

        self.addWire( self.active, 'active', None, y, (x,1), (x+1,-1))
        self.addWire( self.RVT,    'RVT',    None, y, (x, 1), (x+1, -1))

        for i in range(1,  self.finsPerUnitCell):
            self.addWire( self.fin, 'fin', None,  self.finsPerUnitCell*y+i, x, x+1)

        #####   Gate Placement   #####
        for i in range(gu):
            self.addWire( self.pl, 'g', None, gu*x+i,   (y,0), (y,1))

        #####   Nselect Placement   #####
        if x == x_cells -1 and y == y_cells -1:
            self.addRegion( self.nselect, 'ns', None, (0, -1), 0, ((1+x)*gu, -1), (y+1)* self.finsPerUnitCell)

        if x_cells-1==x:
            grid_y0 = y*h + finDummy//2-1
            grid_y1 = grid_y0+(fin+2)//2
            for i in G:
                self.addWire( self.m1, None, None, i, (grid_y0, -1), (grid_y1, 1))
            for i in S+D:
                self.addWire( self.m1, None, None, i, (grid_y0, -1), (grid_y1, 1))
                for j in range((((fin-fin_u)//2 +finDummy+3)//2),self.v0.h_clg.n):
                    self.addVia( self.v0, 'v0', None, i, (y, j))

            #pin = 'VDD' if y%2==0 else 'GND'
            #self.addWire( self.m2, pin, pin, h*(y+1), (0, 1), (x_cells*gu, -1))
            #self.addWire( self.m2, 'GND', 'GND', 0, (0, 1), (x_cells*gu, -1))
            for (pin, contact, track, m3route) in Routing:
                self.addWire( self.m2, pin, pin, y*h+track, (min(contact), -1), (max(contact), 1))
                if y_cells > 1:
                   self.addWire( self.m3, None, None, m3route, (track, -1), (y*h+track, 1))
                   self.addVia( self.v2, None, None, m3route, track)
                   self.addVia( self.v2, None, None, m3route, y*h+track)

                for i in contact:
                    self.addVia( self.v1, None, None, i, y*h+track)


