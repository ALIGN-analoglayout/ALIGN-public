from canvas import FinFET_Mock_PDK_Canvas

class NMOS(FinFET_Mock_PDK_Canvas):

    def unit( self, x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing):
        
        super().genNMOS(x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing)

class PMOS(FinFET_Mock_PDK_Canvas):

    def unit( self, x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing):

        super().genPMOS(x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing)
