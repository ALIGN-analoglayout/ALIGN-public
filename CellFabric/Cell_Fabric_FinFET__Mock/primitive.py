from canvas import FinFET_Mock_PDK_Canvas

class NMOSGenerator(FinFET_Mock_PDK_Canvas):

    def unit( self, x_cells, y_cells, Routing):
        
        super().addNMOSArray(x_cells, y_cells, Routing)

class PMOSGenerator(FinFET_Mock_PDK_Canvas):

    def unit( self, x_cells, y_cells, Routing):

        super().addPMOSArray(x_cells, y_cells, Routing)
