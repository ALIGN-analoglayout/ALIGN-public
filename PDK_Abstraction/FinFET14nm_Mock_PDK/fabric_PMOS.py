from primitive import AbstractMOS
        
class UnitCell(AbstractMOS):

    def unit( self, x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing):

        super().unit(x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing)

        #####   Pselect and Nwell Placement   #####
        if x == x_cells -1 and y == y_cells -1:      
            self.addRegion( self.pselect, 'ps', None, (0, -1), 0, ((1+x)*self.gatesPerUnitCell, -1), (y+1)*self.finsPerUnitCell)
            self.addRegion( self.nwell, 'nw', None, (0, -1), 0, ((1+x)*self.gatesPerUnitCell, -1), (y+1)*self.finsPerUnitCell)    
                
