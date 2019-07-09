        
class pattern():

 #   def __init__(self):       
    def common_centroid(x_cells, gu, gate, gateDummy):
        SA, SB, DA, DB, GA, GB = ([] for i in range(6))
        for k in range(x_cells//2):
            (p,q) = (gateDummy,gu+gateDummy) if k%2 == 0 else (gu+gateDummy,gateDummy)
            (lSa,lSb) = (2*k*gu+p,2*k*gu+q)
            (lDa,lDb) = (lSa+gate,lSb+gate)
            (lGa,lGb) = (lSa+1,lSb+1)
            if k >= x_cells//4:
                (lDa,lDb) = (2*k*gu+p,2*k*gu+q)
                (lSa,lSb) = (lDa+gate,lDb+gate)
                (lGa,lGb) = (lDa+1,lDb+1)
            else:
                pass
            SA.append(lSa)
            GA.append(lGa)
            DA.append(lDa)
            SB.append(lSb)
            GB.append(lGb)
            DB.append(lDb)
        SDG = (SA, GA, DA, SB, GB, DB)
        return SDG

    def interdigitated(x_cells, gu, gate, gateDummy):
        SA, SB, DA, DB, GA, GB = ([] for i in range(6))
        for k in range(x_cells//2):
            (p,q) = (gateDummy,gu+gateDummy)
            (lSa,lSb) = (2*k*gu+p,2*k*gu+q)
            (lDa,lDb) = (lSa+gate,lSb+gate)
            (lGa,lGb) = (lSa+1,lSb+1)
            SA.append(lSa)
            GA.append(lGa)
            DA.append(lDa)
            SB.append(lSb)
            GB.append(lGb)
            DB.append(lDb)
        SDG = (SA, GA, DA, SB, GB, DB)
        return SDG                                                       

