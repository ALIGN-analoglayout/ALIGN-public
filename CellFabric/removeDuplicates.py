
import json

class Scanline:
    def __init__( self, proto, indices, kk):
        self.proto = proto
        self.indices = indices
        self.kk = kk
        self.rects = []
        self.clear()

    def clear( self):
        self.start = None
        self.end = None
        self.currentNet = None

    def isEmpty( self):
        return self.start is None

    def emit( self):
        r = self.proto[:]
        r[kk] = self.start
        r[kk+2] = self.end
        self.rects.append( (r,self.currentNet))

    def set( self, rect, netName):
        self.start = rect[self.kk]
        self.end = rect[self.kk+2]
        self.currentNet = netName

    def updateEnd( self, rect):
        self.end = rect[self.kk+2]
        

def removeDuplicates( data):

    hLayers = { 'ndiff', 'polycon', 'metal0', 'metal2'}
    vLayers = { 'diffcon', 'poly', 'metal1'}

    tbl = {}

    for d in data['terminals']:
        layer = d['layer']
        rect = d['rect']
        netName = d['netName']

        if   layer in hLayers:
            c2 = rect[1]+rect[3]
        elif layer in vLayers:
            c2 = rect[0]+rect[2]
        else:
            assert layer in hLayers or layer in vLayers, layer

        if (layer,c2) not in tbl: tbl[(layer,c2)] = []
        tbl[(layer,c2)].append( (rect,netName))
        
    for (k,v) in tbl.items():
        (layer,c2) = k
        (indices,kk) = ([1,3],0) if layer in hLayers else ([0,2],1)

        sl = Scanline( v[0][0], indices, kk)

        rects = []

        if v:
            (rect0,netName0) = v[0]
            for (rect,netName) in v[1:]:
                assert all( rect[i] == rect0[i] for i in indices)

            s = sorted(v,key=lambda p: p[0][kk])

            start = None
            end = None
            currentNet = None

            for (rect,netName) in s:
                if start is None:
                    start = rect[kk]
                    end = rect[kk+2]
                    currentNet = netName
                elif rect[kk] <= end: # continue
                    end = rect[kk+2]
#                    assert currentNet == netName, (layer, currentNet, netName)
                else: # gap
                    r = s[0][0][:]
                    r[kk] = start
                    r[kk+2] = end
                    rects.append( (r,currentNet))
                    start = rect[kk]
                    end = rect[kk+2]
                    currentNet = netName

            if start is not None:
                r = s[0][0][:]
                r[kk] = start
                r[kk+2] = end
                rects.append( (r,currentNet))
                start = None
                end = None
                currentNet = None

        print( k, len(v), len(rects), rects)


if __name__ == "__main__":
    with open( "mydesign_dr_globalrouting.json", "r") as fp:
        data = json.load( fp)
        removeDuplicates( data)
