import logging
logger = logging.getLogger(__name__)

class instance_wrapper:
    def __init__(self, inst):
        #self.inst = inst
        self.orient = inst.orient
        self.width = inst.width
        self.height = inst.height
        self.originBox = inst.originBox
        self.placedBox = inst.placedBox
        self.name = inst.name
        self.master = inst.master
        self.gdsFile = inst.gdsFile

    def __getattr__(self, nm):
        assert False, nm
        #logger.info( f'instance_wrapper: accessing {nm}')
        #return getattr(self.inst, nm)

class block_wrapper:
    def __init__(self, blk):
        #self.blk = blk

        self.selectedInstance = blk.selectedInstance
        self.instance = { blk.selectedInstance : instance_wrapper(blk.instance[blk.selectedInstance])}
        self.child = blk.child

    def __getattr__(self, nm):
        assert False
        #logger.info( f'block_wrapper: accessing {nm}')
        #return getattr(self.blk, nm)

class hN_wrapper:
    def __init__( self, hN):
        #self.hN = PnR.hierNode(hN)

        self.numPlacement = hN.numPlacement
        self.name = hN.name
        self.width = hN.width
        self.height = hN.height
        self.HPWL = hN.HPWL
        self.cost = hN.cost
        self.constraint_penalty = hN.constraint_penalty
        self.area_norm = hN.area_norm
        self.HPWL_norm = hN.HPWL_norm

        self.Blocks = [ block_wrapper(blk) for blk in hN.Blocks]

    def __getattr__(self, nm):
        assert False, nm
        #logger.info( f'hN_wrapper: accessing {nm}')
        #return getattr(self.hN, nm)

class hN_wrapper2:
    def __init__( self, hN):
        #self.hN = PnR.hierNode(hN)

        self.numPlacement = hN.numPlacement
        self.name = hN.name

    def __getattr__(self, nm):
        assert False
        #logger.info( f'hN_wrapper: accessing {nm}')
        #return getattr(self.hN, nm)


class DB_wrapper:
    def __init__( self, DB):
        self.DB = DB
        self.checkout_cache = {}
        self.hierTree = [ hN_wrapper2(hN) for hN in DB.hierTree]

    def CheckoutHierNode( self, idx, sel):
        return self.DB.CheckoutHierNode( idx, sel)
        # Seems to be using up too much memory
        k = (idx,sel)
        if k not in self.checkout_cache:
            hN = self.DB.CheckoutHierNode( idx, sel)
            self.checkout_cache[k] = hN_wrapper(hN)
            del hN
        return self.checkout_cache[k]
