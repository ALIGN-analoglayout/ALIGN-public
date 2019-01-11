from cpython cimport array
import array

cdef class PyGdsWriter:
    cdef GdsWriter *thisptr

    def __cinit__(self, filename):
        self.thisptr = new GdsWriter( filename.encode())

    def __dealloc__(self):
        del self.thisptr

    def create_lib( self, libname, double dbu_uu, double dbu_m):
        self.thisptr.create_lib( libname.encode(), dbu_uu, dbu_m)

    def gds_write_bgnstr( self):
        self.thisptr.gds_write_bgnstr()

    def gds_write_strname( self, s):
        self.thisptr.gds_write_strname( s.encode())

    def gds_write_layer( self, int ly):
        self.thisptr.gds_write_layer( ly)

    def gds_write_xy( self, list xy):
        x,y = tuple(zip(*xy))
        cdef array.array ax = array.array('i', x)
        cdef array.array ay = array.array('i', y)
        self.thisptr.gds_write_xy( ax.data.as_ints, ay.data.as_ints, len(x))

    def gds_write_boundary( self):
        self.thisptr.gds_write_boundary()

    def gds_write_endel( self):
        self.thisptr.gds_write_endel()

    def gds_write_datatype( self, dt):
        self.thisptr.gds_write_datatype( dt)

    def gds_write_sref( self):
        self.thisptr.gds_write_sref()

    def gds_write_sname( self, s):
        self.thisptr.gds_write_sname( s.encode())

    def gds_write_endstr( self):
        self.thisptr.gds_write_endstr()

    def gds_write_endlib( self):
        self.thisptr.gds_write_endlib()
