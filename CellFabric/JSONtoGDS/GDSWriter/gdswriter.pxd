cdef extern from "GdsWriter.h" namespace "GdsParser":
    cdef cppclass GdsWriter:
        GdsWriter(char *) except +
        void create_lib( const char*, double, double)
        void gds_write_bgnstr()
        void gds_write_strname( const char*)
        void gds_write_layer( int)
        void gds_write_xy( const int*, const int*, int)
        void gds_write_boundary()
        void gds_write_endel()
        void gds_write_datatype( short int)
        void gds_write_sref()
        void gds_write_sname( const char*)
        void gds_write_endstr()
        void gds_write_endlib()

