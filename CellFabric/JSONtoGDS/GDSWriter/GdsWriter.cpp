/**
 * @file   GdsWriter.cpp
 * @author M. Rooks, Yibo Lin
 * @brief  GDSLIB 2.2 writer

   A library of C functions for reading and writing GDSII Stream format,
   following the specification of Release 6 from 1987. This library was 
   written by M. Rooks, Yale University, and released under the GNU 
   public license.

   GDSII was originally developed by the Calma Company, and later sold
   to General Electric. GE sold the format to Cadence Design Systems,
   which released GDSII format into the public domain in 1997 by allowing 
   most of the specification to be reprinted in the SPIE Handbook of 
   Microlithography, Micromachining and Microfabrication, vol 1, 
   P. Rai-Choudhury ed.

   GDSII format is not compact. Lossless compression programs such as
   'zip' and 'compress' can reduce file size by factors of three or more.

   Why use GDSII instead of a simple format like CIF?  Indeed, CIF is
   quite adequate for most algorithmically generated patterns. GDSII
   is useful when you need also to generate cell names, arrays,
   doses (datatypes), text, and rotated cells. It also lets you skip 
   the conversion step when combining patterns. Therefore GDS is just 
   a tiny bit better.

   Diagonal arrays are not supported, because they are stupid.
   Arrays at angles other than 0, 90, 180, and 270 are not supported
   because it's too complicated and subject to misinterpretation.
   Besides, who really wants a rotated array? That's silly.

   2.1  Filters out degenerate vertices.
   2.2  gds_read_double() by Hans Romijn replaces gds_read_float() 

   Supported tokens:

   HEADER              version number (6)
   BGNLIB              creation date
   LIBNAME             library name
   UNITS               database units
   ENDLIB              end of library
   BGNSTR              begin structure (cell) 
   STRNAME             structure (cell) name
   ENDSTR              end structure (cell)
   BOUNDARY            polygon
   PATH                path = line with width
   SREF                structure reference = cell instance
   AREF                array reference = matrix of cells
   TEXT                text, not to be printed
   LAYER               layer number
   DATATYPE            datatype number (often used for dose assignment)
   WIDTH               path width
   XY                  coordinates for cell placement or polygon verticies
   ENDEL               end of element
   SNAME               structure (cell) name
   COLROW              number of columns and rows (for aref)
   TEXTTYPE            just like datatype, for text
   PRESENTATION        text justification
   STRING              character string
   STRANS              contains mirroring and other stuff
   MAG                 magnification
   ANGLE               angle
   PATHTYPE            describes ends of paths
   GENERATIONS         how many generations to retain (useless)
   BOX                 boxes were originally intended as documentation only
   BOXTYPE             boxes are often used like polygons, in practice
   which makes them redundant. They also require
   five vertices, which makes them stupid.


   Unsupported, discontinued, and unused tokens:

REFLIBS     SPACING     STRCLASS     PLEX       ELFLAGS
FONTS       TEXTNODE    RESERVED     BGNEXTN    PROPVALUE
NODE        UINTEGER    FORMAT       ENDEXTN    ELKEY
NODETYPE    USTRING     MASK         LINKKEYS   LINKTYPE
PROPATTR    STYPTABLE   ENDMASKS     TAPENUM    SRFNAME
ATTRTABLE   STRTYPE     LIBDIRSIZE   TAPECODE   LIBSECUR


Token order:

Library:       Structure:   Elements:

HEADER         BGNSTR       BOUNDARY     PATH         SREF      AREF      TEXT           BOX
BGNLIB         STRNAME      LAYER        LAYER        SNAME     SNAME     LAYER          LAYER
LIBNAME        <element>    DATATYPE     DATATYPE     STRANS*   STRANS*   TEXTTYPE       BOXTYPE
UNITS          ENDSTR       XY           PATHTYPE*    MAG*      MAG*      PRESENTATION*  XY
<structures>                ENDEL        WIDTH*       ANGLE*    ANGLE*    PATHTYPE*      ENDEL
ENDLIB                                   XY           XY        COLROW    WIDTH*
ENDEL        ENDEL     XY        STRANS*
ENDEL     MAG*
ANGLE*
XY
STRING
ENDEL

* optional



*/

#include "GdsWriter.h"
#include "String.h"
/// support to .gds.gz if BOOST is available 
//#if ZLIB == 1 
//Jinhyun
//#include <boost/iostreams/filter/gzip.hpp>
//#include <boost/iostreams/device/file.hpp>
//#include <boost/iostreams/filtering_stream.hpp>
//#endif

#define SKIPOVER( fd, count )  { for ( i=0; i < ((count)-4); i+=2 ) read( (fd), &gdsword, 2 ); }
#define BAILOUT( message )     { printf( "\n\nERROR: %s\n\n", (message) ); fflush(stdout); exit(-1); }
#define WARNING( message )     { printf( "\n                            WARNING: %s\n\n", (message) ); fflush(stdout); }


#define MAX_FORWARD_REFS 1000

namespace GdsParser 
{

class GdsStream
{
    public:
        GdsStream(const char* filename)
        {
            m_std = -1; 
#if ZLIB == 1
            if (limbo::get_file_suffix(filename) == "gz") // detect gz file 
            {
                m_bos.push(boost::iostreams::gzip_compressor());
                m_bos.push(boost::iostreams::file_sink(filename));
                m_stream = &m_bos; 
                m_std = 0; 
            }
#endif
            if (m_std == -1)
            {
                m_fos.open(filename);
                if (!m_fos.good()) 
                    BAILOUT( "UNABLE TO OPEN OUTPUT FILE" );
                m_stream = &m_fos; 
                m_std = 1; 
            }
        }
        ~GdsStream()
        {
            if (m_std)
                m_fos.close();
        }
        std::ostream& getStream() {return *m_stream;}
    protected:
#if ZLIB == 1
        boost::iostreams::filtering_ostream m_bos; 
#endif
        std::ofstream m_fos; 
        std::ostream* m_stream; 
        char m_std; ///< 0 for m_bos, 1 for m_fos, -1 for invalid 
};

/*------------------------------------------------------------------------------------------*/
//    GLOBAL VARAIBLES
/*------------------------------------------------------------------------------------------*/

//BYTE  gdsswap;
//short gdsword;

/*------------------------------------------------------------------------------------------*/
//    CONSTRUCTOR AND DESTRUCTOR
/*------------------------------------------------------------------------------------------*/
GdsWriter::GdsWriter(const char* filename)
{
	//this->out = open( filename, O_CREAT | O_TRUNC | O_WRONLY, S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH );
	//if( this->out <= 0 ) BAILOUT( "UNABLE TO OPEN OUTPUT FILE" );
    m_os = new GdsStream (filename); 

    m_capacity = 16*1024; // 16 KB
    m_size = 0; 
    m_buffer = new char [m_capacity]; 
}
GdsWriter::~GdsWriter()
{
    gds_flush();  // remember to write the rest content in the buffer 
    delete [] m_buffer; 
    delete m_os; 
}

/// copy char* as unsigned long* and deal with boundary cases 
inline void fast_copy (char *t, const char *s, std::size_t n)
{
    if (n >= sizeof (unsigned long)) 
    {
        unsigned long *tl = reinterpret_cast<unsigned long *> (t);
        const unsigned long *sl = reinterpret_cast<const unsigned long *> (s);

        while (n >= sizeof (unsigned long)) 
        {
            *tl++ = *sl++;
            n -= sizeof (unsigned long);
        }

        t = reinterpret_cast<char *> (tl);
        s = reinterpret_cast<const char *> (sl);
    }

    while (n-- > 0) 
    {
        *t++ = *s++;
    }
}

/// a buffered writing scheme 
int GdsWriter::gds_write(const char* b, std::size_t n)
{
    //int ret; 
    while (m_size + n > m_capacity) 
    {
        std::size_t nw = m_capacity - m_size;
        if (nw) 
        {
            n -= nw;
            fast_copy(m_buffer + m_size, b, nw);
            b += nw;
        }

        //ret = write (this->out, m_buffer, m_capacity);
        m_os->getStream().write(m_buffer, m_capacity);
        //if (ret < 0)
        //    return ret; 
        m_size = 0;
    }

    if (n) 
    {
        fast_copy (m_buffer + m_size, b, n);
        m_size += n;
    }

    return 1; 
}

void GdsWriter::gds_flush()
{
    if (m_size) // remember to write the rest content in the buffer 
    {
        //write (this->out, m_buffer, m_size);
        m_os->getStream().write(m_buffer, m_size);
        m_size = 0; 
    }
}

/*------------------------------------------------------------------------------------------*/
//    HIGH LEVEL UTILITY FUNCTIONS
/*------------------------------------------------------------------------------------------*/
void GdsWriter::write_boundary(int layer, int datatype, std::vector<int> const& vx, std::vector<int> const& vy, bool has_last)
{
	assert(vx.size() == vy.size() && !vx.empty());

    this->gds_write_boundary(  );       // write just the token
    this->gds_write_layer( layer );       // layer 0, for example
    this->gds_write_datatype(  datatype );    // datatype 1, for example

	// considering vectors store data contiguously 
	this->gds_write_xy(  &vx[0], &vy[0], vx.size(), has_last);    // polygon, four vertices, first vertex repeated => 5 points
    this->gds_write_endel(  );          // end of element
}
void GdsWriter::write_box(int layer, int datatype, int xl, int yl, int xh, int yh)
{
    this->gds_write_boundary(  );       // write just the token
    this->gds_write_layer(  layer );       // layer 0, for example
    this->gds_write_datatype( datatype );    // datatype 1, for example

	int px[4], py[4];
	px[0] = xl; py[0] = yl;
	px[1] = xl; py[1] = yh;
	px[2] = xh; py[2] = yh;
	px[3] = xh; py[3] = yl;

	this->gds_write_xy(  px, py, 4, false);    // polygon, four vertices, first vertex repeated => 5 points
    this->gds_write_endel(  );          // end of element
}
void GdsWriter::create_lib(const char* libname, double dbu_uu, double dbu_m)
{
	// Write HEADER, BGNLIB, LIBNAME, and UNITS.
	gds_write_header(  );
	gds_write_bgnlib(  );
	gds_write_libname(  libname );
	gds_write_units(  dbu_uu, dbu_m);
}

/*------------------------------------------------------------------------------------------*/
//    UTILITY FUNCTIONS
/*------------------------------------------------------------------------------------------*/


void GdsWriter::gds_swap4bytes( BYTE *four  )
{
	static BYTE temp;
#if BYTESWAP
	temp    = four[0];
	four[0] = four[3];
	four[3] = temp;
	temp    = four[1];
	four[1] = four[2];
	four[2] = temp;
#endif
}

/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_swap2bytes( BYTE *two )
{
	static BYTE temp;
#if BYTESWAP 
	temp   = two[0];
	two[0] = two[1];
	two[1] = temp;
#endif
}

/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_make_next_item( struct gds_itemtype **ci )
{
	// mag, angle and strans must be tallied
	// only when flattening the pattern.
	static struct gds_itemtype
		*current_item;


	current_item = *ci;    
	current_item->nextitem = (struct gds_itemtype *) malloc( sizeof( struct gds_itemtype ) );

	if ( ! current_item->nextitem ) BAILOUT( "UNABLE TO ALLOCATE NEXT ITEM" );

	current_item = current_item->nextitem;

	// Each cell has a rotation, magnification and strans, but we do not need
	// to keep a running tally unless we are flattening the pattern.

	current_item->type          = -2;               // invalid
	current_item->width         = 0;
	current_item->n             = 0;
	current_item->layer         = 0; 
	current_item->dt            = 0;
	current_item->cell_number   = -1;               // invalid
	current_item->path_end      = 0;
	current_item->mag           = 1.0;              /* mag */
	current_item->angle         = 0.0;              /* angle */
	current_item->abs_angle     = 0;            /* from strans */
	current_item->abs_mag       = 0;            /* from strans */
	current_item->reflect       = 0;            /* from strans, reflect before rotation */
	current_item->rows          = 0;                /* n cols */
	current_item->cols          = 0;                /* n rows */
	current_item->col_pitch     = 0;                /* column pitch */
	current_item->row_pitch     = 0;	            /* row pitch    */
	current_item->col_pitchy    = 0;                /* diagonal components are */
	current_item->row_pitchx    = 0;	            /* hopefully zero always */
	current_item->nextitem = NULL;

	*ci = current_item;

}  // make_next_item

/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_bindump( BYTE x )            // dump one byte in binary format
{                            // way too clever hack from a forum post, sorry
	int z;
	static char b[9];

	b[0] = '\0';

	for ( z=128; z>0; z >>=1 )
		strcat( b, ((x & z) == z) ? "1" : "0" );

	printf( "%s ", b );        

}

/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_float( double x )

	/* Write 8 bytes after converting back to wacky GDS float format. */

{

	unsigned int
/*		b,*/ // it seems not used 
		sign,
		e64,
		bit[56];

	int            // important
		exponent,
		i;

	double
		fexponent,
		mantissa,
		mantita;    

	BYTE
		by,
		stupid[8];


	if ( ! BYTESWAP )
		WARNING( "WRITING OF FLOATING POINT ON LITTLE-ENDIAN MACHINES HAS NOT BEEN TESTED" );

	// printf( "\nencoding %g\n", x ); fflush( stdout );

	for ( i=0; i<8; i++ ) stupid[i] = 0;

	if ( x != 0.0 ) 
	{

		if ( x < 0.0 )
			sign = 1;
		else
			sign = 0;

		if (x < 0.0) x = -x ;

		exponent = 1 + floor( log( x ) / log( 16 ) );
		if ( exponent < -64 ) BAILOUT( "A NUMBER IS TOO SMALL TO ENCODE AS A GDS FLOAT" );
		fexponent = exponent;
		e64 = exponent + 64;
		mantissa = x / pow( 16.0, fexponent );
		mantita = mantissa;

		// original version is i<=56, I don't think it is correct 
		for( i=0; i<56; i++ )
		{
			bit[i] = floor( pow(2,i+1) * mantita );
			mantita = mantita - bit[i] / pow(2,i+1);
		}

		stupid[0] = pow(2,7) * sign + e64;

		for ( i=0;  i<8;  i++ ) stupid[1] = stupid[1] + bit[i] * pow(2, 7-i);
		for ( i=8;  i<16; i++ ) stupid[2] = stupid[2] + bit[i] * pow(2,15-i);
		for ( i=16; i<24; i++ ) stupid[3] = stupid[3] + bit[i] * pow(2,23-i);
		for ( i=24; i<32; i++ ) stupid[4] = stupid[4] + bit[i] * pow(2,31-i);
		for ( i=32; i<40; i++ ) stupid[5] = stupid[5] + bit[i] * pow(2,39-i);
		for ( i=40; i<48; i++ ) stupid[6] = stupid[6] + bit[i] * pow(2,47-i);
		for ( i=48; i<56; i++ ) stupid[7] = stupid[7] + bit[i] * pow(2,55-i);

	}

	// printf( "\n" );
	for ( i=0; i<8; i++ ) 
	{
		by = stupid[i];
		gds_write((char*)(&by), 1 );
		// gds_bindump( by );    
	}            
	// printf( "\n" ); fflush( stdout );


} // write_float

/*------------------------------------------------------------------------------------------*/
//    TOKEN I/O FUNCTIONS
/*------------------------------------------------------------------------------------------*/

/* Contains GDS version number- we don't care */


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_header(  )
{
	unsigned short int 
		count,
		si,
		token;

	ssize_t w;

	count = 6;
	gds_swap2bytes( (BYTE *) &count );
	w = gds_write((char*)(&count), 2 );

	if ( w <= 0 ) BAILOUT( "UNABLE TO WRITE TO OUTPUT FILE - CHECK OPEN() CALL" );

	token = 0x0002;                // header
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	si = 600;                      // GDSII version 6 
	gds_swap2bytes( (BYTE *) &si );
	gds_write((char*)(&si), 2 );          

}  // write_header


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_bgnlib(  )
{
	time_t *now;
	struct tm *date;

	short int 
		year,
		month,
		day,
		hour,
		minute,
		second,
		token,
		count;

	now  = (time_t *)    malloc( sizeof( time_t ) );
	//date = (struct tm *) malloc( sizeof( struct tm ) );

	time( now );
	date = localtime( now );

	count = 0x1C;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0102;                 // BGNLIB
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );         
	year = 1900 + date->tm_year;    // last modification time
	gds_swap2bytes( (BYTE *) &year );
	gds_write((char*)(&year), 2 );
	month = 1 + date->tm_mon;
	gds_swap2bytes( (BYTE *) &month );
	gds_write((char*)(&month), 2 );
	day = date->tm_mday;
	gds_swap2bytes( (BYTE *) &day );
	gds_write((char*)(&day), 2 );
	hour = date->tm_hour;
	gds_swap2bytes( (BYTE *) &hour );
	gds_write((char*)(&hour), 2 );
	minute = date->tm_min;
	gds_swap2bytes( (BYTE *) &minute );
	gds_write((char*)(&minute), 2 );
	second = date->tm_sec;
	gds_swap2bytes( (BYTE *) &second );
	gds_write((char*)(&second), 2 );

	gds_write((char*)(&year), 2 );          // last access time (same)
	gds_write((char*)(&month), 2 );
	gds_write((char*)(&day), 2 );
	gds_write((char*)(&hour), 2 );
	gds_write((char*)(&minute), 2 );
	gds_write((char*)(&second), 2 );

    free(now);
}  // write_bgnlib



/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_bgnstr(  )
{
	static time_t *now;
	static struct tm *date;

	static short int 
		year,
		month,
		day,
		hour,
		minute,
		second,
		token,
		count;

	now  = (time_t *)    malloc( sizeof( time_t ) );
	//date = (struct tm *) malloc( sizeof( struct tm ) );

	time( now );
	date = localtime( now );

	year   = 1900 + date->tm_year;   
	month  = 1 + date->tm_mon;
	day    = date->tm_mday;
	hour   = date->tm_hour;
	minute = date->tm_min;
	second = date->tm_sec;

	gds_swap2bytes( (BYTE *) &year   );
	gds_swap2bytes( (BYTE *) &month  );
	gds_swap2bytes( (BYTE *) &day    );
	gds_swap2bytes( (BYTE *) &hour   );
	gds_swap2bytes( (BYTE *) &minute );
	gds_swap2bytes( (BYTE *) &second );

	count = 28;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0502;                 // BGNSTR
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_write((char*)(&year), 2 );          // creation time
	gds_write((char*)(&month), 2 );
	gds_write((char*)(&day), 2 );
	gds_write((char*)(&hour), 2 );
	gds_write((char*)(&minute), 2 );
	gds_write((char*)(&second), 2 );
	gds_write((char*)(&year), 2 );          // access time
	gds_write((char*)(&month), 2 );
	gds_write((char*)(&day), 2 );
	gds_write((char*)(&hour), 2 );
	gds_write((char*)(&minute), 2 );
	gds_write((char*)(&second), 2 );

    free(now);
}  // write_bgnstr


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_endlib(  )
{
	static short int
		count,
		token;

	count = 4;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0400;                 // ENDLIB
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

    // I want to keep a lib complete 
    gds_flush(); 

}  // write_endlib


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_endstr(  )
{
	static short int
		count,
		token;

	count = 4;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0700;                 // ENDSTR
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

}  // write_endstr

/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_libname( const char *name )
{
	short int                       // name should be null-terminated
		count,
		token;

	// modified by Yibo Lin 
	// original version cannot handle name with odd number of characters
	int tmp_length = -1;
	char* tmp_name = gds_adjust_string(name, &tmp_length);
	assert(tmp_length != -1);
	count = 4 + tmp_length;

	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0206;                 // LIBNAME
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

	gds_write(tmp_name, tmp_length);
	free(tmp_name);

}  // write_libname


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_strname( const char *name )
{
	static short int         // name should be null-terminated
		count,
		token;

	// modified by Yibo Lin 
	// original version cannot handle name with odd number of characters
	int tmp_length = -1;
	char* tmp_name = gds_adjust_string(name, &tmp_length);
	assert(tmp_length != -1);
	count = 4 + tmp_length;

	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0606;                 // STRNAME
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

	gds_write(tmp_name, tmp_length);
	free(tmp_name);

}  // write_strname


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_string( const char *s )
{                               // s must by null-terminated
	static short int          
		count,
		token;

	int tmp_length = -1;
	char* tmp_s = gds_adjust_string(s, &tmp_length);

	if ( tmp_length > 512 ) 
	{
		WARNING( "ATTEMPT TO WRITE A STRING LONGER THAN 512 CHARACTERS. TRUNCATING." );
		tmp_length = 512;
		tmp_s[tmp_length] = '\0';
	}

	count = 4 + tmp_length;

	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x1906;                 // STRING
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

	gds_write(tmp_s, tmp_length );
	free(tmp_s);

}  // write_string


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_sname( const char *s )
{
	static short int                // s should be null-terminated
		count,
		token;

	int tmp_length = -1;
	char* tmp_s = gds_adjust_string(s, &tmp_length);
	assert(tmp_length != -1);
	count = 4 + tmp_length;

	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x1206;                 // SNAME
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

	gds_write(tmp_s, tmp_length);
	free(tmp_s);

}  // write_sname


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_boundary(  )
{                             // just the token here. "xy" writes the actual polygon.
	static short int
		count,
		token;

	count = 4;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0800;                 // BOUNDARY
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

} // write_boundary


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_box(  )
{                             // Boxes were orignally for documentation only,
	// but later, people started using them like polygons.
	// The spec says we need to store five points,
	// just like a boundary, which is so stupid.
	static short int
		count,
	token;

	WARNING( "BOXES ARE STUPID. USE BOUNDARIES INSTEAD." );

	count = 4;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x2D00;                 // BOX
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

} // write_box


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_boxtype( short int dt )
{
	static short int
		count,
		token;

	if ( dt < 0 )
		WARNING( "NEGATIVE BOXTYPE NUMBER" ); 

	if ( dt > 255 )
		WARNING( "BOXTYPE > 255 " ); 

	count = 6;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x2E02;                 // BOXTYPE
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_swap2bytes( (BYTE *) &dt );
	gds_write((char*)(&dt), 2 );

}  // write_boxtype


/*------------------------------------------------------------------------------------------*/
void GdsWriter::gds_write_path(  )
{                             // Just the token here. "xy" writes the actual path.
	static short int
		count,
		token;

	count = 4;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0900;                 // PATH
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

}  // write_path


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_sref(  )
{                             // Only the token is written here.
	static short int
		count,
		token;

	count = 4;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0A00;                 // SREF
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

}  // write_sref


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_aref(  )
{
	static short int                   // write the aref token only
		count,
		token;

	count = 4;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0B00;                   // AREF
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

}  // write_aref


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_text(  )
{
	static short int                   // write the text token only
		count,
		token;

	count = 4;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0C00;                   // TEXT
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

}  // write_text


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_endel(  )
{
	static short int
		count,
		token;

	count = 4;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x1100;                 // ENDEL
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

}  // write_endel


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_layer( short int layer )
{
	static short int
		count,
		token;

	// Layers are actually supposed to go up to 64 only, but most programs allow
	// values up to 255, because 64 is stupid. Well 255 is also stupid, but less so.
	//
	// modified to -32768~32767

	//if ( layer < 0 || layer > 32767 ) BAILOUT( "INVALID LAYER NUMBER" );
	count = 6;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0D02;                 // LAYER
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_swap2bytes( (BYTE *) &layer );
	gds_write((char*)(&layer), 2 );

}  // write_layer


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_width( int width )
{
	static short int
		count,
		token;

	count = 8;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0F03;                 // WIDTH
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_swap4bytes( (BYTE *) &width );
	gds_write((char*)(&width), 4 );

}  // write_width


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_datatype( short int dt )
{
	static short int
		count,
		token;

	if ( dt < 0 )
		WARNING( "NEGATIVE DATATYPE NUMBER" ); 

	if ( dt > 255 )
		WARNING( "DATATYPE > 255 " ); 

	count = 6;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0E02;                 // DATATYPE
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_swap2bytes( (BYTE *) &dt );
	gds_write((char*)(&dt), 2 );

}  // write_datatype


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_texttype( short int dt )
{
	static short int
		count,
		token;

	if ( dt < 0 )
		WARNING( "NEGATIVE TEXT TYPE NUMBER" ); 

	if ( dt > 255 )
		WARNING( "TEXT TYPE > 255 " ); 

	count = 6;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x1602;                 // TEXTTYPE
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_swap2bytes( (BYTE *) &dt );
	gds_write((char*)(&dt), 2 );

}  // write_texttype


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_generations( short int gens )
{                                       // most useless parameter ever
	static short int
		count,
		token;

	if ( gens < 0 )
		WARNING( "NEGATIVE GENERATIONS NUMBER" ); 

	if ( gens > 99 )
		WARNING( "GENERATIONS > 99 " ); 

	count = 6;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x2202;                 // GENERATIONS
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_swap2bytes( (BYTE *) &gens );
	gds_write((char*)(&gens), 2 );

}  // write_generations


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_pathtype( short int pt )
{
	static short int
		count,
		token;

	if ( (pt < 0) || (pt > 4) )
		BAILOUT( "INVALID PATH TYPE NUMBER" ); 

	count = 6;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x2102;                 // PATHTYPE
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_swap2bytes( (BYTE *) &pt );
	gds_write((char*)(&pt), 2 );

}  // write_pathtype


/*------------------------------------------------------------------------------------------*/
/* Contains the font and orientation of text */
void GdsWriter::gds_write_presentation(      // file descriptor
		int font,    // font number              0, 1, 2, 3
		int vp,      // vertical presentation    0 = top  1 = middle  2 = bottom
		int hp )     // horizontal presentation  0 = left 1 = center  2 = right
{
	static unsigned short
		token, 
		count,
		num;

	if ( (font < 0) || (font > 3) )
	{
		font = 0;
		WARNING( "INVALID FONT NUMBER" );
	}

	if ( (vp < 0) || (vp > 2) )
	{
		vp = 0;
		WARNING( "INVALID VERTICAL PRESENTATION SENT TO WRITE_PRESENTATION" );
	}

	if ( (hp < 0) || (hp > 2) )
	{
		hp = 0;
		WARNING( "INVALID HORIZONTAL PRESENTATION SENT TO WRITE_PRESENTATION" );
	}


	num = hp + 4*vp + 16*font;

	gds_swap2bytes( (BYTE *) &num ); 
	count = 6;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x1701;
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_write((char*)(&num), 2 );

}  // write_presentation


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_strans(            // output file descriptor
		BOOL reflect,       // reflect about X axis before rotation (normally false)
		BOOL abs_angle,     // angles are absolute (normally false)
		BOOL abs_mag  )     // magnification (scale) is absolute (normally false) 
{             
	static unsigned short int
		count,
		token,
		strans;


	strans = 32768 * reflect + 2 * abs_mag + abs_angle;

	count = 6;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x1A01;                 // STRANS
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_swap2bytes( (BYTE *) &strans );
	gds_write((char*)(&strans), 2 );

}  // write_strans


/*------------------------------------------------------------------------------------------*/

// if has_last == true, number of xy pairs is n 
// else number of xy pairs is n+1
void GdsWriter::gds_write_xy( const int *x, const int *y, int n, bool has_last )
{
	static short int            // If this is a polygon, be sure to repeat the first vertex.
		count,                  // If this is a path, do not repeat.
		token;

	static int i;

	//if ( n > 200  ) WARNING( "OVER 200 VERTICIES" );
	if ( n+!has_last > 8200 ) BAILOUT( "WAY TOO MANY VERTICIES" );

	count = 4 + 8 * (n+!has_last);
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x1003;                 // XY
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );

	for ( i=0; i<n; i++ )
	{
		gds_swap4bytes( (BYTE *) &(x[i]) );
		gds_swap4bytes( (BYTE *) &(y[i]) );
		gds_write((char*)(&(x[i])), 4 );
		gds_write((char*)(&(y[i])), 4 );
	}
	if (n > 0 && !has_last)
	{
		gds_write((char*)(&(x[0])), 4 );
		gds_write((char*)(&(y[0])), 4 );
	}

}  // write_xy


/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_colrow(  int ncols, int nrows )
{             
	static unsigned short int
		count,
		token,
		sicols,
		sirows;

	if ( (ncols < 0) || (ncols > 32767) )
		BAILOUT( "NUMBER OF COLUMNS IS INVALID" ); 

	if ( (nrows < 0) || (nrows > 32767) )
		BAILOUT( "NUMBER OF ROWS IS INVALID" ); 

	sicols = ncols;
	sirows = nrows;

	count = 8;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x1302;                 // COLROW
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_swap2bytes( (BYTE *) &sicols );
	gds_write((char*)(&sicols), 2 );
	gds_swap2bytes( (BYTE *) &sirows );
	gds_write((char*)(&sirows), 2 );

}  // write_colrow

/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_units( double dbu_uu, double dbu_m )
{
	short int
		count,
		token;

	count = 20;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x0305;                 // UNITS
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_write_float( dbu_uu );
	gds_write_float( dbu_m );

}  // write_units

/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_mag( double mag )
{
	static int
		count,
		token;

	count = 12;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x1B05;   // MAG
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_write_float( mag );

}  // write_mag

/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_write_angle( double angle )
{
	static int
		count,
		token;

	count = 12;
	gds_swap2bytes( (BYTE *) &count );
	gds_write((char*)(&count), 2 );
	token = 0x1C05;   // ANGLE
	gds_swap2bytes( (BYTE *) &token );
	gds_write((char*)(&token), 2 );
	gds_write_float( angle );

}  // write_angle


/*------------------------------------------------------------------------------------------*/
//  HIGHER LEVEL FUNCTIONS
/*------------------------------------------------------------------------------------------*/


void GdsWriter::gds_create_lib( const char *libname, double dbu_um )
{
	// Write HEADER, BGNLIB, LIBNAME, and UNITS.


	double
		dbu_uu,        // database user units, 1 nm per bit
		dbu_m;         // database unit in meters, usually 1e-9m


	dbu_uu = 0.001;
	dbu_m  = dbu_um * 1.0e-6; 

	gds_write_header(  );
	gds_write_bgnlib(  );
	gds_write_libname(  libname );
	gds_write_units(  dbu_uu, dbu_m );

}  // create_lib



/*------------------------------------------------------------------------------------------*/

void GdsWriter::gds_create_text( const char *str, int x, int y, int layer, int size )
{ 
	static int xx[1], yy[1];

	// generate text centered at x,y

	gds_write_text(  );
	gds_write_layer( layer );
	gds_write_texttype( 0 );
	gds_write_presentation( 0, 1, 0 );  // this->out, font=0, vp=center, hp=left
	gds_write_width( size );
	gds_write_strans( 0, 0, 0 );        // this->out, reflect, abs_angle, abs_mag
	xx[0] = x;  
	yy[0] = y;
	gds_write_xy(  xx, yy, 1 );  
	gds_write_string( str );
	gds_write_endel(  );

} // create_text

/*------------------------------------------------------------------------------------------*/

// if input has odd length 
// append a '\0' to its end 
// output should not be already allocated 
// user should manually free output 
char* GdsWriter::gds_adjust_string(const char* input, int *output_length)
{
	const int input_length = strlen(input);
	char* output = (char*) malloc(sizeof(char)*(input_length+1));
	strncpy(output, input, input_length);
	output[input_length] = '\0';

	*output_length = input_length + (input_length%2);

	return output;
}

} // namespace GdsParser
