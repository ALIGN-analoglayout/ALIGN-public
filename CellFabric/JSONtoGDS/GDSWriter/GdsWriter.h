/**
 * @file   GdsWriter.h
 * @brief  write GDSII file 
 * @author Yibo Lin
 * @date   Nov 2014
 */

#ifndef _GDSPARSER_GDSWRITER_H
#define _GDSPARSER_GDSWRITER_H

#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <time.h>
#include <assert.h>
#include <vector>
#include <iostream>
#include <fstream>

/// Setting BYTESWAP to 1 is appropriate for big-endian Intel processors. 
/// GDS format was originally used on little-endian, older computers.
#define BYTESWAP 1
//#define BYTE unsigned char

//#define BOOL  int
//#define TRUE  1
//#define FALSE 0

//extern BYTE  gdsswap;
//extern short gdsword;

/// namespace for Limbo.GdsParser
namespace GdsParser
{

/// use integer as bool 
typedef int BOOL;
/// use unsigned char as byte 
typedef unsigned char BYTE;

/// @brief GDSII item type 
struct gds_itemtype
{                                /*!< an item might be a polygon, path, aref, sref or text                      */
	int   type;                      /*!< 0 = polygon, 1 = path, 2 = aref, 3 = sref, 4 = text, 5 = box              */
	int   n;                         /*!< in the case of polygons or paths, this is the number of verticies         */
	/*!<     for text this is the number of characters in the string               */
	int   layer;                     /*!< layer                                                                     */
	int   dt;                        /*!< datatype                                                                  */ 
	int   cell_number;               /*!< index into the table of cells- relevant for sref and aref                 */
	double mag;                       /*!< magnification- relevant to sref, aref and text                            */
	double angle;                     /*!< the angle - relevant to sref and aref                                     */
	BOOL  abs_angle;                 /*!< from strans - normally false                                              */
	BOOL  abs_mag;                   /*!< from strans - normally false                                              */
	BOOL  reflect;                   /*!< from strans (reflect over x axis before rotating)                         */
	int   cols;			     /*!< Yes, many of these items are relevant to only one type of item, so        */
	int   rows;			     /*!< perhaps we should invent a different item type for each item, then        */
	int   col_pitch;		     /*!< string them together in a linked list of items.  Why not?                 */
	int   row_pitch;		     /*!< Because the "library" has to be a linked list of one "thing". What we     */
	int   col_pitchy;                /*!< An array's column pitch in y, which would create a diagonal array.        */
	int   row_pitchx;                /*!< An array's row pitch in x. Diagonal arrays are strange and useless.       */
	int   path_end;		     /*!< 0 = flush, 1 = round, 2 = extended. Default 0.                            */
	int   hor_present;		     /*!< The horizontal presentation for text.                                     */
	int   ver_present;		     /*!< The vertical presentation for text.                                       */
	int   font;			     /*!< Also relevant only for text.                                              */
	int   width;                     /*!< Relevant only to paths.                                                   */
	int  *x;                         /*!< array of x coordinates or possibly just the reference point X             */
	int  *y;                         /*!< array of y coordinates or possibly just the reference point Y             */
	char *text;                      /*!< Used only for strings. Such a waste.                                      */
	struct gds_itemtype *nextitem;      /*!< next item */ 
};                               

/// @brief cell type 
struct gds_celltype                  /*!< A GDS library is a linked list of cells.                                  */
{                                /*!< A cell is a linked list of items.                                         */
	char *name;                      /*!< name of the cell                                                          */
	struct gds_itemtype *item;       /*!< one element of the cell                                                   */
	struct gds_celltype *nextcell;   /*!< pointer to the next cell, forming a linked list                           */  
};

// forward declaration of a writer class 
// which is flexiable to choose std::ofstream or boost::iostreams
class GdsStream; 

/// @class GdsParser::GdsWriter
/// write GDSII 
struct GdsWriter
{
    public:
        /// @brief constructor 
        /// @param filename output file name 
        GdsWriter(const char* filename);
        /// @brief destructor 
        ~GdsWriter();

        /**************** high level interfaces *****************/
        /// @name high level interfaces 
        ///@{

        /// @brief write a boundary object 
        /// @param layer layer 
        /// @param datatype data type 
        /// @param vx array of x coordinates 
        /// @param vy array of y coordinates 
        /// @param has_last if true, it means the last point is the same as the first point; 
        ///                 otherwise, we need to add one point to the end.  
        ///                 Default value is true 
        void write_boundary(int layer, int datatype, std::vector<int> const& vx, std::vector<int> const& vy, bool has_last = true);
        /// @brief write a box object 
        /// @param layer layer 
        /// @param datatype data type 
        /// @param xl, yl, xh, yh coordinates of the box 
        void write_box(int layer, int datatype, int xl, int yl, int xh, int yh);
        /// @brief create GDSII library 
        /// @param libname name of the library 
        /// @param dbu_uu is user unit, 1nm per bit
        /// @param dbu_m is database unit in meter, usually 1e-9 
        /// this wrapper is different from gds_create_lib in terms of units 
        void create_lib(const char* libname, double dbu_uu, double dbu_m);

        ///@}
        
        /**************** low level interfaces *****************/
        /// @name low level interfaces 
        ///@{
        
        void gds_make_next_item( struct gds_itemtype **ci );
        /* dump one byte in binary format */
        void gds_bindump( BYTE x );
        /* Write 8 bytes after converting back to wacky GDS float format. */
        void gds_write_float( double x );
        /// @brief swap bytes 
        /// @param four 4-byte of data 
        void gds_swap4bytes( BYTE *four  );
        /// @brief swap bytes 
        /// @param two 2-byte of data 
        void gds_swap2bytes( BYTE *two );
        /// @brief write HEADER 
        void gds_write_header(  );
        /// @brief write BGNLIB 
        void gds_write_bgnlib(  );
        /// @brief write BGNSTR 
        void gds_write_bgnstr(  );
        /// @brief write ENDLIB 
        void gds_write_endlib(  );
        /// @brief write ENDSTR 
        void gds_write_endstr(  );
        /// @brief write LIBNAME 
        /// @param name name of library 
        void gds_write_libname( const char *name );
        /// @brief write STRNAME 
        /// @param name name
        void gds_write_strname( const char *name );
        /// @brief write STRING
        /// @param s string 
        void gds_write_string( const char *s );
        /// @brief write SNAME 
        /// @param s string 
        void gds_write_sname( const char *s );
        /// @brief write BOUNDARY
        void gds_write_boundary(  );
        /// @brief write BOX 
        void gds_write_box(  );
        /// @brief write BOXTYPE
        /// @param dt data type 
        void gds_write_boxtype( short int dt );
        /// @brief write PATH 
        void gds_write_path(  );
        /// @brief write SREF 
        void gds_write_sref(  );
        /// @brief write AREF 
        void gds_write_aref(  );
        /// @brief write TEXT 
        void gds_write_text(  );
        /// @brief write ENDEL 
        void gds_write_endel(  );
        /// @brief write LAYER 
        /// @param layer layer 
        void gds_write_layer( short int layer );
        /// @brief write WIDTH 
        /// @param width width 
        void gds_write_width( int width );
        /// @brief write DATATYPE
        /// @param dt data type 
        void gds_write_datatype( short int dt );
        /// @brief write TEXTTYPE
        /// @param dt text type 
        void gds_write_texttype( short int dt );
        /// @brief write GENERATIONS
        /// @param gens generations 
        void gds_write_generations( short int gens );
        /// @brief write PATHTYPE 
        /// @param pt path type 
        void gds_write_pathtype( short int pt );
        /// @brief write PRESENTATION
        /// @param font font number 0, 1, 2, 3
        /// @param vp vertical presentation 0 = top  1 = middle  2 = bottom
        /// @param hp horizontal presentation 0 = left 1 = center  2 = right
        void gds_write_presentation( int font, int vp, int hp );
        /// @brief write STRANS
        /// @param reflect reflect about X axis before rotation (normally false)
        /// @param abs_angle angles are absolute (normally false)
        /// @param abs_mag magnification (scale) is absolute (normally false) 
        void gds_write_strans( BOOL reflect, BOOL abs_angle, BOOL abs_mag  );
        /// @brief write XY 
        /// @param x array of x coordinates 
        /// @param y array of y coordinates 
        /// @param n length of array 
        /// @param has_last if true, it means the last point is the same as the first point; 
        ///                 otherwise, we need to add one point to the end.  
        ///                 Default value is true.  
        void gds_write_xy( const int *x, const int *y, int n, bool has_last = true);
        /// @brief write COLROW 
        /// @param ncols number of columns 
        /// @param nrows number of rows 
        void gds_write_colrow( int ncols, int nrows );
        /// @brief write UNITS
        /// @param dbu_uu database unit in user units, usually 0.001
        /// @param dbu_m database unit in meters, usually 1e-9
        void gds_write_units( double dbu_uu, double dbu_m );
        /// @brief write MAG
        /// @param mag magnification 
        void gds_write_mag( double mag );
        /// @brief write ANGLE
        /// @param angle angle in degree 
        void gds_write_angle( double angle );
        /// @brief create library with name and unit 
        /// @param libname name of library 
        /// @param dbu_um database unit in microns, usually 1e-6
        void gds_create_lib( const char *libname, double dbu_um );    
        /// @brief wrapper to create text 
        /// @param str text 
        /// @param x x position 
        /// @param y y position 
        /// @param layer layer 
        /// @param size text size 
        void gds_create_text( const char *str, int x, int y, int layer, int size );

        ///@}

        // add by Yibo Lin 
        /// handle string with odd length; 
        /// generate new string output and return its length 
        /// @param input a string 
        /// @param output_length result length 
        /// @return a new string 
        char* gds_adjust_string(const char* input, int *output_length);

    protected:

        /// a buffered putting scheme to speedup writing 
        /// \return negative value if error 
        /// by Yibo Lin 
        int gds_write(const char* b, std::size_t n); 
        /// flush all contents in the buffer 
        void gds_flush(); 

        GdsStream* m_os; ///< output stream 
        //int out; // output gds file descriptor
        BYTE  gdsswap; ///< moved from global variables 
        short gdsword; ///< move from global variables 

        std::size_t m_capacity; ///< output buffer capacity 
        std::size_t m_size; ///< output buffer size 
        char* m_buffer; ///< output buffer 
};

} // namespace GdsParser

#endif 
