#ifndef ILP_solver_h_
#define ILP_solver_h_

#include <stdio.h>
#include <stdlib.h> /* srand, rand */
#include <time.h>   /* time */

#include <algorithm>
#include <climits>
#include <cmath>
#include <fstream>
#include <iostream>
#include <stack>
#include <string>
#include <utility>
#include <vector>

#include "../PnRDB/datatype.h"
#include "Aplace.h"
#include "ConstGraph.h"
#include "Pdatatype.h"
#include "SeqPair.h"
#include "design.h"
#include "lp_lib.h"

using std::cerr;
using std::cin;
using std::cout;
using std::make_pair;
using std::min;
using std::pair;
using std::stack;
using std::string;
using std::vector;

/**
* @file lp.h
* @brief Header for the C API of lp, including functions to
* create, modify and optimize Mixed Integer Linear Programming 
* Problems
*
* @author D.Sc. Haroldo G. Santos
*
* @date 8/2/2016
*/


#ifndef LP_HEADER
#define LP_HEADER

#define LP_ME_DEFAULT     0
#define LP_ME_OPTIMALITY  1
#define LP_ME_FEASIBILITY 2

/* Optimization direction */
#define LP_MIN 0
#define LP_MAX 1

/* Optimization result: */
#define LP_OPTIMAL       0
#define LP_INFEASIBLE    1
#define LP_UNBOUNDED     2
#define LP_FEASIBLE      3
#define LP_INTINFEASIBLE 4
#define LP_NO_SOL_FOUND  5
#define LP_ERROR         6

/* types of cut generators */
#define LP_CUT_TYPES   8
#define LPC_GOMORY     0
#define LPC_REDUCE     1
#define LPC_MIR        2
#define LPC_TWO_MIR    3
#define LPC_L_AND_P    4
#define LPC_ZERO_HALF  5
#define LPC_KNAPSACK   6
#define LPC_FLOW       7

/* constraint types, used when querying model */
#define CONS_PARTITIONING  0
#define CONS_PACKING       1
#define CONS_COVERING      2
#define CONS_CARDINALITY   3
#define CONS_KNAPSACK      4
#define CONS_INV_KNAPSACK  5
#define CONS_FLOW_BIN      6
#define CONS_FLOW_INT      7
#define CONS_FLOW_MX       8
#define CONS_VBOUND        9
#define CONS_OTHER        10
#define CONS_NUMBER       11 /* number of types */

/* LP Callback step */
#define LPCB_CUTS 0
#define LPCB_HEUR 1

typedef struct _LinearProgram LinearProgram;
typedef LinearProgram * LinearProgramPtr;

/** @defgroup groupCreateMod Problem creation and modification functions
 *  
 *  These are the functions that can be used to create and modify Mixed Integer Linear Programs
 *  @{
 */

/** @brief Creates an empty problem.
 *
 * Creates an empty problem.  Use lp_read to read a problem from a file or API functions (lp_add_cols, lp_add_row) 
 * fill the contents of this problem.
*/
LinearProgram *lp_create();


/** @brief Clones the problem in lp
 **/
LinearProgram *lp_clone( LinearProgram *lp );


/** @brief Reads a .lp or .mps file in fileName to object lp
 **/
void lp_read( LinearProgram *lp, const char *fileName );


/** @brief saves the problem in lp to file fileName. Use extension .lp or .mps to define file format.
 */
void lp_write_lp( LinearProgram *lp, const char *fileName );

/** @brief adds a new column (variable)
 * 
 * @param lp the (integer) linear program
 * @param obj the objective function coefficient of this variable
 * @param lb lower bound for this variable
 * @param ub upper bound for this variable
 * @param integer 1 if variable is integer, 0 otherwise
 * @param name variable name
 * @param nz number of non-zero entries of this column in the coefficient matrix
 * @param rowIdx indices of rows where this column appears
 * @param rowCoef coefficients that that this variable has in each of its rows
 */
void lp_add_col( LinearProgram *lp, double obj, double lb, double ub, char integer, char *name, int nz, int *rowIdx, double *rowCoef );


/** @brief adds new columns (variables)
 *
 *  adds new columns to lp, specifying objective function, bounds, integrality and names
 *
 *  @param lp the (integer) linear program
 *  @param count number of columns
 *  @param obj objective function coefficients
 *  @param lb lower bounds - if NULL is specified then it is assumed that all variables have lb=0.0
 *  @param ub upper bounds - if NULL is specified then it is assumed that all variables have ub=infinity
 *  @param integer - vector of boolean values indicating if each variable is integer, if NULL all variables
 *     are assumed to be integral
 *  @param names variable names
 */
void lp_add_cols( LinearProgram *lp, const int count, double *obj, double *lb, double *ub, char *integer, char **name );


/** @brief adds set of columns with the same bounds
 *
 *  @param lp the (integer) linear program
 *  @param count number of columns
 *  @param obj objective function coefficients
 *  @param lb lower bound for these variables
 *  @param ub upper bound for these variables
 *  @param vector indicating if each variable is integer (1) or continuous (0)
 */
void lp_add_cols_same_bound( LinearProgram *lp, const int count, double *obj, double lb, double ub, char *integer, char **name );


/** @brief adds a set of binary variables
 *
 *  @param lp the (integer) linear program
 *  @param count number of columns
 *  @param obj vector with objective function coefficients of these variables
 *  @param obj vector variable names
 */
void lp_add_bin_cols( LinearProgram *lp, const int count, double *obj, char **name );


/**
* Adds a new row (linear constraint) to the problem in lp
* @param lp the (integer) linear program
* @param nz number of non-zero variables in this row
* @param indexes indices of variables
* @param coefs coefficients of variables
* @param name row name
* @param sense E for equal, L for less-or-equal or G for greter-or-equal
* @param rhs right-hand-side of constraint
*/
void lp_add_row( LinearProgram *lp, const int nz, int *indexes, double *coefs, const char *name, char sense, const double rhs );


/**
* Adds new rows (linear constraints) to the problem in lp
* @param lp the (integer) linear program
* @param nRows number of rows
* @param vector indicating where each row i starts starts[i] and ends (starts[i+1]) in idx and coef
* @param idx column indexes 
* @param coef column coefficients
* @param sense E for equal, L for less-or-equal or G for greter-or-equal
* @param rhs right-hand-side of constraint
* @param names row names
*/
void lp_add_rows( LinearProgram *lp, int nRows, int *starts, int *idx, double *coef, char *sense, double *rhs, const char **names );


/** @brief Removes a row from lp
* 
* @param lp the (integer) linear program
* @param idxRow row index
*/
void lp_remove_row( LinearProgram *lp, int idxRow );


/** @brief Removes a set of rows from lp
* Removes a set of rows from lp, calling this function is usually faster
*  than to remove rows one-by-one
*
* @param lp the (integer) linear program
* @param nRows number of rows
* @param rows row indices
*/
void lp_remove_rows( LinearProgram *lp, int nRows, int *rows );


/** @brief sets optimization direction, maximization or minimization
 * 
 *  @param lp the (integer) linear program
 *  @param direction LP_MIN (0) for minimization (default) or LP_MAX (1) for maximization
 */
void lp_set_direction( LinearProgram *lp, const char direction );


/** @brief returns optimization direction, minimization (LP_MIN) or maximization (LP_MAX)
 * 
 *  @param lp the (integer) linear program
 *  @return 0 if minimization, 1 if maximization
 */
int lp_get_direction( LinearProgram *lp );


/** @brief sets objective function coefficients
 *
 *  @param lp the (integer) linear program
 *  @param obj objective function coefficients: obj[0] ... obj[n-1], where n is the number of columns
 */
void lp_set_obj( LinearProgram *lp, double obj[] );


/** @brief changes a set of objective function coefficients
 *
 *  @param lp the (integer) linear program
 *  @param count number of variables whose objective function coefficients will change
 *  @param idx indices of variables whose objective function coefficients will change
 *  @param coef vector with new coefficients
 */
void lp_chg_obj(LinearProgram *lp, int count, int idx[], double obj[] );


/** @brief modifies the right-hand-side of a constraint
 *
 *  @param lp the (integer) linear program
 *  @param row the row index
 *  @param rhs right-hand-side of constraint
 */
void lp_set_rhs( LinearProgram *lp, int row, double rhs );


/** @brief changes lower and upper bound of a column
 * 
 * @param lp the (integer) linear program
 * @param col column index
 * @param lb lower bound
 * @param ub upper bound
 * */
void lp_set_col_bounds( LinearProgram *lp, int col, const double lb, const double ub );


/** @brief fixed a column to a value
 *
 * @param lp the (integer) linear program
 * @param col column index
 * @param val value
 **/
void lp_fix_col( LinearProgram *lp, int col, double val );


/** @brief sets the type of some variables to integer
 *
 * @param lp the (integer) linear program
 * @param nCols number of columns
 * @param cols vector with column indices
 */
void lp_set_integer( LinearProgram *lp, int nCols, int cols[] );


/** @brief Saves the incumbent solution in for lp in fileName 
 * @param lp the (integer) linear program
 * @param fileName file name where the solution will be saved
 **/
void lp_write_sol( LinearProgram *lp, const char *fileName );


/** @brief Enters a initial feasible solution for the problem. Variables are referenced by their names. Only the main decision variables need to be informed.
 * @param lp the (integer) linear program
 * @param count number of variables whose value will be informed
 * @param colNames column names
 * @param colValues column values
 **/
void lp_load_mip_start(LinearProgram *lp, int count, const char **colNames, const double *colValues);

/** @brief Enters a initial feasible solution for the problem using column indexes. Only the main decision variables need to be informed.
 * @param lp the (integer) linear program
 * @param count number of variables whose value will be informed
 * @param colIndexes column indexes
 * @param colValues column values
 */
void lp_load_mip_starti( LinearProgram *lp, int count, const int *colIndexes, const double *colValues );


/** @brief Loads from fileName an initial feasible solution.
 *
 * Loads from fileName an initial feasible solution. The solution should be saved in a simple text file as in the example:
 *
 * `Stopped on iterations - objective value 57597.00000000` <br>
 * `0  x(1,1,2,2)               1 `<br>
 * `1  x(3,1,3,2)               1 `<br>
 * `5  v(5,1)                   2 `<br>
 * `33 x(8,1,5,2)               1 `<br>
 * `...`
 *
 * The first column (column index) is ignored. The first line is also ignored. Only column names (second column) and column values (third column) need to be informed
 * for non-zero variables.
 *
 * @param lp the (integer) linear program
 * @param fileName file name where the solution is stored
 **/
int lp_read_mip_start( LinearProgram *lp, const char *fileName );


/** @brief saves the solution entered as MIPStart
 * @param lp the (integer) linear program
 * @param fileName file name where the solution will be stored
 */
void lp_save_mip_start( LinearProgram *lp, const char *fileName );

/** @brief tries to discover the source of infeasibility in MIPStart
 * @param lp the (integer) linear program
 */
void lp_mipstart_debug( LinearProgram *lp );

/** @brief For debugging purposes: fixes mipstart variables one by one and optimizes (if initial solution is invalid at some point an infeasible LP will appear)
 * @param lp the (integer) linear program
 */
void lp_fix_mipstart( LinearProgram *lp );


/** @brief releases from memory the problem stored in lp
 * 
 *  @param lp the (integer) linear program, memory is freed and lp is set to NULL
 */
void lp_free( LinearProgramPtr *lp );

/** @brief frees environment static memory at the end of the program
 *
 * CPLEX and Gurobi need and environment, which LP creates on demand. Before your program exits, this
 * function should be called to free these data structures. */
void lp_close_env();


/** @} */ // end of group1

/** @defgroup groupOpt Optimization and parameter settings
 *  
 *  These are the functions that can be used to optimize your model and control
 *  some solver configuration.
 *  @{
 */


/** @brief Optimizes your Mixed Integer Program 
 *
 * Optimizes your Mixed Integer Program. Returns the problem status, which can be:<br>
 *
 * ` 0 : LP_OPTIMAL` : optimal solution found <br>
 * ` 1 : LP_INFEASIBLE` : the problem is infeasible <br>
 * ` 2 : LP_UNBOUNDED` : the problem is unbounded <br>
 * ` 3 : LP_FEASIBLE` : a feasible solution was found, but its optimality was not proved <br>
 * ` 4 : LP_INTINFEASIBLE` : the lp relaxation is feasible but no integer feasible solution exists <br>
 * ` 5 : LP_NO_SOL_FOUND` :  optimization concluded without finding any feasible solution <br>
 * ` 6 : LP_ERROR` : the solver reported an error <br>
 *
 *  @param lp the (integer) linear program
 * */
int lp_optimize( LinearProgram *lp );


/** @brief optimizes only the linear programming relaxation of your MIP
 *
 * Optimizes your Mixed Integer Program relaxing integrality constraints (if any). Returns the problem status, which can be:<br>
 *
 * ` 0 : LP_OPTIMAL` : optimal solution found <br>
 * ` 1 : LP_INFEASIBLE` : the problem is infeasible <br>
 * ` 2 : LP_UNBOUNDED` : the problem is unbounded <br>
 * ` 3 : LP_FEASIBLE` : a feasible solution was found, but its optimality was not proved <br>
 * ` 4 : LP_INTINFEASIBLE` : the lp relaxation is feasible but no integer feasible solution exists <br>
 * ` 5 : LP_NO_SOL_FOUND` :  optimization concluded without finding any feasible solution <br>
 * ` 6 : LP_ERROR` : the solver reported an error <br>
 *
 * @param lp the (integer) linear program
 **/
int lp_optimize_as_continuous( LinearProgram *lp );


/** @brief objective value of your optimization 
 * 
 *  @param lp the (integer) linear program
 *  @return objective value found
 * */
double lp_obj_value(LinearProgram *lp);


/** @brief returns the best dual bound found during the search
 *
 * If your Mixed Integer Optimization concluded without finding the optimal solution, you can
 * retrieve the best dual bound (lower bound in minimization), which is a valid estimate of the 
 * best possible value for the optimal solution.
 *
 *  @param lp the (integer) linear program
 *  @return the dual bound (lower bound if minimization)
 * */
double lp_best_bound( LinearProgram *lp ); 


/** @brief returns the vector of solution values
 *
 * @param lp the (integer) linear program
 * @return solution vector
 * */
double *lp_x( LinearProgram *lp );


/** @brief returns the slack vector for rows. Active (tight) rows have slack==0.0
 *
 * @param lp the (integer) linear program
 * @return row slack vector
 * */
double *lp_row_slack( LinearProgram *lp );


/** @brief returns a vector with the dual values, only available when solving continuous models
 * @param lp the (integer) linear program
 * @return vector with row prices
 * */
double *lp_row_price( LinearProgram *lp );


/** @brief reduced cost for columns - only available when solving continous models 
 * @param lp the (integer) linear program
 * @return vector with reduced costs
 * */
double *lp_reduced_cost( LinearProgram *lp );


/** @brief number of solutions stored in the solution pool 
 * @param lp the (integer) linear program
 * @return number of solutions in the solution pool
 * */
int lp_num_saved_sols( LinearProgram *lp );


/** @brief objective value for the isol-th solution of the solution pool 
 * @param lp the (integer) linear program
 * @param isol the solution index
 * @return objective value of the i-th solution from the solution pool
 * */
double lp_saved_sol_obj( LinearProgram *lp, int isol );


/** @brief objective value for the isol-th solution of the solution pool 
 * @param lp the (integer) linear program
 * @param isol the solution index
 * @return solution vector of the i-th solution from the solution pool
 */
double *lp_saved_sol_x( LinearProgram *lp, int isol );


/** @} */ // end of group1


// sets cutoff for MIP optimization, optionally also adds constraint */
void lp_add_cutoff( LinearProgram *lp, double cutoff, char addConstraint );
// higher values indicate that these fractional variables will be branched first
void lp_set_branching_priorities( LinearProgram *lp, int *priorities );
// 1: always chose up first, -1: always chose down first 0: automatic
void lp_set_branching_direction( LinearProgram *lp, int direction );

/* Model optimization, results query
   and solution methods parameters */
void lp_set_mip_emphasis( LinearProgram *lp, const int mipEmphasis );
int lp_get_mip_emphasis( LinearProgram *lp );
char *lp_status_str( int status, char *statusStr );
double lp_solution_time( LinearProgram *lp );

/* add cuts over LP relaxation
 *   maxRoundsCuts[] is a vector of integers
 *   0...LP_CUT_TYPES-1 where for each cut one
 *   must indicate the maximum number of rounds
 *   where this cut is separated */
int lp_strengthen_with_cuts( LinearProgram *lp, const int maxRoundsCuts[] );

/* add some cut manually
 * or when using the callback */
void lp_add_cut( LinearProgram *lp, int nz, int *cutIdx, double *cutCoef, const char *name, char sense, double rhs );

/* command line options */
void lp_parse_options( LinearProgram *lp, int argc, const char **argv );
void lp_help_options( );

/* parameters - input/output */
void lp_set_sol_out_file_name( LinearProgram *lp, const char *sfn );
void lp_set_sol_in_file_name( LinearProgram *lp, const char *sfn );
/* parameters - heuristics */
void lp_set_heur_proximity( LinearProgram *lp, char onOff );
void lp_set_heur_fp_passes( LinearProgram *lp, int passes );
/* parameters - cuts */
void lp_set_cuts( LinearProgram *lp, char onOff );
/* parameters - input/output */
void lp_set_print_messages( LinearProgram *lp, char onOff );
/* parameters - limits */
void lp_set_max_seconds( LinearProgram *lp, int _max );
void lp_set_max_solutions( LinearProgram *lp, int _max );
void lp_set_max_nodes( LinearProgram *lp, int _max );
void lp_set_max_saved_sols( LinearProgram *lp, int _max );
void lp_set_abs_mip_gap( LinearProgram *lp, const double _value );
void lp_set_rel_mip_gap( LinearProgram *lp, const double _value );
/* parameters - parallel */
void lp_set_parallel( LinearProgram *lp, char onOff );

/** @defgroup groupQuery Query problem information
 *  
 *  Routines to query problem information
 *  @{
 */


/** @brief checks if there are integer variables in this program
 *  @param lp the (integer) linear program
 *  @return 1 if there are integer variables, 0 otherwise
 *  */
char lp_is_mip( LinearProgram *lp );


/** @brief checks if a given variable is integer or continuous
 *  @param lp the (integer) linear program
 *  @param j column index
 *  @return 1 if variable is integer, 0 otherwise
 *  */
char lp_is_integer( LinearProgram *lp, const int j );


/** @brief checks if a given variable is binary or not
 *  @param lp the (integer) linear program
 *  @param j column index
 *  @return 1 if variable is integer, 0 otherwise
 *  */
char lp_is_binary( LinearProgram *lp, const int j );



/** @brief counts the number of binary, general integer and continuous variables in this problem 
 *  @param lp the (integer) linear program
 *  @param binaries pointer to the integer that will be used to compute the number of binary variables
 *  @param integer pointer to the integer that will be used to compute the number of general integer variables
 *  @param continuous pointer to the integer that will be used to compute the number of continuous variables
 * */
void lp_cols_by_type( LinearProgram *lp, int *binaries, int *integers, int *continuous );



/** @brief returns the numbef of columns (variables) in a given problem
 *  @param lp the (integer) linear program
 *  @return number of columns (variables)
 * */
int lp_cols( LinearProgram *lp );


/** @brief returns the numbef of rows (linear constraints) in a given problem
 *  @param lp the (integer) linear program
 *  @return number of rows (linear constraints)
 * */
int lp_rows( LinearProgram *lp );


/** @brief returns the numbef of non-zero coefficients in the linear program rows
 *  @param lp the (integer) linear program
 *  @return number of non-zero coefficients in the linear program rows
 * */
int lp_nz( LinearProgram *lp );


/** @brief gets the contents of a given row (linear constraint)
 *  @param lp the (integer) linear program
 *  @param row row index
 *  @param idx pointer to the vector of indexes that will be filled
 *  @param idx pointer to the vector of coefficients that will be filled
 *  @return number of non-zeros in row
 *  */
int lp_row( LinearProgram *lp, int row, int *idx, double *coef );


/** @brief gets the contents of a given column (variable)
 *  @param lp the (integer) linear program
 *  @param col column index
 *  @param pointer to the vector of row indexes that will be filled
 *  @param pointer to the vector of row coefficients that will be filled
 *  @return number of rows that column appears
 */
int lp_col( LinearProgram *lp, int col, int *idx, double *coef );


/** @brief returns the right hand side of a given row
 *  @param lp the (integer) linear program
 *  @return right hand side of row row
 **/
double lp_rhs( LinearProgram *lp, int row );


/** @brief returns the sense of a given constraint
 *
 * Returns the sense of a given constraint:
 *
 * ` E : ` : equal (=) <br>
 * ` G : ` : greater-or-equal (>=) <br>
 * ` L : ` : less-or-equal (<=) <br>
 *
 *  @param lp the (integer) linear program
 *  @param row row index
 * */
char lp_sense( LinearProgram *lp, int row );


/** @brief queries a row name
 *  @param lp the (integer) linear program
 *  @param row row index
 *  @param dest string where the row name will be saved
 *  @return row name
 **/
char *lp_row_name( LinearProgram *lp, int row, char *dest );


/** @brief queries a column name
 *  @param lp the (integer) linear program
 *  @param col column index
 *  @param dest string where the column name will be saved
 *  @return column name
 **/
char *lp_col_name( LinearProgram *lp, int col, char *dest );


/** @brief queries a column lower bound
 *  @param lp the (integer) linear program
 *  @param col column index
 *  @return column lower bound
 *  */
double lp_col_lb( LinearProgram *lp, int col );


/** @brief queries a column upper bound
 *  @param lp the (integer) linear program
 *  @param col column index
 *  @return column upper bound
 *  */
double lp_col_ub( LinearProgram *lp, int col );


/** @brief returns the column (variable) index of a given column name
 *  @param lp the (integer) linear program
 *  @param name column name
 *  @return column index
 *  */
int lp_col_index( LinearProgram *lp, const char *name );


/** @brief returns the row (linear constraint) index of a given row name
 *  @param lp the (integer) linear program
 *  @param name row name
 *  @return row index
 *  */
int lp_row_index( LinearProgram *lp, const char *name );


/** @brief return the vector with objective coefficients
 *  @param lp the (integer) linear program
 *  @return vector with objective coefficients
 **/
const double *lp_obj_coef( LinearProgram *lp );


/** @brief returns the constraint type of a given row
 *
 * Returns the constraint type:<br>
 *
 * ` 0 : CONS_PARTITIONING` : set partitioning constraint <br>
 * ` 1 : CONS_PACKING` : set packing constraint <br>
 * ` 2 : CONS_COVERING` : set covering constraints <br>
 * ` 3 : CONS_CARDINALITY` : cardinality constraint <br>
 * ` 4 : CONS_KNAPSACK` : knapsack constraint <br>
 * ` 5 : CONS_INV_KNAPSACK` :  invariant knapsack constraint <br>
 * ` 6 : CONS_FLOW_BIN` : flow constraint with binary variables <br>
 * ` 7 : CONS_FLOW_INT` : flow constraint with general integer variables <br>
 * ` 8 : CONS_FLOW_MX` : flow constraint continuous and or integer variables <br>
 * ` 9 : CONS_VBOUND` : variable bound constraint <br>
 *
 *  @param lp the (integer) linear program
 *  @param row row index
 *  @return constraint type
 * */
int lp_row_type( LinearProgram *lp, const int row );


/** @brief fills the constraint types vector
 *
 * Fills a constraint type vector:<br>
 *
 * ` 0 : CONS_PARTITIONING` : set partitioning constraint <br>
 * ` 1 : CONS_PACKING` : set packing constraint <br>
 * ` 2 : CONS_COVERING` : set covering constraints <br>
 * ` 3 : CONS_CARDINALITY` : cardinality constraint <br>
 * ` 4 : CONS_KNAPSACK` : knapsack constraint <br>
 * ` 5 : CONS_INV_KNAPSACK` :  invariant knapsack constraint <br>
 * ` 6 : CONS_FLOW_BIN` : flow constraint with binary variables <br>
 * ` 7 : CONS_FLOW_INT` : flow constraint with general integer variables <br>
 * ` 8 : CONS_FLOW_MX` : flow constraint continuous and or integer variables <br>
 * ` 9 : CONS_VBOUND` : variable bound constraint <br>
 *
 *  @param lp the (integer) linear program
 *  @param rtype vector where constraint types will be filled
 * */
void lp_rows_by_type( LinearProgram *lp, int rtype[] );


/** @brief if this is a pre-processed problem, returns indexes of respective original columns
 *  @param lp the (integer) linear program
 *  @return vector with indexes of respective original columns
 **/
int *lp_original_colummns( LinearProgram *lp );


/** @} */ // end of group1

/* callback function prototype */
typedef int (*lp_cb)( LinearProgram *lp, int whereFrom, const int *origCols, LinearProgram *origLP, void *data );
/* enter callback info */
void lp_set_callback( LinearProgram *lp, lp_cb callback, void *data );

// global flag indicating if variable/row names will be stored, can save some memory when off
void lp_set_store_names( bool store );

#endif

class ILP_solver {
  friend class Placer;

  private:
  struct Block {
    int x = 0, y = 0;            // LL of each block
    int H_flip = 0, V_flip = 0;  // flip along V axis and H axis
  };
  vector<Block> Blocks;
  placerDB::point LL, UR;
  double area = 0, HPWL = 0, HPWL_ILP = 0., HPWL_extend = 0, HPWL_extend_terminal = 0, ratio = 0, linear_const = 0, multi_linear_const = 0;
  double area_norm = 0, HPWL_norm = 0;
  double Aspect_Ratio_weight = 1000;
  double Aspect_Ratio[2] = {0, 100};
  double placement_box[2] = {-1.0, -1.0};
  typedef void(lphandlestr_func)(lprec* lp, void* userhandle, char* buf);
  static void lpsolve_logger(lprec* lp, void* userhandle, char* buf);
  vector<vector<int>> block_order;
  int x_pitch, y_pitch;

  inline void roundup(int& v, const int pitch) { v = pitch * ((v + pitch - 1) / pitch); }
  bool MoveBlocksUsingSlack(const std::vector<Block>& blockslocal, const design& mydesign, const SeqPair& curr_sp, const PnRDB::Drc_info& drcInfo);
  bool FrameSolveILP(const design& mydesign, const SeqPair& curr_sp, const PnRDB::Drc_info& drcInfo, bool flushlb = true, const vector<placerDB::point>* prev = nullptr);
  public:
  double cost = 0;
  double constraint_penalty = 0;
  ILP_solver();
  ILP_solver(design& mydesign, PnRDB::hierNode& node);
  ILP_solver(design& mydesign);
  ILP_solver(const ILP_solver& solver);
  ILP_solver& operator=(const ILP_solver& solver);
  double GenerateValidSolutionAnalytical(design& mydesign, PnRDB::Drc_info& drcInfo, PnRDB::hierNode& node);
  double GenerateValidSolution(const design& mydesign, const SeqPair& curr_sp, const PnRDB::Drc_info& drcInfo);
  double GenerateValidSolution_select(design& mydesign, SeqPair& curr_sp, PnRDB::Drc_info& drcInfo);
  double CalculateCost(const design& mydesign) const;
  double CalculateCost(const design& mydesign, const SeqPair& curr_sp) ;
  void WritePlacement(design& caseNL, SeqPair& curr_sp, string outfile);
  void PlotPlacement(design& mydesign, SeqPair& curr_sp, string outfile);
  void PlotPlacementAnalytical(design& caseNL, string outfile, bool plot_pin, bool plot_terminal, bool plot_net);
  std::vector<double> Calculate_Center_Point_feature(std::vector<std::vector<placerDB::point>>& temp_contact);
  void updateTerminalCenter(design& mydesign, SeqPair& curr_sp);
  void updateTerminalCenterAnalytical(design& mydesign);
  void UpdateHierNode(design& mydesign, SeqPair& curr_sp, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo);
  void UpdateHierNodeAnalytical(design& mydesign, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo);
  void UpdateBlockinHierNode(design& mydesign, placerDB::Omark ort, PnRDB::hierNode& node, int i, int sel, PnRDB::Drc_info& drcInfo);
  void UpdateTerminalinHierNode(design& mydesign, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo);
  void UpdateSymmetryNetInfoAnalytical(design& mydesign, PnRDB::hierNode& node, int i, int SBidx, placerDB::Smark axis_dir);
  void UpdateSymmetryNetInfo(design& mydesign, PnRDB::hierNode& node, int i, int SBidx, placerDB::Smark axis_dir, SeqPair& curr_sp);
  PnRDB::bbox ConvertBoundaryData(vector<placerDB::point> Bdata);
  PnRDB::point ConvertPointData(placerDB::point Pdata);
};

#endif
