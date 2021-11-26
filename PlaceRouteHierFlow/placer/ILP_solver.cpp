#include "ILP_solver.h"
#include "CoinTypes.hpp"
#include "Cbc_C_Interface.h"
#include "lp.h"

#include <stdexcept>

#include "spdlog/spdlog.h"


/* at least one solver need to be selected to compile this file */

#define CBC 1

#include <cstddef>
#include <cstring>
#include <cstdlib>
#include <cstdio>
#include <cstdarg>
#include <cassert>
#include <cfloat>
#include <climits>
#include <cmath>
#include <set>
#include <algorithm>
#include <omp.h>
#include <ctime>
#include <cctype>
#include <string>
#include <vector>
#include <map>

#define FILE_NAME_SIZE 1024

#define ERROR( msg ) \
    fprintf( stderr, msg ); \
    abort(); \
    exit(1);

// check if solver needs variable and row indexes
#define NEED_OWN_INDEX 
#include <sstream>

#define SSTR( x ) dynamic_cast< std::ostringstream & >( \
        ( std::ostringstream() << std::dec << x ) ).str()


static inline bool is_integer( const double v );

using namespace std;

// solver dependent includes and definitions
#include <OsiSolverInterface.hpp>
#include <OsiClpSolverInterface.hpp>
#include <OsiCbcSolverInterface.hpp>
#include <CoinBuild.hpp>
#include <CglPreProcess.hpp>

static bool LPstoreNames = true;

const double EPS=1e-5;

#define INT_NOT_SET INT_MIN

struct _LinearProgram {
    /* if integrality should not be considered in lp_optimize() */
    char optAsContinuous;

    /* if all variables need to be set as integer before solving */
    char allInteger; 

    /* number of optimizations already performed */
    int nOptimizations;

    /* solution status */
    double obj;
    double bestBound;
    int status;
    double solutionTime;

    // parameters
    double cutoff;
    char cutoffAsConstraint;


    vector< double > *_x;
    vector< double > *_pi;
    vector< double > *_slack;
    vector< double > *_rc;
    vector< double > *_obj;
    vector< int > *_idx;
    vector< double > *_coef;
    vector< int > *_orig;   /* original columns */

    vector< vector< double > > *_savedSol;
    vector< double > *_savedObj;

#ifdef NEED_OWN_INDEX
    map< string, int > *colNameIdx;
    map< string, int > *rowNameIdx;
#endif

    std::vector< int > *_priorities;

    // MIPStart related data structures
    char **msNames;
    int *msIdx;
    double *msVal;
    int msVars;



    /* parameters */
    int mipEmphasis;
    char mipPreProcess;
    int heurFPPasses;
    int heurProx;
    int maxSeconds;
    int maxSolutions; // exit after found n solutions
    int maxSavedSols;
    int maxNodes;
    int cuts;
    int printMessages;
    double absMIPGap;
    double relMIPGap;
    int parallel;
    int branchDir;
    char silent;

    /* callback function */
    lp_cb callback_;
    void *data_;

    char solOutFN[256];
    char solInFN[256];

    // defining solver dependent
    // LP storing type
#ifdef CBC
    OsiClpSolverInterface *_lp;
    OsiSolverInterface *osiLP;

    /* is a wrapper to an existing osisolverinterface, i.e. should not delete
     * object */
    char justWrapOsi;

    // if model is pre processed then this should be stored
    CglPreProcess *cglPP;

    OsiCuts *cutPool;
    char ownCutPool;
#endif
};

bool lp_str_is_num( const char *str );

#ifdef CBC
void lp_config_cbc_params(LinearProgram *lp, vector<string> &cbcOpt);
#endif

void lp_printRootRelaxInfo(LinearProgram *lp);


#ifdef CBC
/* makes a lp use a predefined OsiSolverInterface (already populated) */
LinearProgram *lp_wrap_osisolver( OsiSolverInterface *osiLP );

// cut generator to accept callbacks in CBC
//
class CglCallback : public CglCutGenerator
{
    public:
        CglCallback();

        lp_cb callback_;
        LinearProgram *lp;
        void *data;
        CbcModel *model;

        /// Copy constructor
        CglCallback(const CglCallback& rhs);

        /// Clone
        virtual CglCutGenerator * clone() const;

        virtual void generateCuts( const OsiSolverInterface & si, OsiCuts & cs,
                const CglTreeInfo info = CglTreeInfo() );

        virtual ~CglCallback();
    private:
};


CglCallback::CglCallback()
    : callback_(NULL),
    lp(NULL),
    data(NULL),
    model(NULL)
{
}

CglCallback::CglCallback(const CglCallback& rhs)
{
    this->callback_ = rhs.callback_;
    this->lp = rhs.lp;
    this->data = rhs.data;
    this->model = rhs.model;
}

CglCutGenerator* CglCallback::clone() const
{
    CglCallback *cglcb = new CglCallback();
    cglcb->callback_ = this->callback_;
    cglcb->lp = this->lp;
    cglcb->data = this->data;
    cglcb->model = this->model;

    return static_cast<CglCutGenerator*>(cglcb);
}

void CglCallback::generateCuts( const OsiSolverInterface &si, OsiCuts &cs, const CglTreeInfo info )
{
    LinearProgram *lp = lp_wrap_osisolver( (OsiSolverInterface *)&si );

    lp->nOptimizations = 0;

    lp->status = LP_ERROR;
    if (lp->osiLP->isProvenOptimal()) {
        /* getting primal and dual solution */
        lp->_x->resize(lp_cols(lp));
        lp->_rc->resize(lp_cols(lp));
        lp->_pi->resize(lp_rows(lp));
        lp->_slack->resize(lp_rows(lp));
        memcpy(&((*(lp->_x))[0]) , lp->osiLP->getColSolution(), sizeof(double)*lp_cols(lp));
        memcpy(&((*(lp->_rc))[0]) , lp->osiLP->getReducedCost(), sizeof(double)*lp_cols(lp));
        memcpy(&((*(lp->_pi))[0]) , lp->osiLP->getRowPrice(), sizeof(double)*lp_rows(lp));
        for ( int i=0 ; (i<lp_rows(lp)) ; ++i )
        {
            double activity = lp->osiLP->getRowActivity()[i];
            double lower = lp->osiLP->getRowLower()[i];
            double upper = lp->osiLP->getRowUpper()[i];
            (*lp->_slack)[i] = std::min( upper-activity, activity-lower );
        }

        lp->obj = lp->osiLP->getObjValue();
        lp->status = LP_OPTIMAL;
        lp->nOptimizations = 1;
    }

    lp->cutPool = &cs;
    this->callback_( lp, LPCB_CUTS, this->model->originalColumns(), this->lp, this->data );
    lp_free(&lp);
}

CglCallback::~CglCallback()
{

}

#endif

/* from names */
void lp_check_mipstart( LinearProgram *lp )
{
    if (lp->msVars==0)
        return;

    assert( lp->msNames!=NULL && lp->msVal!=NULL );

    if (lp->msIdx==NULL)
        lp->msIdx = new int[lp->msVars];

    char warned = 0;
    int p = 0, j = 0;
    int totalChars = 0;
    for ( ; (j<lp->msVars) ; ++j )
    {
        int idxv = lp_col_index( lp, lp->msNames[j] );
        if ( idxv==-1 )
        {
            if (warned<5)
            {
                printf("MIPStart warning: variable %s not found.\n", lp->msNames[j] );
                warned++;
            }
        }
        else
        {
            const double lb = lp_col_lb( lp, idxv );
            const double ub = lp_col_ub( lp, idxv );
            if (lp->msVal[p] >= ub+1e-8 || lp->msVal[p]<=lb-1e-8)
            {
                if (warned<5)
                {
                    printf("MIPStart warning: invalid value informed for variable %s. valid bounds are: [%g,%g].\n", lp->msNames[j], lb, ub );
                    warned++;
                }
            }
            else
            {
                // fixation ok
                lp->msIdx[p] = idxv;
                lp->msVal[p] = lp->msVal[j];
                totalChars += strlen( lp->msNames[j] ) + 1;
                ++p;
            }
        }
    }

    // not all names or bounds are ok
    // including only correct entries
    if ( p && p!=j )
    {
        free( lp->msNames[0] );
        free( lp->msNames );
        lp->msNames = (char**) malloc( (p+1)*sizeof(char*) );
        assert( lp->msNames );
        lp->msNames[0] = (char*) malloc( totalChars*sizeof(char) );
        assert( lp->msNames[0] );
        for ( int i=0 ; (i<p) ; ++i )
        {
            char cName[512] = "";
            lp_col_name( lp, lp->msIdx[i], cName );
            strcpy( lp->msNames[i], cName );
            lp->msNames[i+1] = lp->msNames[i] + strlen(cName)+1;
        }
    }

    lp->msVars = p;
}

void lp_initialize(LinearProgram *lp);

/* to be used in clone */
LinearProgramPtr lp_create_from( LinearProgram *lp );

LinearProgramPtr lp_create()
{
    return lp_create_from( NULL );
}


LinearProgramPtr lp_create_from( LinearProgram *lp )
{
    LinearProgram *result = (LinearProgramPtr) malloc(sizeof(LinearProgram));
    assert(result);

    lp_initialize(result);

#ifdef CBC
    /* cloning */
    if ( lp && lp_cols(lp) )
    {
        result->_lp   = dynamic_cast<OsiClpSolverInterface *>(lp->_lp->clone());
        result->_lp->messageHandler()->setLogLevel(0);
        result->_lp->getModelPtr()->setPerturbation(50);
        result->osiLP = dynamic_cast<OsiSolverInterface *>(result->_lp);
        result->cglPP = NULL;
    }
    else
    {
        result->_lp   = new OsiClpSolverInterface();
        result->_lp->messageHandler()->setLogLevel(0);
        result->_lp->getModelPtr()->setPerturbation(50);
        result->osiLP = dynamic_cast<OsiSolverInterface *>(result->_lp);
        result->cglPP = NULL;
    }

    if (LPstoreNames)
        result->osiLP->setIntParam(OsiNameDiscipline, 1);
#endif

    result->allInteger = 0;

    return result;
}

char getFileType(const char *fileName)
{
    if ( strstr(fileName, ".mps") || strstr(fileName, ".MPS") || strstr(fileName, ".mps.gz") || strstr(fileName, ".MPS.GZ") )
        return 'M';

    return 'L';
}

#ifdef NEED_OWN_INDEX
void lp_fill_col_name_index( LinearProgram *lp )
{
    lp->colNameIdx->clear();
    char colName[512]="";

    for (int i = 0 ; (i < lp_cols(lp)) ; ++i)
        (*lp->colNameIdx)[lp_col_name(lp, i, colName)] = i;
}

void lp_fill_row_name_index( LinearProgram *lp )
{
    lp->rowNameIdx->clear();
    char rowName[512]="";

    for (int i = 0 ; (i < lp_rows(lp)) ; ++i)
        (*lp->rowNameIdx)[lp_row_name(lp, i, rowName)] = i;
}
#endif

#ifdef CBC
LinearProgram *lp_wrap_osisolver( OsiSolverInterface *osiLP )
{
    LinearProgram *lp = (LinearProgramPtr) calloc(sizeof(LinearProgram), 1);
    assert(lp);

    lp_initialize(lp);

    lp->justWrapOsi = 1;
    lp->osiLP = osiLP;
#ifdef NEED_OWN_INDEX
    lp_fill_col_name_index( lp );
    lp_fill_row_name_index( lp );
#endif

    return lp;
}
#endif

void lp_read(LinearProgram *lp, const char *fileName)
{
    assert(lp != NULL);


    switch (getFileType(fileName)) {
        case 'L':
            break;
        case 'M':
            break;
    }
#ifdef NEED_OWN_INDEX
    lp_fill_col_name_index( lp );
    lp_fill_row_name_index( lp );
#endif
}

void lp_write_lp(LinearProgram *lp, const char *fileName)
{
    assert(lp != NULL);
    assert( fileName != NULL );
    assert( strlen(fileName) );

    char fileType = getFileType(fileName);

    switch (fileType) {
        case 'L':
#ifdef CBC
            {
                char outFile[256];
                strcpy(outFile, fileName);
                char *s = NULL;
                if ((s = strstr(outFile, ".lp"))) {
                    if (s != outFile) // not at the start
                        *s = '\0';
                }
                lp->osiLP->writeLp(outFile);
            }
#endif

            break;
        case 'M':
#ifdef CBC
            {
                char outFile[256];
                strcpy(outFile, fileName);
                char *s = NULL;
                if ((s = strstr(outFile, ".mps"))) {
                    if (s != outFile) // not at the start
                        *s = '\0';
                }
                lp->osiLP->writeMps(outFile);
            }
#endif

            break;
    }
}

void lp_set_direction(LinearProgram *lp, const char direction)
{
    assert(lp != NULL);

    switch (direction) {
        case LP_MIN:
#ifdef CBC
            lp->osiLP->setObjSense(1.0);
#endif
            break;
        case LP_MAX:
#ifdef CBC
            lp->osiLP->setObjSense(-1.0);
#endif
            break;
        default:
            break;
    }
}

int lp_get_direction(LinearProgram *lp)
{
    assert(lp != NULL);

#ifdef CBC
    if ((fabs(lp->osiLP->getObjSense() - 1.0)) <= EPS)
        return LP_MIN;
    return LP_MAX;
#endif
}


void lp_add_cut( LinearProgram *lp, int nz, int *cutIdx, double *cutCoef, const char *name, char sense, double rhs )
{

    sense = toupper(sense);

#ifdef CBC
    OsiRowCut orCut;
    orCut.setRow( nz, cutIdx, cutCoef, false );

    double rLB = 0.0, rUB = COIN_DBL_MAX;
    switch (sense) {
        case 'E':
            rLB = rhs;
            rUB = rhs;
            break;
        case 'L':
            rLB = -COIN_DBL_MAX;
            rUB = rhs;
            break;
        case 'G':
            rLB = rhs;
            rUB = COIN_DBL_MAX;
            break;
    }
    orCut.setLb( rLB );
    orCut.setUb( rUB );

    lp->cutPool->insert( orCut );
#endif
}

void lp_add_row(LinearProgram *lp, const int nz,  int *indexes, double *coefs, const char *name, char sense, const double rhs)
{

    // checking if name was not used before
    int idxr = lp_row_index( lp, name );
    if (idxr!=-1)
        printf("lp_add_row: repeated name: %s. previous use was index %d\n", name, idxr );

    sense = toupper(sense);

    char strsense[2]; sprintf(strsense, "%c", sense);
    if (!strstr("GLE", strsense)) {
        abort();
    }

#ifdef CBC
    int currRow = lp_rows(lp);

    double rLB = 0.0, rUB = COIN_DBL_MAX;
    switch (sense) {
        case 'E':
            rLB = rhs;
            rUB = rhs;
            break;
        case 'L':
            rLB = -COIN_DBL_MAX;
            rUB = rhs;
            break;
        case 'G':
            rLB = rhs;
            rUB = COIN_DBL_MAX;
            break;
    }
    lp->osiLP->addRow(nz, indexes, coefs, rLB, rUB);
    lp->osiLP->setRowName(currRow, name);
#endif

#ifdef NEED_OWN_INDEX
    (*lp->rowNameIdx)[string(name)] = lp_rows(lp)-1;
#endif
}


void lp_add_rows( LinearProgram *lp, int nRows, int *starts, int *idx, double *coef, char *sense, double *rhs, const char **names )
{
#ifdef NEED_OWN_INDEX
    int nrbeg = lp_rows( lp );
#endif
#ifdef CBC
    double *rlb, *rub;
    rlb = new double[nRows*2];
    rub = rlb + nRows;

    for ( int i=0 ; (i<nRows) ; ++i )
    {
        switch (toupper(sense[i]))
        {
            case 'E':
                rlb[i] = rub[i] = rhs[i];
                break;
            case 'L':
                rub[i] = rhs[i];
                rlb[i] = -DBL_MAX;
                break;
            case 'G':
                rlb[i] = rhs[i];
                rub[i] = DBL_MAX;
                break;
            default:
                abort();
         }
    }

    int rt = lp_rows( lp );

    lp->osiLP->addRows( nRows, starts, idx, coef, rlb, rub );

    if (names)
        for ( int i=0 ; (i<nRows) ; ++i )
            lp->osiLP->setRowName( rt+i, string(names[i]) );

    delete[] rlb;
#endif
#ifdef NEED_OWN_INDEX
    if (names)
    {
        for ( int i=0 ; (i<nRows) ; ++i )
            (*lp->rowNameIdx)[string(names[i])] = nrbeg+i;
    }
#endif
}

void lp_add_cols(LinearProgram *lp, const int count, double *obj, double *lb, double *ub, char *integer, char **name)
{
    char warntl = false;
    for ( int i=0 ; (i<count) ; i++ )
    {
        if (obj[i]>=1e25 && (!warntl))
        {
            fflush( stdout ); fflush( stderr );
            warntl = true;
        }
    }

#ifdef CBC
    int cols = lp->osiLP->getNumCols();

    {
        vector< int > starts(count + 1, 0);
        lp->osiLP->addCols(count, &starts[0], NULL, NULL, lb, ub, obj);
    }


    if (integer) {
        for (int j = 0 ; (j < count) ; j++)
            if (integer[j])
                lp->osiLP->setInteger(cols + j);
    }

    for (int j = 0 ; (j < count) ; j++)
        lp->osiLP->setColName(cols + j, name[j]);
#endif

#ifdef NEED_OWN_INDEX
    //  updating column name index
    {
        int idxCol = lp_cols(lp) - count;
        for (int j = 0 ; (j < count) ; j++)
        {
            map< string, int >::const_iterator mIt;
            mIt = (*lp->colNameIdx).find(name[j]);
            if ( mIt != (*lp->colNameIdx).end() )
            {
                abort();
            }

            (*lp->colNameIdx)[name[j]] = idxCol++;
        }
    }
#endif
}

void lp_add_cols_same_bound(LinearProgram *lp, const int count, double *obj, double lb, double ub, char *integer, char **name)
{
    assert(lp != NULL);

    vector< double > vlb(count, lb);
    vector< double > vub(count, ub);
    lp_add_cols(lp, count, obj, &vlb[0], &vub[0], integer, name);
}

void lp_add_bin_cols( LinearProgram *lp, const int count, double *obj, char **name )
{
    vector< double > vlb(count, 0.0 );
    vector< double > vub(count, 1.0 );
    vector< char > integer( count, 1 );
    lp_add_cols( lp, count, obj, &vlb[0], &vub[0], &(integer[0]), name );
}

const double *lp_obj_coef( LinearProgram *lp )
{
    assert(lp);

#ifdef CBC
    OsiClpSolverInterface *osilp = lp->_lp;

    return osilp->getObjCoefficients();
#endif

    return NULL;
}

int lp_cols(LinearProgram *lp)
{
    assert(lp != NULL);

#ifdef CBC
    return lp->osiLP->getNumCols();
#endif
}

int lp_rows(LinearProgram *lp)
{
    assert( lp != NULL );
#ifdef CBC
    return lp->osiLP->getNumRows();
#endif
}


char lp_is_integer(LinearProgram *lp, const int j)
{
    assert( lp != NULL );

#ifdef CBC
    return lp->osiLP->isInteger(j);
#endif

}

char lp_isMIP(LinearProgram *lp)
{
    int nCols = lp_cols(lp);
    int j;

    for (j = 0 ; (j < nCols) ; j++)
        if (lp_is_integer(lp, j))
            return 1;

    return 0;
}

int lp_optimize_as_continuous(LinearProgram *lp)
{
    assert(lp != NULL);

    lp->optAsContinuous = 1;
    int status = lp_optimize(lp);
    lp->optAsContinuous = 0;

    return status;
}

int lp_optimize(LinearProgram *lp)
{
    assert(lp != NULL);

    lp->solutionTime = 0.0;

    time_t startT; time(&startT);

    // if needs to read mipstart
    if (strlen(lp->solInFN))
        lp_read_mip_start( lp, lp->solInFN );

    // if mipstarted informed (in file
    // or directly, checking and translating to 
    // indexes)
    lp_check_mipstart( lp );

    int isMIP = 0;

    if (!lp->optAsContinuous)
        isMIP = lp_isMIP(lp);

    lp->_x->resize(lp_cols(lp));
    lp->_rc->resize(lp_cols(lp));
    lp->_obj->resize(lp_cols(lp));
    lp->_pi->resize(lp_rows(lp));
    lp->_slack->resize(lp_rows(lp));
    lp->_savedSol->clear();
    lp->_savedObj->clear();
    lp->obj = DBL_MAX;
    lp->bestBound = DBL_MAX;
    lp->status = LP_ERROR;

    fill(lp->_x->begin(), lp->_x->end(), DBL_MAX);
    fill(lp->_rc->begin(), lp->_rc->end(), DBL_MAX);
    fill(lp->_obj->begin(), lp->_obj->end(), DBL_MAX);
    fill(lp->_pi->begin(), lp->_pi->end(), DBL_MAX);
    fill(lp->_slack->begin(), lp->_slack->end(), DBL_MAX);

    lp->nOptimizations++;

    /* error handling */
    char errorMsg[512] = "";
    int errorLine = -1;

    /* check if problem will be transformed in all integer */
    if (lp->allInteger)
    {
        int cInt, cBin, cCont;
        lp_cols_by_type( lp, &cBin, &cInt, &cCont );
        if (cBin+cInt < lp_cols(lp))
        {
            vector< int > idx;
            for ( int i=0 ; (i<lp_cols(lp)) ; ++i )
                if (!lp_is_integer(lp,i))
                    idx.push_back(i);

            lp_set_integer( lp, idx.size(), &idx[0] );
        }
    } /* transforming into pure IP */

#ifdef CBC
    bool deleteLP = false;
    OsiSolverInterface *linearProgram = NULL;

    {
        lp->status = LP_ERROR;

        if ( lp->nOptimizations == 1 )
            lp->_lp->getModelPtr()->setPerturbation(50);

        if (lp_isMIP(lp)) {
            linearProgram = lp->osiLP->clone();
            deleteLP = true;
        }
        else
            linearProgram = lp->osiLP;


        if ( lp->maxSeconds != INT_NOT_SET )
        {
            ClpSimplex *clp = lp->_lp->getModelPtr();
            clp->setMaximumSeconds( lp->maxSeconds ); 
        }

        //if (lp_isMIP(lp)) {
        //    linearProgram->initialSolve();
        //} else {
        //    if (lp->nOptimizations >= 2)
        //        linearProgram->resolve();
        //    else
        //    {
        //        /* solving initial lp relaxation */
        //        linearProgram->initialSolve();
        //    }
        //}

        /*if (linearProgram->isAbandoned()) {
            sprintf(errorMsg, "Numerical difficulties, linear program abandoned.\n");
            errorLine = __LINE__;
            goto CBC_OPTIMIZATION_ERROR;
        }
        if ((linearProgram->isProvenPrimalInfeasible()) || (linearProgram->isProvenDualInfeasible())) {
            lp->status = LP_INFEASIBLE;
            goto CBC_OPTIMIZATION_CONCLUDED;
        }
        if (linearProgram->isIterationLimitReached()) {
            sprintf(errorMsg, "Iteration limit for linear program reached, abandoning.\n");
            errorLine = __LINE__;
            goto CBC_OPTIMIZATION_ERROR;
        }
        if (linearProgram->isPrimalObjectiveLimitReached()) {
            sprintf(errorMsg, "Primal objective limit reached, abandoning.\n");
            errorLine = __LINE__;
            goto CBC_OPTIMIZATION_ERROR;
        }
        if (linearProgram->isDualObjectiveLimitReached()) {
            sprintf(errorMsg, "Dual objective limit reached, abandoning.\n");
            errorLine = __LINE__;
            goto CBC_OPTIMIZATION_ERROR;
        }

        if ((!isMIP) && (linearProgram->isProvenOptimal())) {
            memcpy(&((*(lp->_x))[0]) , linearProgram->getColSolution(), sizeof(double)*lp_cols(lp));
            memcpy(&((*(lp->_pi))[0]), linearProgram->getRowPrice(), sizeof(double)*lp_rows(lp));
            memcpy(&((*(lp->_rc))[0]), linearProgram->getReducedCost(), sizeof(double)*lp_cols(lp));
            for ( int i=0 ; (i<lp_rows(lp)) ; ++i )
            {
                double activity = lp->osiLP->getRowActivity()[i];
                double lower = lp->osiLP->getRowLower()[i];
                double upper = lp->osiLP->getRowUpper()[i];

                (*lp->_slack)[i] = std::min( upper-activity, activity-lower );
            }

            lp->obj = linearProgram->getObjValue();

            lp->status = LP_OPTIMAL;
            goto CBC_OPTIMIZATION_CONCLUDED;
        }*/

        if (isMIP) {
            // Pass to Cbc initialize defaults
            CbcModel modelA(*linearProgram);
            if (lp->msVars>0)
            {
                assert( lp->msVal!=NULL );
                assert( lp->msNames!=NULL );
                modelA.setMIPStart( lp->msVars, (const char**)lp->msNames, lp->msVal );
            }

            CglCallback *cglCB = NULL;
            if ( lp->callback_ != NULL )
            {
                cglCB = new CglCallback();
                cglCB->callback_ = lp->callback_;
                cglCB->lp = lp;
                cglCB->data = lp->data_;
                cglCB->model = &modelA;
                modelA.addCutGenerator( cglCB, -1, "Callback" );
            }

            CbcModel *model = &modelA;
            {
                if (lp->_priorities->size())
                {
                    vector<int> pri( *(lp->_priorities) );
                    int imin = INT_MAX;
                    int imax = -INT_MAX;
                    for ( int i=0 ; (i<(int)pri.size()) ; ++i )
                    {
                        pri[i] = std::min( pri[i], imin );
                        pri[i] = std::max( pri[i], imax );
                    }

                    int shift = 0;
                    if (imin<1)
                        shift = 1-imin;
                    for ( int i=0 ; (i<(int)pri.size()) ; ++i )
                        pri[i] = shift + imax-pri[i];

                    model->passInPriorities( &(pri[0]), false );
                }

                // filling options and calling solver
#define STR_OPT_SIZE 256
                vector<string> cbcP;
                char **cbcOptStr = NULL;
                CbcMain0(modelA);
                lp_config_cbc_params(lp, cbcP);
                cbcOptStr = (char **) malloc(sizeof(char *)*cbcP.size()); assert(cbcOptStr);
                cbcOptStr[0] = (char *)malloc(sizeof(char) * cbcP.size() * STR_OPT_SIZE); assert(cbcOptStr[0]);
                for (int i = 1 ; (i < (int)cbcP.size()) ; i++) cbcOptStr[i] = cbcOptStr[i - 1] + STR_OPT_SIZE;
                for (int i = 0 ; (i < (int)cbcP.size()) ; i++) strncpy(cbcOptStr[i], cbcP[i].c_str(), STR_OPT_SIZE);

                //                printf("calling CBC with options: %s %d\n", (const char **)cbcOptStr, cbcP.size() );

                CbcMain1(cbcP.size(), (const char **)cbcOptStr, modelA);

                if (cglCB)
                    delete cglCB;
#undef STR_OPT_SIZE
                free(cbcOptStr[0]); free(cbcOptStr); cbcOptStr = NULL;
            }

            lp->status = LP_NO_SOL_FOUND;

            if (model->isAbandoned()) {
                sprintf(errorMsg, "Model isAbandoned()\n");
                errorLine = __LINE__;
                goto CBC_OPTIMIZATION_ERROR;
            }
            if ((model->isProvenInfeasible()) || (model->isProvenDualInfeasible())) {
                lp->status = LP_INTINFEASIBLE;
                goto CBC_OPTIMIZATION_CONCLUDED;
            }

            if (model->bestSolution())
                lp->status = LP_FEASIBLE;
            if (model->isProvenOptimal())
                lp->status = LP_OPTIMAL;

            if (model->bestSolution()) {
                memcpy(&((*(lp->_x))[0]), model->solver()->getColSolution(), sizeof(double)*lp_cols(lp));
                for ( int i=0 ; (i<lp_rows(lp)) ; ++i )
                {
                    double activity = model->getCbcRowActivity()[i];
                    double lower = model->getCbcRowLower()[i];
                    double upper = model->getCbcRowUpper()[i];
                    (*lp->_slack)[i] = std::min( upper-activity, activity-lower );
                }


                for (int i = 0; (i < model->numberSavedSolutions()) ; i++) {
                    const double *si = model->savedSolution(i);
                    vector< double > ti;
                    ti.clear();
                    ti.insert(ti.end(), si, si + lp_cols(lp));

                    lp->_savedSol->push_back(ti);
                    lp->_savedObj->push_back(model->savedSolutionObjective(i));
                } // saved solution
            } // best solution

            lp->obj = model->getObjValue();
        }
    }
CBC_OPTIMIZATION_CONCLUDED:
    if (deleteLP) {
        assert(linearProgram);
        delete linearProgram;
    }

    goto OPTIMIZATION_CONCLUDED;
CBC_OPTIMIZATION_ERROR:
    if (deleteLP) {
        assert(linearProgram);
        delete linearProgram;
    }

    goto OPTIMIZATION_ERROR;
#endif
OPTIMIZATION_CONCLUDED:

    if ( (isMIP) && (lp->status == LP_OPTIMAL) )
        lp->bestBound = lp->obj;

    time_t endT; time(&endT);

    lp->solutionTime = difftime( endT, startT );
    return lp->status;

OPTIMIZATION_ERROR:
    lp_write_lp(lp, "error.lp");
    abort();
}

double lp_obj_value(LinearProgram *lp)
{
    assert(lp != NULL);
    if (lp->nOptimizations == 0) {
        abort();
    }

    return lp->obj;
}

double *lp_row_price(LinearProgram *lp)
{
    assert(lp != NULL);

    if (lp->nOptimizations == 0) {
        abort();
    }

    if (lp->status != LP_OPTIMAL) {
        abort();
    }

    return &((*(lp->_pi))[0]);
}

double *lp_row_slack( LinearProgram *lp )
{
    assert(lp != NULL);

    if (lp->nOptimizations == 0) {
        abort();
    }

    if (lp->status != LP_OPTIMAL && lp->status!=LP_FEASIBLE) {
        abort();
    }

    return &((*(lp->_slack))[0]);
}

double *lp_x(LinearProgram *lp)
{
    assert(lp != NULL);

    if ((lp->status != LP_OPTIMAL) && (lp->status != LP_FEASIBLE)) {
        abort();
    }

    if (lp->nOptimizations == 0) {
        abort();
    }

    return &((*(lp->_x))[0]);
}

int lp_get_mip_emphasis(LinearProgram *lp)
{
    assert(lp != NULL);

    return lp->mipEmphasis;
}

void lp_set_mip_emphasis(LinearProgram *lp, const int mipEmphasis)
{
    assert(lp != NULL);

    lp->mipEmphasis = mipEmphasis;
}

void lp_printRootRelaxInfo(LinearProgram *lp)
{
    assert(lp != NULL);

    double obj = lp_obj_value(lp);
    printf("Root node linear relaxation info:\n");
    printf("\tObjective value: %g\n", obj);
    fflush(stdout);
}

#ifdef CBC
/* cut generation related includes */
#include <CglKnapsackCover.hpp>
#include <CglFlowCover.hpp>
//#include <CglZeroHalf.hpp>
#include <CglMixedIntegerRounding.hpp>
#include <CglTwomir.hpp>
#include <CglLandP.hpp>
#include <CglRedSplit.hpp>
#include <CglGMI.hpp>

int lp_strengthen_with_cuts( LinearProgram *lp, const int maxRoundsCuts[] )
{
    OsiClpSolverInterface *osiLP = lp->_lp;
    int round = 1;
    int totalCuts = 0;
    assert( maxRoundsCuts );

    printf("optimizations %d obj %g\n", lp->nOptimizations, lp_obj_value(lp) );
#ifdef CBC
CUTGEN:
    //int origRows = lp_rows( lp );
    int newCuts = 0;
    char message[256] = "";

    {
        if (!osiLP->optimalBasisIsAvailable())
            osiLP->initialSolve();

        OsiCuts cuts;

        if (round<=maxRoundsCuts[LPC_FLOW])
        {
            int oc = cuts.sizeCuts();
            CglFlowCover flowCoverCuts;
            flowCoverCuts.generateCuts( *osiLP, cuts );
            if (cuts.sizeCuts()>oc)
            {
                char str[64];
                sprintf( str, "(%d)FlowCover ", cuts.sizeCuts()-oc );
                strcat( message, str );
            }
        }

        /*if (round<=maxRoundsCuts[LPC_ZERO_HALF])
        {
            int oc = cuts.sizeCuts();
            CglZeroHalf zhCuts;
            zhCuts.generateCuts( *osiLP, cuts );
            if (cuts.sizeCuts()>oc)
            {
                char str[64];
                sprintf( str, "(%d)ZeroHalf ", cuts.sizeCuts()-oc );
                strcat( message, str );
            }
        }*/

        if (round<=maxRoundsCuts[LPC_MIR])
        {
            int oc = cuts.sizeCuts();
            CglMixedIntegerRounding mirCuts;
            mirCuts.generateCuts( *osiLP, cuts );
            if (cuts.sizeCuts()>oc)
            {
                char str[64];
                sprintf( str, "(%d)MIR ", cuts.sizeCuts()-oc );
                strcat( message, str );
            }
        }

        if (round<=maxRoundsCuts[LPC_GOMORY])
        {
            int oc = cuts.sizeCuts();
            CglGMI gomoryCuts;
            gomoryCuts.generateCuts( *osiLP, cuts );
            if (cuts.sizeCuts()>oc)
            {
                char str[64];
                sprintf( str, "(%d)Gomory ", cuts.sizeCuts()-oc );
                strcat( message, str );
            }
        }

        if (round<=maxRoundsCuts[LPC_KNAPSACK])
        {
            int oc = cuts.sizeCuts();
            CglKnapsackCover coverCuts;
            coverCuts.generateCuts( *osiLP, cuts );
            if (cuts.sizeCuts()>oc)
            {
                char str[64];
                sprintf( str, "(%d)Knapsack ", cuts.sizeCuts()-oc );
                strcat( message, str );
            }
        }

        if (round<=maxRoundsCuts[LPC_TWO_MIR])
        {
            int oc = cuts.sizeCuts();
            CglTwomir twoMirCuts;
            twoMirCuts.generateCuts( *osiLP, cuts );
            if (cuts.sizeCuts()>oc)
            {
                char str[64];
                sprintf( str, "(%d)TwoMIR ", cuts.sizeCuts()-oc );
                strcat( message, str );
            }
        }

        if (round<=maxRoundsCuts[LPC_L_AND_P])
        {
            int oc = cuts.sizeCuts();
            CglLandP landPCuts;
            landPCuts.generateCuts( *osiLP, cuts );
            if (cuts.sizeCuts()>oc)
            {
                char str[64];
                sprintf( str, "(%d)LiftAndProject ", cuts.sizeCuts()-oc );
                strcat( message, str );
            }
        }

        if (round<=maxRoundsCuts[LPC_REDUCE])
        {
            int oc = cuts.sizeCuts();
            CglRedSplit reduceCuts;
            reduceCuts.generateCuts( *osiLP, cuts );
            if (cuts.sizeCuts()>oc)
            {
                char str[64];
                sprintf( str, "(%d)ReduceAndSplit ", cuts.sizeCuts()-oc );
                strcat( message, str );
            }
        }

        newCuts = cuts.sizeCuts();
        osiLP->applyCuts( cuts );
        //assert( newCuts == lp_rows(lp)-origRows );

#ifdef NEED_OWN_INDEX
        {
            char rowName[256];
            for ( int ii=0 ; (ii<newCuts) ; ++ii )
                (*lp->rowNameIdx)[lp_row_name(lp, lp_rows(lp)-ii, rowName)] = lp_rows(lp)-ii;
        }
#endif

    }


    if (newCuts)
    {
        if (!lp->silent)
            printf( "%d new cuts [%s] inserted in formulation.\n", newCuts, message );
        totalCuts += newCuts;
        osiLP->resolve();
        if (!lp->silent)
            printf( "objective value is now %g\n\n", lp_obj_value(lp) );
        ++round;
        goto CUTGEN;
    }
    else
    {
        if (!lp->silent)
            printf( "no violated cuts found.\n" );
    }

    return totalCuts;
#endif
}

void lp_set_callback( LinearProgram *lp, lp_cb callback, void *data )
{
    lp->callback_ = callback;
    lp->data_ = data;
}
#endif // CBC

void lp_free(LinearProgramPtr *lp)
{
    assert(lp != NULL);
    assert(*lp != NULL);

#ifdef CBC
    if ((*lp)->justWrapOsi == 0) {
        if ((*lp)->cglPP == NULL) {
            delete (*lp)->_lp;
            (*lp)->osiLP = NULL;
        }
        else {
            delete (*lp)->cglPP;
            (*lp)->_lp = NULL;
            (*lp)->osiLP = NULL;
        }
    }

    if ( ((*lp)->cutPool)&&((*lp)->ownCutPool) )
        delete ((*lp)->cutPool);
#endif
    delete (*lp)->_x;
    delete (*lp)->_rc;
    delete (*lp)->_obj;
    delete (*lp)->_idx;
    delete (*lp)->_coef;
    delete (*lp)->_pi;
    delete (*lp)->_slack;
    delete (*lp)->_priorities;
    delete (*lp)->_savedSol;
    delete (*lp)->_savedObj;
#ifdef NEED_OWN_INDEX
    delete (*lp)->colNameIdx;
    delete (*lp)->rowNameIdx;
#endif
    delete (*lp)->_orig;

    if ((*lp)->msNames)
    {
        delete[] (*lp)->msNames[0];
        delete[] (*lp)->msNames; 
    }
    if ((*lp)->msIdx)
        delete[] (*lp)->msIdx;
    if ((*lp)->msVal)
        delete[] (*lp)->msVal;


    free(*lp);
    *lp = NULL;
}

int lp_col( LinearProgram *lp, int col, int *idx, double *coef )
{
    int result = -INT_MAX;

#ifdef CBC
    const CoinPackedMatrix *cpmCol =  lp->osiLP->getMatrixByCol();
    const int nzCol = cpmCol->getVectorLengths()[col];
    const CoinBigIndex *starts = cpmCol->getVectorStarts();
    const int *ridx = cpmCol->getIndices() + starts[col];
    const double *rcoef = cpmCol->getElements() + starts[col];

    for (int j = 0 ; (j < nzCol) ; ++j) {
        idx[j] = ridx[j];
        coef[j] = rcoef[j];
    }

    result = nzCol;
#endif

    return result;
}

int lp_row(LinearProgram *lp, int row, int *idx, double *coef)
{
    int result = -INT_MAX;

#ifdef CBC
    const CoinPackedMatrix *cpmRow =  lp->osiLP->getMatrixByRow();
    const int nzRow = cpmRow->getVectorLengths()[row];
    const CoinBigIndex *starts = cpmRow->getVectorStarts();
    const int *ridx = cpmRow->getIndices() + starts[row];
    const double *rcoef = cpmRow->getElements() + starts[row];
    for (int j = 0 ; (j < nzRow) ; ++j) {
        idx[j] = ridx[j];
        coef[j] = rcoef[j];
    }

    result = nzRow;
#endif
    return result;
}

double lp_rhs(LinearProgram *lp, int row)
{
    return lp->osiLP->getRightHandSide()[row];
}

char lp_sense(LinearProgram *lp, int row)
{
    return lp->osiLP->getRowSense()[row];
}

char *lp_row_name(LinearProgram *lp, int row, char *dest)
{
    strcpy(dest, lp->osiLP->getRowName(row).c_str());
    return dest;
}

char *lp_col_name(LinearProgram *lp, int col, char *dest)
{
    strcpy(dest, lp->osiLP->getColName(col).c_str());
    return dest;
}

double lp_col_lb(LinearProgram *lp, int col)
{
    return lp->osiLP->getColLower()[col];
}

double lp_col_ub(LinearProgram *lp, int col)
{
    return lp->osiLP->getColUpper()[col];
}

void lp_set_obj(LinearProgram *lp, double *obj)
{
    assert(lp != NULL);

#ifdef CBC
    return lp->osiLP->setObjective(obj);
#endif
}

void lp_add_col(LinearProgram *lp, double obj, double lb, double ub, char integer, char *name, int nz, int *rowIdx, double *rowCoef)
{
    assert(lp != NULL);

#ifdef CBC
    int starts[] = { 0, nz };
    lp->osiLP->addCols(1, starts, rowIdx, rowCoef, &lb, &ub, &obj);
    if (integer)
        lp->osiLP->setInteger(lp_cols(lp) - 1);
    lp->osiLP->setColName(lp_cols(lp) - 1, name);
#endif

#ifdef NEED_OWN_INDEX
    int idxCol = lp_cols(lp)-1;
    map< string, int > &mNames = (*lp->colNameIdx);
    if ( mNames.find( name ) != mNames.end() )
    {
        abort();
    }
    mNames[name] = idxCol;
#endif
}

void lp_set_rhs(LinearProgram *lp, int row, double rhs)
{
    assert(lp != NULL);

#ifdef CBC
    char sense = lp_sense(lp, row);
    switch (sense) {
        case 'E':
            lp->osiLP->setRowBounds(row, rhs, rhs);
            break;
        case 'G':
            lp->osiLP->setRowBounds(row, rhs, COIN_DBL_MAX);
            break;
        case 'L':
            lp->osiLP->setRowBounds(row, -COIN_DBL_MAX, rhs);
            break;
        default:
            abort();
            exit(1);
    }
#endif
}

double lp_solution_time(LinearProgram *lp)
{
    assert(lp != NULL);

    return lp->solutionTime;
}

void lp_set_cuts(LinearProgram *lp, char onOff)
{
    assert(lp != NULL);
    lp->cuts = onOff;
}

void lp_set_max_seconds(LinearProgram *lp, int _max)
{
    assert(lp != NULL);
    lp->maxSeconds = _max;
}

void lp_set_max_solutions(LinearProgram *lp, int _max)
{
    assert(lp != NULL);
    lp->maxSolutions = _max;
}


int lp_num_saved_sols( LinearProgram *lp )
{
    assert(lp != NULL);
    return (int)lp->_savedSol->size();

}

void lp_set_max_saved_sols(LinearProgram *lp, int _max)
{
    assert(lp != NULL);
    lp->maxSavedSols = _max;
}

void lp_set_max_nodes(LinearProgram *lp, int _max)
{
    assert(lp != NULL);
    lp->maxNodes = _max;
}

void lp_set_print_messages(LinearProgram *lp, char onOff)
{
    assert(lp != NULL);
    lp->printMessages = onOff;
}

void lp_set_parallel(LinearProgram *lp, char onOff)
{
    assert(lp != NULL);
    lp->parallel = onOff;
}

void lp_set_heur_proximity(LinearProgram *lp, char onOff)
{
    assert(lp != NULL);
    lp->heurProx = onOff;
}

void lp_set_heur_fp_passes(LinearProgram *lp, int passes)
{
    assert(lp != NULL);

    lp->heurFPPasses = passes;
}

#ifdef CBC
void lp_config_cbc_params(LinearProgram *lp, vector<string> &cbcP)
{
    assert(lp != NULL);

    cbcP.push_back("someMIP"); // problem name
    if (lp->cuts != INT_NOT_SET) {
        if (lp->cuts)
        {
            cbcP.push_back("-cuts");
            cbcP.push_back("on");
        }
        else
        {
            cbcP.push_back("-cuts");
            cbcP.push_back("off");
        }
    }
    if (lp->printMessages != INT_NOT_SET) {
        if (lp->printMessages)
        {
            cbcP.push_back("-log");
            cbcP.push_back("1");
        }
        else
        {
            cbcP.push_back("-log");
            cbcP.push_back("0");
        }
    }
    /*
       cbcP.push_back("-zero");
       cbcP.push_back("ifmove");

       cbcP.push_back("-multiple");
       cbcP.push_back("2");

       cbcP.push_back("-diveopt");
       cbcP.push_back("7");

       cbcP.push_back("-lagomory");
       cbcP.push_back("endonly");

       cbcP.push_back("-latwomir");
       cbcP.push_back("endonly"); */

    if (lp->cutoff != DBL_MAX)
    {
        cbcP.push_back("-cutoff");
        cbcP.push_back(SSTR(lp->cutoff));
        if (lp->cutoffAsConstraint)
        {
            cbcP.push_back( "-constraintfromCutoff" );
            cbcP.push_back( "on" );
        }
    }

    if ( lp->parallel != INT_NOT_SET )
    {
        if ( lp->parallel )
        {
#ifdef _OPENMP
            int nthreads = omp_get_num_procs();
#else
            int nthreads = 4;
#endif
#ifdef CBC
            if (nthreads>4)
                nthreads = 4; // to avoid excessive memory use
#endif
            if (lp->printMessages!=0)
                printf("CBC will use %d threads.\n", nthreads );
            cbcP.push_back("-threads");
            cbcP.push_back(SSTR(nthreads));
        }
        else
        {
            cbcP.push_back( "-threads" );
            cbcP.push_back( "0" );
        }
    }

    if (lp->maxSeconds != INT_NOT_SET)
    {
        cbcP.push_back("-timeM");
        cbcP.push_back("elapsed");
        cbcP.push_back("-seconds");
        cbcP.push_back(SSTR(lp->maxSeconds));
    }
    if (lp->maxSolutions != INT_NOT_SET)
    {
        cbcP.push_back("-maxSol");
        cbcP.push_back(SSTR(lp->maxSolutions));
    }
    if (lp->maxNodes != INT_NOT_SET)
    {
        cbcP.push_back("-maxNodes");
        cbcP.push_back(SSTR(lp->maxNodes));
    }
    if (lp->heurFPPasses  != INT_NOT_SET)
    {
        cbcP.push_back("-passF");
        cbcP.push_back(SSTR(lp->heurFPPasses));
    }
    if (lp->heurProx != INT_NOT_SET) {
        if (lp->heurProx)
        {
            cbcP.push_back("-proximity");
            cbcP.push_back("on");
        }
        else
        {
            cbcP.push_back("-proximity");
            cbcP.push_back("off");
        }
    }
    if (lp->maxSavedSols != INT_NOT_SET)
    {
        cbcP.push_back("-maxSaved");
        cbcP.push_back(SSTR(lp->maxSavedSols));
    }

    if (strlen(lp->solInFN))
    {
        cbcP.push_back("-mips");
        cbcP.push_back(lp->solInFN);
    }

    if (lp->absMIPGap!=DBL_MAX)
    {
        cbcP.push_back("-allowableGap");
        cbcP.push_back( SSTR(lp->absMIPGap) );
    }
    if (lp->relMIPGap!=DBL_MAX)
    {
        cbcP.push_back("-ratioGap");
        cbcP.push_back(SSTR(lp->relMIPGap));
    }
    if ( lp->mipPreProcess != CHAR_MAX )
    {
        if (!lp->mipPreProcess)
        {
            cbcP.push_back("-preprocess");
            cbcP.push_back("off");
        }
    }

    cbcP.push_back("-solve");
    cbcP.push_back("-quit");
}
#endif

void lp_set_col_bounds(LinearProgram *lp, int col, const double lb, const double ub)
{

    double l = lb;
    double u = ub;
    if ( lp_is_integer(lp,col) )
    {
        if (( l!=-DBL_MAX ) && (l!=DBL_MIN))
            l = floor(lb + 0.5);
        if ( u!=DBL_MAX )
            u = floor(ub + 0.5);
    }

#ifdef CBC
    OsiSolverInterface *linearProgram = lp->osiLP;
    linearProgram->setColBounds(col, l, u);
#endif
}

double lp_saved_sol_obj(LinearProgram *lp, int isol)
{
    assert(lp != NULL);

    assert(isol >= 0);
    assert(isol < (int)lp->_savedObj->size());
    return lp->_savedObj->at(isol);
}

double *lp_saved_sol_x(LinearProgram *lp, int isol)
{
    assert(lp != NULL);

    assert(isol >= 0);
    assert(isol < (int)lp->_savedSol->size());
    return &(lp->_savedSol->at(isol)[0]);
}

LinearProgram *lp_clone(LinearProgram *lp)
{
    assert(lp != NULL);

    LinearProgram *result = lp_create_from( lp );

    result->optAsContinuous = lp->optAsContinuous;
    result->allInteger = lp->allInteger;
    result->nOptimizations = lp->nOptimizations;

    result->obj = lp->obj;
    result->bestBound = lp->bestBound;
    result->status = lp->status;
    result->solutionTime = lp->solutionTime;

    result->cutoff = lp->cutoff;
    result->cutoffAsConstraint = lp->cutoffAsConstraint;


    result->callback_ = lp->callback_;
    result->data_ = lp->data_;

    result->mipEmphasis = lp->mipEmphasis;
    result->mipPreProcess = lp->mipPreProcess;
    result->heurFPPasses = lp->heurFPPasses;
    result->heurProx = lp->heurProx;
    result->maxNodes = lp->maxNodes;
    result->cuts = lp->cuts;
    result->printMessages = lp->printMessages;
    result->maxSolutions = lp->maxSolutions;
    result->parallel = lp->parallel;
    result->absMIPGap = lp->absMIPGap;
    result->relMIPGap = lp->relMIPGap;
    result->maxSeconds = lp->maxSeconds;
    result->maxSavedSols = lp->maxSavedSols;
    result->branchDir = lp->branchDir;
    result->silent = lp->silent;

    (*result->_x)         = (*lp->_x);
    (*result->_pi)        = (*lp->_pi);
    (*result->_slack)     = (*lp->_slack);
    (*result->_rc)        = (*lp->_rc);
    (*result->_obj)       = (*lp->_obj);
    (*result->_savedSol)  = (*lp->_savedSol);
    (*result->_savedObj)  = (*lp->_savedObj);
#ifdef NEED_OWN_INDEX
    (*result->colNameIdx) = (*lp->colNameIdx);
    (*result->rowNameIdx) = (*lp->rowNameIdx);
#endif
    (*result->_orig)      = (*lp->_orig);
 
    strcpy(result->solOutFN, lp->solOutFN );
    strcpy(result->solInFN, lp->solInFN );

    if (lp->msVars == 0)
    {
        result->msVars = 0;
        result->msNames = NULL;
        result->msVal = NULL;
    }
    else
    {
        result->msVars = lp->msVars;

        if (lp->msIdx)
        {
            result->msIdx = new int[lp->msVars];
            memcpy( result->msIdx, lp->msIdx, sizeof(int)*lp->msVars );
        }
        if (lp->msVal)
        {
            result->msVal = new double[lp->msVars];
            memcpy( result->msVal, lp->msVal, sizeof(double)*lp->msVars );
        }
        if (lp->msNames)
        {
            result->msNames = new char*[lp->msVars+1];
            int totalStrSize = 0;
            for ( int i=0 ; (i<lp->msVars) ; ++i )
                totalStrSize += strlen(lp->msNames[i])+1;

            result->msNames[0] = new char[totalStrSize];
            for ( int i=0 ; (i<lp->msVars) ; ++i )
            {
                strcpy( result->msNames[i], lp->msNames[i] );
                result->msNames[i+1] = result->msNames[i]+strlen(result->msNames[i])+1;
            }
        }
    }
    return result;
}

void lp_fix_col(LinearProgram *lp, int col, double val)
{
    if (lp_is_integer(lp, col))
        val = floor(val + 0.5);
#ifdef CBC
    lp->osiLP->setColBounds(col, val, val);
#endif


}

LinearProgram *lp_pre_process(LinearProgram *lp)
{
#ifdef CBC
    LinearProgram *result = (LinearProgramPtr) malloc(sizeof(LinearProgram));

    lp_initialize(result);

    result->cglPP = new CglPreProcess();
    result->_lp = dynamic_cast<OsiClpSolverInterface *>(result->cglPP->preProcess(*(lp->_lp), false, 4));
    result->osiLP = dynamic_cast<OsiSolverInterface *>(result->_lp);
    result->_lp->setIntParam(OsiNameDiscipline, 1);
    result->_lp->messageHandler()->setLogLevel(0);
    result->_orig->resize( lp_cols(result), INT_MAX );
    memcpy( &((*(result->_orig))[0]), (result->cglPP->originalColumns()), sizeof(int)*lp_cols(result) );

    return result;
#else
    abort();
#endif
}

void lp_initialize(LinearProgram *lp)
{
    assert(lp != NULL);

    lp->_x = new vector< double >();
    lp->_rc = new vector< double >();
    lp->_obj = new vector< double >();
    lp->_coef = new vector< double >();
    lp->_idx = new vector< int >();
    lp->_pi = new vector< double >();
    lp->_slack =  new vector< double >();
    lp->_priorities = new std::vector<int>();
    lp->_savedSol = new vector< vector<double> >();
    lp->_savedObj = new vector<double>();
#ifdef NEED_OWN_INDEX
    lp->colNameIdx = new map< string, int >();
    lp->rowNameIdx = new map< string, int >();
#endif
    lp->_orig = new vector< int >();
    lp->callback_ = NULL;
    lp->data_ = NULL;
    lp->cutoff = DBL_MAX;
    lp->cutoffAsConstraint = 0;
    lp->branchDir = INT_NOT_SET;

    lp->msNames = NULL;
    lp->msIdx = NULL;
    lp->msVal = NULL;
    lp->msVars = 0;

#ifdef CBC
    lp->cutPool = NULL;
    lp->ownCutPool = 0;
    lp->justWrapOsi = 0;
#endif

    lp->optAsContinuous = 0;
    lp->mipPreProcess = CHAR_MAX;
    lp->nOptimizations = 0;
    lp->silent = 0;
    lp->solutionTime = 0.0;
    lp->obj = DBL_MAX;
    lp->status = LP_ERROR;
    lp->absMIPGap = DBL_MAX;
    lp->relMIPGap = DBL_MAX;

    strcpy(lp->solOutFN, "");
    strcpy(lp->solInFN, "");

    /* parameters */
    lp->maxSeconds    = INT_NOT_SET;
    lp->maxSavedSols  = INT_NOT_SET;
    lp->heurFPPasses  = INT_NOT_SET;
    lp->heurProx      = INT_NOT_SET;
    lp->maxNodes      = INT_NOT_SET;
    lp->cuts          = INT_NOT_SET;
    lp->printMessages = INT_NOT_SET;
    lp->maxSolutions  = INT_NOT_SET;
    lp->mipEmphasis   = LP_ME_DEFAULT;
    lp->parallel      = INT_NOT_SET;

}

int lp_col_index(LinearProgram *lp, const char *name)
{
    assert(lp != NULL);

#ifdef NEED_OWN_INDEX
    map< string, int >::const_iterator mIt;
    mIt = lp->colNameIdx->find(string(name));
    if (mIt == lp->colNameIdx->end())
        return -1;

    return mIt->second;
#endif
}

int lp_row_index(LinearProgram *lp, const char *name)
{
    assert(lp != NULL);

#ifdef NEED_OWN_INDEX
    map< string, int >::const_iterator mIt;
    mIt = lp->rowNameIdx->find(string(name));
    if (mIt == lp->rowNameIdx->end())
        return -1;

    return mIt->second;
#else
#endif
}

void lp_parse_options(LinearProgram *lp, int argc, const char **argv)
{
    for (int i = 0 ; (i < argc) ; ++i) {
        if (argv[i][0] != '-')
            continue;

        char optLower[256];
        strncpy(optLower, argv[i], 256);
        int len = strlen(optLower);
        for (int j = 0 ; (j < len) ; ++j)
            optLower[j] = tolower(optLower[j]);

        if (strstr(optLower, "allinteger")) {
            lp->allInteger = 1;
            printf("solving as a pure integer program\n");
            continue;
        }
        if (strstr(optLower, "nomip")) {
            lp->optAsContinuous = 1;
            printf( "solving only root node relaxation.\n" );
            continue;
        }
        if (strstr(optLower, "maxsec")) {
            if (i + 1 == argc) {
                fprintf(stderr, "enter number of seconds.\n");
                exit(EXIT_FAILURE);
            }

            int sec = atoi(argv[i + 1]);

            printf("> setting max seconds to %d\n", sec);

            lp_set_max_seconds(lp, sec);
            continue;
        }
        if (strstr(optLower, "maxnodes")) {
            if (i + 1 == argc) {
                fprintf(stderr, "enter number of nodes.\n");
                exit(EXIT_FAILURE);
            }

            int nodes = atoi(argv[i + 1]);

            printf("> setting max nodes to %d\n", nodes);

            lp_set_max_nodes(lp, nodes);
            continue;
        }

        if (strstr(optLower, "mipemphasis")) {
            if (i + 1 == argc) {
                fprintf(stderr, "enter MIP emphasis.\n");
                exit(EXIT_FAILURE);
            }

            if ( strcmp(argv[i + 1], "optimality" )==0 )
            {
                lp_set_mip_emphasis( lp, LP_ME_OPTIMALITY );
                printf("MIP emphasis set to optimality.\n");
                continue;
            }
            if ( strcmp(argv[i + 1], "feasibility" )==0 )
            {
                lp_set_mip_emphasis( lp, LP_ME_FEASIBILITY );
                printf("MIP emphasis set to feasibility.\n");
                continue;
            }

            fprintf( stderr, "MIP emphasis not valid: %s. Valid values are: {optimality,feasibility}. ", argv[i+1]);
            exit(EXIT_FAILURE);
        }
        if (strstr(optLower, "maxsol")) {
            if (i + 1 == argc) {
                fprintf(stderr, "enter number of solutions.\n");
                exit(EXIT_FAILURE);
            }

            int sol = atoi(argv[i + 1]);

            printf("> setting max solutions to %d\n", sol);

            lp_set_max_solutions(lp, sol);
            continue;
        }
        if (strstr(optLower, "absgap")) {
            if (i + 1 == argc) {
                fprintf(stderr, "enter the allowed absolute MIP gap.\n");
                exit(EXIT_FAILURE);
            }

            double agap = atof(argv[i + 1]);

            lp_set_abs_mip_gap( lp, agap );
            continue;
        }
        if (strstr(optLower, "relgap")) {
            if (i + 1 == argc) {
                fprintf(stderr, "enter the relative MIP gap.\n");
                exit(EXIT_FAILURE);
            }

            double rgap = atof(argv[i + 1]);

            lp_set_rel_mip_gap( lp, rgap );
            continue;
        }
        if (strstr(optLower, "soloutfn")) {
            if (i + 1 == argc) {
                fprintf(stderr, "enter solution file name.\n");
                exit(EXIT_FAILURE);
            }

            printf("> setting solution output file name to %s\n", argv[i + 1]);

            lp_set_sol_out_file_name(lp, argv[i + 1]);
            continue;
        }
        if (strstr(optLower, "solinfn")) {
            if (i + 1 == argc) {
                fprintf(stderr, "enter solution file name.\n");
                exit(EXIT_FAILURE);
            }

            printf("> setting solution input file name to %s\n", argv[i + 1]);

            lp_set_sol_in_file_name(lp, argv[i + 1]);
            continue;
        }
    }
}

void lp_set_sol_out_file_name(LinearProgram *lp, const char *sfn)
{
    assert(lp);

    strcpy(lp->solOutFN, sfn);
}

void lp_set_sol_in_file_name(LinearProgram *lp, const char *sfn)
{
    assert(lp);

    strcpy(lp->solInFN, sfn);
}

void lp_load_mip_starti( LinearProgram *lp, int count, const int *colIndexes, const double *colValues )
{
    if (lp->msNames)
    {
        delete[] lp->msNames[0];
        delete[] lp->msNames; 
    }
    if (lp->msIdx)
        delete[] lp->msIdx;
    if (lp->msVal)
        delete[] lp->msVal;

    int totalStrSize = 0;
    for ( int i=0 ; (i<count) ; ++i )
    {
        char colName[512];
        totalStrSize += strlen(lp_col_name(lp, colIndexes[i], colName))+1;
    }
    lp->msNames = new char*[count+1];
    lp->msVars = count;
    lp->msNames[0] = new char[totalStrSize];
    lp->msVal = new double[lp->msVars];
    for ( int i=0 ; (i<count) ; ++i )
    {
        lp_col_name( lp, colIndexes[i], lp->msNames[i] );
        lp->msVal[i] = colValues[i];
        lp->msNames[i+1] = lp->msNames[i]+strlen(lp->msNames[i])+1;
    }
}

void lp_load_mip_start(LinearProgram *lp, int count, const char **colNames, const double *colValues)
{
    if (lp->msNames)
    {
        delete[] lp->msNames[0];
        delete[] lp->msNames; 
    }
    if (lp->msIdx)
        delete[] lp->msIdx;
    if (lp->msVal)
        delete[] lp->msVal;

    int totalStrSize = 0;
    for ( int i=0 ; (i<count) ; ++i )
        totalStrSize += strlen(colNames[i])+1;

    lp->msNames = new char*[count+1];
    lp->msVars = count;
    lp->msVal = new double[lp->msVars];
    lp->msNames[0] = new char[totalStrSize];
    for ( int i=0 ; (i<count) ; ++i )
    {
        strcpy( lp->msNames[i], colNames[i] );
        lp->msNames[i+1] = lp->msNames[i]+strlen(lp->msNames[i])+1;
        lp->msVal[i] = colValues[i];
    }
}

void lp_chg_obj(LinearProgram *lp, int count, int idx[], double obj[])
{
#ifdef CBC
    for (int i=0 ; (i<count) ; i++ )
        lp->_lp->setObjCoeff( idx[i], obj[i]);
#endif
}

int lp_nz(LinearProgram *lp)
{
#ifdef CBC
    return lp->_lp->getNumElements();
#endif
    return 0;
}

void lp_cols_by_type( LinearProgram *lp, int *binaries, int *integers, int *continuous )
{
    *binaries = *integers = *continuous = 0;

    for (int i=0 ; (i<lp_cols(lp)) ; i++ )
    {
        const double lb = lp_col_lb( lp, i );
        const double ub = lp_col_ub( lp, i );

        if (lp_is_integer( lp, i ))
        {
            if ( ( fabs( lb ) <= EPS ) && (fabs( ub - 1.0 ) <= EPS) )
                (*binaries)++;
            else
                (*integers)++;
        }
        else
            (*continuous)++;
    }
}

void lp_help_options()
{
    printf("options:\n");
    printf("\t-nomip             :  solves only the linear programming relaxation\n");
    printf("\t-allinteger        :  solves as a pure integer program\n");
    printf("\t-maxSec sec        :  specifies timelimit of 'sec' seconds\n");
    printf("\t-maxNodes nodes    :  specifies node limit of 'nodes' nodes\n");
    printf("\t-maxSol sol        :  search will be ended when 'sol' solutions are found.\n");
    printf("\t-absgap gap        :  set allowed the absolute MIP gap to 'gap'.\n");
    printf("\t-relgap gap        :  set allowed the relative MIP gap to 'gap'.\n");
    printf("\t-solOutFN solfname :  file name to save solution\n");
    printf("\t-solInFN  solfname :  file name to read solution\n");
}

int lp_read_mip_start( LinearProgram *lp, const char *fileName )
{
#define STR_SIZE 512
    FILE *f = fopen( fileName, "r" );
    if (!f)
    {
        fprintf( stderr, "Could not open mipstart from file %s at %s:%d.\n", fileName, __FILE__, __LINE__ );
        abort();
    }
    char line[STR_SIZE];

    int nLine = 0;

    vector< string > cNames; vector< double > cValues;
    while (fgets( line, STR_SIZE, f ))
    {
        ++nLine;
        char col[4][STR_SIZE];
        int nread = sscanf( line, "%s %s %s %s", col[0], col[1], col[2], col[3] );
        if (!nread)
            continue;
        /* line with variable value */
        if (strlen(col[0])&&isdigit(col[0][0])&&(nread>=3))
        {
            if (!lp_str_is_num(col[0]))
            {
                fprintf( stderr, "LP warning: reading: %s, line %d - first column in mipstart file should be numeric, ignoring.", fileName, nLine );
                continue;
            }
            if (!lp_str_is_num(col[2]))
            {
                fprintf( stderr, "LP warning: reading: %s, line %d - third column in mipstart file should be numeric, ignoring.", fileName, nLine  );
                continue;
            }

            cNames.push_back( col[1] );
            cValues.push_back( atof( col[2] ) );
        }
    }

    if (cNames.size())
        printf("LP: mipstart values read for %zu variables.\n", cNames.size() );
    else
        printf("LP: no mipstart solution read from %s.\n", fileName );

    if (lp->msNames)
    {
        free( lp->msNames[0] );
        free( lp->msNames );
    }
    if (lp->msVal)
        free( lp->msVal );

    int totalChars = 0;
    for ( int i=0 ; (i<(int)cNames.size()) ; ++i )
        totalChars += cNames[i].size()+1;

    lp->msVal = (double*) malloc( sizeof(double)*cNames.size() );
    lp->msNames = (char**) malloc( sizeof(char*)*(cNames.size()+1) );
    lp->msNames[0] = (char*) malloc( sizeof(char)*totalChars );
    for ( int i=1 ; (i<(int)cNames.size()) ; ++i )
        lp->msNames[i] = lp->msNames[i-1] + cNames[i-1].size()+1;

    for ( int i=0 ; (i<(int)cNames.size()) ; ++i )
        strcpy( lp->msNames[i], cNames[i].c_str() );

    lp->msVars = cNames.size();

    fclose(f);

    return cNames.size();
#undef STR_SIZE
}

void lp_set_abs_mip_gap( LinearProgram *lp, const double _value )
{
    lp->absMIPGap = _value;
}

void lp_set_rel_mip_gap( LinearProgram *lp, const double _value )
{
    lp->relMIPGap = _value;
}

bool lp_str_is_num( const char *str )
{
    const size_t l = strlen(str);

    for ( size_t i=0 ; i<l ; ++i )
        if (!(isdigit(str[i])||(str[i]=='.')))
            return false;

    return true;
}

char lp_is_binary( LinearProgram *lp, const int j )
{
    return ( (lp_is_integer(lp,j)) && (fabs(lp_col_lb(lp,j))<= EPS)  && (fabs(lp_col_ub(lp,j)-1.0)<=EPS) );
}

int lp_row_type( LinearProgram *lp, const int row )
{

    lp->_idx->resize( lp_cols(lp) );
    lp->_coef->resize( lp_cols(lp) );

    int *idx = &((*lp->_idx)[0]);
    double *coef = &((*lp->_coef)[0]);

    int result = CONS_OTHER;

    double minc = DBL_MAX, maxc = -DBL_MAX;
    int nz = lp_row( lp, row, idx, coef );
    assert( nz>=0 );

    int nbinaries = 0;
    int nint = 0;
    int ncont = 0;


    int nIntCoef = 0;
    int j;
    for ( j=0 ; (j<nz) ; ++j )
    {
        minc = std::min( minc, coef[j] );
        maxc = std::max( maxc, coef[j] );
        if (lp_is_binary(lp,idx[j]))
            nbinaries++;
        else
            if (lp_is_integer(lp,idx[j]))
                nint++;
            else
                ncont++;
        nIntCoef += is_integer( coef[j] );
    }
    char sense = lp_sense( lp, row );
    double rhs = lp_rhs( lp, row );
    char allOneLHS = ( (fabs(minc-maxc)<=EPS) && (fabs(minc-1.0)<=EPS) );
    char rhsOne = fabs(rhs-1.0) <= EPS;

    /* binaries, all positive and integral */
    if ( (nbinaries==nz)&&(minc>=0.98)&&(rhs>=0.98) )
    {
        switch (sense)
        {
            case 'E':
                {
                    if (allOneLHS )
                    {
                        if ( rhsOne )
                            result = CONS_PARTITIONING;
                        else
                            if ( rhs >= 1.99 )
                                result = CONS_CARDINALITY;
                    }
                    goto RETURN_POINT;
                }
            case 'L':
                {
                    if ( (allOneLHS) && (rhsOne) )
                    {
                        result = CONS_PACKING;
                        goto RETURN_POINT;
                    }
                    else
                        if (allOneLHS)
                        {
                            result = CONS_INV_KNAPSACK;
                            goto RETURN_POINT;
                        }
                        else
                            if ( (maxc>=1.99) && (rhs>=1.99) )
                            {
                                result = CONS_KNAPSACK;
                                goto RETURN_POINT;
                            }

                    goto RETURN_POINT;
                }
            case 'G':
                {
                    if( (allOneLHS) && (rhsOne) )
                    {
                        result = CONS_COVERING;
                        goto RETURN_POINT;
                    }
                    goto RETURN_POINT;

                }
        }
    }

    /*  = 0,  flow constraints */
    if ((fabs(rhs)<=1e-8) && (sense=='E'))
    {
        if ( ( minc <= -0.98 ) && (maxc >= 0.98 ) )
        {
            if ( nbinaries == nz )
            {
                result = CONS_FLOW_BIN;
                goto RETURN_POINT;
            }
            else
            {
                if ( nint+nbinaries == nz )
                {
                    result = CONS_FLOW_INT;
                    goto RETURN_POINT;
                }
                else
                {
                    result = CONS_FLOW_MX;
                    goto RETURN_POINT;
                }
            }
        }
    }

RETURN_POINT:

    return result;
}

double lp_best_bound( LinearProgram *lp )
{
    return lp->bestBound;
}

void lp_rows_by_type( LinearProgram *lp, int rtype[] )
{
    memset( rtype, 0, sizeof(int)*CONS_NUMBER );
    int i;
    for ( i=0 ; (i<lp_rows(lp)) ; ++i )
        rtype[lp_row_type(lp,i)]++;
}

void lp_set_integer( LinearProgram *lp, int nCols, int cols[] )
{
#ifdef CBC
    printf("transforming %d variables into integer ones.\n", nCols );
    lp->osiLP->setInteger( cols, nCols );
#endif
}

char *lp_status_str( int status, char *statusStr )
{
    switch (status)
    {
        case LP_OPTIMAL:
            sprintf( statusStr, "LP_OPTIMAL");
            break;
        case LP_UNBOUNDED:
            sprintf( statusStr, "LP_UNBOUNDED");
            break;
        case LP_INFEASIBLE:
            sprintf( statusStr, "LP_INFEASIBLE");
            break;
        case LP_FEASIBLE:
            sprintf( statusStr, "LP_FEASIBLE");
            break;
        case LP_INTINFEASIBLE:
            sprintf( statusStr, "LP_INTINFEASIBLE");
            break;
        case LP_NO_SOL_FOUND:
            sprintf( statusStr, "LP_NO_SOL_FOUND");
            break;
        case LP_ERROR:
            sprintf( statusStr, "LP_ERROR");
            break;
        default:
            fprintf( stderr, "lp status not recognized: %d\n", status );
            abort();
    }

    return statusStr;
}

int *lp_original_colummns( LinearProgram *lp )
{
    return &((*lp->_orig)[0]);
}

void lp_mipstart_debug( LinearProgram *lp )
{
}

void lp_remove_row( LinearProgram *lp, int idxRow )
{

#ifdef NEED_OWN_INDEX
    {
        char rName[512] = "";
        lp_row_name( lp, idxRow, rName );
        map< string, int >::iterator mIt = (*lp->rowNameIdx).find( string(rName) );
        assert( mIt != (*lp->rowNameIdx).end() );
        (*lp->rowNameIdx).erase( mIt );
    }
#endif

#ifdef NEED_OWN_INDEX
    // updating index of all columns after this
    for ( map< string, int >::iterator it=(*lp->rowNameIdx).begin() ; it!=(*lp->rowNameIdx).end() ; ++it )
        if (it->second >= idxRow)
            --(it->second);
#endif
}


double round( const double v )
{
    return (double) ( (long long) (v+0.5) );
}

bool is_integer( const double v )
{
    if ( (v==DBL_MAX) || (v==DBL_MIN) )
        return true;

    return (  fabs(round(v) - v) <= 1e-10 );
}

double* lp_reduced_cost(LinearProgram* lp)
{
    assert(lp != NULL);

    if (lp->nOptimizations == 0) {
        fprintf(stderr, "No optimizations have been made with this model.\n");
        abort();
    }

    if (lp->status != LP_OPTIMAL) {
        fprintf(stderr, "\n\nERROR: no dual solution available.\n At: %s:%d\n\n", __FILE__, __LINE__);
        abort();
    }

    return &((*(lp->_rc))[0]);
}

void lp_set_store_names(bool store)
{
    LPstoreNames = store;
}

void lp_save_mip_start( LinearProgram *lp, const char *fileName )
{
    char fname[512];
    strcpy( fname, fileName ); 
    if (strstr(fname, ".")==NULL)
        strcat(fname, ".sol");

    assert( lp );
    assert( lp->msVars && lp->msVal && lp->msNames );

    FILE *f = fopen( fname, "w" );
    fprintf( f, "Feasible - 0.00\n" );
    for ( size_t i=0 ; (i<(size_t)lp->msVars) ; ++i )
        fprintf( f, "%zu %s %g\n", i, lp->msNames[i], lp->msVal[i] );
    fclose(f);
}

void lp_remove_rows( LinearProgram *lp, int nRows, int *rows )
{
    std::sort( rows, rows+nRows );

#ifdef NEED_OWN_INDEX
    int minR = rows[0];
    {
        // removing names of removed rows
        char rName[256] = "";
        for ( int i=0 ; (i<nRows) ; ++i )
        {
            lp_row_name( lp, rows[i], rName );
            map< string, int >::iterator mIt = (*lp->rowNameIdx).find( string(rName) );
            if (mIt != (*lp->rowNameIdx).end())
                (*lp->rowNameIdx).erase( mIt );
        }
    }
#endif

#ifdef CBC
    lp->osiLP->deleteRows( nRows, rows );
#endif

#ifdef NEED_OWN_INDEX
    // updating index of all columns after removed columns
    {
        char rowName[256];
        for ( int i=minR ; i<lp_rows(lp) ; ++i )
            (*lp->rowNameIdx)[lp_row_name(lp, i, rowName)] = i;
    }
#endif
}

void lp_set_branching_priorities( LinearProgram *lp, int *priorities )
{
    assert( lp ); assert( priorities );

    lp->_priorities->resize( lp_cols(lp) );
    memcpy( &((*lp->_priorities)[0]), priorities, sizeof(int)*lp_cols(lp) );
}

void lp_set_branching_direction( LinearProgram *lp, int direction )
{
    lp->branchDir = direction;
}

void lp_add_cutoff( LinearProgram *lp, double cutoff, char addConstraint )
{
    lp->cutoff = cutoff;
    lp->cutoffAsConstraint = addConstraint;
}

void lp_fix_mipstart( LinearProgram *lp )
{
    lp_check_mipstart( lp );
    vector< double > lb; vector< double > ub;

    for ( int i=0 ; (i<lp->msVars) ; ++i )
    {
        printf("fixing %s (%d) to %g\n", lp->msNames[i], lp->msIdx[i], lp->msVal[i] ); fflush(stdout); fflush(stderr);
        lb.push_back( lp_col_lb( lp, lp->msIdx[i] ) );
        ub.push_back( lp_col_ub( lp, lp->msIdx[i] ) );
        lp_fix_col( lp, lp->msIdx[i], lp->msVal[i] );
        int status = lp_optimize_as_continuous( lp );
        if ( status != LP_OPTIMAL )
        {
            printf("Error\n");
            lp_write_lp( lp, "errorfix" );

            exit( EXIT_FAILURE );
        }

    }

    // unfixing
    for ( int i=0 ; (i<lp->msVars) ; ++i )
        lp_set_col_bounds( lp, lp->msIdx[i], lb[i], ub[i] );

    printf("%d MIPStart variables fixed.\n", lp->msVars );      
}


ILP_solver::ILP_solver() {}

ILP_solver::ILP_solver(design& mydesign, PnRDB::hierNode& node) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.ILP_solver");
  LL.x = INT_MAX;
  LL.y = INT_MAX;
  UR.x = INT_MIN;
  UR.x = INT_MIN;
  Blocks.resize(mydesign.Blocks.size());
  Aspect_Ratio_weight = mydesign.Aspect_Ratio_weight;
  // first correct global placement result
  for (const auto& symmetry : mydesign.SPBlocks) {
    if (symmetry.axis_dir == placerDB::V) {
      set<int> center_y_set;
      set<int> distance_set;
      int center_x = 0;
      for (const auto& i_selfsym : symmetry.selfsym) {
        center_x += node.Blocks[i_selfsym.first].instance[0].placedCenter.x;
      }
      for (const auto& i_sympair : symmetry.sympair) {
        center_x += node.Blocks[i_sympair.first].instance[0].placedCenter.x;
        center_x += node.Blocks[i_sympair.second].instance[0].placedCenter.x;
      }
      center_x /= (symmetry.selfsym.size() + symmetry.sympair.size() * 2);
      for (const auto& i_selfsym : symmetry.selfsym) {
        while (center_y_set.find(node.Blocks[i_selfsym.first].instance[0].placedCenter.y) != center_y_set.end())
          node.Blocks[i_selfsym.first].instance[0].placedCenter.y++;
        center_y_set.insert(node.Blocks[i_selfsym.first].instance[0].placedCenter.y);
        node.Blocks[i_selfsym.first].instance[0].placedCenter.x = center_x;
      }
      for (const auto& i_sympair : symmetry.sympair) {
        int diff = center_x - (node.Blocks[i_sympair.first].instance[0].placedCenter.x + node.Blocks[i_sympair.second].instance[0].placedCenter.x) / 2;
        node.Blocks[i_sympair.first].instance[0].placedCenter.x += diff - 1;
        node.Blocks[i_sympair.second].instance[0].placedCenter.x += diff + 1;
        while (distance_set.find(abs(node.Blocks[i_sympair.first].instance[0].placedCenter.x - node.Blocks[i_sympair.second].instance[0].placedCenter.x)) !=
               distance_set.end()) {
          node.Blocks[i_sympair.first].instance[0].placedCenter.x--;
          node.Blocks[i_sympair.second].instance[0].placedCenter.x++;
        }
        distance_set.insert(abs(node.Blocks[i_sympair.first].instance[0].placedCenter.x - node.Blocks[i_sympair.second].instance[0].placedCenter.x));
        int center_y = (node.Blocks[i_sympair.first].instance[0].placedCenter.y + node.Blocks[i_sympair.second].instance[0].placedCenter.y) / 2;
        while (center_y_set.find(center_y) != center_y_set.end()) center_y++;
        center_y_set.insert(center_y);
        node.Blocks[i_sympair.first].instance[0].placedCenter.y = center_y;
        node.Blocks[i_sympair.second].instance[0].placedCenter.y = center_y;
      }
    } else {
      set<int> center_x_set;
      set<int> distance_set;
      int center_y = 0;
      for (const auto& i_selfsym : symmetry.selfsym) {
        center_y += node.Blocks[i_selfsym.first].instance[0].placedCenter.y;
      }
      for (const auto& i_sympair : symmetry.sympair) {
        center_y += node.Blocks[i_sympair.first].instance[0].placedCenter.y;
        center_y += node.Blocks[i_sympair.second].instance[0].placedCenter.y;
      }
      center_y /= (symmetry.selfsym.size() + symmetry.sympair.size() * 2);
      for (const auto& i_selfsym : symmetry.selfsym) {
        while (center_x_set.find(node.Blocks[i_selfsym.first].instance[0].placedCenter.x) != center_x_set.end())
          node.Blocks[i_selfsym.first].instance[0].placedCenter.x++;
        center_x_set.insert(node.Blocks[i_selfsym.first].instance[0].placedCenter.x);
        node.Blocks[i_selfsym.first].instance[0].placedCenter.y = center_y;
      }
      for (const auto& i_sympair : symmetry.sympair) {
        int diff = center_y - (node.Blocks[i_sympair.first].instance[0].placedCenter.y + node.Blocks[i_sympair.second].instance[0].placedCenter.y) / 2;
        node.Blocks[i_sympair.first].instance[0].placedCenter.y += diff;
        node.Blocks[i_sympair.second].instance[0].placedCenter.y += diff;
        while (distance_set.find(abs(node.Blocks[i_sympair.first].instance[0].placedCenter.y - node.Blocks[i_sympair.second].instance[0].placedCenter.y)) !=
               distance_set.end()) {
          node.Blocks[i_sympair.first].instance[0].placedCenter.y--;
          node.Blocks[i_sympair.second].instance[0].placedCenter.y++;
        }
        distance_set.insert(abs(node.Blocks[i_sympair.first].instance[0].placedCenter.y - node.Blocks[i_sympair.second].instance[0].placedCenter.y));
        int center_x = (node.Blocks[i_sympair.first].instance[0].placedCenter.x + node.Blocks[i_sympair.second].instance[0].placedCenter.x) / 2;
        while (center_x_set.find(center_x) != center_x_set.end()) center_x++;
        center_x_set.insert(center_x);
        node.Blocks[i_sympair.first].instance[0].placedCenter.x = center_x;
        node.Blocks[i_sympair.second].instance[0].placedCenter.x = center_x;
      }
    }
  }
  // correct alignblocks position
  for (const auto& align : mydesign.Align_blocks) {
    if (align.horizon) {
      int LLy = 0;
      set<int> center_x_set;
      for (unsigned int i = 0; i < align.blocks.size(); i++) {
        LLy += node.Blocks[align.blocks[i]].instance[0].placedCenter.y - node.Blocks[align.blocks[i]].instance[0].height / 2;
      }
      LLy /= align.blocks.size();
      for (unsigned int i = 0; i < align.blocks.size(); i++) {
        while (center_x_set.find(node.Blocks[align.blocks[i]].instance[0].placedCenter.x) != center_x_set.end())
          node.Blocks[align.blocks[i]].instance[0].placedCenter.x++;
        center_x_set.insert(node.Blocks[align.blocks[i]].instance[0].placedCenter.x);
        node.Blocks[align.blocks[i]].instance[0].placedCenter.y = LLy + node.Blocks[align.blocks[i]].instance[0].height / 2;
      }
    } else {
      int LLx = 0;
      set<int> center_y_set;
      for (unsigned int i = 0; i < align.blocks.size(); i++) {
        LLx += node.Blocks[align.blocks[i]].instance[0].placedCenter.x - node.Blocks[align.blocks[i]].instance[0].width / 2;
      }
      LLx /= align.blocks.size();
      for (unsigned int i = 0; i < align.blocks.size(); i++) {
        while (center_y_set.find(node.Blocks[align.blocks[i]].instance[0].placedCenter.y) != center_y_set.end())
          node.Blocks[align.blocks[i]].instance[0].placedCenter.y++;
        center_y_set.insert(node.Blocks[align.blocks[i]].instance[0].placedCenter.y);
        node.Blocks[align.blocks[i]].instance[0].placedCenter.x = LLx + node.Blocks[align.blocks[i]].instance[0].width / 2;
      }
    }
  }
  block_order = vector<vector<int>>(mydesign.Blocks.size(), vector<int>(mydesign.Blocks.size(), 0));
  // from LSB to MSB: at the left, align to left, the same x center, align to right, at the right, reserved, reserved, reserved
  // below, align to the bottom, the same y center, align to the top, above, reserved, reserved, reserved
  // block[i][j]&0x0010==0x0010 means i is to the right of j

  /**
  vector<pair<vector<vector<int>>, PnRDB::Smark>> ordering_alignblock;
  for (auto order : node.Ordering_Constraints) {
    pair<vector<vector<int>>, PnRDB::Smark> temp;
    temp.second = order.second;
    for (auto i : order.first) {
      vector<int> temp_seq = {i};
      for (auto align : node.Align_blocks) {
        if (order.second == PnRDB::H && align.horizon == 0 || order.second == PnRDB::V && align.horizon == 1) {
          if (find(align.blocks.begin(), align.blocks.end(), i) != align.blocks.end())
            for (auto b : align.blocks)
              if (b != i) temp_seq.push_back(b);
        }
      }
      temp.first.push_back(temp_seq);
      // group alignblock into the same order group
    }
    ordering_alignblock.push_back(temp);
  }
  **/
  for (const auto& order : node.Ordering_Constraints) {
    if (order.second == PnRDB::H) {
      for (unsigned int i = 0; i < order.first.size() - 1; i++) {
        for (unsigned int j = i + 1; j < order.first.size(); j++) {
          int blocki = order.first[i];
          int blockj = order.first[j];
          if (blocki < blockj)
            // i is at the left of j
            block_order[blocki][blockj] |= 0x0001;
          else
            // j is at the right of i
            block_order[blockj][blocki] |= 0x0010;
        }
      }
    } else {
      for (unsigned int i = 0; i < order.first.size() - 1; i++) {
        for (unsigned int j = i + 1; j < order.first.size(); j++) {
          int blocki = order.first[i];
          int blockj = order.first[j];
          if (blocki < blockj)
            // i is above j
            block_order[blocki][blockj] |= 0x1000;
          else
            // j is below i
            block_order[blockj][blocki] |= 0x0100;
        }
      }
    }
  }
  /**
  for (auto order : ordering_alignblock) {
    if (order.second == PnRDB::H) {
      for (unsigned int i = 0; i < order.first.size() - 1; i++) {
        for (unsigned int j = i + 1; j < order.first.size(); j++) {
          for (auto blocki : order.first[i]) {
            for (auto blockj : order.first[j]) {
              if (blocki < blockj)
                // i is at the left of j
                block_order[blocki][blockj] |= 0x0001;
              else
                // j is at the right of i
                block_order[blockj][blocki] |= 0x0010;
            }
          }
        }
      }
    } else {
      for (unsigned int i = 0; i < order.first.size() - 1; i++) {
        for (unsigned int j = i + 1; j < order.first.size(); j++) {
          for (auto blocki : order.first[i]) {
            for (auto blockj : order.first[j]) {
              if (blocki < blockj)
                // i is above j
                block_order[blocki][blockj] |= 0x1000;
              else
                // j is below i
                block_order[blockj][blocki] |= 0x0100;
            }
          }
        }
      }
    }
  }
  **/
  for (const auto& align : mydesign.Align_blocks) {
    if (align.horizon) {
      vector<int> blocks(align.blocks);
      sort(blocks.begin(), blocks.end());
      for (unsigned int i = 0; i < blocks.size(); i++) {
        for (unsigned int j = i + 1; j < blocks.size(); j++) {
          if (block_order[blocks[i]][blocks[j]] & 0xff00)
            logger->error("wrong constraint between block {0} and {1}", mydesign.Blocks[blocks[i]][0].name, mydesign.Blocks[blocks[j]][0].name);
          else
            block_order[blocks[i]][blocks[j]] |= 0x0200;  // i and j align to the bottom
        }
      }
    } else {
      vector<int> blocks(align.blocks);
      sort(blocks.begin(), blocks.end());
      for (unsigned int i = 0; i < blocks.size(); i++) {
        for (unsigned int j = i + 1; j < blocks.size(); j++) {
          if (block_order[blocks[i]][blocks[j]] & 0x00ff)
            logger->error("wrong constraint between block {0} and {1}", mydesign.Blocks[blocks[i]][0].name, mydesign.Blocks[blocks[j]][0].name);
          else
            block_order[blocks[i]][blocks[j]] |= 0x0002;  // i and j align to the left
        }
      }
    }
  }
  for (const auto& symmetry : mydesign.SPBlocks) {
    if (symmetry.axis_dir == placerDB::V) {
      for (const auto& pair : symmetry.sympair) {
        int first = pair.first, second = pair.second;
        if (first > second) std::swap(first, second);
        if (block_order[first][second] & 0x1100)
          logger->error("wrong constraint between block {0} and {1}", mydesign.Blocks[first][0].name, mydesign.Blocks[second][0].name);
        else if (block_order[first][second] & 0x0a00 && mydesign.Blocks[first][0].height != mydesign.Blocks[second][0].height)
          logger->error("wrong constraint between block {0} and {1}", mydesign.Blocks[first][0].name, mydesign.Blocks[second][0].name);
        else {
          block_order[first][second] &= 0x00ff;
          block_order[first][second] |= 0x0400;  // i and j have the same y center
        }
      }
      for (unsigned int i = 0; i < symmetry.selfsym.size(); i++) {
        for (unsigned int j = i + 1; j < symmetry.selfsym.size(); j++) {
          int first = symmetry.selfsym[i].first, second = symmetry.selfsym[j].first;
          if (first > second) std::swap(first, second);
          block_order[first][second] |= 0x0004;
          if (node.Blocks[first].instance[0].placedCenter.y < node.Blocks[second].instance[0].placedCenter.y)
            block_order[first][second] |= 0x0100;
          else
            block_order[first][second] |= 0x1000;
        }
      }
    } else {
      for (const auto& pair : symmetry.sympair) {
        int first = pair.first, second = pair.second;
        if (first > second) std::swap(first, second);
        if (block_order[first][second] & 0x0011)
          logger->error("wrong constraint between block {0} and {1}", mydesign.Blocks[first][0].name, mydesign.Blocks[second][0].name);
        else if (block_order[first][second] & 0x000a && mydesign.Blocks[first][0].width != mydesign.Blocks[second][0].width)
          logger->error("wrong constraint between block {0} and {1}", mydesign.Blocks[first][0].name, mydesign.Blocks[second][0].name);
        else {
          block_order[first][second] &= 0xff00;
          block_order[first][second] |= 0x0004;  // i and j have the same x center
        }
      }
      for (unsigned int i = 0; i < symmetry.selfsym.size(); i++) {
        for (unsigned int j = i + 1; j < symmetry.selfsym.size(); j++) {
          int first = symmetry.selfsym[i].first, second = symmetry.selfsym[j].first;
          if (first > second) std::swap(first, second);
          block_order[first][second] |= 0x0400;
          if (node.Blocks[first].instance[0].placedCenter.x < node.Blocks[second].instance[0].placedCenter.x)
            block_order[first][second] |= 0x0001;
          else
            block_order[first][second] |= 0x0010;
        }
      }
    }
  }
  int count = 0;
  for (unsigned int i = 0; i < node.Blocks.size() - 1; i++) {
    for (unsigned int j = i + 1; j < node.Blocks.size(); j++) {
      if ((block_order[i][j] & 0x000e) && (block_order[i][j] & 0x0e00))
        logger->error("wrong constranit between block {0} and {1}", mydesign.Blocks[i][0].name, mydesign.Blocks[j][0].name);
      if (node.Blocks[i].instance[0].width == 0) {
        block_order[i][j] |= 0x0001;
      }
      if ((block_order[i][j] & 0x1111) == 0) {  // neither left right below above
        if (block_order[i][j] & 0x00ff) {
          // align to left, x center, or right
          block_order[i][j] &= 0x00ff;
          if (node.Blocks[i].instance[0].placedCenter.y < node.Blocks[j].instance[0].placedCenter.y) {
            block_order[i][j] |= 0x0100;
            int i_counterpart = mydesign.SPBlocks[mydesign.Blocks[i][0].SBidx].axis_dir == placerDB::V ? mydesign.Blocks[i][0].counterpart : -1;
            int j_counterpart = mydesign.SPBlocks[mydesign.Blocks[j][0].SBidx].axis_dir == placerDB::V ? mydesign.Blocks[j][0].counterpart : -1;
            if (i_counterpart != -1) {
              if (i_counterpart < j && ((block_order[i_counterpart][j] & 0x1111) == 0)) block_order[i_counterpart][j] |= 0x0100;
              if (i_counterpart > j && ((block_order[j][i_counterpart] & 0x1111) == 0)) block_order[j][i_counterpart] |= 0x1000;
            }
            if (j_counterpart != -1) {
              if (i < j_counterpart && ((block_order[i][j_counterpart] & 0x1111) == 0)) block_order[i][j_counterpart] |= 0x0100;
              if (i > j_counterpart && ((block_order[j_counterpart][i] & 0x1111) == 0)) block_order[j_counterpart][i] |= 0x1000;
            }
            if (i_counterpart != -1 && j_counterpart != -1) {
              if (i_counterpart < j_counterpart && ((block_order[i_counterpart][j_counterpart] & 0x1111) == 0))
                block_order[i_counterpart][j_counterpart] |= 0x0100;
              if (i_counterpart > j_counterpart && ((block_order[j_counterpart][i_counterpart] & 0x1111) == 0))
                block_order[j_counterpart][i_counterpart] |= 0x1000;
            }
          } else {
            block_order[i][j] |= 0x1000;
            int i_counterpart = mydesign.SPBlocks[mydesign.Blocks[i][0].SBidx].axis_dir == placerDB::V ? mydesign.Blocks[i][0].counterpart : -1;
            int j_counterpart = mydesign.SPBlocks[mydesign.Blocks[j][0].SBidx].axis_dir == placerDB::V ? mydesign.Blocks[j][0].counterpart : -1;
            if (i_counterpart != -1) {
              if (i_counterpart < j && ((block_order[i_counterpart][j] & 0x1111) == 0)) block_order[i_counterpart][j] |= 0x1000;
              if (i_counterpart > j && ((block_order[j][i_counterpart] & 0x1111) == 0)) block_order[j][i_counterpart] |= 0x0100;
            }
            if (j_counterpart != -1) {
              if (i < j_counterpart && ((block_order[i][j_counterpart] & 0x1111) == 0)) block_order[i][j_counterpart] |= 0x1000;
              if (i > j_counterpart && ((block_order[j_counterpart][i] & 0x1111) == 0)) block_order[j_counterpart][i] |= 0x0100;
            }
            if (i_counterpart != -1 && j_counterpart != -1) {
              if (i_counterpart < j_counterpart && ((block_order[i_counterpart][j_counterpart] & 0x1111) == 0))
                block_order[i_counterpart][j_counterpart] |= 0x1000;
              if (i_counterpart > j_counterpart && ((block_order[j_counterpart][i_counterpart] & 0x1111) == 0))
                block_order[j_counterpart][i_counterpart] |= 0x0100;
            }
          }
        } else if (block_order[i][j] & 0xff00) {
          block_order[i][j] &= 0xff00;
          if (node.Blocks[i].instance[0].placedCenter.x < node.Blocks[j].instance[0].placedCenter.x)
            block_order[i][j] |= 0x0001;
          else
            block_order[i][j] |= 0x0010;
        } else {
          // if((!node.isFirstILP && ( node.placement_id & (1<<(count%30))))
          //|| (node.isFirstILP && abs(node.Blocks[i].instance[0].placedCenter.x - node.Blocks[j].instance[0].placedCenter.x) <
          // abs(node.Blocks[i].instance[0].placedCenter.y - node.Blocks[j].instance[0].placedCenter.y))){
          if (abs(node.Blocks[i].instance[0].placedCenter.x - node.Blocks[j].instance[0].placedCenter.x) <
              abs(node.Blocks[i].instance[0].placedCenter.y - node.Blocks[j].instance[0].placedCenter.y)) {
            block_order[i][j] &= 0x00ff;
            if (node.Blocks[i].instance[0].placedCenter.y < node.Blocks[j].instance[0].placedCenter.y)
              block_order[i][j] |= 0x0100;
            else
              block_order[i][j] |= 0x1000;
          } else {
            block_order[i][j] &= 0xff00;
            if (node.Blocks[i].instance[0].placedCenter.x < node.Blocks[j].instance[0].placedCenter.x)
              block_order[i][j] |= 0x0001;
            else
              block_order[i][j] |= 0x0010;
          }
          count++;
        }
      }
    }
  }
  int a = 1;
}

ILP_solver::ILP_solver(design& mydesign) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.ILP_solver");
  LL.x = INT_MAX;
  LL.y = INT_MAX;
  UR.x = INT_MIN;
  UR.y = INT_MIN;
  Blocks.resize(mydesign.Blocks.size());
  Aspect_Ratio_weight = mydesign.Aspect_Ratio_weight;
  memcpy(Aspect_Ratio, mydesign.Aspect_Ratio, sizeof(mydesign.Aspect_Ratio));
  memcpy(placement_box, mydesign.placement_box, sizeof(mydesign.placement_box));
}

ILP_solver::ILP_solver(const ILP_solver& solver) {
  Blocks = solver.Blocks;
  LL = solver.LL;
  UR = solver.UR;
  area = solver.area;
  HPWL = solver.HPWL;
  HPWL_extend = solver.HPWL_extend;
  HPWL_extend_terminal = solver.HPWL_extend_terminal;
  cost = solver.cost;
  constraint_penalty = solver.constraint_penalty;
  area_norm = solver.area_norm;
  HPWL_norm = solver.HPWL_norm;
  ratio = solver.ratio;
  linear_const = solver.linear_const;
  multi_linear_const = solver.multi_linear_const;
  Aspect_Ratio_weight = solver.Aspect_Ratio_weight;
  memcpy(Aspect_Ratio, solver.Aspect_Ratio, sizeof(solver.Aspect_Ratio));
  memcpy(placement_box, solver.placement_box, sizeof(solver.placement_box));
}

ILP_solver& ILP_solver::operator=(const ILP_solver& solver) {
  Blocks = solver.Blocks;
  LL = solver.LL;
  UR = solver.UR;
  area = solver.area;
  cost = solver.cost;
  constraint_penalty = solver.constraint_penalty;
  HPWL = solver.HPWL;
  HPWL_extend = solver.HPWL_extend;
  HPWL_extend_terminal = solver.HPWL_extend_terminal;
  area_norm = solver.area_norm;
  HPWL_norm = solver.HPWL_norm;
  ratio = solver.ratio;
  multi_linear_const = solver.multi_linear_const;
  Aspect_Ratio_weight = solver.Aspect_Ratio_weight;
  memcpy(Aspect_Ratio, solver.Aspect_Ratio, sizeof(solver.Aspect_Ratio));
  memcpy(placement_box, solver.placement_box, sizeof(solver.placement_box));
  return *this;
}

void ILP_solver::lpsolve_logger(lprec* lp, void* userhandle, char* buf) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.lpsolve_logger");

  // Strip leading newline
  while ((unsigned char)*buf == '\n') buf++;
  // Log non-empty lines
  if (*buf != '\0') logger->debug("Placer lpsolve: {0}", buf);
}

double ILP_solver::GenerateValidSolutionAnalytical(design& mydesign, PnRDB::Drc_info& drcInfo, PnRDB::hierNode& node) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.GenerateValidSolution");

  int v_metal_index = -1;
  int h_metal_index = -1;
  for (unsigned int i = 0; i < drcInfo.Metal_info.size(); ++i) {
    if (drcInfo.Metal_info[i].direct == 0) {
      v_metal_index = i;
      break;
    }
  }
  for (unsigned int i = 0; i < drcInfo.Metal_info.size(); ++i) {
    if (drcInfo.Metal_info[i].direct == 1) {
      h_metal_index = i;
      break;
    }
  }
  x_pitch = drcInfo.Metal_info[v_metal_index].grid_unit_x;
  y_pitch = drcInfo.Metal_info[h_metal_index].grid_unit_y;

  // each block has 4 vars, x, y, H_flip, V_flip;
  unsigned int N_var = mydesign.Blocks.size() * 4 + mydesign.Nets.size() * 2;
  // i*4+1:x
  // i*4+2:y
  // i*4+3:H_flip
  // i*4+4:V_flip
  lprec* lp = make_lp(0, N_var);
  set_verbose(lp, IMPORTANT);
  put_logfunc(lp, &ILP_solver::lpsolve_logger, NULL);
  // set_outputfile(lp, const_cast<char*>("/dev/null"));

  // set integer constraint, H_flip and V_flip can only be 0 or 1
  for (int i = 0; i < mydesign.Blocks.size(); i++) {
#ifdef ilp
    set_int(lp, i * 4 + 1, TRUE);
    set_int(lp, i * 4 + 2, TRUE);
    set_int(lp, i * 4 + 3, TRUE);
    set_int(lp, i * 4 + 4, TRUE);
#endif
    set_binary(lp, i * 4 + 3, TRUE);
    set_binary(lp, i * 4 + 4, TRUE);
  }

  // overlap constraint
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    for (unsigned int j = i + 1; j < mydesign.Blocks.size(); j++) {
      if (block_order[i][j] & 0x0001) {
        // i is at the left of j
        double sparserow[2] = {-1, 1};
        int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
        if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[i][0].width + mydesign.bias_Hgraph)) logger->error("error");
      } else if (block_order[i][j] & 0x0002) {
        // i and j align to LLx
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
        if (!add_constraintex(lp, 2, sparserow, colno, EQ, 0)) logger->error("error");
      } else if (block_order[i][j] & 0x0004) {
        // i and j align to x center
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
        if (!add_constraintex(lp, 2, sparserow, colno, EQ, mydesign.Blocks[j][0].width / 2 - mydesign.Blocks[i][0].width / 2)) logger->error("error");
      } else if (block_order[i][j] & 0x0008) {
        // i and j align to URx
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
        if (!add_constraintex(lp, 2, sparserow, colno, EQ, mydesign.Blocks[j][0].width - mydesign.Blocks[i][0].width)) logger->error("error");
      } else if (block_order[i][j] & 0x0010) {
        // i is at the right of j
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
        if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[j][0].width + mydesign.bias_Hgraph)) logger->error("error");
      }
      if (block_order[i][j] & 0x0100) {
        // i is at below j
        double sparserow[2] = {-1, 1};
        int colno[2] = {int(i) * 4 + 2, int(j) * 4 + 2};
        if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[i][0].height + mydesign.bias_Vgraph)) logger->error("error");
      } else if (block_order[i][j] & 0x0200) {
        // i and j align to LLy
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 2, int(j) * 4 + 2};
        if (!add_constraintex(lp, 2, sparserow, colno, EQ, 0)) logger->error("error");
      } else if (block_order[i][j] & 0x0400) {
        // i and j align to y center
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 2, int(j) * 4 + 2};
        if (!add_constraintex(lp, 2, sparserow, colno, EQ, mydesign.Blocks[j][0].height / 2 - mydesign.Blocks[i][0].height / 2)) logger->error("error");
      } else if (block_order[i][j] & 0x0800) {
        // i and j align to URy
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 2, int(j) * 4 + 2};
        if (!add_constraintex(lp, 2, sparserow, colno, EQ, mydesign.Blocks[j][0].height - mydesign.Blocks[i][0].height)) logger->error("error");
      } else if (block_order[i][j] & 0x1000) {
        // i is above j
        double sparserow[2] = {1, -1};
        int colno[2] = {int(i) * 4 + 2, int(j) * 4 + 2};
        if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[j][0].height + mydesign.bias_Vgraph)) logger->error("error");
      }
    }
  }
  /**
  for (int i = 0; i < mydesign.Blocks.size(); i++) {
    int i_pos_index = find(curr_sp.posPair.begin(), curr_sp.posPair.end(), i) - curr_sp.posPair.begin();
    int i_neg_index = find(curr_sp.negPair.begin(), curr_sp.negPair.end(), i) - curr_sp.negPair.begin();
    for (int j = i + 1; j < mydesign.Blocks.size(); j++) {
      int j_pos_index = find(curr_sp.posPair.begin(), curr_sp.posPair.end(), j) - curr_sp.posPair.begin();
      int j_neg_index = find(curr_sp.negPair.begin(), curr_sp.negPair.end(), j) - curr_sp.negPair.begin();
      if (i_pos_index < j_pos_index) {
        if (i_neg_index < j_neg_index) {
          // i is left of j
          double sparserow[2] = {1, -1};
          int colno[2] = {i * 4 + 1, j * 4 + 1};
          if (!add_constraintex(lp, 2, sparserow, colno, LE, -mydesign.Blocks[i][curr_sp.selected[i]].width - mydesign.bias_Hgraph)) logger->error("error");
        } else {
          // i is above j
          double sparserow[2] = {1, -1};
          int colno[2] = {i * 4 + 2, j * 4 + 2};
          if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[j][curr_sp.selected[j]].height + mydesign.bias_Vgraph)) logger->error("error");
        }
      } else {
        if (i_neg_index < j_neg_index) {
          // i is be low j
          double sparserow[2] = {1, -1};
          int colno[2] = {i * 4 + 2, j * 4 + 2};
          if (!add_constraintex(lp, 2, sparserow, colno, LE, -mydesign.Blocks[i][curr_sp.selected[i]].height - mydesign.bias_Vgraph)) logger->error("error");
        } else {
          // i is right of j
          double sparserow[2] = {1, -1};
          int colno[2] = {i * 4 + 1, j * 4 + 1};
          if (!add_constraintex(lp, 2, sparserow, colno, GE, mydesign.Blocks[j][curr_sp.selected[j]].width + mydesign.bias_Hgraph)) logger->error("error");
        }
      }
    }
  }**/

  // x>=0, y>=0
  for (unsigned int i = 0; i < node.Blocks.size(); i++) {
    {
      double sparserow[1] = {1};
      int colno[1] = {int(i) * 4 + 1};
      if (!add_constraintex(lp, 1, sparserow, colno, GE, 0)) logger->error("error");
    }
    {
      double sparserow[1] = {1};
      int colno[1] = {int(i) * 4 + 2};
      if (!add_constraintex(lp, 1, sparserow, colno, GE, 0)) logger->error("error");
    }
  }

  // symmetry block constraint
  for (const auto& SPBlock : mydesign.SPBlocks) {
    if (SPBlock.axis_dir == placerDB::H) {
      // constraint inside one pair
      for (unsigned int i = 0; i < SPBlock.sympair.size(); i++) {
        int first_id = SPBlock.sympair[i].first, second_id = SPBlock.sympair[i].second;
        // each pair has opposite V flip
        {
          double sparserow[2] = {1, 1};
          int colno[2] = {first_id * 4 + 4, second_id * 4 + 4};
          add_constraintex(lp, 2, sparserow, colno, EQ, 1);
        }
        // x center of blocks in each pair are the same
        //{
        // double sparserow[2] = {1, -1};
        // int colno[2] = {first_id * 4 + 1, second_id * 4 + 1};
        // int first_x_center = mydesign.Blocks[first_id][curr_sp.selected[first_id]].width / 2;
        // int second_x_center = mydesign.Blocks[second_id][curr_sp.selected[second_id]].width / 2;
        // add_constraintex(lp, 2, sparserow, colno, EQ, -first_x_center + second_x_center);
        //}
      }

      // constraint between two pairs
      for (unsigned int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        int i_first_y_center = mydesign.Blocks[i_first_id][0].height / 4;
        int i_second_y_center = mydesign.Blocks[i_second_id][0].height / 4;
        for (unsigned int j = i + 1; j < SPBlock.sympair.size(); j++) {
          // the y center of the two pairs are the same
          int j_first_id = SPBlock.sympair[j].first, j_second_id = SPBlock.sympair[j].second;
          int j_first_y_center = mydesign.Blocks[j_first_id][0].height / 4;
          int j_second_y_center = mydesign.Blocks[j_second_id][0].height / 4;
          double sparserow[4] = {0.5, 0.5, -0.5, -0.5};
          int colno[4] = {i_first_id * 4 + 2, i_second_id * 4 + 2, j_first_id * 4 + 2, j_second_id * 4 + 2};
          int bias = -i_first_y_center - i_second_y_center + j_first_y_center + j_second_y_center;
          add_constraintex(lp, 4, sparserow, colno, EQ, bias);
        }
      }

      // constraint between a pair and a selfsym
      for (unsigned int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        int i_first_y_center = mydesign.Blocks[i_first_id][0].height / 4;
        int i_second_y_center = mydesign.Blocks[i_second_id][0].height / 4;
        for (unsigned int j = 0; j < SPBlock.selfsym.size(); j++) {
          // the y center of the pair and the selfsym are the same
          int j_id = SPBlock.selfsym[j].first;
          int j_y_center = mydesign.Blocks[j_id][0].height / 2;
          double sparserow[3] = {0.5, 0.5, -1};
          int colno[3] = {i_first_id * 4 + 2, i_second_id * 4 + 2, j_id * 4 + 2};
          int bias = -i_first_y_center - i_second_y_center + j_y_center;
          add_constraintex(lp, 3, sparserow, colno, EQ, bias);
        }
      }

      // constraint between two selfsyms
      for (unsigned int i = 0; i < SPBlock.selfsym.size(); i++) {
        int i_id = SPBlock.selfsym[i].first;
        int i_y_center = mydesign.Blocks[i_id][0].height / 2;
        for (unsigned int j = i + 1; j < SPBlock.selfsym.size(); j++) {
          // the y center of the two selfsyms are the same
          int j_id = SPBlock.selfsym[j].first;
          int j_y_center = mydesign.Blocks[j_id][0].height / 2;
          double sparserow[2] = {1, -1};
          int colno[2] = {i_id * 4 + 2, j_id * 4 + 2};
          int bias = -i_y_center + j_y_center;
          add_constraintex(lp, 2, sparserow, colno, EQ, bias);
        }
      }
    } else {
      // axis_dir==V
      // constraint inside one pair
      for (unsigned int i = 0; i < SPBlock.sympair.size(); i++) {
        int first_id = SPBlock.sympair[i].first, second_id = SPBlock.sympair[i].second;
        // each pair has opposite H flip
        {
          double sparserow[2] = {1, 1};
          int colno[2] = {first_id * 4 + 3, second_id * 4 + 3};
          add_constraintex(lp, 2, sparserow, colno, EQ, 1);
        }
        // y center of blocks in each pair are the same
        //{
        // double sparserow[2] = {1, -1};
        // int colno[2] = {first_id * 4 + 2, second_id * 4 + 2};
        // int first_y_center = mydesign.Blocks[first_id][curr_sp.selected[first_id]].height / 2;
        // int second_y_center = mydesign.Blocks[second_id][curr_sp.selected[second_id]].height / 2;
        // add_constraintex(lp, 2, sparserow, colno, EQ, -first_y_center + second_y_center);
        //}
      }

      // constraint between two pairs
      for (unsigned int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        int i_first_x_center = mydesign.Blocks[i_first_id][0].width / 4;
        int i_second_x_center = mydesign.Blocks[i_second_id][0].width / 4;
        for (unsigned int j = i + 1; j < SPBlock.sympair.size(); j++) {
          // the x center of the two pairs are the same
          int j_first_id = SPBlock.sympair[j].first, j_second_id = SPBlock.sympair[j].second;
          int j_first_x_center = mydesign.Blocks[j_first_id][0].width / 4;
          int j_second_x_center = mydesign.Blocks[j_second_id][0].width / 4;
          double sparserow[4] = {0.5, 0.5, -0.5, -0.5};
          int colno[4] = {i_first_id * 4 + 1, i_second_id * 4 + 1, j_first_id * 4 + 1, j_second_id * 4 + 1};
          int bias = -i_first_x_center - i_second_x_center + j_first_x_center + j_second_x_center;
          add_constraintex(lp, 4, sparserow, colno, EQ, bias);
        }
      }

      // constraint between a pair and a selfsym
      for (unsigned int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        int i_first_x_center = mydesign.Blocks[i_first_id][0].width / 4;
        int i_second_x_center = mydesign.Blocks[i_second_id][0].width / 4;
        for (unsigned int j = 0; j < SPBlock.selfsym.size(); j++) {
          // the x center of the pair and the selfsym are the same
          int j_id = SPBlock.selfsym[j].first;
          int j_x_center = mydesign.Blocks[j_id][0].width / 2;
          double sparserow[3] = {0.5, 0.5, -1};
          int colno[3] = {i_first_id * 4 + 1, i_second_id * 4 + 1, j_id * 4 + 1};
          int bias = -i_first_x_center - i_second_x_center + j_x_center;
          add_constraintex(lp, 3, sparserow, colno, EQ, bias);
        }
      }

      // constraint between two selfsyms
      for (unsigned int i = 0; i < SPBlock.selfsym.size(); i++) {
        int i_id = SPBlock.selfsym[i].first;
        int i_x_center = mydesign.Blocks[i_id][0].width / 2;
        for (unsigned int j = i + 1; j < SPBlock.selfsym.size(); j++) {
          // the x center of the two selfsyms are the same
          int j_id = SPBlock.selfsym[j].first;
          int j_x_center = mydesign.Blocks[j_id][0].width / 2;
          double sparserow[2] = {1, -1};
          int colno[2] = {i_id * 4 + 1, j_id * 4 + 1};
          int bias = -i_x_center + j_x_center;
          add_constraintex(lp, 2, sparserow, colno, EQ, bias);
        }
      }
    }
  }
  /**
  // align block constraint
  for (auto alignment_unit : mydesign.Align_blocks) {
    for (int j = 0; j < alignment_unit.blocks.size() - 1; j++) {
      int first_id = alignment_unit.blocks[j], second_id = alignment_unit.blocks[j + 1];
      if (alignment_unit.horizon == 1) {
        // same y
        double sparserow[2] = {1, -1};
        int colno[2] = {first_id * 4 + 2, second_id * 4 + 2};
        add_constraintex(lp, 2, sparserow, colno, EQ, 0);
      } else {
        // same x
        double sparserow[2] = {1, -1};
        int colno[2] = {first_id * 4 + 1, second_id * 4 + 1};
        add_constraintex(lp, 2, sparserow, colno, EQ, 0);
      }
    }
  }**/

  // set_add_rowmode(lp, FALSE);
  {
    double row[N_var + 1] = {0};
    ConstGraph const_graph;
#ifndef min_displacement
    // add HPWL in cost
    for (unsigned int i = 0; i < mydesign.Nets.size(); i++) {
      vector<pair<int, int>> blockids;
      /// for (int j = 0; j < mydesign.Nets[i].connected.size(); j++) {
      /// if (mydesign.Nets[i].connected[j].type == placerDB::Block &&
      ///(blockids.size() == 0 || mydesign.Nets[i].connected[j].iter2 != curr_sp.negPair[blockids.back().first]))
      /// blockids.push_back(std::make_pair(find(curr_sp.negPair.begin(), curr_sp.negPair.end(), mydesign.Nets[i].connected[j].iter2) - curr_sp.negPair.begin(),
      /// mydesign.Nets[i].connected[j].iter));
      //}
      set<pair<pair<int, int>, int>> block_pos_x_set;
      set<pair<pair<int, int>, int>> block_pos_y_set;
      for (unsigned int j = 0; j < mydesign.Nets[i].connected.size(); j++) {
        if (mydesign.Nets[i].connected[j].type == placerDB::Block) {
          block_pos_x_set.insert(std::make_pair(std::make_pair(mydesign.Nets[i].connected[j].iter2, mydesign.Nets[i].connected[j].iter),
                                                node.Blocks[mydesign.Nets[i].connected[j].iter2].instance[0].placedCenter.x));
          block_pos_y_set.insert(std::make_pair(std::make_pair(mydesign.Nets[i].connected[j].iter2, mydesign.Nets[i].connected[j].iter),
                                                node.Blocks[mydesign.Nets[i].connected[j].iter2].instance[0].placedCenter.y));
        }
        // blockids.push_back(std::make_pair(find(curr_sp.negPair.begin(), curr_sp.negPair.end(), mydesign.Nets[i].connected[j].iter2) -
        // curr_sp.negPair.begin(), mydesign.Nets[i].connected[j].iter));
      }
      vector<pair<pair<int, int>, int>> block_pos_x(block_pos_x_set.begin(), block_pos_x_set.end());
      vector<pair<pair<int, int>, int>> block_pos_y(block_pos_y_set.begin(), block_pos_y_set.end());
      if (block_pos_x.size() < 2) continue;
      sort(block_pos_x.begin(), block_pos_x.end(), [](const pair<pair<int, int>, int>& a, const pair<pair<int, int>, int>& b) { return a.second < b.second; });
      sort(block_pos_y.begin(), block_pos_y.end(), [](const pair<pair<int, int>, int>& a, const pair<pair<int, int>, int>& b) { return a.second < b.second; });
      // sort(blockids.begin(), blockids.end(), [](const pair<int, int>& a, const pair<int, int>& b) { return a.first <= b.first; });
      /**int LLblock_id = curr_sp.negPair[blockids.front().first], LLpin_id = blockids.front().second;
      int LLblock_width = mydesign.Blocks[LLblock_id][curr_sp.selected[LLblock_id]].width,
          LLblock_height = mydesign.Blocks[LLblock_id][curr_sp.selected[LLblock_id]].height;
      int LLpin_x = mydesign.Blocks[LLblock_id][curr_sp.selected[LLblock_id]].blockPins[LLpin_id].center.front().x,
          LLpin_y = mydesign.Blocks[LLblock_id][curr_sp.selected[LLblock_id]].blockPins[LLpin_id].center.front().y;
      int URblock_id = curr_sp.negPair[blockids.back().first], URpin_id = blockids.back().second;
      int URblock_width = mydesign.Blocks[URblock_id][curr_sp.selected[URblock_id]].width,
          URblock_height = mydesign.Blocks[URblock_id][curr_sp.selected[URblock_id]].height;
      int URpin_x = mydesign.Blocks[URblock_id][curr_sp.selected[URblock_id]].blockPins[URpin_id].center.front().x,
          URpin_y = mydesign.Blocks[URblock_id][curr_sp.selected[URblock_id]].blockPins[URpin_id].center.front().y;**/
      int Lblock_id = block_pos_x.front().first.first, Lpin_id = block_pos_x.front().first.second;
      int Rblock_id = block_pos_x.back().first.first, Rpin_id = block_pos_x.back().first.second;
      int Lblock_width = mydesign.Blocks[Lblock_id][0].width, Lblock_height = mydesign.Blocks[Lblock_id][0].height;
      int Rblock_width = mydesign.Blocks[Rblock_id][0].width, Rblock_height = mydesign.Blocks[Rblock_id][0].height;
      int Lpin_x = mydesign.Blocks[Lblock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Lblock_id][0].blockPins[Lpin_id].center.front().x
                                                                      : mydesign.Blocks[Lblock_id][0].width / 2,
          Lpin_y = mydesign.Blocks[Lblock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Lblock_id][0].blockPins[Lpin_id].center.front().y
                                                                      : mydesign.Blocks[Lblock_id][0].height / 2;
      int Rpin_x = mydesign.Blocks[Rblock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Rblock_id][0].blockPins[Rpin_id].center.front().x
                                                                      : mydesign.Blocks[Rblock_id][0].width / 2,
          Rpin_y = mydesign.Blocks[Rblock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Rblock_id][0].blockPins[Rpin_id].center.front().y
                                                                      : mydesign.Blocks[Rblock_id][0].height / 2;

      int Dblock_id = block_pos_y.front().first.first, Dpin_id = block_pos_y.front().first.second;
      int Ublock_id = block_pos_y.back().first.first, Upin_id = block_pos_y.back().first.second;
      int Dblock_width = mydesign.Blocks[Dblock_id][0].width, Dblock_height = mydesign.Blocks[Dblock_id][0].height;
      int Ublock_width = mydesign.Blocks[Ublock_id][0].width, Ublock_height = mydesign.Blocks[Ublock_id][0].height;
      int Dpin_x = mydesign.Blocks[Dblock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Dblock_id][0].blockPins[Dpin_id].center.front().x
                                                                      : mydesign.Blocks[Dblock_id][0].width / 2,
          Dpin_y = mydesign.Blocks[Dblock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Dblock_id][0].blockPins[Dpin_id].center.front().y
                                                                      : mydesign.Blocks[Dblock_id][0].height / 2;
      int Upin_x = mydesign.Blocks[Ublock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Ublock_id][0].blockPins[Upin_id].center.front().x
                                                                      : mydesign.Blocks[Ublock_id][0].width / 2,
          Upin_y = mydesign.Blocks[Ublock_id][0].blockPins.size() > 0 ? mydesign.Blocks[Ublock_id][0].blockPins[Upin_id].center.front().y
                                                                      : mydesign.Blocks[Ublock_id][0].height / 2;

      // min abs(LLx+(LLwidth-2LLpinx)*LLHflip+LLpinx-URx-(URwidth-2URpinx)*URHflip-URpinx)=HPWLx
      //-> (LLx+(LLwidth-2LLpinx)*LLHflip+LLpinx-URx-(URwidth-2URpinx)*URHflip-URpinx)<=HPWLx
      //  -(LLx+(LLwidth-2LLpinx)*LLHflip+LLpinx-URx-(URwidth-2URpinx)*URHflip-URpinx)<=HPWLx
      if (Lblock_id != Rblock_id) {
        {
          double sparserow[5] = {const_graph.LAMBDA, (Lblock_width - 2 * Lpin_x) * const_graph.LAMBDA, -const_graph.LAMBDA,
                                 -(Rblock_width - 2 * Rpin_x) * const_graph.LAMBDA, -1};
          int colno[5] = {Lblock_id * 4 + 1, Lblock_id * 4 + 3, Rblock_id * 4 + 1, Rblock_id * 4 + 3, int(mydesign.Blocks.size()) * 4 + int(i) * 2 + 1};
          add_constraintex(lp, 5, sparserow, colno, LE, -Lpin_x + Rpin_x);
        }
        {
          double sparserow[5] = {-const_graph.LAMBDA, -(Lblock_width - 2 * Lpin_x) * const_graph.LAMBDA, const_graph.LAMBDA,
                                 (Rblock_width - 2 * Rpin_x) * const_graph.LAMBDA, -1};
          int colno[5] = {Lblock_id * 4 + 1, Lblock_id * 4 + 3, Rblock_id * 4 + 1, Rblock_id * 4 + 3, int(mydesign.Blocks.size()) * 4 + int(i) * 2 + 1};
          add_constraintex(lp, 5, sparserow, colno, LE, Lpin_x - Rpin_x);
        }
        row[mydesign.Blocks.size() * 4 + i * 2 + 1] = 1;
      }
      if (Dblock_id != Ublock_id) {
        {
          double sparserow[5] = {const_graph.LAMBDA, (Dblock_height - 2 * Dpin_y) * const_graph.LAMBDA, -const_graph.LAMBDA,
                                 -(Ublock_height - 2 * Upin_y) * const_graph.LAMBDA, -1};
          int colno[5] = {Dblock_id * 4 + 2, Dblock_id * 4 + 4, Ublock_id * 4 + 2, Ublock_id * 4 + 4, int(mydesign.Blocks.size()) * 4 + int(i) * 2 + 2};
          add_constraintex(lp, 5, sparserow, colno, LE, -Dpin_y + Upin_y);
        }
        {
          double sparserow[5] = {-const_graph.LAMBDA, -(Dblock_height - 2 * Dpin_y) * const_graph.LAMBDA, const_graph.LAMBDA,
                                 (Ublock_height - 2 * Upin_y) * const_graph.LAMBDA, -1};
          int colno[5] = {Dblock_id * 4 + 2, Dblock_id * 4 + 4, Ublock_id * 4 + 2, Ublock_id * 4 + 4, int(mydesign.Blocks.size()) * 4 + int(i) * 2 + 2};
          add_constraintex(lp, 5, sparserow, colno, LE, Dpin_y - Upin_y);
        }
        row[mydesign.Blocks.size() * 4 + i * 2 + 2] = 1;
      }
    }
#endif

    // add area in cost
    int estimated_width = 0, estimated_height = 0;
    // estimate width
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
      estimated_width += mydesign.Blocks[i][0].width;
    }
    // add estimated area
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
      row[i * 4 + 2] += estimated_width / 2;
    }
    // estimate height
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
      estimated_height += mydesign.Blocks[i][0].height;
    }
    // add estimated area
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
      row[i * 4 + 1] += estimated_height / 2;
    }

    set_obj_fn(lp, row);
    set_minim(lp);
    set_timeout(lp, 10);
// print_lp(lp);
#ifndef ilp
// set_presolve(lp, PRESOLVE_ROWS | PRESOLVE_COLS | PRESOLVE_LINDEP, get_presolveloops(lp));
#endif
    int ret = solve(lp);
    if (ret != 0 && ret != 1) {
      delete_lp(lp);
      return -1;
    }
  }

  double var[N_var];
#ifdef ilp
  get_variables(lp, var);
#else
  int Norig_columns, Norig_rows, i;
  Norig_columns = get_Norig_columns(lp);
  Norig_rows = get_Norig_rows(lp);
  for (i = 1; i <= Norig_columns; i++) {
    var[i - 1] = get_var_primalresult(lp, Norig_rows + i);
  }
#endif
  delete_lp(lp);
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    Blocks[i].x = var[i * 4];
    Blocks[i].y = var[i * 4 + 1];
    roundup(Blocks[i].x, x_pitch);
    roundup(Blocks[i].y, y_pitch);
    Blocks[i].H_flip = var[i * 4 + 2];
    Blocks[i].V_flip = var[i * 4 + 3];
  }

  // calculate LL and UR
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    LL.x = std::min(LL.x, Blocks[i].x);
    LL.y = std::min(LL.y, Blocks[i].y);
    UR.x = std::max(UR.x, Blocks[i].x + mydesign.Blocks[i][0].width);
    UR.y = std::max(UR.y, Blocks[i].y + mydesign.Blocks[i][0].height);
  }
  // calculate area
  area = double(UR.x - LL.x) * double(UR.y - LL.y);
  /**
  // calculate dead area
  dead_area = area;
  for (int i = 0; i < mydesign.Blocks.size(); i++) {
    dead_area -= double(mydesign.Blocks[i][0].width) * double(mydesign.Blocks[i][0].height);
  }
  // calculate ratio
  // ratio = std::max(double(UR.x - LL.x) / double(UR.y - LL.y), double(UR.y - LL.y) / double(UR.x - LL.x));
  **/
  ratio = double(UR.x - LL.x) / double(UR.y - LL.y);
  if (ratio < Aspect_Ratio[0] || ratio > Aspect_Ratio[1]) {
    return -1;
  }
  if (placement_box[0] > 0 && (UR.x - LL.x > placement_box[0]) || placement_box[1] > 0 && (UR.y - LL.y > placement_box[1])) {
    return -1;
  }
  // calculate HPWL
  HPWL = 0;
  for (const auto& neti : mydesign.Nets) {
    int HPWL_min_x = UR.x, HPWL_min_y = UR.y, HPWL_max_x = 0, HPWL_max_y = 0;
    for (const auto& connectedj : neti.connected) {
      if (connectedj.type == placerDB::Block) {
        int iter2 = connectedj.iter2, iter = connectedj.iter;
        if (mydesign.Blocks[iter2][0].blockPins.size() > 0) {
          for (const auto& centerk : mydesign.Blocks[iter2][0].blockPins[iter].center) {
            // calculate contact center
            int pin_x = centerk.x;
            int pin_y = centerk.y;
            if (Blocks[iter2].H_flip) pin_x = mydesign.Blocks[iter2][0].width - pin_x;
            if (Blocks[iter2].V_flip) pin_y = mydesign.Blocks[iter2][0].height - pin_y;
            pin_x += Blocks[iter2].x;
            pin_y += Blocks[iter2].y;
            HPWL_min_x = std::min(HPWL_min_x, pin_x);
            HPWL_max_x = std::max(HPWL_max_x, pin_x);
            HPWL_min_y = std::min(HPWL_min_y, pin_y);
            HPWL_max_y = std::max(HPWL_max_y, pin_y);
          }
        } else {
          int pin_x = mydesign.Blocks[iter2][0].width / 2;
          int pin_y = mydesign.Blocks[iter2][0].height / 2;
          if (Blocks[iter2].H_flip) pin_x = mydesign.Blocks[iter2][0].width - pin_x;
          if (Blocks[iter2].V_flip) pin_y = mydesign.Blocks[iter2][0].height - pin_y;
          pin_x += Blocks[iter2].x;
          pin_y += Blocks[iter2].y;
          HPWL_min_x = std::min(HPWL_min_x, pin_x);
          HPWL_max_x = std::max(HPWL_max_x, pin_x);
          HPWL_min_y = std::min(HPWL_min_y, pin_y);
          HPWL_max_y = std::max(HPWL_max_y, pin_y);
        }
      }
    }
    HPWL += (HPWL_max_y - HPWL_min_y) + (HPWL_max_x - HPWL_min_x);
  }
  // calculate linear constraint
  linear_const = 0;
  std::vector<std::vector<double>> feature_value;
  for (const auto& neti : mydesign.Nets) {
    std::vector<std::vector<placerDB::point>> center_points;
    for (const auto& connectedj : neti.connected) {
      if (connectedj.type == placerDB::Block) {
        std::vector<placerDB::point> pos;
        if (mydesign.Blocks[connectedj.iter2][0].blockPins.size() > 0) {
          for (const auto& ci : mydesign.Blocks[connectedj.iter2][0].blockPins[connectedj.iter].center) {
            placerDB::point newp;
            newp.x = ci.x;
            newp.y = ci.y;
            if (Blocks[connectedj.iter2].H_flip) newp.x = mydesign.Blocks[connectedj.iter2][0].width - newp.x;
            if (Blocks[connectedj.iter2].V_flip) newp.y = mydesign.Blocks[connectedj.iter2][0].height - newp.y;
            newp.x += Blocks[connectedj.iter2].x;
            newp.y += Blocks[connectedj.iter2].y;
            pos.push_back(newp);
          }
          center_points.push_back(pos);
        } else {
          placerDB::point newp;
          newp.x = mydesign.Blocks[connectedj.iter2][0].width / 2;
          newp.y = mydesign.Blocks[connectedj.iter2][0].height / 2;
          if (Blocks[connectedj.iter2].H_flip) newp.x = mydesign.Blocks[connectedj.iter2][0].width - newp.x;
          if (Blocks[connectedj.iter2].V_flip) newp.y = mydesign.Blocks[connectedj.iter2][0].height - newp.y;
          newp.x += Blocks[connectedj.iter2].x;
          newp.y += Blocks[connectedj.iter2].y;
          pos.push_back(newp);
          center_points.push_back(pos);
        }
      } else if (connectedj.type == placerDB::Terminal) {
        center_points.push_back({mydesign.Terminals[connectedj.iter].center});
      }
    }
    std::vector<double> temp_feature = Calculate_Center_Point_feature(center_points);
    feature_value.push_back(temp_feature);
    double temp_sum = 0;
    for (unsigned int j = 0; j < neti.connected.size(); j++) temp_sum += neti.connected[j].alpha * temp_feature[j];
    temp_sum = std::max(temp_sum - neti.upperBound, double(0));
    linear_const += temp_sum;
  }

  // calculate multi linear constraint
  multi_linear_const = 0;
  for (const auto& constrainti : mydesign.ML_Constraints) {
    double temp_sum = 0;
    for (const auto& constraintj : constrainti.Multi_linearConst) {
      for (unsigned int k = 0; k < constraintj.pins.size(); k++) {
        int index_i = 0;
        int index_j = 0;
        for (unsigned int m = 0; m < mydesign.Nets.size(); m++) {
          for (unsigned int n = 0; n < mydesign.Nets[m].connected.size(); n++) {
            if (mydesign.Nets[m].connected[n].iter2 == constraintj.pins[k].first && mydesign.Nets[m].connected[n].iter == constraintj.pins[k].second) {
              index_i = m;
              index_j = n;
              break;
            }
          }
        }
        temp_sum += constraintj.alpha[k] * feature_value[index_i][index_j];
      }
    }
    temp_sum = std::min(temp_sum, constrainti.upperBound);
    multi_linear_const += temp_sum;
  }

  double cost = CalculateCost(mydesign);
  return cost;
}

class TimeMeasure {
  private:
    std::chrono::nanoseconds& _rt;
    std::chrono::high_resolution_clock::time_point _begin;
  public:
    TimeMeasure(std::chrono::nanoseconds& rt) : _rt(rt)
    {
      _begin = std::chrono::high_resolution_clock::now();
    }
    ~TimeMeasure()
    {
      auto _end = std::chrono::high_resolution_clock::now();
      _rt += std::chrono::duration_cast<std::chrono::nanoseconds>(_end - _begin);
    }
};

bool ILP_solver::FrameSolveILP(const design& mydesign, const SeqPair& curr_sp, const PnRDB::Drc_info& drcInfo, bool flushbl, const vector<placerDB::point>* prev) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.FrameSolveILP");

  TimeMeasure tmsol(const_cast<design&>(mydesign).ilp_runtime);

  vector<int> objX(mydesign.Blocks.size(), 0), objY(mydesign.Blocks.size(), 0);
  // add area in cost
  int URblock_pos_id = 0, URblock_neg_id = 0;
  int estimated_width = 0, estimated_height = 0;
  for (unsigned int i = curr_sp.negPair.size() - 1; i >= 0; i--) {
    if (curr_sp.negPair[i] < int(mydesign.Blocks.size())) {
      URblock_neg_id = i;
      break;
    }
  }
  URblock_pos_id = find(curr_sp.posPair.begin(), curr_sp.posPair.end(), curr_sp.negPair[URblock_neg_id]) - curr_sp.posPair.begin();
  // estimate width
  for (int i = URblock_pos_id; i >= 0; i--) {
    if (curr_sp.posPair[i] < int(mydesign.Blocks.size())) {
      estimated_width += mydesign.Blocks[curr_sp.posPair[i]][curr_sp.selected[curr_sp.posPair[i]]].width;
    }
  }
  // add estimated area
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    if (curr_sp.negPair[i] >= mydesign.Blocks.size()) continue;
    objY.at(curr_sp.negPair[i]) += ((flushbl ? estimated_width : -estimated_width) / 2);
  }
  // estimate height
  for (unsigned int i = URblock_pos_id; i < curr_sp.posPair.size(); i++) {
    if (curr_sp.posPair[i] < int(mydesign.Blocks.size())) {
      estimated_height += mydesign.Blocks[curr_sp.posPair[i]][curr_sp.selected[curr_sp.posPair[i]]].height;
    }
  }
  // add estimated area
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    if (curr_sp.negPair[i] >= mydesign.Blocks.size()) continue;
    objX.at(curr_sp.negPair[i]) += ((flushbl ? estimated_height : -estimated_height) / 2);
  }

  int minx{0}, miny{0};
  if (!flushbl) {
    // x>=0, y>=0
    for (const auto& id : curr_sp.negPair) {
      if (id < int(mydesign.Blocks.size())) {
        minx += mydesign.Blocks[id][curr_sp.selected[id]].width;
        miny += mydesign.Blocks[id][curr_sp.selected[id]].height;
      }
    }
    /*for (const auto& id : curr_sp.negPair) {
      if (id < int(mydesign.Blocks.size())) {
        set_bounds(lp, (id * 4 + 1), -10*minx, -mydesign.Blocks[id][curr_sp.selected[id]].width);
        set_bounds(lp, (id * 4 + 2), -10*miny, -mydesign.Blocks[id][curr_sp.selected[id]].height);
      }
    }*/
  }
  // set integer constraint, H_flip and V_flip can only be 0 or 1
  LinearProgram *lp = nullptr;
  {
    TimeMeasure tm(const_cast<design&>(mydesign).ilp_cr_runtime);
    lp = lp_create();
  }
  {
    TimeMeasure tm(const_cast<design&>(mydesign).add_col_runtime);
    unsigned int N_var = (mydesign.Blocks.size() + mydesign.Nets.size()) * 4;
    for (int i = 0; i < mydesign.Blocks.size(); i++) {
      double cLB[] = {0., 0., 0., 0.};
      double cUB[] = {1.e30, 1.e30, 1., 1.};
      if (flushbl) {
        if (prev) {
          cLB[0] = (*prev)[i].x;
          cLB[1] = (*prev)[i].y;
        }
      } else {
        cLB[0] = -10 * minx;
        cLB[1] = -10 * miny;
        cUB[0] = -mydesign.Blocks[i][curr_sp.selected[i]].width;
        cUB[1] = -mydesign.Blocks[i][curr_sp.selected[i]].height;
      }
      double obj[] = {1.*objX[i], 1.*objY[i], 0., 0.};
      std::vector<std::string> namesvec = {
        mydesign.Blocks[i][0].name + "_x\0", mydesign.Blocks[i][0].name + "_y\0",
        mydesign.Blocks[i][0].name + "_flx\0", mydesign.Blocks[i][0].name + "_fly\0"
      };
      vector<char*> names;
      std::transform(namesvec.begin(), namesvec.end(), std::back_inserter(names), [](std::string& s){ return &s[0]; });
      char ints[] = {0, 0, 1, 1};
      lp_add_cols(lp, 4, obj, cLB, cUB, ints, names.data());
    }

    ConstGraph const_graph;
    for (int i = 0; i < mydesign.Nets.size(); ++i) {
      int ind = i * 4 + mydesign.Blocks.size() * 4 + 1;
      double obj[] = {-const_graph.LAMBDA, -const_graph.LAMBDA, const_graph.LAMBDA, const_graph.LAMBDA};
      double cLB[] = {-1.e30, -1.e30, -1.e30, -1.e30};
      double cUB[] = {1.e30, 1.e30, 1.e30, 1.e30};
      if (mydesign.Nets[i].connected.size() < 2) {
        obj[0] = 0.; obj[1] = 0.; obj[2] = 0.; obj[3] = 0.;
      }
      std::vector<std::string> namesvec = {
        mydesign.Nets[i].name + "_ll_x\0", mydesign.Nets[i].name + "_ll_y\0",
        mydesign.Nets[i].name + "_ur_x\0", mydesign.Nets[i].name + "_ur_y\0"
      };
      char ints[] = {0, 0, 0, 0};
      vector<char*> names;
      std::transform(namesvec.begin(), namesvec.end(), std::back_inserter(names), [](std::string& s){ return &s[0]; });
      lp_add_cols(lp, 4, obj, cLB, cUB, ints, names.data());
    }
  }


  {
    TimeMeasure tm(const_cast<design&>(mydesign).add_row_runtime);
    int bias_Hgraph = mydesign.bias_Hgraph, bias_Vgraph = mydesign.bias_Vgraph;
    roundup(bias_Hgraph, x_pitch);
    roundup(bias_Vgraph, y_pitch);
    // overlap constraint
    unsigned constrcnt{0};
    auto constrname = [&constrcnt](const std::string& s) { return s + "_" + std::to_string(constrcnt++);};
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
      int i_pos_index = find(curr_sp.posPair.begin(), curr_sp.posPair.end(), i) - curr_sp.posPair.begin();
      int i_neg_index = find(curr_sp.negPair.begin(), curr_sp.negPair.end(), i) - curr_sp.negPair.begin();
      for (unsigned int j = i + 1; j < mydesign.Blocks.size(); j++) {
        int j_pos_index = find(curr_sp.posPair.begin(), curr_sp.posPair.end(), j) - curr_sp.posPair.begin();
        int j_neg_index = find(curr_sp.negPair.begin(), curr_sp.negPair.end(), j) - curr_sp.negPair.begin();
        if (i_pos_index < j_pos_index) {
          if (i_neg_index < j_neg_index) {
            // i is left of j
            double sparserow[2] = {1, -1};
            int colno[2] = {int(i) * 4, int(j) * 4};
            if (find(mydesign.Abut_Constraints.begin(), mydesign.Abut_Constraints.end(), make_pair(make_pair(int(i), int(j)), placerDB::H)) !=
                mydesign.Abut_Constraints.end()) {
              lp_add_row(lp, 2, colno, sparserow, constrname("overlapl").c_str(), 'E', -mydesign.Blocks[i][curr_sp.selected[i]].width);
            } else {
              lp_add_row(lp, 2, colno, sparserow, constrname("overlapl").c_str(), 'L', -mydesign.Blocks[i][curr_sp.selected[i]].width - bias_Hgraph);
            }
          } else {
            // i is above j
            double sparserow[2] = {1, -1};
            int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
            if (find(mydesign.Abut_Constraints.begin(), mydesign.Abut_Constraints.end(), make_pair(make_pair(int(i), int(j)), placerDB::V)) !=
                mydesign.Abut_Constraints.end()) {
              lp_add_row(lp, 2, colno, sparserow, constrname("overlapa").c_str(), 'E', mydesign.Blocks[j][curr_sp.selected[j]].height);
            } else {
              lp_add_row(lp, 2, colno, sparserow, constrname("overlapa").c_str(), 'G', mydesign.Blocks[j][curr_sp.selected[j]].height + bias_Vgraph);
            }
          }
        } else {
          if (i_neg_index < j_neg_index) {
            // i is be low j
            double sparserow[2] = {1, -1};
            int colno[2] = {int(i) * 4 + 1, int(j) * 4 + 1};
            if (find(mydesign.Abut_Constraints.begin(), mydesign.Abut_Constraints.end(), make_pair(make_pair(int(j), int(i)), placerDB::V)) !=
                mydesign.Abut_Constraints.end()) {
              lp_add_row(lp, 2, colno, sparserow, constrname("overlapb").c_str(), 'E', -mydesign.Blocks[i][curr_sp.selected[i]].height);
            } else {
              lp_add_row(lp, 2, colno, sparserow, constrname("overlapb").c_str(), 'L', -mydesign.Blocks[i][curr_sp.selected[i]].height - bias_Vgraph);
            }
          } else {
            // i is right of j
            double sparserow[2] = {1, -1};
            int colno[2] = {int(i) * 4, int(j) * 4};
            if (find(mydesign.Abut_Constraints.begin(), mydesign.Abut_Constraints.end(), make_pair(make_pair(int(j), int(i)), placerDB::H)) !=
                mydesign.Abut_Constraints.end()) {
              lp_add_row(lp, 2, colno, sparserow, constrname("overlapr").c_str(), 'E', mydesign.Blocks[j][curr_sp.selected[j]].width);
            } else {
              lp_add_row(lp, 2, colno, sparserow, constrname("overlapr").c_str(), 'G', mydesign.Blocks[j][curr_sp.selected[j]].width + bias_Hgraph);
            }
          }
        }
      }
    }


    // symmetry block constraint
    for (const auto& SPBlock : mydesign.SPBlocks) {
      if (SPBlock.axis_dir == placerDB::H) {
        // constraint inside one pair
        for (int i = 0; i < SPBlock.sympair.size(); i++) {
          int first_id = SPBlock.sympair[i].first, second_id = SPBlock.sympair[i].second;
          // each pair has opposite V flip
          {
            double sparserow[2] = {1, 1};
            int colno[2] = {first_id * 4 + 3, second_id * 4 + 3};
            lp_add_row(lp, 2, colno, sparserow, constrname("sp_fl_1").c_str(), 'E', 1);
          }
          // each pair has the same H flip
          {
            double sparserow[2] = {1, -1};
            int colno[2] = {first_id * 4 + 2, second_id * 4 + 2};
            lp_add_row(lp, 2, colno, sparserow, constrname("sp_fl_2").c_str(), 'E', 0);
          }
          // x center of blocks in each pair are the same
          {
            double sparserow[2] = {1, -1};
            int colno[2] = {first_id * 4, second_id * 4 };
            int first_x_center = mydesign.Blocks[first_id][curr_sp.selected[first_id]].width / 2;
            int second_x_center = mydesign.Blocks[second_id][curr_sp.selected[second_id]].width / 2;
            lp_add_row(lp, 2, colno, sparserow, "", 'E', -first_x_center + second_x_center);
          }
        }

        // constraint between two pairs
        for (int i = 0; i < SPBlock.sympair.size(); i++) {
          int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
          int i_first_y_center = mydesign.Blocks[i_first_id][curr_sp.selected[i_first_id]].height / 4;
          int i_second_y_center = mydesign.Blocks[i_second_id][curr_sp.selected[i_second_id]].height / 4;
          for (unsigned int j = i + 1; j < SPBlock.sympair.size(); j++) {
            // the y center of the two pairs are the same
            int j_first_id = SPBlock.sympair[j].first, j_second_id = SPBlock.sympair[j].second;
            int j_first_y_center = mydesign.Blocks[j_first_id][curr_sp.selected[j_first_id]].height / 4;
            int j_second_y_center = mydesign.Blocks[j_second_id][curr_sp.selected[j_second_id]].height / 4;
            double sparserow[4] = {0.5, 0.5, -0.5, -0.5};
            int colno[4] = {i_first_id * 4 + 1, i_second_id * 4 + 1, j_first_id * 4 + 1, j_second_id * 4 + 1};
            int bias = -i_first_y_center - i_second_y_center + j_first_y_center + j_second_y_center;
            lp_add_row(lp, 4, colno, sparserow, constrname("xx").c_str(), 'E', bias);
          }
        }

        // constraint between a pair and a selfsym
        for (int i = 0; i < SPBlock.sympair.size(); i++) {
          int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
          int i_first_y_center = mydesign.Blocks[i_first_id][curr_sp.selected[i_first_id]].height / 4;
          int i_second_y_center = mydesign.Blocks[i_second_id][curr_sp.selected[i_second_id]].height / 4;
          for (unsigned int j = 0; j < SPBlock.selfsym.size(); j++) {
            // the y center of the pair and the selfsym are the same
            int j_id = SPBlock.selfsym[j].first;
            int j_y_center = mydesign.Blocks[j_id][curr_sp.selected[j_id]].height / 2;
            double sparserow[3] = {0.5, 0.5, -1};
            int colno[3] = {i_first_id * 4 + 1, i_second_id * 4 + 1, j_id * 4 + 1};
            int bias = -i_first_y_center - i_second_y_center + j_y_center;
            lp_add_row(lp, 3, colno, sparserow, constrname("xx").c_str(), 'E', bias);
          }
        }

        // constraint between two selfsyms
        for (int i = 0; i < SPBlock.selfsym.size(); i++) {
          int i_id = SPBlock.selfsym[i].first;
          int i_y_center = mydesign.Blocks[i_id][curr_sp.selected[i_id]].height / 2;
          for (unsigned int j = i + 1; j < SPBlock.selfsym.size(); j++) {
            // the y center of the two selfsyms are the same
            int j_id = SPBlock.selfsym[j].first;
            int j_y_center = mydesign.Blocks[j_id][curr_sp.selected[j_id]].height / 2;
            double sparserow[2] = {1, -1};
            int colno[2] = {i_id * 4 + 1, j_id * 4 + 1};
            int bias = -i_y_center + j_y_center;
            lp_add_row(lp, 2, colno, sparserow, constrname("xx").c_str(), 'E', bias);
          }
        }
      } else {
        // axis_dir==V
        // constraint inside one pair
        for (int i = 0; i < SPBlock.sympair.size(); i++) {
          int first_id = SPBlock.sympair[i].first, second_id = SPBlock.sympair[i].second;
          // each pair has opposite H flip
          {
            double sparserow[2] = {1, 1};
            int colno[2] = {first_id * 4 + 2, second_id * 4 + 2};
            lp_add_row(lp, 2, colno, sparserow, constrname("sp_fl_3").c_str(), 'E', 1);
          }
          // each pair has the same V flip
          {
            double sparserow[2] = {1, -1};
            int colno[2] = {first_id * 4 + 3, second_id * 4 + 3};
            lp_add_row(lp, 2, colno, sparserow, constrname("sp_fl_4").c_str(), 'E', 0);
          }
          // y center of blocks in each pair are the same
          {
            double sparserow[2] = {1, -1};
            int colno[2] = {first_id * 4 + 1, second_id * 4 + 1};
            int first_y_center = mydesign.Blocks[first_id][curr_sp.selected[first_id]].height / 2;
            int second_y_center = mydesign.Blocks[second_id][curr_sp.selected[second_id]].height / 2;
            lp_add_row(lp, 2, colno, sparserow, constrname("xx").c_str(), 'E', -first_y_center + second_y_center);
          }
        }

        // constraint between two pairs
        for (int i = 0; i < SPBlock.sympair.size(); i++) {
          int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
          int i_first_x_center = mydesign.Blocks[i_first_id][curr_sp.selected[i_first_id]].width / 4;
          int i_second_x_center = mydesign.Blocks[i_second_id][curr_sp.selected[i_second_id]].width / 4;
          for (unsigned int j = i + 1; j < SPBlock.sympair.size(); j++) {
            // the x center of the two pairs are the same
            int j_first_id = SPBlock.sympair[j].first, j_second_id = SPBlock.sympair[j].second;
            int j_first_x_center = mydesign.Blocks[j_first_id][curr_sp.selected[j_first_id]].width / 4;
            int j_second_x_center = mydesign.Blocks[j_second_id][curr_sp.selected[j_second_id]].width / 4;
            double sparserow[4] = {0.5, 0.5, -0.5, -0.5};
            int colno[4] = {i_first_id * 4, i_second_id * 4, j_first_id * 4, j_second_id * 4};
            int bias = -i_first_x_center - i_second_x_center + j_first_x_center + j_second_x_center;
            lp_add_row(lp, 4, colno, sparserow, constrname("xx").c_str(), 'E', bias);
          }
        }

        // constraint between a pair and a selfsym
        for (int i = 0; i < SPBlock.sympair.size(); i++) {
          int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
          int i_first_x_center = mydesign.Blocks[i_first_id][curr_sp.selected[i_first_id]].width / 4;
          int i_second_x_center = mydesign.Blocks[i_second_id][curr_sp.selected[i_second_id]].width / 4;
          for (unsigned int j = 0; j < SPBlock.selfsym.size(); j++) {
            // the x center of the pair and the selfsym are the same
            int j_id = SPBlock.selfsym[j].first;
            int j_x_center = mydesign.Blocks[j_id][curr_sp.selected[j_id]].width / 2;
            double sparserow[3] = {0.5, 0.5, -1};
            int colno[3] = {i_first_id * 4 , i_second_id * 4 , j_id * 4};
            int bias = -i_first_x_center - i_second_x_center + j_x_center;
            lp_add_row(lp, 3, colno, sparserow, constrname("xx").c_str(), 'E', bias);
          }
        }

        // constraint between two selfsyms
        for (int i = 0; i < SPBlock.selfsym.size(); i++) {
          int i_id = SPBlock.selfsym[i].first;
          int i_x_center = mydesign.Blocks[i_id][curr_sp.selected[i_id]].width / 2;
          for (unsigned int j = i + 1; j < SPBlock.selfsym.size(); j++) {
            // the x center of the two selfsyms are the same
            int j_id = SPBlock.selfsym[j].first;
            int j_x_center = mydesign.Blocks[j_id][curr_sp.selected[j_id]].width / 2;
            double sparserow[2] = {1, -1};
            int colno[2] = {i_id * 4 + 0, j_id * 4 + 0};
            int bias = -i_x_center + j_x_center;
            lp_add_row(lp, 2, colno, sparserow, constrname("xx").c_str(), 'E', bias);
          }
        }
      }
    }

    // align block constraint
    for (const auto& alignment_unit : mydesign.Align_blocks) {
      for (unsigned int j = 0; j < alignment_unit.blocks.size() - 1; j++) {
        int first_id = alignment_unit.blocks[j], second_id = alignment_unit.blocks[j + 1];
        if (alignment_unit.horizon == 1) {
          if (alignment_unit.line == 0) {
            // align to bottom
            double sparserow[2] = {1, -1};
            int colno[2] = {first_id * 4 + 1, second_id * 4 + 1};
            lp_add_row(lp, 2, colno, sparserow, constrname("xx").c_str(), 'E', 0);
          } else if (alignment_unit.line == 1) {
            // align center y
            double sparserow[2] = {1, -1};
            int colno[2] = {first_id * 4 + 1, second_id * 4 + 1};
            int bias = -mydesign.Blocks[first_id][curr_sp.selected[first_id]].height / 2 + mydesign.Blocks[second_id][curr_sp.selected[second_id]].height / 2;
            lp_add_row(lp, 2, colno, sparserow, constrname("xx").c_str(), 'E', bias);
          } else {
            // align to top
            double sparserow[2] = {1, -1};
            int colno[2] = {first_id * 4 + 1, second_id * 4 + 1};
            int bias = -mydesign.Blocks[first_id][curr_sp.selected[first_id]].height + mydesign.Blocks[second_id][curr_sp.selected[second_id]].height;
            lp_add_row(lp, 2, colno, sparserow, constrname("xx").c_str(), 'E', bias);
          }
        } else {
          if (alignment_unit.line == 0) {
            // align to left
            double sparserow[2] = {1, -1};
            int colno[2] = {first_id * 4, second_id * 4};
            lp_add_row(lp, 2, colno, sparserow, constrname("xx").c_str(), 'E', 0);
          } else if (alignment_unit.line == 1) {
            // align center x
            double sparserow[2] = {1, -1};
            int colno[2] = {first_id * 4, second_id * 4};
            int bias = -mydesign.Blocks[first_id][curr_sp.selected[first_id]].width / 2 + mydesign.Blocks[second_id][curr_sp.selected[second_id]].width / 2;
            lp_add_row(lp, 2, colno, sparserow, constrname("xx").c_str(), 'E', bias);
          } else {
            // align to right
            double sparserow[2] = {1, -1};
            int colno[2] = {first_id * 4, second_id * 4 };
            int bias = -mydesign.Blocks[first_id][curr_sp.selected[first_id]].width + mydesign.Blocks[second_id][curr_sp.selected[second_id]].width;
            lp_add_row(lp, 2, colno, sparserow, constrname("xx").c_str(), 'E', bias);
          }
        }
      }
    }
    for (unsigned int i = 0; i < mydesign.Nets.size(); i++) {
      if (mydesign.Nets[i].connected.size() < 2) continue;

      int ind = int(mydesign.Blocks.size() + i) * 4;
      for (unsigned int j = 0; j < mydesign.Nets[i].connected.size(); j++) {
        if (mydesign.Nets[i].connected[j].type == placerDB::Block) {
          const int block_id = mydesign.Nets[i].connected[j].iter2;
          const int pin_id = mydesign.Nets[i].connected[j].iter;
          const auto& blk = mydesign.Blocks[block_id][curr_sp.selected[block_id]];
          int pin_llx = blk.width / 2,  pin_urx = blk.width / 2;
          int pin_lly = blk.height / 2, pin_ury = blk.height / 2;
          if (blk.blockPins.size()) {
            pin_llx = blk.blockPins[pin_id].bbox.LL.x;
            pin_lly = blk.blockPins[pin_id].bbox.LL.y;
            pin_urx = blk.blockPins[pin_id].bbox.UR.x;
            pin_ury = blk.blockPins[pin_id].bbox.UR.y;
          }
          double deltax = 1.*(blk.width  - pin_llx - pin_urx);
          double deltay = 1.*(blk.height - pin_lly - pin_ury);
          {
            double sparserow[3] = {1,                deltax,           -1};
            int    colno[3]     = {block_id * 4 + 0, block_id * 4 + 2, ind};
            lp_add_row(lp, 3, colno, sparserow, constrname("xx").c_str(), 'G', -pin_llx);
          }
          {
            double sparserow[3] = {1,                deltay,           -1};
            int    colno[3]     = {block_id * 4 + 1, block_id * 4 + 3, ind + 1};
            lp_add_row(lp, 3, colno, sparserow, constrname("xx").c_str(), 'G', -pin_lly);
          }
          {
            double sparserow[3] = {1,                deltax,           -1};
            int    colno[3]     = {block_id * 4 + 0, block_id * 4 + 2, ind + 2};
            lp_add_row(lp, 3, colno, sparserow, constrname("xx").c_str(), 'L', -pin_urx);
          }
          {
            double sparserow[3] = {1,                deltay,           -1};
            int    colno[3]     = {block_id * 4 + 1, block_id * 4 + 3, ind + 3};
            lp_add_row(lp, 3, colno, sparserow, constrname("xx").c_str(), 'L', -pin_ury);
          }
        }
      }
    }
  }

  {
    TimeMeasure tmsol(const_cast<design&>(mydesign).ilp_solve_runtime);
    static int fail_cnt{0};
    static std::string block_name;
    if (block_name != mydesign.name) {
      fail_cnt = 0;
      block_name = mydesign.name;
    }
    lp_set_parallel(lp, 1);
    lp_set_max_seconds(lp, 10);
    lp_set_print_messages(lp, 0);
    int status = lp_optimize(lp);

    if (status != 0 && status != 3) {
      {
        TimeMeasure tmsol(const_cast<design&>(mydesign).ilp_dm_runtime);
        lp_free(&lp);
      }
      //logger->info("ilp failed");
      return false;
    }
  }
  //if (fail_cnt++ < 100) {
  //  logger->info("writing {0}", (mydesign.name + "_ilp_" + std::to_string(fail_cnt) + ".lp"));
  //  Cbc_writeLp(lp, const_cast<char*>((mydesign.name + "_ilp_" + std::to_string(fail_cnt) + ".lp").c_str()));
  //}
  {
    const double* solution = lp_x(lp);
    //int numberColumns = Cbc_getNumCols(lp);
    //for (int iColumn=0;iColumn<numberColumns;iColumn++) {
    //  double value=solution[iColumn];
    //  if (Cbc_isInteger(lp, iColumn))
    //    logger->info("col : {0} {1}", iColumn, value);
    //}

    int minx(INT_MAX), miny(INT_MAX);
    for (int i = 0; i < mydesign.Blocks.size(); i++) {
      Blocks[i].x = solution[i * 4];
      Blocks[i].y = solution[i * 4 + 1];
      minx = std::min(minx, Blocks[i].x);
      miny = std::min(miny, Blocks[i].y);
      Blocks[i].H_flip = solution[i * 4 + 2];
      Blocks[i].V_flip = solution[i * 4 + 3];
      //logger->info("block : {0} {1} {2} {3} {4} {5} {6}", mydesign.Blocks[i][0].name, Blocks[i].x, Blocks[i].y, Blocks[i].H_flip, Blocks[i].V_flip, solution[i*4], solution[i*4 + 1]);
    }
    for (int i = 0; i < mydesign.Blocks.size(); i++) {
      Blocks[i].x -= minx;
      Blocks[i].y -= miny;
    }
    // calculate HPWL from ILP solution
    HPWL_ILP = 0.;
    for (int i = 0; i < mydesign.Nets.size(); ++i) {
      int ind = (int(mydesign.Blocks.size()) + i) * 4;
      HPWL_ILP += (solution[ind + 3] + solution[ind + 2] - solution[ind + 1] - solution[ind]);
    }
    {
      TimeMeasure tmsol(const_cast<design&>(mydesign).ilp_dm_runtime);
      lp_free(&lp);
    }
  }
  return true;
}

bool ILP_solver::MoveBlocksUsingSlack(const std::vector<Block>& blockslocal, const design& mydesign, const SeqPair& curr_sp, const PnRDB::Drc_info& drcInfo) {
  std::vector<placerDB::point> slackxy(Blocks.size());
  for (unsigned i = 0; i < Blocks.size(); ++i) {
    slackxy[i].x = Blocks[i].x - blockslocal[i].x;
    slackxy[i].y = Blocks[i].y - blockslocal[i].y;
    if (slackxy[i].x < 0 || slackxy[i].y < 0) return false;
  }
  for (const auto& SPBlock : mydesign.SPBlocks) {
    int minslack(INT_MAX);
    if (SPBlock.axis_dir == placerDB::H) {
      for (const auto& sp : SPBlock.sympair) {
        minslack = std::min(slackxy[sp.first].x,  minslack);
        minslack = std::min(slackxy[sp.second].x, minslack);
      }
      for (const auto& ss : SPBlock.selfsym) {
        minslack = std::min(slackxy[ss.first].x,  minslack);
      }
      if (minslack != INT_MAX) {
        for (const auto& sp : SPBlock.sympair) {
          slackxy[sp.first].x  = minslack;
          slackxy[sp.second].x = minslack;
        }
        for (const auto& ss : SPBlock.selfsym) {
          slackxy[ss.first].x = minslack;
        }
      }
    } else {
      for (const auto& sp : SPBlock.sympair) {
        minslack = std::min(slackxy[sp.first].y,  minslack);
        minslack = std::min(slackxy[sp.second].y, minslack);
      }
      for (const auto& ss : SPBlock.selfsym) {
        minslack = std::min(slackxy[ss.first].y,  minslack);
      }
      if (minslack != INT_MAX) {
        for (const auto& sp : SPBlock.sympair) {
          slackxy[sp.first].y  = minslack;
          slackxy[sp.second].y = minslack;
        }
        for (const auto& ss : SPBlock.selfsym) {
          slackxy[ss.first].y = minslack;
        }
      }
    }
  }
  for (const auto& align : mydesign.Align_blocks) {
    int minslack(INT_MAX);
    if (align.horizon) {
      for (const auto& blk : align.blocks) {
        minslack = std::min(slackxy[blk].y,  minslack);
      }
      if (minslack != INT_MAX) {
        for (const auto& blk : align.blocks) {
          slackxy[blk].y = minslack;
        }
      }
    } else {
      for (const auto& blk : align.blocks) {
        minslack = std::min(slackxy[blk].x,  minslack);
      }
      if (minslack != INT_MAX) {
        for (const auto& blk : align.blocks) {
          slackxy[blk].x = minslack;
        }
      }
    }
  }
  std::vector<placerDB::point> blockpts(Blocks.size());
  for (unsigned i = 0; i < Blocks.size(); ++i) {
    blockpts[i].x = (Blocks[i].x - slackxy[i].x/2);
    blockpts[i].y = (Blocks[i].y - slackxy[i].y/2);
  }
  if (!FrameSolveILP(mydesign, curr_sp, drcInfo, true, &blockpts)) return false;
  return true;
}

double ILP_solver::GenerateValidSolution(const design& mydesign, const SeqPair& curr_sp, const PnRDB::Drc_info& drcInfo) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.GenerateValidSolution");

  int v_metal_index = -1;
  int h_metal_index = -1;
  for (unsigned int i = 0; i < drcInfo.Metal_info.size(); ++i) {
    if (drcInfo.Metal_info[i].direct == 0) {
      v_metal_index = i;
      break;
    }
  }
  for (unsigned int i = 0; i < drcInfo.Metal_info.size(); ++i) {
    if (drcInfo.Metal_info[i].direct == 1) {
      h_metal_index = i;
      break;
    }
  }
  x_pitch = drcInfo.Metal_info[v_metal_index].grid_unit_x;
  y_pitch = drcInfo.Metal_info[h_metal_index].grid_unit_y;
  if (mydesign.Blocks.empty()) return -1;
  ++const_cast<design&>(mydesign)._totalNumCostCalc;
  if (mydesign.Blocks.size() > 1) {
    if (mydesign.leftAlign()) {
      // frame and solve ILP to flush bottom/left
      if (!FrameSolveILP(mydesign, curr_sp, drcInfo, true))  return -1;
    } else if (mydesign.rightAlign()) {
      if (!FrameSolveILP(mydesign, curr_sp, drcInfo, false)) return -1;
    } else {
      if (!FrameSolveILP(mydesign, curr_sp, drcInfo, true))  return -1;
      std::vector<Block> blockslocal{Blocks};
      // frame and solve ILP to flush top/right
      if (!FrameSolveILP(mydesign, curr_sp, drcInfo, false) 
          || !MoveBlocksUsingSlack(blockslocal, mydesign, curr_sp, drcInfo)) {
        // if unable to solve flush top/right or if the solution changed significantly,
        // use the bottom/left flush solution
        Blocks = blockslocal;
      }
    }
  } else {
    Blocks[0].x = 0;
    Blocks[0].y = 0;
  }

  TimeMeasure tm(const_cast<design&>(mydesign).gen_valid_runtime);
  // snap up coordinates to grid
  for (unsigned i = 0; i < mydesign.Blocks.size(); i++) {
    roundup(Blocks[i].x, x_pitch);
    roundup(Blocks[i].y, y_pitch);
  }

  // calculate LL and UR
  LL.x = INT_MAX, LL.y = INT_MAX;
  UR.x = INT_MIN, UR.y = INT_MIN;
  for (int i = 0; i < mydesign.Blocks.size(); i++) {
    LL.x = std::min(LL.x, Blocks[i].x);
    LL.y = std::min(LL.y, Blocks[i].y);
    UR.x = std::max(UR.x, Blocks[i].x + mydesign.Blocks[i][curr_sp.selected[i]].width);
    UR.y = std::max(UR.y, Blocks[i].y + mydesign.Blocks[i][curr_sp.selected[i]].height);
  }
  // calculate area
  area = double(UR.x - LL.x) * double(UR.y - LL.y);
  // calculate norm area
  area_norm = area * 0.1 / mydesign.GetMaxBlockAreaSum();
  // calculate ratio
  // ratio = std::max(double(UR.x - LL.x) / double(UR.y - LL.y), double(UR.y - LL.y) / double(UR.x - LL.x));
  ratio = double(UR.x - LL.x) / double(UR.y - LL.y);
  if (ratio < Aspect_Ratio[0] || ratio > Aspect_Ratio[1]) {
    ++const_cast<design&>(mydesign)._infeasAspRatio;
    return -1;
  }
  if (placement_box[0] > 0 && (UR.x - LL.x > placement_box[0]) || placement_box[1] > 0 && (UR.y - LL.y > placement_box[1])) {
    ++const_cast<design&>(mydesign)._infeasPlBound;
    return -1;
  }
  // calculate HPWL
  HPWL = 0;
  HPWL_extend = 0;
  HPWL_extend_terminal = 0;
  for (const auto& neti : mydesign.Nets) {
    int HPWL_min_x = UR.x, HPWL_min_y = UR.y, HPWL_max_x = 0, HPWL_max_y = 0;
    int HPWL_extend_min_x = UR.x, HPWL_extend_min_y = UR.y, HPWL_extend_max_x = 0, HPWL_extend_max_y = 0;
    for (const auto& connectedj : neti.connected) {
      if (connectedj.type == placerDB::Block) {
        int iter2 = connectedj.iter2, iter = connectedj.iter;
        for (const auto& centerk : mydesign.Blocks[iter2][curr_sp.selected[iter2]].blockPins[iter].center) {
          // calculate contact center
          int pin_x = centerk.x;
          int pin_y = centerk.y;
          if (Blocks[iter2].H_flip) pin_x = mydesign.Blocks[iter2][curr_sp.selected[iter2]].width - pin_x;
          if (Blocks[iter2].V_flip) pin_y = mydesign.Blocks[iter2][curr_sp.selected[iter2]].height - pin_y;
          pin_x += Blocks[iter2].x;
          pin_y += Blocks[iter2].y;
          HPWL_min_x = std::min(HPWL_min_x, pin_x);
          HPWL_max_x = std::max(HPWL_max_x, pin_x);
          HPWL_min_y = std::min(HPWL_min_y, pin_y);
          HPWL_max_y = std::max(HPWL_max_y, pin_y);
        }
        /*int pin_llx = mydesign.Blocks[iter2][curr_sp.selected[iter2]].blockPins[iter].bbox.LL.x;
        int pin_lly = mydesign.Blocks[iter2][curr_sp.selected[iter2]].blockPins[iter].bbox.LL.y;
        int pin_urx = mydesign.Blocks[iter2][curr_sp.selected[iter2]].blockPins[iter].bbox.UR.x;
        int pin_ury = mydesign.Blocks[iter2][curr_sp.selected[iter2]].blockPins[iter].bbox.UR.y;
        if (Blocks[iter2].H_flip) {
          pin_llx = mydesign.Blocks[iter2][curr_sp.selected[iter2]].width -
            mydesign.Blocks[iter2][curr_sp.selected[iter2]].blockPins[iter].bbox.UR.x;
          pin_urx = mydesign.Blocks[iter2][curr_sp.selected[iter2]].width -
            mydesign.Blocks[iter2][curr_sp.selected[iter2]].blockPins[iter].bbox.LL.x;
        }
        if (Blocks[iter2].V_flip) {
          pin_lly = mydesign.Blocks[iter2][curr_sp.selected[iter2]].height -
            mydesign.Blocks[iter2][curr_sp.selected[iter2]].blockPins[iter].bbox.UR.y;
          pin_ury = mydesign.Blocks[iter2][curr_sp.selected[iter2]].height -
            mydesign.Blocks[iter2][curr_sp.selected[iter2]].blockPins[iter].bbox.LL.y;
        }
        pin_llx += Blocks[iter2].x;
        pin_urx += Blocks[iter2].x;
        pin_lly += Blocks[iter2].y;
        pin_ury += Blocks[iter2].y;
        HPWL_extend_min_x = std::min(HPWL_extend_min_x, pin_llx);
        HPWL_extend_max_x = std::max(HPWL_extend_max_x, pin_urx);
        HPWL_extend_min_y = std::min(HPWL_extend_min_y, pin_lly);
        HPWL_extend_max_y = std::max(HPWL_extend_max_y, pin_ury);*/
        for (const auto& boundaryk : mydesign.Blocks[iter2][curr_sp.selected[iter2]].blockPins[iter].boundary) {
          int pin_llx = boundaryk.polygon[0].x, pin_urx = boundaryk.polygon[2].x;
          int pin_lly = boundaryk.polygon[0].y, pin_ury = boundaryk.polygon[2].y;
          if (Blocks[iter2].H_flip) {
            pin_llx = mydesign.Blocks[iter2][curr_sp.selected[iter2]].width - boundaryk.polygon[2].x;
            pin_urx = mydesign.Blocks[iter2][curr_sp.selected[iter2]].width - boundaryk.polygon[0].x;
          }
          if (Blocks[iter2].V_flip) {
            pin_lly = mydesign.Blocks[iter2][curr_sp.selected[iter2]].height - boundaryk.polygon[2].y;
            pin_ury = mydesign.Blocks[iter2][curr_sp.selected[iter2]].height - boundaryk.polygon[0].y;
          }
          pin_llx += Blocks[iter2].x;
          pin_urx += Blocks[iter2].x;
          pin_lly += Blocks[iter2].y;
          pin_ury += Blocks[iter2].y;
          HPWL_extend_min_x = std::min(HPWL_extend_min_x, pin_llx);
          HPWL_extend_max_x = std::max(HPWL_extend_max_x, pin_urx);
          HPWL_extend_min_y = std::min(HPWL_extend_min_y, pin_lly);
          HPWL_extend_max_y = std::max(HPWL_extend_max_y, pin_ury);
        }
      }
    }
    HPWL += (HPWL_max_y - HPWL_min_y) + (HPWL_max_x - HPWL_min_x);
    HPWL_extend += (HPWL_extend_max_y - HPWL_extend_min_y) + (HPWL_extend_max_x - HPWL_extend_min_x);
    bool is_terminal_net = false;
    for (const auto& c : neti.connected) {
      if (c.type == placerDB::Terminal) {
        is_terminal_net = true;
        break;
      }
    }
    if (is_terminal_net) HPWL_extend_terminal += (HPWL_extend_max_y - HPWL_extend_min_y) + (HPWL_extend_max_x - HPWL_extend_min_x);
  }

  // HPWL norm
  if (!mydesign.Nets.empty()) HPWL_norm = HPWL_extend / mydesign.GetMaxBlockHPWLSum() / double(mydesign.Nets.size());
  // calculate linear constraint
  linear_const = 0;
  std::vector<std::vector<double>> feature_value;
  for (const auto& neti : mydesign.Nets) {
    std::vector<std::vector<placerDB::point>> center_points;
    for (const auto& connectedj : neti.connected) {
      if (connectedj.type == placerDB::Block) {
        std::vector<placerDB::point> pos;
        for (const auto& ci : mydesign.Blocks[connectedj.iter2][curr_sp.selected[connectedj.iter2]].blockPins[connectedj.iter].center) {
          placerDB::point newp;
          newp.x = ci.x;
          newp.y = ci.y;
          if (Blocks[connectedj.iter2].H_flip) newp.x = mydesign.Blocks[connectedj.iter2][curr_sp.selected[connectedj.iter2]].width - newp.x;
          if (Blocks[connectedj.iter2].V_flip) newp.y = mydesign.Blocks[connectedj.iter2][curr_sp.selected[connectedj.iter2]].height - newp.y;
          newp.x += Blocks[connectedj.iter2].x;
          newp.y += Blocks[connectedj.iter2].y;
          pos.push_back(newp);
        }
        center_points.push_back(pos);
      } else if (connectedj.type == placerDB::Terminal) {
        center_points.push_back({mydesign.Terminals[connectedj.iter].center});
      }
    }
    std::vector<double> temp_feature = Calculate_Center_Point_feature(center_points);
    feature_value.push_back(temp_feature);
    double temp_sum = 0;
    for (int j = 0; j < neti.connected.size(); j++) temp_sum += neti.connected[j].alpha * temp_feature[j];
    temp_sum = std::max(temp_sum - neti.upperBound, double(0));
    linear_const += temp_sum;
  }

  if (!mydesign.Nets.empty()) linear_const /= (mydesign.GetMaxBlockHPWLSum() * double(mydesign.Nets.size()));

  // calculate multi linear constraint
  multi_linear_const = 0;
  for (const auto& constrainti : mydesign.ML_Constraints) {
    double temp_sum = 0;
    for (const auto& constraintj : constrainti.Multi_linearConst) {
      for (int k = 0; k < constraintj.pins.size(); k++) {
        int index_i = 0;
        int index_j = 0;
        for (int m = 0; m < mydesign.Nets.size(); m++) {
          for (int n = 0; n < mydesign.Nets[m].connected.size(); n++) {
            if (mydesign.Nets[m].connected[n].iter2 == constraintj.pins[k].first && mydesign.Nets[m].connected[n].iter == constraintj.pins[k].second) {
              index_i = m;
              index_j = n;
              break;
            }
          }
        }
        temp_sum += constraintj.alpha[k] * feature_value[index_i][index_j];
      }
    }
    temp_sum = std::min(temp_sum, constrainti.upperBound);
    multi_linear_const += temp_sum;
  }

  double calculated_cost = CalculateCost(mydesign, curr_sp);
  cost = calculated_cost;
  if (cost >= 0.) {
    logger->debug("ILP__HPWL_compare : HPWL_extend={0} HPWL_ILP={1}", HPWL_extend, HPWL_ILP);
  }
  return calculated_cost;
}

double ILP_solver::GenerateValidSolution_select(design& mydesign, SeqPair& curr_sp, PnRDB::Drc_info& drcInfo) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.GenerateValidSolution_select");

  int v_metal_index = -1;
  int h_metal_index = -1;
  for (unsigned int i = 0; i < drcInfo.Metal_info.size(); ++i) {
    if (drcInfo.Metal_info[i].direct == 0) {
      v_metal_index = i;
      break;
    }
  }
  for (unsigned int i = 0; i < drcInfo.Metal_info.size(); ++i) {
    if (drcInfo.Metal_info[i].direct == 1) {
      h_metal_index = i;
      break;
    }
  }
  x_pitch = drcInfo.Metal_info[v_metal_index].grid_unit_x;
  y_pitch = drcInfo.Metal_info[h_metal_index].grid_unit_y;

  // each block has 6+ vars, x, y, H_flip, V_flip, width, height + nvariant;
  unsigned int N_var = mydesign.Blocks.size() * 6 + mydesign.Nets.size() * 2;
  vector<unsigned int> select_begin_id(mydesign.Blocks.size(), 0);  // begin id of select in var
  vector<unsigned int> pin_pos_begin_id(mydesign.Blocks.size());    // begin id of pin position in var
  vector<unsigned int> pin_aux_begin_id(mydesign.Blocks.size());    // begin id of pin auxiliary in var
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    select_begin_id[i] = N_var + 1;
    N_var += mydesign.Blocks[i].size();
  }
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    pin_pos_begin_id[i] = N_var + 1;
    N_var += mydesign.Blocks[i][0].blockPins.size() * 2;
  }
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    pin_aux_begin_id[i] = N_var + 1;
    N_var += mydesign.Blocks[i][0].blockPins.size() * 4;
  }
  // i*6+1:x
  // i*6+2:y
  // i*6+3:H_flip
  // i*6+4:V_flip
  // i*6+5:width
  // i*6+6:height
  lprec* lp = make_lp(0, N_var);
  set_verbose(lp, CRITICAL);
  put_logfunc(lp, &ILP_solver::lpsolve_logger, NULL);
  // set_outputfile(lp, const_cast<char*>("/dev/null"));

  int Mwidth = 0, Mheight = 0;
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    for (unsigned int j = 0; j < mydesign.Blocks[i].size(); j++) {
      Mwidth = std::max(Mwidth, mydesign.Blocks[i][j].width);
      Mheight = std::max(Mheight, mydesign.Blocks[i][j].height);
    }
  }

  // set integer constraint, H_flip and V_flip can only be 0 or 1
  for (unsigned int i = 0; i < N_var; i++) {
    set_int(lp, i + 1, TRUE);
  }
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    set_binary(lp, i * 6 + 3, TRUE);
    set_binary(lp, i * 6 + 4, TRUE);
    for (unsigned int j = 0; j < mydesign.Blocks[i].size(); j++) {
      set_binary(lp, select_begin_id[i] + j, TRUE);
    }
    {
      // select of one block sum up to one
      double sparserow[mydesign.Blocks[i].size()];
      for (unsigned int j = 0; j < mydesign.Blocks[i].size(); j++) sparserow[j] = 1;
      int colno[mydesign.Blocks[i].size()];
      for (unsigned int j = 0; j < mydesign.Blocks[i].size(); j++) colno[j] = select_begin_id[i] + j;
      if (!add_constraintex(lp, mydesign.Blocks[i].size(), sparserow, colno, EQ, 1)) logger->error("error");
    }
    {
      double sparserow[mydesign.Blocks[i].size() + 1];
      int colno[mydesign.Blocks[i].size() + 1];
      // set width of a block
      for (unsigned int j = 0; j < mydesign.Blocks[i].size(); j++) sparserow[j] = mydesign.Blocks[i][j].width;
      sparserow[mydesign.Blocks[i].size()] = -1;
      for (unsigned int j = 0; j < mydesign.Blocks[i].size(); j++) colno[j] = select_begin_id[i] + j;  // select id
      colno[mydesign.Blocks[i].size()] = i * 6 + 5;                                                    // width id
      if (!add_constraintex(lp, mydesign.Blocks[i].size() + 1, sparserow, colno, EQ, 0)) logger->error("error");
      // set height of a block
      for (unsigned int j = 0; j < mydesign.Blocks[i].size(); j++) sparserow[j] = mydesign.Blocks[i][j].height;
      sparserow[mydesign.Blocks[i].size()] = -1;
      for (unsigned int j = 0; j < mydesign.Blocks[i].size(); j++) colno[j] = select_begin_id[i] + j;  // select id
      colno[mydesign.Blocks[i].size()] = i * 6 + 6;                                                    // height id
      if (!add_constraintex(lp, mydesign.Blocks[i].size() + 1, sparserow, colno, EQ, 0)) logger->error("error");
    }
    for (unsigned int k = 0; k < mydesign.Blocks[i][0].blockPins.size(); k++) {
      double sparserow[mydesign.Blocks[i].size() + 1];
      int colno[mydesign.Blocks[i].size() + 1];
      // set x of a blockpin
      for (unsigned int j = 0; j < mydesign.Blocks[i].size(); j++) sparserow[j] = mydesign.Blocks[i][j].blockPins[k].center.front().x;
      sparserow[mydesign.Blocks[i].size()] = -1;
      for (unsigned int j = 0; j < mydesign.Blocks[i].size(); j++) colno[j] = select_begin_id[i] + j;  // select id
      colno[mydesign.Blocks[i].size()] = pin_pos_begin_id[i] + 2 * k;                                  // pin x id
      if (!add_constraintex(lp, mydesign.Blocks[i].size() + 1, sparserow, colno, EQ, 0)) logger->error("error");
      // set x of a blockpin
      for (unsigned int j = 0; j < mydesign.Blocks[i].size(); j++) sparserow[j] = mydesign.Blocks[i][j].blockPins[k].center.front().y;
      sparserow[mydesign.Blocks[i].size()] = -1;
      for (unsigned int j = 0; j < mydesign.Blocks[i].size(); j++) colno[j] = select_begin_id[i] + j;  // select id
      colno[mydesign.Blocks[i].size()] = pin_pos_begin_id[i] + 2 * k + 1;                              // pin y id
      if (!add_constraintex(lp, mydesign.Blocks[i].size() + 1, sparserow, colno, EQ, 0)) logger->error("error");
    }
    for (unsigned int k = 0; k < mydesign.Blocks[i][0].blockPins.size(); k++) {
      // y1+y2=flipx*(width-pinx)+(1-flipx)*pinx
      {
        // y1<=Mwidth*flipx
        double sparserow[2] = {1, double(-Mwidth)};
        int colno[2] = {int(pin_aux_begin_id[i] + 4 * k), int(i) * 6 + 3};
        if (!add_constraintex(lp, 2, sparserow, colno, LE, 0)) logger->error("error");
      }
      {
        // y1<=width-pinx
        double sparserow[3] = {1, -1, 1};
        int colno[3] = {int(pin_aux_begin_id[i] + 4 * k), int(i) * 6 + 5, int(pin_pos_begin_id[i] + 2 * k)};
        if (!add_constraintex(lp, 3, sparserow, colno, LE, 0)) logger->error("error");
      }
      {
        // y1>=width-pinx-Mwidth*(1-flipx)
        double sparserow[4] = {1, -1, 1, double(-Mwidth)};
        int colno[4] = {int(pin_aux_begin_id[i] + 4 * k), int(i) * 6 + 5, int(pin_pos_begin_id[i] + 2 * k), int(i) * 6 + 3};
        if (!add_constraintex(lp, 4, sparserow, colno, GE, -Mwidth)) logger->error("error");
      }
      {
        // y1>=0
        double sparserow[1] = {1};
        int colno[1] = {int(pin_aux_begin_id[i] + 4 * k)};
        if (!add_constraintex(lp, 1, sparserow, colno, GE, 0)) logger->error("error");
      }
      {
        // y2<=Mwidth*(1-flipx)
        double sparserow[2] = {1, double(Mwidth)};
        int colno[2] = {int(pin_aux_begin_id[i] + 4 * k + 1), int(i) * 6 + 3};
        if (!add_constraintex(lp, 2, sparserow, colno, LE, Mwidth)) logger->error("error");
      }
      {
        // y2<=pinx
        double sparserow[2] = {1, -1};
        int colno[2] = {int(pin_aux_begin_id[i] + 4 * k + 1), int(pin_pos_begin_id[i] + 2 * k)};
        if (!add_constraintex(lp, 2, sparserow, colno, LE, 0)) logger->error("error");
      }
      {
        // y2>=pinx-Mwidth*flipx
        double sparserow[3] = {1, -1, double(Mwidth)};
        int colno[3] = {int(pin_aux_begin_id[i] + 4 * k + 1), int(pin_pos_begin_id[i] + 2 * k), int(i) * 6 + 3};
        if (!add_constraintex(lp, 3, sparserow, colno, GE, 0)) logger->error("error");
      }
      {
        // y2>=0
        double sparserow[1] = {1};
        int colno[1] = {int(pin_aux_begin_id[i] + 4 * k + 1)};
        if (!add_constraintex(lp, 1, sparserow, colno, GE, 0)) logger->error("error");
      }
      // y1+y2=flipy*(height-piny)+(1-flipy)*piny
      {
        // y1<=Mheight*flipy
        double sparserow[2] = {1, double(-Mheight)};
        int colno[2] = {int(pin_aux_begin_id[i] + 4 * k + 2), int(i) * 6 + 4};
        if (!add_constraintex(lp, 2, sparserow, colno, LE, 0)) logger->error("error");
      }
      {
        // y1<=height-piny
        double sparserow[3] = {1, -1, 1};
        int colno[3] = {int(pin_aux_begin_id[i] + 4 * k + 2), int(i) * 6 + 6, int(pin_pos_begin_id[i] + 2 * k + 1)};
        if (!add_constraintex(lp, 3, sparserow, colno, LE, 0)) logger->error("error");
      }
      {
        // y1>=height-piny-Mheight*(1-flipy)
        double sparserow[4] = {1, -1, 1, double(-Mheight)};
        int colno[4] = {int(pin_aux_begin_id[i] + 4 * k + 2), int(i) * 6 + 6, int(pin_pos_begin_id[i] + 2 * k + 1), int(i) * 6 + 4};
        if (!add_constraintex(lp, 4, sparserow, colno, GE, -Mheight)) logger->error("error");
      }
      {
        // y1>=0
        double sparserow[1] = {1};
        int colno[1] = {int(pin_aux_begin_id[i] + 4 * k + 2)};
        if (!add_constraintex(lp, 1, sparserow, colno, GE, 0)) logger->error("error");
      }
      {
        // y2<=Mheight*(1-flipy)
        double sparserow[2] = {1, double(Mheight)};
        int colno[2] = {int(pin_aux_begin_id[i] + 4 * k + 3), int(i) * 6 + 4};
        if (!add_constraintex(lp, 2, sparserow, colno, LE, Mheight)) logger->error("error");
      }
      {
        // y2<=piny
        double sparserow[2] = {1, -1};
        int colno[2] = {int(pin_aux_begin_id[i] + 4 * k + 3), int(pin_pos_begin_id[i] + 2 * k + 1)};
        if (!add_constraintex(lp, 2, sparserow, colno, LE, 0)) logger->error("error");
      }
      {
        // y2>=piny-Mheight*flipy
        double sparserow[3] = {1, -1, double(Mheight)};
        int colno[3] = {int(pin_aux_begin_id[i] + 4 * k + 3), int(pin_pos_begin_id[i] + 2 * k + 1), int(i) * 6 + 4};
        if (!add_constraintex(lp, 3, sparserow, colno, GE, 0)) logger->error("error");
      }
      {
        // y2>=0
        double sparserow[1] = {1};
        int colno[1] = {int(pin_aux_begin_id[i] + 4 * k + 3)};
        if (!add_constraintex(lp, 1, sparserow, colno, GE, 0)) logger->error("error");
      }
    }
  }

  int bias_Hgraph = mydesign.bias_Hgraph, bias_Vgraph = mydesign.bias_Vgraph;
  roundup(bias_Hgraph, x_pitch);
  roundup(bias_Vgraph, y_pitch);

  // overlap constraint
  for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) {
    int i_pos_index = find(curr_sp.posPair.begin(), curr_sp.posPair.end(), i) - curr_sp.posPair.begin();
    int i_neg_index = find(curr_sp.negPair.begin(), curr_sp.negPair.end(), i) - curr_sp.negPair.begin();
    for (unsigned int j = i + 1; j < mydesign.Blocks.size(); j++) {
      int j_pos_index = find(curr_sp.posPair.begin(), curr_sp.posPair.end(), j) - curr_sp.posPair.begin();
      int j_neg_index = find(curr_sp.negPair.begin(), curr_sp.negPair.end(), j) - curr_sp.negPair.begin();
      if (i_pos_index < j_pos_index) {
        if (i_neg_index < j_neg_index) {
          // i is left of j
          double sparserow[3] = {1, -1, 1};
          int colno[3] = {int(i) * 6 + 1, int(j) * 6 + 1, int(i) * 6 + 5};
          if (find(mydesign.Abut_Constraints.begin(), mydesign.Abut_Constraints.end(), make_pair(make_pair(int(i), int(j)), placerDB::H)) !=
              mydesign.Abut_Constraints.end()) {
            if (!add_constraintex(lp, 3, sparserow, colno, EQ, 0)) logger->error("error");
          } else if (!add_constraintex(lp, 3, sparserow, colno, LE, 0 - bias_Hgraph))
            logger->error("error");
        } else {
          // i is above j
          double sparserow[3] = {1, -1, -1};
          int colno[3] = {int(i) * 6 + 2, int(j) * 6 + 2, int(j) * 6 + 6};
          if (find(mydesign.Abut_Constraints.begin(), mydesign.Abut_Constraints.end(), make_pair(make_pair(int(i), int(j)), placerDB::V)) !=
              mydesign.Abut_Constraints.end()) {
            if (!add_constraintex(lp, 3, sparserow, colno, EQ, 0)) logger->error("error");
          } else if (!add_constraintex(lp, 3, sparserow, colno, GE, bias_Vgraph))
            logger->error("error");
        }
      } else {
        if (i_neg_index < j_neg_index) {
          // i is be low j
          double sparserow[3] = {1, -1, 1};
          int colno[3] = {int(i) * 6 + 2, int(j) * 6 + 2, int(i) * 6 + 6};
          if (find(mydesign.Abut_Constraints.begin(), mydesign.Abut_Constraints.end(), make_pair(make_pair(int(j), int(i)), placerDB::V)) !=
              mydesign.Abut_Constraints.end()) {
            if (!add_constraintex(lp, 3, sparserow, colno, EQ, 0)) logger->error("error");
          } else if (!add_constraintex(lp, 3, sparserow, colno, LE, -bias_Vgraph))
            logger->error("error");
        } else {
          // i is right of j
          double sparserow[3] = {1, -1, -1};
          int colno[3] = {int(i) * 6 + 1, int(j) * 6 + 1, int(j) * 6 + 5};
          if (find(mydesign.Abut_Constraints.begin(), mydesign.Abut_Constraints.end(), make_pair(make_pair(int(j), int(i)), placerDB::H)) !=
              mydesign.Abut_Constraints.end()) {
            if (!add_constraintex(lp, 3, sparserow, colno, EQ, 0)) logger->error("error");
          } else if (!add_constraintex(lp, 3, sparserow, colno, GE, bias_Hgraph))
            logger->error("error");
        }
      }
    }
  }

  // x>=0, y>=0
  for (const auto& id : curr_sp.negPair) {
    if (id < int(mydesign.Blocks.size())) {
      // x>=0
      {
        double sparserow[1] = {1};
        int colno[1] = {id * 6 + 1};
        if (!add_constraintex(lp, 1, sparserow, colno, GE, 0)) logger->error("error");
      }
      // y>=0
      {
        double sparserow[1] = {1};
        int colno[1] = {id * 6 + 2};
        if (!add_constraintex(lp, 1, sparserow, colno, GE, 0)) logger->error("error");
      }
    }
  }

  // symmetry block constraint
  for (const auto& SPBlock : mydesign.SPBlocks) {
    if (SPBlock.axis_dir == placerDB::H) {
      // constraint inside one pair
      for (int i = 0; i < SPBlock.sympair.size(); i++) {
        int first_id = SPBlock.sympair[i].first, second_id = SPBlock.sympair[i].second;
        // each pair has opposite V flip
        {
          double sparserow[2] = {1, 1};
          int colno[2] = {first_id * 6 + 4, second_id * 6 + 4};
          add_constraintex(lp, 2, sparserow, colno, EQ, 1);
        }
        // each pair has the same H flip
        {
          double sparserow[2] = {1, -1};
          int colno[2] = {first_id * 6 + 3, second_id * 6 + 3};
          add_constraintex(lp, 2, sparserow, colno, EQ, 0);
        }
        // x center of blocks in each pair are the same
        {
          double sparserow[4] = {1, -1, 0.5, -0.5};
          int colno[4] = {first_id * 6 + 1, second_id * 6 + 1, first_id * 6 + 5, second_id * 6 + 5};
          add_constraintex(lp, 4, sparserow, colno, EQ, 0);
        }
      }

      // constraint between two pairs
      for (int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        // int i_first_y_center = mydesign.Blocks[i_first_id][curr_sp.selected[i_first_id]].height / 4;
        // int i_second_y_center = mydesign.Blocks[i_second_id][curr_sp.selected[i_second_id]].height / 4;
        for (unsigned int j = i + 1; j < SPBlock.sympair.size(); j++) {
          // the y center of the two pairs are the same
          int j_first_id = SPBlock.sympair[j].first, j_second_id = SPBlock.sympair[j].second;
          // int j_first_y_center = mydesign.Blocks[j_first_id][curr_sp.selected[j_first_id]].height / 4;
          // int j_second_y_center = mydesign.Blocks[j_second_id][curr_sp.selected[j_second_id]].height / 4;
          double sparserow[8] = {0.5, 0.5, -0.5, -0.5, 0.25, 0.25, -0.25, -0.25};
          int colno[8] = {i_first_id * 6 + 2, i_second_id * 6 + 2, j_first_id * 6 + 2, j_second_id * 6 + 2,
                          i_first_id * 6 + 6, i_second_id * 6 + 6, j_first_id * 6 + 6, j_second_id * 6 + 6};
          // int bias = -i_first_y_center - i_second_y_center + j_first_y_center + j_second_y_center;
          add_constraintex(lp, 8, sparserow, colno, EQ, 0);
        }
      }

      // constraint between a pair and a selfsym
      for (int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        // int i_first_y_center = mydesign.Blocks[i_first_id][curr_sp.selected[i_first_id]].height / 4;
        // int i_second_y_center = mydesign.Blocks[i_second_id][curr_sp.selected[i_second_id]].height / 4;
        for (unsigned int j = 0; j < SPBlock.selfsym.size(); j++) {
          // the y center of the pair and the selfsym are the same
          int j_id = SPBlock.selfsym[j].first;
          // int j_y_center = mydesign.Blocks[j_id][curr_sp.selected[j_id]].height / 2;
          double sparserow[6] = {0.5, 0.5, -1, 0.25, 0.25, -0.5};
          int colno[6] = {i_first_id * 6 + 2, i_second_id * 6 + 2, j_id * 6 + 2, i_first_id * 6 + 6, i_second_id * 6 + 6, j_id * 6 + 6};
          // int bias = -i_first_y_center - i_second_y_center + j_y_center;
          add_constraintex(lp, 6, sparserow, colno, EQ, 0);
        }
      }

      // constraint between two selfsyms
      for (int i = 0; i < SPBlock.selfsym.size(); i++) {
        int i_id = SPBlock.selfsym[i].first;
        // int i_y_center = mydesign.Blocks[i_id][curr_sp.selected[i_id]].height / 2;
        for (unsigned int j = i + 1; j < SPBlock.selfsym.size(); j++) {
          // the y center of the two selfsyms are the same
          int j_id = SPBlock.selfsym[j].first;
          // int j_y_center = mydesign.Blocks[j_id][curr_sp.selected[j_id]].height / 2;
          double sparserow[4] = {1, -1, 0.5, -0.5};
          int colno[4] = {i_id * 6 + 2, j_id * 6 + 2, i_id * 6 + 6, j_id * 6 + 6};
          // int bias = -i_y_center + j_y_center;
          add_constraintex(lp, 4, sparserow, colno, EQ, 0);
        }
      }
    } else {
      // axis_dir==V
      // constraint inside one pair
      for (int i = 0; i < SPBlock.sympair.size(); i++) {
        int first_id = SPBlock.sympair[i].first, second_id = SPBlock.sympair[i].second;
        // each pair has opposite H flip
        {
          double sparserow[2] = {1, 1};
          int colno[2] = {first_id * 6 + 3, second_id * 6 + 3};
          add_constraintex(lp, 2, sparserow, colno, EQ, 1);
        }
        // each pair has the same V flip
        {
          double sparserow[2] = {1, -1};
          int colno[2] = {first_id * 6 + 4, second_id * 6 + 4};
          add_constraintex(lp, 2, sparserow, colno, EQ, 0);
        }
        // y center of blocks in each pair are the same
        {
          double sparserow[4] = {1, -1, 0.5, -0.5};
          int colno[4] = {first_id * 6 + 2, second_id * 6 + 2, first_id * 6 + 6, second_id * 6 + 6};
          // int first_y_center = mydesign.Blocks[first_id][curr_sp.selected[first_id]].height / 2;
          // int second_y_center = mydesign.Blocks[second_id][curr_sp.selected[second_id]].height / 2;
          add_constraintex(lp, 4, sparserow, colno, EQ, 0);
        }
      }

      // constraint between two pairs
      for (int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        // int i_first_x_center = mydesign.Blocks[i_first_id][curr_sp.selected[i_first_id]].width / 4;
        // int i_second_x_center = mydesign.Blocks[i_second_id][curr_sp.selected[i_second_id]].width / 4;
        for (unsigned int j = i + 1; j < SPBlock.sympair.size(); j++) {
          // the x center of the two pairs are the same
          int j_first_id = SPBlock.sympair[j].first, j_second_id = SPBlock.sympair[j].second;
          // int j_first_x_center = mydesign.Blocks[j_first_id][curr_sp.selected[j_first_id]].width / 4;
          // int j_second_x_center = mydesign.Blocks[j_second_id][curr_sp.selected[j_second_id]].width / 4;
          double sparserow[8] = {0.5, 0.5, -0.5, -0.5, 0.25, 0.25, -0.25, -0.25};
          int colno[8] = {i_first_id * 6 + 1, i_second_id * 6 + 1, j_first_id * 6 + 1, j_second_id * 6 + 1,
                          i_first_id * 6 + 5, i_second_id * 6 + 5, j_first_id * 6 + 5, j_second_id * 6 + 5};
          // int bias = -i_first_x_center - i_second_x_center + j_first_x_center + j_second_x_center;
          add_constraintex(lp, 8, sparserow, colno, EQ, 0);
        }
      }

      // constraint between a pair and a selfsym
      for (int i = 0; i < SPBlock.sympair.size(); i++) {
        int i_first_id = SPBlock.sympair[i].first, i_second_id = SPBlock.sympair[i].second;
        // int i_first_x_center = mydesign.Blocks[i_first_id][curr_sp.selected[i_first_id]].width / 4;
        // int i_second_x_center = mydesign.Blocks[i_second_id][curr_sp.selected[i_second_id]].width / 4;
        for (unsigned int j = 0; j < SPBlock.selfsym.size(); j++) {
          // the x center of the pair and the selfsym are the same
          int j_id = SPBlock.selfsym[j].first;
          // int j_x_center = mydesign.Blocks[j_id][curr_sp.selected[j_id]].width / 2;
          double sparserow[6] = {0.5, 0.5, -1, 0.25, 0.25, -0.5};
          int colno[6] = {i_first_id * 6 + 1, i_second_id * 6 + 1, j_id * 6 + 1, i_first_id * 6 + 5, i_second_id * 6 + 5, j_id * 6 + 5};
          // int bias = -i_first_x_center - i_second_x_center + j_x_center;
          add_constraintex(lp, 6, sparserow, colno, EQ, 0);
        }
      }

      // constraint between two selfsyms
      for (int i = 0; i < SPBlock.selfsym.size(); i++) {
        int i_id = SPBlock.selfsym[i].first;
        // int i_x_center = mydesign.Blocks[i_id][curr_sp.selected[i_id]].width / 2;
        for (unsigned int j = i + 1; j < SPBlock.selfsym.size(); j++) {
          // the x center of the two selfsyms are the same
          int j_id = SPBlock.selfsym[j].first;
          // int j_x_center = mydesign.Blocks[j_id][curr_sp.selected[j_id]].width / 2;
          double sparserow[4] = {1, -1, 0.5, -0.5};
          int colno[4] = {i_id * 6 + 1, j_id * 6 + 1, i_id * 6 + 5, j_id * 6 + 5};
          // int bias = -i_x_center + j_x_center;
          add_constraintex(lp, 4, sparserow, colno, EQ, 0);
        }
      }
    }
  }

  // align block constraint
  for (const auto& alignment_unit : mydesign.Align_blocks) {
    for (unsigned int j = 0; j < alignment_unit.blocks.size() - 1; j++) {
      int first_id = alignment_unit.blocks[j], second_id = alignment_unit.blocks[j + 1];
      if (alignment_unit.horizon == 1) {
        if (alignment_unit.line == 0) {
          // align to bottom
          double sparserow[2] = {1, -1};
          int colno[2] = {first_id * 6 + 2, second_id * 6 + 2};
          add_constraintex(lp, 2, sparserow, colno, EQ, 0);
        } else if (alignment_unit.line == 1) {
          // align center y
          double sparserow[4] = {1, -1, 0.5, -0.5};
          int colno[4] = {first_id * 6 + 2, second_id * 6 + 2, first_id * 6 + 6, second_id * 6 + 6};
          // int bias = -mydesign.Blocks[first_id][curr_sp.selected[first_id]].height / 2 + mydesign.Blocks[second_id][curr_sp.selected[second_id]].height / 2;
          add_constraintex(lp, 4, sparserow, colno, EQ, 0);
        } else {
          // align to top
          double sparserow[4] = {1, -1, 1, -1};
          int colno[4] = {first_id * 6 + 2, second_id * 6 + 2, first_id * 6 + 6, second_id * 6 + 6};
          // int bias = -mydesign.Blocks[first_id][curr_sp.selected[first_id]].height + mydesign.Blocks[second_id][curr_sp.selected[second_id]].height;
          add_constraintex(lp, 4, sparserow, colno, EQ, 0);
        }
      } else {
        if (alignment_unit.line == 0) {
          // align to left
          double sparserow[2] = {1, -1};
          int colno[2] = {first_id * 6 + 1, second_id * 6 + 1};
          add_constraintex(lp, 2, sparserow, colno, EQ, 0);
        } else if (alignment_unit.line == 1) {
          // align center x
          double sparserow[4] = {1, -1, 0.5, -0.5};
          int colno[4] = {first_id * 6 + 1, second_id * 6 + 1, first_id * 6 + 5, second_id * 6 + 5};
          // int bias = -mydesign.Blocks[first_id][curr_sp.selected[first_id]].width / 2 + mydesign.Blocks[second_id][curr_sp.selected[second_id]].width / 2;
          add_constraintex(lp, 4, sparserow, colno, EQ, 0);
        } else {
          // align to right
          double sparserow[4] = {1, -1, 1, -1};
          int colno[4] = {first_id * 6 + 1, second_id * 6 + 1, first_id * 6 + 5, second_id * 6 + 5};
          // int bias = -mydesign.Blocks[first_id][curr_sp.selected[first_id]].width + mydesign.Blocks[second_id][curr_sp.selected[second_id]].width;
          add_constraintex(lp, 4, sparserow, colno, EQ, 0);
        }
      }
    }
  }

  // same template
  for (const auto& group : mydesign.Same_Template_Constraints) {
    vector<int> group_vec(group.begin(), group.end());
    for (unsigned int i = 0; i < group.size() - 1; i++) {
      for (unsigned int j = 0; j < mydesign.Blocks[group_vec[i]].size(); j++) {
        double sparserow[2] = {1, -1};
        int colno[2] = {int(select_begin_id[group_vec[i]] + j), int(select_begin_id[group_vec[i] + 1] + j)};
        add_constraintex(lp, 2, sparserow, colno, EQ, 0);
      }
    }
  }

  // set_add_rowmode(lp, FALSE);
  {
    double row[N_var + 1] = {0};
    ConstGraph const_graph;

    // add HPWL in cost
    for (int i = 0; i < mydesign.Nets.size(); i++) {
      vector<pair<int, int>> blockids;
      for (unsigned int j = 0; j < mydesign.Nets[i].connected.size(); j++) {
        if (mydesign.Nets[i].connected[j].type == placerDB::Block &&
            (blockids.size() == 0 || mydesign.Nets[i].connected[j].iter2 != curr_sp.negPair[blockids.back().first]))
          blockids.push_back(std::make_pair(find(curr_sp.negPair.begin(), curr_sp.negPair.end(), mydesign.Nets[i].connected[j].iter2) - curr_sp.negPair.begin(),
                                            mydesign.Nets[i].connected[j].iter));
      }
      if (blockids.size() < 2) continue;
      sort(blockids.begin(), blockids.end(), [](const pair<int, int>& a, const pair<int, int>& b) { return a.first <= b.first; });
    }

    // add HPWL in cost
    for (unsigned int i = 0; i < mydesign.Nets.size(); i++) {
      vector<pair<int, int>> blockids;
      /// for (int j = 0; j < mydesign.Nets[i].connected.size(); j++) {
      /// if (mydesign.Nets[i].connected[j].type == placerDB::Block &&
      ///(blockids.size() == 0 || mydesign.Nets[i].connected[j].iter2 != curr_sp.negPair[blockids.back().first]))
      /// blockids.push_back(std::make_pair(find(curr_sp.negPair.begin(), curr_sp.negPair.end(), mydesign.Nets[i].connected[j].iter2) - curr_sp.negPair.begin(),
      /// mydesign.Nets[i].connected[j].iter));
      //}
      set<pair<pair<int, int>, int>> block_pos_x_set;
      set<pair<pair<int, int>, int>> block_pos_y_set;
      for (unsigned int j = 0; j < mydesign.Nets[i].connected.size(); j++) {
        if (mydesign.Nets[i].connected[j].type == placerDB::Block) {
          block_pos_x_set.insert(
              std::make_pair(std::make_pair(mydesign.Nets[i].connected[j].iter2, mydesign.Nets[i].connected[j].iter),
                             find(curr_sp.negPair.begin(), curr_sp.negPair.end(), mydesign.Nets[i].connected[j].iter2) - curr_sp.negPair.begin()));
          block_pos_y_set.insert(
              std::make_pair(std::make_pair(mydesign.Nets[i].connected[j].iter2, mydesign.Nets[i].connected[j].iter),
                             find(curr_sp.negPair.begin(), curr_sp.negPair.end(), mydesign.Nets[i].connected[j].iter2) - curr_sp.negPair.begin()));
        }
        // blockids.push_back(std::make_pair(find(curr_sp.negPair.begin(), curr_sp.negPair.end(), mydesign.Nets[i].connected[j].iter2) -
        // curr_sp.negPair.begin(), mydesign.Nets[i].connected[j].iter));
      }
      vector<pair<pair<int, int>, int>> block_pos_x(block_pos_x_set.begin(), block_pos_x_set.end());
      vector<pair<pair<int, int>, int>> block_pos_y(block_pos_y_set.begin(), block_pos_y_set.end());
      if (block_pos_x.size() < 2) continue;
      sort(block_pos_x.begin(), block_pos_x.end(), [](const pair<pair<int, int>, int>& a, const pair<pair<int, int>, int>& b) { return a.second < b.second; });
      sort(block_pos_y.begin(), block_pos_y.end(), [](const pair<pair<int, int>, int>& a, const pair<pair<int, int>, int>& b) { return a.second < b.second; });
      // sort(blockids.begin(), blockids.end(), [](const pair<int, int>& a, const pair<int, int>& b) { return a.first <= b.first; });
      /**int LLblock_id = curr_sp.negPair[blockids.front().first], LLpin_id = blockids.front().second;
      int LLblock_width = mydesign.Blocks[LLblock_id][curr_sp.selected[LLblock_id]].width,
          LLblock_height = mydesign.Blocks[LLblock_id][curr_sp.selected[LLblock_id]].height;
      int LLpin_x = mydesign.Blocks[LLblock_id][curr_sp.selected[LLblock_id]].blockPins[LLpin_id].center.front().x,
          LLpin_y = mydesign.Blocks[LLblock_id][curr_sp.selected[LLblock_id]].blockPins[LLpin_id].center.front().y;
      int URblock_id = curr_sp.negPair[blockids.back().first], URpin_id = blockids.back().second;
      int URblock_width = mydesign.Blocks[URblock_id][curr_sp.selected[URblock_id]].width,
          URblock_height = mydesign.Blocks[URblock_id][curr_sp.selected[URblock_id]].height;
      int URpin_x = mydesign.Blocks[URblock_id][curr_sp.selected[URblock_id]].blockPins[URpin_id].center.front().x,
          URpin_y = mydesign.Blocks[URblock_id][curr_sp.selected[URblock_id]].blockPins[URpin_id].center.front().y;**/
      int Lblock_id = block_pos_x.front().first.first, Lpin_id = block_pos_x.front().first.second;
      int Rblock_id = block_pos_x.back().first.first, Rpin_id = block_pos_x.back().first.second;
      /**int Lblock_width = mydesign.Blocks[Lblock_id][curr_sp.selected[Lblock_id]].width,
          Lblock_height = mydesign.Blocks[Lblock_id][curr_sp.selected[Lblock_id]].height;
      int Rblock_width = mydesign.Blocks[Rblock_id][curr_sp.selected[Rblock_id]].width,
          Rblock_height = mydesign.Blocks[Rblock_id][curr_sp.selected[Rblock_id]].height;
      int Lpin_x = mydesign.Blocks[Lblock_id][curr_sp.selected[Lblock_id]].blockPins[Lpin_id].center.front().x,
          Lpin_y = mydesign.Blocks[Lblock_id][curr_sp.selected[Lblock_id]].blockPins[Lpin_id].center.front().y;
      int Rpin_x = mydesign.Blocks[Rblock_id][curr_sp.selected[Rblock_id]].blockPins[Rpin_id].center.front().x,
          Rpin_y = mydesign.Blocks[Rblock_id][curr_sp.selected[Rblock_id]].blockPins[Rpin_id].center.front().y;**/

      int Dblock_id = block_pos_y.front().first.first, Dpin_id = block_pos_y.front().first.second;
      int Ublock_id = block_pos_y.back().first.first, Upin_id = block_pos_y.back().first.second;
      /**int Dblock_width = mydesign.Blocks[Dblock_id][curr_sp.selected[Dblock_id]].width,
          Dblock_height = mydesign.Blocks[Dblock_id][curr_sp.selected[Dblock_id]].height;
      int Ublock_width = mydesign.Blocks[Ublock_id][curr_sp.selected[Ublock_id]].width,
          Ublock_height = mydesign.Blocks[Ublock_id][curr_sp.selected[Ublock_id]].height;
      int Dpin_x = mydesign.Blocks[Dblock_id][curr_sp.selected[Dblock_id]].blockPins[Dpin_id].center.front().x,
          Dpin_y = mydesign.Blocks[Dblock_id][curr_sp.selected[Dblock_id]].blockPins[Dpin_id].center.front().y;
      int Upin_x = mydesign.Blocks[Ublock_id][curr_sp.selected[Ublock_id]].blockPins[Upin_id].center.front().x,
          Upin_y = mydesign.Blocks[Ublock_id][curr_sp.selected[Ublock_id]].blockPins[Upin_id].center.front().y;**/

      // min abs(LLx+(LLwidth-2LLpinx)*LLHflip+LLpinx-URx-(URwidth-2URpinx)*URHflip-URpinx)=HPWLx
      //-> (LLx+(LLwidth-2LLpinx)*LLHflip+LLpinx-URx-(URwidth-2URpinx)*URHflip-URpinx)<=HPWLx
      //  -(LLx+(LLwidth-2LLpinx)*LLHflip+LLpinx-URx-(URwidth-2URpinx)*URHflip-URpinx)<=HPWLx
      //-> (LLx+(y1+y2)_LLpin-URx-(y1+y2)_URpin)<=HPWLx
      //  -(LLx+(y1+y2)_LLpin-URx-(y1+y2)_URpin)<=HPWLx
      if (Lblock_id != Rblock_id) {
        {
          double sparserow[7] = {1, 1, 1, -1, -1, -1, -1};
          int colno[7] = {Lblock_id * 6 + 1,
                          int(pin_aux_begin_id[Lblock_id] + 4 * Lpin_id),
                          int(pin_aux_begin_id[Lblock_id] + 4 * Lpin_id + 1),
                          Rblock_id * 6 + 1,
                          int(pin_aux_begin_id[Rblock_id] + 4 * Rpin_id),
                          int(pin_aux_begin_id[Rblock_id] + 4 * Rpin_id + 1),
                          int(mydesign.Blocks.size() * 6 + i * 2 + 1)};
          add_constraintex(lp, 7, sparserow, colno, LE, 0);
        }
        {
          double sparserow[7] = {-1, -1, -1, 1, 1, 1, -1};
          int colno[7] = {Lblock_id * 6 + 1,
                          int(pin_aux_begin_id[Lblock_id] + 4 * Lpin_id),
                          int(pin_aux_begin_id[Lblock_id] + 4 * Lpin_id + 1),
                          Rblock_id * 6 + 1,
                          int(pin_aux_begin_id[Rblock_id] + 4 * Rpin_id),
                          int(pin_aux_begin_id[Rblock_id] + 4 * Rpin_id + 1),
                          int(mydesign.Blocks.size() * 6 + i * 2 + 1)};
          add_constraintex(lp, 7, sparserow, colno, LE, 0);
        }
        row[mydesign.Blocks.size() * 6 + i * 2 + 1] = 1;
      }
      if (Dblock_id != Ublock_id) {
        {
          double sparserow[7] = {1, 1, 1, -1, -1, -1, -1};
          int colno[7] = {Dblock_id * 6 + 2,
                          int(pin_aux_begin_id[Dblock_id] + 4 * Dpin_id + 2),
                          int(pin_aux_begin_id[Dblock_id] + 4 * Dpin_id + 3),
                          Ublock_id * 6 + 2,
                          int(pin_aux_begin_id[Ublock_id] + 4 * Upin_id + 2),
                          int(pin_aux_begin_id[Ublock_id] + 4 * Upin_id + 3),
                          int(mydesign.Blocks.size() * 6 + i * 2 + 2)};
          add_constraintex(lp, 7, sparserow, colno, LE, 0);
        }
        {
          double sparserow[7] = {-1, -1, -1, 1, 1, 1, -1};
          int colno[7] = {Dblock_id * 6 + 2,
                          int(pin_aux_begin_id[Dblock_id] + 4 * Dpin_id + 2),
                          int(pin_aux_begin_id[Dblock_id] + 4 * Dpin_id + 3),
                          Ublock_id * 6 + 2,
                          int(pin_aux_begin_id[Ublock_id] + 4 * Upin_id + 2),
                          int(pin_aux_begin_id[Ublock_id] + 4 * Upin_id + 3),
                          int(mydesign.Blocks.size() * 6 + i * 2 + 2)};
          add_constraintex(lp, 7, sparserow, colno, LE, 0);
        }
        row[mydesign.Blocks.size() * 6 + i * 2 + 2] = const_graph.LAMBDA;
      }
    }

    // add area in cost
    int URblock_pos_id = 0, URblock_neg_id = 0;
    int estimated_width = 0, estimated_height = 0;
    for (unsigned int i = curr_sp.negPair.size() - 1; i >= 0; i--) {
      if (curr_sp.negPair[i] < int(mydesign.Blocks.size())) {
        URblock_neg_id = i;
        break;
      }
    }
    URblock_pos_id = find(curr_sp.posPair.begin(), curr_sp.posPair.end(), curr_sp.negPair[URblock_neg_id]) - curr_sp.posPair.begin();
    // estimate width
    for (int i = URblock_pos_id; i >= 0; i--) {
      if (curr_sp.posPair[i] < int(mydesign.Blocks.size())) {
        estimated_width += mydesign.Blocks[curr_sp.posPair[i]][0].width;
      }
    }
    // add estimated area
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) row[curr_sp.negPair[i] * 6 + 2] += estimated_width / 2;
    // estimate height
    for (unsigned int i = URblock_pos_id; i < curr_sp.posPair.size(); i++) {
      if (curr_sp.posPair[i] < int(mydesign.Blocks.size())) {
        estimated_height += mydesign.Blocks[curr_sp.posPair[i]][0].height;
      }
    }
    // add estimated area
    for (unsigned int i = 0; i < mydesign.Blocks.size(); i++) row[curr_sp.negPair[i] * 6 + 1] += estimated_height / 2;

    set_obj_fn(lp, row);
    set_minim(lp);
    set_timeout(lp, 1);
    set_presolve(lp, PRESOLVE_ROWS | PRESOLVE_COLS | PRESOLVE_LINDEP, get_presolveloops(lp));
    int ret = solve(lp);
    if (ret != 0 && ret != 1) {
      delete_lp(lp);
      return -1;
    }
  }

  double var[N_var];
  int Norig_columns, Norig_rows;
  REAL value;
  Norig_columns = get_Norig_columns(lp);
  Norig_rows = get_Norig_rows(lp);
  for (int i = 1; i <= Norig_columns; i++) {
    var[i - 1] = get_var_primalresult(lp, Norig_rows + i);
  }
  // get_variables(lp, var);
  delete_lp(lp);

  for (int i = 0; i < mydesign.Blocks.size(); i++) {
    Blocks[i].x = var[i * 6];
    Blocks[i].y = var[i * 6 + 1];
    roundup(Blocks[i].x, x_pitch);
    roundup(Blocks[i].y, y_pitch);
    Blocks[i].H_flip = var[i * 6 + 2];
    Blocks[i].V_flip = var[i * 6 + 3];
    for (unsigned int j = 0; j < mydesign.Blocks[i].size(); j++) {
      if (var[select_begin_id[i] - 1 + j]) {
        curr_sp.selected[i] = j;
        break;
      }
    }
  }
  /*auto hflipVec = curr_sp.GetFlip(true);
  auto vflipVec = curr_sp.GetFlip(false);
  if (!hflipVec.empty() && !vflipVec.empty()) {
    for (unsigned i = 0; i < mydesign.Blocks.size(); i++) {
      Blocks[i].H_flip = hflipVec[i];
      Blocks[i].V_flip = vflipVec[i];
    }
  }*/

  // calculate LL and UR
  LL.x = INT_MAX, LL.y = INT_MAX;
  UR.x = INT_MIN, UR.y = INT_MIN;
  for (int i = 0; i < mydesign.Blocks.size(); i++) {
    LL.x = std::min(LL.x, Blocks[i].x);
    LL.y = std::min(LL.y, Blocks[i].y);
    UR.x = std::max(UR.x, Blocks[i].x + mydesign.Blocks[i][curr_sp.selected[i]].width);
    UR.y = std::max(UR.y, Blocks[i].y + mydesign.Blocks[i][curr_sp.selected[i]].height);
  }
  // calculate area
  area = double(UR.x - LL.x) * double(UR.y - LL.y);
  // calculate norm area
  area_norm = area * 0.1 / mydesign.GetMaxBlockAreaSum();
  // calculate ratio
  // ratio = std::max(double(UR.x - LL.x) / double(UR.y - LL.y), double(UR.y - LL.y) / double(UR.x - LL.x));
  ratio = double(UR.x - LL.x) / double(UR.y - LL.y);
  if (ratio < Aspect_Ratio[0] || ratio > Aspect_Ratio[1]) return -1;
  if (placement_box[0] > 0 && (UR.x - LL.x > placement_box[0]) || placement_box[1] > 0 && (UR.y - LL.y > placement_box[1])) return -1;
  // calculate HPWL
  HPWL = 0;
  HPWL_extend = 0;
  HPWL_extend_terminal = 0;
  for (const auto& neti : mydesign.Nets) {
    int HPWL_min_x = UR.x, HPWL_min_y = UR.y, HPWL_max_x = 0, HPWL_max_y = 0;
    int HPWL_extend_min_x = UR.x, HPWL_extend_min_y = UR.y, HPWL_extend_max_x = 0, HPWL_extend_max_y = 0;
    for (const auto& connectedj : neti.connected) {
      if (connectedj.type == placerDB::Block) {
        int iter2 = connectedj.iter2, iter = connectedj.iter;
        for (const auto& centerk : mydesign.Blocks[iter2][curr_sp.selected[iter2]].blockPins[iter].center) {
          // calculate contact center
          int pin_x = centerk.x;
          int pin_y = centerk.y;
          if (Blocks[iter2].H_flip) pin_x = mydesign.Blocks[iter2][curr_sp.selected[iter2]].width - pin_x;
          if (Blocks[iter2].V_flip) pin_y = mydesign.Blocks[iter2][curr_sp.selected[iter2]].height - pin_y;
          pin_x += Blocks[iter2].x;
          pin_y += Blocks[iter2].y;
          HPWL_min_x = std::min(HPWL_min_x, pin_x);
          HPWL_max_x = std::max(HPWL_max_x, pin_x);
          HPWL_min_y = std::min(HPWL_min_y, pin_y);
          HPWL_max_y = std::max(HPWL_max_y, pin_y);
        }
        for (const auto& boundaryk : mydesign.Blocks[iter2][curr_sp.selected[iter2]].blockPins[iter].boundary) {
          int pin_llx = boundaryk.polygon[0].x, pin_urx = boundaryk.polygon[2].x;
          int pin_lly = boundaryk.polygon[0].y, pin_ury = boundaryk.polygon[2].y;
          if (Blocks[iter2].H_flip) {
            pin_llx = mydesign.Blocks[iter2][curr_sp.selected[iter2]].width - boundaryk.polygon[2].x;
            pin_urx = mydesign.Blocks[iter2][curr_sp.selected[iter2]].width - boundaryk.polygon[0].x;
          }
          if (Blocks[iter2].V_flip) {
            pin_lly = mydesign.Blocks[iter2][curr_sp.selected[iter2]].height - boundaryk.polygon[2].y;
            pin_ury = mydesign.Blocks[iter2][curr_sp.selected[iter2]].height - boundaryk.polygon[0].y;
          }
          pin_llx += Blocks[iter2].x;
          pin_urx += Blocks[iter2].x;
          pin_lly += Blocks[iter2].y;
          pin_ury += Blocks[iter2].y;
          HPWL_extend_min_x = std::min(HPWL_extend_min_x, pin_llx);
          HPWL_extend_max_x = std::max(HPWL_extend_max_x, pin_urx);
          HPWL_extend_min_y = std::min(HPWL_extend_min_y, pin_lly);
          HPWL_extend_max_y = std::max(HPWL_extend_max_y, pin_ury);
        }
      }
    }
    HPWL += (HPWL_max_y - HPWL_min_y) + (HPWL_max_x - HPWL_min_x);
    HPWL_extend += (HPWL_extend_max_y - HPWL_extend_min_y) + (HPWL_extend_max_x - HPWL_extend_min_x);
    bool is_terminal_net = false;
    for (const auto& c : neti.connected) {
      if (c.type == placerDB::Terminal) {
        is_terminal_net = true;
        break;
      }
    }
    if (is_terminal_net) HPWL_extend_terminal += (HPWL_extend_max_y - HPWL_extend_min_y) + (HPWL_extend_max_x - HPWL_extend_min_x);
  }

  // HPWL norm
  if (!mydesign.Nets.empty()) HPWL_norm = HPWL_extend / mydesign.GetMaxBlockHPWLSum() / double(mydesign.Nets.size());
  // calculate linear constraint
  linear_const = 0;
  std::vector<std::vector<double>> feature_value;
  for (const auto& neti : mydesign.Nets) {
    std::vector<std::vector<placerDB::point>> center_points;
    for (const auto& connectedj : neti.connected) {
      if (connectedj.type == placerDB::Block) {
        std::vector<placerDB::point> pos;
        for (const auto& ci : mydesign.Blocks[connectedj.iter2][curr_sp.selected[connectedj.iter2]].blockPins[connectedj.iter].center) {
          placerDB::point newp;
          newp.x = ci.x;
          newp.y = ci.y;
          if (Blocks[connectedj.iter2].H_flip) newp.x = mydesign.Blocks[connectedj.iter2][curr_sp.selected[connectedj.iter2]].width - newp.x;
          if (Blocks[connectedj.iter2].V_flip) newp.y = mydesign.Blocks[connectedj.iter2][curr_sp.selected[connectedj.iter2]].height - newp.y;
          newp.x += Blocks[connectedj.iter2].x;
          newp.y += Blocks[connectedj.iter2].y;
          pos.push_back(newp);
        }
        center_points.push_back(pos);
      } else if (connectedj.type == placerDB::Terminal) {
        center_points.push_back({mydesign.Terminals[connectedj.iter].center});
      }
    }
    std::vector<double> temp_feature = Calculate_Center_Point_feature(center_points);
    feature_value.push_back(temp_feature);
    double temp_sum = 0;
    for (int j = 0; j < neti.connected.size(); j++) temp_sum += neti.connected[j].alpha * temp_feature[j];
    temp_sum = std::max(temp_sum - neti.upperBound, double(0));
    linear_const += temp_sum;
  }

  if (!mydesign.Nets.empty()) linear_const /= (mydesign.GetMaxBlockHPWLSum() * double(mydesign.Nets.size()));

  // calculate multi linear constraint
  multi_linear_const = 0;
  for (const auto& constrainti : mydesign.ML_Constraints) {
    double temp_sum = 0;
    for (const auto& constraintj : constrainti.Multi_linearConst) {
      for (int k = 0; k < constraintj.pins.size(); k++) {
        int index_i = 0;
        int index_j = 0;
        for (int m = 0; m < mydesign.Nets.size(); m++) {
          for (int n = 0; n < mydesign.Nets[m].connected.size(); n++) {
            if (mydesign.Nets[m].connected[n].iter2 == constraintj.pins[k].first && mydesign.Nets[m].connected[n].iter == constraintj.pins[k].second) {
              index_i = m;
              index_j = n;
              break;
            }
          }
        }
        temp_sum += constraintj.alpha[k] * feature_value[index_i][index_j];
      }
    }
    temp_sum = std::min(temp_sum, constrainti.upperBound);
    multi_linear_const += temp_sum;
  }

  double calculated_cost = CalculateCost(mydesign, curr_sp);
  cost = calculated_cost;
  return calculated_cost;
}

double ILP_solver::CalculateCost(const design& mydesign) const {
  ConstGraph const_graph;
  double cost = 0;
  cost += area;
  cost += HPWL * const_graph.LAMBDA;
  double match_cost = 0;
  for (const auto& mbi : mydesign.Match_blocks) {
    match_cost +=
        abs(Blocks[mbi.blockid1].x + mydesign.Blocks[mbi.blockid1][0].width / 2 - Blocks[mbi.blockid2].x - mydesign.Blocks[mbi.blockid2][0].width / 2) +
        abs(Blocks[mbi.blockid1].y + mydesign.Blocks[mbi.blockid1][0].height / 2 - Blocks[mbi.blockid2].y - mydesign.Blocks[mbi.blockid2][0].height / 2);
  }
  cost += match_cost * const_graph.BETA;
  cost += ratio * Aspect_Ratio_weight;
  cost += 0.0 / area * const_graph.PHI;  // dead_area
  cost += linear_const * const_graph.PI;
  cost += multi_linear_const * const_graph.PII;
  return cost;
}

double ILP_solver::CalculateCost(const design& mydesign, const SeqPair& curr_sp) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.CalculateCost");

  ConstGraph const_graph;
  double cost = 0;

  if (false) {
    cost += area_norm;
    cost += HPWL_norm * const_graph.LAMBDA;
  } else {
    cost += log(area);
    if (HPWL_extend > 0) {
      cost += log(HPWL_extend) * const_graph.LAMBDA;
    }
  }

  double match_cost = 0;
  double max_dim = std::max(UR.x - LL.x, UR.y - LL.y);
  for (const auto& mbi : mydesign.Match_blocks) {
    match_cost += (abs(Blocks[mbi.blockid1].x + mydesign.Blocks[mbi.blockid1][curr_sp.selected[mbi.blockid1]].width / 2 - Blocks[mbi.blockid2].x -
                       mydesign.Blocks[mbi.blockid2][curr_sp.selected[mbi.blockid2]].width / 2) +
                   abs(Blocks[mbi.blockid1].y + mydesign.Blocks[mbi.blockid1][curr_sp.selected[mbi.blockid1]].height / 2 - Blocks[mbi.blockid2].y -
                       mydesign.Blocks[mbi.blockid2][curr_sp.selected[mbi.blockid2]].height / 2)) /
                  max_dim;
  }
  if (!mydesign.Match_blocks.empty()) match_cost /= (mydesign.Match_blocks.size());
  constraint_penalty = match_cost * const_graph.BETA + linear_const * const_graph.PI + multi_linear_const * const_graph.PII;
  cost += constraint_penalty;
  return cost;
}

void ILP_solver::WritePlacement(design& mydesign, SeqPair& curr_sp, string outfile) {
  ofstream fout;
  fout.open(outfile.c_str());
  // cout << "Placer-Info: write placement" << endl;
  fout << "# TAMU blocks 1.0" << endl << endl;
  fout << "DIE {" << LL.x << ", " << LL.y << "} {" << UR.x << "," << UR.y << "}" << endl << endl;
  for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
    string ort;
    if (!Blocks[i].H_flip && !Blocks[i].V_flip) {
      ort = "N";
    } else if (Blocks[i].H_flip && !Blocks[i].V_flip) {
      ort = "FN";
    } else if (!Blocks[i].H_flip && Blocks[i].V_flip) {
      ort = "FS";
    } else {
      ort = "S";
    }
    fout << mydesign.Blocks.at(i).back().name << "\t" << Blocks[i].x << "\t" << Blocks[i].y << "\t" << ort << endl;
  }
  fout << endl;
  for (const auto& ni : mydesign.Nets) {
    // for each pin
    for (const auto& ci : ni.connected) {
      if (ci.type == placerDB::Terminal) {
        int tno = ci.iter;
        fout << mydesign.Terminals.at(tno).name << "\t" << mydesign.Terminals.at(tno).center.x << "\t" << mydesign.Terminals.at(tno).center.y << endl;
        break;
      }
    }
  }
  fout.close();
}

void ILP_solver::PlotPlacementAnalytical(design& mydesign, string outfile, bool plot_pin, bool plot_terminal, bool plot_net) {
  // cout << "Placer-Info: create gnuplot file" << endl;
  placerDB::point p, bp;
  if (!mydesign.is_first_ILP) {
    ofstream f("Results/" + mydesign.name + "_gds/" + mydesign.name + ".csv", std::ios::app);
    if (f.is_open()) {
      f << mydesign.placement_id << " " << area << " " << HPWL << endl;
    }
    f.close();
  }

  ofstream fout;
  vector<placerDB::point> p_pin;
  fout.open(outfile.c_str());
  fout << "#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)" << endl;
  fout << "\nset title \" " << mydesign.name << " #Blocks= " << mydesign.Blocks.size() << ", #Terminals= " << mydesign.Terminals.size()
       << ", #Nets= " << mydesign.Nets.size() << ",Area=" << area << ", HPWL= " << HPWL << " \"" << endl;
  fout << "\nset nokey" << endl;
  fout << "#   Uncomment these two lines starting with \"set\"" << endl;
  fout << "#   to save an EPS file for inclusion into a latex document" << endl;
  fout << "# set terminal postscript eps color solid 20" << endl;
  fout << "# set output \"result.eps\"" << endl << endl;
  fout << "#   Uncomment these two lines starting with \"set\"" << endl;
  fout << "#   to save a PS file for printing" << endl;
  fout << "# set terminal postscript portrait color solid 20" << endl;
  fout << "# set output \"result.ps\"" << endl << endl;

  int bias = 100;
  int range = std::max(UR.x, UR.y) + bias;
  fout << "\nset xrange [" << LL.x - bias << ":" << UR.x + bias << "]" << endl;
  fout << "\nset yrange [" << LL.y - bias << ":" << UR.y + bias << "]" << endl;
  // set labels for blocks
  for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
    placerDB::point tp;
    tp.x = Blocks[i].x + mydesign.Blocks[i][0].width / 2;
    tp.y = Blocks[i].y + mydesign.Blocks[i][0].height / 2;
    if (mydesign.Blocks[i][0].width > 0 && mydesign.Blocks[i][0].height > 0)
      fout << "\nset label \"" << mydesign.Blocks[i][0].name << "\" at " << tp.x << " , " << tp.y << " center " << endl;
    if (plot_pin) {
      for (unsigned int j = 0; j < mydesign.Blocks[i][0].blockPins.size(); j++) {
        for (unsigned int k = 0; k < mydesign.Blocks[i][0].blockPins[j].center.size(); k++) {
          placerDB::point newp;
          newp.x = mydesign.Blocks[i][0].blockPins[j].center[k].x;
          newp.y = mydesign.Blocks[i][0].blockPins[j].center[k].y;
          if (Blocks[i].H_flip) newp.x = mydesign.Blocks[i][0].width - newp.x;
          if (Blocks[i].V_flip) newp.y = mydesign.Blocks[i][0].height - newp.y;
          newp.x += Blocks[i].x;
          newp.y += Blocks[i].y;
          fout << "\nset label \"" << mydesign.Blocks[i][0].blockPins[j].name << "\" at " << newp.x << " , " << newp.y << endl;
          fout << endl;
        }
      }
    }
  }

  // set labels for terminals
  // cout << "set labels for terminals..." << endl;
  if (plot_terminal) {
    for (const auto& ni : mydesign.Nets) {
      // for each pin
      for (const auto& ci : ni.connected) {
        if (ci.type == placerDB::Terminal) {
          int tno = ci.iter;
          fout << "\nset label \"" << mydesign.Terminals.at(tno).name << "\" at " << mydesign.Terminals.at(tno).center.x << " , "
               << mydesign.Terminals.at(tno).center.y << " center                " << endl;
          break;
        }
      }
    }
  }

  // plot blocks
  fout << "\nplot[:][:] \'-\' with lines linestyle 3";
  if (plot_pin) fout << ", \'-\' with lines linestyle 7";
  if (plot_terminal) fout << ", \'-\' with lines linestyle 1";
  if (plot_net) fout << ", \'-\' with lines linestyle 0";
  fout << endl << endl;
  for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
    vector<placerDB::point> newp = mydesign.Blocks[i][0].boundary.polygon;
    fout << "# block " << mydesign.Blocks[i][0].name << " select " << 0 << " bsize " << newp.size() << endl;
    for (unsigned int it = 0; it < newp.size(); it++) {
      fout << "\t" << newp[it].x + Blocks[i].x << "\t" << newp[it].y + Blocks[i].y << endl;
    }
    fout << "\t" << newp[0].x + Blocks[i].x << "\t" << newp[0].y + Blocks[i].y << endl;
    fout << endl;
  }
  fout << "\nEOF" << endl;

  // plot block pins
  if (plot_pin) {
    for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
      for (unsigned int j = 0; j < mydesign.Blocks[i][0].blockPins.size(); j++) {
        for (unsigned int k = 0; k < mydesign.Blocks[i][0].blockPins[j].boundary.size(); k++) {
          for (unsigned int it = 0; it < mydesign.Blocks[i][0].blockPins[j].boundary[k].polygon.size(); it++) {
            placerDB::point newp;
            newp.x = mydesign.Blocks[i][0].blockPins[j].boundary[k].polygon[it].x;
            newp.y = mydesign.Blocks[i][0].blockPins[j].boundary[k].polygon[it].y;
            if (Blocks[i].H_flip) newp.x = mydesign.Blocks[i][0].width - newp.x;
            if (Blocks[i].V_flip) newp.y = mydesign.Blocks[i][0].height - newp.y;
            newp.x += Blocks[i].x;
            newp.y += Blocks[i].y;
            fout << "\t" << newp.x << "\t" << newp.y << endl;
          }
          placerDB::point newp;
          newp.x = mydesign.Blocks[i][0].blockPins[j].boundary[k].polygon[0].x;
          newp.y = mydesign.Blocks[i][0].blockPins[j].boundary[k].polygon[0].y;
          if (Blocks[i].H_flip) newp.x = mydesign.Blocks[i][0].width - newp.x;
          if (Blocks[i].V_flip) newp.y = mydesign.Blocks[i][0].height - newp.y;
          newp.x += Blocks[i].x;
          newp.y += Blocks[i].y;
          fout << "\t" << newp.x << "\t" << newp.y << endl;
          fout << endl;
        }
      }
    }
    fout << "\nEOF" << endl;
  }

  // plot terminals
  if (plot_terminal) {
    for (const auto& ni : mydesign.Nets) {
      // for each pin
      for (const auto& ci : ni.connected) {
        if (ci.type == placerDB::Terminal) {
          int tno = ci.iter;
          int bias = 20;
          fout << endl;
          fout << "\t" << mydesign.Terminals.at(tno).center.x - bias << "\t" << mydesign.Terminals.at(tno).center.y - bias << endl;
          fout << "\t" << mydesign.Terminals.at(tno).center.x - bias << "\t" << mydesign.Terminals.at(tno).center.y + bias << endl;
          fout << "\t" << mydesign.Terminals.at(tno).center.x + bias << "\t" << mydesign.Terminals.at(tno).center.y + bias << endl;
          fout << "\t" << mydesign.Terminals.at(tno).center.x + bias << "\t" << mydesign.Terminals.at(tno).center.y - bias << endl;
          fout << "\t" << mydesign.Terminals.at(tno).center.x - bias << "\t" << mydesign.Terminals.at(tno).center.y - bias << endl;
          break;
        }
      }
    }
    fout << "\nEOF" << endl;
  }

  // plot nets
  if (plot_net) {
    for (vector<placerDB::net>::iterator ni = mydesign.Nets.begin(); ni != mydesign.Nets.end(); ++ni) {
      placerDB::point tp;
      vector<placerDB::point> pins;
      // for each pin
      for (const auto& ci : ni->connected) {
        if (ci.type == placerDB::Block) {
          if (mydesign.Blocks[ci.iter2][0].blockPins.size() > 0) {
            if (mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size() > 0) {
              tp.x = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[0].x;
              tp.y = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[0].y;
              if (Blocks[ci.iter2].H_flip) tp.x = mydesign.Blocks[ci.iter2][0].width - tp.x;
              if (Blocks[ci.iter2].V_flip) tp.y = mydesign.Blocks[ci.iter2][0].height - tp.y;
              tp.x += Blocks[ci.iter2].x;
              tp.y += Blocks[ci.iter2].y;
              pins.push_back(tp);
            }
          } else {
            tp.x = mydesign.Blocks[ci.iter2][0].width / 2;
            tp.y = mydesign.Blocks[ci.iter2][0].height / 2;
            if (Blocks[ci.iter2].H_flip) tp.x = mydesign.Blocks[ci.iter2][0].width - tp.x;
            if (Blocks[ci.iter2].V_flip) tp.y = mydesign.Blocks[ci.iter2][0].height - tp.y;
            tp.x += Blocks[ci.iter2].x;
            tp.y += Blocks[ci.iter2].y;
            pins.push_back(tp);
          }
        } else if (ci.type == placerDB::Terminal) {
          pins.push_back(mydesign.Terminals.at(ci.iter).center);
        }
      }
      fout << "\n#Net: " << ni->name << endl;
      if (pins.size() >= 2) {
        for (int i = 1; i < (int)pins.size(); i++) {
          fout << "\t" << pins.at(0).x << "\t" << pins.at(0).y << endl;
          fout << "\t" << pins.at(i).x << "\t" << pins.at(i).y << endl;
          fout << "\t" << pins.at(0).x << "\t" << pins.at(0).y << endl << endl;
        }
      }
    }
    fout << "\nEOF" << endl;
  }
  fout << endl << "pause -1 \'Press any key\'";
  fout.close();
}

void ILP_solver::PlotPlacement(design& mydesign, SeqPair& curr_sp, string outfile) {
  // cout << "Placer-Info: create gnuplot file" << endl;
  placerDB::point p, bp;
  ofstream fout;
  vector<placerDB::point> p_pin;
  fout.open(outfile.c_str());
  fout << "#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)" << endl;
  fout << "\nset title\" #Blocks= " << mydesign.Blocks.size() << ", #Terminals= " << mydesign.Terminals.size() << ", #Nets= " << mydesign.Nets.size()
       << ",Area=" << area << ", HPWL= " << HPWL_extend << " \"" << endl;
  fout << "\nset nokey" << endl;
  fout << "#   Uncomment these two lines starting with \"set\"" << endl;
  fout << "#   to save an EPS file for inclusion into a latex document" << endl;
  fout << "# set terminal postscript eps color solid 20" << endl;
  fout << "# set output \"result.eps\"" << endl << endl;
  fout << "#   Uncomment these two lines starting with \"set\"" << endl;
  fout << "#   to save a PS file for printing" << endl;
  fout << "# set terminal postscript portrait color solid 20" << endl;
  fout << "# set output \"result.ps\"" << endl << endl;

  int bias = 50;
  int range = std::max(UR.x, UR.y) + bias;
  fout << "\nset xrange [" << LL.x - bias << ":" << UR.x + bias << "]" << endl;
  fout << "\nset yrange [" << LL.y - bias << ":" << UR.y + bias << "]" << endl;
  // set labels for blocks
  for (int i = 0; i < mydesign.Blocks.size(); ++i) {
    placerDB::point tp;
    tp.x = Blocks[i].x + mydesign.Blocks[i][curr_sp.selected[i]].width / 2;
    tp.y = Blocks[i].y + mydesign.Blocks[i][curr_sp.selected[i]].height / 2;
    fout << "\nset label \"" << mydesign.Blocks[i][curr_sp.selected[i]].name << "\" at " << tp.x << " , " << tp.y << " center " << endl;
    for (unsigned int j = 0; j < mydesign.Blocks[i][curr_sp.selected[i]].blockPins.size(); j++) {
      for (unsigned int k = 0; k < mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].center.size(); k++) {
        placerDB::point newp;
        newp.x = mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].center[k].x;
        newp.y = mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].center[k].y;
        if (Blocks[i].H_flip) newp.x = mydesign.Blocks[i][curr_sp.selected[i]].width - newp.x;
        if (Blocks[i].V_flip) newp.y = mydesign.Blocks[i][curr_sp.selected[i]].height - newp.y;
        newp.x += Blocks[i].x;
        newp.y += Blocks[i].y;
        fout << "\nset label \"" << mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].name << "\" at " << newp.x << " , " << newp.y << endl;
        fout << endl;
      }
    }
  }

  // set labels for terminals
  // cout << "set labels for terminals..." << endl;
  for (const auto& ni : mydesign.Nets) {
    // for each pin
    for (const auto& ci : ni.connected) {
      if (ci.type == placerDB::Terminal) {
        int tno = ci.iter;
        fout << "\nset label \"" << mydesign.Terminals.at(tno).name << "\" at " << mydesign.Terminals.at(tno).center.x << " , "
             << mydesign.Terminals.at(tno).center.y << " center                " << endl;
        break;
      }
    }
  }

  // plot blocks
  fout << "\nplot[:][:] \'-\' with lines linestyle 3, \'-\' with lines linestyle 7, \'-\' with lines linestyle 1, \'-\' with lines linestyle 0" << endl << endl;
  for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
    vector<placerDB::point> newp = mydesign.Blocks[i][curr_sp.selected[i]].boundary.polygon;
    fout << "# block " << mydesign.Blocks[i][curr_sp.selected[i]].name << " select " << curr_sp.selected[i] << " bsize " << newp.size() << endl;
    for (unsigned int it = 0; it < newp.size(); it++) {
      fout << "\t" << newp[it].x + Blocks[i].x << "\t" << newp[it].y + Blocks[i].y << endl;
    }
    fout << "\t" << newp[0].x + Blocks[i].x << "\t" << newp[0].y + Blocks[i].y << endl;
    fout << endl;
  }
  fout << "\nEOF" << endl;

  // plot block pins
  for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
    for (unsigned int j = 0; j < mydesign.Blocks[i][curr_sp.selected[i]].blockPins.size(); j++) {
      for (unsigned int k = 0; k < mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].boundary.size(); k++) {
        for (unsigned int it = 0; it < mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].boundary[k].polygon.size(); it++) {
          placerDB::point newp;
          newp.x = mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].boundary[k].polygon[it].x;
          newp.y = mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].boundary[k].polygon[it].y;
          if (Blocks[i].H_flip) newp.x = mydesign.Blocks[i][curr_sp.selected[i]].width - newp.x;
          if (Blocks[i].V_flip) newp.y = mydesign.Blocks[i][curr_sp.selected[i]].height - newp.y;
          newp.x += Blocks[i].x;
          newp.y += Blocks[i].y;
          fout << "\t" << newp.x << "\t" << newp.y << endl;
        }
        placerDB::point newp;
        newp.x = mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].boundary[k].polygon[0].x;
        newp.y = mydesign.Blocks[i][curr_sp.selected[i]].blockPins[j].boundary[k].polygon[0].y;
        if (Blocks[i].H_flip) newp.x = mydesign.Blocks[i][curr_sp.selected[i]].width - newp.x;
        if (Blocks[i].V_flip) newp.y = mydesign.Blocks[i][curr_sp.selected[i]].height - newp.y;
        newp.x += Blocks[i].x;
        newp.y += Blocks[i].y;
        fout << "\t" << newp.x << "\t" << newp.y << endl;
        fout << endl;
      }
    }
  }
  fout << "\nEOF" << endl;

  // plot terminals
  for (const auto& ni : mydesign.Nets) {
    // for each pin
    for (const auto& ci : ni.connected) {
      if (ci.type == placerDB::Terminal) {
        int tno = ci.iter;
        int bias = 20;
        fout << endl;
        fout << "\t" << mydesign.Terminals.at(tno).center.x - bias << "\t" << mydesign.Terminals.at(tno).center.y - bias << endl;
        fout << "\t" << mydesign.Terminals.at(tno).center.x - bias << "\t" << mydesign.Terminals.at(tno).center.y + bias << endl;
        fout << "\t" << mydesign.Terminals.at(tno).center.x + bias << "\t" << mydesign.Terminals.at(tno).center.y + bias << endl;
        fout << "\t" << mydesign.Terminals.at(tno).center.x + bias << "\t" << mydesign.Terminals.at(tno).center.y - bias << endl;
        fout << "\t" << mydesign.Terminals.at(tno).center.x - bias << "\t" << mydesign.Terminals.at(tno).center.y - bias << endl;
        break;
      }
    }
  }
  fout << "\nEOF" << endl;

  // plot nets
  for (vector<placerDB::net>::iterator ni = mydesign.Nets.begin(); ni != mydesign.Nets.end(); ++ni) {
    placerDB::point tp;
    vector<placerDB::point> pins;
    // for each pin
    for (const auto& ci : ni->connected) {
      if (ci.type == placerDB::Block) {
        if (mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size() > 0) {
          tp.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[0].x;
          tp.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[0].y;
          if (Blocks[ci.iter2].H_flip) tp.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - tp.x;
          if (Blocks[ci.iter2].V_flip) tp.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - tp.y;
          tp.x += Blocks[ci.iter2].x;
          tp.y += Blocks[ci.iter2].y;
          pins.push_back(tp);
        }
      } else if (ci.type == placerDB::Terminal) {
        pins.push_back(mydesign.Terminals.at(ci.iter).center);
      }
    }
    fout << "\n#Net: " << ni->name << endl;
    if (pins.size() >= 2) {
      for (int i = 1; i < (int)pins.size(); i++) {
        fout << "\t" << pins.at(0).x << "\t" << pins.at(0).y << endl;
        fout << "\t" << pins.at(i).x << "\t" << pins.at(i).y << endl;
        fout << "\t" << pins.at(0).x << "\t" << pins.at(0).y << endl << endl;
      }
    }
  }
  fout << "\nEOF" << endl;
  fout << endl << "pause -1 \'Press any key\'";
  fout.close();
}

std::vector<double> ILP_solver::Calculate_Center_Point_feature(std::vector<std::vector<placerDB::point>>& temp_contact) {
  std::vector<double> temp_x;
  std::vector<double> temp_y;
  std::vector<double> feature;
  double sum_x;
  double sum_y;
  for (unsigned int i = 0; i < temp_contact.size(); i++) {
    sum_x = 0;
    sum_y = 0;
    for (unsigned int j = 0; j < temp_contact[i].size(); j++) {
      sum_x = sum_x + (double)temp_contact[i][j].x;
      sum_y = sum_y + (double)temp_contact[i][j].y;
    }
    sum_x = sum_x / (double)temp_contact[i].size();
    sum_y = sum_y / (double)temp_contact[i].size();
    temp_x.push_back(sum_x);
    temp_y.push_back(sum_y);
  }

  sum_x = 0;
  sum_y = 0;
  for (unsigned int i = 0; i < temp_x.size(); i++) {
    sum_x = sum_x + temp_x[i];
    sum_y = sum_y + temp_y[i];
  }
  double center_x = sum_x / (double)temp_x.size();
  double center_y = sum_y / (double)temp_y.size();
  for (unsigned int i = 0; i < temp_x.size(); i++) {
    feature.push_back(abs(center_x - (double)temp_x[i]) + abs(center_y - (double)temp_y[i]));
  }
  return feature;
}

void ILP_solver::updateTerminalCenterAnalytical(design& mydesign) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.updateTerminalCenter");

  int Xmax = UR.x;
  int Ymax = UR.y;
  vector<placerDB::point> pos;
  placerDB::point p, bp;
  int alpha;
  vector<placerDB::point> pos_pin;
  std::set<int> solved_terminals;
  // for each terminal
  for (unsigned int i = 0; i < mydesign.Terminals.size(); i++) {
    if (solved_terminals.find(i) != solved_terminals.end()) continue;
    solved_terminals.insert(i);
    int netIdx = mydesign.Terminals.at(i).netIter;
    int sbIdx = mydesign.Terminals.at(i).SBidx;
    int cp = mydesign.Terminals.at(i).counterpart;
    if (netIdx < 0 || netIdx >= mydesign.Nets.size()) {
      logger->error("Placer-Warning: terminal {0} is dangling; set it on origin", i);
      mydesign.Terminals.at(i).center = {0, 0};
      continue;
    }
    if ((mydesign.Nets.at(netIdx).priority).compare("min") == 0) {
      alpha = 4;
    } else if ((mydesign.Nets.at(netIdx).priority).compare("mid") == 0) {
      alpha = 2;
    } else {
      alpha = 1;
    }
    alpha *= mydesign.Nets.at(netIdx).weight;  // add weight to reflect the modification for bigMacros
    if (sbIdx != -1) {                         // in symmetry group
      placerDB::Smark axis = mydesign.SBlocks[sbIdx].axis_dir;
      if (cp == (int)i) {  // self-symmetric
        if (axis == placerDB::V) {
          int axis_X = Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first].x + mydesign.Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first][0].width / 2;
          int distTerm = INT_MAX;
          placerDB::point tp(axis_X, 0);
          for (const auto& ci : mydesign.Nets[netIdx].connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
                p += bp;
                if (p.y < distTerm) {
                  distTerm = p.y;
                  tp.y = 0;
                }
                if (Ymax - p.y < distTerm) {
                  distTerm = Ymax - p.y;
                  tp.y = Ymax;
                }
              }
            }
          }
          mydesign.Terminals.at(i).center = tp;
        } else if (axis == placerDB::H) {
          int axis_Y = Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first].y + mydesign.Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first][0].height / 2;
          int distTerm = INT_MAX;
          placerDB::point tp(0, axis_Y);
          for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
                p += bp;
                if (p.x < distTerm) {
                  distTerm = p.x;
                  tp.x = 0;
                }
                if (Xmax - p.x < distTerm) {
                  distTerm = Xmax - p.x;
                  tp.x = Xmax;
                }
              }
            }
          }
          mydesign.Terminals.at(i).center = tp;
        } else {
          logger->error("Placer-Error: incorrect axis direction");
        }
      } else {  // symmetry pair
        if (solved_terminals.find(cp) != solved_terminals.end()) continue;
        solved_terminals.insert(cp);
        int netIdx2 = mydesign.Terminals.at(cp).netIter;
        if (netIdx2 < 0 or netIdx2 >= mydesign.Nets.size()) {
          logger->error("Placer-Error: terminal {0} is not dangling, but its counterpart {1} is dangling; set them on origin", i, cp);
          mydesign.Terminals.at(i).center = {0, 0};
          mydesign.Terminals.at(cp).center = {0, 0};
          continue;
        }
        int alpha2;
        if ((mydesign.Nets.at(netIdx2).priority).compare("min") == 0) {
          alpha2 = 4;
        } else if ((mydesign.Nets.at(netIdx2).priority).compare("mid") == 0) {
          alpha2 = 2;
        } else {
          alpha2 = 1;
        }
        alpha2 *= mydesign.Nets.at(netIdx2).weight;  // add weight to reflect the modification for bigMacros
        if (axis == placerDB::V) {
          placerDB::point tpL1, tpR1;
          int distTermL = INT_MAX, distTermR = INT_MAX;
          for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
                p += bp;
                if (p.x < distTermL) {
                  distTermL = p.x;
                  tpL1.x = 0;
                  tpL1.y = p.y;
                }
                if (Xmax - p.x < distTermR) {
                  distTermR = Xmax - p.x;
                  tpR1.x = Xmax;
                  tpR1.y = p.y;
                }
              }
            }
          }
          placerDB::point tpL2, tpR2;
          int distTermL2 = INT_MAX, distTermR2 = INT_MAX;
          for (const auto& ci : mydesign.Nets.at(netIdx2).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
                p += bp;
                if (p.x < distTermL2) {
                  distTermL2 = p.x;
                  tpL2.x = 0;
                  tpL2.y = p.y;
                }
                if (Xmax - p.x < distTermR2) {
                  distTermR2 = Xmax - p.x;
                  tpR2.x = Xmax;
                  tpR2.y = p.y;
                }
              }
            }
          }
          if (distTermL * alpha + distTermR2 * alpha2 < distTermR * alpha + distTermL2 * alpha2) {
            mydesign.Terminals.at(i).center = tpL1;
            mydesign.Terminals.at(cp).center = tpR2;
          } else {
            mydesign.Terminals.at(i).center = tpR1;
            mydesign.Terminals.at(cp).center = tpL2;
          }
        } else if (axis == placerDB::H) {
          placerDB::point tpL1, tpU1;
          int distTermL = INT_MAX, distTermU = INT_MAX;
          for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
                p += bp;
                if (p.y < distTermL) {
                  distTermL = p.y;
                  tpL1.x = p.x;
                  tpL1.y = 0;
                }
                if (Ymax - p.y < distTermU) {
                  distTermU = Ymax - p.y;
                  tpU1.x = p.x;
                  tpU1.y = Ymax;
                }
              }
            }
          }
          placerDB::point tpL2, tpU2;
          int distTermL2 = INT_MAX, distTermU2 = INT_MAX;
          for (const auto& ci : mydesign.Nets.at(netIdx2).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
                p += bp;
                if (p.y < distTermL2) {
                  distTermL2 = p.y;
                  tpL2.x = p.x;
                  tpL2.y = 0;
                }
                if (Ymax - p.y < distTermU2) {
                  distTermU2 = Ymax - p.y;
                  tpU2.x = p.x;
                  tpU2.y = Ymax;
                }
              }
            }
          }
          if (distTermL * alpha + distTermU2 * alpha2 < distTermU * alpha + distTermL2 * alpha2) {
            mydesign.Terminals.at(i).center = tpL1;
            mydesign.Terminals.at(cp).center = tpU2;
          } else {
            mydesign.Terminals.at(i).center = tpU1;
            mydesign.Terminals.at(cp).center = tpL2;
          }
        } else {
          logger->error("Placer-Error: incorrect axis direction");
        }
      }
    } else {  // not in symmetry group
      int tar = -1;
      for (unsigned int j = 0; j < mydesign.Port_Location.size(); j++) {
        if (mydesign.Port_Location.at(j).tid == (int)i) {
          tar = j;
          break;
        }
      }
      if (tar != -1) {  // specifiy PortLocation constraint
        int x1 = Xmax / 3, x2 = Xmax * 2 / 3, x3 = Xmax;
        int y1 = Ymax / 3, y2 = Ymax * 2 / 3, y3 = Ymax;
        placerDB::point tp;
        pos.clear();
        for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
          if (ci.type == placerDB::Block) {
            bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
            for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
              p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
              if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
              if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
              p += bp;
              pos.push_back(p);
            }
          }
        }
        int shot = -1;
        int distTerm = INT_MAX;
        for (unsigned int k = 0; k < pos.size(); k++) {
          p = pos.at(k);
          // Bmark {TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT};
          switch (mydesign.Port_Location.at(tar).pos) {
            case placerDB::TL:
              if (p.x >= 0 and p.x <= x1) {
                if (Ymax - p.y < distTerm) {
                  distTerm = Ymax - p.y;
                  shot = k;
                  tp = {p.x, Ymax};
                }
              } else {
                if (std::abs(p.x - 0) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - 0) + Ymax - p.y;
                  shot = k;
                  tp = {0, Ymax};
                }
                if (std::abs(p.x - x1) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x1) + Ymax - p.y;
                  shot = k;
                  tp = {x1, Ymax};
                }
              }
              break;
            case placerDB::TC:
              if (p.x >= x1 and p.x <= x2) {
                if (Ymax - p.y < distTerm) {
                  distTerm = Ymax - p.y;
                  shot = k;
                  tp = {p.x, Ymax};
                }
              } else {
                if (std::abs(p.x - x2) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x2) + Ymax - p.y;
                  shot = k;
                  tp = {x2, Ymax};
                }
                if (std::abs(p.x - x1) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x1) + Ymax - p.y;
                  shot = k;
                  tp = {x1, Ymax};
                }
              }
              break;
            case placerDB::TR:
              if (p.x >= x2 and p.x <= x3) {
                if (Ymax - p.y < distTerm) {
                  distTerm = Ymax - p.y;
                  shot = k;
                  tp = {p.x, Ymax};
                }
              } else {
                if (std::abs(p.x - x2) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x2) + Ymax - p.y;
                  shot = k;
                  tp = {x2, Ymax};
                }
                if (std::abs(p.x - x3) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x3) + Ymax - p.y;
                  shot = k;
                  tp = {x3, Ymax};
                }
              }
              break;
            case placerDB::RT:
              if (p.y >= y2 and p.y <= y3) {
                if (Xmax - p.x < distTerm) {
                  distTerm = Xmax - p.x;
                  shot = k;
                  tp = {Xmax, p.y};
                }
              } else {
                if (std::abs(p.y - y2) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y2) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y2};
                }
                if (std::abs(p.y - y3) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y3) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y3};
                }
              }
              break;
            case placerDB::RC:
              if (p.y >= y1 and p.y <= y2) {
                if (Xmax - p.x < distTerm) {
                  distTerm = Xmax - p.x;
                  shot = k;
                  tp = {Xmax, p.y};
                }
              } else {
                if (std::abs(p.y - y2) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y2) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y2};
                }
                if (std::abs(p.y - y1) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y1) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y1};
                }
              }
              break;
            case placerDB::RB:
              if (p.y >= 0 and p.y <= y1) {
                if (Xmax - p.x < distTerm) {
                  distTerm = Xmax - p.x;
                  shot = k;
                  tp = {Xmax, p.y};
                }
              } else {
                if (std::abs(p.y - 0) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - 0) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, 0};
                }
                if (std::abs(p.y - y1) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y1) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y1};
                }
              }
              break;
            case placerDB::BL:
              if (p.x >= 0 and p.x <= x1) {
                if (p.y < distTerm) {
                  distTerm = p.y;
                  shot = k;
                  tp = {p.x, 0};
                }
              } else {
                if (std::abs(p.x - 0) + p.y < distTerm) {
                  distTerm = std::abs(p.x - 0) + p.y;
                  shot = k;
                  tp = {0, 0};
                }
                if (std::abs(p.x - x1) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x1) + p.y;
                  shot = k;
                  tp = {x1, 0};
                }
              }
              break;
            case placerDB::BC:
              if (p.x >= x1 and p.x <= x2) {
                if (p.y < distTerm) {
                  distTerm = p.y;
                  shot = k;
                  tp = {p.x, 0};
                }
              } else {
                if (std::abs(p.x - x2) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x2) + p.y;
                  shot = k;
                  tp = {x2, 0};
                }
                if (std::abs(p.x - x1) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x1) + p.y;
                  shot = k;
                  tp = {x1, 0};
                }
              }
              break;
            case placerDB::BR:
              if (p.x >= x2 and p.x <= x3) {
                if (p.y < distTerm) {
                  distTerm = p.y;
                  shot = k;
                  tp = {p.x, 0};
                }
              } else {
                if (std::abs(p.x - x2) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x2) + p.y;
                  shot = k;
                  tp = {x2, 0};
                }
                if (std::abs(p.x - x3) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x3) + p.y;
                  shot = k;
                  tp = {x3, 0};
                }
              }
              break;
            case placerDB::LT:
              if (p.y >= y2 and p.y <= y3) {
                if (p.x < distTerm) {
                  distTerm = p.x;
                  shot = k;
                  tp = {0, p.y};
                }
              } else {
                if (std::abs(p.y - y2) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y2) + p.x;
                  shot = k;
                  tp = {0, y2};
                }
                if (std::abs(p.y - y3) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y3) + p.x;
                  shot = k;
                  tp = {0, y3};
                }
              }
              break;
            case placerDB::LC:
              if (p.y >= y1 and p.y <= y2) {
                if (p.x < distTerm) {
                  distTerm = p.x;
                  shot = k;
                  tp = {0, p.y};
                }
              } else {
                if (std::abs(p.y - y2) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y2) + p.x;
                  shot = k;
                  tp = {0, y2};
                }
                if (std::abs(p.y - y1) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y1) + p.x;
                  shot = k;
                  tp = {0, y1};
                }
              }
              break;
            case placerDB::LB:
              if (p.y >= 0 and p.y <= y1) {
                if (p.x < distTerm) {
                  distTerm = p.x;
                  shot = k;
                  tp = {0, p.y};
                }
              } else {
                if (std::abs(p.y - 0) + p.x < distTerm) {
                  distTerm = std::abs(p.y - 0) + p.x;
                  shot = k;
                  tp = {0, 0};
                }
                if (std::abs(p.y - y1) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y1) + p.x;
                  shot = k;
                  tp = {0, y1};
                }
              }
              break;
            default:
              logger->warn("Placer-Warning: incorrect port position");
          }
        }
        if (shot != -1) {
          mydesign.Terminals.at(i).center = tp;
        }
      } else {  // no constraint
        placerDB::point tp;
        int distTerm = INT_MAX;
        for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
          if (ci.type == placerDB::Block) {
            if (mydesign.Blocks[ci.iter2][0].blockPins.size() == 0) continue;
            bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
            for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center.size(); k++) {
              p = mydesign.Blocks[ci.iter2][0].blockPins[ci.iter].center[k];
              if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][0].width - p.x;
              if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][0].height - p.y;
              p += bp;
              if (p.x < distTerm) {
                distTerm = p.x;
                tp = {0, p.y};
              }
              if (Xmax - p.x < distTerm) {
                distTerm = Xmax - p.x;
                tp = {Xmax, p.y};
              }
              if (p.y < distTerm) {
                distTerm = p.y;
                tp = {p.x, 0};
              }
              if (Ymax - p.y < distTerm) {
                distTerm = Ymax - p.y;
                tp = {p.x, Ymax};
              }
            }
          }
        }
        mydesign.Terminals.at(i).center = tp;
      }
    }
  }
}

void ILP_solver::updateTerminalCenter(design& mydesign, SeqPair& curr_sp) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.updateTerminalCenter");

  int Xmax = UR.x;
  int Ymax = UR.y;
  vector<placerDB::point> pos;
  placerDB::point p, bp;
  int alpha;
  vector<placerDB::point> pos_pin;
  std::set<int> solved_terminals;
  // for each terminal
  for (int i = 0; i < mydesign.Terminals.size(); i++) {
    if (solved_terminals.find(i) != solved_terminals.end()) continue;
    solved_terminals.insert(i);
    int netIdx = mydesign.Terminals.at(i).netIter;
    int sbIdx = mydesign.Terminals.at(i).SBidx;
    int cp = mydesign.Terminals.at(i).counterpart;
    if (netIdx < 0 || netIdx >= int(mydesign.Nets.size())) {
      logger->error("Placer-Warning: terminal {0} is dangling; set it on origin", i);
      mydesign.Terminals.at(i).center = {0, 0};
      continue;
    }
    if ((mydesign.Nets.at(netIdx).priority).compare("min") == 0) {
      alpha = 4;
    } else if ((mydesign.Nets.at(netIdx).priority).compare("mid") == 0) {
      alpha = 2;
    } else {
      alpha = 1;
    }
    alpha *= mydesign.Nets.at(netIdx).weight;  // add weight to reflect the modification for bigMacros
    if (sbIdx != -1) {                         // in symmetry group
      placerDB::Smark axis = curr_sp.GetSymmBlockAxis(sbIdx);
      if (cp == (int)i) {  // self-symmetric
        if (axis == placerDB::V) {
          int axis_X = Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first].x +
                       mydesign.Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first][curr_sp.selected[mydesign.SBlocks[sbIdx].selfsym[0].first]].width / 2;
          int distTerm = INT_MAX;
          placerDB::point tp(axis_X, 0);
          for (const auto& ci : mydesign.Nets[netIdx].connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
                p += bp;
                if (p.y < distTerm) {
                  distTerm = p.y;
                  tp.y = 0;
                }
                if (Ymax - p.y < distTerm) {
                  distTerm = Ymax - p.y;
                  tp.y = Ymax;
                }
              }
            }
          }
          mydesign.Terminals.at(i).center = tp;
        } else if (axis == placerDB::H) {
          int axis_Y = Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first].y +
                       mydesign.Blocks[mydesign.SBlocks[sbIdx].selfsym[0].first][curr_sp.selected[mydesign.SBlocks[sbIdx].selfsym[0].first]].height / 2;
          int distTerm = INT_MAX;
          placerDB::point tp(0, axis_Y);
          for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
                p += bp;
                if (p.x < distTerm) {
                  distTerm = p.x;
                  tp.x = 0;
                }
                if (Xmax - p.x < distTerm) {
                  distTerm = Xmax - p.x;
                  tp.x = Xmax;
                }
              }
            }
          }
          mydesign.Terminals.at(i).center = tp;
        } else {
          logger->error("Placer-Error: incorrect axis direction");
        }
      } else {  // symmetry pair
        if (solved_terminals.find(cp) != solved_terminals.end()) continue;
        solved_terminals.insert(cp);
        int netIdx2 = mydesign.Terminals.at(cp).netIter;
        if (netIdx2 < 0 || netIdx2 >= int(mydesign.Nets.size())) {
          logger->error("Placer-Error: terminal {0} is not dangling, but its counterpart {1} is dangling; set them on origin", i, cp);
          mydesign.Terminals.at(i).center = {0, 0};
          mydesign.Terminals.at(cp).center = {0, 0};
          continue;
        }
        int alpha2;
        if ((mydesign.Nets.at(netIdx2).priority).compare("min") == 0) {
          alpha2 = 4;
        } else if ((mydesign.Nets.at(netIdx2).priority).compare("mid") == 0) {
          alpha2 = 2;
        } else {
          alpha2 = 1;
        }
        alpha2 *= mydesign.Nets.at(netIdx2).weight;  // add weight to reflect the modification for bigMacros
        if (axis == placerDB::V) {
          placerDB::point tpL1, tpR1;
          int distTermL = INT_MAX, distTermR = INT_MAX;
          for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
                p += bp;
                if (p.x < distTermL) {
                  distTermL = p.x;
                  tpL1.x = 0;
                  tpL1.y = p.y;
                }
                if (Xmax - p.x < distTermR) {
                  distTermR = Xmax - p.x;
                  tpR1.x = Xmax;
                  tpR1.y = p.y;
                }
              }
            }
          }
          placerDB::point tpL2, tpR2;
          int distTermL2 = INT_MAX, distTermR2 = INT_MAX;
          for (const auto& ci : mydesign.Nets.at(netIdx2).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
                p += bp;
                if (p.x < distTermL2) {
                  distTermL2 = p.x;
                  tpL2.x = 0;
                  tpL2.y = p.y;
                }
                if (Xmax - p.x < distTermR2) {
                  distTermR2 = Xmax - p.x;
                  tpR2.x = Xmax;
                  tpR2.y = p.y;
                }
              }
            }
          }
          if (distTermL * alpha + distTermR2 * alpha2 < distTermR * alpha + distTermL2 * alpha2) {
            mydesign.Terminals.at(i).center = tpL1;
            mydesign.Terminals.at(cp).center = tpR2;
          } else {
            mydesign.Terminals.at(i).center = tpR1;
            mydesign.Terminals.at(cp).center = tpL2;
          }
        } else if (axis == placerDB::H) {
          placerDB::point tpL1, tpU1;
          int distTermL = INT_MAX, distTermU = INT_MAX;
          for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
                p += bp;
                if (p.y < distTermL) {
                  distTermL = p.y;
                  tpL1.x = p.x;
                  tpL1.y = 0;
                }
                if (Ymax - p.y < distTermU) {
                  distTermU = Ymax - p.y;
                  tpU1.x = p.x;
                  tpU1.y = Ymax;
                }
              }
            }
          }
          placerDB::point tpL2, tpU2;
          int distTermL2 = INT_MAX, distTermU2 = INT_MAX;
          for (const auto& ci : mydesign.Nets.at(netIdx2).connected) {
            if (ci.type == placerDB::Block) {
              bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
              for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
                p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
                if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
                if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
                p += bp;
                if (p.y < distTermL2) {
                  distTermL2 = p.y;
                  tpL2.x = p.x;
                  tpL2.y = 0;
                }
                if (Ymax - p.y < distTermU2) {
                  distTermU2 = Ymax - p.y;
                  tpU2.x = p.x;
                  tpU2.y = Ymax;
                }
              }
            }
          }
          if (distTermL * alpha + distTermU2 * alpha2 < distTermU * alpha + distTermL2 * alpha2) {
            mydesign.Terminals.at(i).center = tpL1;
            mydesign.Terminals.at(cp).center = tpU2;
          } else {
            mydesign.Terminals.at(i).center = tpU1;
            mydesign.Terminals.at(cp).center = tpL2;
          }
        } else {
          logger->error("Placer-Error: incorrect axis direction");
        }
      }
    } else {  // not in symmetry group
      int tar = -1;
      for (int j = 0; j < mydesign.Port_Location.size(); j++) {
        if (mydesign.Port_Location.at(j).tid == (int)i) {
          tar = j;
          break;
        }
      }
      if (tar != -1) {  // specifiy PortLocation constraint
        int x1 = Xmax / 3, x2 = Xmax * 2 / 3, x3 = Xmax;
        int y1 = Ymax / 3, y2 = Ymax * 2 / 3, y3 = Ymax;
        placerDB::point tp;
        pos.clear();
        for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
          if (ci.type == placerDB::Block) {
            bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
            for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
              p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
              if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
              if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
              p += bp;
              pos.push_back(p);
            }
          }
        }
        int shot = -1;
        int distTerm = INT_MAX;
        for (int k = 0; k < pos.size(); k++) {
          p = pos.at(k);
          // Bmark {TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT};
          switch (mydesign.Port_Location.at(tar).pos) {
            case placerDB::TL:
              if (p.x >= 0 && p.x <= x1) {
                if (Ymax - p.y < distTerm) {
                  distTerm = Ymax - p.y;
                  shot = k;
                  tp = {p.x, Ymax};
                }
              } else {
                if (std::abs(p.x - 0) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - 0) + Ymax - p.y;
                  shot = k;
                  tp = {0, Ymax};
                }
                if (std::abs(p.x - x1) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x1) + Ymax - p.y;
                  shot = k;
                  tp = {x1, Ymax};
                }
              }
              break;
            case placerDB::TC:
              if (p.x >= x1 && p.x <= x2) {
                if (Ymax - p.y < distTerm) {
                  distTerm = Ymax - p.y;
                  shot = k;
                  tp = {p.x, Ymax};
                }
              } else {
                if (std::abs(p.x - x2) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x2) + Ymax - p.y;
                  shot = k;
                  tp = {x2, Ymax};
                }
                if (std::abs(p.x - x1) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x1) + Ymax - p.y;
                  shot = k;
                  tp = {x1, Ymax};
                }
              }
              break;
            case placerDB::TR:
              if (p.x >= x2 && p.x <= x3) {
                if (Ymax - p.y < distTerm) {
                  distTerm = Ymax - p.y;
                  shot = k;
                  tp = {p.x, Ymax};
                }
              } else {
                if (std::abs(p.x - x2) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x2) + Ymax - p.y;
                  shot = k;
                  tp = {x2, Ymax};
                }
                if (std::abs(p.x - x3) + Ymax - p.y < distTerm) {
                  distTerm = std::abs(p.x - x3) + Ymax - p.y;
                  shot = k;
                  tp = {x3, Ymax};
                }
              }
              break;
            case placerDB::RT:
              if (p.y >= y2 && p.y <= y3) {
                if (Xmax - p.x < distTerm) {
                  distTerm = Xmax - p.x;
                  shot = k;
                  tp = {Xmax, p.y};
                }
              } else {
                if (std::abs(p.y - y2) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y2) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y2};
                }
                if (std::abs(p.y - y3) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y3) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y3};
                }
              }
              break;
            case placerDB::RC:
              if (p.y >= y1 && p.y <= y2) {
                if (Xmax - p.x < distTerm) {
                  distTerm = Xmax - p.x;
                  shot = k;
                  tp = {Xmax, p.y};
                }
              } else {
                if (std::abs(p.y - y2) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y2) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y2};
                }
                if (std::abs(p.y - y1) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y1) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y1};
                }
              }
              break;
            case placerDB::RB:
              if (p.y >= 0 && p.y <= y1) {
                if (Xmax - p.x < distTerm) {
                  distTerm = Xmax - p.x;
                  shot = k;
                  tp = {Xmax, p.y};
                }
              } else {
                if (std::abs(p.y - 0) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - 0) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, 0};
                }
                if (std::abs(p.y - y1) + Xmax - p.x < distTerm) {
                  distTerm = std::abs(p.y - y1) + Xmax - p.x;
                  shot = k;
                  tp = {Xmax, y1};
                }
              }
              break;
            case placerDB::BL:
              if (p.x >= 0 && p.x <= x1) {
                if (p.y < distTerm) {
                  distTerm = p.y;
                  shot = k;
                  tp = {p.x, 0};
                }
              } else {
                if (std::abs(p.x - 0) + p.y < distTerm) {
                  distTerm = std::abs(p.x - 0) + p.y;
                  shot = k;
                  tp = {0, 0};
                }
                if (std::abs(p.x - x1) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x1) + p.y;
                  shot = k;
                  tp = {x1, 0};
                }
              }
              break;
            case placerDB::BC:
              if (p.x >= x1 && p.x <= x2) {
                if (p.y < distTerm) {
                  distTerm = p.y;
                  shot = k;
                  tp = {p.x, 0};
                }
              } else {
                if (std::abs(p.x - x2) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x2) + p.y;
                  shot = k;
                  tp = {x2, 0};
                }
                if (std::abs(p.x - x1) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x1) + p.y;
                  shot = k;
                  tp = {x1, 0};
                }
              }
              break;
            case placerDB::BR:
              if (p.x >= x2 && p.x <= x3) {
                if (p.y < distTerm) {
                  distTerm = p.y;
                  shot = k;
                  tp = {p.x, 0};
                }
              } else {
                if (std::abs(p.x - x2) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x2) + p.y;
                  shot = k;
                  tp = {x2, 0};
                }
                if (std::abs(p.x - x3) + p.y < distTerm) {
                  distTerm = std::abs(p.x - x3) + p.y;
                  shot = k;
                  tp = {x3, 0};
                }
              }
              break;
            case placerDB::LT:
              if (p.y >= y2 && p.y <= y3) {
                if (p.x < distTerm) {
                  distTerm = p.x;
                  shot = k;
                  tp = {0, p.y};
                }
              } else {
                if (std::abs(p.y - y2) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y2) + p.x;
                  shot = k;
                  tp = {0, y2};
                }
                if (std::abs(p.y - y3) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y3) + p.x;
                  shot = k;
                  tp = {0, y3};
                }
              }
              break;
            case placerDB::LC:
              if (p.y >= y1 && p.y <= y2) {
                if (p.x < distTerm) {
                  distTerm = p.x;
                  shot = k;
                  tp = {0, p.y};
                }
              } else {
                if (std::abs(p.y - y2) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y2) + p.x;
                  shot = k;
                  tp = {0, y2};
                }
                if (std::abs(p.y - y1) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y1) + p.x;
                  shot = k;
                  tp = {0, y1};
                }
              }
              break;
            case placerDB::LB:
              if (p.y >= 0 && p.y <= y1) {
                if (p.x < distTerm) {
                  distTerm = p.x;
                  shot = k;
                  tp = {0, p.y};
                }
              } else {
                if (std::abs(p.y - 0) + p.x < distTerm) {
                  distTerm = std::abs(p.y - 0) + p.x;
                  shot = k;
                  tp = {0, 0};
                }
                if (std::abs(p.y - y1) + p.x < distTerm) {
                  distTerm = std::abs(p.y - y1) + p.x;
                  shot = k;
                  tp = {0, y1};
                }
              }
              break;
            default:
              logger->warn("Placer-Warning: incorrect port position");
          }
        }
        if (shot != -1) {
          mydesign.Terminals.at(i).center = tp;
        }
      } else {  // no constraint
        placerDB::point tp;
        int distTerm = INT_MAX;
        for (const auto& ci : mydesign.Nets.at(netIdx).connected) {
          if (ci.type == placerDB::Block) {
            bp = placerDB::point(Blocks[ci.iter2].x, Blocks[ci.iter2].y);
            for (unsigned int k = 0; k < mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center.size(); k++) {
              p = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].blockPins[ci.iter].center[k];
              if (Blocks[ci.iter2].H_flip) p.x = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].width - p.x;
              if (Blocks[ci.iter2].V_flip) p.y = mydesign.Blocks[ci.iter2][curr_sp.selected[ci.iter2]].height - p.y;
              p += bp;
              if (p.x < distTerm) {
                distTerm = p.x;
                tp = {0, p.y};
              }
              if (Xmax - p.x < distTerm) {
                distTerm = Xmax - p.x;
                tp = {Xmax, p.y};
              }
              if (p.y < distTerm) {
                distTerm = p.y;
                tp = {p.x, 0};
              }
              if (Ymax - p.y < distTerm) {
                distTerm = Ymax - p.y;
                tp = {p.x, Ymax};
              }
            }
          }
        }
        mydesign.Terminals.at(i).center = tp;
      }
    }
  }
}

void ILP_solver::UpdateHierNode(design& mydesign, SeqPair& curr_sp, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo) {
  node.width = UR.x;
  node.height = UR.y;
  node.HPWL = HPWL;
  node.HPWL_extend = HPWL_extend;
  node.HPWL_extend_wo_terminal = node.HPWL_extend - HPWL_extend_terminal;  // HPWL without terminal nets' HPWL
  node.area_norm = area_norm;
  node.HPWL_norm = HPWL_norm;
  node.constraint_penalty = constraint_penalty;
  node.cost = cost;

  for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
    node.Blocks.at(i).selectedInstance = curr_sp.GetBlockSelected(i);
    node.HPWL_extend += node.Blocks[i].instance[node.Blocks.at(i).selectedInstance].HPWL_extend_wo_terminal;
    node.HPWL_extend_wo_terminal += node.Blocks[i].instance[node.Blocks.at(i).selectedInstance].HPWL_extend_wo_terminal;
    placerDB::Omark ort;
    if (Blocks[i].H_flip) {
      if (Blocks[i].V_flip)
        ort = placerDB::S;
      else
        ort = placerDB::FN;
    } else {
      if (Blocks[i].V_flip)
        ort = placerDB::FS;
      else
        ort = placerDB::N;
    }
    UpdateBlockinHierNode(mydesign, ort, node, i, curr_sp.GetBlockSelected(i), drcInfo);
  }
  UpdateTerminalinHierNode(mydesign, node, drcInfo);
  for (unsigned int i = 0; i < mydesign.SNets.size(); ++i) {
    int SBidx = mydesign.SNets.at(i).SBidx;
    placerDB::Smark axis_dir = curr_sp.GetSymmBlockAxis(SBidx);
    UpdateSymmetryNetInfo(mydesign, node, i, SBidx, axis_dir, curr_sp);
  }
}

void ILP_solver::UpdateHierNodeAnalytical(design& mydesign, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo) {
  node.width = UR.x;
  node.height = UR.y;
  node.HPWL = HPWL;
  node.HPWL_extend = HPWL_extend;
  node.HPWL_extend_wo_terminal = node.HPWL_extend - HPWL_extend_terminal;  // HPWL without terminal nets' HPWL
  node.area_norm = area_norm;
  node.HPWL_norm = HPWL_norm;
  node.constraint_penalty = constraint_penalty;
  node.cost = cost;

  for (unsigned int i = 0; i < mydesign.Blocks.size(); ++i) {
    node.Blocks.at(i).selectedInstance = 0;
    node.HPWL_extend += node.Blocks[i].instance[node.Blocks.at(i).selectedInstance].HPWL_extend_wo_terminal;
    node.HPWL_extend_wo_terminal += node.Blocks[i].instance[node.Blocks.at(i).selectedInstance].HPWL_extend_wo_terminal;
    placerDB::Omark ort;
    if (Blocks[i].H_flip) {
      if (Blocks[i].V_flip)
        ort = placerDB::S;
      else
        ort = placerDB::FN;
    } else {
      if (Blocks[i].V_flip)
        ort = placerDB::FS;
      else
        ort = placerDB::N;
    }
    UpdateBlockinHierNode(mydesign, ort, node, i, 0, drcInfo);
  }
  UpdateTerminalinHierNode(mydesign, node, drcInfo);
  for (unsigned int i = 0; i < mydesign.SNets.size(); ++i) {
    int SBidx = mydesign.SNets.at(i).SBidx;
    placerDB::Smark axis_dir = mydesign.SBlocks[i].axis_dir;
    UpdateSymmetryNetInfoAnalytical(mydesign, node, i, SBidx, axis_dir);
  }
}

void ILP_solver::UpdateBlockinHierNode(design& mydesign, placerDB::Omark ort, PnRDB::hierNode& node, int i, int sel, PnRDB::Drc_info& drcInfo) {
  vector<vector<placerDB::point>> boundary;
  vector<placerDB::point> center;
  vector<placerDB::point> bbox;
  placerDB::point bpoint;

  int x = Blocks[i].x;
  int y = Blocks[i].y;

  // SMB Hack
  int v_metal_index = -1;
  int h_metal_index = -1;
  for (unsigned int i = 0; i < drcInfo.Metal_info.size(); ++i) {
    if (drcInfo.Metal_info[i].direct == 0) {
      v_metal_index = i;
      break;
    }
  }
  for (unsigned int i = 0; i < drcInfo.Metal_info.size(); ++i) {
    if (drcInfo.Metal_info[i].direct == 1) {
      h_metal_index = i;
      break;
    }
  }

  x_pitch = drcInfo.Metal_info[v_metal_index].grid_unit_x;
  y_pitch = drcInfo.Metal_info[h_metal_index].grid_unit_y;
  roundup(x, x_pitch);
  roundup(y, y_pitch);

  placerDB::point LL = {x, y};
  bbox = mydesign.GetPlacedBlockAbsBoundary(i, ort, LL, sel);
  bpoint = mydesign.GetBlockAbsCenter(i, ort, LL, sel);
  auto& nd = node.Blocks.at(i).instance.at(sel);

  nd.orient = PnRDB::Omark(ort);
  nd.placedBox = ConvertBoundaryData(bbox);
  nd.placedCenter = ConvertPointData(bpoint);
  for (int j = 0; j < mydesign.GetBlockPinNum(i, sel); j++) {
    boundary = mydesign.GetPlacedBlockPinAbsBoundary(i, j, ort, LL, sel);
    center = mydesign.GetPlacedBlockPinAbsPosition(i, j, ort, LL, sel);
    for (unsigned int k = 0; k < nd.blockPins.at(j).pinContacts.size(); k++) {
      nd.blockPins.at(j).pinContacts.at(k).placedBox = ConvertBoundaryData(boundary.at(k));
      nd.blockPins.at(j).pinContacts.at(k).placedCenter = ConvertPointData(center.at(k));
    }
    // update pin vias
    for (unsigned int k = 0; k < node.Blocks.at(i).instance.at(sel).blockPins.at(j).pinVias.size(); k++) {
      auto& pv = nd.blockPins.at(j).pinVias.at(k);
      pv.placedpos = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, pv.originpos, LL, sel);
      pv.UpperMetalRect.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, pv.UpperMetalRect.originBox, LL, sel);
      pv.LowerMetalRect.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, pv.LowerMetalRect.originBox, LL, sel);
      pv.ViaRect.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, pv.ViaRect.originBox, LL, sel);
      pv.UpperMetalRect.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, pv.UpperMetalRect.originCenter, LL, sel);
      pv.LowerMetalRect.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, pv.LowerMetalRect.originCenter, LL, sel);
      pv.ViaRect.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, pv.ViaRect.originCenter, LL, sel);
    }
  }
  // update internal metals
  for (unsigned int j = 0; j < node.Blocks.at(i).instance.at(sel).interMetals.size(); j++) {
    auto& im = nd.interMetals.at(j);
    im.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, im.originBox, LL, sel);
    im.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, im.originCenter, LL, sel);
  }
  // update internal vias
  for (unsigned int j = 0; j < node.Blocks.at(i).instance.at(sel).interVias.size(); j++) {
    auto& iv = nd.interVias.at(j);
    iv.placedpos = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, iv.originpos, LL, sel);
    iv.UpperMetalRect.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, iv.UpperMetalRect.originBox, LL, sel);
    iv.LowerMetalRect.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, iv.LowerMetalRect.originBox, LL, sel);
    iv.ViaRect.placedBox = mydesign.GetPlacedBlockInterMetalAbsBox(i, ort, iv.ViaRect.originBox, LL, sel);
    iv.UpperMetalRect.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, iv.UpperMetalRect.originCenter, LL, sel);
    iv.LowerMetalRect.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, iv.LowerMetalRect.originCenter, LL, sel);
    iv.ViaRect.placedCenter = mydesign.GetPlacedBlockInterMetalAbsPoint(i, ort, iv.ViaRect.originCenter, LL, sel);
  }
}

void ILP_solver::UpdateTerminalinHierNode(design& mydesign, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo) {
  map<int, int> terminal_to_net;
  for (unsigned int i = 0; i < node.Nets.size(); i++) {
    for (const auto& c : node.Nets[i].connected) {
      if (c.type == PnRDB::Terminal) {
        terminal_to_net[c.iter] = i;
        break;
      }
    }
  }
  for (int i = 0; i < (int)mydesign.GetSizeofTerminals(); i++) {
    auto& tC = node.Terminals.at(i).termContacts;
    tC.clear();
    for (const auto& c : node.Nets[terminal_to_net[i]].connected) {
      if (c.type == PnRDB::Terminal) continue;
      for (const auto& con : node.Blocks[c.iter2].instance[node.Blocks[c.iter2].selectedInstance].blockPins[c.iter].pinContacts) {
        tC.push_back(con);
        tC.back().originBox = tC.back().placedBox;
        tC.back().originCenter = tC.back().placedCenter;
      }
    }
  }
  /**
  for (int i = 0; i < (int)mydesign.GetSizeofTerminals(); i++) {
    auto& tC = node.Terminals.at(i).termContacts;
    tC.clear();
    tC.resize(1);
    auto c = ConvertPointData(mydesign.GetTerminalCenter(i));
    tC.back().placedCenter = c;
    // tC.back() has other fields that remain at their default values: originBox, placedBox, originCenter
    tC.back().originCenter = c;
    tC.back().originBox.LL = c;
    tC.back().originBox.UR = c;
    tC.back().placedBox.LL = c;
    tC.back().placedBox.UR = c;
  }**/
  for (int i = 0; i < (int)mydesign.GetSizeofTerminals(); i++) {
    const auto& t = node.Terminals.at(i);
    PnRDB::pin temp_pin;
    temp_pin.name = t.name;
    temp_pin.type = t.type;
    temp_pin.netIter = t.netIter;
    temp_pin.pinContacts = t.termContacts;
    for (int j = 0; j < temp_pin.pinContacts.size(); j++) temp_pin.pinContacts[j].metal = drcInfo.Metal_info[0].name;
    temp_pin.name = node.Terminals.at(i).name;
    temp_pin.type = node.Terminals.at(i).type;
    node.blockPins.push_back(temp_pin);
  }
}

void ILP_solver::UpdateSymmetryNetInfoAnalytical(design& mydesign, PnRDB::hierNode& node, int i, int SBidx, placerDB::Smark axis_dir) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.UpdateSymmetryNetInfo");

  int axis_coor = 0;
  if (axis_dir == placerDB::V) {
    if (mydesign.SBlocks[SBidx].selfsym.size() > 0) {
      // self sym x axis coordinate
      axis_coor = Blocks[mydesign.SBlocks[SBidx].selfsym[0].first].x + mydesign.Blocks[mydesign.SBlocks[SBidx].selfsym[0].first][0].width / 2;
    } else {
      // sym pair x axis coordinate
      axis_coor = Blocks[mydesign.SBlocks[SBidx].sympair[0].first].x / 2 + mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].first][0].width / 4 +
                  Blocks[mydesign.SBlocks[SBidx].sympair[0].second].x / 2 + mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].second][0].width / 4;
    }
  } else if (axis_dir == placerDB::H) {
    if (mydesign.SBlocks[SBidx].selfsym.size() > 0) {
      axis_coor = Blocks[mydesign.SBlocks[SBidx].selfsym[0].first].y + mydesign.Blocks[mydesign.SBlocks[SBidx].selfsym[0].first][0].height / 2;
    } else {
      axis_coor = Blocks[mydesign.SBlocks[SBidx].sympair[0].first].y / 2 + mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].first][0].height / 4 +
                  Blocks[mydesign.SBlocks[SBidx].sympair[0].second].y / 2 + mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].second][0].height / 4;
    }
  } else {
    logger->error("Placer-Error: incorrect symmetry axis direction");
  }
  string net1 = mydesign.SNets.at(i).net1.name;
  string net2 = mydesign.SNets.at(i).net2.name;
  for (std::vector<PnRDB::net>::iterator it = node.Nets.begin(); it != node.Nets.end(); ++it) {
    if (it->name.compare(net1) == 0 || it->name.compare(net2) == 0) {
      it->axis_dir = PnRDB::Smark(int(axis_dir));
      it->axis_coor = axis_coor;
    }
  }
}

void ILP_solver::UpdateSymmetryNetInfo(design& mydesign, PnRDB::hierNode& node, int i, int SBidx, placerDB::Smark axis_dir, SeqPair& curr_sp) {
  auto logger = spdlog::default_logger()->clone("placer.ILP_solver.UpdateSymmetryNetInfo");

  int axis_coor = 0;
  if (axis_dir == placerDB::V) {
    if (mydesign.SBlocks[SBidx].selfsym.size() > 0) {
      // self sym x axis coordinate
      axis_coor = Blocks[mydesign.SBlocks[SBidx].selfsym[0].first].x +
                  mydesign.Blocks[mydesign.SBlocks[SBidx].selfsym[0].first][curr_sp.selected[mydesign.SBlocks[SBidx].selfsym[0].first]].width / 2;
    } else {
      // sym pair x axis coordinate
      axis_coor = Blocks[mydesign.SBlocks[SBidx].sympair[0].first].x / 2 +
                  mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].first][curr_sp.selected[mydesign.SBlocks[SBidx].sympair[0].first]].width / 4 +
                  Blocks[mydesign.SBlocks[SBidx].sympair[0].second].x / 2 +
                  mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].second][curr_sp.selected[mydesign.SBlocks[SBidx].sympair[0].second]].width / 4;
    }
  } else if (axis_dir == placerDB::H) {
    if (mydesign.SBlocks[SBidx].selfsym.size() > 0) {
      axis_coor = Blocks[mydesign.SBlocks[SBidx].selfsym[0].first].y +
                  mydesign.Blocks[mydesign.SBlocks[SBidx].selfsym[0].first][curr_sp.selected[mydesign.SBlocks[SBidx].selfsym[0].first]].height / 2;
    } else {
      axis_coor = Blocks[mydesign.SBlocks[SBidx].sympair[0].first].y / 2 +
                  mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].first][curr_sp.selected[mydesign.SBlocks[SBidx].sympair[0].first]].height / 4 +
                  Blocks[mydesign.SBlocks[SBidx].sympair[0].second].y / 2 +
                  mydesign.Blocks[mydesign.SBlocks[SBidx].sympair[0].second][curr_sp.selected[mydesign.SBlocks[SBidx].sympair[0].second]].height / 4;
    }
  } else {
    logger->error("Placer-Error: incorrect symmetry axis direction");
  }
  string net1 = mydesign.SNets.at(i).net1.name;
  string net2 = mydesign.SNets.at(i).net2.name;
  for (std::vector<PnRDB::net>::iterator it = node.Nets.begin(); it != node.Nets.end(); ++it) {
    if (it->name.compare(net1) == 0 || it->name.compare(net2) == 0) {
      it->axis_dir = PnRDB::Smark(int(axis_dir));
      it->axis_coor = axis_coor;
    }
  }
}

PnRDB::bbox ILP_solver::ConvertBoundaryData(vector<placerDB::point> Bdata) {
  PnRDB::bbox newBdata;
  PnRDB::point tmpp;
  int x = Bdata.at(0).x, X = Bdata.at(0).x, y = Bdata.at(0).y, Y = Bdata.at(0).y;
  for (vector<placerDB::point>::iterator it = Bdata.begin(); it != Bdata.end(); ++it) {
    tmpp.x = it->x;
    tmpp.y = it->y;
    if ((it->x) < x) {
      x = it->x;
    }
    if ((it->x) > X) {
      X = it->x;
    }
    if ((it->y) < y) {
      y = it->y;
    }
    if ((it->y) > Y) {
      Y = it->y;
    }
  }
  newBdata.LL = {x, y};
  newBdata.UR = {X, Y};
  return newBdata;
}

PnRDB::point ILP_solver::ConvertPointData(placerDB::point Pdata) {
  PnRDB::point newPdata;
  newPdata.x = Pdata.x;
  newPdata.y = Pdata.y;
  return newPdata;
}
