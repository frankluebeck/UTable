/***************************************************************************
**
*A  scalar.c            Helper for scalar products              Frank Lübeck
**
**  
*Y  Copyright (C) 2025  Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
**  
**  `UTScalarProductInternal' as kernel function.
**  
*/


/* read GAP source header files with a combined header file */

#include        "gap_all.h"          /* GAP headers                */


#include        <stdio.h>
#include        <limits.h>

/*          the functions         */


/* This function is transformed from a stand alone  C-program, which looks
   very much like the corresponding GAP-function.
   Instead of 'malloc' we use here 'NewBag' with type 'T_DATOBJ'. */ 

Obj FuncUTScalarProductInternal( Obj self, Obj sci, Obj c, Obj d)
{
  Obj res, x, y, z, ci, di;
  long pos, done, co, i, j, k, m, n, bnd, dim;
  int cnz, dnz;
  Obj null = INTOBJ_INT(0);

  if (! (IS_PLIST(sci) || LEN_PLIST(sci) < 2))
    ErrorQuit("first argument must be plain list of length >= 2.",0L,0L);
  if (! (IS_PLIST(c) || LEN_PLIST(c) < 1))
    ErrorQuit("second argument must be plain list of length >= 1.",0L,0L);
  if (! (IS_PLIST(d) || LEN_PLIST(d) < 1))
    ErrorQuit("third argument must be plain list of length >= 1.",0L,0L);


  done = INT_INTOBJ(ELM_PLIST(sci, 2));
  res = null;
  pos = 3;
  while (pos < done) {
    co = INT_INTOBJ(ELM_PLIST(sci, pos));
    i = INT_INTOBJ(ELM_PLIST(sci, pos+1));
    if (co == 1) {
      ci = ELM_PLIST(c, i);
      di = ELM_PLIST(d, i);
      if (ci != null && di != null) { 
        z = ProdInt(ci, di);
        z = ProdInt(z, ELM_PLIST(sci, pos+3));
        res = SumInt(res, z);
      }
    } else {
      dim = INT_INTOBJ(ELM_PLIST(sci, pos+3));
      /* check if entries are non-zero */
      cnz = 0;
      for(j=0; j<dim && cnz == 0; j++) {
        if (ELM_PLIST(c, i+j) != null)
          cnz = 1;
      }
      dnz = 0;
      for(j=0; j<dim && dnz == 0; j++) {
        if (ELM_PLIST(d, i+j) != null)
          dnz = 1;
      }
      if (cnz && dnz) {
        x = null;
        for(k=pos+5, bnd=INT_INTOBJ(ELM_PLIST(sci, pos+2))-1; 
            k<bnd; k += 2) {
          j = INT_INTOBJ(ELM_PLIST(sci, k));
          y = null;
          for(m=0; m<dim; m++){
            ci = ELM_PLIST(c, i+m);
            if (ci != null) {
              n = m - j;
              if (n<0) n += co;
              di = ELM_PLIST(d, i+n);
              if (n<dim && di != null) {
                z = ProdInt(ci, di);
                y = SumInt(y, z);
              }
            }
          }
          if (y != null) {
            z = ProdInt(ELM_PLIST(sci, k+1), y);
            x = SumInt(x, z);
          }
        }
        if (x != null) {
          z = ProdInt(x, ELM_PLIST(sci, pos+4));
          res = SumInt(res, z);
        }
      }
    }
    pos = INT_INTOBJ(ELM_PLIST(sci, pos+2));
  }
  res = QuoInt(res, ELM_PLIST(sci, 1));
  return res;
}

                                

/*F * * * * * * * * * * * * * initialize package * * * * * * * * * * * * * */

/****************************************************************************
*V  GVarFuncs . . . . . . . . . . . . . . . . . . list of functions to export
*/
static StructGVarFunc GVarFuncs [] = {

  { "UTScalarProductInternal", 3, "sci, char1, char2", 
    FuncUTScalarProductInternal, 
    "scalar.c:UTScalarProductInternal" },

  { 0 }

};

/****************************************************************************
*F  InitKernel( <module> )  . . . . . . . . initialise kernel data structures
*/
static Int InitKernel (
    StructInitInfo *    module )
{

    /* init filters and functions                                          */
    InitHdlrFuncsFromTable( GVarFuncs );

    /* return success                                                      */
    return 0;
}


/****************************************************************************
*F  InitLibrary( <module> ) . . . . . . .  initialise library data structures
*/
static Int InitLibrary (
    StructInitInfo *    module )
{
    /* init filters and functions                                          */
    InitGVarFuncsFromTable( GVarFuncs );

    /* return success                                                      */
    return 0;
}


/****************************************************************************
**
*F  InitInfopl()  . . . . . . . . . . . . . . . . . table of init functions
*/
/* <name> returns the description of this module                           */
static StructInitInfo module = {
#ifdef SCALARSTATIC
    .type = MODULE_STATIC,
#else
    .type = MODULE_DYNAMIC,
#endif
    .name = "scalar",
    .initKernel = InitKernel,
    .initLibrary = InitLibrary,
};

#ifndef SCALARSTATIC
StructInitInfo * Init__Dynamic ( void )
{
 return &module;
}
#endif

StructInitInfo * Init__scalar ( void )
{
  return &module;
}

