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
#include        <stdlib.h>
#include        <limits.h>

/*          the functions         */

/* space to cache arguments */
static long lencache;
static Obj *csci, *cc, *cd;

/* caching functions */
void cachec(Obj c) 
{
  long i;
  if (c == cc[0]) return;
  cc[0] = c;
  for(i=1; i<=LEN_PLIST(c); i++) {
    cc[i] = ELM_PLIST(c, i);
  }
}
void cached(Obj d) 
{
  long i;
  if (d == cd[0]) return;
  cd[0] = d;
  for(i=1; i<=LEN_PLIST(d); i++) {
    cd[i] = ELM_PLIST(d, i);
  }
}
void cachesci(Obj sci)
{
  long i, done, pos, co, k, bnd;
long count=1;
  if (csci[0] == sci) return;
  for(i=1; i<=LEN_PLIST(sci); i++) {
    csci[i] = ELM_PLIST(sci, i);
  }
  /* we want some entries as C integers */
  done = INT_INTOBJ(csci[2]);
  csci[2] = (Obj)done;
  pos = 3;
  while (pos < done) {
    co = INT_INTOBJ(csci[pos]);
    csci[pos] = (Obj)co;
    csci[pos+1] = (Obj)INT_INTOBJ(csci[pos+1]);
    csci[pos+2] = (Obj)INT_INTOBJ(csci[pos+2]);
    if (co != 1) {
      csci[pos+3] = (Obj)INT_INTOBJ(csci[pos+3]);
      for(k=pos+5, bnd=(long)csci[pos+2]-1; 
          k<bnd; k += 2) {
        csci[k] = (Obj)INT_INTOBJ(csci[k]);
      }
    }
    pos = (long)csci[pos+2];
  }
}

/* The following two functions are C-versions of the GAP-function 
   UTScalarProduct. The variant FuncUTScalarProductInternal2 caches
   its arguments in a buffer (it is often called for the same table
   or even the same first or second character in a row).
*/

Obj FuncUTScalarProductInternal2( Obj self, Obj sci, Obj c, Obj d)
{
  Obj res, x, y, z, ci, di;
  long max, pos, done, co, i, j, k, m, n, bnd, dim;
  int cnz, dnz;
  Obj null = INTOBJ_INT(0);

  if (! (IS_PLIST(sci) || LEN_PLIST(sci) < 2))
    ErrorQuit("first argument must be plain list of length >= 2.",0L,0L);
  if (! (IS_PLIST(c) || LEN_PLIST(c) < 1))
    ErrorQuit("second argument must be plain list of length >= 1.",0L,0L);
  if (! (IS_PLIST(d) || LEN_PLIST(d) < 1))
    ErrorQuit("third argument must be plain list of length >= 1.",0L,0L);
  max = LEN_PLIST(sci);
  if (LEN_PLIST(c) > max) max = LEN_PLIST(c);
  if (LEN_PLIST(d) > max) max = LEN_PLIST(d);
  if (max > lencache-1) {
    lencache = max+10000;
    csci = (Obj*) realloc((void*)csci, lencache*sizeof(Obj));
    cc = (Obj*) realloc((void*)cc, lencache*sizeof(Obj));
    cd = (Obj*) realloc((void*)cd, lencache*sizeof(Obj));
  }
  cachec(c);
  cached(d);
  cachesci(sci);

  done = (long)csci[2];
  res = null;
  pos = 3;
  while (pos < done) {
    co = (long)csci[pos];
    i = (long)csci[pos+1];
    if (co == 1) {
      ci = cc[i];
      di = cd[i];
      if (ci != null && di != null) { 
        z = ProdInt(ci, di);
        z = ProdInt(z, csci[pos+3]);
        res = SumInt(res, z);
      }
    } else {
      dim = (long)csci[pos+3];
      /* check if entries are non-zero */
      cnz = 0;
      for(j=0; j<dim && cnz == 0; j++) {
        if (cc[i+j] != null)
          cnz = 1;
      }
      dnz = 0;
      for(j=0; j<dim && dnz == 0; j++) {
        if (cd[i+j] != null)
          dnz = 1;
      }
      if (cnz && dnz) {
        x = null;
        for(k=pos+5, bnd=(long)csci[pos+2]-1; 
            k<bnd; k += 2) {
          j = (long)csci[k];
          y = null;
          for(m=0; m<dim; m++){
            ci = cc[i+m];
            if (ci != null) {
              n = m - j;
              if (n<0) n += co;
              di = cd[i+n];
              if (n<dim && di != null) {
                z = ProdInt(ci, di);
                y = SumInt(y, z);
              }
            }
          }
          if (y != null) {
            z = ProdInt(csci[k+1], y);
            x = SumInt(x, z);
          }
        }
        if (x != null) {
          z = ProdInt(x, csci[pos+4]);
          res = SumInt(res, z);
        }
      }
    }
    pos = (long)csci[pos+2];
  }
  res = QuoInt(res, csci[1]);
  return res;
}


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

  { "UTScalarProductInternal2", 3, "sci, char1, char2", 
    FuncUTScalarProductInternal2, 
    "scalar.c:UTScalarProductInternal2" },

  { 0 }

};

/****************************************************************************
*F  InitKernel( <module> )  . . . . . . . . initialise kernel data structures
*/
static Int InitKernel (
    StructInitInfo *    module )
{

    /* create argument caches */
    lencache = 10000;
    csci = (Obj*) malloc(10000*sizeof(Obj));
    cc = (Obj*) malloc(10000*sizeof(Obj));
    cd = (Obj*) malloc(10000*sizeof(Obj));

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

