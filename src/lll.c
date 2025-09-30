/***************************************************************************
**
*A  lll.c            C-version of ReduceLLLRecord               Frank Lübeck
**
**  
*Y  Copyright (C) 2025  Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
**  
**  `ReduceLLLRecord' as kernel function.
**  
*/


/* read GAP source header files with a combined header file */

#include        "gap_all.h"          /* GAP headers                */


#include        <stdio.h>
#include        <stdlib.h>
#include        <limits.h>

/*          the functions         */

//Obj RED(Obj gram, Obj mue, Obj H, Obj nint, Obj kint, Obj lint, Obj rint)
Obj RED(Obj gram, Obj mue, Obj H, long n, long k, long l, long r)
{
  long i, j;
  Obj rat, x, y, xx, xi, a, b, q, t1, t2;

  Obj null=INTOBJ_INT(0), one=INTOBJ_INT(1), two=INTOBJ_INT(2);

  if (l == 0) return NULL;

  a = ELM_PLIST(mue, k);
  rat = ELM_PLIST(a, l);
  if (IS_INT(rat)) {
    if (rat == null)
      return NULL;
    q = rat;
    rat = null;
  } else {
    x = NUM_RAT(rat);
    y = DEN_RAT(rat);
    xx = ProdInt(two, x);
    xi = AInvInt(xx);
    if (!LtInt(y, xx) && !LtInt(y, xi))
      return NULL;
    if (!IS_NEG_INT(x)) {
      t1 = SumInt(xx,y);
      t2 = ProdInt(two,y);
      q = QuoInt(t1, t2);
    } else {
      t1 = DiffInt(xx,y);
      t2 = ProdInt(two,y);
      q = QuoInt(t1, t2);
    }
    rat = DIFF(rat, q);
  }

  a = ELM_PLIST(gram, k);
  x = ELM_PLIST(a, l);
  if (x != null) {
    y = ELM_PLIST(a, k);
    t2 = ProdInt(q, x);
    y = DiffInt(y, t2);
    SET_ELM_PLIST(a, k, y);
    CHANGED_BAG(a);
  } 
  b = ELM_PLIST(gram, l);
  for (i=r+1; i<=l; i++) {
    x = ELM_PLIST(b, i);
    if (x != null) {
      t1 = ELM_PLIST(a, i);
      t2 = ProdInt(q, x);
      y = DiffInt(t1, t2);
      SET_ELM_PLIST(a, i, y);
      CHANGED_BAG(a);
    }
  }
  for (i=l+1; i<=k; i++) {
    b = ELM_PLIST(gram, i);
    b = ELM_PLIST(b, l);
    if (b != null) {
      t1 = ELM_PLIST(a, i);
      t2 = ProdInt(q, b);
      y = DiffInt(t1, t2);
      SET_ELM_PLIST(a, i, y);
      CHANGED_BAG(a);
    }
  }
  for (i=k+1; i<=n; i++) {
    a = ELM_PLIST(gram, i);
    b = ELM_PLIST(a, l);
    if (b != null) {
      t1 = ELM_PLIST(a, k);
      t2 = ProdInt(q, b);
      y = DiffInt(t1, t2);
      SET_ELM_PLIST(a, k, y);
      CHANGED_BAG(a);
    }
  }

  a = ELM_PLIST(mue, k);
  b = ELM_PLIST(mue, l);
  SET_ELM_PLIST(a, l, rat);
  CHANGED_BAG(a);
  for (i=r+1; i<=l-1; i++) {
    x = ELM_PLIST(b, i);
    if (x != null) {
      t1 = ELM_PLIST(a, i);
      t2 = PROD(q, x);
      y = DIFF(t1, t2);
      SET_ELM_PLIST(a, i, y);
      CHANGED_BAG(a);
    }
  }

  a = ELM_PLIST(H, k);
  b = ELM_PLIST(H, l);
  for (i=1; i<=n; i++) {
    x = ELM_PLIST(b, i);
    if (x != null) {
      t1 = ELM_PLIST(a, i);
      t2 = ProdInt(q, x);
      y = DiffInt(t1, t2);
      SET_ELM_PLIST(a, i, y);
      CHANGED_BAG(a);
    }
  }
  return NULL;
}

int cond(Obj B, Obj mue, Obj y, long k) 
{
  Obj z;
  z = ELM_PLIST(ELM_PLIST(mue, k), k-1);
  z = DIFF(y, PROD(z, z));
  z = PROD(z, ELM_PLIST(B, k-1));
  return LT(ELM_PLIST(B, k), z);
}

Obj FuncReduceLLLRecordInternal(Obj self, Obj LR, Obj y)
{
  Obj gram, mue, B, H, ak, a, b, z, q, bk, muek, akj, mmue, BB, row;
  long r, n, k, kmax, i, j, l;
  Obj *ptr, *pa, *pb;
  Obj t1, t2;
  Obj null=INTOBJ_INT(0), one=INTOBJ_INT(1);

  gram = ELM_REC(LR, RNamName("gram"));
  CLEAR_FILTS_LIST(gram);
  mue = ELM_REC(LR, RNamName("mue"));
  CLEAR_FILTS_LIST(mue);
  B = ELM_REC(LR, RNamName("B"));
  CLEAR_FILTS_LIST(B);
  H = ELM_REC(LR, RNamName("H"));
  CLEAR_FILTS_LIST(H);
  r = INT_INTOBJ(ELM_REC(LR, RNamName("r")));
  n = INT_INTOBJ(ELM_REC(LR, RNamName("n")));
  kmax = INT_INTOBJ(ELM_REC(LR, RNamName("kmax")));

  k = kmax + 1;

  for (i=1; i<=kmax; i++) {
    a = ELM_PLIST(H, i);
    GROW_PLIST(a, n);
    ptr=ADDR_OBJ(a);
    for (j=k; j<=n; j++) 
      ptr[j] = null;
    SET_LEN_PLIST(a, n);
    CHANGED_BAG(a);
  }
  GROW_PLIST(H, n);

  for (i=k; i<=n; i++) {
    a = NEW_PLIST(T_PLIST, n);
    ptr=ADDR_OBJ(a);
    for (j=1; j<=n; j++)
      ptr[j] = null;
    ptr[i] = one;
    SET_LEN_PLIST(a, n);
    CHANGED_BAG(a);
    SET_ELM_PLIST(H, i, a);
    CHANGED_BAG(H);
  }
  SET_LEN_PLIST(H, n);

  ak = NEW_PLIST(T_PLIST, n);
  SET_LEN_PLIST(ak, n);

  GROW_PLIST(B, n);
  GROW_PLIST(mue, n);
  while (k <= n) {
    if (k > kmax) {
      kmax = k;
      a = ELM_PLIST(gram, k);
      bk = ELM_PLIST(a, k);
      muek = NEW_PLIST(T_PLIST, k-1);
      SET_LEN_PLIST(muek, k-1);
      for (j=r+1; j<=k-1; j++) {
        b = ELM_PLIST(mue, j);
        akj = ELM_PLIST(a, j);
        for (i=r+1; i<=j-1; i++) {
          t1 = ELM_PLIST(b, i);
          t2 = ELM_PLIST(ak, i);
          t2 = PROD(t1, t2);
          akj = DIFF(akj, t2);
        }
        z = QUO(akj, ELM_PLIST(B, j));
        SET_ELM_PLIST(muek, j, z);
        CHANGED_BAG(muek);
        t2 = PROD(z, akj);
        bk = DIFF(bk, t2);
        SET_ELM_PLIST(ak, j, akj);
        CHANGED_BAG(ak);
      }
      SET_ELM_PLIST(B, k, bk);
      SET_LEN_PLIST(B, k);
      CHANGED_BAG(B);
      SET_ELM_PLIST(mue, k, muek);
      SET_LEN_PLIST(mue, k);
      CHANGED_BAG(mue);
    }

    if (k > 1) {
      RED(gram, mue, H, n, k, k-1, r);
      while (cond(B, mue, y, k)) {
        ptr = ADDR_OBJ(H);
        q = ptr[k];
        ptr[k] = ptr[k-1];
        ptr[k-1] = q;

        a = ELM_PLIST(gram, k);
        pa = ADDR_OBJ(a);
        b = ELM_PLIST(gram, k-1);
        pb = ADDR_OBJ(b);
        for (j=r+1; j<=k-2; j++) {
          q = pa[j];
          pa[j] = pb[j];
          pb[j] = q;
        }
        for (j=k+1; j<=n; j++) {
          pa = ADDR_OBJ(ELM_PLIST(gram, j));
          q = pa[k];
          pa[k] = pa[k-1];
          pa[k-1] = q;
        }
        a = ELM_PLIST(gram, k);
        pa = ADDR_OBJ(a);
        q = pb[k-1];
        pb[k-1] = pa[k];
        pa[k] = q;

        pa = ADDR_OBJ(ELM_PLIST(mue, k));
        pb = ADDR_OBJ(ELM_PLIST(mue, k-1));
        for (j=r+1; j<=k-2; j++) {
          q = pa[j];
          pa[j] = pb[j];
          pb[j] = q;
        }
        
        mmue = ELM_PLIST(ELM_PLIST(mue, k), k-1);
        BB = PROD(mmue, mmue);
        t2 = ELM_PLIST(B, k-1);
        BB = PROD(BB, t2);
        t1 = ELM_PLIST(B, k);
        BB = SUM(t1, BB);

        if (BB == null) {
          SET_ELM_PLIST(B, k, ELM_PLIST(B, k-1));
          SET_ELM_PLIST(B, k-1, null);

          for (i=k+1; i<=kmax; i++) {
            pa = ADDR_OBJ(ELM_PLIST(mue, i));
            q = pa[k];
            pa[k] = pa[k-1];
            pa[k-1] = q;
          }
        } else if (ELM_PLIST(B, k) == null && mmue != null) {
          SET_ELM_PLIST(B, k-1, BB);
          CHANGED_BAG(B);
          b = QUO(one, mmue);
          a = ELM_PLIST(mue, k);
          SET_ELM_PLIST(a, k-1, b);
          CHANGED_BAG(a);

          for (i=k+1; i<=kmax; i++) {
            a = ELM_PLIST(mue, i);
            t1 = ELM_PLIST(a, k-1);
            z = PROD(t1, b);
            SET_ELM_PLIST(a, k-1, z);
            CHANGED_BAG(a);
          } 
        } else {
          t1 = ELM_PLIST(B, k-1);
          q = QUO(t1, BB);
          b = PROD(mmue, q);
          a = ELM_PLIST(mue, k);
          SET_ELM_PLIST(a, k-1, b);
          CHANGED_BAG(a);
          t1 = ELM_PLIST(B, k);
          z = PROD(t1, q);
          SET_ELM_PLIST(B, k, z);
          SET_ELM_PLIST(B, k-1, BB);
          CHANGED_BAG(B);

          for (i=k+1; i<=kmax; i++) {
            a = ELM_PLIST(mue, i);
            q = ELM_PLIST(a, k);
            t1 = ELM_PLIST(a, k-1);
            t2 = PROD(mmue, q);
            z = DIFF(t1, t2);
            SET_ELM_PLIST(a, k, z);
            CHANGED_BAG(a);
            t2 = PROD(b, z);
            z = SUM(q, t2);
            SET_ELM_PLIST(a, k-1, z);
            CHANGED_BAG(a);
          }
        }
        if (k>2) k--;
        RED(gram, mue, H, n, k, k-1, r);
      }
    }

    if (ELM_PLIST(B, r+1) == null) r++;

    for (l=k-2; l>=r+1; l--) {
      RED(gram, mue, H, n, k, l, r);
    }
    k++;
  }
 
  ASS_REC(LR, RNamName("kmax"), INTOBJ_INT(kmax));
  ASS_REC(LR, RNamName("r"), INTOBJ_INT(r));
  CHANGED_BAG(LR);

  return NULL;
}
                                

/*F * * * * * * * * * * * * * initialize package * * * * * * * * * * * * * */

/****************************************************************************
*V  GVarFuncs . . . . . . . . . . . . . . . . . . list of functions to export
*/
static StructGVarFunc GVarFuncs [] = {

  { "ReduceLLLRecordInternal", 2, "LR, delta", 
    FuncReduceLLLRecordInternal, 
    "lll.c:ReduceLLLRecordInternal" },

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
    .name = "lll",
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

