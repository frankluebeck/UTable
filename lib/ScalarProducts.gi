###########################################################################
##  ScalarProducts.gi
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  These files contains functions to compute the scalar products of
##  generalized characters (Z-linear combinations of irreducible characters) 
##  of a finite group (also works for Q-linear combinations).
##  
##  Such class functions only need to be given on one conjugacy class of
##  every rational class, when power maps are available. The remaining
##  values for classes in the same rational class can be computed as 
##  Galois conjugates of the given values.
##  
##  This is used to store generalized characters in UTable(G).
##  
##  The functions here can efficiently compute scalar products of
##  generalized characters given this way.
##  

##  Every element in Q[E(n)] can be written as Q-linear combination of the
##  basis {E(n)^i| i=0..Phi(n)-1}. This function returns a list l of n integers
##  such that l[j] is the coefficient at E(n)^0=1 of E(n)^(j-1).
BindGlobal("RatPartVec", function(n)
  local cp, phi, res, v, i;
  if not IsBound(RATPARTVEC[n]) then
    cp := CyclotomicPol(n);
    phi := Length(cp)-1;
    res := 0*cp;
    res[1] := 1;
    res[phi+1] := -1;
    v := 0*cp;
    Add(v, 1);
    for i in [phi+1..n-1] do
      ReduceCoeffs(v, cp);
      Add(res, v[1]);
      v := Concatenation([0],v);
    od;
    RATPARTVEC[n] := res;
  fi;
  return RATPARTVEC[n];
end);

##  This function returns a list of lists of integers. Each entry is of form
##  [i, j, k2, ..., km] where i is the number of a class x^G, j is the number of
##  the class of x^-1, m is the number of conjugacy classes in the rational
##  class of x with representatives x, x^k2, ..., x^km (in the order of the
##  entry of RationalClassSets(G) starting with i).
##  
InstallMethod(RatClassExps, ["IsGroup"],
function(G)
  local rs, pms, res, l, pm, a, j;
  rs := RationalClassSets(G);
  pms := PowerMapsOfAllClasses(G);
  res := [];
  for a in rs do
    # first class and class of its inverses
    l := [a[1]];
    pm := pms[a[1]];
    Add(l, pm[Length(pm)]);
    for j in [2..Length(a)] do
      Add(l, Position(pm, a[j])-1);
    od;
    Add(res, l);
  od;
  return res;
end);
InstallMethod(RatClassExps, ["IsNearlyCharacterTable and HasUnderlyingGroup"], 
  UT-> RatClassExps(UnderlyingGroup(UT)));

InstallMethod(RationalClassesInfo, ["IsGroup"], function(G)
  local cl, pms, rc, rce, ords, res, last, sparsify, r, 
        pm, o, st, c, rv, e, i;
  cl := ConjugacyClasses(G);
  pms := PowerMapsOfAllClasses(G);
  rc := RationalClassSets(G);
  rce := RatClassExps(G);
  ords := OrdersClassRepresentatives(G);
  res := [];
  last := 0;
  # sparse representation of vector
  sparsify := function(v)
    local res, i;
    res := [];
    for i in [1..Length(v)] do
      if v[i]<>0 then
        Add(res, i);
        Add(res, v[i]);
      fi;
    od;
    return res;
  end;
  for i in [1..Length(rc)] do
    r := rec(classes := rc[i],
             exponents := rce[i],
             order := ords[rc[i][1]],
             classlen := Size(cl[rc[i][1]]));
    if Length(rc[i]) = 1 then
      r.conductor := 1;
      r.ind := last+1;
      last := last+1;
    else
      pm := pms[rc[i][1]];
      o := ords[rc[i][1]];
      # Galois stabilizer of class and character field
      st := Positions(pm, pm[2])-1;
      r.order := o;
      r.field := NF(o, st);
      c := Conductor(r.field);
      r.conductor := c;
      r.cpol := CyclotomicPol(c);
      r.dim := Length(r.cpol)-1;
      # adjust stabilizer if conductor is smaller than o
      if c < o then
        st := Set(st mod c);
      fi;
      r.stabilizer := st;
      r.ind := [last+1..last+r.dim];
      last := last+r.dim;
      rv := RatPartVec(c);
      e := Concatenation([1], r.exponents{[3..Length(r.exponents)]});
      # in position i the rational coefficient of
      # Sum(e, k-> E(r.conductor)^(i*k)) wrt. cyclotomic polynomial
      r.ratvec := sparsify(List([0..c-1], i-> Sum(rv{(i*e mod c)+1}))); 
      for i in [1,3..Length(r.ratvec)-1] do
        r.ratvec[i] := r.ratvec[i]-1;
      od;
    fi;
    Add(res, r);
  od;
  return res;
end);
InstallMethod(RationalClassesInfo, ["IsNearlyCharacterTable and HasUnderlyingGroup"], 
function(UT)
  return RationalClassesInfo(UnderlyingGroup(UT));
end);
# here we encode the data from RationalClassesInfo(G) needed to compute
# scalar products in a plain list of integers
InstallMethod(ScalarInfo, ["IsGroup"], function(G)
  local rci, res, pos, r;
  rci := RationalClassesInfo(G);
  # we change second entry to length + 1 later
  res := [Size(G), -1];
  pos := 3;
  for r in rci do
    if r.conductor = 1 then
      Append(res, [1, r.ind, pos+4, r.classlen]);
    else
      Append(res, [r.conductor, r.ind[1], pos+5+Length(r.ratvec),
                   r.dim, r.classlen]);
      Append(res, r.ratvec);
    fi;
    pos := Length(res)+1;
  od;
  res[2] := Length(res)+1;
  return res;
end);
InstallMethod(ScalarInfo, ["IsUTable and HasUnderlyingGroup"], 
function(UT)
  return ScalarInfo(UnderlyingGroup(UT));
end);

##  Compute scalar product of generalized characters, only given the values
##  x on the classes i which start an entry of RatClassExps(G). The other
##  values on classes of the same rational class are GaloisCyc(x,kj), kj as 
##  in RatClassExps.
##
##  This is implemented for a UTable as first argument, but the same
##  method can also be used for usual characters in character tables.

# this could also be used for usual characters:
ScalProd1 := function(t, c, d)
  local res, sc, i, j, s, x, n, rv, p, a, l, k;
  res := 0;
  c := ValuesOfClassFunction(c);
  d := ValuesOfClassFunction(d);
  sc := SizesConjugacyClasses(t);
  for a in RatClassExps(t) do
    i := a[1];
    j := a[2];
    if c[i] <> 0 and d[j] <> 0 then
      s := c[i]*d[j];
      if IsRat(s) and Length(a) > 2 then
        s := (Length(a)-1) * s;
      elif Length(a) > 2 then
        #x := COEFFS_CYC(s, Conductor(s));
        x := ExtRepOfObj(s);
        n := Length(x);
        rv := RatPartVec(n);
        s := 0;
        for l in [1..n] do
          if x[l] <> 0 then
            if rv[l] <> 0 then
              s := s+rv[l]*x[l];
            fi;
            for k in [3..Length(a)] do
              p := ((l-1)*a[k]) mod n + 1;
              if rv[p] <> 0 then
                s := s + rv[p]*x[l];
              fi;
            od;
          fi;
        od;
      fi;
      res := res + s*sc[i];
    fi;
  od;
  return res/Size(t);
end;

UTScalarProductLANG := function(UT, c, d)
  local rci, res, co, i, rv, s, x, y, n, r, k, m, ind;
  rci := RationalClassesInfo(UT);
  res := 0;
  for r in rci do
    co := r.conductor;
    if co = 1 then
      i := r.ind;
      if c[i] <> 0 and d[i] <> 0 then
        res := res + c[i] * d[i] * r.classlen;
      fi;
    else
      ind := r.ind;
      if ForAny(ind, i-> c[i] <> 0) and ForAny(ind, i-> d[i] <> 0) then
        rv := r.ratvec;
        s := r.ind[1];
        x := 0;
        for k in [1..Length(rv)/2] do
          i := rv[2*k-1];
          y := 0;
          for m in [0..co-1] do
            if c[s+m] <> 0 then
              n := m - i;
              if n < 0 then
                n := n+co;
              fi;
              if d[s+n] <> 0 then
                y := y + c[s+m]*d[s+n];
              fi;
            fi;
          od;
          if y <> 0 then
            x := x + y * rv[2*k];
          fi;
        od;
        if x <> 0 then
          res := res + x * r.classlen;
        fi;
      fi;
    fi;
  od;
  return res/Size(UT);
end;

UTScalarProduct_ratinfo := function(UT, c, d)
  local rci, res, co, i, rv, s, x, y, n, r, k, m, ind, dim;
  rci := RationalClassesInfo(UT);
  res := 0;
  for r in rci do
    co := r.conductor;
    if co = 1 then
      i := r.ind;
      if c[i] <> 0 and d[i] <> 0 then
        res := res + c[i] * d[i] * r.classlen;
      fi;
    else
      ind := r.ind;
      if ForAny(ind, i-> c[i] <> 0) and ForAny(ind, i-> d[i] <> 0) then
        rv := r.ratvec;
        dim := r.dim;
        s := r.ind[1];
        x := 0;
        for k in [1..Length(rv)/2] do
          i := rv[2*k-1];
          y := 0;
          for m in [0..dim-1] do
            if c[s+m] <> 0 then
              n := m - i;
              if n < 0 then
                n := n+co;
              fi;
              if n < dim and d[s+n] <> 0 then
                y := y + c[s+m]*d[s+n];
              fi;
            fi;
          od;
          if y <> 0 then
            x := x + y * rv[2*k];
          fi;
        od;
        if x <> 0 then
          res := res + x * r.classlen;
        fi;
      fi;
    fi;
  od;
  return res/Size(UT);
end;

UTScalarProduct := function(UT, c, d)
  local sci, done, res, pos, co, i, dim, rg, rv, x, j, y, n, k, m;
  sci := ScalarInfo(UT);
  done := sci[2];
  res := 0;
  pos := 3;
  # loop over rational classes
  while pos < done do
    co := sci[pos];
    i := sci[pos+1];
    if co = 1 then
      if c[i] <> 0 and d[i] <> 0 then
        res := res + c[i] * d[i] * sci[pos+3];
      fi;
    else
      dim := sci[pos+3];
      rg := [0..dim-1];
      if ForAny(rg, j-> c[i+j] <> 0) and ForAny(rg, j-> d[i+j] <> 0) then
        x := 0;
        for k in [pos+5, pos+7..sci[pos+2]-2] do
          j := sci[k];
          y := 0;
          for m in [0..dim-1] do
            if c[i+m] <> 0 then
              n := m - j;
              if n < 0 then
                n := n+co;
              fi;
              if n < dim and d[i+n] <> 0 then
                y := y + c[i+m]*d[i+n];
              fi;
            fi;
          od;
          if y <> 0 then
            x := x + y * sci[k+1];
          fi;
        od;
        if x <> 0 then
          res := res + x * sci[pos+4];
        fi;
      fi;
    fi;
    pos := sci[pos+2];
  od;
  return res/sci[1];
end;

if IsBound(UTScalarProductInternal) then
  InstallOtherMethod(ScalarProduct, ["IsUTable", "IsList", "IsList"],
  function(UT, c, d)
    return UTScalarProductInternal2(ScalarInfo(UT), c, d);
  end);
else
  InstallOtherMethod(ScalarProduct, ["IsUTable", "IsList", "IsList"],
  function(UT, c, d)
    return UTScalarProduct(UT, c, d);
  end);
fi;

