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

##  Compute scalar product of generalized characters, only given the values
##  x on the classes i which start an entry of RatClassExps(G). The other
##  values on classes of the same rational class are GaloisCyc(x,kj), kj as 
##  in RatClassExps.
##
##  This is implemented for a UTable as first argument, but the same
##  method can also be used for usual characters in character tables.
InstallOtherMethod(ScalarProduct, ["IsUTable", "IsList", "IsList"],
function(UT, c, d)
  local res, rci, rce, sc, a, s, x, n, rv, p, i, l, k;
  res := 0;
  rci := RationalClassIndices(UT);
  rce := RatClassExps(UT);
  sc := SizesConjugacyClasses(UT){rci};
  for i in [1..Length(rce)] do
    a := rce[i];
    if c[i] <> 0 and d[i] <> 0 then
      s := c[i]*GaloisCyc(d[i],-1);
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
  return res/Size(UT);
end);

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

