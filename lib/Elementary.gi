###########################################################################
##  Elementary.gd
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  Functions to parameterize the maximal non-cyclic p-elementary subgroups
##  C x P of a group G up to conjugacy.
##  
##  This file provides functions 
##     MaximalNonCyclicElementarySubgroups(G)
##     InducedFromElementary(G, i, p[, "linear"/"nonlinear")
##  

##  returns list of pairs [i, p] encoding the elementary subgroups
##  <x> x P where x is an element from class i and P is a Sylow-p-subgroup
##  of the centralizer of x in G (up to conjugacy in G)
InstallMethod(MaximalNonCyclicElementarySubgroups, ["IsGroup"], function(G)
  local cls, ords, sords, sz, fac, cenords, faccen, facnoncyc, pnoncyc, pms, ratcl, 
        rord, nrat, res, notneeded, o, ncl, ps, f, op, poss, i, p, j;
  cls := ConjugacyClasses(G);
  ords := OrdersClassRepresentatives(G);
  sords := Set(ords);
  sz := Size(G);
  fac := Collected(Factors(sz));
  cenords := List(cls, c-> sz/Size(c));
  faccen := List(cenords, k-> Collected(Factors(k)));
  
  # prime divisors p of |G| with non-cyclic Sylow-p-subgroups:
  facnoncyc := Filtered(fac, a-> not a[1]^a[2] in sords);
  pnoncyc := List(facnoncyc, a-> a[1]);

  pms := PowerMapsOfAllClasses(G);
  # rational classes by positions, sort by decreasing element order
  ratcl := ShallowCopy(RationalClassSets(G));
  rord := List(ratcl, a-> ords[a[1]]);
  SortParallel(rord, ratcl, {x,y}-> y<x);
  nrat := Length(ratcl);
  
  res := [];
  notneeded := [];
  for i in [1..nrat] do
    o := rord[i];
    ncl := ratcl[i][1];
    # p with gcd(o, p) = 1
    ps := Filtered(pnoncyc, p-> o mod p <> 0 and not [i,p] in notneeded);
    for p in ps do
      f := Filtered(faccen[ncl], a-> a[1]=p);
      if Length(f) > 0 then
        # check if Sylow-p in centralizer is not cyclic
        # (then there would be an element of the order of
        # the elementary subgroup in the preimage of some
        # power map)
        op := o*f[1][1]^f[1][2];
        poss := Positions(ords, op);
        if not ForAny(poss, j-> ncl in pms[j]) then
          Add(res, [i, p]);
          # throw out smaller groups with same p-part
          # and subgroup of the cyclic part
          for j in Difference(pms[ncl], ratcl[i]) do
            if f[1] in faccen[j] then
              Add(notneeded, [First([1..nrat], m-> j in ratcl[m]), p]);
            fi;
          od;
        fi;
      fi;
    od;
  od;
  # for result translate number of rational class in number of class
  # 
  # ordering is with growing order cyclic groups
  # (in many examples we have seen that these are needed
  # anyway in the InduceRestrict algorithm, and they often
  # push down the Gram determinant significantly)
  return List(Reversed(res), a-> [ratcl[a[1]][1], a[2]]);
end);

##  computes the induced irreducible characters from an elementary subgroup
##  (given by [i, p] as above) to G
##  with optional argument "linear" only the linear characters are induced
##  with optional argument "nonlinear" only the nonlinear characters are induced
##  with an integer max in optional arguments the function returns only the
##       number of conjugacy classes of the elementary subgroup if
##       this number is larger than max
##  
##  characters are returned as list of values in Ordering of ConjugacyClasses(G)
BindGlobal("InducedFromElementary", function(GorUT, i, p, opts...)
  local G, ut, max, scen, cls, ncl, cl, x, o, cen, s, ss, t, scl, sscl, 
        fus, pms, lt, res, c, m, efus, e, j, l, k, ch, a;
  if IsGroup(GorUT) then
    G := GorUT;
    ut := UTable(G);
  elif IsUTable(GorUT) then
    ut := GorUT;
    G := UnderlyingGroup(ut);
  else
    Error("InducedFromElementary: First argument must be group or UTable");
    return;
  fi;
  k := Filtered(opts, IsInt);
  if Length(k) > 0 then
    max := k[1];
  else
    max := false;
  fi;

  scen := SizesCentralizers(ut);
  cls := ConjugacyClasses(ut);
  ncl := Length(cls);

  # if arg is UTable we store only values on reps of rational classes
  cl := cls[i];
  # generator of cyclic part
  x := Representative(cl);
  o := Order(x);
  # centralizer of representative
  cen := StabilizerOfExternalSet(cl);
  # p-part (and remove it from attribute)
  s := SylowSubgroup(cen, p);
  Remove(ComputedSylowSubgroups(cen));
  Remove(ComputedSylowSubgroups(cen));
  IsPGroup(s);
  ss := Size(s);
  if IsInt(max) and NrConjugacyClasses(s)*o > max then
    return NrConjugacyClasses(s)*o;
  fi;
  if "linear" in opts then
    t := LinearCharacters(s);
  else
    # in which cases it may be sensible to move to PcGroup?
    t := IrrBaumClausen(s);
    if "nonlinear" in opts then
      t := Filtered(t, ch-> Degree(ch) > 1);
    fi;
  fi;
  scl := ConjugacyClasses(s);
  sscl := List(scl, Size);
  # fusion of classes of x y with y reps of classes of s
  fus := List(scl, cl-> PositionConjugacyClass(G, x*Representative(cl)));

  # the rest we get from power maps
  pms := PowerMapsOfAllClasses(ut);

  # we use the character table of <x> x s without writing it down
  lt := Length(t);
  res := List([1..lt*o], i-> 0*[1..ncl]);
  c := E(o);
  for e in [0..o-1] do
    # m such that (x y)^m = x^e y
    m := ChineseRem([o, ss], [e, 1]);
    efus := List(fus, i-> pms[i][(m mod Length(pms[i]))+1]);
    for j in [1..Length(fus)] do
      for l in [0..o-1] do
        for k in [1..lt] do
          a := efus[j];
          res[l*lt+k][a] := res[l*lt+k][a] + c^(e*l)*t[k][j]*sscl[j];
        od;
      od;
    od;
  od;
  # some induced characters can be the same
  res := Set(res);
  # finally the factor coming from class lengths in G
  for j in [1..ncl] do
    c := scen[j]/ss/o;
    for ch in res do
      if not ch[j] = 0 then
        ch[j] := c*ch[j];
      fi;
    od;
  od;
  return res;
end);

# Fusion of elementary subgroup <x> x S (x in class i, S p-Sylow in
# centralizer of x): returns pair of lists [fus, needed] where fus is list of 
# lists of form
#     [j, [e1, ...], [e2, ...] ...]
# where j is number of class in G in the image, e1, e2,... exponents,
# followed by numbers k such that the classes of x^e1 y with y in class k of
# S fuse into class j of G.
# Only classes j which represent rational classes of G are considered.
# And the second entry 'needed' contains the numbers of classes of S
# occuring in fus.
BindGlobal("FusionElementaryUTable", function(UT, i, p)
  local G, cls, ncl, reps, ords, cens, s, ssz, x, o, pms, rci, todo, 
        scl, scll, oscl, e, k, excl, ko, kk, fus1, z, fus, m, efus, img, 
        poss, needed, pp, a, b, j;
  G := UnderlyingGroup(UT);
  cls := ConjugacyClasses(UT);
  ncl := NrConjugacyClasses(UT);
  reps := List(cls, Representative);
  ords := OrdersClassRepresentatives(UT);
  cens := List(cls, StabilizerOfExternalSet);
  # p-group (it is not needed later, we remove the stored attribute)
  s := SylowSubgroup(cens[i], p);
  ssz := Size(s);
  # generator of cyclic group
  x := Representative(cls[i]);
  o := ords[i];
  pms := PowerMapsOfAllClasses(UT);
  rci := RationalClassesInfo(UT);
  # restrict information to representatives of rational classes
  todo := BlistList([1..ncl], List(rci, a-> a.classes[1]));
  # classes of s
  IsSupersolvableGroup(s);
  scl := ConjugacyClasses(s);
  scll := List(scl, Size);
  oscl := OrdersClassRepresentatives(s);

  # if i<>1 we may be able to exclude some classes during identification
  e := Exponent(s);
  k := 1;
  excl := [];
  while k <= e do
    # for y in s of order k, the element 
    # x y has order k*|x| and its k-th power
    # is in the class of x^k (which we know from pms)
    ko := k*o;
    if o > 1 then
      kk := pms[i][(k mod o) + 1];
      excl[k] := Filtered([1..ncl], j-> ords[j] = ko and pms[j][k+1] <> kk);
    else
      excl[k] := [];
    fi;
    k := k*p;
  od;
  
  # fusion of classes of x y with y in reps of classes of s
  fus1 := [];
  for j in [1..Length(scl)] do
    z := x*Representative(scl[j]);
    Add(fus1, PositionConjugacyClass(G, z, excl[oscl[j]]));
  od;

  # the rest we get from power maps
  # (e+1)-th entry is fusion of x^e y, y reps of classes of s
  fus := [];
  for e in [0..o-1] do
    # m such that (x y)^m = x^e y
    if e = 1 then
      Add(fus, fus1);
    else
      m := ChineseRem([o, ssz], [e, 1]);
      efus := List(fus1, i-> pms[i][(m mod Length(pms[i]))+1]);
      Add(fus, efus);
    fi;
  od;
  
  # collect information for representing classes in rational classes
  img := Filtered(Set(Flat(fus)), j-> todo[j]);
  poss := [];
  needed := [];
  for j in img do
    pp := [j];
    for k in [0..o-1] do
      a := [k];
      b := Positions(fus[k+1], j);
      Append(a, b);
      if Length(a) > 1 then
        Add(pp, a);
        Append(needed, b);
      fi;
    od;
    Add(poss, pp);
  od;
  needed := Set(needed);

  return [poss, needed];
end);

# Here we produce a sort data with an iteration function which produces
# |x| induced irreducible characters at a time. We use 'BaumClausenInfo' and
# then compute character values as in 'IrrBaumClausen' later on the fly.
# This way we can handle elementary subgroups with a huge number of classes.
# The disadvantage is that we sometimes have some extra work because we do not
# detect if several induced characters are the same.
BindGlobal("InductionDataFromElementaryUTable", function(UT, i, p)
  local fus, needed, G, sz, cls, ncl, szcen, ords, o, st, s, ssz, scls, szscls, 
        lg, bc, pcgs, exp, q, gcdq, exps, cr, eL, eE, j, next;

  # first get the fusion data
  fus := FusionElementaryUTable(UT, i, p);
  needed := fus[2];
  fus := fus[1];
  
  # we need class lengths of G and Sylow P
  G := UnderlyingGroup(UT);
  sz := Size(UT);
  cls := ConjugacyClasses(UT);
  ncl := NrConjugacyClasses(UT);
  szcen := SizesCentralizers(UT);
  ords := OrdersClassRepresentatives(UT);
  o := ords[i];
  # p-group
  st := StabilizerOfExternalSet(cls[i]);
  s := SylowSubgroup(st, p);
  Remove(ComputedSylowSubgroups(st));
  Remove(ComputedSylowSubgroups(st));
  ssz := Size(s);
  scls := ConjugacyClasses(s);
  szscls := List(scls, Size);

  # irreducibles of s described by Baum-Clausen
  # (representations as monomial matrices on pc-generators)
  bc := ShallowCopy(BaumClausenInfo(s));
  # simplify
  bc.nonlin := List(bc.nonlin, a-> List(a, b-> [b.diag, b.perm]));
  # collect relevant data in bc
  pcgs := bc.pcgs;
  exp := bc.exponent;
  q := Gcd(exp, Length(bc.lin));
  gcdq := exp/q;

  exps := List(scls, c-> ExponentsOfPcElement(pcgs, Representative(c)));
  cr := SortedList(exps{needed});
  Unbind(bc.pcgs);
  Unbind(bc.kernel);
  Unbind(bc.exponent);
  lg := Length(pcgs);
  eL := [1];
  eE := E(o);
  for j in [1..o-1] do
    Add(eL, eL[j]*eE);
  od;
  bc.pos := 1;

  # and here is a function 'next' to iterate over chi in Irr(s)
  # which returns the induced characters of {chi x zeta, zeta in Irr(<x>)}
  next := function()
    local pos, lin, rep, mul, gcd, m, deg, id, trace, l, v,
          j, perm, diag, e, vals, res, k, sums, b, f, a, i, jj, bt, t;
    # first linear characters
    pos := bc.pos;
    lin := IsBound(bc.lin);
    if lin then
      rep := bc.lin[pos];
      for a in cr do
        Add(a, (a*rep)/gcdq mod q + 1);
      od;
      if pos = Length(bc.lin) then
        bc.pos := 1;
        Unbind(bc.lin);
      else
        bc.pos := pos+1;
      fi;
    elif pos <= Length(bc.nonlin) then
      mul := function(a, b)
        local x;
        x := [[],b[2]{a[2]}];
        x[1]{b[2]} := b[1]{b[2]} + a[1];
        return x;
      end;
      rep := bc.nonlin[pos];
      gcd:= GcdInt(Gcd(List(rep, x-> Gcd(x[1]))), exp);
      m := exp/gcd;
      deg := Length(rep[1][2]);
      id := [0*[1..deg], [1..deg]];
      trace := 0*[1..m];
      trace[1] := deg;
      Add(cr[1], trace);
      l := List([1..lg], i-> id);
      # We go through sorted list of exponents and reuse
      # partial product from previous representative.
      for i in [2..Length(cr)] do
        j := 1;
        while cr[i-1][j] = cr[i][j] do
          j := j+1;
        od;
        for k in [cr[i-1][j]+1..cr[i][j]] do
          l[j] := mul(l[j], rep[j]);
        od;
        for jj in [j+1..lg] do
          l[jj] := l[jj-1];
          for k in [1..cr[i][jj]] do
            l[jj] := mul(l[jj], rep[jj]);
          od;
        od;
        # Compute the character value.
        trace:= 0*[1..m];
        perm := l[lg][2];
        diag := l[lg][1];
        for k in [1..deg] do
          if perm[k] = k then
            e := (diag[k] / gcd) mod m;
            trace[e+1]:= trace[e+1] + 1;
          fi;
        od;
        # We append the character values to the exponents lists
        # and remove them (in the right order) after this loop.
        Add(cr[i], trace);
      od;
      bc.pos := pos+1;
    else
      return fail;
    fi;

    # now we extract the values on needed classes (coefficient lists in
    # powers of some E(?))
    vals := [];
    for j in needed do
      vals[j] := Remove(exps[j]);
    od;
    bc.vals:=vals;

    # now we compute the fusion on reps of rational classes of G
    res := List([1..o], j-> 0*[1..ncl]);
    for a in fus do
      k := a[1];
      sums := [];
      for j in [2..Length(a)] do
        b := a[j];
        if lin then
          v := 0*[1..q];
          for t in [2..Length(b)] do
            bt := b[t];
            m := vals[bt];
            v[m] := v[m] + szscls[bt];
          od;
        else
          bt := b[2];
          v := szscls[bt] * vals[bt];
          for t in [3..Length(b)] do
            bt := b[t];
            v := v + szscls[bt] * vals[bt];
          od;
        fi;
        Add(sums, CycList(v));
      od;
      f := szcen[k]/o/ssz;
      for j in [0..o-1] do
        res[j+1][k] := f*(List([2..Length(a)], l-> eL[a[l][1]*j mod o + 1])*sums);
      od;
    od;
    return EncodeForUTable(UT, res);
  end;
  bc.next := next;
  return bc;
end);

# temporary test function, should behave like 
#     EncodeForUTable(UT, InducedFromElementary(UT, i, p))
fu:=function(UT,i,p)
  local bc, next, res, a;
  bc := InductionDataFromElementaryUTable(UT,i,p);
  next := bc.next;
  res := [];
  a := next();
  while a <> fail do
    Append(res,a);
    a := next();
  od;
  return res;
end;

