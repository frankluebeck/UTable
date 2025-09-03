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
##  
##  characters are returned as list of values in Ordering of ConjugacyClasses(G)
BindGlobal("InducedFromElementary", function(GorUT, i, p, opts...)
  local G, ut, scen, cls, ncl, cl, x, o, cen, s, ss, t, scl, sscl, 
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
  # p-part
  s := SylowSubgroup(cen, p);
  ss := Size(s);
  if "linear" in opts then
    t := LinearCharacters(s);
  else
    t := Irr(s);
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


