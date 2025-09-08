###########################################################################
##  UTable.gi
##  
##  (C) 2025 Frank Lübeck, Lehrstuhl für Algebra und Zahlentheorie, RWTH Aachen
##  
##  These files contains functions to create a UTable for a finite group.
##  This will be used as a container for computing the irreducible characters
##  of the group without using 'CharacterTable'.
##  
##  Characters are stored as lists of values only on representing classes of
##  rational classes (the remaining values can be computed with GaloisCyc,
##  see 'RatClassExps'.
##  
##  We install various attributes for UTable which delegate to the group.
##  
##  Furthermore, there are functions to import generalized characters in
##  various formats, and to LLL-reduce the lattice of generalized characters
##  found so far.
##  
##  The method 'Irr' for a 'UTable' computes all irreducibles, essentially
##  via Unger's algorithm, using the functionality of this package.

# create (empty) UTable
InstallMethod(UTable, ["IsGroup"], function(G)
  local res;
  # we have lists for characters: i irreducible,
  # n: newly imported or computed characters
  # and an LLL record to which we can add new characters and
  # extract irreducible ones
  res := ObjectifyWithAttributes(rec(ichars := [], nchars := []), 
                                 UTableType, UnderlyingGroup, G);
  res!.lll := LLLRecord({v,w}-> ScalarProduct(res, v, w), 9/10);
  return res;
end);
InstallMethod(ViewObj, ["IsUTable"], function(UT)
  Print("UTable( ");
  ViewObj(UnderlyingGroup(UT));
  Print(" )");
end);
InstallMethod(PrintObj, ["IsUTable"], function(UT)
  Print("UTable( ");
  PrintObj(UnderlyingGroup(UT));
  Print(" )");
end);

# delegate some attributes to group
InstallOtherMethod(Size, ["IsUTable"], 
  UT-> Size(UnderlyingGroup(UT)));
InstallOtherMethod(ConjugacyClasses, ["IsUTable"], 
  UT-> ConjugacyClasses(UnderlyingGroup(UT)));
InstallOtherMethod(NrConjugacyClasses, ["IsUTable"], 
  UT-> NrConjugacyClasses(UnderlyingGroup(UT)));
InstallOtherMethod(PowerMapsOfAllClasses, ["IsUTable"], 
  UT-> PowerMapsOfAllClasses(UnderlyingGroup(UT)));
InstallOtherMethod(RationalClassSets, ["IsUTable"], 
  UT-> RationalClassSets(UnderlyingGroup(UT)));
InstallMethod(NrRationalClasses, ["IsUTable"], 
  UT-> Length(RationalClassSets(UT)));
InstallMethod(NrRationalClasses, ["IsGroup"], 
  G-> Length(RationalClassSets(G)));
InstallMethod(RationalClassIndices, ["IsGroup"], 
  G-> List(RationalClassSets(G), a-> a[1]));
InstallMethod(RationalClassIndices, ["IsUTable"], 
  UT-> RationalClassIndices(UnderlyingGroup(UT)));
InstallOtherMethod(OrdersClassRepresentatives, ["IsUTable"],
  UT-> List(ConjugacyClasses(UT), c-> Order(Representative(c))));
InstallOtherMethod(SizesConjugacyClasses, ["IsUTable"],
  UT-> List(ConjugacyClasses(UT), Size));


##  importing generalized characters on all classes (ordered as in G)
##  or from character table of G, they are added to
##  the list of new characters UT!.nchars after subtracting the projection
##  on the space of already known irreducibles
##  
##  Note: only rational linear combinations of irreducibles can be handled
##  here, not arbitrary class functions!

# First a separate function to encode a characters as integer vector;
# each character can be a list of values (in the ordering of the conjugacy 
# classes of the group) or 
# a class function object (values in ordering of the
# IdentificationOfConjugacyClasses of the table, if this is set).
BindGlobal("EncodeForUTable", function(UT, l)
  local rci, ind, len, res, t, idc, ch, c, v, r, co, pol, cc, s, i, j;
  rci := RationalClassesInfo(UT);
  ind := List(rci, a-> a.classes[1]);
  len := Length(ind);
  res := [];
  for ch in l do
    if HasUnderlyingCharacterTable(ch) then
      t := UnderlyingCharacterTable(ch);
      if HasIdentificationOfConjugacyClasses(t) then
        idc := IdentificationOfConjugacyClasses(t);
        ch := AsList(ch);
        c := [];
        c{idc} := ch;
        ch := c;
      else
        ch := AsList(ch);
      fi;
    fi;
      
    ch := ch{ind};
    v := [];
    for i in [1..len] do
      r := rci[i];
      co := r.conductor;
      if co = 1 then
        Add(v, ch[i]);
      else
        if IsRat(ch[i]) then
          Add(v, ch[i]);
          for j in [2..r.dim] do
            Add(v, 0);
          od;
        else
          pol := r.cpol;
          cc := CoeffsCyc(ch[i], co);
          s := ReduceCoeffs(cc, pol);
          for j in [1..s] do
            Add(v,cc[j]);
          od;
          for j in [s+1..r.dim] do
            Add(v, 0);
          od;
        fi;
      fi;
    od;
    Add(res, v);
  od;
  return res;
end);


BindGlobal("ImportToUTable", function(UT, l)
  local vs, c, v, ic;
  if Length(l) = 0 then
    return;
  fi;
  vs := EncodeForUTable(UT, l);
  for v in vs do
    # reduce with known irreducibles
    for ic in UT!.ichars do
      c := ScalarProduct(UT, v, ic);
      if c <> 0 then
        v := v - c * ic;
      fi;
    od;

    if not (IsZero(v) or v in UT!.lll.vectors or v in UT!.nchars) then
      Add(UT!.nchars, v);
    fi;
  od;
end);
# Converse of import:
# l can be a list of integer vectors in the format of characters in UT,
# or a list of integers meaning UT!.ichars{l}.
# Without argument l all characters in UT!.ichars will be expanded.
BindGlobal("ExpandFromUTable", function(UT, li...)
  local rci, res, v, c, x, vals, l, r, i;
  if Length(li) > 0 then
    li := li[1];
    if li=[] then
      return [];
    fi;
    if IsList(li) and IsInt(li[1]) then
      li := UT!.ichars{li};
    fi;
  else
    li := UT!.ichars;
  fi;
  rci := RationalClassesInfo(UT);
  res := [];
  
  for l in li do
    v := [];
    for r in rci do
      c := r.conductor;
      if c = 1 then
        v[r.classes[1]] := l[r.ind];
      else
        x := l{r.ind};
        while Length(x)<c do
          Add(x, 0);
        od;
        x := CycList(x);
        vals := [x];
        for i in [3..Length(r.exponents)] do
          Add(vals, GaloisCyc(x, r.exponents[i]));
        od;
        v{r.classes} := vals;
      fi;
    od;
    Add(res, v);
  od;
  return res;
end);

# extend LLL record by new characters in UT!.nchars
# done in a loop of adding a few new characters, reducing and cleaning 
# the LLL record (this can avoid the computation of many scalar products)
BindGlobal("ExtendLLLUTable", function(UT)
  local k, nc, lll, len, rg;
  k := 10;
  # we reduce at most k new characters at a time
  nc := UT!.nchars;
  lll := UT!.lll;
  len := Length(nc);
  rg := [1..k];
  while rg[1] <= len do
    if rg[Length(rg)] > len then
      rg := [rg[1]..len];
    fi;
    AddVectorsLLLRecord(lll, nc{rg});
    CleanLLLRecord(lll);
    rg := [rg[1]+k..rg[1]+(2*k-1)];
  od;
  UT!.nchars := [];
end);

# reduce characters in UT!.lll and
# move found irreducibles to UT!.ichars, and remove those from the remaining
# characters
BindGlobal("ReduceUTable", function(UT, delta...)
  local ncl, lll, nirr, irr, g, len, m, oc, 
        noc, ch, ng, gg, v, ni, i, j;
  lll := UT!.lll;
  if Length(delta) > 0 then
    delta := delta[1];
  else
    delta := lll.y;
  fi;
  ncl := NrConjugacyClasses(UT);
  # reduce and clean
  ReduceLLLRecord(lll, delta);
  CleanLLLRecord(lll);
  
  # now check for irreducibles and adjust
  nirr := [];
  irr := [];
  g := lll.gram;
  len := Length(g);
  for i in [1..len] do
    if g[i][i] = 1 then
      Add(irr, i);
    else
      Add(nirr, i);
    fi;
  od;
  # since g is lower triangular
  m := function(i,j)
    if j <= i then
      return g[i][j];
    else
      return g[j][i];
    fi;
  end;
  if Length(irr) > 0 then
    oc := lll.vectors;
    # new list of vectors
    noc := [];
    for i in nirr do
      ch := oc[i];
      # subtract irreducibles in irr
      for j in irr do
        ch := ch - m(i,j)*oc[j];
      od;
      Add(noc, ch);
    od;
    # new gram
    ng := [];
    gg := [];
    for i in nirr do
      # write reduced character as sum of new irreducibles and remain
      # (all mutually orthogonal) -> easy to get new gram entry from old
      gg[i] := List(irr, k-> m(i,k));
      v := [];
      for j in nirr do
        if j <= i then
          Add(v, g[i][j] - gg[i]*gg[j]);
        fi;
      od;
      Add(ng, v);
    od;
    # remove zero characters from new characters
    for i in [Length(noc), Length(noc)-1..1] do
      if IsZero(noc[i]) then
        Remove(noc, i);
        Remove(ng, i);
        for v in ng do
          Remove(v, i);
        od;
      fi;
    od;
    # move the new irreducibles (after adjusting sign)
    ni := oc{irr};
    for ch in ni do
      if ch[1] < 0 then
        Add(UT!.ichars, -ch);
      else
        Add(UT!.ichars, ch);
      fi;
    od;
    # reset LLL record
    lll.vectors := noc;
    lll.gram := ng;
    lll.n := Length(ng);
    lll.kmax := 0;
    lll.r := 0;
    lll.mue := [];
    lll.B := [];
    lll.H := [];
    ReduceLLLRecord(lll, delta);
  fi;
  Info(InfoUTable, 1, "|irr| = ",Length(UT!.ichars), "/", ncl,  " |other| = ",
       Length(UT!.lll.vectors), " det(Gram) = ", DeterminantGramUTable(UT));
end);

# Can be useful information
BindGlobal("DeterminantGramUTable", function(UT)
  return Product(Filtered(UT!.lll.B, c-> c<>0));
end);

# The main automatic function.
# Can be called from the start or after adding characters by hand.
InstallOtherMethod(Irr, ["IsUTable"], 
function(UT)
  local G, len, scen, ncl, ords, op, v, l, det, mc, mnc, g, i, a, j;
  G := UnderlyingGroup(UT);
  len := NrRationalClasses(UT);
  scen := SizesCentralizers(UT);
  ncl := NrConjugacyClasses(UT);
  ords := OrdersClassRepresentatives(UT);
  op := function(i, p)
    local sz, res;
    sz := scen[i]/p;
    res := 1;
    while IsInt(sz) do
      res := res*p;
      sz := sz/p;
    od;
    return res;
  end;


  # induce from all (maximal) cyclic subgroups
  Info(InfoUTable, 1, "Induce from maximal cyclic subgroups");
  ImportToUTable(UT, InducedFromAllMaximalCyclicSubgroups(G));
  
  # Note that it is not good to add the trivial character as
  # irreducible first, because reduction with it will make
  # sparse induced characters non-sparse.
  Info(InfoUTable, 1, "Trivial and natural characters");
  ImportToUTable(UT, [0*[1..ncl]+1]);
  l := NaturalCharacters(G);
  ImportToUTable(UT, l);

  ExtendLLLUTable(UT);
  ReduceUTable(UT);
  if Length(UT!.ichars) = ncl then
    Sort(UT!.ichars);
    return UT!.ichars;
  fi;

  # And some cheap characters from power maps
  Info(InfoUTable, 1, "Cheap characters from power maps");
  l := SmallPowerMapCharacters(G);
  ImportToUTable(UT, l);

  # Reduce these
  ExtendLLLUTable(UT);
  ReduceUTable(UT);
  if Length(UT!.ichars) = ncl then
    Sort(UT!.ichars);
    return UT!.ichars;
  fi;

  # now induce from (maximal) non-cyclic elementary subgroups
  mnc := MaximalNonCyclicElementarySubgroups(G);
  if not IsBound(UT!.mncdone) then
    UT!.mncdone := [];
    UT!.mncbig := [];
    UT!.mncbigncl := [];
  fi;
  # first only cases where p is still in determinant of Gram matrix
  # (this is in the index of the lattice found so far)
  for a in mnc do
    if not a in UT!.mncdone then
      det := DeterminantGramUTable(UT);
      if det mod a[2] = 0 then
        # avoid excessive number of induced characters
        l := InducedFromElementary(UT, a[1], a[2], 1000);
        if IsInt(l) then
          Info(InfoUTable, 1, "Skipping elementary ",a,
               " with ",l," conjugacy classes");
          Add(UT!.mncbig, a);
          Add(UT!.mncbigncl, l);
        else
          Info(InfoUTable, 1, "Induce from elementary ", a,
                " |C|=",ords[a[1]]," |P|=",op(a[1], a[2]));
          ImportToUTable(UT, l);
          AddSet(UT!.mncdone, a);
          ExtendLLLUTable(UT);
          ReduceUTable(UT);
          if Length(UT!.ichars) = ncl then
            Sort(UT!.ichars);
            return UT!.ichars;
          fi;
        fi;
      fi;
    fi;
  od;
  # if not done the remaining cases with not too many classes
  for a in mnc do
    if not a in UT!.mncdone and not a in UT!.mncbig then
      l := InducedFromElementary(UT, a[1], a[2], 1000);
      if IsInt(l) then
        Info(InfoUTable, 1, "Skipping elementary ",a,
             " with ",l," conjugacy classes");
        Add(UT!.mncbig, a);
        Add(UT!.mncbigncl, l);
      else
        Info(InfoUTable, 1, "Induce from elementary ", a,
              " |C|=",ords[a[1]]," |P|=",op(a[1], a[2]));
        ImportToUTable(UT, l);
        AddSet(UT!.mncdone, a);
        ExtendLLLUTable(UT);
        ReduceUTable(UT);
        if Length(UT!.ichars) = ncl then
          Sort(UT!.ichars);
          return UT!.ichars;
        fi;
      fi;
    fi;
  od;
  # remaining elementary subgroups, first those with fewer classes
  SortParallel(UT!.mncbigncl, UT!.mncbig);
  for i in [1..Length(UT!.mncbig)] do
    a := UT!.mncbig[i];
    Info(InfoUTable, 1, "Induce from elementary ", a,
          " |C|=",ords[a[1]]," |P|=",op(a[1], a[2]), 
          " (", UT!.mncbigncl[i], " classes)");
    l := InducedFromElementary(UT, a[1], a[2]);
    ImportToUTable(UT, l);
    AddSet(UT!.mncdone, a);
    ExtendLLLUTable(UT);
    ReduceUTable(UT);
    if Length(UT!.ichars) = ncl then
      Sort(UT!.ichars);
      return UT!.ichars;
    fi;
  od;

  # we should be done by now, but maybe we need a stronger LLL
  ExtendLLLUTable(UT);
  ReduceUTable(UT, 99999/100000);
  if Length(UT!.ichars) = ncl then
    Sort(UT!.ichars);
    return UT!.ichars;
  fi;
  
  # we give up, print a warning and return fail
  Info(InfoWarning, 1, "Irr for UTable: not all irreducibles found.\n",
       "Maybe try LLL with delta=1, or add some characters...");
  return fail;
end);





