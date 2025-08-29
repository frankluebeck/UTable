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
  # we have lists for characters: i irreducible,
  # o: others for which gram is computed,
  # n: newly imported or computed characters
  # gram: Gram matrix of chars in ochar
  return ObjectifyWithAttributes(rec(ichars := [], ochars := [], 
                                     nchars := [], gram := []), 
                                 UTableType, UnderlyingGroup, G);
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
##  or from character table of G
##  or values on RationalClassIndices(UT), they are added to
##  the list of new characters UT!.nchars after subtracting the projection
##  on the space of already known irreducibles
##  
##  Note: only rational linear combinations of irreducibles can be handled
##  here, not arbitrary class functions!
BindGlobal("ImportToUTable", function(UT, l)
  local ind, len, t, idc, ch, c, ic;
  if Length(l) = 0 then
    return;
  fi;
  ind := RationalClassIndices(UT);
  len := Length(ind);
  for ch in l do
    if HasUnderlyingCharacterTable(ch) then
      t := UnderlyingCharacterTable(ch);
      idc := IdentificationOfConjugacyClasses(t);
      ch := AsList(ch);
      c := [];
      c{idc} := ch;
      ch := c;
    fi;
    if Length(ch) <> len then
      ch := ch{ind};
    fi;
    # reduce with known irreducibles
    for ic in UT!.ichars do
      c := ScalarProduct(UT, ch, ic);
      if c <> 0 then
        ch := ch - c * ic;
      fi;
    od;

    if not (IsZero(ch) or ch in UT!.ochars or ch in UT!.nchars) then
      Add(UT!.nchars, ch);
    fi;
  od;
end);

# extend Gram matrix for new characters in UT!.nchars
# and move those characters to UT!.ochars
BindGlobal("ExtendGramUTable", function(UT)
  local ng, nc, c, v, i;
  ng := [];
  nc := UT!.nchars;
  for i in [1..Length(nc)] do
    c := nc[i];
    v := List(UT!.ochars, d-> ScalarProduct(UT, c, d));
    Append(v, List([1..i], j-> ScalarProduct(UT, c, nc[j])));
    Add(ng, v);
  od;
  Append(UT!.gram, ng);
  Append(UT!.ochars, nc);
  UT!.nchars := [];
end);

# reduce characters in UT!.ochars using LLL
# move found irreducibles to UT!.ichars
BindGlobal("ReduceUTable", function(UT, delta...)
  local lll, nirr, irr, g, len, m, oc, 
        noc, ch, ng, gg, v, ni, i, j;
  if Length(UT!.gram) = 0 then
    return;
  fi;
  if Length(delta) > 0 then
    delta := delta[1];
  else
    delta := 9/10;
  fi;
  lll := LLLReducedGramMat(UT!.gram, delta);
  UT!.gram := lll.remainder;
  UT!.ochars := lll.transformation * UT!.ochars;
  
  # now check for irreducibles and adjust
  nirr := [];
  irr := [];
  g := UT!.gram;
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
    oc := UT!.ochars;
    # new ochars
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
    # remove zero characters from ochars and gram
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
    UT!.ochars := noc;
    UT!.gram := ng;
    for ch in ni do
      if ch[1] < 0 then
        Add(UT!.ichars, -ch);
      else
        Add(UT!.ichars, ch);
      fi;
    od;
  fi;
  Info(InfoUTable, 1, "|irr| = ",Length(UT!.ichars), " |other| = ",
       Length(UT!.ochars), " det(Gram) = ", DeterminantGramUTable(UT));
end);

# Can be useful information
BindGlobal("DeterminantGramUTable", function(UT)
  local g, n, i, j;
  g := UT!.gram;
  if Length(g) = 0 then
    return 1;
  fi;
  g := List(g, ShallowCopy);
  n := Length(g);
  for i in [1..n-1] do
    for j in [i+1..n] do
      g[i][j] := g[j][i];
    od;
  od;
  return DeterminantIntMat(g);
end);

# The main automatic function.
# Can be called from the start or after adding characters by hand.
InstallOtherMethod(Irr, ["IsUTable"], 
function(UT)
  local G, len, scen, ncl, ords, op, v, l, mc, mnc, g, i, a, j;
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

  # Add trivial and natural characters
  if not IsBound(UT!.naturaldone) then
    Info(InfoUTable, 1, "Trivial and natural characters");
    v := 1+0*[1..len];
    if not v in UT!.ichars then
      Add(UT!.ichars, v);
    fi;

    l := NaturalCharacters(G);
    ImportToUTable(UT, l);
    UT!.naturaldone := true;
  fi;

  # And some cheap characters from power maps
  if not IsBound(UT!.pmchars) then
    Info(InfoUTable, 1, "Cheap characters from power maps");
    l := SmallPowerMapCharacters(G);
    ImportToUTable(UT, l);
  fi;

  # Reduce these
##    ExtendGramUTable(UT);
##    ReduceUTable(UT);

  # induce from all (maximal) cyclic subgroups
  mc := MaximalCyclics(G);
  if not IsBound(UT!.mcdone) then
    UT!.mcdone := [];
  fi;
  for i in mc do
    if not i in UT!.mcdone then
      Info(InfoUTable, 1, "Induce from maximal cyclic ", i, " (|g|=", ords[i],")");
      l := InduceAllFromCyclicSubgroup(UT, i);
      ImportToUTable(UT, l);
      AddSet(UT!.mcdone, i);
    fi;
  od;
  ExtendGramUTable(UT);
  ReduceUTable(UT);

  # now induce from (maximal) non-cyclic elementary subgroups
  mnc := MaximalNonCyclicElementarySubgroups(G);
  if not IsBound(UT!.mncdone) then
    UT!.mncdone := [];
  fi;
  # first only cases where p is still in determinant of Gram matrix
  # (this is in the index of the lattice found so far)
  for a in mnc do
    if not a in UT!.mncdone then
      g := List(UT!.gram, ShallowCopy);
      for i in [1..Length(g)] do
        for j in [i+1..Length(g)] do
          g[i][j] := g[j][i];
        od;
      od;
      if Length(g) = 0 or RankMat(Z(a[2])^0 * g) < Length(g) then
        Info(InfoUTable, 1, "Induce from elementary ", a,
                " |C|=",ords[a[1]]," |P|=",op(a[1], a[2]));
        l := InducedFromElementary(UT, a[1], a[2]);
        ImportToUTable(UT, l);
        AddSet(UT!.mncdone, a);
        ExtendGramUTable(UT);
        ReduceUTable(UT);
        if Length(UT!.ichars) = ncl then
          Sort(UT!.ichars);
          return UT!.ichars;
        fi;
      fi;
    fi;
  od;
  # if not done the remaining cases
  for a in mnc do
    if not a in UT!.mncdone then
      Info(InfoUTable, 1, "Induce from elementary ", a,
              " |C|=",ords[a[1]]," |P|=",op(a[1], a[2]));
      l := InducedFromElementary(UT, a[1], a[2]);
      ImportToUTable(UT, l);
      AddSet(UT!.mncdone, a);
      ExtendGramUTable(UT);
      ReduceUTable(UT);
      if Length(UT!.ichars) = ncl then
        Sort(UT!.ichars);
        return UT!.ichars;
      fi;
    fi;
  od;
  # we should be done by now, but maybe we need a stronger LLL
  ExtendGramUTable(UT);
  ReduceUTable(UT, 99999/100000);
  if Length(UT!.ichars) = ncl then
    Sort(UT!.ichars);
    return UT!.ichars;
  fi;

  Error("Irr for UTable: not all irreducibles found.");
end);





