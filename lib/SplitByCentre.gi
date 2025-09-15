

# do nothing if splitting centre is already installed
InstallMethod(SplitByCentre, ["IsUTable and HasSplittingCentre"],
function(UT) end);
# find classes in centre and call method below
InstallMethod(SplitByCentre, ["IsUTable"], function(UT)
  local scls;
  scls := SizesConjugacyClasses(UT);
  SplitByCentre(UT, Positions(scls, 1));
end);
# now the real function
InstallMethod(SplitByCentre, ["IsUTable and HasUnderlyingGroup", "IsList"], 
function(UT, zind)
  local G, cls, ncl, z, zmaps, done, x, a, sz, zg, tz, zchars, det, inv, e, 
        pr, found, reps, zgalois, k, jj, zchmults, ichars, lll, nchars, 
        lllsplit, lr, i, j;
  # refuse to do anything for trivial case
  if Length(zind) = 1 then
    return;
  fi;

  # to compute splitting we need the map on classes by multiplication with
  # centre elements
  G := UnderlyingGroup(UT);
  cls := ConjugacyClasses(UT);
  ncl := NrConjugacyClasses(UT);
  z := List(zind, i-> Representative(cls[i]));
  zmaps := [zind];
  done := BlistList([1..ncl], zind);
  for i in [1..ncl] do
    if not done[i] then
      x := Representative(cls[i]);
      a := [i];
      for j in [2..Length(z)] do
        Add(a, PositionConjugacyClass(G, x*z[j]));
      od;
      for k in a do
        done[k] := true;
      od;
      Add(zmaps, a);
    fi;
  od;
  UT!.zmaps := zmaps;

  # the character table of the splitting group which parameterizes the
  # splitting
  sz := Length(z);
  zg := Group(z);
  SetConjugacyClasses(zg, List(z, x-> ConjugacyClass(zg, x)));
  tz :=CharacterTable(zg);
  zchars := List(Irr(tz), AsList);
  UT!.zchars := zchars;
  det := DeterminantMat(zchars);
  inv := det*zchars^-1;
  UT!.invzchars := [det, inv];

  # during computations we only need one character of z per Galois orbit
  e := Exponent(zg);
  pr := PrimeResidues(e);
  found := BlistList([1..sz], []);
  reps := [];
  zgalois := [];
  for i in [1..sz] do
    if not found[i] then
      found[i] := true;
      Add(reps, i);
      for j in pr do
        k := Position(zchars, GaloisCyc(zchars[i], j));
        if not found[k] then
          found[k] := true;
          # want exponent prime to |G|
          jj := j;
          while Gcd(Size(G), jj) <> 1 do
            jj := jj + e;
          od;
          zgalois[k] := [i,jj];
        fi;
      od;
    fi;
  od;
  UT!.zchreps := reps;
  UT!.zgalois := zgalois;
  # for counting purposes
  zchmults := [];
  for i in reps do
    zchmults[i] := 1 + Number(Set(zgalois), a-> a[1]=i);
  od;
  UT!.zchmults := zchmults;

  SetSplittingCentre(UT, zind);

  # now we split the existing characters into lists of sz lists
  # (only the entries in reps above will be used)
  ichars := UT!.ichars;
  lll := UT!.lll;
  nchars := UT!.nchars;
  UT!.ichars := SplitCharactersByCentre(UT, ichars);
  UT!.nchars := SplitCharactersByCentre(UT, nchars);
  UT!.lll := [];
  CleanLLLRecord(lll);
  lllsplit := SplitCharactersByCentre(UT, lll.vectors);
  for i in reps do
    lr := LLLRecord(lll.y, lll.scalar);
    AddVectorsLLLRecord(lr, lllsplit[i]);
    CleanLLLRecord(lr);
    UT!.lll[i] := lr;
  od;
end);

# in general characters of centre involve cyclotomics
# we do the splitting with the expanded character
# 
# ch is a character encoded in UT format
SplitCharacterByCentre := function(UT, ch)
  local zchars, inv, zmaps, zind, reps, res, ech, pos, coeffs, i, a;

  zchars := UT!.zchars;
  inv := UT!.invzchars;
  zmaps := UT!.zmaps;
  zind := zmaps[1];
  reps := UT!.zchreps;

  res := [];
  ech := ExpandFromUTable(UT, [ch])[1];
  pos := Position(zchars, ech{zind}/ech[1]);
  if pos <> fail then
    # nothing to do
    if pos in reps then
      res[pos] := ch;
    fi;
    return res;
  fi;

  for i in reps do
    res[i] := [];
  od;
  for a in zmaps do
    coeffs := (ech{a} * inv[2]) / inv[1];
    for i in reps do
      res[i]{a} := coeffs[i]*zchars[i];
    od;
  od;
  res{reps} := EncodeForUTable(UT, res{reps});
  return res;
end;

InstallMethod(SplitCharactersByCentre, 
              ["IsUTable and HasSplittingCentre", "IsList"], 
function(UT, chs)
  local zchars, inv, zmaps, zind, reps, res, 
        echs, ech, pos, r, coeffs, i, j, a;

  zchars := UT!.zchars;
  inv := UT!.invzchars;
  zmaps := UT!.zmaps;
  zind := zmaps[1];
  reps := UT!.zchreps;

  res := [];
  for i in reps do
    res[i] := [];
  od;
  echs := ExpandFromUTable(UT, chs);
  for j in [1..Length(chs)] do
    ech := echs[j];
    if ech[1] <> 0 then
      pos := Position(zchars, ech{zind}/ech[1]);
    else
      pos := fail;
    fi;
    if pos <> fail then
      # nothing to do
      if pos in reps then
        Add(res[pos], chs[j]);
      fi;
    else
      r := [];
      for i in reps do
        r[i] := [];
      od;
      for a in zmaps do
        coeffs := (ech{a} * inv[2]) / inv[1];
        for i in reps do
          r[i]{a} := coeffs[i]*zchars[i];
        od;
      od;
      r{reps} := EncodeForUTable(UT, r{reps});
      for i in reps do
        Add(res[i], r[i]);
      od;
    fi;
  od;
  return res;
end);

