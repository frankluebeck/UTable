

# arguments: [delta,][scalarfun]
BindGlobal("LLLRecord", function(args...)
  local res, f;
  res := rec();
  # the constant for Lovasz condition, default 3/4
  f := First([1..Length(args)], i-> IsRat(args[i]));
  if f <> fail then
    res.y := args[f];
    if res.y <= 1/4 or res.y > 1 then
      res.y := 3/4;
    fi;
  else
    res.y := 3/4;
  fi;
  # the function function(v1, v2) for computing the scalar product
  # of vectors v1 and v2, default is standard scalar product
  f := First([1..Length(args)], i-> IsFunction(args[i]));
  if f <> fail then
    res.scalar := args[f];
  else
    res.scalar := function(v1, v2) return v1*v2; end;
  fi;

  # setting up the (empty) data structures
  # input vectors (will be set to "false" when the record
  # is extended by new rows of the Gram matrix instead of vectors)
  res.vectors := [];
  # number of input vectors
  res.n := 0;
  # lower triangular part of Gram matrix
  res.gram := [];
  # mue coefficients, entries below diagonal
  res.mue := [];
  # number of vectors reduced to zero
  res.r := 0;
  # number of vectors processed so far
  res.kmax := 0;
  # the transition matrix to LLL-reduced basis
  # (first r rows yield zero vectors)
  res.H := [];
  # norms of Gram-Schmidt basis
  res.B := [];

  return res;
end);

# adding non-zero vectors and extending the Gram matrix
# (zero vectors are ignored, no reduction is done)
BindGlobal("AddVectorsLLLRecord", function(LR, vs)
  local vecs, gram, sc, kmax, ng, v;
  vecs := LR.vectors;
  gram := LR.gram;
  sc := LR.scalar;
  kmax := LR.kmax;
  for v in vs do
    if not IsZero(v) then
      if kmax > 0 then
        ng := LR.H * List([1..kmax], i-> sc(v, vecs[i]));
      else
        ng := [];
      fi;
      Append(ng, List([kmax+1..LR.n], i-> sc(v,vecs[i])));
      Add(ng, sc(v,v));
      Add(vecs, v);
      Add(gram, ng);
      LR.n := LR.n+1;
    fi;
  od;
end);

# adding rows of Gram matrix, in that case set LR.vectors to false
# (no reduction is done)
BindGlobal("AddGramLLLRecord", function(LR, gramrows)
  LR.vectors := false;
  Append(LR.gram, gramrows);
  LR.n := LR.n + Length(gramrows);
end);

# the main function implementing the LLL algorithm, essentially
# LLLReducedGramMat from GAP library which follows 
#    Cohen, A course in algebraic number theory
# 
# optional argument delta overwrites the default in LR
# 
# in this function we do not change input vectors, such that repeated
# calls to AddVectorsLLLRecord and ReduceLLLRecord are equivalent to
# adding all vectors in the beginning and reducing once
BindGlobal("ReduceLLLRecord", function(LR, delta...)
  local y, gram, mue, B, H, r, n, kmax, k, null, ak, a, b,
        RED, q, mmue, BB, row, i, j, l;
  if Length(delta) > 0 then
    y := delta[1];
  else
    y := LR.y;
  fi;
  gram := LR.gram;
  mue := LR.mue;
  B := LR.B;
  H := LR.H;
  r := LR.r;
  n := LR.n;
  kmax := LR.kmax;
  # we start here since first kmax vectors are already reduced
  k := kmax+1; 
  # extend the H matrix
  null := 0*[k..n];
  for row in H do
    Append(row, null);
  od;
  null := 0*[1..n];
  for i in [k..n] do
    H[i] := ShallowCopy(null);
    H[i][i] := 1;
  od;

  # helper that is needed in several places below
  RED := function( gram, mue, H, n, k, l )
    local rat, a, b, q, i;
    if l = 0 then
      return;
    fi;

    # Terminate for $\|\mue_{k,l}\| \leq \frac{1}{2}$.
    if 1 < mue[k][l] * 2 or mue[k][l] * 2 < -1 then

      # Let $q = `Round( mue[k][l] )'$ (is never zero), \ldots
      #q:= Int( mue[k][l] );
      #if AbsoluteValue( mue[k][l] - q ) * 2 > 1 then
      #  q:= q + SignInt( mue[k][l] );
      #fi;
      rat := mue[k][l];
      a := NumeratorRat(rat);
      b := DenominatorRat(rat);
      if a >= 0 then
        q := QuoInt(2*a+b, 2*b);
      else
        q := QuoInt(2*a-b, 2*b);
      fi;
      # rat = rat-q
      rat := (a - b*q)/b;

      # \ldots adjust the Gram matrix (rows and columns, but only
      # in the lower triangular half), \ldots
      #gram[k][k]:= gram[k][k] - q * gram[k][l];
      #for i in [ r+1 .. l ] do
      #  gram[k][i]:= gram[k][i] - q * gram[l][i];
      #od;
      #for i in [ l+1 .. k ] do
      #  gram[k][i]:= gram[k][i] - q * gram[i][l];
      #od;
      #for i in [ k+1 .. n ] do
      #  gram[i][k]:= gram[i][k] - q * gram[i][l];
      #od;
      a := gram[k];
      if a[l] <> 0 then
        a[k] := a[k] - q*a[l];
      fi;
      b := gram[l];
      for i in [ r+1 .. l ] do
        if b[i] <> 0 then
          a[i] := a[i] - q*b[i];
        fi;
      od;
      for i in [ l+1 .. k ] do
        b := gram[i][l];
        if b <> 0 then
          a[i] := a[i] - q*b;
        fi;
      od;
      for i in [ k+1 .. n ] do
        a := gram[i];
        if a[l] <> 0 then
          a[k] := a[k] - q*a[l];
        fi;
      od;

      # \ldots adjust `mue', \ldots
      #mue[k][l]:= mue[k][l] - q;
      mue[k][l]:= rat;
      for i in [ r+1 .. l-1 ] do
        if mue[l][i] <> 0 then
          mue[k][i]:= mue[k][i] - q * mue[l][i];
        fi;
      od;

      # \ldots and the basechange.
      #H[k]:= H[k] - q * H[l];
      a := H[k];
      b := H[l];
      for i in [1..n] do
        if b[i] <> 0 then
          a[i] := a[i] - q*b[i];
        fi;
      od;
    fi;
  end;

  # buffer
  ak := [];

  # now the actual work
  while k <= n do

    # step 2 (Incremental Gram-Schmidt)

    # If $k \leq k_{max}$ go to step 3.
    if k > kmax then

      Info( InfoUTable, 5,
            "ReducedLLLRecord: Take ", Ordinal( k ), " vector" );

      # Otherwise \ldots
      kmax:= k;
      B[k]:= gram[k][k];
      mue[k]:= [];
      for j in [ r+1 .. k-1 ] do
        ak[j]:= gram[k][j];
        for i in [ r+1 .. j-1 ] do
          ak[j]:= ak[j] - mue[j][i] * ak[i];
        od;
        mue[k][j]:= ak[j] / B[j];
        B[k]:= B[k] - mue[k][j] * ak[j];
      od;

    fi;

    # step 3 (Test LLL condition)
    if k > 1 then
      RED( gram, mue, H, n, k, k-1 );
      while B[k] < ( y - mue[k][k-1]^2 ) * B[k-1] do

        # Execute Sub-algorithm SWAPG$( k )$\:
        # Exchange $H_k$ and $H_{k-1}$,
        q      := H[k];
        H[k]   := H[k-1];
        H[k-1] := q;

        # adjust the Gram matrix (rows and columns,
        # but only in the lower triangular half),
        a := gram[k];
        b := gram[k-1];
        for j in [ r+1 .. k-2 ] do
          #q            := gram[k][j];
          #gram[k][j]   := gram[k-1][j];
          #gram[k-1][j] := q;
          q    := a[j];
          a[j] := b[j];
          b[j] := q;
        od;
        for j in [ k+1 .. n ] do
          #q            := gram[j][k];
          #gram[j][k]   := gram[j][k-1];
          #gram[j][k-1] := q;
          a := gram[j];
          q      := a[k];
          a[k]   := a[k-1];
          a[k-1] := q;
        od;
        a := gram[k];
        b := gram[k-1];
        #q              := gram[k-1][k-1];
        #gram[k-1][k-1] := gram[k][k];
        #gram[k][k]     := q;
        q      := b[k-1];
        b[k-1] := a[k];
        a[k]   := q;

        # and if $k > 2$, for all $j$ such that $1 \leq j \leq k-2$
        # exchange $\mue_{k,j}$ with $\mue_{k-1,j}$.
        a := mue[k];
        b := mue[k-1];
        for j in [ r+1 .. k-2 ] do
          #q           := mue[k][j];
          #mue[k][j]   := mue[k-1][j];
          #mue[k-1][j] := q;
          q    := a[j];
          a[j] := b[j];
          b[j] := q;
        od;

        # Then set $\mue \leftarrow \mue_{k,k-1}$
        mmue:= mue[k][k-1];

        # and $B \leftarrow B_k + \mue^2 B_{k-1}$.
        BB:= B[k] + mmue^2 * B[k-1];

        # Now, in the case $B = 0$ (i.e. $B_k = \mue = 0$),
        if BB = 0 then

          # exchange $B_k$ and $B_{k-1}$
          B[k]   := B[k-1];
          B[k-1] := 0;

          # and for $i = k+1, k+2, \ldots, k_{max}$
          # exchange $\mue_{i,k}$ and $\mue_{i,k-1}$.
          for i in [ k+1 .. kmax ] do
            a := mue[i];
            #q           := mue[i][k];
            #mue[i][k]   := mue[i][k-1];
            #mue[i][k-1] := q;
            q      := a[k];
            a[k]   := a[k-1];
            a[k-1] := q;
          od;

        # In the case $B_k = 0$ and $\mue \not= 0$,
        elif B[k] = 0 and mmue <> 0 then

          # set $B_{k-1} \leftarrow B$,
          B[k-1]:= BB;

          # $\mue_{k,k-1} \leftarrow \frac{1}{\mue}
          b := 1 / mmue;
          #mue[k][k-1]:= 1 / mmue;
          mue[k][k-1] := b;

          # and for $i = k+1, k+2, \ldots, k_{max}$
          # set $\mue_{i,k-1} \leftarrow \mue_{i,k-1} / \mue$.
          for i in [ k+1 .. kmax ] do
            a := mue[i];
            #mue[i][k-1]:= mue[i][k-1] / mmue;
            a[k-1] := a[k-1] * b;
          od;

        else

          # Finally, in the case $B_k \not= 0$,
          # set (in this order) $t \leftarrow B_{k-1} / B$,
          q:= B[k-1] / BB;

          # $\mue_{k,k-1} \leftarrow \mue t$,
          b := mmue * q;
          #mue[k][k-1]:= mmue * q;
          mue[k][k-1] := b;

          # $B_k \leftarrow B_k t$,
          B[k]:= B[k] * q;

          # $B_{k-1} \leftarrow B$,
          B[k-1]:= BB;

          # then for $i = k+1, k+2, \ldots, k_{max}$ set
          # (in this order) $t \leftarrow \mue_{i,k}$,
          # $\mue_{i,k} \leftarrow \mue_{i,k-1} - \mue t$,
          # $\mue_{i,k-1} \leftarrow t + \mue_{k,k-1} \mue_{i,k}$.
          for i in [ k+1 .. kmax ] do
            a := mue[i];
            #q:= mue[i][k];
            #mue[i][k]:= mue[i][k-1] - mmue * q;
            #mue[i][k-1]:= q + mue[k][k-1] * mue[i][k];
            q      := a[k];
            a[k]   := a[k-1] - mmue * q;
            a[k-1] := q + b * a[k];
          od;

        fi;

        # Terminate the subalgorithm.

        if k > 2 then k:= k-1; fi;

        # Here we have always `k > r' since the loop is entered
        # for `k > r+1' only (because of `B[k-1] <> 0'),
        # so the only problem might be the case `k = r+1',
        # namely `mue[ r+1 ][r]' is used then; but this is bound
        # provided that the initial Gram matrix did not start
        # with zero columns, and its (perhaps not updated) value
        # does not matter because this would mean just to subtract
        # a multiple of a zero vector.

        RED(  gram, mue, H, n, k, k-1 );

      od;
    fi;

    if B[ r+1 ] = 0 then
      r:= r+1;
    fi;

    for l in [ k-2, k-3 .. r+1 ] do
      RED(  gram, mue, H, n, k, l );
    od;
    k:= k+1;

    # step 4 (Finished?)
    # If $k \leq n$ go to step 2 (beginning of this loop)

  od;
  # copy kmax and r into record
  LR.kmax := kmax;
  LR.r := r;
end);
  

# this function first calls ReduceLLLRecord (which does nothing if kmax is
# already n) and then changes the input vectors to the reduced basis and
# adjusts the other data accordingly
BindGlobal("CleanLLLRecord", function(LR)
  local n, r, tr, nvec, gram, ngram, mue, nmue, nB, nH;
  n := LR.n;
  if n > LR.kmax then
    ReduceLLLRecord(LR);
  fi;
  r := LR.r;
  tr := LR.H{[r+1..n]};
  if LR.vectors = false then
    nvec := false;
  else
    nvec := tr * LR.vectors;
  fi;
  gram := LR.gram;
  ngram := List([r+1..n], i-> gram[i]{[r+1..i]});
  mue := LR.mue;
  nmue := List([r+1..n], i-> mue[i]{[r+1..i-1]});
  nB := LR.B{[r+1..n]};
  if n > r then
    nH := IdentityMat(n-r);
  else
    nH := [];
  fi;
  LR.vectors := nvec;
  LR.gram := ngram;
  LR.mue := nmue;
  LR.H := nH;
  LR.B := nB;
  LR.r := 0;
  LR.n := n-r;
  LR.kmax := n-r;
end);


   
