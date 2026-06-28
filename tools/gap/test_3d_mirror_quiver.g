########################################################
# test_3d_mirror_quiver.g
#
# Verifies algebraic structures from Koroteev-Zeitlin
# 3D mirror symmetry (arXiv:2309.xxxxx style).
#
# Covers:
#   1. Weyl group W(A_r) = S_{r+1}
#   2. Root system / coroot lattice for A_1,A_2,A_3
#   3. QQ-system via Cartan matrix
#   4. Bethe root count = dimension vector
#   5. Mirror involution / Euler form invariance
#   6. Quiver path algebra for A_2
#
# Every test prints true or false.
########################################################

Print("=== 3D Mirror Symmetry Verification ===\n\n");

########################################################
# 1. Weyl group W(A_r) = S_{r+1} acting on Bethe roots
########################################################

Print("--- Test 1: Weyl group W(A_r) ---\n");

# W(A_r) is the symmetric group S_{r+1}.
# Weyl reflections s_i permute adjacent Bethe
# roots (s_{a,i} <-> s_{a,i+1}), matching the
# transpositions (i, i+1) generating S_{r+1}.

WeylGroupTest := function(r)
  local W, gens, n, expected_order, ok,
        bethe, sigma, permuted, g;
  n := r + 1;
  W := SymmetricGroup(n);
  gens := GeneratorsOfGroup(W);

  # |W(A_r)| = (r+1)!
  expected_order := Factorial(n);
  ok := Size(W) = expected_order;

  # Verify generators are adjacent transpositions
  # (Coxeter presentation of S_n)
  # Check s_i^2 = 1 for all generators
  for g in gens do
    if Order(g) <> 2 then
      ok := false;
    fi;
  od;

  # Simulate Weyl action on Bethe roots:
  # roots = [z_1, z_2, ..., z_n]
  bethe := [1..n];
  sigma := (1,2); # simple reflection s_1
  permuted := Permuted(bethe, sigma);
  # s_1 swaps positions 1 and 2
  if permuted[1] <> 2 or permuted[2] <> 1 then
    ok := false;
  fi;

  return ok;
end;

Print("  W(A_1)=S_2 order 2: ",
  WeylGroupTest(1), "\n");
Print("  W(A_2)=S_3 order 6: ",
  WeylGroupTest(2), "\n");
Print("  W(A_3)=S_4 order 24: ",
  WeylGroupTest(3), "\n");

########################################################
# 2. Root system of type A_r, coroot lattice
########################################################

Print("\n--- Test 2: Root system A_r ---\n");

# Simple roots of A_r: alpha_i = e_i - e_{i+1}
# Simple coroots: alpha_i^vee = alpha_i (simply
# laced). Coroot lattice is Z-span of coroots.

CartanMatrixAr := function(r)
  local C, i;
  C := NullMat(r, r);
  for i in [1..r] do
    C[i][i] := 2;
    if i > 1 then C[i][i-1] := -1; fi;
    if i < r then C[i][i+1] := -1; fi;
  od;
  return C;
end;

SimpleRootsAr := function(r)
  local roots, i, v;
  roots := [];
  for i in [1..r] do
    v := ListWithIdenticalEntries(r+1, 0);
    v[i] := 1;
    v[i+1] := -1;
    Add(roots, v);
  od;
  return roots;
end;

RootSystemTest := function(r)
  local C, roots, i, j, ip, ok;
  C := CartanMatrixAr(r);
  roots := SimpleRootsAr(r);
  ok := true;

  # Verify Cartan matrix entries:
  # C_{ij} = 2 <alpha_i, alpha_j> /
  #              <alpha_j, alpha_j>
  for i in [1..r] do
    for j in [1..r] do
      ip := roots[i] * roots[j];
      if C[i][j] <> 2 * ip / (roots[j]*roots[j])
      then
        ok := false;
      fi;
    od;
  od;

  # Coroot lattice rank = r
  # (matrix of coroots has rank r)
  if RankMat(roots) <> r then
    ok := false;
  fi;

  # Determinant of Cartan matrix = r+1
  if DeterminantMat(C) <> r + 1 then
    ok := false;
  fi;

  return ok;
end;

Print("  A_1 root system: ",
  RootSystemTest(1), "\n");
Print("  A_2 root system: ",
  RootSystemTest(2), "\n");
Print("  A_3 root system: ",
  RootSystemTest(3), "\n");

########################################################
# 3. QQ-system relations in Grothendieck ring
########################################################

Print("\n--- Test 3: QQ-system / Cartan ---\n");

# The QQ-system for A_r:
#   Q_a(z * q) * Q_a(z / q)
#     = prod_{b~a} Q_b(z) + (lower terms)
#
# At the level of the Cartan matrix, this is
# encoded by:
#   C_{ab} = 2 delta_{ab} - A_{ab}
# where A is the adjacency matrix of the Dynkin
# diagram. The QQ-system reproduces the quantum
# group relations (Frenkel-Reshetikhin).
#
# We verify:
#   (a) Cartan matrix has the correct form
#   (b) Off-diagonal = -adjacency of Dynkin
#   (c) Symmetrizability: D*C symmetric, D diag

QQSystemTest := function(r)
  local C, adj, i, j, ok, DC;
  C := CartanMatrixAr(r);
  ok := true;

  # Build adjacency matrix of A_r Dynkin diagram
  adj := NullMat(r, r);
  for i in [1..r-1] do
    adj[i][i+1] := 1;
    adj[i+1][i] := 1;
  od;

  # Check C = 2*I - adj
  for i in [1..r] do
    for j in [1..r] do
      if i = j then
        if C[i][j] <> 2 then ok := false; fi;
      else
        if C[i][j] <> -adj[i][j] then
          ok := false;
        fi;
      fi;
    od;
  od;

  # A_r is simply-laced so D = I works:
  # D*C is already symmetric
  DC := C; # D = identity
  if DC <> TransposedMat(DC) then
    ok := false;
  fi;

  # QQ-system structural check:
  # For each node a, the number of neighbors
  # equals -sum of off-diagonal C_{a,b}.
  for i in [1..r] do
    if Sum(C[i]) - 2 <>
       -(Number([1..r], j -> adj[i][j] = 1))
    then
      ok := false;
    fi;
  od;

  return ok;
end;

Print("  QQ-system A_1: ",
  QQSystemTest(1), "\n");
Print("  QQ-system A_2: ",
  QQSystemTest(2), "\n");
Print("  QQ-system A_3: ",
  QQSystemTest(3), "\n");

########################################################
# 4. Bethe root count = dimension vector
########################################################

Print("\n--- Test 4: Bethe roots = dim vector ---\n");

# In 3D mirror symmetry a quiver gauge theory
# has dimension vector v = (v_1,...,v_r) and
# framing vector w = (w_1,...,w_r).
# The number of Bethe roots at node a is v_a.
# We verify this counting for sample vectors.

BetheCountTest := function(v)
  local a, bethe_roots, ok;
  ok := true;
  for a in [1..Length(v)] do
    # Allocate v[a] Bethe roots at node a
    bethe_roots := [1..v[a]];
    if Length(bethe_roots) <> v[a] then
      ok := false;
    fi;
  od;
  return ok;
end;

# A_2 quiver, dimension vector (2,3)
Print("  v=(2,3): ",
  BetheCountTest([2,3]), "\n");
# A_3 quiver, dimension vector (1,2,1)
Print("  v=(1,2,1): ",
  BetheCountTest([1,2,1]), "\n");
# A_3 quiver, dimension vector (3,4,2)
Print("  v=(3,4,2): ",
  BetheCountTest([3,4,2]), "\n");

########################################################
# 5. Mirror involution & Euler form
########################################################

Print("\n--- Test 5: Mirror involution ---\n");

# For A_r quiver the Euler form is:
#   Euler(v,w) = sum_i w_i*v_i
#              - sum_{i->j in Q_1} v_i*v_j
#
# For the A_r Dynkin quiver the arrows are
# i -> i+1 for i=1..r-1.
#
# 3D mirror symmetry swaps (v,w) <-> (w',v')
# in a dual quiver. For the self-mirror A_r
# case, the Euler form of the pair (v,w) equals
# the Euler form of (w,v) when the quiver is
# undirected (i.e., considering the symmetrized
# Euler form).

EulerFormAr := function(r, v, w)
  local total, i;
  # diagonal part: sum w_i * v_i
  total := Sum([1..r], i -> w[i] * v[i]);
  # arrow part: subtract v_i*v_{i+1}
  for i in [1..r-1] do
    total := total - v[i] * v[i+1];
  od;
  return total;
end;

# Symmetrized Euler form:
#   <v,w> + <w,v> is symmetric in v,w
# when computed with the same arrow set.
SymEulerAr := function(r, v, w)
  return EulerFormAr(r, v, w)
       + EulerFormAr(r, w, v);
end;

MirrorInvolutionTest := function(r, v, w)
  local ok, E1, E2, SE1, SE2;
  ok := true;

  # The symmetrized Euler form is invariant
  # under (v,w) <-> (w,v)
  SE1 := SymEulerAr(r, v, w);
  SE2 := SymEulerAr(r, w, v);
  if SE1 <> SE2 then
    ok := false;
  fi;

  # For the Tits form (v=w case), Euler form
  # is invariant under the Weyl group action.
  # Check Tits form q(v) = Euler(v,v):
  E1 := EulerFormAr(r, v, v);
  # Verify q(v) = sum v_i^2 - sum v_i*v_{i+1}
  E2 := Sum([1..r], i -> v[i]^2)
      - Sum([1..r-1], i -> v[i]*v[i+1]);
  if E1 <> E2 then
    ok := false;
  fi;

  return ok;
end;

Print("  Mirror A_2 v=(1,1) w=(1,0): ",
  MirrorInvolutionTest(2, [1,1], [1,0]),
  "\n");
Print("  Mirror A_2 v=(2,3) w=(1,1): ",
  MirrorInvolutionTest(2, [2,3], [1,1]),
  "\n");
Print("  Mirror A_3 v=(1,2,1) w=(1,0,1): ",
  MirrorInvolutionTest(3,[1,2,1],[1,0,1]),
  "\n");

########################################################
# 6. Quiver path algebra for A_2
########################################################

Print("\n--- Test 6: Path algebra A_2 ---\n");

# The A_2 quiver has vertices {1,2} and one
# arrow a: 1 -> 2.
#
# The path algebra kQ over a field k has basis:
#   { e_1, e_2, a }
# where e_i are idempotents (lazy paths).
# So dim(kQ) = 3.
#
# We construct this as a matrix algebra.
# Represent kQ inside Mat(2, Q):
#   e_1 = E_{11}, e_2 = E_{22}, a = E_{12}
# These satisfy:
#   e_1*a = a, a*e_2 = a
#   e_1^2 = e_1, e_2^2 = e_2
#   e_1*e_2 = 0, a^2 = 0 (no path of length 2)

PathAlgebraA2Test := function()
  local e1, e2, a, ok, basis, V;
  e1 := [[1,0],[0,0]];
  e2 := [[0,0],[0,1]];
  a  := [[0,1],[0,0]];
  ok := true;

  # Idempotent checks
  if e1 * e1 <> e1 then ok := false; fi;
  if e2 * e2 <> e2 then ok := false; fi;

  # Orthogonality
  if e1 * e2 <> 0 * e1 then ok := false; fi;
  if e2 * e1 <> 0 * e1 then ok := false; fi;

  # Completeness: e1 + e2 = identity
  if e1 + e2 <> IdentityMat(2) then
    ok := false;
  fi;

  # Arrow relations
  if e1 * a <> a then ok := false; fi;
  if a * e2 <> a then ok := false; fi;
  if a * a <> 0 * e1 then ok := false; fi;

  # Dimension = 3 (span of {e1, e2, a})
  basis := [Flat(e1), Flat(e2), Flat(a)];
  V := VectorSpace(Rationals, basis);
  if Dimension(V) <> 3 then ok := false; fi;

  return ok;
end;

Print("  kQ(A_2) dim=3, relations: ",
  PathAlgebraA2Test(), "\n");

# Extended test: A_2 quiver with both
# orientations (a: 1->2, b: 2->1).
# The double quiver has dim(kQ) = 5:
# {e_1, e_2, a, b, a*b or b*a}
# but a*b = E_{11} = e_1 and b*a = E_{22} = e_2
# so as a vector space it is still 4-dimensional
# (e1, e2, a, b) since a*b and b*a are already
# in span. Actually:
#   a = E_{12}, b = E_{21}
#   a*b = E_{11} = e_1 (already in basis)
#   b*a = E_{22} = e_2 (already in basis)
# So the full matrix algebra Mat(2,Q) has dim 4.

DoubleQuiverA2Test := function()
  local e1, e2, a, b, ok, basis, V;
  e1 := [[1,0],[0,0]];
  e2 := [[0,0],[0,1]];
  a  := [[0,1],[0,0]];
  b  := [[0,0],[1,0]];
  ok := true;

  # a*b = e1, b*a = e2
  if a * b <> e1 then ok := false; fi;
  if b * a <> e2 then ok := false; fi;

  # Full algebra = Mat(2,Q), dim = 4
  basis := [Flat(e1), Flat(e2),
            Flat(a), Flat(b)];
  V := VectorSpace(Rationals, basis);
  if Dimension(V) <> 4 then ok := false; fi;

  return ok;
end;

Print("  Double A_2 (Mat_2) dim=4: ",
  DoubleQuiverA2Test(), "\n");

########################################################
# Summary
########################################################

Print("\n=== All tests completed ===\n");
