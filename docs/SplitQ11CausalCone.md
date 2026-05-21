# SplitQ11 Causal Cone

Lean module:

```lean
InfoGeometry.Clifford.SplitQ11CausalCone
```

## Scope

This module is the theorem-owner surface for the local split-quaternion /
`Cl(1,1)` causal-Krein atom.

It proves finite algebraic identities only.  It does not prove that physical
phenomena are forced by this algebra, and it does not derive Heisenberg,
Kac-Moody, Sugawara, or Virasoro structures.  Those live at higher
mode-indexed theorem-owner surfaces.

The defensible local claim is:

```text
Cl(1,1) ~= H_s ~= M_2(R)
```

is the minimal local model for phase, Krein squeeze, null propagation, and
sector projection.

## Local Dictionary

The prose-facing split-quaternion names are:

```lean
splitQuaternionI  -- square -1 phase axis
splitQuaternionJ  -- square +1 off-diagonal generator
splitQuaternionK  -- square +1 Krein involution
```

The theorem:

```lean
split_quaternion_basis_laws
```

proves:

```text
i^2 = -1
j^2 =  1
k^2 =  1
i*j = k
j*i = -k
```

The matrix-side theorem:

```lean
matrix_split_quaternion_basis_laws
```

records the same law in the real `2 x 2` matrix model.

The matrix-side null-hop theorem:

```lean
matrix_causal_nulls_explicit
```

identifies the null generators with the expected elementary matrices:

```text
u_+ = [[0, 1], [0, 0]]
u_- = [[0, 0], [1, 0]]
```

The theorem:

```lean
matrix_causal_null_closure_laws
```

proves the same nilpotent/projector/commutator closure on the matrix side.

## Krein Projectors

The local Krein projectors are:

```lean
kreinPlusProjector  = (1 / 2) * (1 + splitQuaternionK)
kreinMinusProjector = (1 / 2) * (1 - splitQuaternionK)
```

The theorem:

```lean
krein_projector_laws
```

proves:

```text
P_+^2 = P_+
P_-^2 = P_-
P_+ P_- = 0
P_- P_+ = 0
P_+ + P_- = 1
```

The theorem:

```lean
matrix_krein_projectors_explicit
```

identifies these with the diagonal matrix projectors:

```text
P_+ = [[1, 0], [0, 0]]
P_- = [[0, 0], [0, 1]]
```

These are primitive local sector projectors.  They are not central idempotents
of the full matrix algebra.

The theorem:

```lean
matrix_krein_projectors_noncentral
```

records a concrete noncentrality witness: the matrix Krein projectors do not
commute with the appropriate null-hop matrices.  This formalizes the important
distinction between local primitive sector projectors and central ring
decomposition idempotents.

The theorem:

```lean
matrix_projector_spinor_action
```

records the two-component readout:

```text
P_+ (psi_+, psi_-) = (psi_+, 0)
P_- (psi_+, psi_-) = (0, psi_-)
```

## Null Generators

The null causal hops are:

```lean
causalNullPlus  = (1 / 2) * (splitQuaternionJ + splitQuaternionI)
causalNullMinus = (1 / 2) * (splitQuaternionJ - splitQuaternionI)
```

The theorem:

```lean
causal_null_closure_laws
```

proves:

```text
u_+^2 = 0
u_-^2 = 0
u_+ u_- = P_+
u_- u_+ = P_-
u_+ u_- + u_- u_+ = 1
u_+ u_- - u_- u_+ = K
```

The correct identity is:

```text
1 = u_+ u_- + u_- u_+
```

not any repeated-loop variant.

The theorem:

```lean
matrix_null_spinor_action
```

records the matrix action of the null hops:

```text
u_+ (psi_+, psi_-) = (psi_-, 0)
u_- (psi_+, psi_-) = (0, psi_+)
```

## Sector Hopping

The theorem:

```lean
sector_hopping_laws
```

proves the exact source/target sector rules:

```text
P_+ u_+ = u_+
u_+ P_- = u_+
P_- u_- = u_-
u_- P_+ = u_-

P_- u_+ = 0
u_+ P_+ = 0
P_+ u_- = 0
u_- P_- = 0
```

Thus `u_+` maps the negative Krein sector to the positive sector, while `u_-`
maps the positive Krein sector to the negative sector.

## Dilaton And Squeeze

The finite inner derivation is:

```lean
finiteDilatonDerivation A = (1 / 2) * (K*A - A*K)
```

The theorem:

```lean
finite_dilaton_action_on_nulls
```

proves:

```text
delta_K(u_+) =  u_+
delta_K(u_-) = -u_-
```

The finite squeeze element is:

```lean
kreinSqueeze sigma =
  exp sigma * P_+ + exp (-sigma) * P_-
```

The theorems:

```lean
krein_squeeze_projector_decomposition
krein_squeeze_left_right_null_scaling
krein_squeeze_half_conjugates_nulls
```

prove the diagonal rescaling of the two null generators.

At this finite `M_2(R)` level, this is an inner dilation shadow.  A genuinely
outer modular-time interpretation belongs to an infinite von Neumann/KMS
setting and is not asserted here.

## Off-Diagonal Mass Bridge

The local off-diagonal bridge is:

```lean
massBridgeBeta = splitQuaternionJ
massTerm m = m * massBridgeBeta
```

The theorem:

```lean
mass_bridge_beta_laws
```

proves:

```text
beta^2 = 1
K beta + beta K = 0
beta P_+ = P_- beta
beta P_- = P_+ beta
```

So diagonal `K`-squeeze preserves the local sector split, while the
off-diagonal mass bridge flips the two sectors.

## Schematic Wave-Equation Readout

The local algebra acts on a two-component real carrier by splitting it into
`P_+` and `P_-` sectors.  The null hops have the schematic interpretation:

```text
u_+ : P_- K -> P_+ K
u_- : P_+ K -> P_- K
```

At the purely algebraic level the theorem `causal_null_closure_laws` proves the
part that makes the first-order null decomposition work:

```text
u_+^2 = 0
u_-^2 = 0
u_+ u_- + u_- u_+ = 1
```

Thus a formal null first-order operator

```text
D_0 = u_+ partial_+ + u_- partial_-
```

is represented in Lean by:

```lean
masslessNullDiracSymbol dPlus dMinus
```

The theorem:

```lean
massless_null_dirac_symbol_sq
```

proves the finite scalar second-order core:

```text
D_0^2 = partial_+ partial_-
```

This is still an algebraic symbol theorem.  Analytic differential operator
hypotheses belong in a separate PDE/operator module.

## Cantor-Krein Sector Product

The Cantor projectors are different from the local Krein projectors.

The theorem-owner for finite Cantor cylinders is:

```lean
InfoGeometry.Canonical.CantorCylinderLattice
```

Key theorem names:

```lean
cylinderIndicator_idempotent
cylinderIndicator_refinement
```

The theorem-owner for the combined Cantor-Krein sector lattice is:

```lean
InfoGeometry.Canonical.SectorLattice
```

Key theorem names:

```lean
elementaryProjectionAssignment_idempotent
refineProjectionAssignment_elementary
projectionAssignment_galoisConnection
```

The intended sector picture is:

```text
global topology       : e_{n,w}
local causal chirality: P_+ or P_-
combined sector       : e_{n,w} tensor P_±
```

The Lean formalization represents this through finite functions and pointwise
Krein sectors rather than by postulating an analytic tensor-product operator
algebra.  That keeps the finite sector lattice theorem-owned and avoids a false
operator-algebra completion claim.

## Corrected Physical Claim

The algebra does not prove that the universe must be this structure.

The defensible claim is representation-level:

```text
generators define local transformations;
idempotents define sectors;
traces, indices, or pairings define observables once supplied by the relevant
operator-algebraic layer.
```

So the strongest local statement is:

```text
Cl(1,1) ~= M_2(R)
```

is a minimal finite algebraic model for:

```text
phase axis,
Krein squeeze,
null propagation,
sector projection,
off-diagonal sector coupling.
```

It is not a global theorem of physical inevitability and not a derivation of
current/conformal algebras.

## Closure Packet

The theorem:

```lean
localCausalConeClosure
```

packages the local theorem surface:

```text
split-quaternion laws
+ matrix laws
+ projector laws
+ matrix null-hop laws
+ matrix projector noncentrality
+ matrix spinor readout
+ null closure
+ sector hopping
+ finite dilaton action
+ squeeze scaling
+ off-diagonal mass bridge
+ null Dirac symbol square
```

The compact readback theorem:

```lean
final_local_causal_cone_identities
```

records the final local identities in one proposition:

```text
i^2 = -1
K^2 = 1
u_+^2 = u_-^2 = 0
P_+ = (1 + K) / 2
P_- = (1 - K) / 2
P_+ = u_+ u_-
P_- = u_- u_+
{u_+, u_-} = 1
[u_+, u_-] = K
kreinSqueeze sigma = exp(sigma) P_+ + exp(-sigma) P_-
K beta + beta K = 0
```

This is the correct local closure.  It is a rigorous finite algebraic model,
not a global physical necessity theorem.
