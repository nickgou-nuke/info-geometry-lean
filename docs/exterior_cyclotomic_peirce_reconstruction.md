# Exterior degree, cyclotomic projectors, and finite Peirce matrices

## Source and scope

The source is the current attachment `Pasted markdown(20260906-080631).md`. Its six sections propose a higher-dimensional wedge/Hodge replacement of Zorn cells, a chiral Peirce matrix, paravectors, and a finite-order Fourier decomposition. This extension retains the exact associative/exterior constructions and distinguishes them from claims not supported by those constructions.

The repository foundation is `main` commit `b0fa422e6cb6d3da5be7cbbb5ecfae5c12f3237b`. The new branch does not depend on previous draft PRs. Existing Zorn multiplication, Clifford carriers, exterior parity, and Hodge operators remain unchanged.

**Verification:** the new Lean declarations have explicit proof scripts but have not been elaborated here. The actual local build launcher stopped with exit 127 because `lake` is unavailable. Independent exact polynomial/matrix regressions and the source/audit-coverage scan passed. Neither certifies imported proof dependencies. Keep the PR draft until the focused build and native transitive audit execute successfully.

## 1. General finite Peirce decomposition, with the actual corner constraints

The existing `Core.PeirceDecomposition` already owns the binary decomposition and routing laws. The new `Core.FinitePeirceMatrix` generalizes them using Mathlib's `CompleteOrthogonalIdempotents`, for an arbitrary finite index type, in any associative algebra A over a commutative scalar ring K.

For a complete orthogonal family e_i define

```
blocks(e,x)_ij = e_i x e_j,
assemble(B) = sum_ij B_ij,
cornerSpace(e) = { B | e_i B_ij e_j = B_ij for every i,j }.
```

The source includes the two-sided reconstruction and multiplicative laws:

```
assemble(blocks(e,x)) = x,
blocks(e,assemble(B)) = B  for B in cornerSpace(e),
blocks(e,xy) = blocks(e,x) blocks(e,y),
blocks(e,1) = diag(e_i).
```

`cornerEquiv` is a genuine linear equivalence from A to this constrained matrix subspace. Its multiplication compatibility, product closure, and left/right unit identities are separately proved. No Ring or Algebra instance with an incompatible ambient matrix unit is installed.

This is not the unrestricted matrix algebra `Matrix I I A`. In particular its identity is the diagonal projector family, not the ambient diagonal of copies of 1. Orthogonal intermediate sectors annihilate, and every individual off-diagonal corner squares to zero. The binary specialization agrees definitionally with the repository's four existing component functions.

The construction requires neither primitive nor nonzero projectors. Primitive idempotence is a strictly stronger condition than complementarity, and is not inferred.

## 2. Constructed fourth-order Fourier projectors

The existing `Canonical.CyclotomicProjectorReadout` has a general law-field interface and a concrete binary instance. The new `Algebra.FourthRootPeirceProjectors` constructs the fourth-order case in any complex associative algebra. The hypothesis is `U^4=1` (order dividing four), not a promise that all four sectors are nonzero.

With z_k=i^k, define

```
P_k(U) = 1/4 [1 + z_k^3 U + z_k^2 U^2 + z_k U^3].
```

A theorem identifies this with the attachment's inverse-character Fourier sum. From the polynomial condition, the scripts derive

```
U P_k = z_k P_k,
P_j P_k = delta_jk P_k,
sum_k P_k = 1,
U = sum_k z_k P_k.
```

Only after those derivations is the existing `FourierCyclotomicReadout` populated. The native complete-idempotent family then instantiates the finite Peirce reconstruction. The selection theorem is provided both for algebra eigenvectors and for vectors in a module, without a finite-dimensionality requirement.

The finite Peirce theory is arbitrary-index; the Fourier-polynomial construction in this extension is specifically order four. A constructed Fourier resolution for every n is not claimed. General finite Fourier formulas need a suitable splitting scalar field, invertible n, and a primitive scalar root. Algebraic orthogonality `P_j P_k=0` is not automatically self-adjoint orthogonality; that requires additional adjoint/unitarity assumptions.

## 3. The exact square-minus-one obstruction

The attachment's lines 126–132 identify a volume-type operator with square -1 with four exterior degree classes. The direct polynomial calculation instead gives

```
If U^2=-1:
P_0=0,
P_1=(1-iU)/2,
P_2=0,
P_3=(1+iU)/2.
```

There are only two possibly nonzero eigenspace sectors, +i and -i. Order dividing four alone does not determine a four-way degree decomposition.

This is instantiated with the repository's actual six-component Lorentzian `hodgeStarLinear`. Its two nonzero Fourier formulas equal the existing `selfDualPartLinear` and `antiSelfDualPartLinear`; no replacement Hodge matrix is defined. The geometric derivation of that finite star from a smooth metric is not supplied by this specialization.

## 4. The genuine exterior degree phase

`Clifford.ExteriorDegreePhaseFour` constructs the correct operator on `ExteriorAlgebra Complex V` for any complex module V, through native exterior functoriality:

```
degreePhase = ExteriorAlgebra.map (i * identity_on_V).
```

It is multiplicative for the exterior product. Its square is proved equal to the repository's existing generic `ExteriorSpinorChiralityBridge.gradeInvolution`, as an equality of algebra homomorphisms. The corresponding linear operator has fourth power identity.

The phase law is proved first on native alternating products, then on the entire native kth exterior-power submodule using its universal property:

```
U(x) = i^k x      for x in exteriorPower(k,V),
P_j(x) = x       if j = k mod 4,
P_j(x) = 0       otherwise.
```

Thus these are actual degree-residue projectors, not merely a relabeling of a different operator's eigenvalues. Their even and odd coarsenings recover `(1+grade)/2` and `(1-grade)/2` exactly.

The same phase has the all-state identities

```
U(v wedge x) = i (v wedge Ux),
U(contract_phi x) = -i contract_phi(Ux).
```

These use native exterior multiplication and `CliffordAlgebra.contractLeft`. On the scalar unit U acts as identity, which proves that U squared cannot equal minus the identity operator.

A separate theorem rules out silently transporting multiplicativity to a nonzero quadratic Clifford product. In any nontrivial complex algebra, if `a^2=q*1` with q nonzero, no complex algebra homomorphism can send a to ia. Applying the proposed homomorphism to the square would give q=-q. Consequently exterior degree modulo four is not, in general, a Clifford algebra grading with the original product; Clifford contraction changes degree by two while preserving parity.

## 5. The existing real 32-dimensional exterior spinor is used directly

`Canonical.ExteriorCyclotomicPeirceBridge` uses the existing `SplitClifford55ExteriorParity` projectors, rather than constructing another real spinor space or volume operator. Their already-proved laws provide `spinProjectorsComplete`, and the new finite corner equivalence applies to their full endomorphism algebra.

The actual wedge-plus-contraction Clifford-vector action has zero diagonal chiral blocks. Products of two vector actions have zero off-diagonal blocks. More strongly, `evenClifford_offDiagonal_zero` applies to every element of the existing native even Clifford algebra, reusing the owner's invariant-subspace theorem.

These are full parity blocks. They are not confined to scalar/pseudoscalar degrees on the diagonal or vector/pseudovector degrees off the diagonal. The source's initial restricted table omits intermediate grades; its later full even/odd sums are the correct associative interpretation.

The general complex exterior phase and the existing real five-mode spinor are separate scalar-field constructions. No unstated real/complex basis identification is inserted.

## 6. A grade-shifting relation does not imply nilpotence

The attachment also asserts a cyclic sector-ladder rule with a nilpotent operator. The new module constructs a concrete 4-by-4 cyclic shift N and diagonal clock U such that

```
U N = i N U,
N P_k(U) = P_(k+1 mod 4)(U) N,
N^4 = 1 != 0.
```

Thus the stated covariance alone does not imply `N^4=0`. Nilpotence requires its own algebraic or filtration argument. In contrast, native left wedge multiplication by one vector really has square zero; the bridge proves this from the existing exterior relation.

The independent exterior-matrix regression checks the raising and lowering projector identities for all basis states in dimensions 3, 4, and 5. In Lean, the generic all-state phase-covariance and homogeneous-projector selection theorems are provided; the matrix regression is not substituted for those scripts.

## 7. Geometric product and paravector interval without an invented determinant

The bridge uses the native `CliffordAlgebra.equivExterior` and `changeForm_ι_mul_ι` identity. Its exact readout of two Clifford vectors is

```
equivExterior_Q(ι(u)ι(v)) = ι_ext(u)ι_ext(v) - associated(-Q)(u,v)*1.
```

Since `associated(-Q)=-associated(Q)`, this is the scalar contraction plus exterior wedge formula. The equivalence is linear, not multiplicative.

The actual paravector product is also proved for arbitrary real quadratic form Q:

```
(t*1 + ι(v))(t*1 - ι(v)) = (t^2 - Q(v))*1.
```

It does not require a Hodge map or a generalized determinant of form-valued blocks. The expression in the source involving a dot product of a vector with its Hodge dual does not specify an ordinary determinant. With differential-form conventions, top-form norm expressions use wedge and a specified metric/orientation; that is a separate construction.

## 8. Other qualifications retained at the boundary

The usual norm-compatible vector-cross-product restriction needs its actual axioms and scalar/metric hypotheses. A dimension mismatch does not forbid arbitrary alternating bilinear maps `V x V -> V`; in particular the exceptional seven-dimensional construction is not an isomorphism from all of the 21-dimensional second exterior power to V. This PR does not claim a cross-product classification or construct a new alternative composition algebra.

With an orthogonal real Clifford frame satisfying p positive and q negative squares, the volume square is `(-1)^(q + D(D-1)/2)`. Thus Euclidean dimension four and signature (2,2) give +1, not the source's -1 examples. Signature (2,2) is split, not Lorentzian (1,3) or (3,1). A normalized chirality operator must be distinguished from the raw volume element and from a Hodge operator. Hodge maps degree k to D-k; for even D it preserves degree parity rather than reversing it.

No smooth Clifford bundle, Dirac–Kähler differential equation, metric Hodge theorem, gauge curvature, quantization functor, or nonassociative Zorn multiplication is derived merely from an associative Peirce decomposition. Those require additional defined data and proofs.

## Reproduction

```
bash scripts/check_cyclotomic_peirce.sh
python3 scripts/audit_cyclotomic_peirce_sources.py
python3 scripts/audit_cyclotomic_peirce_exact.py
```

The first command builds `InfoGeometry.Canonical.ExteriorCyclotomicPeirceBridge`, then checks native transitive axiom reports for every public declaration. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The exact-regression companion requires SymPy.

The actual recorded source scan covers five Lean files and 79 public declarations: 60 theorems and 19 definitions. The local launcher did not execute Lean. The independent exact tests cover the Fourier polynomials, constrained corner products, non-self-adjoint idempotent example, cyclic shift, 8/16/32-state exterior models, Clifford paravectors, and the existing finite Hodge formulas.

Primary code references are the pinned Mathlib `RingTheory/Idempotents.lean`, `ExteriorAlgebra/Basic.lean`, `ExteriorPower/Basic.lean`, and `CliffordAlgebra/Contraction.lean`, plus the repository owners cited above. Proof scripts and these independent checks are not a kernel-certification claim.
