# Klein insertion and native graded Clifford doubling

## Exact contract

The informal input contains several distinct mathematical assertions. This change
keeps their carriers and hypotheses separate and proves the connecting maps.

| Layer | Carrier | Result |
|---|---|---|
| Block algebra | `Matrix (Fin 2) (Fin 2) A`, `[Ring A]` | Opposite diagonal insertion, Peirce/CAR relations, and integral reconstruction |
| Recursive family | Full nested block ring over `[Ring A]` | `2*n` explicitly indexed generators with their signed squares and all pairwise anticommutators |
| Native tensor equivalence | Real quadratic module `Q`, with no dimension assumption | `(evenOdd q11 ᵍ⊗[ℝ] evenOdd Q) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)` |
| Native tower classification | Existing `CliffordTower.Clsplit n` | `Clsplit n ≃ₐ[ℝ] M_(2^n)(ℝ)`, and `M_(2^n)(A) ≃ₐ[ℝ] Clsplit n ⊗[ℝ] A` for any real algebra `A` |

The coefficient ring in the first two rows is arbitrary and need not commute.
The third row uses Mathlib's actual `CliffordAlgebra`, `evenOdd`,
`GradedTensorProduct`, and `AlgEquiv` structures. It is a structural theorem,
not only a list of matrix relations.

## Reused owners and new implications

`SplitAtomDoubling` already owned `repeated`, `twisted`, the positive and
negative block seeds, and their elementary anticommutator identities. Its
block-only section moves to `SplitAtomDoubling/Basic`, retaining the existing
declaration names and mathematical statements. The proof scripts remove
unused simplifier arguments. The original import remains a compatible
entrypoint.

`Cl11Matrix.cl11EquivMat` owns the real split Clifford atom. The new tensor
proof uses that equivalence after an explicit Hadamard change of basis.
Mathlib's `CliffordAlgebra.involute` supplies the native parity automorphism.
The right-factor insertion is the algebra homomorphism

`a ↦ diag(a, involute a)`.

On the even submodule it is `repeated a`. On the odd submodule it is `twisted a`.
These restrictions are proved from Mathlib's even/odd involution theorems.
The two factor maps supercommute, so `GradedTensorProduct.lift` constructs
`untwistHom`. An explicit linear equivalence—ordinary matrix/tensor conversion
followed by applying `involute` to the second column—proves that this map is
bijective. Composing with `CliffordAlgebra.prodEquiv` gives the native split
periodicity step for `q11.prod Q`.

`BottPeriodicity.splitBottStep` remains the naming façade for the existing
`CliffordTower.clsplit_succ_equiv` recursive graded-factorization owner.
`Cl11SplitTowerMatrixEquiv` uses that same
`CliffordTower.Qsplit` quadratic form, iterates the newly proved matrix step,
and applies native matrix composition/reindexing. This gives a structural
all-stage matrix classification, followed by scalar extension to arbitrary
noncommutative real coefficient algebras. No competing tower carrier replaces it.

## Dependency order

1. Existing repeated/twisted block laws.
2. Chirality, Peirce matrix units, and parity-dependent insertion laws.
3. Generic family doubling, followed by recursion through the full matrix rings.
4. Existing real split Clifford equivalence and native Clifford involution.
5. Homogeneous supercommutation of the two factor maps.
6. Native graded tensor lift, explicit bijectivity, and the split Clifford
   algebra-to-matrix equivalence.
7. Existing split quadratic tower, successor untwisting, full matrix-index
   flattening, and scalar extension to the noncommutative coefficient algebra.

The recursive matrix-family branch and native tensor branch share the block
calculus, but neither is presented as a consequence of a mere dimension count.

## Scope corrections

- `twisted a = diag(a,-a)` is not an algebra homomorphism on an ungraded ring:
  `twisted a * twisted b = repeated (a*b)`. The native algebra map above inserts
  the sign according to actual Clifford parity.
- `klein_reconstruction` proves an integral identity with right side `M + M`.
  Turning this into inversion requires an inverse for two. In characteristic
  two it does not recover the input matrix.
- The Clifford isomorphism is stated over `ℝ`; arbitrary-ring block identities
  do not establish an integral Clifford matrix classification.
- The recursive theorem constructs and checks a family in nested matrix rings.
  Its `2*n` count is the cardinality of the index type. In characteristic two,
  the positive and negative signs coincide and indexed matrix elements can
  coincide as well. No distinctness, linear independence, or algebra-generation
  conclusion is asserted for this arbitrary-ring family.
  It does not identify an analytic completion, a colimit topology, or a physical
  Majorana Hilbert-space representation.
- The `Cl(1,1)` and coefficient Clifford factors are multiplied using the
  Koszul multiplication until the explicitly proved untwisting equivalence is
  applied. An underlying tensor linear equivalence alone is not used as an
  algebra equivalence.

## Validation

Validation results are recorded in the pull request and source-bound report.
No previous-run verification is inherited by this rewrite.
