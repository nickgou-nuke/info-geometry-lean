# Lie--Jordan / Peirce epistemic compilation contract

Base: `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4` (main).
This is a separate addition from PR #228; it does not modify that branch.

## Intake provenance

- `Pasted text(20261028-091932).txt`: `2bbbcb930837a8ff82ab3e0d486f5af50289f870aa8c0d5df429f9ae2856d4f7`.
- `Pasted text (2)(20261028-092023).txt`: `0a95f3948dc8e241844197bd3034a9fcf01ee16817c91f0f7b1d2afa83599259`.

The source texts call their snippets verified. That assertion is not evidence.
The new statements are checked separately at their actual Lean types.

## Exact carriers and owners

- `Module.End R A`, with `[CommRing R] [Ring A] [Algebra R A]`; no
  commutativity of `A` or of the inputs is assumed. In particular `A` can be
  the full `Matrix n n R`, or an endomorphism algebra.
- Native `LinearMap.mulLeft`, `mulRight`, and `mulLeftRight` provide the maps.
- `Core.JordanAssociatorRing` owns `commutator_operator_commutator`,
  `commutator_symm_operator`, and `symm_operator_commutator`. The new bundled
  theorems reuse those proofs rather than reintroducing the identities.
- `Algebra.IdempotentProjector` owns `peirce11/10/01/00`, complementary
  idempotents, reconstruction, square-zero corners, and their products.
- `Algebra.PeirceDeWittChiralSplit` owns the even/odd sums and grading.
- `Clifford.Cl11TensorTowerLimit` owns the actual noncommutative matrix
  direct limit, its ring inclusions, and their successor compatibility.
  The separate diagonal-MASA cylinder carrier is not used as a substitute.

## Corrections, not silent reinterpretations

For `A = ad_H`, `B = J_S`, the source's ordered-product prose has the wrong
sign: `(A-B)(A+B) = A^2-B^2+[A,B]`, and `[A,B]=J_[H,S]`.
Both ordered products and their nonzero difference must be retained.

For an idempotent `p`, the source's complementary-corner formula is correct:
`2(1-p)X(1-p) = 2X-J_p(X)-ad_p^2(X)`. The initial intake review incorrectly
called that minus sign erroneous; both exact dense-matrix computation and
Lean rejected the resulting positive-sign variant. The final theorem retains
the source sign, and `positive_sign_variant_false` guards against repeating
that review error. The incorrect plus-sign variant has defect `-2 ad_p^2(X)`.
Also `dualMinus p p (ad_p X)=2(1-p)Xp`, not its negative.

`trace(XY)` is a bilinear trace pairing, not the complex Hilbert--Schmidt
inner product `trace(X^*Y)` and not a state-dependent BKM metric.
The weighted form `trace((2p-1)XY)` is generally nonsymmetric. Its symmetry
and alternating restrictions must be proved, not called a DeWitt metric,
Fubini--Study metric, Berry curvature, or Connes--Chern form by analogy.
No manifold, torsion-free connection, Levi-Civita identification, statistical
cubic tensor, dual flatness, physical Dirac wave, or spectral theorem follows
from these algebraic identities alone.

## Dependency order

Native regular-module multiplication -> bundled Lie/Jordan actions ->
operator brackets -> signed ordered products -> directional coefficient
commutators. Independently: native idempotent corners -> orthogonal projection
composition -> Peirce multiplication -> division-free quartet -> odd projection.
Their joint consumers are trace duality, matrix block identities, and transport
through the existing full-matrix direct limit. These are logical dependencies,
not asserted spacetime causal relations.

## Verification policy

Full proof terms only: no `sorry`, `admit`, custom axiom, `native_decide`,
scalar proxy, or assumed theorem hidden in a structure field.
The supplementary workflow uses the existing locked `check_peirce_weyl`
source-closure/axiom checker, with its target list specialized to this packet.
It checks the exact Mathlib commit and Lean toolchain from the unchanged
repository files, and does not claim a root-package build. It neither disables
nor replaces existing CI. Kernel verification is pending until the workflow
has actually completed; source inspection is not kernel verification.
