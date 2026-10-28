# Lie--Jordan / Peirce epistemic compilation contract

Base: `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4` (main).
Separate addition from PR #228; its branch and dependency pins are unchanged.

## Source and exact scope

Source: the two user-supplied pastes dated 2026-10-28, at 09:19:32 and
09:20:23, titled operatorial information geometry and Peirce--DeWitt geometry.
Their assertions of verification are not compiler evidence.

The carrier is `Module.End R A` for an arbitrary associative `R`-algebra,
including the full matrix algebra. Native `LinearMap.mulLeft`, `mulRight`,
and `mulLeftRight` provide the operations. No matrices are diagonalized and
no commuting-input hypothesis suppresses the defects.

Existing owners read before drafting:
- `Core.JordanAssociatorRing`: `commutator_operator_commutator`,
  `commutator_symm_operator`, `symm_operator_commutator`.
- `Algebra.IdempotentProjector`: `peirce11/10/01/00`, reconstruction,
  complementary idempotents and off-diagonal square-zero laws.
- `Algebra.PeirceDeWittChiralSplit`: even/odd parts and grading.
- `Clifford.Cl11TensorTowerLimit`: full-matrix direct limit and stage maps.

## Corrections

For `A=ad_H`, `B=J_S`, `(A-B)(A+B)=A^2-B^2+[A,B]`, with
`[A,B]=J_[H,S]`. The source's ordered-product prose has the wrong sign.
Both ordered products must retain this term.

The complementary Peirce formula is
`2(1-p)X(1-p)=2X-J_p(X)+ad_p^2(X)`, with a positive double-commutator term.
The source formula's defect is `2 ad_p^2(X)`.
Also `dualMinus p p (ad_p X)=2(1-p)Xp`, not its negative.

`trace(XY)` is a bilinear trace pairing, not `trace(X^*Y)` and not a
state-dependent BKM metric. The weighted form `trace((2p-1)XY)` is generally
nonsymmetric. Its restricted symmetric/alternating behavior must be proved.
No DeWitt/Fubini--Study/Berry/Connes--Chern identification is asserted.

## Dependency poset

Native multiplication -> bundled Lie/Jordan actions -> operator brackets ->
signed ordered products -> directional coefficient commutators.
Native idempotent corners -> projector composition -> Peirce multiplication ->
corrected quartet -> parity projection. Their common consumers are trace
pairings, block-operator factorization and native matrix-colimit transport.
These are proof dependencies, not physical causal relations.

## Verification

The supplementary workflow specializes the existing serial
`tools.quality.check_peirce_weyl` checker. It compares the exact Mathlib commit
and Lean toolchain with the unchanged manifest, compiles the source-import
closure, and audits transitive axioms. This is not the root Lake package build,
and it does not disable or replace existing CI. Verification remains pending
until the actual workflow succeeds. No placeholder proof or custom axiom is
permitted. Further consumers are added to the same scoped target list.
