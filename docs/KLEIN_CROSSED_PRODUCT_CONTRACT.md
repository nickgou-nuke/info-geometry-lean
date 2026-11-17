# Klein, skew-polynomial and CAR theorem contract

## Intake and provenance

Source: user attachment `Pasted text(20261116-172043).txt`, received
2026-11-16. SHA-256:
`59b9de1246525d12fd6200f92ed79ed5b0ea7f7af0fc1b73e24943f89351e593`.
The original attachment is preserved unchanged. This document records the
mathematical claims extracted from it; its psychological narrative is not a
hypothesis, proof method, or conclusion of the Lean development.

Base revision: `08c34e03f610b452e03422037949196dc7d92d6d`.
Work branch: `codex/klein-crossed-product-20261116`.
The earlier split-spinor work and draft PR #363 are a separate change.

## Source search and existing owners

The search covered repo-owned Lean sources using filenames, theorem names,
formulas, imports, and consumers. Candidate owners were read directly. No
fresh declaration-graph snapshot was available in the inspected artifact
surface; graph provenance is not claimed. Exact Lean source is authoritative.

| Subject | Existing owner and reusable declarations | Actual scope |
| --- | --- | --- |
| Glide square | `Canonical/KleinBottleTwistedCommutantBridge.lean`, `klein_glide_square_in_commutant` | Relative commutant of the embedded coefficient ring. |
| Group center | `Canonical/KleinOrientationCharacterBridge.lean`, `nativeKlein_mem_center_iff_glide_square_zpow` | Center of the native Klein semidirect-product **group**. |
| Orientation character | Same owner, `nativeKlein_mem_center_iff_left_eq_zero_and_orientation_one` | Separates the center from the larger orientation kernel. |
| Half-sum nilpotents | `Algebra/CPTComplexStructure.lean`, `isotropicSheetPlus_sq`, `isotropicSheetMinus_sq`, `isotropicSheets_anticommute` | A real algebra with a `Cl11Atom`. |
| CAR projectors | `OperatorAlgebra/CARProjectors.lean` | Complementary orthogonal idempotents from a `SplitClifford.CARPair`. |
| CAR matrix units | `Canonical/ReflexiveMatrixCorner.lean`, `pairMatrixUnit_mul`, `pairMatrixCornerHom`, `pairMatrixAlgHom` | Matrix multiplication inside an associative algebra under the stated support hypotheses. |
| Compression defect | `Core/PeirceCompressionDefect.lean`, `compression_mul_defect` | Exact ordered difference `e*(a*b)*e - (e*a*e)*(e*b*e) = e*a*(1-e)*b*e`. |
| Projector ansatz | `OperatorAlgebra/Z2ProjectorWeights.lean`, `projectorPlus`, `projectorMinus` | Existing rational half-sum definitions; idempotence was proved under an involution hypothesis. |
| Polynomial evaluation | Pinned Mathlib `Algebra/Polynomial/Eval/Defs.lean`, `eval₂_mul_noncomm`, `eval₂RingHom'` | Evaluation is multiplicative when the coefficient images commute with the evaluation point. |
| Skew multiplication | Pinned Mathlib `Algebra/SkewPolynomial/Basic.lean` | Actual skew monoid algebra with twist `SkewPolynomial.φ`. |
| Characteristic identity | Pinned Mathlib `LinearAlgebra/Charpoly/Basic.lean`, `Algebra.aeval_self_charpoly_lmul` | Finite free algebras admit a regular-representation characteristic identity without an Azumaya assumption. |

The bounded search found no existing exact quadratic crossed-product matrix
subring, generic CAR two-sided-ideal collapse theorem, or requested skew
factorization. It did find extensive neighboring topology, Peirce, Clifford,
and group-theoretic constructions; those are not replaced by this work.

## Atomic claim ledger

| ID | Source passage | Correct mathematical statement / boundary | Initial classification |
| --- | --- | --- | --- |
| K1 | Phase 0.1, Ded.1 | The Klein relation forces the double glide to commute with the phase generator. Ambient centrality needs a generation hypothesis or an explicit ring model. | Owner-backed / conditional |
| K2 | Phase 0.1, Ded.7 | The commutative orientation-cover subalgebra and the center are different objects. The group center and orientation kernel are also distinct. | Correction / owner-backed group statement |
| K3 | Ded.1 | For invertible generators satisfying the Klein relation, commutation implies `U²=1`, not `U=1` or `U=-1` in an arbitrary operator ring. | Counterexample to the stronger claim |
| K4 | Phase IV, Ded.2 | `P=(1+G)/2` has defect `(G²-1)/4`; idempotence is equivalent to `G²=1` over a rational algebra. | Candidate extension of existing owner |
| K5 | Phase 0.2, Ded.2 | In the actual skew polynomial ring, `φ(v)=u` and `u*v=1` imply `(X-Cu)*(X+Cv)=X²-1`. | Candidate |
| K6 | Phase IV | The ordered symmetric-factor defect is `C(φ(u)-u)*X`. Its nonzero status requires `φ(u)≠u`. | Candidate |
| K7 | Phase 0.2 | Central/centralizing-coefficient polynomial evaluation is legitimate in noncommutative targets. Reduced characteristic polynomials are not the sole available construction. | Native Mathlib reuse / correction |
| K8 | Phase 0.3 | Nilpotency, field inseparability, Lie roots, and conjugacy orbits are distinct notions. Zero may be a weight; nilpotent cones need not be individual smooth orbits. | Correction |
| K9 | Ded.3 | In the existing real-algebra `Cl11Atom` owner, half-sums of an involution and an anticommuting square root of `-1` form a CAR pair. General invertible-2 coefficients are outside this adapter's scope. | Existing owner plus compatibility map |
| K10 | Ded.3 | In any unital ring, `ab+ba=1` implies that a two-sided ideal containing **either** `a` or `b` is the whole ring. Nilpotency and simplicity are unnecessary. | Candidate stronger theorem |
| K11 | Ded.3 | A unital homomorphism killing either CAR generator has a subsingleton codomain; the corresponding two-sided quotient is zero. | Candidate consequence |
| K12 | Ded.4 | An involutive automorphism of a commutative coefficient ring and a fixed parameter give a faithful quadratic matrix subring with ordered crossed multiplication. | Candidate construction |
| K13 | Ded.4–5 | Its trace and determinant are fixed by the automorphism and embed centrally; its elements satisfy the specified quadratic characteristic identity. | Candidate |
| K14 | Ded.5 | A glide with `G²=T` is a **twisted** quadratic construction; an ordinary `C₂` semidirect product has the canonical generator square 1. | Correction |
| K15 | Phase IV, Ded.6 | Laurent invariants, global center equality, finite rank over that center, discriminant localization and Azumaya status require their own constructions and hypotheses. | Conditional / open debt |
| K16 | Ded.6 | `G²=T` does not by itself prove a nonzero Brauer class. Cyclic algebras can split; base extension can kill a Brauer class. | Counterexample to permanence claim |
| K17 | Ded.8 | CAR projectors and Peirce blocks are already owned. Compression is additive and is not generally multiplicative; proper central fibers need nonzero-fiber hypotheses. | Owner-backed / correction |
| K18 | Phase V | Increasing rank can certify acyclicity of a given graph, but cannot prove its nodes or uniqueness of a mathematical synthesis. No maps/category define the proposed obstruction colimit. | Interpretation / open debt |

## Ground-truth contracts

### A. Twisted quadratic matrix ring

Carrier: `Matrix (Fin 2) (Fin 2) L`, with `[CommRing L]`, a ring equivalence
`σ : L ≃+* L`, `Function.Involutive σ`, and `T : L` satisfying `σ T = T`.
Define the actual matrix

```text
ρ(a,b) = [[a, b*T], [σ b, σ a]].
```

Prove that this coordinate map is injective, preserve ordinary addition, and
prove the **ordered** matrix multiplication formula

```text
ρ(a,b) * ρ(c,d) = ρ(a*c + b*σ(d)*T, a*d + b*σ(c)).
```

Close its image as a native `Subring`. The coefficient embedding is `a ↦ ρ(a,0)`
and the glide is `ρ(0,1)`. Prove the glide square, the twisted coefficient
relation, and the fixed-coefficient centrality criterion. Prove that
`a+σ(a)` and `a*σ(a)-T*b*σ(b)` are fixed by `σ`, identify them with the native
matrix trace/determinant, and prove the quadratic characteristic identity.

No unit assumption on `T` is needed for the faithful quadratic ring. Prove
`glide_isUnit` separately from `IsUnit T` using the native unit-power theorem
and the coefficient homomorphism. This is an actual matrix subring, with
noncommutative instances, over a commutative **coefficient** ring; it is
not a scalar replacement of the operator product. No Laurent-center
classification, Galois/étale extension, universal Ore quotient property,
Azumaya locus, or reduced characteristic polynomial in a separately
constructed central simple algebra is asserted.

The concrete complex-conjugation instance with `T=1` proves that the actual
glide and embedded `Complex.I` fail to commute inside this image. The existing
generic matrix-unit owner supplies the separate ambient `M₂(R)` witness.
The general theory continues to admit commutative identity-twist instances.

### B. Native skew-polynomial factorization

Carrier: `SkewPolynomial R` with `[Ring R]` and
`[MulSemiringAction (Multiplicative ℕ) R]`. The twist is the native
`SkewPolynomial.φ`, not an unrelated automorphism. Constants use its native
`C` and the variable its native `X`.

Required input: `φ v = u` and `u*v=1`. Prove the exact factorization and
ordered symmetric-factor defect. Keep all products in their written order.
Neither global commutativity nor involutivity of the twist is needed for this
minimal theorem. Distinct factorizations, irreducibility, skew root evaluation,
and uniqueness up to associates are separate statements.

### C. CAR two-sided ideals and existing Clifford sheets

Carrier: any unital associative ring `R`, native `TwoSidedIdeal R` and unital
`RingHom`. Input: `a*b+b*a=1`. Prove `a∈I → I=⊤` and its counterpart for `b`,
then the actual quotient/subsingleton and homomorphism consequences. These
are useful impossibility results about proper quotients, not vacuous attempts
to prove an unrelated geometric theory from `0=1`.

Reuse `SplitClifford.CARPair` and the existing real-algebra `Cl11Atom` sheets.
Any adapter must construct the compatibility laws using the existing square
and anticommutator theorems and then feed the actual quotient theorem. No
new half-sum definitions or duplicate matrix-unit API are needed.

### D. Defect of the existing half-sum projector

Carrier: `[Ring A] [Algebra ℚ A]`. Reuse `projectorPlus` and `projectorMinus`
from `OperatorAlgebra/Z2ProjectorWeights.lean`; add exact defect identities
and idempotence iff the original operator squares to 1. The original source
uses an umbrella Mathlib import; narrow it to the actual existing finite-spin
and tactic imports if the complete owner still compiles. No dependency pin
changes and no new projector carrier.

## Genuine dependency order

- Native skew multiplication → `X*C` relation → factorization and ordered defect.
- Matrix coordinates → injectivity and ordered multiplication → native subring.
- Matrix formula + involutivity/fixed parameter → trace/norm invariance.
- Fixed coefficient centrality + quadratic identity → a central quadratic annihilating identity.
- Existing Clifford sheet squares/anticommutator → explicit CAR compatibility.
- `ab+ba=1` + two-sided absorption → ideal equals top → quotient/homomorphism collapse.
- Existing half-sum definition → exact defect → idempotence iff involution.

There are no proved dependency arrows from these algebraic facts to an
orientation class, an Azumaya classification, a physical law, or an obstruction
colimit. The broader attachment contains useful research questions, but those
questions do not become axioms in the promoted Lean code.

### Global algebra versus split fibers

The Laurent Klein model `C[u±1][g±1; σ]`, with `σ(u)=u⁻¹`, is a domain:
for nonzero finite Laurent sums whose highest `g` exponents are `m,n`, the
coefficient of `g^(m+n)` in their product is `a_m * σ^m(b_n)`, which is
nonzero. Thus this global ring has no nonzero nilpotents. A CAR pair in a
split matrix fiber or after scalar extension cannot be silently treated as
a pair in that global ring. The present quotient theorem assumes a CAR pair
on its actual carrier and does not construct one globally. This elementary
domain argument is explanatory mathematics, not an additional Lean theorem
of this change.

### References for boundaries beyond this Lean slice

- [Mathlib's polynomial-evaluation API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Eval/Defs.html)
  explicitly supplies multiplicative evaluation into a noncommutative target
  under coefficient-commutation hypotheses. Local pinned sources determine
  the exact API used here.
- T. Y. Lam and André Leroy, [Principal One-Sided Ideals in Ore Polynomial Rings](https://leroy.perso.math.cnrs.fr/Articles/principal.pdf),
  §2: skew right-root evaluation is defined by one-sided division and has a
  twisted product rule. A factorization identity alone is not ordinary
  substitution or a unique-factorization classification.
- Simon Crawford, [Azumaya Skew Group Algebras and an Application to Quantum Kleinian Singularities](https://arxiv.org/abs/1711.08669),
  Theorem 1.1: the Azumaya criterion includes explicit algebra, action, and
  freeness hypotheses. No such criterion is discharged by the matrix
  identities alone.
- Philippe Gille and Tamás Szamuely, [Central Simple Algebras and Galois Cohomology](https://www.math.ens.psl.eu/~benoist/refs/Gille-Szamuely.pdf),
  Corollaries 4.7.4–4.7.5: in the cyclic Galois **field** setting the Brauer
  class is controlled by the parameter modulo norms. Being a nontrivial
  square relation is not a proof that the Brauer class is nonzero, and a
  splitting field can kill the class.

## Verification plan and acceptance boundary

Use the pinned Lean 4.34.1 / Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` without changing dependency metadata.
All compilation is serialized under the shared build lock. Check exact source
closures and all selected declaration axioms; run strict placeholder, semantic
vacuity, and OpenGauss checks and the installed staged proof gate. Independent
agents review candidates other than their own. Record exact commands and
source hashes in the final verification report.

The earlier root Lake workspace blocker was the missing unversioned path
package `external_refs/homotopy-hypothesis-lean4`; narrow native source checks
must not be reported as a complete repository build.
