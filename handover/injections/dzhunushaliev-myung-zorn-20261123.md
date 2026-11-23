# Dzhunushaliev: Table I, Myung's criterion, and the canonical Zorn basis

## Intake and provenance

The 2026-11-23 request supplies an audit and proposed Lean source for Vladimir
Dzhunushaliev, *Hidden structures in quantum mechanics*,
[arXiv:0805.3221v6](https://arxiv.org/pdf/0805.3221v6), revised 29 November
2008. The journal version appeared in 2009. The request connects the printed
Table I, equations (17)–(28), the representation question (29)–(31), and the
Myung criterion (38)–(40) to the repository's Peirce/Zorn infrastructure.

The intake proposes a new `RepairedSplitOct R` carrier. This implementation
instead reuses `InfoGeometry.Canonical.ZornMatrix R`, its actual product,
Peirce idempotents, and upper/lower basis. No complex scalar is introduced.

Repository baseline: `fe24e350b08fdea04f74c0748ef9fd9417c47529` (`main`).
Lean: `v4.34.1`. Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Claim ledger and theorem contract

| Intake | Exact contract | Boundary |
|---|---|---|
| Table I is not alternative | Transcribe all signed basis products and extend them bilinearly to `Fin 8 → ℤ`; prove the two associators and a repeated-argument right-alternativity counterexample | A theorem about this full printed table; opposite commutator signs alone are not an abstract obstruction |
| Repair the table by Zorn multiplication | Use the canonical Zorn product with `qSpin = lower − upper`, `qSpace = upper + lower`, `qCut7 = minus − plus` | Several mixed products change signs; this is not a one-entry repair |
| Universal Leibniz defect | Native Mathlib `associator` and repository `akivisBracket` on any `NonUnitalNonAssocRing` | No associativity, scalar field, or characteristic assumption |
| Myung necessity | Every inner commutator obeying Leibniz implies diagonal flexibility, its linearization, and Jacobi | Ordinary flexibility and its linearization are kept distinct |
| Myung converse | Linearized flexibility plus Jacobi imply Leibniz when integer multiplication by two has trivial kernel | No unrestricted characteristic-two converse |
| Alternative defects | Integer coefficient identities `D = −3 • associator` and `J = 6 • associator` | Nonzero conclusions require a separate carrier/hypothesis |
| Spin reconstruction | Explicit cyclic products, commutators, squares, full quaternion-slice closure/associativity, and chiral associator on the existing Zorn carrier | Real algebraic generators; the paper's complex spin normalization is not silently retained |
| Characteristic-two sharpness | The Zorn algebra over `ZMod 2` is flexible and has zero Jacobiator everywhere, but the pure upper Peirce triple has Leibniz defect `1` | The upper-basis witness is used because `qSpin` and `qSpace` coalesce in characteristic two |
| No matrix realization | Reuse obstruction to **injective multiplication-preserving** maps into associative semigroups | Linear left-regular maps still exist; they fail multiplicativity by the associator |
| Clifford Nambu realization | Refer to the actual operator, coefficient, and carrier of any existing implementation | An alternating triple product is not an associator and does not solve equation (31) |
| Mapping to Axioms 1–4 | Peirce basis relationships only, wherever proved | No physical unobservability, dynamics, or equivalence of whole frameworks follows from the finite identities |

## Owner search

The bounded source search covered `lean/InfoGeometry`, related `src/` owners,
and the imported Mathlib associator API. It followed definitions, native
instances, theorem statements, and consumers rather than filenames alone.

- `Algebra/AkivisIdentity.lean`: native associator, `akivisBracket`,
  `akivisJacobiator`, and `akivis_identity`. The generic Leibniz expansion is
  factored into this algebra layer.
- `NCG/ZornCommutator.lean`: existing generic product-rule defect and its
  operator-valued specialization. Its public generic theorem is retained and
  now reuses the algebra-layer expansion.
- `Algebra/AssociativityObstruction.lean`: injective multiplicative maps into
  associative semigroups force source associativity.
- `Canonical/ZornSpinor.lean`: the canonical carrier, native additive/module
  structures, Zorn product, `zornPlus`, `zornMinus`, `chiralUpperBasis`, and
  `chiralLowerBasis`.
- `Canonical/CanonicalZornNonUnitalNonAssocRing.lean`: the native nonassociative
  ring instance; its previously real-only statements are generalized to
  commutative coefficient rings without changing the carrier or product.
- `Canonical/ZornCliffordRepresentation.lean`: existing `zornNormFun` on this
  same carrier.
- `Canonical/SplitOctonionAssociator.lean`: the exact left-regular
  multiplication defect, with explicit nonassociative bracketing.
- `Algebra/ZornVectorMatrix.lean`, `Algebra/ZornAlternativeLaws.lean`, and
  `Canonical/SplitOctonionParaKahlerNullCone.lean`: related alternativity,
  composition, and representation-obstruction results on other carriers.
  No unproved carrier identification is used.

## Dependency order

1. Native additive and distributive laws give the universal Leibniz and
   Jacobi identities.
2. Vanishing Leibniz defects gives the characteristic-free Myung necessity.
3. Outer-skew associators give `2D = −J`; cancellation of two gives the converse.
4. Alternating associators give the exact integer coefficients `−3` and `6`.
5. The corrected Zorn basis supplies the concrete associator and nonzero real
   defect witnesses.
6. The independently transcribed printed table supplies a counterexample to
   the source's claimed alternativity.

## Source corrections

The PDF has `q₁q₂ = q₃`, `q₄q₅ = −q₃`, `q₁q₄ = −q₇`, and `q₁q₅ = q₆`
in Table I. Its Zorn formula (23), applied to its own basis (24)–(26), instead
gives `q₄q₅ = q₃`, `q₁q₄ = q₇`, and `q₁q₅ = −q₆`, while preserving
`q₁q₂ = q₃`. The table's alternativity failure is established directly;
there is no assumption that a lone orientation choice explains all failures.

Equations (20), (21), and (28) also require care with the complex spin factor
and Einstein summation. The delivered real reconstruction does not assert
that these printed normalizations are mutually consistent.

A bounded source check did not find the intake's named
`DiracSpinCasimirNambuModules` in this baseline. The existing
`Algebra/NoncommutativeZornNambuAssociator.lean` proves the six-term alternating
polynomial over an associative ring. The separately existing
`Canonical/SplitOctonionDiracFrameCl31.lean` gives anticommuting generators in
the nonassociative Zorn carrier. Neither result supplies the claimed
associative real Clifford/Hodge realization; that identification remains
outside this implementation.

The paper states the Myung equivalence without a characteristic qualifier.
The exact ring-level result here exposes the required cancellation explicitly.
See also Kamiya and Okubo, RIMS Kôkyûroku 1809 (2012), Proposition 1.1,
which assumes characteristic different from two:
<https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1809-05.pdf>.

## Validation scope

Current disposition: **reviewed candidate; kernel verification blocked**.
The independent A-A semantic review passed. A distinct QA-A reviewed the
source, verifier, and scope, but has not granted compiler acceptance.

The six-owner strict OpenGauss screener and strict refute checks passed with
zero traps. Static Gate 4 passed with its explicit
`STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED` status. The semantic scan reported
ten `trivial_surface` warnings: eight native coordinate readbacks, the exact
left-regular defect readback, and the retained self-commutator identity. Both
independent reviewers assessed those warnings as correctly scoped statements.
The staged proof gate and whitespace check passed. The bounded source
inventory contains 101 explicitly named public declarations; this is an
inventory count, not a completed axiom audit.

Two compiler attempts were queued: first a single-table target, then the full
one-lock validation batch. Neither reached a Lean compiler invocation because
other jobs held `/tmp/info-geometry-build.lock`. Only this task's own queued
processes were interrupted; no external job or lock was changed. The last
observed holder was `real-matrix-split:70`. The generated verification report
therefore remains `incomplete`, and no kernel or transitive-axiom success is
claimed. These files must be compiled and repaired as necessary before proof
acceptance or publication as verified mathematics.

Resume from the repository root, with the pinned toolchain on `PATH`, using
`python3 verification/dzhunushaliev/check.py`. It builds all six owners plus
the real derivation consumer, freshly elaborates the owners, audits every
inventoried public declaration's axioms, and reruns the static gates. The
compiler commands run serially under one invocation of the existing locking
wrapper. After any compiler repairs, request A-A rereview and a distinct QA-A
rerun of the final source. A focused package check is not a root-package or
repository-wide build.
