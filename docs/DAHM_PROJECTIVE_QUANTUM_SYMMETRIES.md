# Dahm: finite projective incidence and noncommuting operators

## Source and theorem contract

Source: Rolf Dahm, *Discrete and Lie Quantum Symmetries derived from Classical
Projective Geometry*, Journal of Physics: Conference Series 3152 (2025),
012008, DOI [10.1088/1742-6596/3152/1/012008](https://doi.org/10.1088/1742-6596/3152/1/012008).
Page references below use the article's printed numbering; the uploaded PDF
has an additional cover page.

The implementation starts from upstream revision
`732d97c30f292d61ea332ca9da4d1e1d8f69bd00`. Its scope is the finite operator
incidence construction in section 3, especially figure 1 on page 5, and the
two-qubit interpretation on page 7. It does not identify a real Lie group from
an unsigned incidence diagram.

### Existing owners

- `InfoGeometry.Weyl.WeylDisplacement`: `weylD_mul` proves the ordered Weyl
  multiplication law in an associative, potentially noncommutative semiring.
- `InfoGeometry.Quantum.SylvesterWeylBraidBridge`: constructs the actual clock
  and shift matrices and proves their braid relation. The new binary words
  specialize these definitions at dimension two and phase minus one.
- `Mathlib.LinearAlgebra.Matrix.Kronecker`: transports multiplication to the
  two-factor matrix representation.
- `InfoGeometry.Projective.KleinQuadricPlucker` and the
  `ExteriorPowerPluckerBridge`, `ExteriorKleinProjective`, and
  `ExteriorKleinTwoPlaneEquiv` owners already supply the classical Plücker/Klein
  geometry, including the full real decomposability converse and a two-plane
  equivalence. They are related source context, not dependencies of the new
  finite binary representation.
- `InfoGeometry.Optics.SheetWittCircularBasis` already proves orthogonality
  and completeness of joint projectors under its stated commuting-involution
  hypotheses. Its `CommutingInvolutions` structure also stores
  `projector_commute` as an input; this task does not remove that assumption.
  Primitiveness of a projector is an additional assertion.

### Exact carriers and targets

The binary label space is `(ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)`.
Write the labels as `v = ((a₁,b₁),(a₂,b₂))` and
`w = ((c₁,d₁),(c₂,d₂))`. Set

```
c(v,w) = b₁ c₁ + b₂ c₂
ω(v,w) = c(v,w) + c(w,v).
```

The coefficient ring of the matrices is independent of this label field.
For a commutative coefficient ring `R`, the operator carrier is the full
`Matrix (ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2) R`, with ordinary matrix
multiplication. Explicit noncommutativity witnesses require `CharZero R`.
The word convention is `P(v) = X^a₁ Z^b₁ ⊗ X^a₂ Z^b₂`.
The targets are the signed multiplication law, the symplectic commutation law,
the square and ordered triple-product identities, and a concrete
noncommutativity witness. The implemented exact commutation characterizations
use `CharZero R`. This is stronger than the mathematical requirement that
the characteristic differ from two, and avoids concealing an additional
typeclass assumption.

Finite lines are the sets `{v,w,v+w}` for distinct nonzero labels. The targets
include the 15-point, 35-line incidence geometry, the split into 15 isotropic
and 20 nonisotropic lines, and the theorem connecting line isotropy to actual
matrix commutation. A constructive equivalence connects the nonzero labels
to native `Projectivization (ZMod 2) Label`. The line bridge identifies each
three-point set with the nonzero part of the native span of its two
generators, and `finrank_span_pair` states that this span has dimension two.
Finite enumeration uses kernel-checked proofs; external calculations are
corroboration only.

Over a field `K` with `CharZero K`, the further targets are the trace-pairing
identity `trace(P(v)ᵀ P(w)) = 4 δ(v,w)`, a native `Module.Basis` of all sixteen
words, and equality of the span of the fifteen nonzero-label words with
`LieAlgebra.SpecialLinear.sl (ZMod 2 × ZMod 2) K`. The basis claim is not made
over arbitrary characteristic-zero rings: invertibility of two is essential
to span all matrices. This endpoint identifies the split matrix Lie algebra;
it supplies no compact or quaternionic real-form identification.

### Dependency order

Binary addition and the bilinear cocycle determine the symplectic form and
finite incidence. Independently, the existing clock/shift braid relation
determines binary Weyl multiplication. The Kronecker multiplication theorem
joins these paths in the signed two-factor product law. The commutator,
ordered line products, and commuting-line classification are consequences of
that product law. The one-factor trace pairing and Kronecker multiplication
give the full matrix basis. Its identity coefficient determines the trace,
so deleting the zero binary label gives precisely the native special linear
Lie algebra. No edge from this finite construction to a topological
completion or physical interpretation is asserted.

## Boundaries of the paper's claims

- A diagram of product labels discards a central sign. That sign is retained
  in the formal operator lift and is necessary to recover the Lie bracket.
- A real two-factor clock/shift realization does not by itself identify
  `su(4)` or `su*(4)`. Real forms, star operations, and covering maps need
  separate constructions.
- The replacement of a scalar imaginary unit by an internal operator on
  pages 3–4 requires its commutation relations. Merely assuming `J² = -1`
  does not justify the ordinary scalar sum-of-squares formula.
- The page 6 joint-projector formula requires commuting involutions.
  Idempotence and orthogonality alone do not imply primitiveness.
- The photon/Goldstone, Calabi–Yau, and quantum-computing performance
  interpretations are not consequences of the finite algebra proved here.

### Passage-by-passage disposition

| Printed location | Mathematical obligation | Disposition |
| --- | --- | --- |
| Page 3, equation (1), and page 4, section 2.4 | Plücker relation and decomposability of Klein-null bivectors. | Existing Plücker/exterior-power owners; no duplicate implementation. |
| Page 4, section 2.4, and page 8 outlook | Projective decomposable bivectors correspond to real two-planes. | Existing `realTwoPlaneEquivKleinLocus` is a set-level equivalence. A manifold structure or a covering theorem requires further work. |
| Pages 3–4, section 2.3 | Replace scalar imaginary multiplication by an internal operator. | Commutation hypotheses must be specified. The correction identity below is explanatory and is not one of the new Lean theorems. |
| Page 5, section 3 and figure 1 | Binary projective incidence lifts to signed operator multiplication. | New native projectivization/span bridges, finite incidence, cocycle, and matrix multiplication targets. |
| Page 5 Lie discussion and page 7 application | Identify the linear span and the Lie bracket of the two-factor words. | New full matrix basis and exact native special-linear span. Other real forms require their defining structures. |
| Page 6 joint-idempotent formula | Commuting involutions give orthogonal joint projectors. | Existing projector owner supplies idempotence, orthogonality, and completeness under its input record. Primitive ideals are not established by those facts alone. |
| Page 4, section 2.3 | Pass from six real coordinates to complex projective geometry and a special unitary group. | Complex projective space requires the complex-scalar quotient. A Hermitian norm supplies the unitary condition; determinant one is an additional condition. Neither transition is part of the binary construction. |
| Pages 2–3 and 7 physical interpretations | Infer photon, Goldstone, or computing behavior from geometry. | These require a physical or operational model and additional theorems. |

For an arbitrary associative ring, direct distributivity gives

```text
(a + J*b)*(a - J*b) = a^2 - (J*b)^2 + ((J*b)*a - a*(J*b)).
```

If `J^2 = -1` and `J` commutes with `a` and `b`, this simplifies to
`a^2 + b^2 + J*(b*a - a*b)`. The last commutator cannot be discarded
without another hypothesis. This is the precise reason the internal-unit
substitution is not inferred from its square alone.

For the group-level signature distinction, `SL(4,R)` corresponds to
`Spin(3,3)`, while `SU(2,2)` corresponds to `Spin(4,2)`; see
[Woit, *Euclidean Twistor Unification*, Appendix A.3.1–A.3.2](https://www.math.columbia.edu/~woit/twistorunification/euclidean-twistor-unification.pdf).
These are source clarifications, not group equivalences formalized by this
change. Likewise, the seven Fano triangles in figure 2 should be distinguished
from the bipartite Heawood incidence graph, which has no triangles.

## Public theorem map

| Source owner | Principal declarations | Coefficient assumptions |
| --- | --- | --- |
| `Projective.BinarySymplecticGeometry` | `projectivePointEquiv`, `finrank_span_pair`, `mem_line_iff_mem_span_pair`, `exists_unique_line`, `symplectic_nondegenerate`, `points_card`, `lines_card`, `commutingLines_card`, `noncommutingLines_card` | The label field is `ZMod 2`; no operator coefficient ring occurs. |
| `Quantum.BinaryWeyl` | `word_mul`, `word_trace_pair` | `CommRing R`. |
| `Quantum.BinaryWeyl` | `phase_injective`, `shift_clock_noncommute` | `CommRing R`, `CharZero R`. |
| `Quantum.TwoQubitPauliGeometry` | `pauli_mul`, `pauli_mul_self`, `pauli_mul_inverse`, `pauli_phase_commutation`, `pauli_lie`, `pauli_line_product` | `CommRing R`. |
| `Quantum.TwoQubitPauliGeometry` | `pauli_commute_iff`, `line_pairwise_commute_iff`, `first_factor_noncommute` | `CommRing R`, `CharZero R`. |
| `Quantum.TwoQubitPauliGeometry` | `commuting_operator_lines_card` | `CommRing R`, `CharZero R`, `DecidableEq R`; the last instance makes the finite operator-equality filter decidable. |
| `Quantum.TwoQubitPauliBasis` | `pauli_trace_pair`, `pauli_trace` | `CommRing R`. |
| `Quantum.TwoQubitPauliBasis` | `pauli_linearIndependent`, `pauliBasis`, `trace_zero_iff_identity_coefficient_zero`, `nonzero_pauli_span_eq_sl`, `nonzero_pauli_span_finrank` | `Field K`, `CharZero K`. |

The new files preserve the distinction between scalar commutativity and
operator commutativity. `R` is commutative so that Kronecker multiplication
has its usual factorization, but `Operator R` is the full matrix ring. The
two explicit noncommutativity witnesses are stated on the actual two-by-two
and four-by-four matrix carriers.

`Quantum.TwoQubitPauliAudit` imports the final owner and prints transitive
axiom dependencies for every public declaration added by the four owners.
The standard foundational dependencies `propext`, `Classical.choice`, and
`Quot.sound` are allowed; a placeholder or a custom postulate is not.

## Validation

Author verification passes for the five new modules and their selected import
closure, using the repository's maintained focused checker and the root pins.

- Building `InfoGeometry.Quantum.TwoQubitPauliAudit` completed successfully
  (3110 jobs), including the four source owners. The two substantial finite
  line counts are checked by the Lean kernel with `decide +kernel`.
- Fresh elaboration of the audit companion reported all 96 public
  declarations, in exact agreement with its requests. Its complete transitive
  axiom set is `propext`, `Classical.choice`, and `Quot.sound`; there are no
  proof placeholders or custom postulates in those dependencies.
- The five new files emit no compiler warnings. The build replays five
  existing warnings from `SylvesterWeylBraidBridge`: one unused section
  instance and four deprecated conditional-lemma names.
- The strict screener, strict refuter, static Gate 4 review, and error-level
  semantic-vacuity gate pass. Eleven normalization/API helper warnings remain
  in the vacuity report, within the source reviewer's accepted helper set.
  These lexical checks are separate from native compilation and axiom checks.
- A root Lake build of the five changed targets stops before target
  compilation because `external_refs/homotopy-hypothesis-lean4` is missing.
  Separately, `python3 tools/infra/ci_bootstrap.py paths` exits 1 at the stated
  base: `HomotopyHypothesis` and `Atlas` lack tracked source/configuration,
  and the pinned `GIFT` gitlink is uninitialized. The local push gate and CI
  provenance preflight are distinct checks. No dependency pin or root Lake
  configuration was changed.

The maintained focused checker uses Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, matching the root pins.
The author checks ran within one maintained `check.py env` lock. Equivalent
reproducible invocations are:

```sh
python3 verification/language-symmetry/check.py build InfoGeometry.Quantum.TwoQubitPauliAudit
python3 verification/language-symmetry/check.py env lean /absolute/repository/lean/InfoGeometry/Quantum/TwoQubitPauliAudit.lean
```

The PR verification record must also include a separate nonauthor QA receipt
for the frozen source hashes and the result of the unchanged publication gate
on the proposed commit. Focused verification certifies the selected source
closure; it does not certify unrelated root path packages or default targets.
