# Zeta, Weil–Krein and finite Stokes theorem contract

Base revision: `fe24e350b08fdea04f74c0748ef9fd9417c47529` (observed upstream main on 2026-11-23).
Toolchain: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Intake and provenance

Both supplied texts are preserved verbatim in `docs/intake/zeta-weil-krein-stokes-20261123/`, with SHA-256 digests. They are proposals, not verification evidence. This contract also covers the accompanying request about five-axiom GRH symmetries.

## Grounded owner search

Repository-owned searches covered `lean/` and `src/`, followed by definitions, imports and consumers in arithmetic, Krein, canonical geometry and operator algebra. Mathlib sources were inspected at the pinned revision. No external graph service or complete whole-repository build is asserted.

| Intake reference | Source-grounded owner and actual scope |
|---|---|
| `ZetaDihedral.lean:210`, `vonMangoldt_log_der` | The current ZetaDihedral file has fewer than 210 lines and owns commuting functional/conjugation reflections and the antiunitary critical fixed locus. The named declaration was not found in the bounded `lean/`/`src/` search. |
| von Mangoldt logarithmic derivative | `Arithmetic/ActualRiemannZetaVonMangoldtBridge.lean` reuses native Mathlib to prove the actual zeta identity for `1 < s.re`, with the negative-logarithmic-derivative convention. Native `DirichletCharacter.LSeries_twist_vonMangoldt_eq` supplies the character version. |
| `logSoldering` / `RingDeriv` | No `logSoldering` declaration found in the bounded search. The custom `RingDeriv` in NoncommutativePeierlsBerryKitaevSynthesis has only a Leibniz field. New finite Euler results use native `Derivation k R R`, including additivity. |
| Mellin scale derivative and residues | `Arithmetic/ZetaEulerLaurentMonodromy.lean` owns `deriv_expPullback_eq_eulerDerivative`, simple-zero residue signs, and a pole regularization identity. |
| Canonical Hilbertization | `Omega/Conclusion/AnomalyQuotientCanonicalHilbertization.lean` projects finite subset coefficients and rewrites a sum of squares; it does not construct the Weil form or its quotient. `GrandAnomalyOntology.descendSymmetricPairing` is a general Setoid quotient descent, not a completed Hilbert space. |
| Real null pairing | `Krein/Metric.hessian_indefinite_formCoord` owns the coordinate cross-pairing; `Krein/DoubledSpace` and HilbertBridge own real doubled carriers and their rotations. |
| Supertrace | `OperatorAlgebra/FiniteParitySupertrace.lean` owns the real parity matrix, oddness and graded cyclicity. SpinorialCore/FiniteSupertrace already handles rectangular block partners; these APIs are not duplicated. |
| Discrete Stokes | DiscreteStokesFinite, RealStokesGaussHomology and DiscreteSplitOctonionStokes own triangle, finite-support and cellular variants. The new rectangular identity has arbitrary additive coefficients. |
| Rotor derivatives / pure gauge | CartanHestenesRotorSpinConnectionMaurerCartanSynthesis and ReflexiveRotorRealTime already prove rotor derivatives. `MaurerCartanTower.thetaL_flat` proves pure-gauge curvature zero. |

## Intended accepted statements and carriers

1. Native module endomorphisms: `J*J=1` and `J*D*J=-D` imply anticommutation and transport nonzero eigenvectors from eigenvalue `w` to `-w`. A real two-dimensional counterexample has eigenvalue `1` and these same reflection laws.
2. Real spectral coordinates: `(-sigma,height)=(sigma,height)` iff `sigma=0`. This differs from simultaneous sign reversal.
3. Native `Derivation k R R` on a commutative algebra and units: logarithmic velocity is additive on finite products; its negative on `E^-1=1-a`, `D a=-ell*a` equals `ell*E*a`. Finite prime-power expansion keeps `ell*E*a^(M+1)`. The geometric telescoping sublemma works in any ring.
4. Real inner-product evaluation blocks: diagonal and antidiagonal cross-pairings have opposite strict signs for a nonzero vector. A surjective evaluation map transfers the negative direction; surjectivity is an explicit hypothesis, not a theorem about Weil test functions.
5. Native real bilinear forms and `V / ker B`: descend the symmetric form using Mathlib quotient maps, prove positive definiteness from semidefiniteness, and construct an inner-product core. Negative directions cannot be removed by taking the radical quotient. Completeness is separate.
6. Real finite matrices: positive powers of a parity-odd matrix have zero supertrace; a finite polynomial contributes only its constant term.
7. Finite incidence data and arbitrary additive cell cochains: curvature sum is the alternating cardinality count under explicit incidence hypotheses; rectangular Stokes cancels internal edges, and exact edge differences have zero cell circulation.

## Dependency order of the extracted patterns

| Pattern in the intake | Mathematical prerequisites | Consequence supplied here |
|---|---|---|
| Mirror / paired sectors | Involutive native endomorphism and the generator-reversal identity | Nonzero eigenvector transport and an explicit counterexample to a stronger spectral conclusion |
| Multiplicative motion / logarithmic velocity | Native derivation, commuting units, and specified Euler factors | Additive logarithmic derivatives, with signed finite prime-power expansion and exact remainder |
| Null directions / opposite signs | Existing real cross-pairing on two evaluation coordinates | Isotropic coordinate sheets and positive/negative diagonal directions |
| Detecting a negative test value | Surjective evaluation, or a realized antidiagonal block with a strict remainder bound | Failure of nonnegativity for the specified pulled-back form |
| Removing null vectors | Symmetric bilinear form; positive semidefiniteness for a positive core | Native radical quotient preserving all self-pairings, followed conditionally by an inner-product core |
| Boundary cancellation | Additive grid cochains or explicit incidence totals | Finite Stokes and incidence-curvature identities |
| Graded cancellation | A finite real matrix anticommuting with its parity operator | Vanishing positive-power supertraces and a constant-term polynomial identity |

The mirror and logarithmic-derivative branches are independent algebraic inputs. They are connected to a global Weil argument only after an explicit formula and a suitable analytic evaluation construction are supplied. The quotient branch consumes positivity; it does not produce that missing analytic input. Boundary and grading identities are separate finite branches unless an explicit compatibility map is constructed.

## Claims corrected or left outside the theorems

- Open half-planes are not vector subspaces. A spectral subspace construction is additional data.
- Reflection symmetry does not force critical-line support. The Clifford identification additionally requires the generator square laws; a derivative is not automatically a Clifford unit.
- `w -> -w` and `w -> -conj(w)` are distinct; only the latter fixes the shifted critical line.
- A complex Hermitian (1,1) block has real signature (2,2). Scalar real (1,1) blocks and realified complex blocks are distinct.
- The actual infinite Weil criterion needs an admissible test space, Mellin evaluations, convergence, zero multiplicities, interpolation and control of the remaining zero sum. Local indefinite-block algebra does not discharge these.
- `g^-1 (partial_s g)=g'/g`; the positive von Mangoldt expansion uses its negative. The operator `partial_s` is not `x partial_x`.
- A PSD radical quotient is an inner-product space; a Hilbert space additionally needs completeness or completion.
- A finite incidence count is not a surface-realization theorem. A finite polynomial is not an analytic heat kernel.
- A pure gauge `g^-1 dg` is flat. A curved Levi-Civita connection requires an independent connection and its transformation law. The diagonal boost preserves the off-diagonal null metric, not its diagonal generator.
- No result in this change identifies the formalized core with GRH or imports/validates an external announced proof.

## External evidence

Connes–Consani, *Weil positivity and trace formula, the archimedean place*, Appendix C: https://alainconnes.org/wp-content/uploads/Selecta.pdf . This specifies the interpolation and tail-control step in the positivity criterion. The current Hexagon item https://hexagonmath.org/2611.00789v1 is a separate finite-field proposal with substantial cohomological hypotheses; it is not imported as Lean authority.

## Verification

Implementation is present. Scoped staged proof checks and the strict OpenGauss source refutation screen pass. The semantic-vacuity screen reports four low-level computation/representation warnings: `coordinate_sheets_isotropic`, `quotientForm_mk`, `innerProductCore_inner_mk`, and the existing `supertrace_eq_sum_sign_mul_diagonal`. These identify elementary evaluation lemmas, not an assumed arithmetic positivity result.

Serial compilation and the declaration-axiom audit are pending behind the shared build lock. The focused verification project preserves all nine relevant dependency pins and the root toolchain. It imports seventeen repository modules, including every changed owner and the actual arithmetic owners used in the audit. No whole-repository certificate is inferred.

On the requested publication retry, a fresh focused build attempt exited with code 2 because the shared build lock was occupied by `real-matrix-split`. The draft publication therefore retains pending compiler and root-gate status. The added focused CI workflow runs the exact PR head, checks the pins, compiles with warnings treated as errors, captures fresh axiom output, and enforces the 46-declaration allow-list. Its presence is not evidence that it has passed.

## Compatibility

The supertrace extension strengthens the two `odd_mul_*Projector` lemmas by removing their unused grading-normalization argument. Four local callers were updated. The unused `supertrace_mul_comm_of_odd_odd` alias was removed; its conclusion is supplied by `supertrace_mul_comm_of_odd_left`, requiring only oddness of the left factor. A tracked `lean/` and `src/` consumer search found no additional consumers of the modified owner API. External callers of these signatures would need the same argument adjustment. The independent `src/` owner remains outside this change.
