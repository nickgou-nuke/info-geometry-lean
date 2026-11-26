# Bessel–Hagen: divergence symmetries and real conformal currents

## Source and theorem contract

Source: E. Bessel-Hagen, *Über die Erhaltungssätze der Elektrodynamik*
(1921), supplied English translation, §§1, 4–7, especially equations
(5)–(7), (17)–(24), PDF pages 4–5 and 13–19.

Baseline: `fe24e350b08fdea04f74c0748ef9fd9417c47529`.

At the baseline, the existing real Maxwell tensor is owned by
`Conformal/MannheimOpenDebtConstructiveClosure.lean`; its symmetry and
signature-contracted trace zero are already proved. The present change
extracts that algebra into a focused owner and adds the missing differential
contraction argument. NoetherInference and the CAR current hierarchy describe
different constructions and are not substituted for field-theoretic currents.

The differential carrier is a commutative real algebra `A` with native Mathlib
`Derivation ℝ A A`. Derivations act on algebra elements, not pointwise real
numbers masquerading as functions. Coordinate formulas use explicit elements
`x i : A` with `D i (x j) = δᵢⱼ`. Native multivariate polynomials realize these
coordinate rules below; general smooth-function and manifold realizations are
outside the current contract.

Acceptance statements:

1. Construct the first-order integration-by-parts identity from the Leibniz
   rule, with supplied variational coefficients, and prove that divergence
   symmetry plus Euler–Lagrange equations imply conservation of the corrected
   current.
2. Prove antisymmetric superpotential improvements have zero double divergence
   when the derivations commute.
3. Prove the symmetric/skew contraction and the exact identity
   `div(S ξ) = (div S)·ξ + σ tr_g S` for symmetric contravariant `S` and a
   conformal Killing covector `ξ`.
4. Construct translation, antisymmetric linear, dilation and special-conformal
   covectors in a real diagonal metric and verify their conformal factors.
5. Instantiate the contraction theorem with the existing Maxwell tensor,
   raising both indices explicitly.
6. Derive stress conservation from the vacuum Maxwell equation, field
   antisymmetry, Bianchi identity and constant metric. For a potential, derive
   antisymmetry, Bianchi and gauge invariance from commuting derivations.
   Combine these results to obtain conformal-current conservation directly
   from the potential's vacuum Maxwell equation.

## Mathematical content

Write `q = algebraMap ℝ A (1/4)`, `gᵢⱼ = εᵢ δᵢⱼ`, with `εᵢ² = 1`.
For the covariant field strength and stress tensor,

```text
Fᵢⱼ = Dᵢ Aⱼ − Dⱼ Aᵢ
F² = Σᵢⱼ εᵢ εⱼ Fᵢⱼ²
Tᵢⱼ = Σₖ εₖ Fᵢₖ Fⱼₖ − q gᵢⱼ F²
Sⁱʲ = εᵢ εⱼ Tᵢⱼ
Jⁱ = Σⱼ Sⁱʲ ξⱼ
```

The coefficient-algebra Maxwell owner proves the general dimension identity
`Σᵢ εᵢ Tᵢᵢ = (1 − q·card ι) F²`. Its vanishing at `card ι = 4`
does not require field equations. A null field can also have zero trace in
other dimensions, so no dimension characterization for an individual null
field is asserted.

The differential argument proves that Bianchi and the vacuum Maxwell equation

```text
Dᵢ Fⱼₖ + Dⱼ Fₖᵢ + Dₖ Fᵢⱼ = 0
Σᵢ εᵢ Dᵢ Fᵢⱼ = 0
```

imply `Σᵢ Dᵢ Sⁱʲ = 0`. Contracting Bianchi with the field gives the precise
one-quarter gradient cancellation needed in the stress divergence. This
conservation argument works in every finite dimension. Four dimensions enter
only when the metric trace is removed from the conformal-current identity.

For a conformal Killing covector,
`Dᵢ ξⱼ + Dⱼ ξᵢ = 2 σ gᵢⱼ`, the exact identity is

```text
div J = Σⱼ (div S)ʲ ξⱼ + σ Σᵢⱼ Sⁱʲ gᵢⱼ.
```

The symmetric/skew split is explicit: contraction of symmetric `S` with the
skew part of `Dξ` is zero. The generator module verifies the factors

| Covector family | Formula | Conformal factor |
|---|---|---|
| Translation | constant covector | `0` |
| Lowered Lorentz generator | `Kⱼₖ xᵏ`, with constant antisymmetric `K` | `0` |
| Dilation | `εⱼ xʲ` | `1` |
| Special conformal | `2 g(b,x) εⱼ xʲ − g(x,x) εⱼ bʲ` | `2 g(b,x)` |

These are the four families behind the paper's `4 + 6 + 1 + 4` parameters in
four dimensions. Linear independence and completeness of that parameterization
are not proved here.

The coordinate hypotheses are realized by `MvPolynomial ι ℝ` with native
`MvPolynomial.pderiv`. An additional constant-field polynomial theorem proves
stress conservation directly and instantiates the special-conformal current
without an assumed stress-divergence premise.

## Source owners and compatibility

| Owner | Role |
|---|---|
| `Canonical/BesselHagenNoether.lean` | Constructed integration-by-parts identity, boundary correction and antisymmetric superpotentials |
| `Conformal/MaxwellStressTensor.lean` | Existing real tensor generalized to a real coefficient algebra; dimension-dependent trace; index raising; preserved legacy names |
| `Conformal/BesselHagenCurrent.lean` | Symmetric/skew contraction, conformal trace source and gauge-compensated characteristic |
| `Conformal/BesselHagenGenerators.lean` | Four explicit generator families, trace balance laws and actual polynomial realizations |
| `Conformal/MaxwellStressConservation.lean` | Stress conservation derived from Maxwell and Bianchi |
| `Conformal/BesselHagenMaxwell.lean` | Potential, gauge invariance, constructed Bianchi and the combined conformal-current theorem |

The names `MannheimOpenDebtConstructiveClosure.maxwellStressTensor4` and
`maxwellStressTensor4_symm_and_trace_zero` are preserved in the focused tensor
owner. The old Mannheim module imports that owner and removes the duplicated
definitions. At real coefficients the component formula is unchanged. The
separate `src/` source lane is untouched.

## Scope boundaries

The coefficient algebra is commutative, as in classical abelian
electromagnetism. This is not a theorem about the repository's noncommutative
Zorn/Yang–Mills carrier. No complex unit or imaginary time coordinate occurs
in the new constructions. Arbitrary diagonal signatures are retained.

The variational coefficients are not constructed by differentiating a general
Lagrangian. The algebraic first-variation theorem and the Maxwell stress-current
theorem have not yet been connected by a theorem identifying the corrected
Noether current for the differentiated Maxwell Lagrangian with `stressCurrent`.
The gauge-compensated characteristic is proved separately.

The local current identities do not construct integrated charges, a global
conformal-group action, or a classification of all conformal Killing fields.
Matter with nonzero total stress trace gives the exact dilation source `tr_g S`
and special-conformal source `2 g(b,x) tr_g S`. The source may vanish where its
conformal factor vanishes; no everywhere-nonzero assertion is made.

## Validation

Validated on 2026-11-26 with the repository's unchanged pins:

- Lean `v4.34.1`.
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Exact repository-source import closure: the six focused modules above.

The maintained source-closure checker passed compilation with **zero warnings
in every module** and a native audit of every declaration owned by those modules,
including generated/private declarations and the legacy compatibility names.
The audit found only `propext`, `Classical.choice`, and `Quot.sound`.

| Module | Audited declarations |
|---|---:|
| `Canonical.BesselHagenNoether` | 18 |
| `Conformal.MaxwellStressTensor` | 20 |
| `Conformal.BesselHagenCurrent` | 21 |
| `Conformal.BesselHagenGenerators` | 29 |
| `Conformal.MaxwellStressConservation` | 8 |
| `Conformal.BesselHagenMaxwell` | 10 |
| **Total** | **106** |

The exact successful author command, run from the checkout root, was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/012eca46cbbe/tmp/mathlib \
  --lean /home/agent/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  --output /workspace/scratch/9401d24a3608/verification \
  --target InfoGeometry.Canonical.BesselHagenNoether \
  --target InfoGeometry.Conformal.MaxwellStressTensor \
  --target InfoGeometry.Conformal.BesselHagenCurrent \
  --target InfoGeometry.Conformal.BesselHagenGenerators \
  --target InfoGeometry.Conformal.MaxwellStressConservation \
  --target InfoGeometry.Conformal.BesselHagenMaxwell \
  --incremental
```

Despite its historical filename, the maintained checker accepts explicit target
modules. It validates the exact pinned environment, hashes the copied repository
source closure, serializes compilation through the shared build lock, audits all
owned declarations, and checks that the source and verification implementation
remain unchanged. Its built-in warning rejection is specific to the original
Clifford prefix; the zero-warning result for all six modules was therefore also
checked explicitly in the resulting report.

Independent A-A source review passed the final mathematical statements,
implementation, compatibility refactor, and scope boundaries. A separate QA-A
agent reran the same six-target command with output
`/workspace/scratch/9401d24a3608/qa-verification` and **without `--incremental`**.
Every module was freshly compiled (`reused = false`), with zero warnings; the
independent audit again covered all 106 declarations with only the three allowed
foundational axioms. QA also reran all static gates below and verified that the
six owners, legacy refactor, documentation, Git index and baseline remained
unchanged throughout the run.

The independent disposition is **`ACCEPTED_WITH_LIMITED_SCOPE`**: the exact six
focused modules and their owned declarations, including both moved legacy
Maxwell names. The build and mathematical boundaries below remain explicit.

### Static gates

Each command below was run on all six focused owner paths (the proof proxy gate
uses the staged diff):

```bash
python3 tools/infra/opengauss_screener.py <six-owner-paths> --strict
python3 tools/infra/opengauss_cli.py refute <six-owner-paths> --strict
python3 tools/infra/opengauss_cli.py review <six-owner-paths> --gate GATE_4
python3 tools/quality/proof_proxy_staged_gate.py
python3 tools/quality/semantic_vacuity_gate.py <six-owner-paths> --fail-on warning
```

- OpenGauss screening and strict refutation: pass, zero traps.
- Gate 4: `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED` for all six modules. This is
  static-review evidence; the separate compilation and axiom audit supply the
  kernel evidence.
- Staged proof proxy and `git diff --check`: pass.
- Semantic-vacuity scanner: **four lexical `trivial_surface` warnings, no errors**;
  exit 1 under `--fail-on warning`. The warnings concern `divergence_add`,
  `divergence_sub`, `deriv_parameterPairing`, and `abelianFieldStrength_skew`.
  Independent review accepted each as a meaningful elementary helper with no
  assumed conclusion. The raw strict scanner result is not a clean pass.

### Build coverage limit

The ordinary repository Lake check failed before theorem elaboration because
`external_refs/homotopy-hypothesis-lean4` was absent (`HomotopyHypothesis` package
directory not found). Source-closure inspection of the heavy Mannheim consumer
also found an unresolved `Architect` dependency. No dependency or toolchain pins
were changed to bypass these obstacles.

The focused check compiles the actual moved Maxwell compatibility declarations
inside `MaxwellStressTensor.lean`, but does not compile the complete historical
Mannheim dependency graph. Consequently this is a six-module source-closure
certificate, not a whole-repository build or a claim that every legacy consumer
has been rebuilt.
