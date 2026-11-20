# Radon diffusion–decay: theorem contract and experimental audit

## Scope and provenance

This change extracts the mathematical content of the supplied nine-cartridge
radon draft into native Mathlib analysis and ordered matrix algebra. It also
recomputes the draft's numerical claims. Experimental assumptions, floating-point
regressions, exact rational certificates, and kernel-checked analytic statements
are separate forms of evidence.

- Intake: `data/radon_diffusion/intake_20261118.txt`, an unchanged copy of
  `Pasted text(20261118-075647).txt`.
- Intake SHA-256: `882b6799b2787041c86e07b36c7fe892ee1e7807756e05273227ac73b9411754`.
- Base: `nickgou-nuke/info-geometry-lean` main commit
  `08c34e03f610b452e03422037949196dc7d92d6d`.
- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Toolchain and dependency pins are unchanged.

The experiment date, saturation explanation, equilibrium statements, fitted
uncertainty, and measurement-order explanation in the intake are reported
claims. This change does not establish them as observations.

The subsequent leak drafts and `222Rn.md` are analyzed in
[`RADON_LEAKAGE_MODEL_AUDIT.md`](RADON_LEAKAGE_MODEL_AUDIT.md). That extension
adds general Robin and two-reservoir profiles, the restricted shifted-sinh
branch, and observation/background/handling-loss identities. Its provenance
and numerical checks are recorded separately from the original CSV audit.

## Formal owners and dependencies

| Owner under `lean/InfoGeometry/Nuclear/` | Carrier and exact contract |
|---|---|
| `RadonDiffusionProfiles.lean` | Real functions with actual first and second derivatives; exponential, sinh, and cosh profiles solve `D*C'' - lambda*C = 0` under `D*k^2 = lambda`; correctly normalized boundary values; exact uniform interval averages; common cartridge centers; exponential halving and terminal cosh shape ratio. |
| `DiffusionParameters.lean` | Storage/apparent-diffusivity identities, the square-root parameter relation, diffusivity inversion, zero-loss boundary profiles, and an actual dimensionless Dirichlet-to-linear ratio. Depends on the profile owner. |
| `DiffusionTransfer.lean` | Ordered products over an arbitrary ring, followed by real 2-by-2 concentration–flux generators and hyperbolic transfer matrices. Proves composition, inverses, determinant, generator specialization, and noncommutation for unequal squared impedances and nonzero layer factors. Includes closed generic-matrix and positive-layer witnesses. |
| `DiffusionTransferODE.lean` | Actual entrywise derivatives `T' = A*T`; the actual matrix-vector state solves the first-order equation with the prescribed initial value. Separately constructs the zero-loss shear. Depends on the transfer owner. |
| `DecayAcquisitionCorrection.lean` | Counts defined by an interval integral with constant live fraction; exact inversion, including zero loss. Reuses `DetectorBeerLambert.partialCollisionIntegral_eq`. |
| `RadonDataAudit.lean` | Exact entered count/timing vectors, rational counterexamples to exact ratios, real correction covariance, common-factor cancellation, and reference-time invariance. No statistical or calibration claim. |
| `RadonBoundaryModels.lean` | Two-reservoir endpoint values, actual Robin flux laws, general normalized Robin family, positive-flux Dirichlet counterexample, restricted shifted-sinh branch, strict tail-ratio inequality, and Dirichlet/linear flux ratio. |
| `RadonObservationArtifacts.lean` | Actual constant-offset residual, observation ambiguity, two-peak response/background mixtures, background subtraction before acquisition inversion, and conditional spatial/temporal attenuation confounding. |
| `RadonDiffusion.lean` | Focused import surface for the mathematical owners. |
| `RadonDiffusionAxiomAudit.lean` | Transitive axiom inspection for the declared owner surface. |

`SolvesDiffusionDecay` includes differentiability of both the function and its
derivative. Its residual is not applied to arbitrary nondifferentiable functions
using totalized derivatives. Parameter relations are explicit hypotheses, not
fields that assume the desired solution.

Source inspection covered existing nuclear detector integration, nuclear decay
inference, split-boost, hyperbolic rotor, and optical transfer owners, along with
their imports and relevant Mathlib declarations. All existing integral-owner
definitions, theorem statements, and proof bodies are unchanged; its broad
`Mathlib` import is replaced with focused imports and the required repository
header is added. The new concentration–flux interface is not an
identification with an optical scattering space or a completed operator algebra.
This is a bounded source-search record, not a repository-wide novelty claim.

## Model assumptions and canonical equations

Let `c` be pore-gas concentration, `S = epsilon + rho_b*K_a` the storage factor,
and `B` the coefficient defined by the bulk flux law `J = -B*c_x`. For constant
coefficients, linear local adsorption equilibrium, no advection, no distributed
source, and equal radioactive decay of retained and gaseous radon, the mass
balance is

\[
S c_t = B c_{xx} - \lambda S c,\qquad D_a=B/S.
\]

The assumptions are physical inputs. At steady state the resulting equation is
`D_a*C'' - lambda*C = 0`. If a pore diffusivity is instead defined by
`J = -epsilon*D_pore*c_x`, then `B = epsilon*D_pore`; this porosity factor must
not disappear by changing the meaning of the coefficient.

The later `222Rn.md` explicitly incorporates porosity into its `D_pore` and
changes its concentration variable to total volumetric concentration `S*c`.
With constant storage, its `J=-D_e*C_x` is consistent in that convention.
The ambiguity of the original abbreviated definition does not establish a
missing factor in this later, explicit convention.

For positive `k,L` and `k^2=lambda/D_a`, the boundary profiles are

\[
C_D(x)=C_0\frac{\sinh(k(L-x))}{\sinh(kL)},\qquad
C_N(x)=C_0\frac{\cosh(k(L-x))}{\cosh(kL)},\qquad
C_\infty(x)=C_0e^{-kx}.
\]

The proved boundary conditions are respectively `(C(0),C(L))=(C0,0)` and
`(C(0),C'(L))=(C0,0)`. The word “open” does not by itself justify a perfect-sink
boundary. A flattened measured profile does not by itself establish zero flux.

For `N` equal cartridges of width `d`, covering `[0,N*d]`, use

\[
x_i=(i-\tfrac12)d,\qquad \mu=kd,\qquad
k(L-x_i)=\mu(N+\tfrac12-i).
\]

Thus both finite-column shapes use `9.5-i` for `N=9`. The source's sinh formula
uses `10-i`, which corresponds to a different outlet registration. For uniform
response within a cartridge the actual cell average satisfies

\[
\frac1d\int_{x_i-d/2}^{x_i+d/2} C(x)\,dx
=\frac{2\sinh(kd/2)}{kd}C(x_i)
\]

for both finite-column profiles when `k,d` are nonzero. A free amplitude can
absorb this factor. Uniform detector response and homogeneous loading remain
assumptions about the experiment.

The source's `R/(10-i)` retains count-rate units. The dimensionless
Dirichlet comparison is instead the ratio to the same-inlet no-loss linear
profile:

\[
\frac{C_D(x)}{C_0(L-x)/L}
=\frac{L}{L-x}\frac{\sinh(k(L-x))}{\sinh(kL)}.
\]

The formal quotient theorem states all required nonzero conditions. Separate
zero-loss profiles are constructed; substitution into a zero denominator is
not used as a proof of a limiting profile. No convergence or arbitrary-ODE
uniqueness theorem is claimed.

## Real ordered transport

For the concentration–flux state `y=(C,J)`, assume `B != 0`, `k != 0`, and
`k^2 = lambda*S/B`. The generator and its square are

\[
A=\begin{pmatrix}0&-1/B\\-\lambda S&0\end{pmatrix},\qquad
A^2=k^2I.
\]

Writing `z=B*k`, the proved positive-attenuation propagator is

\[
T(d)=\begin{pmatrix}
\cosh(kd)&-\sinh(kd)/z\\
-z\sinh(kd)&\cosh(kd)
\end{pmatrix}
=\cosh(kd)I+\frac{\sinh(kd)}k A.
\]

The analytic owner proves `T'=A*T`, `T(0)=I`, and the state equation for
`T(d)*y0`. Composition places a subsequent layer on the left. The exact
upper-left commutator entry is

\[
(T_2T_1-T_1T_2)_{00}
=\left(\frac{z_1}{z_2}-\frac{z_2}{z_1}\right)
\sinh(k_1d_1)\sinh(k_2d_2).
\]

Nonzero factors and unequal squared impedances therefore prove
noncommutation. The generic ring theorem retains `p*q` and `q*p` separately.
There is no diagonal replacement of that noncommutative statement.

At zero loss the separate fundamental matrix is the shear

\[
T_0(d)=\begin{pmatrix}1&-d/B\\0&1\end{pmatrix}=I+dA(B,S,0).
\]

Its derivative, initial matrix, composition, and nonidentity for nonzero `B,d`
are proved. No infinite-dimensional completion, Clifford equivalence, or
matrix-exponential identification is asserted.

## Acquisition and calibration

Let `r0` be a reference **peak count rate**, including its detector response.
Under constant live fraction, the expected counts are defined by

\[
N=\frac{t_{\rm live}}{T_{\rm real}}
\int_0^{T_{\rm real}}r_0e^{-\lambda(\Delta t+s)}\,ds.
\]

For positive loss and durations the exact inverse is

\[
r_0=\frac{N}{t_{\rm live}}e^{\lambda\Delta t}
\frac{\lambda T_{\rm real}}{1-e^{-\lambda T_{\rm real}}}.
\]

The no-decay case has correction factor one and is proved separately. For a
variable live gate, the denominator is a weighted exposure integral; total
live and real times do not determine that integral. Physical use also assumes
nonnegative rate and `0 < t_live <= T_real`.

For the source's real durations and decay constant, the finite-acquisition
factor is about `1.000946` to `1.001002`. Numerical source-claim comparisons
below deliberately retain the source's start-time-only correction. The missing
factor is reported separately rather than silently applied.

Peak activity inference additionally needs efficiency, photon emission
probability, geometry, and other corrections. A nearly constant 352/609 raw
ratio does not establish daughter activities equal to each other or to radon.
Transport steady state, daughter equilibrium, and radon retention after
separation are distinct assumptions.

## Recomputed source claims

All numbers here use the entered net areas and
`R_source = (N/900)*exp(2.0982e-6*elapsed_seconds)`.

| Source claim | Recomputed finding |
|---|---|
| Ready-to-import working spreadsheet | Header is row 20 and data are rows 21–29. All 125 data formulas refer one row too early. Absolute parameter references remain unchanged. D10 and D11 contain formula-like descriptions with undefined names. |
| Strict halving over cartridges 2–8 | 609 keV adjacent ratios are `2.003703, 1.661716, 1.956344, 2.008197, 2.007898, 1.912255`. Their mean is `1.925019` and sample SD `0.134500`; these are descriptive statistics, not measurement errors. |
| Supplied cosh fit has `R²=0.9997` | For supplied amplitudes and `mu=0.686`, samples 2–9 give `R²=0.993700` at 609 keV and `0.994289` at 352 keV on the corrected-rate scale. |
| `R²` expresses more than 99.8% accuracy | `R²` is not pointwise accuracy. Maximum absolute relative residuals of the fixed cosh curves over 2–9 are about 19.24% and 19.08%. |
| Strictly constant peak ratio | For cartridges 1–8, mean `1.563038`, sample SD `0.017379`, range `1.540235–1.592551`; cartridge 9 is `1.736351`. Exact constancy is false. |
| Precomputed table exactly follows the formulas | All 18 corrected-rate entries round correctly. Across nine rows and seven calculated columns, excluding cartridge number and elapsed time, 33 of 63 entries disagree at two-decimal precision. |
| `mu=0.686 ± 0.008` is established | A fitting objective, weighting/error model, and uncertainty calculation are missing. A value near 0.686 is possible under log-rate cosh fitting; the stated uncertainty is not derived. |

The common-geometry cosh refit demonstrates objective sensitivity:

| Line | Fit range | Objective | Fitted `mu` | Corrected-rate `R²` |
|---|---|---|---:|---:|
| 609 keV | 2–9 | Unweighted squared rate residuals | 0.639205 | 0.998353 |
| 609 keV | 2–9 | Unweighted squared log-rate residuals | 0.684290 | 0.987383 |
| 352 keV | 2–9 | Unweighted squared rate residuals | 0.640832 | 0.999015 |
| 352 keV | 2–9 | Unweighted squared log-rate residuals | 0.677671 | 0.992508 |

Here the rate objective and reported `R²` use the unlogged, start-time-corrected
rates, not the uncorrected `N/900` values. Output keys containing `raw` mean the
unlogged scale in contrast with the log-rate objective.

All fits are descriptive, with a free positive amplitude. Both ranges 1–9 and
2–9 are retained in the machine-readable output. No Poisson uncertainty is
assigned to net peak areas, and no confidence interval or boundary-condition
selection is inferred. Excluding cartridge 1 repeats the source's choice;
it does not prove saturation. The source's `d=1.50 cm` is explicitly a
placeholder, so resulting dimensional diffusivities are conditional examples.

## Reproduction and validation

The numerical audit requires Python, NumPy, and SciPy:

```bash
python3 scripts/analysis/audit_radon_diffusion.py \
  data/radon_diffusion/intake_20261118.txt /tmp/radon-audit
```

The intended repository checks are:

```bash
python3 tools/infra/run_locked_lean.py \
  lean/InfoGeometry/Nuclear/RadonDiffusionAxiomAudit.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Nuclear.RadonDiffusion
```

The accompanying [validation record](RADON_DIFFUSION_DECAY_VALIDATION.md)
distinguishes exact pinned-Mathlib focused checks from root-project integration.
A successful focused check is not a
whole-repository certificate. All new declarations must pass a transitive axiom
audit permitting only `propext`, `Classical.choice`, and `Quot.sound` before
the change is described as kernel verified.

## External metrology references

These references support physical interpretation and measurement conventions;
they are not axioms of the Lean development.

1. [NIST procedure RPD-P-23, version 1.00](https://www.nist.gov/system/files/documents/2024/01/29/Procedure%2023v100.pdf),
   equation (1), printed page 7: count-to-activity conversion uses live time,
   full-energy efficiency, photon emission probability, and corrections.
2. [EPA 402-B-17-001, October 2019](https://www.epa.gov/sites/default/files/2020-07/documents/guide_for_high_resolution_gamma_spectrometry_analyses_camera_ready.pdf),
   printed pages 28–30: decay during acquisition uses real/clock time and decay
   chains require the appropriate equilibrium assumptions.
3. [IAEA-TECDOC-1712](https://www-pub.iaea.org/MTCD/Publications/PDF/TE-1712_web.pdf),
   Appendix, Table 5: radon-222 half-life and the lead-214/bismuth-214 peak energies.

## Explicit unresolved claims

No experimental transport steady state, secular equilibrium, retention model,
adsorption saturation, detector uniformity, calibrated concentration, fitted
uncertainty, or physical endpoint condition is proved by this source tree.
No arbitrary-solution uniqueness or zero-loss convergence theorem is claimed.
The exact model implications and arithmetic certificates remain useful without
promoting any of those additional statements.
