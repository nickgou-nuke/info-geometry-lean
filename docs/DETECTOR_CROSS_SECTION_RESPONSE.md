# VPD receiving area and quadratic response

Status: `[kernel_verified]` and `[accepted_limited_scope]` for the selected real
scalar source closure; the physical model remains `[bucket_2_conditional]`.
Source context: base `fe24e350b08fdea04f74c0748ef9fd9417c47529` plus the four
integrated owners/audits below. This is not a full root Lake build certificate.

## Intake and mathematical contract

Intake provenance: the user's VPD discussion and clarification in the active
conversation, followed by the request to compile it into the current codebase.
The receiving-area clarification states: “it is a way to model the detector
efficiency by a crossection”; the preceding request describes “loosing singles
into coincident doubles”. These motivate the two separate model parameters below.

The user's request connects a cross section situated at the virtual point detector
(VPD) to singles registration, its fitted slope, and diversion into coincidences.
The clarification puts **effective receiving area** first: it is the first-order
response scale; conditional transfer area controls the second-order correction.
The informal scattering analogy supplies a model interpretation, not a microscopic law.

Carrier: `ℝ`, with ordinary commutative arithmetic, `Real.pi`, and `Real.sqrt`.
For one photon line, let $Q_\gamma=Ap$ be the emitted photon rate, where $A$
is activity and $p$ is photon yield per decay. For isotropic point emission,
take the source-to-VPD distance to be $\rho=d+r_0>0$:

$$
\phi_\gamma(\rho)=\frac{Q_\gamma}{4\pi\rho^2},\qquad
R_0=\phi_\gamma\Sigma,\qquad
\epsilon_0=\frac{R_0}{Q_\gamma}=\frac{\Sigma}{4\pi\rho^2}.
$$

Here $\Sigma$ is the summing-free full-energy-peak receiving area.
The dilution sphere $4\pi\rho^2$ is centered on the **source**; the effective
receiving cross section is assigned to the **VPD**. No literal detector-centered
sphere, material surface, or geometric aperture is constructed by these owners.
The pointwise definition $\Sigma(d)=4\pi\rho(d)^2\epsilon_0(d)$ is algebraic;
constancy across distance assumes an inverse-square model for the extended detector.
For a physical receiving efficiency in $[0,1]$, also require
$0\le\Sigma\le4\pi\rho^2$ over the chosen distance range;
`spherical_loss_probability_bounds` applies to this same ratio with area $\Sigma$.

## Slope dictionary and normalization

Assume positive responses and the positive branch of each reciprocal square root.
The affine value must be positive; a physical interpretation also uses positive
slopes and $\rho>0$. The following slopes belong to different observables:

| Observable and affine relation | VPD offset | Receiving area |
|---|---|---|
| Absolute efficiency: $\epsilon_0^{-1/2}=m_\epsilon d+c_\epsilon$ | $r_0=c_\epsilon/m_\epsilon$ | $\Sigma=4\pi/m_\epsilon^2$ |
| Normalized transfer: $x=\epsilon_0/\epsilon_{\rm ref}$, $x^{-1/2}=\alpha+\beta d$ | $r_0=\alpha/\beta$ | $\Sigma=4\pi\epsilon_{\rm ref}/\beta^2$ |
| Corrected count rate: $R_0^{-1/2}=m_R(d+r_0)$ | From the rate intercept divided by $m_R$ | $\Sigma=4\pi/(Ap\,m_R^2)$ |

Normalized data alone do not fix the absolute area: $\epsilon_{\rm ref}$ is required.
Count-rate slopes retain the emitted photon rate $Ap$. In the common exact model,

$$
L=\frac1{\beta^2},\quad x=\frac L{\rho^2},\quad
\Sigma=4\pi\epsilon_{\rm ref}L,\quad
\beta=\sqrt{\epsilon_{\rm ref}}\,m_\epsilon,\quad
m_R=\frac{m_\epsilon}{\sqrt{Ap}}.
$$

For the manuscript gauge $G=\alpha^{-2}$, $r_0=\alpha/\beta$, with nonzero
$\alpha,\beta$, $L=Gr_0^2$. Retain $G$: setting it to one changes the area.
The conversion is exact for the supplied predictor, even when it approximates the data.
For $\beta$ in mm$^{-1}$, $\Sigma[\mathrm{cm}^2]=4\pi\epsilon_{\rm ref}/(100\beta_{\rm mm}^2)$.

## Two areas and the second-order coefficient

Write $u=(4\pi\rho^2)^{-1}$. For a chosen baseline receiving area $\Sigma_B$
and a signed conditional transfer area $\sigma$, the algebraic factorization is

$$
\epsilon_B=\Sigma_Bu,\qquad
\epsilon_{\rm model}=\Sigma_Bu(1-\sigma u)
=\Sigma_Bu-\Sigma_B\sigma u^2.
$$

Thus the first coefficient is an area and the second is a product of two areas.
For normalized $y=\epsilon_{\rm obs}/\epsilon_{\rm ref}=ax+bx^2$, choose

$$
\Sigma_B=a\Sigma,\qquad
\sigma_{\rm fit}=-\frac ba\frac{\Sigma}{\epsilon_{\rm ref}}
=-4\pi L\frac ba,\qquad a\ne0.
$$

Then $\epsilon_{\rm obs}=a\Sigma u+(b\Sigma^2/\epsilon_{\rm ref})u^2$.
The summing-free receiving area is $\Sigma$; the fitted observed first-order
area is $a\Sigma$. The response coefficient $a$ is distinct from the geometric
slope $\beta$. Neither dimensionless $b$ nor $b/a$ is itself an area.
For $L\ge0,a>0,b\le0$, the inferred fitted-baseline area is nonnegative;
positive $b$ instead gives a signed gain correction.

A probability interpretation additionally requires $0\le\sigma\le4\pi\rho^2$.
Multiplying a primary rate by this conditional factor gives
$Q_\gamma\Sigma_B\sigma/((4\pi)^2\rho^4)$.
The event-partition identities partition modeled primary events; they do not
derive the multiplicity of singles lost per recorded double or a coincidence window.

## Physical baseline and residuals

The constant $\sigma_{\rm fit}$ is inferred relative to the fitted baseline $ax$.
Relative to the physical free baseline $x$, define the signed fractional-deficit area

$$
\sigma_{\rm phys}=4\pi\rho^2(1-y/x)
=4\pi(1-a)\rho^2-4\pi bL.
$$

In the exact quadratic model, $a=1$ removes the distance-dependent defect.
Conversely, equality of this physical-baseline area at two nonzero distances
with different squares forces $a=1$, assuming $L\ne0$.
If actual normalized response is $y=ax+bx^2+\eta$, then

$$
\sigma_{\rm phys}
=a\sigma_{\rm fit}+4\pi(1-a)\rho^2-\frac{4\pi\rho^2\eta}{x}.
$$

For an explicit positive baseline $B$, a supplied bound $|\eta|\le\delta$
gives $|\Delta\sigma|\le4\pi\rho^2\delta/B$. With $B=x=L/\rho^2$, the
amplification is $4\pi\rho^4/L$. This is deterministic propagation of a response
residual; it is not a fitted uncertainty, confidence interval, or geometric-fit error bound.

## Owner reuse and declaration map

Canonical files are in `lean/InfoGeometry/Probability/`:
[Response](../lean/InfoGeometry/Probability/DetectorCrossSectionResponse.lean),
[Response audit](../lean/InfoGeometry/Probability/DetectorCrossSectionResponseAudit.lean),
[Receiving area](../lean/InfoGeometry/Probability/DetectorReceivingArea.lean), and
[Receiving audit](../lean/InfoGeometry/Probability/DetectorReceivingAreaAudit.lean).
Below, `R` abbreviates `InfoGeometry.Probability.DetectorCrossSectionDuality.Response`
and `A` abbreviates `InfoGeometry.Probability.DetectorCrossSectionDuality.ReceivingArea`.

Reuse is explicit: [DetectorCrossSectionDuality](../lean/InfoGeometry/Probability/DetectorCrossSectionDuality.lean)
owns `singlesResponse`, `linearizer`, `photopeakArea`, and `virtualSummingArea`;
[ApollonianBipolarField](../lean/InfoGeometry/Nuclear/ApollonianBipolarField.lean)
owns `geometricCoupling` and `effectiveArea`. The receiving module adds no definitions.
`R` adds only `transfer L ρ = L/ρ²`, `inferredCrossSection L a b = -4πLb/a`,
and `crossSectionFromDeficit ρ B y = 4πρ²(1-y/B)`.

| Receiving theorem in `A` | Exact scope / hypotheses |
|---|---|
| `receiving_area_of_normalized_transfer` | Supplied coupling/reference equals transfer; reference and distance nonzero. |
| `inverse_sqrt_eq_iff_inverse_square` | Equivalence for positive efficiency and positive affine value. |
| `receiving_area_of_affine_efficiency_linearizer` | Positive area, nonzero slope, positive affine value, supplied exact square-root relation. |
| `receiving_area_of_normalized_affine_transfer` | Nonzero reference, slope, shifted distance; supplied normalized inverse-square equality. |
| `receiving_area_of_count_rate_linearizer` | Area, activity, yield, slope, distance positive; supplied exact rate linearizer. |
| `inferred_loss_area_from_receiving_area` | Supplied $\Sigma=4\pi\epsilon_{\rm ref}L$, nonzero reference; fitted-baseline interpretation also uses $a\ne0$. |
| `two_area_efficiency_factorization` | Scalar identity from the existing coupling and singles-response definitions. |

| Response theorem(s) in `R` | Exact scope / hypotheses |
|---|---|
| `response_factorization` | Exact quadratic factorization; distance and $a$ nonzero. |
| `recover_fitted_cross_section` | Recovery from fitted baseline; $L,\rho,a\ne0$. |
| `inferred_cross_section_nonneg`, `inferred_cross_section_pos` | Nonnegative/positive $L$, positive $a$, nonpositive/negative $b$. |
| `inferred_cross_section_nonpos_of_gain` | $L\ge0,a>0,b\ge0$. |
| `physical_baseline_defect`, `unit_slope_physical_cross_section` | Physical-baseline identities; $L,\rho\ne0$. |
| `constant_physical_area_forces_unit_slope` | Equal areas, $L\ne0$, nonzero distances with unequal squares. |
| `gauge_conversion`, `affine_cross_section_conversion` | Algebraic substitutions of $Gr_0^2$ and $1/\beta^2$. |
| `affine_transfer_conversion` | Affine predictor equals shifted inverse-square transfer; $\beta\ne0$. |
| `sum_proxy_conversion`, `sum_proxy_linearizer_conversion` | Substitutions for $cX-kX^2$, with $X=H/\rho^2$. |
| `inferred_cross_section_eq_virtual_summing_area` | Equality with the existing `virtualSummingArea` convention. |
| `event_partition_conservation`, `event_partition_nonneg` | Arithmetic partition; nonnegative baseline and $p\in[0,1]$ for signs. |
| `spherical_loss_probability_bounds` | Nonzero distance and $0\le\sigma\le4\pi\rho^2$. |
| `pair_rate_inverse_fourth` | Product of inverse-square factors; distance nonzero. |
| `cross_section_residual_difference` | Exact signed response-residual identity for an explicit baseline. |
| `physical_baseline_with_residual` | Physical-baseline defect plus residual; $L,\rho\ne0$. |
| `physical_baseline_inferred_with_residual` | Conversion from fitted area; additionally $a\ne0$. |
| `cross_section_residual_error_bound` | Positive baseline and supplied absolute residual bound. |

## Actual source-level dependency order

These are direct local theorem uses in the kernel-checked proof bodies.
This table records proof dependencies, not physical causation or an exported declaration DAG.

| Downstream declaration | Direct local theorem prerequisites |
|---|---|
| `R.unit_slope_physical_cross_section`, `R.constant_physical_area_forces_unit_slope` | `R.physical_baseline_defect` |
| `R.inferred_cross_section_eq_virtual_summing_area` | `R.sum_proxy_linearizer_conversion` |
| `R.physical_baseline_with_residual` | `R.cross_section_residual_difference`, `R.physical_baseline_defect` |
| `R.physical_baseline_inferred_with_residual` | `R.physical_baseline_with_residual` |
| `R.cross_section_residual_error_bound` | `R.cross_section_residual_difference` |
| `A.receiving_area_of_affine_efficiency_linearizer` | `A.inverse_sqrt_eq_iff_inverse_square`, `A.receiving_area_of_normalized_transfer`, `R.affine_transfer_conversion` |
| `A.receiving_area_of_normalized_affine_transfer` | `A.receiving_area_of_normalized_transfer`, `R.affine_transfer_conversion` |
| `A.receiving_area_of_count_rate_linearizer` | `A.receiving_area_of_affine_efficiency_linearizer` |

Other theorems use definitions and imported Mathlib facts directly.
The receiving-to-loss conversion assumes its area identity; the two-area factorization unfolds definitions.

## Boundaries and verification record

`[bucket_3_open_debt]`: identifying a constant area from data, absolute calibration,
finite-crystal transport, anisotropic emission, angular/cascade response, separation
of summing-in from summing-out, and statistical uncertainty are outside these proofs.
Area need not equal the physical frontal area. All units are external to `ℝ`;
Lean's totalized division makes some identities valid even at zero denominators,
which does not give those cases a physical efficiency or cross-section meaning.

The completed native run checked four targets and seven repository source modules:
22 response theorems plus three definitions, seven receiving theorems, and their
audits. All 32 executed axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. The proof sources contain no placeholders, custom axioms,
`native_decide`, unsafe proof bypasses, or vacuous `True` wrappers.

Independent source and mathematical-contract reviews passed. The actual unchanged
pre-commit hook also passed. The complete run used a task-local serialization
driver that calls the maintained checker's unchanged `verify` function under its
shared build lock, then runs the ordinary Git commit hook before releasing that
lock. A separate read-only review confirmed the same entrypoint guards and pins.
No verification implementation, dependency pin, or hook was changed.

Two reused owners, `DetectorCrossSectionDuality` and `ApollonianBipolarField`,
emit the existing `Mathlib.Data.Real.Basic` import-deprecation warning. The new
owners and audits compiled without additional warnings; the closure was not
checked with warnings treated as errors. Exact source hashes, axiom classification,
and the native verifier report are retained with the delivery record.

Pinned environment: Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`,
LeanArchitect `54d3fb249685db8e5a564e0b3f331cff77991607`. Set `VPD_LEAN` to the
native compiler, `VPD_MATHLIB` and `VPD_ARCHITECT` to clean checkouts at these pins,
and `VPD_OUTPUT` to a task-owned output directory. The equivalent standalone
reproduction command, from the independent repository root, is:

```bash
python3 tools/infra/check_plucker_infinity_modular.py \
  --lean "${VPD_LEAN:?Set the pinned native compiler path}" \
  --mathlib "${VPD_MATHLIB:?Set the pinned Mathlib checkout}" \
  --lean-architect "${VPD_ARCHITECT:?Set the pinned LeanArchitect checkout}" \
  --output "${VPD_OUTPUT:?Set a task-owned verification directory}" \
  InfoGeometry.Probability.DetectorCrossSectionResponse \
  InfoGeometry.Probability.DetectorCrossSectionResponseAudit \
  InfoGeometry.Probability.DetectorReceivingArea \
  InfoGeometry.Probability.DetectorReceivingAreaAudit
```

This maintained checker holds the shared build lock, checks pins, and compiles the
selected source import closure. Its result is distinct from a root Lake build.
The root environment has a known bootstrap block: configured Atlas/Homotopy path
packages are absent in this checkout. The root build remains a separate acceptance
requirement; after restoring those dependencies, run:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Probability.DetectorCrossSectionResponse \
  InfoGeometry.Probability.DetectorReceivingArea
```

The scoped success does not certify a full build or satisfy the root publication
gate. Preserve pins and caches and use the tracked hooks unchanged. Publication
status and the final commit identity belong in the delivery record; no upstream
publication is claimed by this theorem contract.
