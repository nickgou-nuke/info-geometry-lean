# Klein Quadric / Determinant Monodromy Synthesis

This note gives a clean formulation of the themes you listed, aligned with the Lean file
`lean/InfoGeometry/Projective/KleinQuadricMonodromy.lean` and the witness script
`formalizations/klein_quadric_monodromy_witness.py`.

## 1) Core geometric data

Let

- `P : Plucker6 ℂ` be a Plücker/Klein quadric coordinate vector,
- `Q(P) = Plucker6.kleinQ P : ℂ` the Klein quadratic form (the determinant-like scalar),
- `Q(P) = 0` the **null / singular divisor** (chiral causal boundary / polar locus).

Define the open domain

\[
M := \{P \in Plucker6(\mathbb C) \mid Q(P) \neq 0\}.
\]

On `M`, define the logarithmic potential and 1-form

\[
\Phi(P) := \log Q(P), \qquad
\omega := d\Phi = \frac{dQ}{Q}.
\]

## 2) de Rham meaning

Since `Q` is nonzero on `M`, `Q⁻¹` is smooth there, so

- `ω` is well-defined on `M`,
- `dω = 0` (formally, `d(d log Q)=0`),
- the class `[ω] ∈ H^1(M)` records a nontrivial period around the divisor.

In particular, loop integration along a positively oriented circle about the divisor gives residue data.

## 3) Local model and circle integral

For the model form on `ℂ\setminus\{0\}`,

\[
\eta(z)=\frac{1}{z}
\]

the implemented theorem proves

\[
\oint_{|z|=R} \eta\,dz = 2\pi i, \quad R>0.
\]

This is exactly `circleIntegral_one_div` in Lean.

## 4) Winding / monodromy

If a loop has integer winding number `n`, then

\[
\oint \omega = n\cdot 2\pi i,
\]

formalized as

\[
(n:\mathbb C) \cdot \oint\eta = \logarithmicPhase(n) = (n:\mathbb C)(2\pi i).
\]

The symbolic name in Lean: `deRhamClass_of_winding`.

## 5) Universal cover and sheet-shift

The universal log lift in the repo (`uLog`) is a multivalued/cover-aware branch.

\[
\text{uLog}(z,n+1)-\text{uLog}(z,n)=2\pi i.
\]

This is exactly `universalCoverLog_sheet_increment`.

## 6) Holonomy / Wilson-style phase

Exponentiating the loop value gives the phase (Wilson/monodromy holonomy)

\[
\exp\bigl(\logarithmicPhase(n)\bigr)
= \exp(2\pi i n)=1.
\]

So the multiplicative holonomy for a **closed integer winding** is trivial in `\mathbb C^×` (pure phase with integer monodromy, and the integer lattice is kernel via `exp(2πi n)`).
Lean theorem: `holonomyPhase_is_root_of_unity`.

The corresponding Wilson-loop statement is now written as
`wilsonPhase_of_winding`.

## 7) Chiral-null determinant classification

For `Plucker6` over `ℂ` one has

- `Q(P)=0` iff `polar(P,P)=0` (equivalently rank-2 isotropic incidence in this normalization),

formalized in Lean as
`chiralNullConductor_eq_selfOrthogonal`.

## 8) Klein-quadratic interpretation

All of this is the determinant-hypersurface story in local coordinates:

- `Q=0` is the divisor where the logarithm necessarily branches,
- `ω=dQ/Q` is the closed generator detecting that branch,
- winding/monodromy around `Q=0` is encoded by `2πi · n`.

That is the precise bridge from:
- Klein quadric / chiral cone geometry,
- Grothendieck–de Rham class viewpoint (`[ω]`),
- and geometric holonomy/Wilson loop monodromy.

## 8) Pointers in this repo

- Lean formalization: `lean/InfoGeometry/Projective/KleinQuadricMonodromy.lean`
- Umbrella import added in: `lean/InfoGeometry/Projective/All.lean`
- Legacy witness: `formalizations/klein_quadric_monodromy_witness.py`
- Multibackend pipeline: `formalizations/klein_quadric_multibackend_pipeline.py`
- Motivic-style bridge checks (sympy/sage/gap/galgebra/clifford/M2): `formalizations/klein_quadric_motive_bridge.py`
- Backend status note: `docs/klein_quadric_multibackend_pipeline.md`