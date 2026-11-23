# Real helical phases and Clifford midline reflection

## Intake and acceptance status

This contract records the mathematical intake from
`Pasted text(20261123-115751).txt` (198 lines), SHA-256
`4f895d5347951b892ddbd8f05418e78bf6fdfdd7b457a3f9986ac994c04ab197`.
Its single fenced Lean block has 159 lines and SHA-256
`c5381feef6d9ec6b1e7bf7c16181e6e17bf91b6a6adc85739bcc224f9a00d2ff`.
The original block is preserved without repairs in the intake artifacts.

**Candidate contract: source review and the staged gate passed; compilation and
axiom inspection are pending.** Source review, a compiler result, and acceptance
of the surrounding interpretation are separate records. The attachment's three theorem statements concern coordinate,
Fourier-phase, and finite-matrix identities. They do not state GRH, an analytic
KMS condition, or a theorem about the growth of the full matrix evolution.

## Owner map

| Mathematical object | Existing owner | Intended use |
| --- | --- | --- |
| Real `2 × 2` Clifford algebra | `Clifford.Cl11Matrix` | Reuse `Eplus`, `Eminus`, `J1`, the native linear map `gen`, `gen_sq`, and the concrete noncommuting witness. |
| Symmetric and skew components | `OperatorAlgebra.RealMatrixSplit` | Express the split with native `selfAdjointPart` and `skewAdjointPart`. |
| Generic real phase rotor | `Clifford.FiniteCommutingRotorAction` | Reuse `rotor B θ = cos θ • 1 + sin θ • B`; do not introduce a scalar imaginary unit. |
| Midline glide and circular radius | `Canonical.KMSShearTubuleKleinPrimon` | Reuse the reflection, its fixed-locus law, and the existing circular-coordinate owner. |
| Circle coordinate | Mathlib `AddCircle (1 : ℝ)` | State the screw-period compatibility of the explicit map into `AddCircle 1 × ℝ`. |
| Bounded elliptic evolution | `Canonical.PolarizedShearSpinFrame` and its `Evolution`/`Solution` modules | Transport the existing constructed global finite-dimensional ODE solutions by an explicit real change of basis. |
| KMS/critical-strip coordinate correspondence | `NCG.KMSStripKleinMonodromy` | Document the existing affine correspondence and its scope; do not reinterpret it as an identity of KMS correlation functions and zeta functions. |

The search also inspected `DualAffineSaddleHelixTubuleBridge`,
`RiemannRotorBoostGeometricAlgebraBridge`, and
`HyperbolicEllipticKmsDecoherence`. Their curvature polynomials, complex
factorizations, and abstract dual-seed algebra do not replace the concrete
maps needed here. This is a bounded source search, not a repository-wide
nonexistence claim.

The two new owners expose 28 public theorems and seven definitions:

| New owner | Contents |
| --- | --- |
| `Canonical/RealHelicalFourierBridge.lean` | 15 theorems and six definitions for screw coordinates, their native circle projection, and real matrix Fourier phases. |
| `Canonical/RealCl11MidlineStability.lean` | 13 theorems and one native `LinearEquiv` for the existing Clifford generator's reflection, split, determinant, and bounded dynamics. |

Their dependency order follows the actual proof terms:

| Endpoint | Prerequisite used by its proof |
| --- | --- |
| `tubuleCover_screw` | Real trigonometric integer periods and `axialCoordinate_screw`. |
| `cylinderCoordinate_screw` | Native `AddCircle` coercion laws and the same axial invariance. |
| `helicalMode_half_screw_parity` | The existing real rotor, integer half-period trigonometric identities, and Mathlib integer parity. |
| `restrictedMode_half_screw_parity` | The exact restricted-mode coordinate identity with `P ≠ 0`, followed by the general half-shift theorem. |
| `gen_selfAdjointPart`, `gen_skewAdjointPart` | The existing `gen` and native real-matrix split formulas. |
| `exists_bounded_gen_solution` | The owned constructed shear solutions, `shearCoordinates_symm_intertwines`, and `shearCoordinates_square_sum`. |
| `off_midline_bounded_solution` | The preceding existence theorem and rational normalization of the bound to four. |

There is no proof dependency from these identities to a GRH conclusion.

## 1. Screw-periodic cylinder coordinates

For real radius `R` and pitch `P`, the coordinate map is

\[
\Phi_{R,P}(u,t)=
\bigl(R\cos(2\pi u),R\sin(2\pi u),t-Pu\bigr).
\]

The useful invariance is

\[
\Phi_{R,P}(u+m,t+mP)=\Phi_{R,P}(u,t),\qquad m\in\mathbb Z.
\]

The axial coordinate `z = t - P*u` is unchanged by these shifts. In particular,
this map from `ℝ × ℝ` is not injective. Its interpretation as a cylinder uses
the circle coordinate `[u]`; the invariant projection is

\[
(u,t)\longmapsto([u],t-Pu)\in (\mathbb R/\mathbb Z)\times\mathbb R.
\]

A compatibility theorem for this projection is not, by itself, a construction
of a quotient homeomorphism or a smooth embedding. The image has the ordinary
circular radius relation. The term "helix" describes suitable parameter curves
on that cylinder, not an additional topological conclusion.

The half shift sends the transverse coordinates to their antipodes and leaves
the axial coordinate unchanged. Adding the independent reflection of `σ`
gives

\[
S(\sigma,u,t)=(1-\sigma,u+1/2,t+P/2),\qquad
S^2(\sigma,u,t)=(\sigma,u+1,t+P).
\]

Thus two half shifts give one full turn. The fixed-coordinate statement is
`1 - σ = σ ↔ σ = 1/2`; it is not a fixed-point statement for the full seam.
These formulas do not establish a spin representation, a `4π` spinor return,
or a Möbius-bundle classification.

## 2. Real phases and the unrestricted axial frequency

Let `J = atomJ = [[0,-1],[1,0]]` be the existing real phase matrix with
`J² = -1`. It equals `-Eminus`, so its orientation is opposite to the `ε`
used in the Clifford generator below. Use the generic real rotor to write

\[
M_{n,\nu}(u,t)=
\operatorname{rotor}\!\left(J,
2\pi\bigl(nu+\nu(t-Pu)\bigr)\right),
\qquad n\in\mathbb Z,\ \nu\in\mathbb R.
\]

The screw shift leaves the axial coordinate unchanged and changes the angle
by an integer multiple of `2π`. The half shift gives

\[
M_{n,\nu}(u+1/2,t+P/2)=(-1)^n M_{n,\nu}(u,t).
\]

The sign depends on the integer angular mode; `ν` is an arbitrary real number. The
attachment's restricted phase

\[
2\pi(ku+\omega t/P)
\]

is recovered with `n = k + ω` and `ν = ω/P`, assuming `P ≠ 0`. This explains
its parity factor `(-1)^(k+ω)` without inferring that the noncompact axis has
quantized frequency. The real mode is a rotation matrix, not a new copy of a
complex phase API. Periodicity and antiperiodicity here are exact transformation
laws; identifying them with a fermionic KMS state requires additional data.

## 3. The midline as a symmetry and skew-adjointness condition

Use the existing Clifford linear map directly:

\[
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
\varepsilon=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\quad
W=\operatorname{gen}(\delta,\gamma)=\delta Z+\gamma\varepsilon,
\quad\delta=\sigma-1/2.
\]

The required identities are

\[
(-\varepsilon)W\varepsilon=\operatorname{gen}(-\delta,\gamma),
\qquad
W_{\mathrm{sym}}=\delta Z,
\qquad W_{\mathrm{skew}}=\gamma\varepsilon.
\]

The reflection fixes `W` exactly when `δ = 0`, which is also exactly the
condition that `W` is skew-adjoint in the standard Euclidean inner product.
For an individual vector,

\[
v^T Wv=\delta(v_0^2-v_1^2).
\]

Vanishing for every vector is equivalent to `δ = 0`; vanishing for one vector
does not force that conclusion. These are statements about the full
noncommutative real matrix carrier, with its concrete noncommuting generators.
For `δ ≠ 0`, the symmetric term `δ Z` is indefinite. The split therefore does
not supply a positive Onsager dissipation operator or a GENERIC structure.

## 4. The growth claim needs the full generator

The existing Clifford relation gives

\[
W^2=(\delta^2-\gamma^2)I.
\]

Its ordinary real matrix determinant is `γ² - δ²`; these finite two-dimensional
readouts do not identify a frame-volume Jacobian with a spacetime interval.

The sign of this discriminant, rather than `δ ≠ 0` alone, separates elliptic,
nilpotent, and hyperbolic cases. In particular, the exponential of the sum
cannot be replaced by a product of the pure boost and pure rotation
exponentials without a compatibility proof: `Z` and `ε` do not commute.

The existing polarized-shear operator is
`L(δ,γ) = δ J1 + γ ε`. The explicit real change of basis

\[
C=\begin{pmatrix}1&-1\\1&1\end{pmatrix},\qquad
C^{-1}=\tfrac12 C^T
\]

relates `W` and `L`. Its scaled orthogonality also transports Euclidean square
bounds. The owned `exists_bounded_solution` theorem constructs a global
trajectory for every initial vector when `|δ| < γ` and damping is nonnegative.
At zero damping this gives a bounded-forward-time example even when `δ ≠ 0`.
One rational choice lying inside the strip is

\[
\sigma=11/16,\quad\delta=3/16,\quad\gamma=5/16,
\qquad W^2=-\tfrac1{16}I.
\]

The source-backed target is the exact basis transport and bounded-solution
theorem. A source review of that formula alone is not kernel verification of
the new adapter.

## 5. Boundary of the KMS and GRH interpretation

The KMS condition is an analytic, state-dependent boundary relation with
reversed operator order. It does not automatically make the two boundary
values equal or identify the strip's edges as points. The existing
`KMSStripKleinMonodromy` owner already records this distinction.

Likewise, invariance of a zero set under a reflection does not imply that
each zero is a fixed point. Establishing GRH would require a relation to the
actual relevant `L`-functions and a theorem excluding off-line zeros. Neither
the supplied three Lean theorem statements nor the coordinate and finite
operator bridges above supplies that implication. No GRH theorem is claimed.
Related repository owners preserve that dependency explicitly:
`TraceFormula/HestenesGeometricIntegralConfinement` assumes its symmetry and
Casimir bound, and `External/Auto/CriticalLineMetriplectic` takes an independent
`CriticalLineLock` premise. Those hypotheses are not constructed by this
attachment.

Primary references for these boundaries:

- Vaughan F. R. Jones, *Von Neumann Algebras*, Definition 13.4.2:
  <https://math.berkeley.edu/~vfr/VonNeumann2009.pdf>.
- Enrico Bombieri, *Problems of the Millennium: the Riemann Hypothesis*, §I:
  <https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf>.

## Validation record

Root and independent mathematical source reviews are complete. The unchanged
staged proof-integrity gate passed for these two new owners. Their combined
focused build has been launched and is waiting for the shared build lock;
the native declaration/axiom audit has not run. No kernel acceptance is claimed
for these 28 theorem declarations at this publication snapshot. The original
attached Lean block is preserved without repair and was not compiled.

```bash
python3 verification/real-matrix-split/check.py build \
  InfoGeometry.Canonical.RealHelicalFourierBridge \
  InfoGeometry.Canonical.RealCl11MidlineStability
```

| Owner | Frozen SHA-256 | Status |
| --- | --- | --- |
| `Canonical.RealHelicalFourierBridge` | `1bd9bc99abdba382b726d5072becb69c534854283392f0b378a88665aca6eedc` | Reviewed; focused build queued; audit unrun |
| `Canonical.RealCl11MidlineStability` | `4243a5343d999f0ff6145e54f51f29559d2f8e1a8b739a6b4c29641eaad7b6f2` | Reviewed; focused build queued; audit unrun |

The environment remains Lean 4.34.1 with Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The focused import closure has no
dependency on the missing root Homotopy/Atlas/GIFT paths. The separately
disclosed root pre-push dependency blocker remains; this focused lane is not
a root or whole-repository build certificate.
