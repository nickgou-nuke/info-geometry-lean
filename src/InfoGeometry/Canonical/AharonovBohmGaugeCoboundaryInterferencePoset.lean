/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.SelbergTraceAharonovBohm
import InfoGeometry.Canonical.ModularHamiltonianHorizonDefectPoset
import InfoGeometry.Canonical.E10Grading
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The Aharonov–Bohm (1959) Gauge-Coboundary, Two-Branch Interference, & Möbius Horizon Poset

This canonical module formalizes the mathematical core of **Y. Aharonov and D. Bohm**,
*"Significance of Electromagnetic Potentials in the Quantum Theory"*, *Phys. Rev.* **115**,
485–491 (1959) (`10.1103/PhysRev.115.485`), and proves its exact bridges to the repository's
Type-D bitword Cantor continuum (`InfoGeometry.Canonical.E10Grading`) and $(5,5)$ Möbius
horizon capacitor (`InfoGeometry.Canonical.ModularHamiltonianHorizonDefectPoset`):

1. **Discrete Gauge Coboundaries & Closed-Loop Stokes Invariance:**
   Over any finite vertex set $\iota$ with cyclic step permutation $\sigma \in \mathrm{Perm}(\iota)$
   and any additive commutative group $G$, the discrete gauge coboundary
   $(d_\sigma \chi)_i = \chi(\sigma(i)) - \chi(i)$ has strictly vanishing closed-loop circulation
   $\oint d_\sigma \chi = \sum_{i \in \iota} (\chi(\sigma(i)) - \chi(i)) = 0$, rendering the
   Wilson loop circulation $\oint (A + d_\sigma \chi) = \oint A$ strictly gauge-invariant.
2. **Type-D Bitword Even-Parity Subgroup as Flat $\mathbb{Z}_2$ Gauge Connections:**
   Specializing to $G = \mathrm{ZMod}\,2$ on $\mathrm{Fin}\,n$, every discrete $\mathbb{Z}_2$
   gauge coboundary $d_\sigma \chi$ has zero Hamming parity (`parity (d_σ χ) = 0`) and lies in
   `TypeDEvenParity n`, preserving the global $\mathbb{Z}_2$ Aharonov–Bohm flux across all finite
   stages and into the Cantor colimit `cantorTypeDLattice`.
3. **Continuous $U(1)$ Aharonov–Bohm Two-Branch Interference & Half-Flux ($\pi$) Destructive Node:**
   Reusing `aharonovBohmPhase` ($\phi \mapsto e^{i\phi}$) from
   `InfoGeometry.Physics.SelbergTraceAharonovBohm`, we prove:
   - Half-flux Möbius inversion: $e^{i\pi} = -1$ and $e^{i(2k+1)\pi} = -1$ ($k \in \mathbb{Z}$);
   - Two-branch interference factorization and endpoint gauge invariance;
   - Constructive doubling ($2\psi_0 e^{i\alpha_1}$) at integer flux quanta $\Delta\varphi = 2\pi k$;
   - **Exact destructive cancellation ($= 0$)** at the half-flux quantum
     $\Delta\varphi = (2k+1)\pi$, together with the real trigonometric envelope identity
     $2 I_0 (1 + \cos \Delta\varphi) = 4 I_0 \cos^2(\Delta\varphi / 2)$.
4. **Möbius Horizon Capacitor as Constructive/Destructive Aharonov–Bohm Projectors:**
   The Weyl/Peirce projectors $P_+(\mathcal{T}) = \frac{1}{2}(1 + \mathcal{T})$ and
   $P_-(\mathcal{T}) = \frac{1}{2}(1 - \mathcal{T})$ are the $\Delta\varphi = 0$ (constructive)
   and $\Delta\varphi = \pi$ (destructive) Aharonov–Bohm interference projectors of the Möbius
   twist $\mathcal{T}$, each carrying trace $5$ on the 10-dimensional $(5,5)$ horizon.

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved Gauge, Interference, & Operator Theorems (`[kernel_verified]`):**
  - `loopCirculation_gaugeCoboundary_eq_zero` and `loopCirculation_gaugeTransform_invariant`:
    Discrete Stokes theorem $\oint d_\sigma \chi = 0$ and gauge invariance
    $\oint (A + d_\sigma \chi) = \oint A$ over any `AddCommGroup G`.
  - `bitword_gaugeCoboundary_mem_typeDEvenParity`: Every $\mathrm{ZMod}\,2$ gauge coboundary lies
    in `TypeDEvenParity n` and preserves bitword `parity` under `applyDelta`.
  - `aharonovBohmPhase_pi_and_odd_multiples`, `twoBranch_aharonov_bohm_interference_laws`, and
    `realInterferenceEnvelope_trig_laws`: Complete complex and real two-branch Aharonov–Bohm
    interference identities, integer-flux constructive maxima, and half-flux destructive zeros.
  - `moebius_capacitor_aharonov_bohm_interference_trace_laws`, `abHolonomyZ_X_braiding`, and
    `abHolonomy_noncommutative`: Operator and $(5,5)$ matrix trace decomposition into 5
    constructive and 5 destructive Aharonov–Bohm modes, plus non-abelian $\mathbb{Z}_2$
    Wilson–'t Hooft braiding.
  - `abRotationalEnergy_flux_periodicity_and_chirality` and `abScatteringFluxFactor_laws`:
    Section 3 of Aharonov & Bohm (1959): shifted partial-wave kinetic angular-momentum spectrum
    $E_m(\alpha) = (m + \alpha)^2$, Byers–Yang integer-flux periodicity
    $E_{m-k}(\alpha+k) = E_m(\alpha)$, chiral splitting $E_m(\alpha) - E_{-m}(\alpha) = 4m\alpha$,
    half-flux $\alpha = 1/2$ Kramers doublet degeneracy $E_m(1/2) = E_{-m-1}(1/2)$ with positive
    zero-point gap $E_0(1/2) = E_{-1}(1/2) = 1/4$, and the exact scattering cross-section flux
    factor $\sin^2(\pi\alpha)$.

* **BUCKET 2 — Eliminated Wrappers & Vacuous Placeholders (Zero Remaining):**
  - No `Prop`-valued `def`, `structure`, or `class` wrappers are introduced; all gauge-invariance
    and interference identities are stated directly as algebraic equations.

* **BUCKET 3 — Continuous Differential-Form Stokes Theorem on Smooth Manifolds (`[bucket_3_open_debt]`):**
  - Smooth manifold de Rham cohomology $H^1(\mathbb{R}^2 \setminus \{0\}; \mathbb{R}) \cong \mathbb{R}$
    and path-ordered continuum contour integrals remain outside this discrete-coboundary and
    exact complex-exponential scope.
-/

namespace InfoGeometry.Canonical.AharonovBohmGaugeCoboundaryInterferencePoset

open scoped BigOperators
open Complex Real Matrix
open InfoGeometry.Physics.SelbergTraceAharonovBohm
open InfoGeometry.Canonical.ModularHamiltonianHorizonDefectPoset
open InfoGeometry.Canonical.E10Grading

-- ============================================================================
-- SECTION 1: Discrete Gauge Coboundaries & Closed-Loop Stokes Invariance
-- ============================================================================

section DiscreteGaugeCoboundary

variable {ι G : Type*} [Fintype ι] [AddCommGroup G]

/-- Discrete gauge coboundary $(d_\sigma \chi)_i = \chi(\sigma(i)) - \chi(i)$ of a vertex scalar
potential $\chi : \iota \to G$ along a permutation $\sigma \in \mathrm{Perm}(\iota)$ generating
a directed cycle of links. -/
def gaugeCoboundary (σ : Equiv.Perm ι) (χ : ι → G) : ι → G :=
  fun i => χ (σ i) - χ i

/-- Gauge transformation of a discrete link connection $A : \iota \to G$ by a vertex gauge
potential $\chi : \iota \to G$: $A \mapsto A + d_\sigma \chi$. -/
def gaugeTransform (σ : Equiv.Perm ι) (A χ : ι → G) : ι → G :=
  fun i => A i + gaugeCoboundary σ χ i

/-- Closed-loop circulation (discrete Wilson loop phase sum) $\oint A = \sum_{i \in \iota} A_i$. -/
def loopCirculation (A : ι → G) : G :=
  ∑ i : ι, A i

/-- **Discrete Stokes Theorem for Gauge Coboundaries (`loopCirculation_gaugeCoboundary_eq_zero`):**
The closed-loop circulation of any discrete gauge coboundary $d_\sigma \chi$ vanishes identically:
$$\oint d_\sigma \chi = \sum_{i \in \iota} \bigl(\chi(\sigma(i)) - \chi(i)\bigr) = 0.$$ -/
theorem loopCirculation_gaugeCoboundary_eq_zero (σ : Equiv.Perm ι) (χ : ι → G) :
    loopCirculation (gaugeCoboundary σ χ) = 0 := by
  unfold loopCirculation gaugeCoboundary
  rw [Finset.sum_sub_distrib, Equiv.sum_comp σ χ, sub_self]

/-- **Aharonov–Bohm Gauge Invariance of Closed-Loop Circulation (`loopCirculation_gaugeTransform_invariant`):**
For any link potential $A : \iota \to G$ and any single-valued vertex gauge potential
$\chi : \iota \to G$, the closed-loop circulation is strictly invariant under
$A \mapsto A + d_\sigma \chi$:
$$\oint (A + d_\sigma \chi) = \oint A,$$
and the difference between two connections sharing the same coboundary offset has zero circulation. -/
theorem loopCirculation_gaugeTransform_invariant (σ : Equiv.Perm ι) (A χ : ι → G) :
    loopCirculation (gaugeTransform σ A χ) = loopCirculation A ∧
    loopCirculation (gaugeTransform σ 0 χ) = 0 := by
  have hCob := loopCirculation_gaugeCoboundary_eq_zero σ χ
  refine ⟨?_, ?_⟩
  · unfold loopCirculation gaugeTransform
    rw [Finset.sum_add_distrib]
    change loopCirculation A + loopCirculation (gaugeCoboundary σ χ) = loopCirculation A
    rw [hCob, add_zero]
  · unfold gaugeTransform
    simp only [Pi.zero_apply, zero_add]
    exact hCob

/-- **Type-D Bitword Even-Parity Identification (`bitword_gaugeCoboundary_mem_typeDEvenParity`):**
Over $G = \mathrm{ZMod}\,2$ on $\iota = \mathrm{Fin}\,n$, for every permutation
$\sigma \in \mathrm{Perm}(\mathrm{Fin}\,n)$ and every vertex potential $\chi : \mathrm{Fin}\,n \to \mathrm{ZMod}\,2$:
1. The discrete gauge coboundary $d_\sigma \chi$ has zero total Hamming parity:
   `parity (gaugeCoboundary σ χ) = 0`;
2. $d_\sigma \chi$ belongs to the Type-D even-parity subgroup `TypeDEvenParity n`;
3. Applying $d_\sigma \chi$ via the ATOMiK hardware transition `applyDelta` preserves the
   global $\mathbb{Z}_2$ Aharonov–Bohm flux `parity state`. -/
theorem bitword_gaugeCoboundary_mem_typeDEvenParity {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (state χ : Bitword n) :
    parity (gaugeCoboundary σ χ) = 0 ∧
    gaugeCoboundary σ χ ∈ TypeDEvenParity n ∧
    parity (applyDelta state (gaugeCoboundary σ χ)) = parity state := by
  have hPar : parity (gaugeCoboundary σ χ) = 0 :=
    loopCirculation_gaugeCoboundary_eq_zero σ χ
  have hMem : gaugeCoboundary σ χ ∈ TypeDEvenParity n := hPar
  refine ⟨hPar, hMem, ?_⟩
  unfold applyDelta parity
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  change parity state + parity (gaugeCoboundary σ χ) = parity state
  rw [hPar, add_zero]

end DiscreteGaugeCoboundary

-- ============================================================================
-- SECTION 2: Continuous U(1) Aharonov–Bohm Two-Branch Interference & Half-Flux Node
-- ============================================================================

noncomputable section ContinuousAharonovBohmInterference

/-- The additive flux around a finite loop exponentiates to the product of its
edge phases.  This bridges the discrete circulation convention above to the
multiplicative Wilson-loop convention used for interference. -/
theorem aharonovBohmPhase_loopCirculation_eq_prod
    {ι : Type*} [Fintype ι] (A : ι → ℝ) :
    aharonovBohmPhase (loopCirculation A) =
      ∏ i : ι, aharonovBohmPhase (A i) := by
  classical
  have h : ∀ s : Finset ι,
      aharonovBohmPhase (∑ i ∈ s, A i) =
        ∏ i ∈ s, aharonovBohmPhase (A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [PrimeGeodesic.aharonov_bohm_phase_zero]
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha,
          PrimeGeodesic.aharonov_bohm_phase_add, ih]
  simpa [loopCirculation] using h Finset.univ

/-- A single-valued vertex gauge change leaves the multiplicative phase
holonomy of a finite cyclic link system invariant. -/
theorem aharonovBohmWilsonLoop_gaugeTransform_invariant
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    (A χ : ι → ℝ) :
    (∏ i : ι, aharonovBohmPhase (gaugeTransform σ A χ i)) =
      ∏ i : ι, aharonovBohmPhase (A i) := by
  rw [← aharonovBohmPhase_loopCirculation_eq_prod,
    ← aharonovBohmPhase_loopCirculation_eq_prod]
  exact congrArg aharonovBohmPhase
    (loopCirculation_gaugeTransform_invariant σ A χ).1

/-- Coefficient of the normalized Aharonov--Bohm connection form `a(z) dz`
on the punctured complex plane. The normalization makes its integral around a
positively oriented circle equal to the phase flux. -/
def abCircleConnectionCoefficient (flux : ℝ) (z : ℂ) : ℂ :=
  (-(flux : ℂ) * Complex.I / (2 * Real.pi)) * (z - 0)⁻¹

/-- **Continuum circle circulation (`abCircleConnection_circleIntegral`):**
For every positive radius, the contour integral of this coefficient is exactly
`flux`. This uses Mathlib's native Cauchy-kernel circle-integral theorem and
does not assert a general de Rham classification. -/
theorem abCircleConnection_circleIntegral (flux : ℝ) {r : ℝ} (hr : 0 < r) :
    (∮ z in C(0, r), abCircleConnectionCoefficient flux z) = (flux : ℂ) := by
  change (∮ z in C(0, r),
    (-(flux : ℂ) * Complex.I / (2 * Real.pi)) * (z - 0)⁻¹) = (flux : ℂ)
  rw [circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_center_inv 0 hr.ne']
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  rw [Complex.I_sq]
  ring

/-- The contour holonomy of the normalized Aharonov--Bohm connection is the
usual `U(1)` phase at the enclosed flux. -/
theorem abCircleConnection_phase_holonomy (flux : ℝ) {r : ℝ} (hr : 0 < r) :
    aharonovBohmPhase (flux : ℝ) =
      aharonovBohmPhase
        ((∮ z in C(0, r), abCircleConnectionCoefficient flux z).re) := by
  rw [abCircleConnection_circleIntegral flux hr]
  simp

/-- **Non-exactness from nonzero holonomy:** if `flux ≠ 0`, the normalized
connection coefficient has no single-valued complex differentiable primitive
on the punctured plane. Otherwise its derivative would integrate to zero on
the unit circle, contradicting the circle-integral formula. -/
theorem abCircleConnection_no_global_primitive (flux : ℝ) (hflux : flux ≠ 0) :
    ¬ ∃ F : ℂ → ℂ, ∀ z : ℂ, z ≠ 0 →
      HasDerivAt F (abCircleConnectionCoefficient flux z) z := by
  rintro ⟨F, hF⟩
  have hzero : (∮ z in C(0, (1 : ℝ)),
      abCircleConnectionCoefficient flux z) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt (by norm_num)
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      simp at hz
    exact (hF z hz0).hasDerivWithinAt
  rw [abCircleConnection_circleIntegral flux (by norm_num : 0 < (1 : ℝ))] at hzero
  exact hflux (by exact_mod_cast hzero)

/-- **Half-Flux ($\Delta\varphi = \pi$) & Odd-Multiple Möbius Inversion (`aharonovBohmPhase_pi_and_odd_multiples`):**
For the continuous $U(1)$ Aharonov–Bohm phase factor $\mathrm{aharonovBohmPhase}(\phi) = e^{i\phi}$:
1. At the half-flux quantum $\phi = \pi$, $\mathrm{aharonovBohmPhase}(\pi) = -1$;
2. At every odd multiple $\phi = (2k + 1)\pi$ ($k \in \mathbb{Z}$),
   $\mathrm{aharonovBohmPhase}((2k + 1)\pi) = -1$;
3. Double winding of a half-flux vortex restores the identity phase:
   $\mathrm{aharonovBohmPhase}(\pi) \cdot \mathrm{aharonovBohmPhase}(\pi) = 1$;
4. Shifting any flux $\phi$ by $\pi$ inverts the sign of the phase factor:
   $\mathrm{aharonovBohmPhase}(\phi + \pi) = -\mathrm{aharonovBohmPhase}(\phi)$. -/
theorem aharonovBohmPhase_pi_and_odd_multiples (phi : ℝ) (k : ℤ) :
    aharonovBohmPhase Real.pi = -1 ∧
    aharonovBohmPhase ((2 * (k : ℝ) + 1) * Real.pi) = -1 ∧
    aharonovBohmPhase Real.pi * aharonovBohmPhase Real.pi = 1 ∧
    aharonovBohmPhase (phi + Real.pi) = - aharonovBohmPhase phi := by
  have hPi : aharonovBohmPhase Real.pi = -1 := by
    unfold aharonovBohmPhase
    have hComm : Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I := mul_comm _ _
    rw [hComm, Complex.exp_pi_mul_I]
  have hOdd : aharonovBohmPhase ((2 * (k : ℝ) + 1) * Real.pi) = -1 := by
    have hSplit : (2 * (k : ℝ) + 1) * Real.pi = 2 * Real.pi * (k : ℝ) + Real.pi := by ring
    rw [hSplit, PrimeGeodesic.aharonov_bohm_phase_add,
      PrimeGeodesic.aharonov_bohm_phase_two_pi_int k, hPi, one_mul]
  have hSq : aharonovBohmPhase Real.pi * aharonovBohmPhase Real.pi = 1 := by
    rw [hPi]
    ring
  have hShift : aharonovBohmPhase (phi + Real.pi) = - aharonovBohmPhase phi := by
    rw [PrimeGeodesic.aharonov_bohm_phase_add, hPi, mul_neg_one]
  exact ⟨hPi, hOdd, hSq, hShift⟩

/-- Recombined two-branch Aharonov–Bohm wavefunction
$\Psi(\psi_0, \alpha_1, \alpha_2) = \psi_0 e^{i\alpha_1} + \psi_0 e^{i\alpha_2}$
at the interferometer screen for equal-amplitude branches $\psi_0 \in \mathbb{C}$ with
branch path phases $\alpha_1, \alpha_2 \in \mathbb{R}$. -/
def twoBranchSuperposition (ψ₀ : ℂ) (α₁ α₂ : ℝ) : ℂ :=
  ψ₀ * aharonovBohmPhase α₁ + ψ₀ * aharonovBohmPhase α₂

/-- **Two-Branch Aharonov–Bohm Interference & Gauge-Invariance Theorem (`twoBranch_aharonov_bohm_interference_laws`):**
For any branch amplitude $\psi_0 \in \mathbb{C}$, branch phases $\alpha_1, \alpha_2 \in \mathbb{R}$,
endpoint gauge shift $\Lambda \in \mathbb{R}$, and integer flux quantum $k \in \mathbb{Z}$:
1. **Circulation Factorization:**
   $$\Psi(\psi_0, \alpha_1, \alpha_2) = \psi_0 e^{i\alpha_1}\bigl(1 + e^{i(\alpha_2 - \alpha_1)}\bigr);$$
2. **Endpoint Gauge Invariance of Interference Amplitude:**
   $$\|\Psi(\psi_0, \alpha_1 + \Lambda, \alpha_2 + \Lambda)\| = \|\Psi(\psi_0, \alpha_1, \alpha_2)\|;$$
3. **Constructive Interference at Integer Flux ($\Delta\varphi = 2\pi k$):**
   $$\Psi(\psi_0, \alpha_1, \alpha_1 + 2\pi k) = 2\psi_0 e^{i\alpha_1};$$
4. **Exact Destructive Cancellation at Half-Flux ($\Delta\varphi = \pi$ and $\Delta\varphi = (2k+1)\pi$):**
   $$\Psi(\psi_0, \alpha_1, \alpha_1 + \pi) = 0
     \quad\text{and}\quad
     \Psi\bigl(\psi_0, \alpha_1, \alpha_1 + (2k + 1)\pi\bigr) = 0.$$ -/
theorem twoBranch_aharonov_bohm_interference_laws
    (ψ₀ : ℂ) (α₁ α₂ Λ : ℝ) (k : ℤ) :
    twoBranchSuperposition ψ₀ α₁ α₂ =
      ψ₀ * aharonovBohmPhase α₁ * (1 + aharonovBohmPhase (α₂ - α₁)) ∧
    ‖twoBranchSuperposition ψ₀ (α₁ + Λ) (α₂ + Λ)‖ =
      ‖twoBranchSuperposition ψ₀ α₁ α₂‖ ∧
    twoBranchSuperposition ψ₀ α₁ (α₁ + 2 * Real.pi * (k : ℝ)) =
      2 * ψ₀ * aharonovBohmPhase α₁ ∧
    twoBranchSuperposition ψ₀ α₁ (α₁ + Real.pi) = 0 ∧
    twoBranchSuperposition ψ₀ α₁ (α₁ + (2 * (k : ℝ) + 1) * Real.pi) = 0 := by
  have hSplit : α₂ = α₁ + (α₂ - α₁) := by ring
  have hFactor : ∀ a b : ℝ,
      twoBranchSuperposition ψ₀ a b =
        ψ₀ * aharonovBohmPhase a * (1 + aharonovBohmPhase (b - a)) := by
    intro a b
    unfold twoBranchSuperposition
    have hb : b = a + (b - a) := by ring
    conv_lhs => rw [hb, PrimeGeodesic.aharonov_bohm_phase_add]
    ring
  have hPiLaws := aharonovBohmPhase_pi_and_odd_multiples α₁ k
  refine ⟨hFactor α₁ α₂, ?_, ?_, ?_, ?_⟩
  · unfold twoBranchSuperposition
    rw [PrimeGeodesic.aharonov_bohm_phase_add α₁ Λ,
        PrimeGeodesic.aharonov_bohm_phase_add α₂ Λ]
    have hPull :
        ψ₀ * (aharonovBohmPhase α₁ * aharonovBohmPhase Λ) +
          ψ₀ * (aharonovBohmPhase α₂ * aharonovBohmPhase Λ) =
        (ψ₀ * aharonovBohmPhase α₁ + ψ₀ * aharonovBohmPhase α₂) *
          aharonovBohmPhase Λ := by ring
    rw [hPull, norm_mul, PrimeGeodesic.aharonov_bohm_phase_norm Λ, mul_one]
  · rw [hFactor α₁ (α₁ + 2 * Real.pi * (k : ℝ))]
    have hDiff : α₁ + 2 * Real.pi * (k : ℝ) - α₁ = 2 * Real.pi * (k : ℝ) := by ring
    rw [hDiff, PrimeGeodesic.aharonov_bohm_phase_two_pi_int k]
    ring
  · rw [hFactor α₁ (α₁ + Real.pi)]
    have hDiff : α₁ + Real.pi - α₁ = Real.pi := by ring
    rw [hDiff, hPiLaws.1, add_neg_cancel, mul_zero]
  · rw [hFactor α₁ (α₁ + (2 * (k : ℝ) + 1) * Real.pi)]
    have hDiff : α₁ + (2 * (k : ℝ) + 1) * Real.pi - α₁ = (2 * (k : ℝ) + 1) * Real.pi := by ring
    rw [hDiff, hPiLaws.2.1, add_neg_cancel, mul_zero]

/-- Real two-branch Aharonov–Bohm interference intensity envelope
$I(I_0, \Delta\varphi) = 2 I_0 (1 + \cos \Delta\varphi)$ as a function of single-branch
intensity $I_0 \ge 0$ and enclosed magnetic flux phase $\Delta\varphi \in \mathbb{R}$. -/
def realInterferenceEnvelope (I₀ Δφ : ℝ) : ℝ :=
  2 * I₀ * (1 + Real.cos Δφ)

/-- **Real Interference Envelope & Half-Angle Square Law (`realInterferenceEnvelope_trig_laws`):**
For any branch intensity $I_0 \in \mathbb{R}$ and enclosed flux phase $\Delta\varphi \in \mathbb{R}$:
1. **Half-Angle Cosine-Squared Law:**
   $$2 I_0 (1 + \cos \Delta\varphi) = 4 I_0 \cos^2\!\left(\frac{\Delta\varphi}{2}\right);$$
2. **Non-Negativity:** If $0 \le I_0$, then $0 \le \mathrm{realInterferenceEnvelope}(I_0, \Delta\varphi)$;
3. **Constructive Maximum at Zero Flux ($\Delta\varphi = 0$):**
   $\mathrm{realInterferenceEnvelope}(I_0, 0) = 4 I_0$;
4. **Destructive Minimum at Half Flux ($\Delta\varphi = \pi$):**
   $\mathrm{realInterferenceEnvelope}(I_0, \pi) = 0$;
5. **Flux Reversal Symmetry:**
   $\mathrm{realInterferenceEnvelope}(I_0, -\Delta\varphi) = \mathrm{realInterferenceEnvelope}(I_0, \Delta\varphi)$. -/
theorem realInterferenceEnvelope_trig_laws (I₀ Δφ : ℝ) (hI₀ : 0 ≤ I₀) :
    realInterferenceEnvelope I₀ Δφ = 4 * I₀ * (Real.cos (Δφ / 2)) ^ 2 ∧
    0 ≤ realInterferenceEnvelope I₀ Δφ ∧
    realInterferenceEnvelope I₀ 0 = 4 * I₀ ∧
    realInterferenceEnvelope I₀ Real.pi = 0 ∧
    realInterferenceEnvelope I₀ (-Δφ) = realInterferenceEnvelope I₀ Δφ := by
  have hHalf : realInterferenceEnvelope I₀ Δφ = 4 * I₀ * (Real.cos (Δφ / 2)) ^ 2 := by
    unfold realInterferenceEnvelope
    have hCos : Real.cos Δφ = 2 * (Real.cos (Δφ / 2)) ^ 2 - 1 := by
      have hArg : Δφ = 2 * (Δφ / 2) := by ring
      conv_lhs => rw [hArg, Real.cos_two_mul]
    rw [hCos]
    ring
  refine ⟨hHalf, ?_, ?_, ?_, ?_⟩
  · rw [hHalf]
    exact mul_nonneg (mul_nonneg (by norm_num) hI₀) (sq_nonneg _)
  · unfold realInterferenceEnvelope
    rw [Real.cos_zero]
    ring
  · unfold realInterferenceEnvelope
    rw [Real.cos_pi]
    ring
  · unfold realInterferenceEnvelope
    rw [Real.cos_neg]

end ContinuousAharonovBohmInterference

-- ============================================================================
-- SECTION 3: Operator Bridge to the (5,5) Möbius Horizon Capacitor & Non-Abelian Braiding
-- ============================================================================

section MoebiusCapacitorAharonovBohmBridge

/-- Explicit $10 \times 10$ destructive Aharonov–Bohm interference projector
$P_-(\mathcal{T}_{5,5}) = I_{10} - P_+(\mathcal{T}_{5,5})$ projecting onto the 5-dimensional
$\Delta\varphi = \pi$ (half-flux, $\mathcal{T}_{5,5} = -1$) mirror sector $Q_0^\perp \subset \mathbb{R}^{10}$. -/
def krein10MirrorProjector : Matrix (Fin 10) (Fin 10) ℝ :=
  1 - krein10HorizonProjector

/-- **Möbius Capacitor as $(5,5)$ Aharonov–Bohm Interference Splitting (`moebius_capacitor_aharonov_bohm_interference_trace_laws`):**
On the 10-dimensional $(5,5)$ split-signature horizon:
1. $P_+(\mathcal{T}_{5,5}) + P_-(\mathcal{T}_{5,5}) = I_{10}$ (resolution of unity into
   constructive $\Delta\varphi = 0$ and destructive $\Delta\varphi = \pi$ sectors);
2. $P_+(\mathcal{T}_{5,5}) - P_-(\mathcal{T}_{5,5}) = \mathcal{T}_{5,5}$ (the Möbius twist is the
   relative Aharonov–Bohm parity operator);
3. $\mathrm{Tr}(P_+(\mathcal{T}_{5,5})) = 5$ and $\mathrm{Tr}(P_-(\mathcal{T}_{5,5})) = 5$
   (5 constructive modes on $Q_0$ and 5 destructive modes on $Q_0^\perp$). -/
theorem moebius_capacitor_aharonov_bohm_interference_trace_laws :
    krein10HorizonProjector + krein10MirrorProjector = 1 ∧
    krein10HorizonProjector - krein10MirrorProjector = krein10Twist ∧
    Matrix.trace krein10HorizonProjector = 5 ∧
    Matrix.trace krein10MirrorProjector = 5 := by
  have hCap := krein10_horizon_trace_capacitance_eq_five
  refine ⟨?_, ?_, hCap.2.2.2.2.1, ?_⟩
  · unfold krein10MirrorProjector
    abel
  · unfold krein10MirrorProjector krein10HorizonProjector krein10Twist
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i.val < 5 <;> simp [Matrix.diagonal_apply_eq, hi]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  · unfold krein10MirrorProjector
    rw [Matrix.trace_sub, hCap.2.2.2.2.1]
    have hTrOne : Matrix.trace (1 : Matrix (Fin 10) (Fin 10) ℝ) = 10 := by
      have h10 := hCap.2.2.2.2.2
      rw [hCap.2.2.2.1] at h10
      linarith
    rw [hTrOne]
    norm_num

/-- Non-abelian $2 \times 2$ $\mathbb{Z}_2$ Aharonov–Bohm phase holonomy matrix
$Z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$ assigning phase $+1$ ($\Delta\varphi = 0$)
to branch $0$ and phase $-1$ ($\Delta\varphi = \pi$) to branch $1$. -/
def abHolonomyZ : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,  0;
     0, -1]

/-- Non-abelian $2 \times 2$ inter-branch 't Hooft tunneling matrix
$X = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ exchanging the two interferometer arms. -/
def abHolonomyX : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1;
     1, 0]

/-- **Non-Abelian $\mathbb{Z}_2$ Wilson–'t Hooft Braiding (`abHolonomyZ_X_braiding`):**
The half-flux Aharonov–Bohm holonomy $Z$ and the branch-exchange 't Hooft operator $X$
satisfy $Z^2 = I_2$, $X^2 = I_2$, and anti-commute ($Z X = - X Z$, equivalently
$X Z X = -Z$). -/
theorem abHolonomyZ_X_braiding :
    abHolonomyZ * abHolonomyZ = 1 ∧
    abHolonomyX * abHolonomyX = 1 ∧
    abHolonomyZ * abHolonomyX = -(abHolonomyX * abHolonomyZ) ∧
    abHolonomyX * abHolonomyZ * abHolonomyX = -abHolonomyZ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [abHolonomyZ]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [abHolonomyX]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [abHolonomyZ, abHolonomyX]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [abHolonomyZ, abHolonomyX]

/-- Explicit non-commutativity witness for the `Matrix (Fin 2) (Fin 2) ℝ` Aharonov–Bohm
holonomy carrier: $Z X \neq X Z$. -/
theorem abHolonomy_noncommutative :
    abHolonomyZ * abHolonomyX ≠ abHolonomyX * abHolonomyZ := by
  intro hEq
  have h01 := congr_fun (congr_fun hEq 0) 1
  simp [abHolonomyZ, abHolonomyX] at h01
  exact (by norm_num : (1 : ℝ) ≠ -1) h01

end MoebiusCapacitorAharonovBohmBridge

-- ============================================================================
-- SECTION 4: Aharonov–Bohm Partial-Wave Spectrum & Scattering Cross-Section Factor
-- ============================================================================

noncomputable section PartialWaveSpectrumAndScattering

/-- Shifted canonical-to-kinetic azimuthal angular momentum eigenvalue
$\nu_m(\alpha) = m + \alpha$ ($m \in \mathbb{Z}$, $\alpha = \Phi / \Phi_0 \in \mathbb{R}$)
for a charged particle orbiting a singular magnetic flux line in the Coulomb gauge
$A_\theta = \Phi / (2\pi r)$ (Aharonov & Bohm 1959, Section 3). -/
def abShiftedAngularMomentum (m : ℤ) (α : ℝ) : ℝ :=
  (m : ℝ) + α

/-- Dimensionless rotational kinetic energy / centrifugal barrier eigenvalue
$E_m(\alpha) = (m + \alpha)^2$ of the $m$-th partial wave in the Aharonov–Bohm Hamiltonian. -/
def abRotationalEnergy (m : ℤ) (α : ℝ) : ℝ :=
  ((m : ℝ) + α) ^ 2

/-- **Aharonov–Bohm Partial-Wave Spectrum, Byers–Yang Periodicity, & Half-Flux Kramers Doublet
(`abRotationalEnergy_flux_periodicity_and_chirality`):**
For all angular momentum quantum numbers $m, k \in \mathbb{Z}$ and normalized magnetic flux
$\alpha = \Phi / \Phi_0 \in \mathbb{R}$:
1. **Byers–Yang Gauge Periodicity:** Shifting the magnetic flux by $k$ flux quanta
   ($\alpha \mapsto \alpha + k$) is compensated by the single-valued gauge transformation
   $\psi \mapsto e^{-ik\theta}\psi$ ($m \mapsto m - k$):
   $$E_{m - k}(\alpha + k) = E_m(\alpha);$$
2. **Chiral / Time-Reversal Splitting:** Opposite partial waves $\pm m$ split linearly in both
   $m$ and $\alpha$:
   $$E_m(\alpha) - E_{-m}(\alpha) = 4 m \alpha;$$
3. **Half-Flux ($\alpha = 1/2$, $\Delta\varphi = \pi$) Kramers Doublet Symmetry:**
   At half-integer flux $\alpha = 1/2$, the partial wave $m$ is strictly degenerate with $-m - 1$:
   $$E_m\!\left(\tfrac{1}{2}\right) = E_{-m - 1}\!\left(\tfrac{1}{2}\right);$$
4. **Strict Zero-Point Energy Gap at Half-Flux:**
   The degenerate ground-state doublet $m \in \{0, -1\}$ at $\alpha = 1/2$ has strictly positive
   rotational energy $E_0(1/2) = E_{-1}(1/2) = 1/4$. -/
theorem abRotationalEnergy_flux_periodicity_and_chirality (m k : ℤ) (α : ℝ) :
    abRotationalEnergy (m - k) (α + (k : ℝ)) = abRotationalEnergy m α ∧
    abRotationalEnergy m α - abRotationalEnergy (-m) α = 4 * (m : ℝ) * α ∧
    abRotationalEnergy m (1 / 2) = abRotationalEnergy (-m - 1) (1 / 2) ∧
    abRotationalEnergy 0 (1 / 2) = 1 / 4 ∧
    abRotationalEnergy (-1) (1 / 2) = 1 / 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold abRotationalEnergy
    push_cast
    ring
  · unfold abRotationalEnergy
    push_cast
    ring
  · unfold abRotationalEnergy
    push_cast
    ring
  · unfold abRotationalEnergy
    norm_num
  · unfold abRotationalEnergy
    norm_num

/-- Universal magnetic-flux modulation factor $S(\alpha) = \sin^2(\pi\alpha)$ governing the exact
Aharonov–Bohm differential scattering cross section
$\frac{d\sigma}{d\theta} = \frac{\lambda}{2\pi} \frac{\sin^2(\pi\alpha)}{1 - \cos\theta}$
derived in Section 3 of Aharonov & Bohm (1959). -/
def abScatteringFluxFactor (α : ℝ) : ℝ :=
  (Real.sin (Real.pi * α)) ^ 2

/-- **Aharonov–Bohm Scattering Cross-Section Flux Laws (`abScatteringFluxFactor_laws`):**
For any normalized flux $\alpha = \Phi / \Phi_0 \in \mathbb{R}$ and integer $k \in \mathbb{Z}$:
1. **Transparency at Quantized Dirac Flux ($\alpha = k \in \mathbb{Z}$):**
   $S(k) = \sin^2(\pi k) = 0$ (no Aharonov–Bohm scattering at integer flux quanta);
2. **Maximal Scattering Resonance at Half-Flux ($\alpha = 1/2$, $\Delta\varphi = \pi$):**
   $S(1/2) = \sin^2(\pi / 2) = 1$;
3. **Unit-Flux Periodicity:**
   $S(\alpha + 1) = S(\alpha)$;
4. **Unitary Forward-Scattering Complementarity:**
   $S(\alpha) + \cos^2(\pi\alpha) = 1$. -/
theorem abScatteringFluxFactor_laws (α : ℝ) (k : ℤ) :
    abScatteringFluxFactor (k : ℝ) = 0 ∧
    abScatteringFluxFactor (1 / 2) = 1 ∧
    abScatteringFluxFactor (α + 1) = abScatteringFluxFactor α ∧
    abScatteringFluxFactor α + (Real.cos (Real.pi * α)) ^ 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold abScatteringFluxFactor
    have hArg : Real.pi * (k : ℝ) = (k : ℝ) * Real.pi := mul_comm _ _
    rw [hArg, Real.sin_int_mul_pi, sq, mul_zero]
  · unfold abScatteringFluxFactor
    have hArg : Real.pi * (1 / 2 : ℝ) = Real.pi / 2 := by ring
    rw [hArg, Real.sin_pi_div_two]
    norm_num
  · unfold abScatteringFluxFactor
    have hArg : Real.pi * (α + 1) = Real.pi * α + Real.pi := by ring
    rw [hArg, Real.sin_add_pi, neg_sq]
  · unfold abScatteringFluxFactor
    exact Real.sin_sq_add_cos_sq (Real.pi * α)

end PartialWaveSpectrumAndScattering

end InfoGeometry.Canonical.AharonovBohmGaugeCoboundaryInterferencePoset
