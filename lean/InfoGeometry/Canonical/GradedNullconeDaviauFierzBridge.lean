/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Core.PeirceDecomposition
import InfoGeometry.Dynamics.MoebiusTrifactorFlows
import InfoGeometry.Clifford.LochakRodichevFierzKrein

noncomputable section

open scoped BigOperators
open Matrix
open InfoGeometry.Clifford.LochakRodichevFierzKrein
open InfoGeometry.Clifford.DaviauChiralPeirceSU2

private abbrev DaviauRealSpinor := InfoGeometry.Algebra.FiniteSpin.Vec8R

namespace InfoGeometry.Canonical.GradedNullconeDaviauFierzBridge

/-! ### Part 1: Parabolic Peirce Shear via the Existing Unipotent Flow -/

/-- A Peirce `01` corner generates an elementary unipotent conjugation that
shears the source idempotent by the corner itself. -/
theorem peirce01_parabolic_conjugates_idempotent
    {B : Type*} [Ring B] [Algebra ℝ B] (p ω : B) (hp : p * p = p) (t : ℝ) :
    InfoGeometry.Dynamics.MoebiusFlow.parabolicFlow
        (InfoGeometry.Core.PeirceDecomposition.component01 p ω) t * p *
      InfoGeometry.Dynamics.MoebiusFlow.parabolicFlow
        (InfoGeometry.Core.PeirceDecomposition.component01 p ω) (-t) =
      p + t • InfoGeometry.Core.PeirceDecomposition.component01 p ω := by
  let n := InfoGeometry.Core.PeirceDecomposition.component01 p ω
  have hpn : p * n = 0 := by
    dsimp [n, InfoGeometry.Core.PeirceDecomposition.component01,
      InfoGeometry.Core.PeirceDecomposition.peirceCorner,
      InfoGeometry.Core.PeirceDecomposition.complementIdempotent]
    have hpq : p * (1 - p) = 0 := by
      rw [mul_sub, mul_one, hp, sub_self]
    calc
      p * ((1 - p) * ω * p) = (p * (1 - p)) * ω * p := by noncomm_ring
      _ = 0 := by rw [hpq]; simp
  have hnp : n * p = n := by
    dsimp [n, InfoGeometry.Core.PeirceDecomposition.component01,
      InfoGeometry.Core.PeirceDecomposition.peirceCorner,
      InfoGeometry.Core.PeirceDecomposition.complementIdempotent]
    calc
      ((1 - p) * ω * p) * p = (1 - p) * ω * (p * p) := by noncomm_ring
      _ = (1 - p) * ω * p := by rw [hp]
  have hn2 : n * n = 0 :=
    InfoGeometry.Core.PeirceDecomposition.component01_sq_eq_zero p ω hp
  have htnp : (t • n) * p = t • n := by
    rw [Algebra.smul_mul_assoc, hnp]
  have hpnt : p * ((-t) • n) = 0 := by
    rw [Algebra.mul_smul_comm, hpn, smul_zero]
  have hcross : (t • n) * ((-t) • n) = 0 := by
    rw [InfoGeometry.Dynamics.MoebiusFlow.smul_mul_smul, hn2, smul_zero]
  change (1 + t • n) * p * (1 + (-t) • n) = p + t • n
  calc
    (1 + t • n) * p * (1 + (-t) • n) = (p + t • n) * (1 + (-t) • n) := by
      rw [add_mul, one_mul, htnp]
    _ = p * 1 + p * ((-t) • n) + (t • n) * 1 +
        (t • n) * ((-t) • n) := by
      simp only [mul_add, add_mul]
      abel
    _ = p + t • n := by rw [mul_one, hpnt, hcross]; simp

/-! ### Part 2: Two-Sheet Complex Fierz Readouts and Unitary Symmetry -/

/-- Doubled chiral Dirac/Daviau spinor `(ψ₊, ψ₋) ∈ ℂ² × ℂ²` on the dual null sheets `N₊ ⊕ N₋`. -/
abbrev ChiralDiracSpinor := EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)

/-- Scalar readout `Ω₁(ψ) = 2 Re⟨ψ₊, ψ₋⟩` on the two-sheet carrier. -/
def fierzScalar (ψ : ChiralDiracSpinor) : ℝ :=
  2 * (inner ℂ ψ.1 ψ.2).re

/-- Pseudoscalar readout `Ω₂(ψ) = 2 Im⟨ψ₊, ψ₋⟩` on the two-sheet carrier. -/
def fierzPseudoscalar (ψ : ChiralDiracSpinor) : ℝ :=
  2 * (inner ℂ ψ.1 ψ.2).im

/-- Positive Hilbert norm density `j⁰(ψ) = ‖ψ₊‖² + ‖ψ₋‖²`. -/
def kreinProbDensity (ψ : ChiralDiracSpinor) : ℝ :=
  ‖ψ.1‖ ^ 2 + ‖ψ.2‖ ^ 2

/-- Chiral axial density `k⁰(ψ) = ‖ψ₊‖² - ‖ψ₋‖²` (cut expectation `⟨ψ, Γ ψ⟩_ℋ`). -/
def chiralAxialDensity (ψ : ChiralDiracSpinor) : ℝ :=
  ‖ψ.1‖ ^ 2 - ‖ψ.2‖ ^ 2

/-- Read the repository's real Daviau spinor as two complex Weyl coordinates. This is a linear
readout into the proposed complex carrier, not an identification of the full real Clifford
algebra with a complex matrix algebra. -/
def daviauWeylReadout (Φ : DaviauRealSpinor) : ChiralDiracSpinor :=
  (WithLp.toLp 2 (weylXi Φ), WithLp.toLp 2 (weylEta Φ))

/-- Daviau's explicit left-chiral family has zero left Weyl readout in this owner's
coordinate convention. The nonzero component lies in the opposite slot. -/
theorem daviauPhiL_weylXi_eq_zero (a : Fin 4 → ℝ) :
    (daviauWeylReadout (daviauPhiL a)).1 = 0 := by
  apply (WithLp.ext_iff 2).2
  funext i
  fin_cases i <;> apply Complex.ext <;>
    simp [daviauWeylReadout, weylXi, phiToPsi, daviauPhiL]

/-- Daviau's explicit right-chiral family has zero right Weyl readout. -/
theorem daviauPhiR_weylEta_eq_zero (b : Fin 4 → ℝ) :
    (daviauWeylReadout (daviauPhiR b)).2 = 0 := by
  apply (WithLp.ext_iff 2).2
  funext i
  fin_cases i <;> simp [daviauWeylReadout, weylEta, phiToPsi, daviauPhiR]

/-- Cross-owner convention check: the repository's family named `daviauPhiL` satisfies its
left Peirce predicate, while the `phiToPsi` coordinates put it in the `eta` slot. -/
theorem daviauPhiL_chiral_readout_convention (a : Fin 4 → ℝ) :
    IsLeftChiralSpinor ⟨2, by decide⟩ (daviauPhiL a) ∧
      (daviauWeylReadout (daviauPhiL a)).1 = 0 :=
  ⟨daviauPhiL_isLeftChiral a, daviauPhiL_weylXi_eq_zero a⟩

/-- Cross-owner convention check for the explicit right family and the `xi` slot. -/
theorem daviauPhiR_chiral_readout_convention (b : Fin 4 → ℝ) :
    IsRightChiralSpinor ⟨2, by decide⟩ (daviauPhiR b) ∧
      (daviauWeylReadout (daviauPhiR b)).2 = 0 :=
  ⟨daviauPhiR_isRightChiral b, daviauPhiR_weylEta_eq_zero b⟩

/-- The explicit left family has vanishing scalar/pseudoscalar Fierz invariant. -/
theorem daviauPhiL_readout_fierz_invariant_zero (a : Fin 4 → ℝ) :
    fierzScalar (daviauWeylReadout (daviauPhiL a)) ^ 2 +
      fierzPseudoscalar (daviauWeylReadout (daviauPhiL a)) ^ 2 = 0 := by
  have hzero := daviauPhiL_weylXi_eq_zero a
  simp [fierzScalar, fierzPseudoscalar, hzero]

/-- The explicit right family has vanishing scalar/pseudoscalar Fierz invariant. -/
theorem daviauPhiR_readout_fierz_invariant_zero (b : Fin 4 → ℝ) :
    fierzScalar (daviauWeylReadout (daviauPhiR b)) ^ 2 +
      fierzPseudoscalar (daviauWeylReadout (daviauPhiR b)) ^ 2 = 0 := by
  have hzero := daviauPhiR_weylEta_eq_zero b
  simp [fierzScalar, fierzPseudoscalar, hzero]

/-- The readout cross inner product is the existing Weyl pairing. -/
theorem daviauWeylReadout_cross_inner (Φ : DaviauRealSpinor) :
    inner ℂ (daviauWeylReadout Φ).1 (daviauWeylReadout Φ).2 =
      weylCrossInner Φ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [daviauWeylReadout, weylCrossInner, dotProduct, Fin.sum_univ_two]
  ; ring

/-- The complex scalar readout agrees with the real Daviau scalar bilinear. -/
theorem daviauWeylReadout_fierzScalar (Φ : DaviauRealSpinor) :
    fierzScalar (daviauWeylReadout Φ) = omega1 Φ := by
  rw [fierzScalar, daviauWeylReadout_cross_inner, weylCrossInner_re]
  ring

/-- The pseudoscalar readout has the owner convention's opposite sign. -/
theorem daviauWeylReadout_fierzPseudoscalar (Φ : DaviauRealSpinor) :
    fierzPseudoscalar (daviauWeylReadout Φ) = -omega2 Φ := by
  rw [fierzPseudoscalar, daviauWeylReadout_cross_inner, weylCrossInner_im]
  ring

/-- Transport of the squared complex Fierz invariant to the real Daviau bilinears. -/
theorem daviauWeylReadout_fierzInvariant (Φ : DaviauRealSpinor) :
    fierzScalar (daviauWeylReadout Φ) ^ 2 +
        fierzPseudoscalar (daviauWeylReadout Φ) ^ 2 =
      omega1 Φ ^ 2 + omega2 Φ ^ 2 := by
  rw [daviauWeylReadout_fierzScalar, daviauWeylReadout_fierzPseudoscalar]
  ring

/-- Transport the complex readout estimate to the existing real Daviau currents. -/
theorem daviauWeylReadout_current_bound (Φ : DaviauRealSpinor) :
    fierzScalar (daviauWeylReadout Φ) ^ 2 +
        fierzPseudoscalar (daviauWeylReadout Φ) ^ 2 ≤
      (electricCurrentJ Φ 0) ^ 2 - (axialCurrentSigma Φ 0) ^ 2 := by
  rw [daviauWeylReadout_fierzInvariant]
  exact lochak_real_chiral_current_bound Φ

/-- A positive readout invariant forces nonzero content in both real Weyl sectors. -/
theorem daviauWeylReadout_positive_invariant_requires_both_real_sectors
    (Φ : DaviauRealSpinor)
    (h : 0 < fierzScalar (daviauWeylReadout Φ) ^ 2 +
      fierzPseudoscalar (daviauWeylReadout Φ) ^ 2) :
    realWeylLeft Φ ≠ 0 ∧ realWeylRight Φ ≠ 0 := by
  apply both_real_weyl_sectors_nonzero_of_positive_fierz_norm
  rw [← daviauWeylReadout_fierzInvariant]
  exact h

/-- The readout's zero Fierz invariant is equivalent to the existing Weyl
cross-orthogonality condition. -/
theorem daviauWeylReadout_lightcone_orthogonality (Φ : DaviauRealSpinor) :
    fierzScalar (daviauWeylReadout Φ) ^ 2 +
        fierzPseudoscalar (daviauWeylReadout Φ) ^ 2 = 0 ↔
      inner ℂ (daviauWeylReadout Φ).1 (daviauWeylReadout Φ).2 = 0 := by
  rw [daviauWeylReadout_fierzInvariant, daviauWeylReadout_cross_inner]
  exact lochak_eq47_lightcone_orthogonality Φ

/-- **Two-Sheet Fierz–Takabayasi Identity and Decoupling**:
1. Exact Fierz–Takabayasi identity: `Ω₁² + Ω₂² = 4 ‖⟨ψ₊, ψ₋⟩‖²`.
2. Cauchy–Schwarz gives the bound by `(j⁰)² - (k⁰)²`.
3. If either sheet is zero, the scalar/pseudoscalar invariant vanishes and
   `(k⁰)² = (j⁰)²`. This does not assert a field equation or a Proca fusion result. -/
theorem two_sheet_fierz_takabayasi_and_decoupling (ψ : ChiralDiracSpinor) :
    fierzScalar ψ ^ 2 + fierzPseudoscalar ψ ^ 2 = 4 * ‖inner ℂ ψ.1 ψ.2‖ ^ 2 ∧
    fierzScalar ψ ^ 2 + fierzPseudoscalar ψ ^ 2 ≤
      kreinProbDensity ψ ^ 2 - chiralAxialDensity ψ ^ 2 ∧
    (ψ.1 = 0 ∨ ψ.2 = 0 →
      fierzScalar ψ ^ 2 + fierzPseudoscalar ψ ^ 2 = 0 ∧
      chiralAxialDensity ψ ^ 2 = kreinProbDensity ψ ^ 2) := by
  have hMod : fierzScalar ψ ^ 2 + fierzPseudoscalar ψ ^ 2 = 4 * ‖inner ℂ ψ.1 ψ.2‖ ^ 2 := by
    unfold fierzScalar fierzPseudoscalar
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hCS : ‖inner ℂ ψ.1 ψ.2‖ ^ 2 ≤ ‖ψ.1‖ ^ 2 * ‖ψ.2‖ ^ 2 := by
    calc ‖inner ℂ ψ.1 ψ.2‖ ^ 2 ≤ (‖ψ.1‖ * ‖ψ.2‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm ψ.1 ψ.2) 2
      _ = ‖ψ.1‖ ^ 2 * ‖ψ.2‖ ^ 2 := by ring
  have hDiff : kreinProbDensity ψ ^ 2 - chiralAxialDensity ψ ^ 2 =
      4 * (‖ψ.1‖ ^ 2 * ‖ψ.2‖ ^ 2) := by
    unfold kreinProbDensity chiralAxialDensity
    ring
  refine ⟨hMod, ?_, ?_⟩
  · rw [hMod, hDiff]
    linarith
  · intro hNull
    rcases hNull with h1 | h2
    · have h0 : inner ℂ ψ.1 ψ.2 = 0 := by rw [h1, inner_zero_left]
      have hNorm0 : ‖ψ.1‖ = 0 := by rw [h1, norm_zero]
      refine ⟨by rw [hMod, h0, norm_zero]; norm_num, ?_⟩
      unfold kreinProbDensity chiralAxialDensity
      rw [hNorm0]; ring
    · have h0 : inner ℂ ψ.1 ψ.2 = 0 := by rw [h2, inner_zero_right]
      have hNorm0 : ‖ψ.2‖ = 0 := by rw [h2, norm_zero]
      refine ⟨by rw [hMod, h0, norm_zero]; norm_num, ?_⟩
      unfold kreinProbDensity chiralAxialDensity
      rw [hNorm0]; ring

/-- A nonzero scalar/pseudoscalar Fierz invariant requires both chiral components.
The converse is not asserted: the two nonzero components may be orthogonal. -/
theorem nonzero_fierz_invariant_requires_both_sheets (ψ : ChiralDiracSpinor)
    (h : fierzScalar ψ ^ 2 + fierzPseudoscalar ψ ^ 2 ≠ 0) :
    ψ.1 ≠ 0 ∧ ψ.2 ≠ 0 := by
  constructor
  · intro h₁
    apply h
    simp [fierzScalar, fierzPseudoscalar, h₁]
  · intro h₂
    apply h
    simp [fierzScalar, fierzPseudoscalar, h₂]

/-- Non-commutativity witness for complex 2×2 matrix operators (Gate 2.4 / Trap T16). -/
theorem matrix2_complex_noncommutative_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  use !![0, 1; 0, 0], !![0, 0; 1, 0]
  intro h
  have h00 : (!![0, 1; 0, 0] * !![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
      (!![0, 0; 1, 0] * !![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [h]
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Simultaneous unitary invariance of the complex chiral cross-pairing:
any `U ∈ U(2)` acting on both chiral sheets
`ψ₊ ↦ U ψ₊`, `ψ₋ ↦ U ψ₋` preserves the complex Fierz pairing `⟨ψ₊, ψ₋⟩ = ∑ conj(ψ₊ᵢ) ψ₋ᵢ`
and therefore preserves both real and imaginary readouts. -/
theorem simultaneous_unitary_preserves_chiral_pairing
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (u v : Fin 2 → ℂ) :
    dotProduct (star (U.mulVec u)) (U.mulVec v) = dotProduct (star u) v := by
  have hStar : star (U.mulVec u) = (Uᴴ).vecMul (star u) := by
    ext j
    simp only [Pi.star_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, star_sum, star_mul']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  rw [hStar, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

end InfoGeometry.Canonical.GradedNullconeDaviauFierzBridge
