/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge
import InfoGeometry.Physics.CrankingParity
import InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Geometromagnetogravity Cranking & Nonlinear Self-Interacting Dirac Vacuum

Formalizes the three-way synthesis connecting Einstein–Cartan spin-torsion cranking, the
Fierz–Kofink–Rodichev–Daviau null current identities, Yvon–Takabayasi chiral invariance, and
Inglis cranking Routhian destabilization — reusing committed repository owners
`DiracSpinCasimirNambuModulesBridge`, `CrankingParity`, and
`DoubledMinkowskiRotatingSpinInstability`:

1. **Chiral Null Currents & Fierz–Kofink–Rodichev Identities**:
   On a two-sheeted real Dirac bispinor `((a₁, b₁, a₂, b₂), (c₁, d₁, c₂, d₂)) ∈ ℝ⁴ × ℝ⁴`,
   defining vector current `J = j_L + j_R` and axial torsion-cranking current `J₅ = j_L - j_R`
   yields `η(j_L, j_L) = η(j_R, j_R) = 0`, `η(J, J) = Ω₁² + Ω₂²`, `η(J₅, J₅) = -(Ω₁² + Ω₂²)`,
   `η(J, J₅) = 0`, the Einstein–Cartan axial torsion self-interaction identity
   `-η(κ_EC J₅, J₅) = κ_EC (Ω₁² + Ω₂²)`, and `diracVectorLift j` square-zero nilpotency.
2. **Yvon–Takabayasi Chiral Invariance & Cranked Vacuum Condensation**:
   Rotations by chiral angle `β` preserve `Ω₁² + Ω₂²`, and when gravitomagnetic cranking
   `ω_crank` exceeds the bare threshold `μ₀`, the condensed vacuum `ρ_*² = (ω_crank² - μ₀²) / λ`
   achieves a strictly lower global minimum `V_vac(ρ_*) = -(ω_crank² - μ₀²)² / (4 λ) < V_vac(0)`.
3. **Inglis Cranking Routhian Bridge**:
   Connects `DoubledMinkowskiRotatingSpinInstability.rotatingSpinHamiltonian J Ω` directly to
   `CrankingParity.routhian`, recovering the singlet and co-rotating triplet spectrum `-(3/4)J`
   and `(1/4)J - Ω` via `CrankingParity.routhian_joint_eigenvector`.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE THEOREMS
* `fierz_kofink_rodichev_chiral_null_current_identities`
* `chiralNullCurrent_diracLift_square_zero`
* `rotatingSpinHamiltonian_eq_cranking_routhian`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* `yvon_takabayasi_chiral_invariance_and_cranked_vacuum_condensation` (under `μ₀² < ω_crank²`, `0 < lam`)

#### BUCKET 3: OPEN CLOSURE DEBT
* Dynamic continuum PDE existence for curved Einstein–Cartan spinor-torsion field equations
  remains outside this finite-algebraic canonical bridge.
-/

noncomputable section

namespace InfoGeometry.Canonical.GeometroMagnetoGravityCrankingDirac

open InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge
open InfoGeometry.Physics.CrankingParity
open InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability

/-! ### Part 1: Two-Sheeted Chiral Null Currents & Fierz–Kofink–Rodichev Identities -/

/-- Minkowski inner product `η(u, v) = u₀ v₀ - u₁ v₁ - u₂ v₂ - u₃ v₃` on `ℝ^{1,3}`. -/
def minkPair (u v : Fin 4 → ℝ) : ℝ :=
  u 0 * v 0 - u 1 * v 1 - u 2 * v 2 - u 3 * v 3

/-- Realified Weyl null 4-current `j(a₁, b₁, a₂, b₂) ∈ ℝ^{1,3}` of a 4-component real chiral
spinor `(a₁ + ε b₁, a₂ + ε b₂)`. -/
def chiralNullCurrent (a₁ b₁ a₂ b₂ : ℝ) : Fin 4 → ℝ :=
  ![ (a₁ ^ 2 + b₁ ^ 2 + a₂ ^ 2 + b₂ ^ 2) / 2,
     a₁ * a₂ + b₁ * b₂,
     b₁ * a₂ - a₁ * b₂,
     (a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2) / 2 ]

/-- Dirac vector 4-current `J^μ = j_L^μ + j_R^μ`. -/
def diracVectorCurrent (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : ℝ) : Fin 4 → ℝ :=
  fun μ => chiralNullCurrent a₁ b₁ a₂ b₂ μ + chiralNullCurrent c₁ d₁ c₂ d₂ μ

/-- Dirac axial spin / torsion-cranking 4-current `J₅^μ = j_L^μ - j_R^μ`. -/
def diracAxialCurrent (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : ℝ) : Fin 4 → ℝ :=
  fun μ => chiralNullCurrent a₁ b₁ a₂ b₂ μ - chiralNullCurrent c₁ d₁ c₂ d₂ μ

/-- Real scalar bilinear invariant `Ω₁ = Ψ̄ Ψ = a₁ c₂ - b₁ d₂ - a₂ c₁ + b₂ d₁`. -/
def diracScalarOmega1 (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : ℝ) : ℝ :=
  a₁ * c₂ - b₁ * d₂ - a₂ * c₁ + b₂ * d₁

/-- Real pseudoscalar bilinear invariant `Ω₂ = Ψ̄ γ⁵ Ψ = a₁ d₂ + b₁ c₂ - a₂ d₁ - b₂ c₁`. -/
def diracPseudoscalarOmega2 (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : ℝ) : ℝ :=
  a₁ * d₂ + b₁ * c₂ - a₂ * d₁ - b₂ * c₁

/-- **Theorem 1 (Fierz–Kofink–Rodichev Identities & Einstein–Cartan Torsion Cranking)**:
Both chiral currents `j_L, j_R` are null, `η(J, J) = Ω₁² + Ω₂²`, `η(J₅, J₅) = -(Ω₁² + Ω₂²)`,
`η(J, J₅) = 0`, and substituting `S = κ_EC J₅` yields `-η(S, J₅) = κ_EC (Ω₁² + Ω₂²)`. -/
theorem fierz_kofink_rodichev_chiral_null_current_identities
    (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC : ℝ) :
    let jL := chiralNullCurrent a₁ b₁ a₂ b₂
    let jR := chiralNullCurrent c₁ d₁ c₂ d₂
    let J := diracVectorCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    let J₅ := diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    let S : Fin 4 → ℝ := fun μ => κ_EC * J₅ μ
    let Ω₁ := diracScalarOmega1 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    let Ω₂ := diracPseudoscalarOmega2 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    (minkPair jL jL = 0 ∧ minkPair jR jR = 0) ∧
    (minkPair J J = Ω₁ ^ 2 + Ω₂ ^ 2) ∧
    (minkPair J₅ J₅ = -(Ω₁ ^ 2 + Ω₂ ^ 2)) ∧
    (minkPair J J₅ = 0) ∧
    (-minkPair S J₅ = κ_EC * (Ω₁ ^ 2 + Ω₂ ^ 2)) := by
  dsimp
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    { simp [minkPair, chiralNullCurrent, diracVectorCurrent, diracAxialCurrent,
        diracScalarOmega1, diracPseudoscalarOmega2]
      ring }

/-- The Weyl chiral null current `j = chiralNullCurrent a₁ b₁ a₂ b₂` lifts via
`DiracSpinCasimirNambuModulesBridge.diracVectorLift` to a square-zero Dirac operator with
vanishing trace pairing `Tr(ι(j)²) = 0`. -/
theorem chiralNullCurrent_diracLift_square_zero (a₁ b₁ a₂ b₂ : ℝ) :
    let j := chiralNullCurrent a₁ b₁ a₂ b₂
    diracVectorLift j * diracVectorLift j = 0 ∧
    Matrix.trace (diracVectorLift j * diracVectorLift j) = 0 := by
  dsimp
  have hNull : lorentzInner (chiralNullCurrent a₁ b₁ a₂ b₂) (chiralNullCurrent a₁ b₁ a₂ b₂) = 0 :=
    (fierz_kofink_rodichev_chiral_null_current_identities a₁ b₁ a₂ b₂ 0 0 0 0 0).1.1
  exact diracVectorLift_null_trace_zero hNull

/-! ### Part 2: Yvon–Takabayasi Chiral Invariance & Cranked Nonlinear Dirac Vacuum Condensation -/

/-- Cranked nonlinear Dirac vacuum effective potential
`V_vac(ρ) = ½(μ₀² - ω_crank²) ρ² + ¼ λ ρ⁴`. -/
def crankedDiracVacuumPot (μ₀ ω_crank lam ρ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (μ₀ ^ 2 - ω_crank ^ 2) * ρ ^ 2 + (1 / 4 : ℝ) * lam * ρ ^ 4

/-- **Theorem 2 (Yvon–Takabayasi Chiral Invariance & Cranked Nonlinear Dirac Vacuum Mass Gap)**:
Chiral angle rotation leaves `Ω₁² + Ω₂²` invariant, and above the cranking threshold
`μ₀² < ω_crank²` (`0 < lam`), the condensed vacuum `ρ_*² = (ω_crank² - μ₀²) / lam` minimizes
`V_vac` strictly below `V_vac 0 = 0`. -/
theorem yvon_takabayasi_chiral_invariance_and_cranked_vacuum_condensation
    (Ω₁ Ω₂ β μ₀ ω_crank lam ρ ρ_star : ℝ)
    (hCrank : μ₀ ^ 2 < ω_crank ^ 2) (hLam : 0 < lam)
    (hStar : ρ_star ^ 2 = (ω_crank ^ 2 - μ₀ ^ 2) / lam) :
    let Ω₁' := Real.cos β * Ω₁ - Real.sin β * Ω₂
    let Ω₂' := Real.sin β * Ω₁ + Real.cos β * Ω₂
    (Ω₁' ^ 2 + Ω₂' ^ 2 = Ω₁ ^ 2 + Ω₂ ^ 2) ∧
    (0 < ρ_star ^ 2) ∧
    (crankedDiracVacuumPot μ₀ ω_crank lam ρ -
      crankedDiracVacuumPot μ₀ ω_crank lam ρ_star =
      (lam / 4) * (ρ ^ 2 - ρ_star ^ 2) ^ 2) ∧
    (crankedDiracVacuumPot μ₀ ω_crank lam ρ_star ≤
      crankedDiracVacuumPot μ₀ ω_crank lam ρ) ∧
    (crankedDiracVacuumPot μ₀ ω_crank lam ρ_star =
      -(ω_crank ^ 2 - μ₀ ^ 2) ^ 2 / (4 * lam)) ∧
    (crankedDiracVacuumPot μ₀ ω_crank lam ρ_star <
      crankedDiracVacuumPot μ₀ ω_crank lam 0) := by
  dsimp
  have hLamNe : lam ≠ 0 := ne_of_gt hLam
  have hYT : (Real.cos β * Ω₁ - Real.sin β * Ω₂) ^ 2 +
      (Real.sin β * Ω₁ + Real.cos β * Ω₂) ^ 2 = Ω₁ ^ 2 + Ω₂ ^ 2 := by
    calc (Real.cos β * Ω₁ - Real.sin β * Ω₂) ^ 2 +
          (Real.sin β * Ω₁ + Real.cos β * Ω₂) ^ 2
        = (Real.cos β ^ 2 + Real.sin β ^ 2) * (Ω₁ ^ 2 + Ω₂ ^ 2) := by ring
      _ = Ω₁ ^ 2 + Ω₂ ^ 2 := by rw [Real.cos_sq_add_sin_sq, one_mul]
  have hStarPos : 0 < ρ_star ^ 2 := by
    rw [hStar]
    exact div_pos (by linarith [hCrank]) hLam
  have hDiff : crankedDiracVacuumPot μ₀ ω_crank lam ρ -
      crankedDiracVacuumPot μ₀ ω_crank lam ρ_star =
      (lam / 4) * (ρ ^ 2 - ρ_star ^ 2) ^ 2 := by
    unfold crankedDiracVacuumPot
    have h4 : ρ ^ 4 = (ρ ^ 2) ^ 2 := by ring
    have h4s : ρ_star ^ 4 = (ρ_star ^ 2) ^ 2 := by ring
    rw [h4, h4s, hStar]
    field_simp [hLamNe]
    ring
  have hMinVal : crankedDiracVacuumPot μ₀ ω_crank lam ρ_star =
      -(ω_crank ^ 2 - μ₀ ^ 2) ^ 2 / (4 * lam) := by
    unfold crankedDiracVacuumPot
    have h4s : ρ_star ^ 4 = (ρ_star ^ 2) ^ 2 := by ring
    rw [h4s, hStar]
    field_simp [hLamNe]
    ring
  have hZeroVal : crankedDiracVacuumPot μ₀ ω_crank lam 0 = 0 := by
    unfold crankedDiracVacuumPot; ring
  refine ⟨hYT, hStarPos, hDiff, ?_, hMinVal, ?_⟩
  · have hNN : 0 ≤ (lam / 4) * (ρ ^ 2 - ρ_star ^ 2) ^ 2 :=
      mul_nonneg (by linarith [hLam]) (sq_nonneg _)
    linarith [hDiff, hNN]
  · rw [hMinVal, hZeroVal]
    have hNum : 0 < (ω_crank ^ 2 - μ₀ ^ 2) ^ 2 := sq_pos_of_pos (by linarith [hCrank])
    have hDen : 0 < 4 * lam := by linarith [hLam]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hNum) hDen

/-! ### Part 3: Inglis Cranking Routhian Bridge to Rotating Spin-Exchange Instability -/

private lemma crk_singlet_energy_eq (J Ω : ℝ) :
    -(3 / 4 : ℝ) * J - Ω * 0 = -(3 / 4 : ℝ) * J := by
  ring

private lemma crk_triplet_energy_eq (J Ω : ℝ) :
    (1 / 4 : ℝ) * J - Ω * 1 = (1 / 4 : ℝ) * J - Ω := by
  ring

/-- **Theorem 3 (Inglis Cranking Routhian Realization of Rotating Spin Instability)**:
`Matrix.toLin' (rotatingSpinHamiltonian J Ω)` is identically the `CrankingParity.routhian` of
`((J / 4 : ℝ) • spinExchange4)` and `totalSpinZ4` at cranking speed `Ω`, reproducing both the
singlet energy `-(3/4) * J` and the co-rotating `m = +1` triplet energy `(1/4) * J - Ω` via
`CrankingParity.routhian_joint_eigenvector`. -/
theorem rotatingSpinHamiltonian_eq_cranking_routhian (J Ω : ℝ) :
    let H := Matrix.toLin' ((J / 4 : ℝ) • spinExchange4)
    let L := Matrix.toLin' totalSpinZ4
    (Matrix.toLin' (rotatingSpinHamiltonian J Ω) = routhian H L Ω) ∧
    (routhian H L Ω singletState = (-(3 / 4 : ℝ) * J) • singletState) ∧
    (routhian H L Ω tripletPlusState = ((1 / 4 : ℝ) * J - Ω) • tripletPlusState) := by
  dsimp
  have hLin : Matrix.toLin' (rotatingSpinHamiltonian J Ω) =
      routhian (Matrix.toLin' ((J / 4 : ℝ) • spinExchange4)) (Matrix.toLin' totalSpinZ4) Ω := by
    unfold rotatingSpinHamiltonian routhian
    rw [map_sub, map_smul, map_smul]
  have hInst := real_rotating_frame_singlet_triplet_instability J 0
  have hInstT := real_rotating_frame_singlet_triplet_instability J Ω
  have hHs : (Matrix.toLin' ((J / 4 : ℝ) • spinExchange4)) singletState =
      (-(3 / 4 : ℝ) * J) • singletState := by
    rw [Matrix.toLin'_apply]
    have h0 := hInst.2.1
    simpa [rotatingSpinHamiltonian, zero_smul, sub_zero] using h0
  have hLs : (Matrix.toLin' totalSpinZ4) singletState = (0 : ℝ) • singletState := by
    rw [Matrix.toLin'_apply, zero_smul]
    calc
      totalSpinZ4.mulVec singletState = totalSpinZ4.mulVec (singletProj4.mulVec singletState) := by
        rw [hInst.1]
      _ = (totalSpinZ4 * singletProj4).mulVec singletState := Matrix.mulVec_mulVec _ _ _
      _ = (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ).mulVec singletState := by
        rw [real_singlet_triplet_decomposition_and_casimir_splitting.2.2.2.1]
      _ = 0 := Matrix.zero_mulVec _
  have hHt : (Matrix.toLin' ((J / 4 : ℝ) • spinExchange4)) tripletPlusState =
      ((1 / 4 : ℝ) * J) • tripletPlusState := by
    rw [Matrix.toLin'_apply]
    have h0 := hInst.2.2.2.2.1
    simpa [rotatingSpinHamiltonian, zero_smul, sub_zero] using h0
  have hLt : (Matrix.toLin' totalSpinZ4) tripletPlusState = (1 : ℝ) • tripletPlusState := by
    rw [Matrix.toLin'_apply, one_smul]
    exact hInstT.2.2.2.1
  refine ⟨hLin, ?_, ?_⟩
  · rw [routhian_joint_eigenvector _ _ Ω _ 0 singletState hHs hLs, crk_singlet_energy_eq]
  · rw [routhian_joint_eigenvector _ _ Ω _ 1 tripletPlusState hHt hLt, crk_triplet_energy_eq]

end InfoGeometry.Canonical.GeometroMagnetoGravityCrankingDirac
