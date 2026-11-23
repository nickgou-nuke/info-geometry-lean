/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Clifford.DaviauRealDirac8x8
import InfoGeometry.Clifford.LochakRodichevFierzKrein
import InfoGeometry.Clifford.DaviauBertrandCl3LorentzDilation
import InfoGeometry.Clifford.DaviauLochakDifferentialGauge

/-!
# Daviau–Bertrand `Cl₃`-Spinor Lorentz Lift (`GL(2,ℂ)` & `SL(2,ℂ) → SO⁺(1,3)`) on `ℝ⁸`

Completes the dynamical and Lorentz-covariant dictionary between Daviau's real `M₈(ℝ)` spinors
(`Vec8R`) and Daviau & Bertrand's (2018) `Cl₃ ≅ M₂(ℂ)` spinor representation `vec8ToCl3Spinor`:

1. **All-4-Component Paravector Current Identifications**:
   Proves for ALL `μ : Fin 4` (not just `μ = 0`) that
   - `Re Tr(φ φᴴ σ_μ) = J^μ(Φ)` and `paravectorMat (electricCurrentJ Φ) = 2 • (φ φᴴ)`;
   - `Re Tr(φ σ₃ φᴴ σ_μ) = Σ^μ(Φ)` and `paravectorMat (axialCurrentSigma Φ) = 2 • (φ σ₃ φᴴ)`.
2. **Exact Real Dirac / Quaternionic / Chiral Dictionary**:
   Defines the spatial reversal involution `cl3Hat` on `M₂(ℂ)` and proves:
   - `vec8ToCl3Spinor (Γ_μ Φ) = σ_μ * cl3Hat (vec8ToCl3Spinor Φ)` for all `μ : Fin 4`;
   - `vec8ToCl3Spinor (Γ⁰¹²³ Φ) = -i • vec8ToCl3Spinor Φ`;
   - `vec8ToCl3Spinor (P₃ Φ) = vec8ToCl3Spinor Φ * (i σ₃)`;
   - `vec8ToCl3Spinor (γ₅ Φ) = vec8ToCl3Spinor Φ * σ₃`.
3. **Real `8 × 8` Spinor Lift `lorentzDilationMat8 : M₂(ℂ) → M₈(ℝ)`**:
   Lifts left multiplication `φ ↦ M φ` to an associative monoid homomorphism `Mat2C →* Mat8R`
   embedding chiral gauge `chiralGaugeMat α = lorentzDilationMat8 ((cos α - i sin α) I₂)` while
   strictly commuting with `P₃`, `γ₅`, and Daviau's electric gauge `electricGaugeMat α`.
4. **Full `GL(2,ℂ)` Bilinear / Dirac Covariance & `SL(2,ℂ) → SO⁺(1,3)` Double Cover**:
   Proves `J^μ(L(M) Φ) = R(M) J(Φ)`, `Σ^μ(L(M) Φ) = R(M) Σ(Φ)`, `(Ω₁, Ω₂)` complex-determinant
   dilation, exact lowered Dirac intertwining
   `L((cl3Hat M)ᴴ) * Γ_μ * L(M) = ∑_ν R((cl3Hat M)ᴴ)^ν_μ • Γ_ν`,
   and the full spinor-level `SL(2,ℂ) → SO⁺(1,3)` double cover where `L(-I₂) = -I₈ ≠ I₈`
   while `R(-I₂) = I₄`.
-/

noncomputable section

open scoped ComplexConjugate
open Matrix Module
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Clifford.QuaternionPauliRealForm hiding Mat2C
open InfoGeometry.Clifford.DaviauRealDirac8x8
open InfoGeometry.Clifford.LochakRodichevFierzKrein
open InfoGeometry.Clifford.DaviauBertrandCl3LorentzDilation
open InfoGeometry.Clifford.DaviauLochakDifferentialGauge

namespace InfoGeometry.Clifford.DaviauBertrandSpinorLorentzLift

abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-! ### Trap T16 Noncommutativity Guards -/

/-- Explicit Trap T16 noncommutativity witnesses for both `M₂(ℂ)` and `M₈(ℝ)`. -/
theorem mat2C_and_mat8R_noncomm_guard :
    (∃ A B : Mat2C, A * B ≠ B * A) ∧ (∃ A B : Mat8R, A * B ≠ B * A) := by
  refine ⟨⟨sigma1, sigma2, ?_⟩, ⟨gammaR 0, gammaR 1, daviau_mat8_noncomm.1⟩⟩
  intro h
  have h01 := congrFun (congrFun h 0) 0
  simp [sigma1, sigma2, Matrix.mul_apply, Fin.sum_univ_two] at h01
  have him := congrArg Complex.im h01
  norm_num at him

/-! ### Section 1: Spatial-Reversal Conjugation `cl3Hat` on `M₂(ℂ)` -/

/-- Main spatial-reversal involution `φ ↦ φ̂ = σ₂ φ* σ₂` (equivalently `(adjugate φ)ᴴ`) in `Cl₃ ≅ M₂(ℂ)`. -/
def cl3Hat (φ : Mat2C) : Mat2C :=
  !![star (φ 1 1), -star (φ 1 0); -star (φ 0 1), star (φ 0 0)]

@[simp]
theorem cl3Hat_involutive (φ : Mat2C) : cl3Hat (cl3Hat φ) = φ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cl3Hat]

@[simp]
theorem cl3Hat_one : cl3Hat (1 : Mat2C) = (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cl3Hat]

theorem cl3Hat_add (A B : Mat2C) : cl3Hat (A + B) = cl3Hat A + cl3Hat B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cl3Hat, Matrix.add_apply, neg_add]

theorem cl3Hat_neg (A : Mat2C) : cl3Hat (-A) = -cl3Hat A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cl3Hat]

theorem cl3Hat_smul_real (r : ℝ) (A : Mat2C) : cl3Hat (r • A) = r • cl3Hat A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cl3Hat, Complex.real_smul]

theorem cl3Hat_smul_complex (z : ℂ) (A : Mat2C) : cl3Hat (z • A) = star z • cl3Hat A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cl3Hat]

theorem cl3Hat_mul (A B : Mat2C) : cl3Hat (A * B) = cl3Hat A * cl3Hat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cl3Hat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem cl3Hat_det (φ : Mat2C) : (cl3Hat φ).det = star φ.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp [cl3Hat]
  ring

theorem cl3Hat_pauli4_zero : cl3Hat (pauli4 0) = pauli4 0 := by
  simp [pauli4]

theorem cl3Hat_pauli4_spatial (k : Fin 3) : cl3Hat (pauli4 k.succ) = -pauli4 k.succ := by
  fin_cases k <;>
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [cl3Hat, pauli4, sigma1, sigma2, sigma3]

theorem cl3Hat_conjTranspose_mul (M : Mat2C) :
    (cl3Hat M)ᴴ * M = M.det • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cl3Hat, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.det_fin_two] <;> ring

theorem mul_cl3Hat_conjTranspose (M : Mat2C) :
    M * (cl3Hat M)ᴴ = M.det • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cl3Hat, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.det_fin_two] <;> ring

theorem sl2c_cl3Hat_conjTranspose_eq_inv (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    (cl3Hat M.1)ᴴ = (M⁻¹).1 := by
  have hmul : (cl3Hat M.1)ᴴ * M.1 = 1 := by
    rw [cl3Hat_conjTranspose_mul, M.prop, one_smul]
  calc
    (cl3Hat M.1)ᴴ = (cl3Hat M.1)ᴴ * (M.1 * (M⁻¹).1) := by
          have hinv : M.1 * (M⁻¹).1 = 1 := by
            change (M * M⁻¹).1 = 1
            rw [mul_inv_cancel]
            rfl
          rw [hinv, Matrix.mul_one]
    _ = ((cl3Hat M.1)ᴴ * M.1) * (M⁻¹).1 := (Matrix.mul_assoc _ _ _).symm
    _ = (M⁻¹).1 := by rw [hmul, Matrix.one_mul]

/-! ### Section 2: All-4-Component Paravector Current Trace Identifications -/

private lemma electricCurrentJ_coord_expand (Φ : Vec8R) (μ : Fin 4) :
    electricCurrentJ Φ μ = match μ with
      | ⟨0, _⟩ => Φ 0 ^ 2 + Φ 1 ^ 2 + Φ 2 ^ 2 + Φ 3 ^ 2 + Φ 4 ^ 2 + Φ 5 ^ 2 + Φ 6 ^ 2 + Φ 7 ^ 2
      | ⟨1, _⟩ => 2 * (Φ 0 * Φ 5 - Φ 1 * Φ 4 - Φ 2 * Φ 7 + Φ 3 * Φ 6)
      | ⟨2, _⟩ => 2 * (Φ 0 * Φ 6 - Φ 1 * Φ 7 + Φ 2 * Φ 4 - Φ 3 * Φ 5)
      | ⟨3, _⟩ => 2 * (Φ 0 * Φ 7 + Φ 1 * Φ 6 + Φ 2 * Φ 5 + Φ 3 * Φ 4) := by
  fin_cases μ <;>
    · simp only [electricCurrentJ,
        InfoGeometry.Canonical.KreinMajoranaBlockInvariance.kreinInnerProduct,
        InfoGeometry.Canonical.KreinMajoranaBlockInvariance.kreinMetric8,
        gammaR, castZ8, gammaZ, gamma0Z, gamma1Z, gamma2Z, gamma3Z,
        Matrix.mulVec, dotProduct, Fin.sum_univ_eight, RingHom.mapMatrix_apply,
        Matrix.of_apply]
      norm_num
      ring

private lemma axialCurrentSigma_coord_expand (Φ : Vec8R) (μ : Fin 4) :
    axialCurrentSigma Φ μ = match μ with
      | ⟨0, _⟩ => 2 * (Φ 0 * Φ 7 - Φ 1 * Φ 6 - Φ 2 * Φ 5 + Φ 3 * Φ 4)
      | ⟨1, _⟩ => 2 * (-Φ 0 * Φ 2 - Φ 1 * Φ 3 + Φ 4 * Φ 6 + Φ 5 * Φ 7)
      | ⟨2, _⟩ => 2 * (-Φ 0 * Φ 1 + Φ 2 * Φ 3 - Φ 4 * Φ 5 + Φ 6 * Φ 7)
      | ⟨3, _⟩ => Φ 0 ^ 2 - Φ 1 ^ 2 - Φ 2 ^ 2 + Φ 3 ^ 2 + Φ 4 ^ 2 - Φ 5 ^ 2 - Φ 6 ^ 2 + Φ 7 ^ 2 := by
  fin_cases μ <;>
    · simp only [axialCurrentSigma,
        InfoGeometry.Canonical.KreinMajoranaBlockInvariance.kreinInnerProduct,
        InfoGeometry.Canonical.KreinMajoranaBlockInvariance.kreinMetric8,
        gamma5Real, gammaR, gamma0123R, quatPR, quatPZ, p3Z, castZ8,
        gammaZ, gamma0Z, gamma1Z, gamma2Z, gamma3Z, gamma0123Z,
        Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_eight,
        RingHom.mapMatrix_apply, Matrix.of_apply]
      norm_num
      ring

private lemma vec8ToCl3Spinor_eq (Φ : Vec8R) :
    vec8ToCl3Spinor Φ =
      !![weylXi Φ 0, -star (weylEta Φ 1); weylXi Φ 1, star (weylEta Φ 0)] :=
  rfl

/-- All-4-component trace identity for the Dirac vector probability current:
`Re Tr(φ φᴴ σ_μ) = J^μ(Φ)` for every `μ : Fin 4` (Daviau & Bertrand Eq. 10). -/
theorem vec8ToCl3Spinor_electricCurrentJ_trace (Φ : Vec8R) (μ : Fin 4) :
    ((vec8ToCl3Spinor Φ * (vec8ToCl3Spinor Φ)ᴴ) * pauli4 μ).trace.re =
      electricCurrentJ Φ μ := by
  rw [electricCurrentJ_coord_expand Φ μ, vec8ToCl3Spinor_eq]
  fin_cases μ <;>
    · simp [weylXi, weylEta, phiToPsi, pauli4, sigma1, sigma2, sigma3,
        Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two]
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
      ring

/-- All-4-component trace identity for the axial magnetic current:
`Re Tr(φ σ₃ φᴴ σ_μ) = Σ^μ(Φ)` for every `μ : Fin 4`. -/
theorem vec8ToCl3Spinor_axialCurrentSigma_trace (Φ : Vec8R) (μ : Fin 4) :
    ((vec8ToCl3Spinor Φ * sigma3 * (vec8ToCl3Spinor Φ)ᴴ) * pauli4 μ).trace.re =
      axialCurrentSigma Φ μ := by
  rw [axialCurrentSigma_coord_expand Φ μ, vec8ToCl3Spinor_eq]
  fin_cases μ <;>
    · simp [weylXi, weylEta, phiToPsi, pauli4, sigma1, sigma2, sigma3,
        Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two]
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
      ring

/-- Hermitian paravector reconstruction `paravectorMat (J(Φ)) = 2 • (φ φᴴ)` for all 4
components simultaneously. -/
theorem paravectorMat_electricCurrentJ (Φ : Vec8R) :
    paravectorMat (electricCurrentJ Φ) =
      (2 : ℂ) • (vec8ToCl3Spinor Φ * (vec8ToCl3Spinor Φ)ᴴ) := by
  dsimp [paravectorMat]
  rw [Fin.sum_univ_four]
  have hj : ∀ μ : Fin 4, electricCurrentJ Φ μ =
      ((vec8ToCl3Spinor Φ * (vec8ToCl3Spinor Φ)ᴴ) * pauli4 μ).trace.re :=
    fun μ => (vec8ToCl3Spinor_electricCurrentJ_trace Φ μ).symm
  set φ := vec8ToCl3Spinor Φ
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [hj 0, hj 1, hj 2, hj 3]
      apply Complex.ext <;>
        · simp [pauli4, sigma1, sigma2, sigma3, Matrix.trace, Matrix.diag, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.real_smul, Complex.nsmul_eq_mul]
          ring

/-- Hermitian paravector reconstruction `paravectorMat (Σ(Φ)) = 2 • (φ σ₃ φᴴ)` for all 4
components simultaneously. -/
theorem paravectorMat_axialCurrentSigma (Φ : Vec8R) :
    paravectorMat (axialCurrentSigma Φ) =
      (2 : ℂ) • (vec8ToCl3Spinor Φ * sigma3 * (vec8ToCl3Spinor Φ)ᴴ) := by
  dsimp [paravectorMat]
  rw [Fin.sum_univ_four]
  have hs : ∀ μ : Fin 4, axialCurrentSigma Φ μ =
      ((vec8ToCl3Spinor Φ * sigma3 * (vec8ToCl3Spinor Φ)ᴴ) * pauli4 μ).trace.re :=
    fun μ => (vec8ToCl3Spinor_axialCurrentSigma_trace Φ μ).symm
  set φ := vec8ToCl3Spinor Φ
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [hs 0, hs 1, hs 2, hs 3]
      apply Complex.ext <;>
        · simp [pauli4, sigma1, sigma2, sigma3, Matrix.trace, Matrix.diag, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.real_smul, Complex.nsmul_eq_mul]
          ring

/-! ### Section 3: Exact `Cl₃`-Spinor Operator Dictionary (`Γ_μ`, `Γ⁰¹²³`, `P₃`, `γ₅`) -/

/-- Exact lowered Dirac matrix dictionary:
`vec8ToCl3Spinor (Γ_μ Φ) = σ_μ * cl3Hat (vec8ToCl3Spinor Φ)` for all `μ : Fin 4`. -/
theorem vec8ToCl3Spinor_gammaLowR (μ : Fin 4) (Φ : Vec8R) :
    vec8ToCl3Spinor (gammaLowR μ *ᵥ Φ) = pauli4 μ * cl3Hat (vec8ToCl3Spinor Φ) := by
  fin_cases μ <;>
    · rw [vec8ToCl3Spinor_eq, vec8ToCl3Spinor_eq]
      ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        · simp [weylXi, weylEta, phiToPsi, cl3Hat, pauli4, sigma1, sigma2, sigma3,
            gammaLowR, gammaLowZ, minkowskiMetricZ, gammaZ, gamma0Z, gamma1Z, gamma2Z, gamma3Z,
            castZ8, Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
            Fin.sum_univ_eight, RingHom.mapMatrix_apply, Matrix.of_apply]
          ring

/-- Exact contravariant Dirac matrix dictionary:
`vec8ToCl3Spinor (Γ^μ Φ) = g^{μμ} • (σ_μ * cl3Hat (vec8ToCl3Spinor Φ))`. -/
theorem vec8ToCl3Spinor_gammaR (μ : Fin 4) (Φ : Vec8R) :
    vec8ToCl3Spinor (gammaR μ *ᵥ Φ) =
      (minkowskiMetricR μ : ℂ) • (pauli4 μ * cl3Hat (vec8ToCl3Spinor Φ)) := by
  have h : gammaR μ = minkowskiMetricR μ • gammaLowR μ := by
    rw [gammaLowR_eq, smul_smul]
    fin_cases μ <;> simp [minkowskiMetricR, minkowskiMetricZ]
  rw [h, Matrix.smul_mulVec, LinearEquiv.map_smul, vec8ToCl3Spinor_gammaLowR, Complex.coe_smul]

/-- Exact pseudoscalar dictionary: `vec8ToCl3Spinor (Γ⁰¹²³ Φ) = -i • vec8ToCl3Spinor Φ`. -/
theorem vec8ToCl3Spinor_gamma0123R (Φ : Vec8R) :
    vec8ToCl3Spinor (gamma0123R *ᵥ Φ) = -(Complex.I • vec8ToCl3Spinor Φ) := by
  rw [vec8ToCl3Spinor_eq, vec8ToCl3Spinor_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    · simp [weylXi, weylEta, phiToPsi, gamma0123R, gamma0123Z, castZ8, Matrix.mulVec, dotProduct,
        Fin.sum_univ_eight, RingHom.mapMatrix_apply, Matrix.of_apply]
      ring

/-- Exact electric-generator dictionary: `vec8ToCl3Spinor (P₃ Φ) = vec8ToCl3Spinor Φ * (i σ₃)`. -/
theorem vec8ToCl3Spinor_quatPR2 (Φ : Vec8R) :
    vec8ToCl3Spinor (quatPR 2 *ᵥ Φ) = vec8ToCl3Spinor Φ * (Complex.I • sigma3) := by
  rw [vec8ToCl3Spinor_eq, vec8ToCl3Spinor_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    · simp [weylXi, weylEta, phiToPsi, quatPR, quatPZ, p3Z, castZ8, sigma3, Matrix.mulVec,
        Matrix.mul_apply, dotProduct, Fin.sum_univ_two, Fin.sum_univ_eight,
        RingHom.mapMatrix_apply, Matrix.of_apply]
      ring

/-- Exact chiral-involution dictionary: `vec8ToCl3Spinor (γ₅ Φ) = vec8ToCl3Spinor Φ * σ₃`. -/
theorem vec8ToCl3Spinor_gamma5Real2 (Φ : Vec8R) :
    vec8ToCl3Spinor (gamma5Real ⟨2, by decide⟩ *ᵥ Φ) = vec8ToCl3Spinor Φ * sigma3 := by
  have hg5 : gamma5Real ⟨2, by decide⟩ *ᵥ Φ = gamma0123R *ᵥ (quatPR 2 *ᵥ Φ) := by
    dsimp [gamma5Real]
    rw [Matrix.mulVec_mulVec]
  rw [hg5, vec8ToCl3Spinor_gamma0123R, vec8ToCl3Spinor_quatPR2, smul_mul_assoc,
    mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]

/-! ### Section 4: Lifting `GL(2,ℂ)` Left Multiplication to `Mat8R` -/

/-- ℝ-linear spinor action `Φ ↦ vec8ToCl3Spinor⁻¹ (M * vec8ToCl3Spinor Φ)` on `ℝ⁸`. -/
def lorentzDilationSpinorAct (M : Mat2C) : Vec8R →ₗ[ℝ] Vec8R where
  toFun Φ := vec8ToCl3Spinor.symm (M * vec8ToCl3Spinor Φ)
  map_add' Φ Ψ := by
    rw [map_add, Matrix.mul_add, map_add]
  map_smul' r Φ := by
    rw [map_smul, Complex.coe_smul, mul_smul_comm, ← Complex.coe_smul, map_smul]
    rfl

/-- Real `8 × 8` matrix lift `L(M) ∈ M₈(ℝ)` representing left multiplication `φ ↦ M φ`
under `vec8ToCl3Spinor`. -/
def lorentzDilationMat8 (M : Mat2C) : Mat8R :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (lorentzDilationSpinorAct M)

@[simp]
theorem lorentzDilationMat8_mulVec (M : Mat2C) (Φ : Vec8R) :
    lorentzDilationMat8 M *ᵥ Φ = vec8ToCl3Spinor.symm (M * vec8ToCl3Spinor Φ) := by
  ext i
  have h := congrFun (LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℝ (Fin 8))
    (Pi.basisFun ℝ (Fin 8)) (lorentzDilationSpinorAct M) Φ) i
  simpa [lorentzDilationMat8, lorentzDilationSpinorAct] using h

@[simp]
theorem vec8ToCl3Spinor_lorentzDilationMat8 (M : Mat2C) (Φ : Vec8R) :
    vec8ToCl3Spinor (lorentzDilationMat8 M *ᵥ Φ) = M * vec8ToCl3Spinor Φ := by
  rw [lorentzDilationMat8_mulVec, LinearEquiv.apply_symm_apply]

theorem mat8R_eq_of_mulVec {A B : Mat8R} (h : ∀ Φ : Vec8R, A *ᵥ Φ = B *ᵥ Φ) : A = B := by
  ext i j
  have hv := congrFun (h (Pi.single j (1 : ℝ))) i
  simpa [Matrix.mulVec, dotProduct] using hv

@[simp]
theorem lorentzDilationMat8_one : lorentzDilationMat8 (1 : Mat2C) = (1 : Mat8R) := by
  refine mat8R_eq_of_mulVec fun Φ => ?_
  rw [lorentzDilationMat8_mulVec, Matrix.one_mul, LinearEquiv.symm_apply_apply, Matrix.one_mulVec]

@[simp]
theorem lorentzDilationMat8_neg_one : lorentzDilationMat8 (-(1 : Mat2C)) = -(1 : Mat8R) := by
  refine mat8R_eq_of_mulVec fun Φ => ?_
  rw [lorentzDilationMat8_mulVec, neg_mul, Matrix.one_mul, map_neg,
    LinearEquiv.symm_apply_apply, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem lorentzDilationMat8_mul (M N : Mat2C) :
    lorentzDilationMat8 (M * N) = lorentzDilationMat8 M * lorentzDilationMat8 N := by
  refine mat8R_eq_of_mulVec fun Φ => ?_
  rw [lorentzDilationMat8_mulVec, Matrix.mulVec_mulVec, lorentzDilationMat8_mulVec,
    lorentzDilationMat8_mulVec, LinearEquiv.apply_symm_apply, Matrix.mul_assoc]

/-- Complex scalar phase `exp(-i α) I₂` lifts verbatim to Lochak's chiral gauge matrix
`chiralGaugeMat α = cos(α) I₈ + sin(α) Γ⁰¹²³`. -/
theorem lorentzDilationMat8_chiralGauge (α : ℝ) :
    lorentzDilationMat8 (Real.cos α • (1 : Mat2C) - Real.sin α • (Complex.I • (1 : Mat2C))) =
      chiralGaugeMat α := by
  refine mat8R_eq_of_mulVec fun Φ => ?_
  apply vec8ToCl3Spinor.injective
  rw [vec8ToCl3Spinor_lorentzDilationMat8]
  dsimp [chiralGaugeMat]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    map_add, map_smul, map_smul, vec8ToCl3Spinor_gamma0123R]
  rw [sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul, smul_mul_assoc, one_mul,
    Complex.coe_smul, Complex.coe_smul, smul_neg, sub_eq_add_neg]

/-- Every Lorentz–dilation lift `L(M)` commutes strictly with Daviau's `P₃`. -/
theorem lorentzDilationMat8_comm_quatPR2 (M : Mat2C) :
    lorentzDilationMat8 M * quatPR 2 = quatPR 2 * lorentzDilationMat8 M := by
  refine mat8R_eq_of_mulVec fun Φ => ?_
  apply vec8ToCl3Spinor.injective
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    vec8ToCl3Spinor_lorentzDilationMat8, vec8ToCl3Spinor_quatPR2,
    vec8ToCl3Spinor_quatPR2, vec8ToCl3Spinor_lorentzDilationMat8, Matrix.mul_assoc]

/-- Every Lorentz–dilation lift `L(M)` commutes strictly with real `γ₅ = Γ⁰¹²³ P₃`. -/
theorem lorentzDilationMat8_comm_gamma5Real2 (M : Mat2C) :
    lorentzDilationMat8 M * gamma5Real ⟨2, by decide⟩ =
      gamma5Real ⟨2, by decide⟩ * lorentzDilationMat8 M := by
  refine mat8R_eq_of_mulVec fun Φ => ?_
  apply vec8ToCl3Spinor.injective
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    vec8ToCl3Spinor_lorentzDilationMat8, vec8ToCl3Spinor_gamma5Real2,
    vec8ToCl3Spinor_gamma5Real2, vec8ToCl3Spinor_lorentzDilationMat8, Matrix.mul_assoc]

/-- Every Lorentz–dilation lift `L(M)` commutes with Daviau's electric gauge `exp(α P₃)`. -/
theorem lorentzDilationMat8_comm_electricGauge (M : Mat2C) (α : ℝ) :
    lorentzDilationMat8 M * electricGaugeMat α = electricGaugeMat α * lorentzDilationMat8 M := by
  dsimp [electricGaugeMat]
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul, lorentzDilationMat8_comm_quatPR2 M]

/-! ### Section 5: Full `GL(2,ℂ)` Bilinear & Dirac Covariance + `SL(2,ℂ) → SO⁺(1,3)` Double Cover -/

private lemma paravectorMat_inj {x y : Fin 4 → ℝ}
    (h : paravectorMat x = paravectorMat y) : x = y := by
  funext μ
  have h00 := congrArg (fun M : Mat2C => (M 0 0).re) h
  have h11 := congrArg (fun M : Mat2C => (M 1 1).re) h
  have h01re := congrArg (fun M : Mat2C => (M 0 1).re) h
  have h10im := congrArg (fun M : Mat2C => (M 1 0).im) h
  dsimp [paravectorMat] at h00 h11 h01re h10im
  simp [Fin.sum_univ_four, pauli4, sigma1, sigma2, sigma3, Complex.real_smul]
    at h00 h11 h01re h10im
  fin_cases μ <;> (dsimp; linarith)

/-- **Full `GL(2,ℂ)` Bilinear Covariance Theorem** in real `M₈(ℝ)`:
under `Φ' = L(M) Φ`,
- `det(φ') = det(M) det(φ)`;
- `(Ω₁', Ω₂')` undergoes a conformal rotation-dilation by `det(M)`;
- `Ω₁'² + Ω₂'² = |det M|² (Ω₁² + Ω₂²)`;
- ALL four components of `J^μ` and `Σ^μ` transform by `R(M) = lorentzDilationMat M`. -/
theorem lorentzDilationMat8_bilinear_covariance (M : Mat2C) (Φ : Vec8R) :
    ((vec8ToCl3Spinor (lorentzDilationMat8 M *ᵥ Φ)).det =
      M.det * (vec8ToCl3Spinor Φ).det) ∧
    (omega1 (lorentzDilationMat8 M *ᵥ Φ) =
      M.det.re * omega1 Φ - M.det.im * omega2 Φ) ∧
    (omega2 (lorentzDilationMat8 M *ᵥ Φ) =
      M.det.im * omega1 Φ + M.det.re * omega2 Φ) ∧
    (omega1 (lorentzDilationMat8 M *ᵥ Φ) ^ 2 + omega2 (lorentzDilationMat8 M *ᵥ Φ) ^ 2 =
      Complex.normSq M.det * (omega1 Φ ^ 2 + omega2 Φ ^ 2)) ∧
    (∀ μ : Fin 4,
      electricCurrentJ (lorentzDilationMat8 M *ᵥ Φ) μ =
        (lorentzDilationMat M).mulVec (electricCurrentJ Φ) μ) ∧
    (∀ μ : Fin 4,
      axialCurrentSigma (lorentzDilationMat8 M *ᵥ Φ) μ =
        (lorentzDilationMat M).mulVec (axialCurrentSigma Φ) μ) := by
  have hdet : (vec8ToCl3Spinor (lorentzDilationMat8 M *ᵥ Φ)).det =
      M.det * (vec8ToCl3Spinor Φ).det := by
    rw [vec8ToCl3Spinor_lorentzDilationMat8, Matrix.det_mul]
  have hre : 2 * (vec8ToCl3Spinor Φ).det.re = omega1 Φ :=
    (vec8ToCl3Spinor_fierz_and_currents Φ).2.1
  have him : 2 * (vec8ToCl3Spinor Φ).det.im = omega2 Φ :=
    (vec8ToCl3Spinor_fierz_and_currents Φ).2.2.1
  have hre' : 2 * (vec8ToCl3Spinor (lorentzDilationMat8 M *ᵥ Φ)).det.re =
      omega1 (lorentzDilationMat8 M *ᵥ Φ) :=
    (vec8ToCl3Spinor_fierz_and_currents _).2.1
  have him' : 2 * (vec8ToCl3Spinor (lorentzDilationMat8 M *ᵥ Φ)).det.im =
      omega2 (lorentzDilationMat8 M *ᵥ Φ) :=
    (vec8ToCl3Spinor_fierz_and_currents _).2.2.1
  have ho1 : omega1 (lorentzDilationMat8 M *ᵥ Φ) =
      M.det.re * omega1 Φ - M.det.im * omega2 Φ := by
    have hmulre := congrArg Complex.re hdet
    rw [Complex.mul_re] at hmulre
    linarith
  have ho2 : omega2 (lorentzDilationMat8 M *ᵥ Φ) =
      M.det.im * omega1 Φ + M.det.re * omega2 Φ := by
    have hmulim := congrArg Complex.im hdet
    rw [Complex.mul_im] at hmulim
    linarith
  have hnsq : omega1 (lorentzDilationMat8 M *ᵥ Φ) ^ 2 + omega2 (lorentzDilationMat8 M *ᵥ Φ) ^ 2 =
      Complex.normSq M.det * (omega1 Φ ^ 2 + omega2 Φ ^ 2) := by
    rw [ho1, ho2, Complex.normSq_apply]
    ring
  have hJvec :
      electricCurrentJ (lorentzDilationMat8 M *ᵥ Φ) =
        (lorentzDilationMat M).mulVec (electricCurrentJ Φ) := by
    apply paravectorMat_inj
    rw [paravectorMat_electricCurrentJ, vec8ToCl3Spinor_lorentzDilationMat8,
      paravectorMat_lorentzDilation, paravectorMat_electricCurrentJ,
      Matrix.conjTranspose_mul, mul_smul_comm, smul_mul_assoc]
    simp only [Matrix.mul_assoc]
  have hSvec :
      axialCurrentSigma (lorentzDilationMat8 M *ᵥ Φ) =
        (lorentzDilationMat M).mulVec (axialCurrentSigma Φ) := by
    apply paravectorMat_inj
    rw [paravectorMat_axialCurrentSigma, vec8ToCl3Spinor_lorentzDilationMat8,
      paravectorMat_lorentzDilation, paravectorMat_axialCurrentSigma,
      Matrix.conjTranspose_mul, mul_smul_comm, smul_mul_assoc]
    simp only [Matrix.mul_assoc]
  exact ⟨hdet, ho1, ho2, hnsq, fun μ => congrFun hJvec μ, fun μ => congrFun hSvec μ⟩

/-- **Exact `GL(2,ℂ)` Lowered Dirac Intertwining Theorem** in `M₈(ℝ)`:
`L((cl3Hat M)ᴴ) * Γ_μ * L(M) = ∑_ν R((cl3Hat M)ᴴ)^ν_μ • Γ_ν`
for every `M : Mat2C` and `μ : Fin 4`. -/
theorem lorentzDilationMat8_gammaLowR_intertwine (M : Mat2C) (μ : Fin 4) :
    lorentzDilationMat8 (cl3Hat M)ᴴ * (gammaLowR μ * lorentzDilationMat8 M) =
      ∑ ν : Fin 4, lorentzDilationMat (cl3Hat M)ᴴ ν μ • gammaLowR ν := by
  refine mat8R_eq_of_mulVec fun Φ => ?_
  apply vec8ToCl3Spinor.injective
  have hcol :
      (lorentzDilationMat (cl3Hat M)ᴴ).mulVec (fun k => if k = μ then (1 : ℝ) else 0) =
        fun ν => lorentzDilationMat (cl3Hat M)ᴴ ν μ := by
    ext ν
    simp [Matrix.mulVec, dotProduct]
  have hpar :
      paravectorMat (fun ν => lorentzDilationMat (cl3Hat M)ᴴ ν μ) =
        (cl3Hat M)ᴴ * pauli4 μ * cl3Hat M := by
    have h1 := paravectorMat_lorentzDilation (cl3Hat M)ᴴ
      (fun k => if k = μ then (1 : ℝ) else 0)
    have h2 : paravectorMat (fun k => if k = μ then (1 : ℝ) else 0) = pauli4 μ := by
      dsimp [paravectorMat]; simp
    rw [hcol, h2, Matrix.conjTranspose_conjTranspose] at h1
    exact h1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, vec8ToCl3Spinor_lorentzDilationMat8,
    vec8ToCl3Spinor_gammaLowR, vec8ToCl3Spinor_lorentzDilationMat8, cl3Hat_mul]
  rw [Matrix.sum_mulVec, map_sum]
  have hrhs :
      ∑ ν : Fin 4, vec8ToCl3Spinor (lorentzDilationMat (cl3Hat M)ᴴ ν μ • (gammaLowR ν *ᵥ Φ)) =
        (∑ ν : Fin 4, (lorentzDilationMat (cl3Hat M)ᴴ ν μ : ℂ) • pauli4 ν) *
          cl3Hat (vec8ToCl3Spinor Φ) := by
    rw [Matrix.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [map_smul, vec8ToCl3Spinor_gammaLowR, Complex.coe_smul, smul_mul_assoc]
  rw [hrhs]
  change (cl3Hat M)ᴴ * (pauli4 μ * (cl3Hat M * cl3Hat (vec8ToCl3Spinor Φ))) =
    paravectorMat (fun ν => lorentzDilationMat (cl3Hat M)ᴴ ν μ) * cl3Hat (vec8ToCl3Spinor Φ)
  rw [hpar]
  simp only [Matrix.mul_assoc]

/-- **`SL(2,ℂ) → SO⁺(1,3)` Spinor Double Cover Theorem on `ℝ⁸`**:
Restricting `M ∈ SL(2,ℂ)`:
1. `L(M)` is invertible in `M₈(ℝ)` with inverse `L(M⁻¹)`;
2. The Dirac matrices `Γ_μ` intertwine by `L(M⁻¹) * Γ_μ * L(M) = ∑_ν R(M⁻¹)^ν_μ • Γ_ν`;
3. `Ω₁` and `Ω₂` are strictly Lorentz-invariant while `J^μ, Σ^μ` transform by `R(M) ∈ SO⁺(1,3)`;
4. Genuine double cover: `L(-I₂) = -I₈ ≠ I₈` on spinors while `R(-I₂) = I₄` on vectors. -/
theorem sl2c_dirac8_spinor_double_cover (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    (lorentzDilationMat8 M.1 * lorentzDilationMat8 (M⁻¹).1 = (1 : Mat8R) ∧
      lorentzDilationMat8 (M⁻¹).1 * lorentzDilationMat8 M.1 = (1 : Mat8R)) ∧
    (∀ μ : Fin 4,
      lorentzDilationMat8 (M⁻¹).1 * (gammaLowR μ * lorentzDilationMat8 M.1) =
        ∑ ν : Fin 4, lorentzDilationMat (M⁻¹).1 ν μ • gammaLowR ν) ∧
    (∀ Φ : Vec8R,
      omega1 (lorentzDilationMat8 M.1 *ᵥ Φ) = omega1 Φ ∧
      omega2 (lorentzDilationMat8 M.1 *ᵥ Φ) = omega2 Φ ∧
      (∀ μ : Fin 4, electricCurrentJ (lorentzDilationMat8 M.1 *ᵥ Φ) μ =
        (lorentzDilationMat M.1).mulVec (electricCurrentJ Φ) μ) ∧
      (∀ μ : Fin 4, axialCurrentSigma (lorentzDilationMat8 M.1 *ᵥ Φ) μ =
        (lorentzDilationMat M.1).mulVec (axialCurrentSigma Φ) μ)) ∧
    ((lorentzDilationMat M.1)ᵀ * minkowskiEta4 * lorentzDilationMat M.1 = minkowskiEta4 ∧
      (lorentzDilationMat M.1).det = 1 ∧ 0 < lorentzDilationMat M.1 0 0) ∧
    (lorentzDilationMat8 (-(1 : Mat2C)) = -(1 : Mat8R) ∧
      lorentzDilationMat8 (-(1 : Mat2C)) ≠ (1 : Mat8R) ∧
      lorentzDilationMat (-(1 : Mat2C)) = (1 : Matrix (Fin 4) (Fin 4) ℝ)) := by
  have hinvR : lorentzDilationMat8 M.1 * lorentzDilationMat8 (M⁻¹).1 = 1 := by
    rw [← lorentzDilationMat8_mul]
    have hmul : M.1 * (M⁻¹).1 = 1 := by
      change (M * M⁻¹).1 = 1
      rw [mul_inv_cancel]
      rfl
    rw [hmul, lorentzDilationMat8_one]
  have hinvL : lorentzDilationMat8 (M⁻¹).1 * lorentzDilationMat8 M.1 = 1 := by
    rw [← lorentzDilationMat8_mul]
    have hmul : (M⁻¹).1 * M.1 = 1 := by
      change (M⁻¹ * M).1 = 1
      rw [inv_mul_cancel]
      rfl
    rw [hmul, lorentzDilationMat8_one]
  have hinter : ∀ μ : Fin 4,
      lorentzDilationMat8 (M⁻¹).1 * (gammaLowR μ * lorentzDilationMat8 M.1) =
        ∑ ν : Fin 4, lorentzDilationMat (M⁻¹).1 ν μ • gammaLowR ν := by
    intro μ
    have h := lorentzDilationMat8_gammaLowR_intertwine M.1 μ
    rwa [sl2c_cl3Hat_conjTranspose_eq_inv M] at h
  have hbilin : ∀ Φ : Vec8R,
      omega1 (lorentzDilationMat8 M.1 *ᵥ Φ) = omega1 Φ ∧
      omega2 (lorentzDilationMat8 M.1 *ᵥ Φ) = omega2 Φ ∧
      (∀ μ : Fin 4, electricCurrentJ (lorentzDilationMat8 M.1 *ᵥ Φ) μ =
        (lorentzDilationMat M.1).mulVec (electricCurrentJ Φ) μ) ∧
      (∀ μ : Fin 4, axialCurrentSigma (lorentzDilationMat8 M.1 *ᵥ Φ) μ =
        (lorentzDilationMat M.1).mulVec (axialCurrentSigma Φ) μ) := by
    intro Φ
    rcases lorentzDilationMat8_bilinear_covariance M.1 Φ with ⟨_, ho1, ho2, _, hJ, hS⟩
    have hdet : M.1.det = 1 := M.prop
    rw [hdet, Complex.one_re, Complex.one_im] at ho1 ho2
    refine ⟨by linarith, by linarith, hJ, hS⟩
  have hso := sl2c_double_cover_soPlus13 M
  have hneg_ne : lorentzDilationMat8 (-(1 : Mat2C)) ≠ (1 : Mat8R) := by
    rw [lorentzDilationMat8_neg_one]
    intro h
    have h00 := congrFun (congrFun h 0) 0
    norm_num at h00
  have hRneg : lorentzDilationMat (-(1 : Mat2C)) = 1 :=
    (sl2c_double_cover_soPlus13 1).2.2.2.1.trans lorentzDilationMat_one
  exact ⟨⟨hinvR, hinvL⟩, hinter, hbilin, ⟨hso.1, hso.2.1, hso.2.2.1⟩,
    ⟨lorentzDilationMat8_neg_one, hneg_ne, hRneg⟩⟩

end InfoGeometry.Clifford.DaviauBertrandSpinorLorentzLift
