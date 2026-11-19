/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Clifford8BdGHorizon
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Four-Factor Real Supertwistor Lift Cl(1,1)^⊗4 ≅ M₁₆(ℝ), Polarized Fermi Sea & Real 3D Bloch Ball

Formalizes Archetype 1 (`Poset T₀..T₇`):
1. Real-rebit symmetric centralizer no-go (`real_rebit_symmetric_centralizer_trivial`):
   the symmetric centralizer of `J₂` in `M₂(ℝ)` is 1-dimensional (`ℝ · I₂`), missing the
   imaginary Pauli-`Y` direction on `ℝ²`.
2. Unpolarized `U_TFD` collapse onto `Q₊` and the hyperbolic `(J₈ Q₊ K₈)ᵀ = +J₈ Q₊ K₈`
   obstruction in `M₈(ℝ)` (`clifford8_unpolarized_tfd_collapse_and_hyperbolic_obstruction`).
3. Polarized Fermi-sea projector `P_Fermi_Z = E₀₀ + E₆₆` (`2 P_Fermi = V₈ (1 + K₈)`) and
   exact unit-trace Gibbs marginal `ρ_Gibbs8(χ)` (`polarized_fermi_sea_unit_trace_state`).
4. Four-factor real supertwistor carrier `Mat16Prod := Matrix (Fin 8 × Fin 2) (Fin 8 × Fin 2) ℝ`
   equipped with the explicit algebra equivalence `mat16Equiv : Mat16Prod ≃ₐ[ℝ] Matrix (Fin 16) (Fin 16) ℝ`,
   exposing two orthogonal skew-adjoint complex structures `J_spin16` and `J_phase16`
   (`supertwistor16_dual_complex_structures_and_traces`).
5. Skew-adjoint Tomita–Takesaki modular generator `G_Tomita16 = J_phase16 * (Q₊₁₆ K₈₁₆)` and
   compact orthogonal flow `U_Tomita16(t)`, KMS invariance of `ρ_Gibbs16`, and Larmor precession
   (`supertwistor16_skew_tomita_unitary_flow`).
6. Full 3D real qubit Bloch ball `B³` (`M₂(ℝ)_spin ⊗ M₂(ℝ)_phase`) reconstruction, Pauli algebra,
   4D Hermitian centralizer characterization (`mem_real_qubit_hermitian_iff_bloch_span`), and
   `S²` pure-state idempotent boundary (`rx² + ry² + rz² = 1`).
-/

noncomputable section

open scoped Kronecker

namespace InfoGeometry.OperatorAlgebra.PeirceBiSandwich

/-! ### Helper Lemmas for Real Matrices & Kronecker Products -/

lemma star_eq_transpose_R {n : Type*} (M : Matrix n n ℝ) : star M = M.transpose := by
  ext i j
  rw [Matrix.star_apply, star_trivial, Matrix.transpose_apply]

lemma toMat8R_transpose (M : Matrix (Fin 8) (Fin 8) ℤ) :
    (toMat8R M).transpose = toMat8R M.transpose := by
  rw [← star_eq_transpose_R, star_toMat8R]

lemma kronecker_transpose {l m n p R : Type*} [Mul R] (A : Matrix l m R) (B : Matrix n p R) :
    (A ⊗ₖ B).transpose = A.transpose ⊗ₖ B.transpose :=
  (Matrix.kroneckerMap_transpose (· * ·) A B).symm

lemma kronecker_smul_left {l m n p : Type*} (r : ℝ)
    (A : Matrix l m ℝ) (B : Matrix n p ℝ) :
    (r • A) ⊗ₖ B = r • (A ⊗ₖ B) :=
  Matrix.smul_kronecker r A B

lemma kronecker_smul_right {l m n p : Type*} (r : ℝ)
    (A : Matrix l m ℝ) (B : Matrix n p ℝ) :
    A ⊗ₖ (r • B) = r • (A ⊗ₖ B) :=
  Matrix.kronecker_smul r A B

/-! ### 1. Real-Rebit Modular No-Go (`T₀`) -/

/-- Canonical symplectic / complex structure `J₂` on `ℝ²`. -/
def J2_R : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- Real-rebit symmetric centralizer no-go: the real symmetric operators commuting with `J₂`
    in `M₂(ℝ)` are strictly scalar (`ℝ · I₂`), missing a symmetric `σ_Y` generator. -/
theorem real_rebit_symmetric_centralizer_trivial (X : Matrix (Fin 2) (Fin 2) ℝ) :
    (X.transpose = X ∧ comm J2_R X = 0) ↔ ∃ c : ℝ, X = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  constructor
  · rintro ⟨hT, hC⟩
    have h01_T := congr_fun (congr_fun hT 0) 1
    have h00_C := congr_fun (congr_fun hC 0) 0
    have h01_C := congr_fun (congr_fun hC 0) 1
    simp only [Matrix.transpose_apply] at h01_T
    simp only [comm, J2_R, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
               Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.zero_apply] at h00_C h01_C
    have h01 : X 0 1 = 0 := by linarith
    have h10 : X 1 0 = 0 := by linarith
    have hdiag : X 0 0 = X 1 1 := by linarith
    refine ⟨X 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, hdiag]
  · rintro ⟨c, rfl⟩
    refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [comm, J2_R]

/-! ### 2. Unpolarized `U_TFD` Collapse & Hyperbolic Obstruction in `M₈(ℝ)` (`T₁`) -/

/-- Unpolarized `U_TFD` pinching collapse onto `Q₊` and hyperbolic obstruction
    `(J₈ Q₊ K₈)ᵀ = +J₈ Q₊ K₈` in `M₈(ℝ)`. -/
theorem clifford8_unpolarized_tfd_collapse_and_hyperbolic_obstruction (χ : ℝ) :
    let Qp := toMat8R (Qplus P8_Z A8_Z A8_Z)
    let Qm := toMat8R (Qminus P8_Z A8_Z A8_Z)
    Qp * (U_TFD χ * Qm * star (U_TFD χ)) * Qp = (Real.sin χ ^ 2) • Qp ∧
    (J8_spin_Z * Qplus P8_Z A8_Z A8_Z * K8_Z).transpose =
      J8_spin_Z * Qplus P8_Z A8_Z A8_Z * K8_Z ∧
    (J8_spin_Z * Qplus P8_Z A8_Z A8_Z * K8_Z) ^ 2 = Qplus P8_Z A8_Z A8_Z := by
  intro Qp Qm
  let V_Z := casimirV P8_Z A8_Z A8_Z
  let Qp_Z := Qplus P8_Z A8_Z A8_Z
  let Qm_Z := Qminus P8_Z A8_Z A8_Z
  let P0_Z := 1 - V_Z
  let G_Z := Omega8_Z * jOp P8_Z A8_Z A8_Z
  let V := toMat8R V_Z
  let P0 := toMat8R P0_Z
  let G := toMat8R G_Z
  have hQp_P0 : Qp * P0 = 0 := by rw [← map_mul, show Qp_Z * P0_Z = 0 by decide, map_zero]
  have hP0_Qm : P0 * Qm = 0 := by rw [← map_mul, show P0_Z * Qm_Z = 0 by decide, map_zero]
  have hP0_Qp : P0 * Qp = 0 := by rw [← map_mul, show P0_Z * Qp_Z = 0 by decide, map_zero]
  have hV_Qm : V * Qm = Qm := by rw [← map_mul, show V_Z * Qm_Z = Qm_Z by decide]
  have hQm_V : Qm * V = Qm := by rw [← map_mul, show Qm_Z * V_Z = Qm_Z by decide]
  have hQp_Qm : Qp * Qm = 0 := by rw [← map_mul, show Qp_Z * Qm_Z = 0 by decide, map_zero]
  have hQm_Qp : Qm * Qp = 0 := by rw [← map_mul, show Qm_Z * Qp_Z = 0 by decide, map_zero]
  have hQp_G : Qp * G = toMat8R (Qp_Z * G_Z) := (map_mul toMat8R Qp_Z G_Z).symm
  have hG_star : star G = -G := by
    rw [star_toMat8R, show G_Z.transpose = -G_Z by decide, map_neg]
  have hP0_star : star P0 = P0 := by
    rw [star_toMat8R, show P0_Z.transpose = P0_Z by decide]
  have hV_star : star V = V := by
    rw [star_toMat8R, show V_Z.transpose = V_Z by decide]
  have h_prod : (Qp * G) * Qm * (star G * Qp) = Qp := by
    rw [hG_star, hQp_G]
    have hZ : (Qp_Z * G_Z) * Qm_Z * (-G_Z * Qp_Z) = Qp_Z := by decide
    change (toMat8R (Qp_Z * G_Z) * toMat8R Qm_Z) * (-toMat8R G_Z * toMat8R Qp_Z) = toMat8R Qp_Z
    rw [← map_neg, ← map_mul, ← map_mul, ← map_mul, hZ]
  have h_mid : U_TFD χ * Qm * star (U_TFD χ) =
      Real.cos χ ^ 2 • Qm + (Real.cos χ * Real.sin χ) • (Qm * star G + G * Qm) +
      Real.sin χ ^ 2 • (G * Qm * star G) := by
    have hP0_eq : P0 = 1 - V := by dsimp [P0, P0_Z, V]; rw [map_sub, map_one]
    have hU : U_TFD χ = P0 + Real.cos χ • V + Real.sin χ • G := by
      dsimp [U_TFD]; rw [hP0_eq]
    have hU_star : star (U_TFD χ) = P0 + Real.cos χ • V + Real.sin χ • star G := by
      rw [hU]
      simp only [star_add, star_smul, star_trivial, hP0_star, hV_star]
    have hQm_P0 : Qm * P0 = 0 := by rw [← map_mul, show Qm_Z * P0_Z = 0 by decide, map_zero]
    have hGQm_P0 : G * Qm * P0 = 0 := by rw [mul_assoc, hQm_P0, mul_zero]
    have hGQm_V : G * Qm * V = G * Qm := by rw [mul_assoc, hQm_V]
    have hLeft : (P0 + Real.cos χ • V + Real.sin χ • G) * Qm =
        Real.cos χ • Qm + Real.sin χ • (G * Qm) := by
      simp only [add_mul, smul_mul_assoc, hP0_Qm, hV_Qm, zero_add]
    rw [hU_star, hU, hLeft]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
               hQm_P0, hGQm_P0, hQm_V, hGQm_V,
               smul_zero, zero_add]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  refine ⟨?_, by decide, by decide⟩
  have hQp_star : star Qp = Qp := by rw [star_toMat8R, show Qp_Z.transpose = Qp_Z by decide]
  calc Qp * (U_TFD χ * Qm * star (U_TFD χ)) * Qp
      = Qp * (Real.cos χ ^ 2 • Qm + (Real.cos χ * Real.sin χ) • (Qm * star G + G * Qm) +
          Real.sin χ ^ 2 • (G * Qm * star G)) * Qp := by rw [h_mid]
    _ = Real.cos χ ^ 2 • (Qp * Qm * Qp) +
        (Real.cos χ * Real.sin χ) • ((Qp * Qm) * star G * Qp + Qp * G * (Qm * Qp)) +
        Real.sin χ ^ 2 • ((Qp * G) * Qm * (star G * Qp)) := by
        simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = Real.sin χ ^ 2 • Qp := by
        rw [hQp_Qm, hQm_Qp, h_prod]
        simp only [zero_mul, mul_zero, add_zero, zero_add, smul_zero]

/-! ### 3. Polarized Fermi-Sea Projector & Exact Unit-Trace Gibbs Marginal (`T₂`) -/

/-- Polarized Fermi-sea projector `P_Fermi = E₀₀ + E₆₆ = (1/2) V₈ (1 + K₈)` in `Mat₈(ℤ)`. -/
def P_Fermi_Z : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.diagonal ![1, 0, 0, 0, 0, 0, 1, 0]

/-- Pinched unit-trace Gibbs marginal `ρ_Gibbs8(χ) = Q₊ (U_TFD(χ) P_Fermi U_TFD(χ)ᵀ) Q₊`. -/
noncomputable def rho_Gibbs8 (χ : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  let Qp := toMat8R (Qplus P8_Z A8_Z A8_Z)
  Qp * (U_TFD χ * toMat8R P_Fermi_Z * star (U_TFD χ)) * Qp

/-- Exact polarized Fermi-sea state: `ρ_Gibbs8(χ) = cos²(χ) E₀₀ + sin²(χ) E₁₁ = (1/2)(Q₊ + cos(2χ) Q₊ K₈)`,
    symmetric with constant trace `1` for all `χ : ℝ`. -/
theorem polarized_fermi_sea_unit_trace_state (χ : ℝ) :
    let E00_Z : Matrix (Fin 8) (Fin 8) ℤ := Matrix.diagonal ![1, 0, 0, 0, 0, 0, 0, 0]
    let E11_Z : Matrix (Fin 8) (Fin 8) ℤ := Matrix.diagonal ![0, 1, 0, 0, 0, 0, 0, 0]
    let Qp := toMat8R (Qplus P8_Z A8_Z A8_Z)
    P_Fermi_Z * P_Fermi_Z = P_Fermi_Z ∧
    P_Fermi_Z.transpose = P_Fermi_Z ∧
    2 * P_Fermi_Z = casimirV P8_Z A8_Z A8_Z * (1 + K8_Z) ∧
    rho_Gibbs8 χ = (Real.cos χ ^ 2) • toMat8R E00_Z + (Real.sin χ ^ 2) • toMat8R E11_Z ∧
    rho_Gibbs8 χ = (1 / 2 : ℝ) • (Qp + Real.cos (2 * χ) • (Qp * toMat8R K8_Z)) ∧
    (rho_Gibbs8 χ).transpose = rho_Gibbs8 χ ∧
    (rho_Gibbs8 χ).trace = 1 := by
  intro E00_Z E11_Z Qp
  let V_Z := casimirV P8_Z A8_Z A8_Z
  let P0_Z := 1 - V_Z
  let Qp_Z := Qplus P8_Z A8_Z A8_Z
  let G_Z := Omega8_Z * jOp P8_Z A8_Z A8_Z
  let V := toMat8R V_Z
  let P0 := toMat8R P0_Z
  let G := toMat8R G_Z
  let PF := toMat8R P_Fermi_Z
  have hP0_PF : P0 * PF = 0 := by rw [← map_mul, show P0_Z * P_Fermi_Z = 0 by decide, map_zero]
  have hPF_P0 : PF * P0 = 0 := by rw [← map_mul, show P_Fermi_Z * P0_Z = 0 by decide, map_zero]
  have hQp_V_PF : Qp * (V * PF * V) * Qp = toMat8R E00_Z := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul,
        show Qp_Z * (V_Z * P_Fermi_Z * V_Z) * Qp_Z = E00_Z by decide]
  have hQp_V_PF_G : Qp * (V * PF * -G) * Qp = 0 := by
    rw [← map_neg, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
        show Qp_Z * (V_Z * P_Fermi_Z * -G_Z) * Qp_Z = 0 by decide, map_zero]
  have hQp_G_PF_V : Qp * (G * PF * V) * Qp = 0 := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul,
        show Qp_Z * (G_Z * P_Fermi_Z * V_Z) * Qp_Z = 0 by decide, map_zero]
  have hQp_G_PF_G : Qp * (G * PF * -G) * Qp = toMat8R E11_Z := by
    rw [← map_neg, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
        show Qp_Z * (G_Z * P_Fermi_Z * -G_Z) * Qp_Z = E11_Z by decide]
  have hP0_star : star P0 = P0 := by rw [star_toMat8R, show P0_Z.transpose = P0_Z by decide]
  have hV_star : star V = V := by rw [star_toMat8R, show V_Z.transpose = V_Z by decide]
  have hG_star : star G = -G := by rw [star_toMat8R, show G_Z.transpose = -G_Z by decide, map_neg]
  have hrho : rho_Gibbs8 χ =
      (Real.cos χ ^ 2) • toMat8R E00_Z + (Real.sin χ ^ 2) • toMat8R E11_Z := by
    have hP0_eq : P0 = 1 - V := by dsimp [P0, P0_Z, V]; rw [map_sub, map_one]
    have hU : U_TFD χ = P0 + Real.cos χ • V + Real.sin χ • G := by
      dsimp [U_TFD]; rw [hP0_eq]
    have hU_star : star (U_TFD χ) = P0 + Real.cos χ • V + Real.sin χ • (-G) := by
      rw [hU]; simp only [star_add, star_smul, star_trivial, hP0_star, hV_star, hG_star]
    dsimp only [rho_Gibbs8]
    change Qp * (U_TFD χ * PF * star (U_TFD χ)) * Qp = _
    rw [hU_star, hU]
    have h_exp : (P0 + Real.cos χ • V + Real.sin χ • G) * PF *
          (P0 + Real.cos χ • V + Real.sin χ • (-G)) =
        Real.cos χ ^ 2 • (V * PF * V) +
        (Real.cos χ * Real.sin χ) • (V * PF * -G + G * PF * V) +
        Real.sin χ ^ 2 • (G * PF * -G) := by
      have hLeft : (P0 + Real.cos χ • V + Real.sin χ • G) * PF =
          Real.cos χ • (V * PF) + Real.sin χ • (G * PF) := by
        simp only [add_mul, smul_mul_assoc, hP0_PF, zero_add]
      rw [hLeft]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
                 mul_assoc V PF P0, mul_assoc G PF P0, hPF_P0, mul_zero, smul_zero, zero_add]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [h_exp]
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
               hQp_V_PF, hQp_V_PF_G, hQp_G_PF_V, hQp_G_PF_G, add_zero, smul_zero]
  have hcos : rho_Gibbs8 χ =
      (1 / 2 : ℝ) • (Qp + Real.cos (2 * χ) • (Qp * toMat8R K8_Z)) := by
    rw [hrho]
    have hsum_Z : Qp_Z = E00_Z + E11_Z := by decide
    have hdiff_Z : Qp_Z * K8_Z = E00_Z - E11_Z := by decide
    have hsum : Qp = toMat8R E00_Z + toMat8R E11_Z := by rw [← map_add, ← hsum_Z]
    have hdiff : Qp * toMat8R K8_Z = toMat8R E00_Z - toMat8R E11_Z := by
      rw [← map_mul, hdiff_Z, map_sub]
    rw [hdiff, hsum, Real.cos_two_mul]
    have h1 : (1 / 2 : ℝ) * (1 + (2 * Real.cos χ ^ 2 - 1)) = Real.cos χ ^ 2 := by ring
    have h2 : (1 / 2 : ℝ) * (1 - (2 * Real.cos χ ^ 2 - 1)) = Real.sin χ ^ 2 := by
      have hsc := Real.cos_sq_add_sin_sq χ
      linarith
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (toMat8R E00_Z i j) * h1.symm + (toMat8R E11_Z i j) * h2.symm
  have hT : (rho_Gibbs8 χ).transpose = rho_Gibbs8 χ := by
    rw [hrho, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
        toMat8R_transpose, toMat8R_transpose,
        show E00_Z.transpose = E00_Z by decide,
        show E11_Z.transpose = E11_Z by decide]
  have hTr : (rho_Gibbs8 χ).trace = 1 := by
    rw [hrho, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
    have htr0 : (toMat8R E00_Z).trace = 1 := by
      simp [E00_Z, toMat8R, Matrix.trace, Matrix.diag, Fin.sum_univ_eight]
    have htr1 : (toMat8R E11_Z).trace = 1 := by
      simp [E11_Z, toMat8R, Matrix.trace, Matrix.diag, Fin.sum_univ_eight]
    rw [htr0, htr1, smul_eq_mul, smul_eq_mul, mul_one, mul_one, Real.cos_sq_add_sin_sq]
  exact ⟨by decide, by decide, by decide, hrho, hcos, hT, hTr⟩

/-! ### 4. Four-Factor Real Supertwistor Carrier `Cl(1,1)^⊗4 ≅ M₁₆(ℝ)` (`T₃..T₅`) -/

/-- Kronecker-product 16×16 real matrix carrier `M₈(ℝ) ⊗ M₂(ℝ)_phase`. -/
abbrev Mat16Prod := Matrix (Fin 8 × Fin 2) (Fin 8 × Fin 2) ℝ

/-- Explicit algebra isomorphism onto literal `Matrix (Fin 16) (Fin 16) ℝ`. -/
def mat16Equiv : Mat16Prod ≃ₐ[ℝ] Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ finProdFinEquiv

lemma mat16Equiv_transpose (M : Mat16Prod) :
    (mat16Equiv M).transpose = mat16Equiv M.transpose := by
  ext i j
  simp [mat16Equiv, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

lemma mat16Equiv_trace (M : Mat16Prod) :
    (mat16Equiv M).trace = M.trace := by
  simp only [mat16Equiv, Matrix.coe_reindexAlgEquiv, Matrix.trace, Matrix.diag,
             Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp finProdFinEquiv.symm (fun k => M k k)

/-- 2×2 real phase complex structure `J_phase2` (`J² = -1`, `Jᵀ = -J`). -/
def J_phase2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]
def I2_R : Matrix (Fin 2) (Fin 2) ℝ := 1
def eta_phase2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def K_phase2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Canonical lifted 16×16 real supertwistor operators. -/
def J_spin16 : Mat16Prod := toMat8R J8_spin_Z ⊗ₖ I2_R
def K8_16 : Mat16Prod := toMat8R K8_Z ⊗ₖ I2_R
def Omega8_16 : Mat16Prod := toMat8R Omega8_Z ⊗ₖ I2_R
def Qp16 : Mat16Prod := toMat8R (Qplus P8_Z A8_Z A8_Z) ⊗ₖ I2_R
def Qm16 : Mat16Prod := toMat8R (Qminus P8_Z A8_Z A8_Z) ⊗ₖ I2_R
def V16 : Mat16Prod := toMat8R (casimirV P8_Z A8_Z A8_Z) ⊗ₖ I2_R
def P0_16 : Mat16Prod := toMat8R (1 - casimirV P8_Z A8_Z A8_Z) ⊗ₖ I2_R
def P8_16 : Mat16Prod := toMat8R P8_Z ⊗ₖ I2_R
def J_phase16 : Mat16Prod := (1 : Matrix (Fin 8) (Fin 8) ℝ) ⊗ₖ J_phase2

lemma J_phase2_sq : J_phase2 * J_phase2 = -I2_R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J_phase2, I2_R, Matrix.mul_apply, Fin.sum_univ_two]

lemma J_phase2_transpose : J_phase2.transpose = -J_phase2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J_phase2]

lemma J_phase2_trace : J_phase2.trace = 0 := by
  unfold Matrix.trace Matrix.diag
  rw [Fin.sum_univ_two]
  dsimp [J_phase2]
  norm_num

lemma I2_R_trace : I2_R.trace = 2 := by
  unfold Matrix.trace Matrix.diag
  rw [Fin.sum_univ_two]
  dsimp [I2_R]
  norm_num

/-- OpenGauss T16 non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`:
    the phase rotation `J_phase2` and parity `eta_phase2` anticommute. -/
lemma matrix_fin2_R_noncomm : ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨J_phase2, eta_phase2, ?_⟩
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [J_phase2, eta_phase2, Matrix.mul_apply, Fin.sum_univ_two] at h01
  revert h01; norm_num

/-- Orthogonal coexistence of `J_spin16` and `J_phase16` in `Cl(1,1)^⊗4 ≅ M₁₆(ℝ)`,
    with trace orthogonality `(J_spin16ᵀ J_phase16).trace = 0` and literal `Fin 16` transport. -/
theorem supertwistor16_dual_complex_structures_and_traces :
    J_spin16 * J_spin16 = -1 ∧
    J_phase16 * J_phase16 = -1 ∧
    J_spin16.transpose = -J_spin16 ∧
    J_phase16.transpose = -J_phase16 ∧
    comm J_phase16 J_spin16 = 0 ∧
    comm J_phase16 K8_16 = 0 ∧
    comm J_phase16 Omega8_16 = 0 ∧
    comm J_phase16 Qp16 = 0 ∧
    (∀ c : ℝ, J_phase16 ≠ c • J_spin16) ∧
    (J_spin16.transpose * J_phase16).trace = 0 ∧
    (J_spin16.transpose * J_spin16).trace = 16 ∧
    (J_phase16.transpose * J_phase16).trace = 16 ∧
    mat16Equiv J_phase16 * mat16Equiv J_spin16 = mat16Equiv J_spin16 * mat16Equiv J_phase16 ∧
    (mat16Equiv J_phase16).transpose = -mat16Equiv J_phase16 := by
  have hJ_sq : J_spin16 * J_spin16 = -1 := by
    dsimp [J_spin16, I2_R]
    rw [← Matrix.mul_kronecker_mul, mul_one, ← map_mul, show J8_spin_Z * J8_spin_Z = -1 by decide,
        map_neg, map_one, ← neg_one_smul ℝ (1 : Matrix (Fin 8) (Fin 8) ℝ),
        kronecker_smul_left, Matrix.one_kronecker_one, neg_one_smul]
  have hPh_sq : J_phase16 * J_phase16 = -1 := by
    dsimp [J_phase16]
    rw [← Matrix.mul_kronecker_mul, mul_one, J_phase2_sq,
        show (-I2_R) = (-1 : ℝ) • I2_R by simp [I2_R],
        kronecker_smul_right, show I2_R = 1 from rfl, Matrix.one_kronecker_one, neg_one_smul]
  have hJ_T : J_spin16.transpose = -J_spin16 := by
    dsimp [J_spin16, I2_R]
    rw [kronecker_transpose, toMat8R_transpose, Matrix.transpose_one,
        show J8_spin_Z.transpose = -J8_spin_Z by decide, map_neg,
        ← neg_one_smul ℝ (toMat8R J8_spin_Z), kronecker_smul_left, neg_one_smul]
  have hPh_T : J_phase16.transpose = -J_phase16 := by
    dsimp [J_phase16]
    rw [kronecker_transpose, Matrix.transpose_one, J_phase2_transpose,
        ← neg_one_smul ℝ J_phase2, kronecker_smul_right, neg_one_smul]
  have hcomm_kron : ∀ X_Z : Matrix (Fin 8) (Fin 8) ℤ,
      comm J_phase16 (toMat8R X_Z ⊗ₖ I2_R) = 0 := by
    intro X_Z
    dsimp [comm, J_phase16]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        one_mul, mul_one, show I2_R = 1 from rfl, mul_one, one_mul, sub_self]
  have hcomm_JS : J_phase16 * J_spin16 = J_spin16 * J_phase16 := sub_eq_zero.mp (hcomm_kron J8_spin_Z)
  refine ⟨hJ_sq, hPh_sq, hJ_T, hPh_T,
          hcomm_kron J8_spin_Z, hcomm_kron K8_Z, hcomm_kron Omega8_Z,
          hcomm_kron (Qplus P8_Z A8_Z A8_Z), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    have h00 := congr_fun (congr_fun hc (0, 0)) (0, 1)
    simp [J_phase16, J_spin16, J_phase2, J8_spin_Z, I2_R, toMat8R] at h00
  · rw [hJ_T, Matrix.neg_mul, Matrix.trace_neg]
    dsimp [J_spin16, J_phase16, I2_R]
    rw [← Matrix.mul_kronecker_mul, mul_one, one_mul, Matrix.trace_kronecker,
        J_phase2_trace, mul_zero, neg_zero]
  · rw [hJ_T]
    calc (-J_spin16 * J_spin16).trace = (-(J_spin16 * J_spin16)).trace := by rw [Matrix.neg_mul]
      _ = (1 : Mat16Prod).trace := by rw [hJ_sq, neg_neg]
      _ = 16 := by simp [Matrix.trace, Matrix.diag]
  · rw [hPh_T]
    calc (-J_phase16 * J_phase16).trace = (-(J_phase16 * J_phase16)).trace := by rw [Matrix.neg_mul]
      _ = (1 : Mat16Prod).trace := by rw [hPh_sq, neg_neg]
      _ = 16 := by simp [Matrix.trace, Matrix.diag]
  · rw [← map_mul, ← map_mul, hcomm_JS]
  · rw [mat16Equiv_transpose, hPh_T, map_neg]

/-- OpenGauss T16 non-commutativity witness on `Matrix (Fin 16) (Fin 16) ℝ`:
    the lifted generators `mat16Equiv J_spin16` and `mat16Equiv K8_16` do not commute. -/
lemma matrix_fin16_R_noncomm : ∃ A B : Matrix (Fin 16) (Fin 16) ℝ, A * B ≠ B * A := by
  refine ⟨mat16Equiv J_spin16, mat16Equiv K8_16, ?_⟩
  intro h
  have h_prod : J_spin16 * K8_16 = K8_16 * J_spin16 := by
    apply mat16Equiv.injective
    simpa only [map_mul] using h
  have hJK : J_spin16 * K8_16 = (toMat8R (J8_spin_Z * K8_Z)) ⊗ₖ I2_R := by
    dsimp [J_spin16, K8_16, I2_R]
    rw [← Matrix.mul_kronecker_mul, mul_one, map_mul]
  have hKJ : K8_16 * J_spin16 = (toMat8R (K8_Z * J8_spin_Z)) ⊗ₖ I2_R := by
    dsimp [J_spin16, K8_16, I2_R]
    rw [← Matrix.mul_kronecker_mul, mul_one, map_mul]
  rw [hJK, hKJ] at h_prod
  have h01 := congr_fun (congr_fun h_prod (0, 0)) (1, 0)
  dsimp [I2_R, Matrix.kroneckerMap_apply] at h01
  simp only [Matrix.one_apply, ↓reduceIte, mul_one, toMat8R,
             RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom] at h01
  have h_val1 : (J8_spin_Z * K8_Z) 0 1 = 1 := by decide
  have h_val2 : (K8_Z * J8_spin_Z) 0 1 = -1 := by decide
  rw [h_val1, h_val2] at h01
  revert h01; norm_num

/-! ### 5. Skew-Adjoint Tomita–Takesaki Modular Group & Larmor Flow (`T₅`) -/

/-- Skew-adjoint Tomita–Takesaki modular generator `G_Tomita = J_phase (Q₊ K₈)` in `M₁₆(ℝ)`. -/
def G_Tomita16 : Mat16Prod := J_phase16 * (Qp16 * K8_16)

/-- Compact orthogonal Tomita–Takesaki modular flow `U_Tomita(t) = (1 - Q₊) + cos(t) Q₊ + sin(t) G_Tomita`. -/
noncomputable def U_Tomita16 (t : ℝ) : Mat16Prod :=
  (1 - Qp16) + Real.cos t • Qp16 + Real.sin t • G_Tomita16

/-- Real-lifted polarized Gibbs state `ρ_Gibbs16(χ) = ρ_Gibbs8(χ) ⊗ (1/2) I₂`. -/
noncomputable def rho_Gibbs16 (χ : ℝ) : Mat16Prod :=
  rho_Gibbs8 χ ⊗ₖ ((1 / 2 : ℝ) • I2_R)

/-- Skew-adjointness of `G_Tomita16`, compact orthogonal group law of `U_Tomita16(t)`,
    exact KMS stationarity of `ρ_Gibbs16(χ)`, and Larmor precession on transverse spin. -/
theorem supertwistor16_skew_tomita_unitary_flow (χ s t : ℝ) :
    let Qp_Z := Qplus P8_Z A8_Z A8_Z
    let Sigma1_16 : Mat16Prod := toMat8R (Qp_Z * Omega8_Z) ⊗ₖ I2_R
    let Sigma2_16 : Mat16Prod := toMat8R (Qp_Z * J8_spin_Z) ⊗ₖ J_phase2
    G_Tomita16.transpose = -G_Tomita16 ∧
    G_Tomita16 * G_Tomita16 = -Qp16 ∧
    (U_Tomita16 t).transpose * U_Tomita16 t = 1 ∧
    U_Tomita16 0 = 1 ∧
    U_Tomita16 (s + t) = U_Tomita16 s * U_Tomita16 t ∧
    (rho_Gibbs16 χ).trace = 1 ∧
    U_Tomita16 t * rho_Gibbs16 χ * (U_Tomita16 t).transpose = rho_Gibbs16 χ ∧
    U_Tomita16 t * Sigma1_16 * (U_Tomita16 t).transpose =
      Real.cos (2 * t) • Sigma1_16 + Real.sin (2 * t) • Sigma2_16 := by
  intro Qp_Z Sigma1_16 Sigma2_16
  have hG_kron : G_Tomita16 = toMat8R (Qp_Z * K8_Z) ⊗ₖ J_phase2 := by
    dsimp [G_Tomita16, Qp16, K8_16, J_phase16, I2_R]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        one_mul, mul_one, mul_one, map_mul]
  have hG_T : G_Tomita16.transpose = -G_Tomita16 := by
    rw [hG_kron, kronecker_transpose, toMat8R_transpose, J_phase2_transpose,
        show (Qp_Z * K8_Z).transpose = Qp_Z * K8_Z by decide,
        ← neg_one_smul ℝ J_phase2, kronecker_smul_right, neg_one_smul]
  have hG_sq : G_Tomita16 * G_Tomita16 = -Qp16 := by
    rw [hG_kron, ← Matrix.mul_kronecker_mul, ← map_mul,
        show (Qp_Z * K8_Z) * (Qp_Z * K8_Z) = Qp_Z by decide,
        J_phase2_sq, ← neg_one_smul ℝ I2_R, kronecker_smul_right, neg_one_smul]
    rfl
  have hQp_idem : Qp16 * Qp16 = Qp16 := by
    dsimp [Qp16, I2_R]
    rw [← Matrix.mul_kronecker_mul, mul_one, ← map_mul, show Qp_Z * Qp_Z = Qp_Z by decide]
  have hQp_T : Qp16.transpose = Qp16 := by
    dsimp [Qp16, I2_R]
    rw [kronecker_transpose, toMat8R_transpose, Matrix.transpose_one,
        show Qp_Z.transpose = Qp_Z by decide]
  have hQp_G : Qp16 * G_Tomita16 = G_Tomita16 := by
    rw [hG_kron]
    dsimp [Qp16, I2_R]
    rw [← Matrix.mul_kronecker_mul, one_mul, ← map_mul, show Qp_Z * (Qp_Z * K8_Z) = Qp_Z * K8_Z by decide]
  have hG_Qp : G_Tomita16 * Qp16 = G_Tomita16 := by
    rw [hG_kron]
    dsimp [Qp16, I2_R]
    rw [← Matrix.mul_kronecker_mul, mul_one, ← map_mul, show (Qp_Z * K8_Z) * Qp_Z = Qp_Z * K8_Z by decide]
  have h1Qp_Qp : (1 - Qp16) * Qp16 = 0 := by
    calc (1 - Qp16) * Qp16 = Qp16 - Qp16 * Qp16 := by noncomm_ring
      _ = 0 := by rw [hQp_idem, sub_self]
  have hQp_1Qp : Qp16 * (1 - Qp16) = 0 := by
    calc Qp16 * (1 - Qp16) = Qp16 - Qp16 * Qp16 := by noncomm_ring
      _ = 0 := by rw [hQp_idem, sub_self]
  have h1Qp_G : (1 - Qp16) * G_Tomita16 = 0 := by
    calc (1 - Qp16) * G_Tomita16 = G_Tomita16 - Qp16 * G_Tomita16 := by noncomm_ring
      _ = 0 := by rw [hQp_G, sub_self]
  have hG_1Qp : G_Tomita16 * (1 - Qp16) = 0 := by
    calc G_Tomita16 * (1 - Qp16) = G_Tomita16 - G_Tomita16 * Qp16 := by noncomm_ring
      _ = 0 := by rw [hG_Qp, sub_self]
  have h1Qp_idem : (1 - Qp16) * (1 - Qp16) = 1 - Qp16 := by
    calc (1 - Qp16) * (1 - Qp16) = 1 - 2 • Qp16 + Qp16 * Qp16 := by noncomm_ring
      _ = 1 - Qp16 := by rw [hQp_idem]; simp only [two_smul]; abel
  have hU_mul : ∀ a b : ℝ, U_Tomita16 a * U_Tomita16 b = U_Tomita16 (a + b) := by
    intro a b
    dsimp [U_Tomita16]
    have htrigC : Real.cos (a + b) = Real.cos a * Real.cos b - Real.sin a * Real.sin b :=
      Real.cos_add a b
    have htrigS : Real.sin (a + b) = Real.sin a * Real.cos b + Real.cos a * Real.sin b :=
      Real.sin_add a b
    calc ((1 - Qp16) + Real.cos a • Qp16 + Real.sin a • G_Tomita16) *
           ((1 - Qp16) + Real.cos b • Qp16 + Real.sin b • G_Tomita16)
        = (1 - Qp16) +
          (Real.cos a * Real.cos b - Real.sin a * Real.sin b) • Qp16 +
          (Real.sin a * Real.cos b + Real.cos a * Real.sin b) • G_Tomita16 := by
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
                     h1Qp_idem, h1Qp_Qp, hQp_1Qp, h1Qp_G, hG_1Qp, hQp_idem,
                     hQp_G, hG_Qp, hG_sq, smul_zero, add_zero, zero_add]
          ext i j
          simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
                     smul_eq_mul]
          ring
      _ = (1 - Qp16) + Real.cos (a + b) • Qp16 + Real.sin (a + b) • G_Tomita16 := by
          rw [htrigC, htrigS]
  have hU_T : ∀ r : ℝ, (U_Tomita16 r).transpose = U_Tomita16 (-r) := by
    intro r
    dsimp [U_Tomita16]
    rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one,
        hQp_T, Matrix.transpose_smul, Matrix.transpose_smul, hQp_T, hG_T,
        Real.cos_neg, Real.sin_neg, smul_neg, neg_smul]
  have hU0 : U_Tomita16 0 = 1 := by
    dsimp [U_Tomita16]
    rw [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero, sub_add_cancel]
  have h_orth : (U_Tomita16 t).transpose * U_Tomita16 t = 1 := by
    rw [hU_T, hU_mul, neg_add_cancel, hU0]
  have h_orth_right : U_Tomita16 t * (U_Tomita16 t).transpose = 1 := by
    rw [hU_T, hU_mul, add_neg_cancel, hU0]
  have h_rho_tr : (rho_Gibbs16 χ).trace = 1 := by
    dsimp [rho_Gibbs16]
    rw [Matrix.trace_kronecker, Matrix.trace_smul, I2_R_trace,
        (polarized_fermi_sea_unit_trace_state χ).2.2.2.2.2.2]
    norm_num
  have h_comm_rho : G_Tomita16 * rho_Gibbs16 χ = rho_Gibbs16 χ * G_Tomita16 := by
    have hcos := (polarized_fermi_sea_unit_trace_state χ).2.2.2.2.1
    change rho_Gibbs8 χ = (1 / 2 : ℝ) • (toMat8R Qp_Z + Real.cos (2 * χ) • (toMat8R Qp_Z * toMat8R K8_Z)) at hcos
    have hcomm8 : toMat8R (Qp_Z * K8_Z) * rho_Gibbs8 χ = rho_Gibbs8 χ * toMat8R (Qp_Z * K8_Z) := by
      rw [hcos, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
          mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
      have h1 : (Qp_Z * K8_Z) * Qp_Z = Qp_Z * (Qp_Z * K8_Z) := by decide
      rw [h1]
    dsimp [rho_Gibbs16]
    rw [hG_kron, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hcomm8,
        mul_smul_comm, smul_mul_assoc]
    dsimp [I2_R]
    rw [mul_one, one_mul]
  have h_Qp_rho : Qp16 * rho_Gibbs16 χ = rho_Gibbs16 χ := by
    have hcos := (polarized_fermi_sea_unit_trace_state χ).2.2.2.2.1
    change rho_Gibbs8 χ = (1 / 2 : ℝ) • (toMat8R Qp_Z + Real.cos (2 * χ) • (toMat8R Qp_Z * toMat8R K8_Z)) at hcos
    have h8 : toMat8R Qp_Z * rho_Gibbs8 χ = rho_Gibbs8 χ := by
      rw [hcos, mul_smul_comm, mul_add, mul_smul_comm, ← map_mul, ← mul_assoc, ← map_mul,
          show Qp_Z * Qp_Z = Qp_Z by decide]
    dsimp [Qp16, rho_Gibbs16, I2_R]
    rw [← Matrix.mul_kronecker_mul, h8, one_mul]
  have h_rho_Qp : rho_Gibbs16 χ * Qp16 = rho_Gibbs16 χ := by
    have hT8 := (polarized_fermi_sea_unit_trace_state χ).2.2.2.2.2.1
    have hT16 : (rho_Gibbs16 χ).transpose = rho_Gibbs16 χ := by
      dsimp [rho_Gibbs16]
      rw [kronecker_transpose, hT8, Matrix.transpose_smul, show I2_R.transpose = I2_R by simp [I2_R]]
    have h := congrArg Matrix.transpose h_Qp_rho
    rw [Matrix.transpose_mul, hQp_T, hT16] at h
    exact h
  have h_U_rho : U_Tomita16 t * rho_Gibbs16 χ * (U_Tomita16 t).transpose = rho_Gibbs16 χ := by
    have h_comm_U : U_Tomita16 t * rho_Gibbs16 χ = rho_Gibbs16 χ * U_Tomita16 t := by
      dsimp [U_Tomita16]
      simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
                 smul_mul_assoc, mul_smul_comm, h_Qp_rho, h_rho_Qp, h_comm_rho]
    rw [h_comm_U, mul_assoc, h_orth_right, mul_one]
  have h_larmor : U_Tomita16 t * Sigma1_16 * (U_Tomita16 t).transpose =
      Real.cos (2 * t) • Sigma1_16 + Real.sin (2 * t) • Sigma2_16 := by
    have hGS1 : G_Tomita16 * Sigma1_16 = Sigma2_16 := by
      rw [hG_kron]
      dsimp [Sigma1_16, Sigma2_16, I2_R]
      rw [← Matrix.mul_kronecker_mul, mul_one, ← map_mul,
          show (Qp_Z * K8_Z) * (Qp_Z * Omega8_Z) = Qp_Z * J8_spin_Z by decide]
    have hS1G : Sigma1_16 * G_Tomita16 = -Sigma2_16 := by
      rw [hG_kron]
      dsimp [Sigma1_16, Sigma2_16, I2_R]
      rw [← Matrix.mul_kronecker_mul, one_mul, ← map_mul,
          show (Qp_Z * Omega8_Z) * (Qp_Z * K8_Z) = -(Qp_Z * J8_spin_Z) by decide,
          map_neg, ← neg_one_smul ℝ (toMat8R (Qp_Z * J8_spin_Z)),
          kronecker_smul_left, neg_one_smul]
    have hGS2 : G_Tomita16 * Sigma2_16 = -Sigma1_16 := by
      rw [hG_kron]
      dsimp [Sigma1_16, Sigma2_16]
      rw [← Matrix.mul_kronecker_mul, J_phase2_sq,
          ← map_mul toMat8R (Qp_Z * K8_Z) (Qp_Z * J8_spin_Z),
          show (Qp_Z * K8_Z) * (Qp_Z * J8_spin_Z) = Qp_Z * Omega8_Z by decide,
          show (-I2_R) = (-1 : ℝ) • I2_R by simp [I2_R],
          kronecker_smul_right, neg_one_smul]
    have hS2G : Sigma2_16 * G_Tomita16 = Sigma1_16 := by
      rw [hG_kron]
      dsimp [Sigma1_16, Sigma2_16]
      rw [← Matrix.mul_kronecker_mul, J_phase2_sq,
          ← map_mul toMat8R (Qp_Z * J8_spin_Z) (Qp_Z * K8_Z),
          show (Qp_Z * J8_spin_Z) * (Qp_Z * K8_Z) = -(Qp_Z * Omega8_Z) by decide,
          map_neg, ← neg_one_smul ℝ (toMat8R (Qp_Z * Omega8_Z)),
          show (-I2_R) = (-1 : ℝ) • I2_R by simp [I2_R],
          kronecker_smul_left, kronecker_smul_right, smul_smul]
      norm_num
    have hQpS1 : Qp16 * Sigma1_16 = Sigma1_16 := by
      dsimp [Qp16, Sigma1_16, I2_R]
      rw [← Matrix.mul_kronecker_mul, one_mul, ← map_mul,
          show Qp_Z * (Qp_Z * Omega8_Z) = Qp_Z * Omega8_Z by decide]
    have hS1Qp : Sigma1_16 * Qp16 = Sigma1_16 := by
      dsimp [Qp16, Sigma1_16, I2_R]
      rw [← Matrix.mul_kronecker_mul, mul_one, ← map_mul,
          show (Qp_Z * Omega8_Z) * Qp_Z = Qp_Z * Omega8_Z by decide]
    have h1QpS1 : (1 - Qp16) * Sigma1_16 = 0 := by
      calc (1 - Qp16) * Sigma1_16 = Sigma1_16 - Qp16 * Sigma1_16 := by noncomm_ring
        _ = 0 := by rw [hQpS1, sub_self]
    have hS11Qp : Sigma1_16 * (1 - Qp16) = 0 := by
      calc Sigma1_16 * (1 - Qp16) = Sigma1_16 - Sigma1_16 * Qp16 := by noncomm_ring
        _ = 0 := by rw [hS1Qp, sub_self]
    have hQpS2 : Qp16 * Sigma2_16 = Sigma2_16 := by
      dsimp [Qp16, Sigma2_16, I2_R]
      rw [← Matrix.mul_kronecker_mul, one_mul, ← map_mul,
          show Qp_Z * (Qp_Z * J8_spin_Z) = Qp_Z * J8_spin_Z by decide]
    have hS21Qp : Sigma2_16 * (1 - Qp16) = 0 := by
      calc Sigma2_16 * (1 - Qp16) = Sigma2_16 - Sigma2_16 * Qp16 := by noncomm_ring
        _ = 0 := by
          have hS2Qp : Sigma2_16 * Qp16 = Sigma2_16 := by
            dsimp [Qp16, Sigma2_16, I2_R]
            rw [← Matrix.mul_kronecker_mul, mul_one, ← map_mul,
                show (Qp_Z * J8_spin_Z) * Qp_Z = Qp_Z * J8_spin_Z by decide]
          rw [hS2Qp, sub_self]
    have hS2Qp : Sigma2_16 * Qp16 = Sigma2_16 := by
      dsimp [Qp16, Sigma2_16, I2_R]
      rw [← Matrix.mul_kronecker_mul, mul_one, ← map_mul,
          show (Qp_Z * J8_spin_Z) * Qp_Z = Qp_Z * J8_spin_Z by decide]
    rw [hU_T]
    dsimp [U_Tomita16]
    rw [Real.cos_neg, Real.sin_neg]
    have hleft : ((1 - Qp16) + Real.cos t • Qp16 + Real.sin t • G_Tomita16) * Sigma1_16 =
        Real.cos t • Sigma1_16 + Real.sin t • Sigma2_16 := by
      simp only [add_mul, smul_mul_assoc, h1QpS1, hQpS1, hGS1, zero_add]
    rw [hleft]
    have hstep : (Real.cos t • Sigma1_16 + Real.sin t • Sigma2_16) *
        ((1 - Qp16) + Real.cos t • Qp16 + (-Real.sin t) • G_Tomita16) =
        (Real.cos t ^ 2 - Real.sin t ^ 2) • Sigma1_16 +
        (2 * Real.sin t * Real.cos t) • Sigma2_16 := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
                 hS11Qp, hS21Qp, hS1Qp, hS2Qp, hS1G, hS2G, smul_zero, zero_add]
      ext ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hstep, Real.cos_two_mul', Real.sin_two_mul]
  refine ⟨hG_T, hG_sq, h_orth, hU0, (hU_mul s t).symm, h_rho_tr, h_U_rho, h_larmor⟩

/-! ### 6. Full 3D Real Qubit Bloch Ball `B³` & `S²` Pure-State Boundary (`T₇`) -/

/-- Realified qubit algebra `M₂(ℝ)_spin ⊗ M₂(ℝ)_phase`. -/
abbrev RealQubitMat := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ

def I4_R : RealQubitMat := (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)
def J4_phase : RealQubitMat := (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ J_phase2
def sigmaX_R : RealQubitMat := !![0, 1; 1, 0] ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)
def sigmaY_R : RealQubitMat := !![0, -1; 1, 0] ⊗ₖ J_phase2
def sigmaZ_R : RealQubitMat := !![1, 0; 0, -1] ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)

def blochProjector (rx ry rz : ℝ) : RealQubitMat :=
  (1 / 2 : ℝ) • (I4_R + rx • sigmaX_R + ry • sigmaY_R + rz • sigmaZ_R)

def blochState (rx ry rz : ℝ) : RealQubitMat :=
  (1 / 4 : ℝ) • (I4_R + rx • sigmaX_R + ry • sigmaY_R + rz • sigmaZ_R)

/-- Exact 4D characterization of real symmetric `J_phase`-commuting operators in `M₄(ℝ)`
    as the real Bloch linear span `ℝ·I₄ ⊕ ℝ·σ_X ⊕ ℝ·σ_Y ⊕ ℝ·σ_Z`. -/
theorem mem_real_qubit_hermitian_iff_bloch_span (X : RealQubitMat) :
    (X.transpose = X ∧ comm J4_phase X = 0) ↔
      ∃ c rx ry rz : ℝ, X = c • I4_R + rx • sigmaX_R + ry • sigmaY_R + rz • sigmaZ_R := by
  constructor
  · rintro ⟨hT, hC⟩
    have hT0010 := congr_fun (congr_fun hT (0, 0)) (1, 0)
    have hT0011 := congr_fun (congr_fun hT (0, 0)) (1, 1)
    have hT0110 := congr_fun (congr_fun hT (0, 1)) (1, 0)
    have hT0111 := congr_fun (congr_fun hT (0, 1)) (1, 1)
    have hT0001 := congr_fun (congr_fun hT (0, 0)) (0, 1)
    have hT1011 := congr_fun (congr_fun hT (1, 0)) (1, 1)
    simp only [Matrix.transpose_apply] at hT0010 hT0011 hT0110 hT0111 hT0001 hT1011
    have hC0000 := congr_fun (congr_fun hC (0, 0)) (0, 0)
    have hC0001 := congr_fun (congr_fun hC (0, 0)) (0, 1)
    have hC0010 := congr_fun (congr_fun hC (0, 0)) (1, 0)
    have hC0011 := congr_fun (congr_fun hC (0, 0)) (1, 1)
    have hC1010 := congr_fun (congr_fun hC (1, 0)) (1, 0)
    have hC1011 := congr_fun (congr_fun hC (1, 0)) (1, 1)
    simp only [comm, J4_phase, J_phase2, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_prod_type,
               Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply,
               Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.zero_apply] at hC0000 hC0001 hC0010 hC0011 hC1010 hC1011
    norm_num at hC0000 hC0001 hC0010 hC0011 hC1010 hC1011
    refine ⟨(X (0, 0) (0, 0) + X (1, 0) (1, 0)) / 2,
            X (0, 0) (1, 0),
            -X (0, 1) (1, 0),
            (X (0, 0) (0, 0) - X (1, 0) (1, 0)) / 2, ?_⟩
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [I4_R, sigmaX_R, sigmaY_R, sigmaZ_R, J_phase2, Matrix.kroneckerMap_apply] <;>
      linarith
  · rintro ⟨c, rx, ry, rz, rfl⟩
    refine ⟨?_, ?_⟩
    · ext ⟨i1, i2⟩ ⟨j1, j2⟩
      fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
        simp [I4_R, sigmaX_R, sigmaY_R, sigmaZ_R, J_phase2, Matrix.kroneckerMap_apply]
    · ext ⟨i1, i2⟩ ⟨j1, j2⟩
      fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
        simp [comm, J4_phase, I4_R, sigmaX_R, sigmaY_R, sigmaZ_R, J_phase2,
              Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
              Matrix.kroneckerMap_apply]

/-- 3D Real Bloch ball Pauli algebra, expectation moments `(rx, ry, rz)`, and `S²`
    idempotent boundary `blochProjector r ^ 2 = blochProjector r ↔ rx² + ry² + rz² = 1`. -/
theorem real_bloch_ball_pauli_reconstruction (rx ry rz : ℝ) :
    sigmaX_R.transpose = sigmaX_R ∧ sigmaY_R.transpose = sigmaY_R ∧ sigmaZ_R.transpose = sigmaZ_R ∧
    sigmaX_R * sigmaX_R = I4_R ∧ sigmaY_R * sigmaY_R = I4_R ∧ sigmaZ_R * sigmaZ_R = I4_R ∧
    anticomm sigmaX_R sigmaY_R = 0 ∧ anticomm sigmaY_R sigmaZ_R = 0 ∧ anticomm sigmaZ_R sigmaX_R = 0 ∧
    sigmaX_R * sigmaY_R = J4_phase * sigmaZ_R ∧
    (blochState rx ry rz).trace = 1 ∧
    (blochState rx ry rz * sigmaX_R).trace = rx ∧
    (blochState rx ry rz * sigmaY_R).trace = ry ∧
    (blochState rx ry rz * sigmaZ_R).trace = rz ∧
    (blochProjector rx ry rz * blochProjector rx ry rz = blochProjector rx ry rz ↔
      rx ^ 2 + ry ^ 2 + rz ^ 2 = 1) := by
  have hX_T : sigmaX_R.transpose = sigmaX_R := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [sigmaX_R]
  have hY_T : sigmaY_R.transpose = sigmaY_R := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [sigmaY_R, J_phase2]
  have hZ_T : sigmaZ_R.transpose = sigmaZ_R := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [sigmaZ_R]
  have hXX : sigmaX_R * sigmaX_R = I4_R := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [sigmaX_R, I4_R, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hYY : sigmaY_R * sigmaY_R = I4_R := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [sigmaY_R, I4_R, J_phase2, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hZZ : sigmaZ_R * sigmaZ_R = I4_R := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [sigmaZ_R, I4_R, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hXY : sigmaX_R * sigmaY_R = J4_phase * sigmaZ_R := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [sigmaX_R, sigmaY_R, sigmaZ_R, J4_phase, J_phase2,
            Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hXY_anti : anticomm sigmaX_R sigmaY_R = 0 := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [anticomm, sigmaX_R, sigmaY_R, J_phase2,
            Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hYZ_anti : anticomm sigmaY_R sigmaZ_R = 0 := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [anticomm, sigmaY_R, sigmaZ_R, J_phase2,
            Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hZX_anti : anticomm sigmaZ_R sigmaX_R = 0 := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [anticomm, sigmaZ_R, sigmaX_R,
            Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hI_sq : I4_R * I4_R = I4_R := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [I4_R, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have htrI : I4_R.trace = 4 := by
    simp [I4_R, Matrix.trace, Matrix.diag]
  have htrX : sigmaX_R.trace = 0 := by
    simp [sigmaX_R, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two]
  have htrY : sigmaY_R.trace = 0 := by
    simp [sigmaY_R, J_phase2, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two]
  have htrZ : sigmaZ_R.trace = 0 := by
    simp [sigmaZ_R, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two]
  have htr_st : (blochState rx ry rz).trace = 1 := by
    dsimp [blochState]
    simp only [Matrix.trace_smul, Matrix.trace_add, smul_eq_mul, htrI, htrX, htrY, htrZ,
               mul_zero, add_zero]
    norm_num
  have hI4_one : I4_R = 1 := by
    dsimp [I4_R]; exact Matrix.one_kronecker_one
  have hXY_tr : (sigmaX_R * sigmaY_R).trace = 0 := by
    rw [hXY]
    simp [J4_phase, sigmaZ_R, J_phase2, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two]
  have hXZ_tr : (sigmaX_R * sigmaZ_R).trace = 0 := by
    simp [sigmaX_R, sigmaZ_R, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two]
  have hYZ_tr : (sigmaY_R * sigmaZ_R).trace = 0 := by
    simp [sigmaY_R, sigmaZ_R, J_phase2, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two]
  have htr_x : (blochState rx ry rz * sigmaX_R).trace = rx := by
    dsimp [blochState]
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul,
        Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
        smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
        Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
        hI4_one, one_mul, htrX, hXX, htrI,
        show (sigmaY_R * sigmaX_R).trace = -((sigmaX_R * sigmaY_R).trace) by
          have h := congrArg Matrix.trace hXY_anti
          dsimp [anticomm] at h
          rw [Matrix.trace_add, Matrix.trace_zero] at h
          linarith,
        hXY_tr, neg_zero]
    have hzx_tr : (sigmaZ_R * sigmaX_R).trace = 0 := by
      simp [sigmaZ_R, sigmaX_R, Matrix.trace, Matrix.diag, Matrix.mul_apply,
            Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [hzx_tr]
    simp only [smul_eq_mul]; ring
  have htr_y : (blochState rx ry rz * sigmaY_R).trace = ry := by
    dsimp [blochState]
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul,
        Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
        smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
        Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
        hI4_one, one_mul, htrY, hXY_tr, hYY, htrI]
    have hzy_tr : (sigmaZ_R * sigmaY_R).trace = 0 := by
      simp [sigmaZ_R, sigmaY_R, J_phase2, Matrix.trace, Matrix.diag, Matrix.mul_apply,
            Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [hzy_tr]
    simp only [smul_eq_mul]; ring
  have htr_z : (blochState rx ry rz * sigmaZ_R).trace = rz := by
    dsimp [blochState]
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul,
        Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
        smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
        Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
        hI4_one, one_mul, htrZ, hXZ_tr, hYZ_tr, hZZ, htrI]
    simp only [smul_eq_mul]; ring
  have hproj_iff :
      blochProjector rx ry rz * blochProjector rx ry rz = blochProjector rx ry rz ↔
        rx ^ 2 + ry ^ 2 + rz ^ 2 = 1 := by
    let S : RealQubitMat := rx • sigmaX_R + ry • sigmaY_R + rz • sigmaZ_R
    have hS_sq : S * S = (rx ^ 2 + ry ^ 2 + rz ^ 2) • I4_R := by
      have hyx : sigmaY_R * sigmaX_R = -(sigmaX_R * sigmaY_R) := by
        have h := hXY_anti; dsimp [anticomm] at h; exact eq_neg_of_add_eq_zero_right h
      have hzy : sigmaZ_R * sigmaY_R = -(sigmaY_R * sigmaZ_R) := by
        have h := hYZ_anti; dsimp [anticomm] at h; exact eq_neg_of_add_eq_zero_right h
      have hxz : sigmaX_R * sigmaZ_R = -(sigmaZ_R * sigmaX_R) := by
        have h := hZX_anti; dsimp [anticomm] at h; exact eq_neg_of_add_eq_zero_right h
      dsimp [S]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
                 hXX, hYY, hZZ, hyx, hzy, hxz]
      ext ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hbp : blochProjector rx ry rz = (1 / 2 : ℝ) • (I4_R + S) := by
      dsimp [blochProjector, S]; simp only [add_assoc]
    have hP_sq : blochProjector rx ry rz * blochProjector rx ry rz =
        (1 / 4 : ℝ) • ((1 + (rx ^ 2 + ry ^ 2 + rz ^ 2)) • I4_R + (2 : ℝ) • S) := by
      rw [hbp]
      simp only [hI4_one, Matrix.smul_mul, Matrix.mul_smul,
                 add_mul, mul_add, one_mul, mul_one, hS_sq]
      ext ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    constructor
    · intro hp
      have htr_S : S.trace = 0 := by
        dsimp [S]
        simp only [Matrix.trace_add, Matrix.trace_smul, htrX, htrY, htrZ, smul_zero, add_zero]
      have htr_eq := congrArg Matrix.trace hp
      rw [hP_sq, hbp] at htr_eq
      simp only [Matrix.trace_smul, Matrix.trace_add, htrI, htr_S, smul_eq_mul] at htr_eq
      linarith
    · intro hr
      rw [hP_sq, hr, hbp]
      ext ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
  exact ⟨hX_T, hY_T, hZ_T, hXX, hYY, hZZ, hXY_anti, hYZ_anti, hZX_anti, hXY,
         htr_st, htr_x, htr_y, htr_z, hproj_iff⟩

end InfoGeometry.OperatorAlgebra.PeirceBiSandwich
