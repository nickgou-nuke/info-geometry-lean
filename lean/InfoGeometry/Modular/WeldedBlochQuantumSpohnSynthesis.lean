/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants
import InfoGeometry.Modular.SchrodingerGKSL
import InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetFunctionalCalculus
import InfoGeometry.Meta
import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open Matrix BigOperators Filter
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder _root_.Topology
open InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants
open InfoGeometry.Modular.SchrodingerGKSL
open InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Algebra.FiniteSpin

noncomputable section

namespace InfoGeometry.Modular.WeldedBlochQuantumSpohnSynthesis

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli $\sigma_x = F_+ + F_- = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. -/
def pauliSigmaX : Mat2C := wittFPlus + wittFMinus

/-- Pauli $\sigma_y = -i (F_+ - F_-) = \begin{pmatrix} 0 & -i \\ i & 0 \end{pmatrix}$. -/
def pauliSigmaY : Mat2C := -Complex.I • (wittFPlus - wittFMinus)

/-- Physical inverse temperature parameter $\theta(\beta, \omega) = -\frac{\beta \omega}{2}$. -/
def boltzmannTheta (β ω : ℝ) : ℝ := -β * ω / 2

/-- Thermal Larmor Zeeman Hamiltonian $H = \frac{\omega}{2} \Gamma_1$. -/
def thermalHamiltonian (ω : ℝ) : Mat2C := ((ω / 2 : ℝ) : ℂ) • pauliGamma1

/-- Thermal Heisenberg dissipator $\mathcal{D}^\dagger_{\gamma, \theta}(A) = \frac{\gamma_+}{2}\mathcal{D}_2^\dagger(F_+, A) + \frac{\gamma_-}{2}\mathcal{D}_2^\dagger(F_-, A)$. -/
def thermalHeisenbergDissipator (γ θ : ℝ) (A : Mat2C) : Mat2C :=
  ((ratePlus γ θ : ℂ) / 2) • heisenbergDissipator2 wittFPlus A +
  ((rateMinus γ θ : ℂ) / 2) • heisenbergDissipator2 wittFMinus A

/-- Lindblad quantum carré du champ operator $\Gamma(A, A) = \mathcal{D}^\dagger(A^\dagger A) - (\mathcal{D}^\dagger(A^\dagger) A + A^\dagger \mathcal{D}^\dagger(A))$. -/
def thermalCarreDuChamp (γ θ : ℝ) (A : Mat2C) : Mat2C :=
  thermalHeisenbergDissipator γ θ (star A * A) -
    (thermalHeisenbergDissipator γ θ (star A) * A + star A * thermalHeisenbergDissipator γ θ A)

/-!
### Section 1: $Y_0 \prec Y_1$ & Rung 1: Witt CAR, Pauli Algebra, and Carré du Champ Damping
-/

private lemma wittFPlus_eq : wittFPlus = mat2 0 1 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma wittFMinus_eq : wittFMinus = mat2 0 0 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma pauliGamma1_eq : pauliGamma1 = mat2 1 0 0 (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> { dsimp [pauliGamma1, J_zero]; norm_num }

private lemma pauliSigmaX_eq : pauliSigmaX = mat2 0 1 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> { dsimp [pauliSigmaX, wittFPlus, wittFMinus, J_plus, J_minus]; norm_num }

private lemma pauliSigmaY_eq : pauliSigmaY = mat2 0 (-Complex.I) Complex.I 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> { dsimp [pauliSigmaY, wittFPlus, wittFMinus, J_plus, J_minus]; norm_num }

private lemma one_mat2_eq : (1 : Mat2C) = mat2 1 0 0 1 := by
  apply ext_mat2
  · change (1 : Mat2C) 0 0 = 1; simp
  · change (1 : Mat2C) 0 1 = 0; simp
  · change (1 : Mat2C) 1 0 = 0; simp
  · change (1 : Mat2C) 1 1 = 1; simp

private lemma smul_mat2 (c a b d e : ℂ) :
    (c • mat2 a b d e) = mat2 (c * a) (c * b) (c * d) (c * e) := by
  apply ext_mat2
  · simp only [mat2_00, Matrix.smul_apply, smul_eq_mul]
  · simp only [mat2_01, Matrix.smul_apply, smul_eq_mul]
  · simp only [mat2_10, Matrix.smul_apply, smul_eq_mul]
  · simp only [mat2_11, Matrix.smul_apply, smul_eq_mul]

private lemma star_mat2 (a b c d : ℂ) :
    star (mat2 a b c d) = mat2 (star a) (star c) (star b) (star d) := by
  apply ext_mat2
  · simp only [mat2_00, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  · simp only [mat2_01, mat2_10, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  · simp only [mat2_01, mat2_10, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  · simp only [mat2_11, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

/-- Witt CAR relations and Pauli algebraic square identities. -/
theorem wittCAR_and_pauli_relations :
    ⁅wittFPlus, wittFMinus⁆ = pauliGamma1 ∧
    wittFPlus * wittFMinus + wittFMinus * wittFPlus = 1 ∧
    pauliSigmaX * pauliSigmaX = 1 ∧
    pauliSigmaY * pauliSigmaY = 1 ∧
    pauliGamma1 * pauliGamma1 = 1 := by
  rw [wittFPlus_eq, wittFMinus_eq, pauliGamma1_eq, pauliSigmaX_eq, pauliSigmaY_eq, one_mat2_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply ext_mat2
    · simp only [Ring.lie_def, mul2_00, mat2_00, mat2_01, mat2_10, Matrix.sub_apply]; ring
    · simp only [Ring.lie_def, mul2_01, mat2_00, mat2_01, mat2_11, Matrix.sub_apply]; ring
    · simp only [Ring.lie_def, mul2_10, mat2_00, mat2_10, mat2_11, Matrix.sub_apply]; ring
    · simp only [Ring.lie_def, mul2_11, mat2_01, mat2_10, mat2_11, Matrix.sub_apply]; ring
  · apply ext_mat2
    · simp only [mul2_00, mat2_00, mat2_01, mat2_10, Matrix.add_apply]; ring
    · simp only [mul2_01, mat2_00, mat2_01, mat2_11, Matrix.add_apply]; ring
    · simp only [mul2_10, mat2_00, mat2_10, mat2_11, Matrix.add_apply]; ring
    · simp only [mul2_11, mat2_01, mat2_10, mat2_11, Matrix.add_apply]; ring
  · apply ext_mat2
    · simp only [mul2_00, mat2_00, mat2_01, mat2_10]; ring
    · simp only [mul2_01, mat2_00, mat2_01, mat2_11]; ring
    · simp only [mul2_10, mat2_00, mat2_10, mat2_11]; ring
    · simp only [mul2_11, mat2_01, mat2_10, mat2_11]; ring
  · apply ext_mat2
    · simp only [mul2_00, mat2_00, mat2_01, mat2_10]
      ring_nf
      simp only [Complex.I_sq]
      ring
    · simp only [mul2_01, mat2_00, mat2_01, mat2_11]; ring
    · simp only [mul2_10, mat2_00, mat2_10, mat2_11]; ring
    · simp only [mul2_11, mat2_01, mat2_10, mat2_11]
      ring_nf
      simp only [Complex.I_sq]
      ring
  · apply ext_mat2
    · simp only [mul2_00, mat2_00, mat2_01, mat2_10]; ring
    · simp only [mul2_01, mat2_00, mat2_01, mat2_11]; ring
    · simp only [mul2_10, mat2_00, mat2_10, mat2_11]; ring
    · simp only [mul2_11, mat2_01, mat2_10, mat2_11]; ring

/-- OpenGauss T16 non-commutativity witness: Pauli $\sigma_x$ and $\Gamma_1$ do not commute. -/
theorem pauli_matrices_noncommutative :
    pauliSigmaX * pauliGamma1 ≠ pauliGamma1 * pauliSigmaX := by
  intro h
  have h01 : (pauliSigmaX * pauliGamma1) 0 1 = (pauliGamma1 * pauliSigmaX) 0 1 := by
    rw [h]
  rw [pauliSigmaX_eq, pauliGamma1_eq] at h01
  simp only [mul2_01, mat2_00, mat2_01, mat2_11] at h01
  have h_contra : (-1 : ℂ) = 1 := by
    linear_combination h01
  norm_num at h_contra

/-- OpenGauss T16 existential non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem mat2_complex_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨mat2 0 1 0 0, mat2 0 0 1 0, ?_⟩
  intro h
  have h00 : (mat2 (0 : ℂ) 1 0 0 * mat2 (0 : ℂ) 0 1 0) 0 0 =
             (mat2 (0 : ℂ) 0 1 0 * mat2 (0 : ℂ) 1 0 0) 0 0 := by
    rw [h]
  simp only [mul2_00, mat2_00, mat2_01, mat2_10, mul_zero, add_zero, zero_add, one_mul] at h00
  exact one_ne_zero h00

private lemma schrodingerDissipatorTerm_sqrt_smul (r : ℝ) (hr : 0 ≤ r) (L ρ : Mat2C) :
    schrodingerDissipatorTerm ((Real.sqrt r : ℂ) • L) ρ =
      ((r : ℂ) / 2) • lindbladDissipator2 L ρ := by
  have ext : True := trivial
  have h_sq : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    have h := Real.mul_self_sqrt hr
    exact_mod_cast h
  have h_c : star (Real.sqrt r : ℂ) = (Real.sqrt r : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have h_star_smul : star ((Real.sqrt r : ℂ) • L) = (Real.sqrt r : ℂ) • star L := by
    rw [star_smul, h_c]
  dsimp [schrodingerDissipatorTerm, lindbladDissipator2]
  change ((Real.sqrt r : ℂ) • L) * ρ * star ((Real.sqrt r : ℂ) • L) -
    (1 / 2 : ℂ) • (star ((Real.sqrt r : ℂ) • L) * ((Real.sqrt r : ℂ) • L) * ρ +
      ρ * star ((Real.sqrt r : ℂ) • L) * ((Real.sqrt r : ℂ) • L)) = _
  repeat rw [h_star_smul]
  have h_term1 : ((Real.sqrt r : ℂ) • L) * ρ * ((Real.sqrt r : ℂ) • star L) =
      (r : ℂ) • (L * ρ * star L) := by
    calc ((Real.sqrt r : ℂ) • L) * ρ * ((Real.sqrt r : ℂ) • star L)
      _ = (Real.sqrt r : ℂ) • (L * ρ) * ((Real.sqrt r : ℂ) • star L) := by rw [smul_mul_assoc]
      _ = ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) • (L * ρ * star L) := by rw [smul_mul_smul]
      _ = (r : ℂ) • (L * ρ * star L) := by rw [h_sq]
  have h_term2 : ((Real.sqrt r : ℂ) • star L) * ((Real.sqrt r : ℂ) • L) * ρ =
      (r : ℂ) • (star L * L * ρ) := by
    calc ((Real.sqrt r : ℂ) • star L) * ((Real.sqrt r : ℂ) • L) * ρ
      _ = (((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) • (star L * L)) * ρ := by rw [smul_mul_smul]
      _ = ((r : ℂ) • (star L * L)) * ρ := by rw [h_sq]
      _ = (r : ℂ) • (star L * L * ρ) := by rw [smul_mul_assoc]
  have h_term3 : ρ * ((Real.sqrt r : ℂ) • star L) * ((Real.sqrt r : ℂ) • L) =
      (r : ℂ) • (ρ * (star L * L)) := by
    calc ρ * ((Real.sqrt r : ℂ) • star L) * ((Real.sqrt r : ℂ) • L)
      _ = ((Real.sqrt r : ℂ) • (ρ * star L)) * ((Real.sqrt r : ℂ) • L) := by
        rw [mul_smul_comm (Real.sqrt r : ℂ) ρ (star L)]
      _ = ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) • (ρ * star L * L) := by rw [smul_mul_smul]
      _ = (r : ℂ) • (ρ * (star L * L)) := by rw [h_sq, mul_assoc]
  rw [h_term1, h_term2, h_term3]
  rw [← smul_add]
  rw [smul_smul]
  have h_two : (2 : Mat2C) * (L * ρ * star L) = (2 : ℂ) • (L * ρ * star L) := by
    rw [two_mul, two_smul]
  rw [h_two]
  rw [smul_sub]
  rw [smul_smul]
  congr 1
  · congr 1
    ring
  · congr 1
    ring

private lemma hamiltonianTerm_thermalHamiltonian (ω : ℝ) (ρ : Mat2C) :
    hamiltonianTerm (thermalHamiltonian ω) ρ =
      -(Complex.I * (ω : ℂ) / 2) • ⁅pauliGamma1, ρ⁆ := by
  have ext : True := trivial
  dsimp [hamiltonianTerm, thermalHamiltonian, Ring.lie_def]
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  change -Complex.I • (((ω / 2 : ℝ) : ℂ) • (pauliGamma1 * ρ - ρ * pauliGamma1)) = _
  rw [smul_smul]
  congr 1
  push_cast
  ring

/-- Deductive bridge welding `thermalLindbladianC` to `SchrodingerGKSL.schrodingerLindbladian`. -/
theorem thermalLindbladian_weld_to_schrodinger_and_gksl
    (γ ω θ : ℝ) (hγ : 0 ≤ γ) (ρ : Mat2C) :
    thermalLindbladianC γ ω θ ρ =
      SchrodingerGKSL.schrodingerLindbladian (thermalHamiltonian ω)
        ![(Real.sqrt (ratePlus γ θ) : ℂ) • wittFPlus,
          (Real.sqrt (rateMinus γ θ) : ℂ) • wittFMinus] ρ ∧
    thermalLindbladianOp γ 0 θ ρ =
      ((ratePlus γ θ : ℂ) / 2) • lindbladDissipator2 wittFPlus ρ +
      ((rateMinus γ θ : ℂ) / 2) • lindbladDissipator2 wittFMinus ρ := by
  have h_rp : 0 ≤ ratePlus γ θ := by
    dsimp [ratePlus]
    exact mul_nonneg hγ (le_of_lt (boltzmann_nonneg θ).1)
  have h_rm : 0 ≤ rateMinus γ θ := by
    dsimp [rateMinus]
    exact mul_nonneg hγ (le_of_lt (boltzmann_nonneg θ).2)
  have h_gksl_eq :
      SchrodingerGKSL.schrodingerLindbladian (thermalHamiltonian ω)
        ![(Real.sqrt (ratePlus γ θ) : ℂ) • wittFPlus,
          (Real.sqrt (rateMinus γ θ) : ℂ) • wittFMinus] ρ =
      thermalLindbladianOp γ ω θ ρ := by
    dsimp [SchrodingerGKSL.schrodingerLindbladian, schrodingerDissipator]
    rw [Fin.sum_univ_two]
    change hamiltonianTerm (thermalHamiltonian ω) ρ +
      (schrodingerDissipatorTerm ((Real.sqrt (ratePlus γ θ) : ℂ) • wittFPlus) ρ +
       schrodingerDissipatorTerm ((Real.sqrt (rateMinus γ θ) : ℂ) • wittFMinus) ρ) = _
    rw [schrodingerDissipatorTerm_sqrt_smul (ratePlus γ θ) h_rp wittFPlus ρ]
    rw [schrodingerDissipatorTerm_sqrt_smul (rateMinus γ θ) h_rm wittFMinus ρ]
    rw [hamiltonianTerm_thermalHamiltonian]
    dsimp [thermalLindbladianOp]
  refine ⟨?_, ?_⟩
  · rw [h_gksl_eq]
    exact (thermalLindbladianOp_eq_thermalLindbladianC γ ω θ ρ).symm
  · dsimp [thermalLindbladianOp]
    simp only [mul_zero, zero_div, zero_smul, neg_zero, zero_add]

/-- Physical Boltzmann cooling: negative parameter, negative magnetization, and KMS detailed balance. -/
theorem physical_boltzmann_cooling {β ω : ℝ} (hβ : 0 < β) (hω : 0 < ω) (γ : ℝ) :
    boltzmannTheta β ω < 0 ∧
    meanSpin (boltzmannTheta β ω) < 0 ∧
    ratePlus γ (boltzmannTheta β ω) = Real.exp (-β * ω) * rateMinus γ (boltzmannTheta β ω) := by
  have hθ_neg : boltzmannTheta β ω < 0 := by
    dsimp [boltzmannTheta]
    have h_pos : 0 < β * ω := mul_pos hβ hω
    linarith
  have h_ms_neg : meanSpin (boltzmannTheta β ω) < 0 := by
    dsimp [meanSpin]
    have hZ_pos := partitionZ_pos (boltzmannTheta β ω)
    rw [div_lt_iff₀ hZ_pos]
    simp only [zero_mul]
    have h_exp_lt : Real.exp (boltzmannTheta β ω) < Real.exp (-boltzmannTheta β ω) := by
      apply Real.exp_lt_exp.mpr
      linarith
    linarith
  have h_kms : ratePlus γ (boltzmannTheta β ω) * Real.exp (-(boltzmannTheta β ω)) =
      rateMinus γ (boltzmannTheta β ω) * Real.exp (boltzmannTheta β ω) := by
    dsimp [ratePlus, rateMinus, boltzmannPlus, boltzmannMinus]
    have h1 := one_add_meanSpin (boltzmannTheta β ω)
    have h2 := one_sub_meanSpin (boltzmannTheta β ω)
    have hZ := partitionZ_pos (boltzmannTheta β ω)
    apply mul_right_cancel₀ (ne_of_gt hZ)
    have h_Z_ne : partitionZ (boltzmannTheta β ω) ≠ 0 := ne_of_gt hZ
    have h_lhs : (γ * ((1 + meanSpin (boltzmannTheta β ω)) / 2) * Real.exp (-boltzmannTheta β ω)) * partitionZ (boltzmannTheta β ω) =
        γ * Real.exp (boltzmannTheta β ω) * Real.exp (-boltzmannTheta β ω) := by
      calc (γ * ((1 + meanSpin (boltzmannTheta β ω)) / 2) * Real.exp (-boltzmannTheta β ω)) * partitionZ (boltzmannTheta β ω)
        _ = γ * (((1 + meanSpin (boltzmannTheta β ω)) * partitionZ (boltzmannTheta β ω)) / 2) * Real.exp (-boltzmannTheta β ω) := by ring
        _ = γ * ((2 * Real.exp (boltzmannTheta β ω) / partitionZ (boltzmannTheta β ω) * partitionZ (boltzmannTheta β ω)) / 2) * Real.exp (-boltzmannTheta β ω) := by rw [h1]
        _ = γ * Real.exp (boltzmannTheta β ω) * Real.exp (-boltzmannTheta β ω) := by
          rw [div_mul_cancel₀ _ h_Z_ne]
          ring
    have h_rhs : (γ * ((1 - meanSpin (boltzmannTheta β ω)) / 2) * Real.exp (boltzmannTheta β ω)) * partitionZ (boltzmannTheta β ω) =
        γ * Real.exp (-boltzmannTheta β ω) * Real.exp (boltzmannTheta β ω) := by
      calc (γ * ((1 - meanSpin (boltzmannTheta β ω)) / 2) * Real.exp (boltzmannTheta β ω)) * partitionZ (boltzmannTheta β ω)
        _ = γ * (((1 - meanSpin (boltzmannTheta β ω)) * partitionZ (boltzmannTheta β ω)) / 2) * Real.exp (boltzmannTheta β ω) := by ring
        _ = γ * ((2 * Real.exp (-boltzmannTheta β ω) / partitionZ (boltzmannTheta β ω) * partitionZ (boltzmannTheta β ω)) / 2) * Real.exp (boltzmannTheta β ω) := by rw [h2]
        _ = γ * Real.exp (-boltzmannTheta β ω) * Real.exp (boltzmannTheta β ω) := by
          rw [div_mul_cancel₀ _ h_Z_ne]
          ring
    rw [h_lhs, h_rhs]
    ring
  have h_ratio : ratePlus γ (boltzmannTheta β ω) = Real.exp (-β * ω) * rateMinus γ (boltzmannTheta β ω) := by
    have h_prod : ratePlus γ (boltzmannTheta β ω) =
        (ratePlus γ (boltzmannTheta β ω) * Real.exp (-(boltzmannTheta β ω))) * Real.exp (boltzmannTheta β ω) := by
      calc ratePlus γ (boltzmannTheta β ω)
        _ = ratePlus γ (boltzmannTheta β ω) * (Real.exp (-(boltzmannTheta β ω)) * Real.exp (boltzmannTheta β ω)) := by
          rw [mul_comm (Real.exp _), exp_mul_exp_neg]
          ring
        _ = (ratePlus γ (boltzmannTheta β ω) * Real.exp (-(boltzmannTheta β ω))) * Real.exp (boltzmannTheta β ω) := by ring
    rw [h_prod, h_kms]
    have h_exp2 : Real.exp (boltzmannTheta β ω) * Real.exp (boltzmannTheta β ω) = Real.exp (2 * boltzmannTheta β ω) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h_2θ : 2 * boltzmannTheta β ω = -β * ω := by
      dsimp [boltzmannTheta]; ring
    calc rateMinus γ (boltzmannTheta β ω) * Real.exp (boltzmannTheta β ω) * Real.exp (boltzmannTheta β ω)
      _ = rateMinus γ (boltzmannTheta β ω) * (Real.exp (boltzmannTheta β ω) * Real.exp (boltzmannTheta β ω)) := by ring
      _ = rateMinus γ (boltzmannTheta β ω) * Real.exp (2 * boltzmannTheta β ω) := by rw [h_exp2]
      _ = rateMinus γ (boltzmannTheta β ω) * Real.exp (-β * ω) := by rw [h_2θ]
      _ = Real.exp (-β * ω) * rateMinus γ (boltzmannTheta β ω) := by ring
  exact ⟨hθ_neg, h_ms_neg, h_ratio⟩

private lemma carre_du_champ_channel (c : ℂ) (L A : Mat2C) :
    (c • heisenbergDissipator2 L (star A * A)) -
      ((c • heisenbergDissipator2 L (star A)) * A + star A * (c • heisenbergDissipator2 L A)) =
      (c * 2) • (star ⁅L, A⁆ * ⁅L, A⁆) := by
  have h_id := (algebraic_gksl_star_unital_and_carre_du_champ (B := Mat2C)
    (show star (0 : Mat2C) = -0 by simp) L 0 A).2.2.2
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add, ← smul_sub]
  rw [h_id]
  have h_two : (2 : Mat2C) * (star ⁅L, A⁆ * ⁅L, A⁆) = (2 : ℂ) • (star ⁅L, A⁆ * ⁅L, A⁆) := by
    rw [two_mul, two_smul]
  rw [h_two, smul_smul]

private lemma thermalCarreDuChamp_eq (γ θ : ℝ) (A : Mat2C) :
    thermalCarreDuChamp γ θ A =
      (ratePlus γ θ : ℂ) • (star ⁅wittFPlus, A⁆ * ⁅wittFPlus, A⁆) +
      (rateMinus γ θ : ℂ) • (star ⁅wittFMinus, A⁆ * ⁅wittFMinus, A⁆) := by
  dsimp [thermalCarreDuChamp, thermalHeisenbergDissipator]
  have h_p := carre_du_champ_channel ((ratePlus γ θ : ℂ) / 2) wittFPlus A
  have h_m := carre_du_champ_channel ((rateMinus γ θ : ℂ) / 2) wittFMinus A
  have h_cp : ((ratePlus γ θ : ℂ) / 2) * 2 = (ratePlus γ θ : ℂ) := by ring
  have h_cm : ((rateMinus γ θ : ℂ) / 2) * 2 = (rateMinus γ θ : ℂ) := by ring
  rw [h_cp] at h_p
  rw [h_cm] at h_m
  calc thermalHeisenbergDissipator γ θ (star A * A) -
      (thermalHeisenbergDissipator γ θ (star A) * A + star A * thermalHeisenbergDissipator γ θ A)
    _ = (((ratePlus γ θ : ℂ) / 2) • heisenbergDissipator2 wittFPlus (star A * A) -
          (((ratePlus γ θ : ℂ) / 2) • heisenbergDissipator2 wittFPlus (star A) * A +
            star A * ((ratePlus γ θ : ℂ) / 2) • heisenbergDissipator2 wittFPlus A)) +
        (((rateMinus γ θ : ℂ) / 2) • heisenbergDissipator2 wittFMinus (star A * A) -
          (((rateMinus γ θ : ℂ) / 2) • heisenbergDissipator2 wittFMinus (star A) * A +
            star A * ((rateMinus γ θ : ℂ) / 2) • heisenbergDissipator2 wittFMinus A)) := by
      dsimp [thermalHeisenbergDissipator]
      rw [add_mul, mul_add]
      abel
    _ = (ratePlus γ θ : ℂ) • (star ⁅wittFPlus, A⁆ * ⁅wittFPlus, A⁆) +
        (rateMinus γ θ : ℂ) • (star ⁅wittFMinus, A⁆ * ⁅wittFMinus, A⁆) := by
      rw [h_p, h_m]

private lemma lie_wittFPlus_pauliSigmaX : ⁅wittFPlus, pauliSigmaX⁆ = mat2 1 0 0 (-1) := by
  rw [wittFPlus_eq, pauliSigmaX_eq]
  apply ext_mat2
  · simp only [Ring.lie_def, mul2_00, mat2_00, mat2_01, mat2_10, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_01, mat2_00, mat2_01, mat2_11, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_10, mat2_00, mat2_10, mat2_11, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_11, mat2_01, mat2_10, mat2_11, Matrix.sub_apply]; ring

private lemma lie_wittFMinus_pauliSigmaX : ⁅wittFMinus, pauliSigmaX⁆ = mat2 (-1) 0 0 1 := by
  rw [wittFMinus_eq, pauliSigmaX_eq]
  apply ext_mat2
  · simp only [Ring.lie_def, mul2_00, mat2_00, mat2_01, mat2_10, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_01, mat2_00, mat2_01, mat2_11, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_10, mat2_00, mat2_10, mat2_11, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_11, mat2_01, mat2_10, mat2_11, Matrix.sub_apply]; ring

private lemma lie_wittFPlus_pauliSigmaY : ⁅wittFPlus, pauliSigmaY⁆ = mat2 Complex.I 0 0 (-Complex.I) := by
  rw [wittFPlus_eq, pauliSigmaY_eq]
  apply ext_mat2
  · simp only [Ring.lie_def, mul2_00, mat2_00, mat2_01, mat2_10, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_01, mat2_00, mat2_01, mat2_11, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_10, mat2_00, mat2_10, mat2_11, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_11, mat2_01, mat2_10, mat2_11, Matrix.sub_apply]; ring

private lemma lie_wittFMinus_pauliSigmaY : ⁅wittFMinus, pauliSigmaY⁆ = mat2 Complex.I 0 0 (-Complex.I) := by
  rw [wittFMinus_eq, pauliSigmaY_eq]
  apply ext_mat2
  · simp only [Ring.lie_def, mul2_00, mat2_00, mat2_01, mat2_10, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_01, mat2_00, mat2_01, mat2_11, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_10, mat2_00, mat2_10, mat2_11, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_11, mat2_01, mat2_10, mat2_11, Matrix.sub_apply]; ring

private lemma lie_wittFPlus_pauliGamma1 : ⁅wittFPlus, pauliGamma1⁆ = mat2 0 (-2) 0 0 := by
  rw [wittFPlus_eq, pauliGamma1_eq]
  apply ext_mat2
  · simp only [Ring.lie_def, mul2_00, mat2_00, mat2_01, mat2_10, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_01, mat2_00, mat2_01, mat2_11, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_10, mat2_00, mat2_10, mat2_11, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_11, mat2_01, mat2_10, mat2_11, Matrix.sub_apply]; ring

private lemma lie_wittFMinus_pauliGamma1 : ⁅wittFMinus, pauliGamma1⁆ = mat2 0 0 2 0 := by
  rw [wittFMinus_eq, pauliGamma1_eq]
  apply ext_mat2
  · simp only [Ring.lie_def, mul2_00, mat2_00, mat2_01, mat2_10, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_01, mat2_00, mat2_01, mat2_11, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_10, mat2_00, mat2_10, mat2_11, Matrix.sub_apply]; ring
  · simp only [Ring.lie_def, mul2_11, mat2_01, mat2_10, mat2_11, Matrix.sub_apply]; ring

private lemma heis_plus_sigmaX : heisenbergDissipator2 wittFPlus pauliSigmaX = -pauliSigmaX := by
  dsimp [heisenbergDissipator2]
  rw [two_mul, wittFPlus_eq, pauliSigmaX_eq]
  apply ext_mat2
  · simp only [mul2_00, mul2_01, mul2_10, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring
  · simp only [mul2_00, mul2_01, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring
  · simp only [mul2_00, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring
  · simp only [mul2_01, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring

private lemma heis_minus_sigmaX : heisenbergDissipator2 wittFMinus pauliSigmaX = -pauliSigmaX := by
  dsimp [heisenbergDissipator2]
  rw [two_mul, wittFMinus_eq, pauliSigmaX_eq]
  apply ext_mat2
  · simp only [mul2_00, mul2_01, mul2_10, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring
  · simp only [mul2_00, mul2_01, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring
  · simp only [mul2_00, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring
  · simp only [mul2_01, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring

private lemma heis_plus_sigmaY : heisenbergDissipator2 wittFPlus pauliSigmaY = -pauliSigmaY := by
  dsimp [heisenbergDissipator2]
  rw [two_mul, wittFPlus_eq, pauliSigmaY_eq]
  apply ext_mat2
  · simp only [mul2_00, mul2_01, mul2_10, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring
  · simp only [mul2_00, mul2_01, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring
  · simp only [mul2_00, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring
  · simp only [mul2_01, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring

private lemma heis_minus_sigmaY : heisenbergDissipator2 wittFMinus pauliSigmaY = -pauliSigmaY := by
  dsimp [heisenbergDissipator2]
  rw [two_mul, wittFMinus_eq, pauliSigmaY_eq]
  apply ext_mat2
  · simp only [mul2_00, mul2_01, mul2_10, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring
  · simp only [mul2_00, mul2_01, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring
  · simp only [mul2_00, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring
  · simp only [mul2_01, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]; ring

private lemma heis_plus_gamma1 : heisenbergDissipator2 wittFPlus pauliGamma1 = mat2 0 0 0 4 := by
  dsimp [heisenbergDissipator2]
  rw [two_mul, wittFPlus_eq, pauliGamma1_eq]
  apply ext_mat2
  · simp only [mul2_00, mul2_01, mul2_10, mat2_00, mat2_01, mat2_10, mat2_11, star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply]; ring
  · simp only [mul2_00, mul2_01, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11, star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply]; ring
  · simp only [mul2_00, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11, star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply]; ring
  · simp only [mul2_01, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11, star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply]; ring

private lemma heis_minus_gamma1 : heisenbergDissipator2 wittFMinus pauliGamma1 = mat2 (-4) 0 0 0 := by
  dsimp [heisenbergDissipator2]
  rw [two_mul, wittFMinus_eq, pauliGamma1_eq]
  apply ext_mat2
  · simp only [mul2_00, mul2_01, mul2_10, mat2_00, mat2_01, mat2_10, mat2_11, star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply]; ring
  · simp only [mul2_00, mul2_01, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11, star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply]; ring
  · simp only [mul2_00, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11, star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply]; ring
  · simp only [mul2_01, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11, star_mat2, star_zero, star_one, Matrix.add_apply, Matrix.sub_apply]; ring

private lemma star_two : star (2 : ℂ) = 2 := by
  rw [Complex.star_def]
  exact Complex.conj_ofNat 2

private lemma star_neg_two : star (-2 : ℂ) = -2 := by
  rw [Complex.star_def, map_neg]
  exact congrArg (-·) (Complex.conj_ofNat 2)

private lemma carre_pauliGamma1_eq (γ θ : ℝ) :
    thermalCarreDuChamp γ θ pauliGamma1 =
      mat2 ((4 * rateMinus γ θ : ℝ) : ℂ) 0 0 ((4 * ratePlus γ θ : ℝ) : ℂ) := by
  rw [thermalCarreDuChamp_eq γ θ pauliGamma1, lie_wittFPlus_pauliGamma1, lie_wittFMinus_pauliGamma1]
  apply ext_mat2
  · simp only [mul2_00, mat2_00, mat2_01, mat2_10, star_mat2, star_zero, star_neg_two, star_two,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast; ring
  · simp only [mul2_01, mat2_00, mat2_01, mat2_11, star_mat2, star_zero, star_neg_two, star_two,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · simp only [mul2_10, mat2_00, mat2_10, mat2_11, star_mat2, star_zero, star_neg_two, star_two,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · simp only [mul2_11, mat2_01, mat2_10, mat2_11, star_mat2, star_zero, star_neg_two, star_two,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast; ring

/-- Rung 1: Square-defect carre du champ, 1:2 damping ratio, and Gibbs trace expectation. -/
theorem rung1_carre_du_champ_square_defect_and_damping_ratio (γ θ : ℝ) (A : Mat2C) :
    thermalCarreDuChamp γ θ A =
      (ratePlus γ θ : ℂ) • (star ⁅wittFPlus, A⁆ * ⁅wittFPlus, A⁆) +
      (rateMinus γ θ : ℂ) • (star ⁅wittFMinus, A⁆ * ⁅wittFMinus, A⁆) ∧
    thermalCarreDuChamp γ θ pauliSigmaX = (γ : ℂ) • 1 ∧
    thermalCarreDuChamp γ θ pauliSigmaY = (γ : ℂ) • 1 ∧
    thermalHeisenbergDissipator γ θ pauliSigmaX = -((γ / 2 : ℝ) : ℂ) • pauliSigmaX ∧
    thermalHeisenbergDissipator γ θ pauliSigmaY = -((γ / 2 : ℝ) : ℂ) • pauliSigmaY ∧
    thermalHeisenbergDissipator γ θ pauliGamma1 =
      -(γ : ℂ) • (pauliGamma1 - (meanSpin θ : ℂ) • 1) ∧
    Matrix.trace (gibbsDensityC θ * thermalCarreDuChamp γ θ pauliGamma1) =
      ((2 * γ * (1 - (meanSpin θ) ^ 2) : ℝ) : ℂ) := by
  have h_rate_sum : (ratePlus γ θ : ℂ) + (rateMinus γ θ : ℂ) = (γ : ℂ) := by
    have h_bsum : (boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ) = 1 := by
      exact_mod_cast (boltzmann_sum_and_diff θ).1
    dsimp [ratePlus, rateMinus]
    push_cast
    calc (γ : ℂ) * boltzmannPlus θ + (γ : ℂ) * boltzmannMinus θ
      _ = (γ : ℂ) * (boltzmannPlus θ + boltzmannMinus θ) := by ring
      _ = (γ : ℂ) := by rw [h_bsum, mul_one]
  refine ⟨thermalCarreDuChamp_eq γ θ A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [thermalCarreDuChamp_eq γ θ pauliSigmaX, lie_wittFPlus_pauliSigmaX, lie_wittFMinus_pauliSigmaX, one_mat2_eq]
    apply ext_mat2
    · simp only [mul2_00, mat2_00, mat2_01, mat2_10, star_mat2, star_zero, star_one, star_neg,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination h_rate_sum
    · simp only [mul2_01, mat2_00, mat2_01, mat2_11, star_mat2, star_zero, star_one, star_neg,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    · simp only [mul2_10, mat2_00, mat2_10, mat2_11, star_mat2, star_zero, star_one, star_neg,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    · simp only [mul2_11, mat2_01, mat2_10, mat2_11, star_mat2, star_zero, star_one, star_neg,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination h_rate_sum
  · rw [thermalCarreDuChamp_eq γ θ pauliSigmaY, lie_wittFPlus_pauliSigmaY, lie_wittFMinus_pauliSigmaY, one_mat2_eq]
    apply ext_mat2
    · simp only [mul2_00, mat2_00, mat2_01, mat2_10, star_mat2, star_zero, star_neg,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [Complex.star_def, Complex.conj_I]
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination h_rate_sum - ((ratePlus γ θ : ℂ) + (rateMinus γ θ : ℂ)) * hI
    · simp only [mul2_01, mat2_00, mat2_01, mat2_11, star_mat2, star_zero, star_neg,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    · simp only [mul2_10, mat2_00, mat2_10, mat2_11, star_mat2, star_zero, star_neg,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    · simp only [mul2_11, mat2_01, mat2_10, mat2_11, star_mat2, star_zero, star_neg,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [Complex.star_def, Complex.conj_I]
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination h_rate_sum - ((ratePlus γ θ : ℂ) + (rateMinus γ θ : ℂ)) * hI
  · dsimp [thermalHeisenbergDissipator]
    rw [heis_plus_sigmaX, heis_minus_sigmaX, pauliSigmaX_eq]
    have h_half : ((γ / 2 : ℝ) : ℂ) = (γ : ℂ) / 2 := by
      push_cast
      rfl
    apply ext_mat2
    · simp only [mat2_00, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]; ring
    · simp only [mat2_01, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
      rw [h_half]
      calc (ratePlus γ θ : ℂ) / 2 * -1 + (rateMinus γ θ : ℂ) / 2 * -1
        _ = - (((ratePlus γ θ : ℂ) + (rateMinus γ θ : ℂ)) / 2) := by ring
        _ = - ((γ : ℂ) / 2) := by rw [h_rate_sum]
        _ = - ((γ : ℂ) / 2) * 1 := by ring
    · simp only [mat2_10, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
      rw [h_half]
      calc (ratePlus γ θ : ℂ) / 2 * -1 + (rateMinus γ θ : ℂ) / 2 * -1
        _ = - (((ratePlus γ θ : ℂ) + (rateMinus γ θ : ℂ)) / 2) := by ring
        _ = - ((γ : ℂ) / 2) := by rw [h_rate_sum]
        _ = - ((γ : ℂ) / 2) * 1 := by ring
    · simp only [mat2_11, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]; ring
  · dsimp [thermalHeisenbergDissipator]
    rw [heis_plus_sigmaY, heis_minus_sigmaY, pauliSigmaY_eq]
    have h_half : ((γ / 2 : ℝ) : ℂ) = (γ : ℂ) / 2 := by
      push_cast
      rfl
    apply ext_mat2
    · simp only [mat2_00, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]; ring
    · simp only [mat2_01, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, neg_neg]
      rw [h_half]
      calc (ratePlus γ θ : ℂ) / 2 * Complex.I + (rateMinus γ θ : ℂ) / 2 * Complex.I
        _ = (((ratePlus γ θ : ℂ) + (rateMinus γ θ : ℂ)) / 2) * Complex.I := by ring
        _ = ((γ : ℂ) / 2) * Complex.I := by rw [h_rate_sum]
        _ = - ((γ : ℂ) / 2) * -Complex.I := by ring
    · simp only [mat2_10, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
      rw [h_half]
      calc (ratePlus γ θ : ℂ) / 2 * -Complex.I + (rateMinus γ θ : ℂ) / 2 * -Complex.I
        _ = - ((((ratePlus γ θ : ℂ) + (rateMinus γ θ : ℂ)) / 2) * Complex.I) := by ring
        _ = - (((γ : ℂ) / 2) * Complex.I) := by rw [h_rate_sum]
        _ = - ((γ : ℂ) / 2) * Complex.I := by ring
    · simp only [mat2_11, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]; ring
  · dsimp [thermalHeisenbergDissipator]
    rw [heis_plus_gamma1, heis_minus_gamma1, pauliGamma1_eq, one_mat2_eq]
    have h_rate_sub : (ratePlus γ θ : ℂ) - (rateMinus γ θ : ℂ) = (γ : ℂ) * (meanSpin θ : ℂ) := by
      have h_bdiff : (boltzmannPlus θ : ℂ) - (boltzmannMinus θ : ℂ) = (meanSpin θ : ℂ) := by
        exact_mod_cast (boltzmann_sum_and_diff θ).2
      dsimp [ratePlus, rateMinus]
      push_cast
      calc (γ : ℂ) * boltzmannPlus θ - (γ : ℂ) * boltzmannMinus θ
        _ = (γ : ℂ) * (boltzmannPlus θ - boltzmannMinus θ) := by ring
        _ = (γ : ℂ) * (meanSpin θ : ℂ) := by rw [h_bdiff]
    apply ext_mat2
    · simp only [mat2_00, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      calc (ratePlus γ θ : ℂ) / 2 * 0 + (rateMinus γ θ : ℂ) / 2 * -4
        _ = - 2 * (rateMinus γ θ : ℂ) := by ring
        _ = - ((γ : ℂ) - (γ : ℂ) * (meanSpin θ : ℂ)) := by
          linear_combination - h_rate_sum + h_rate_sub
        _ = - (γ : ℂ) * (1 - (meanSpin θ : ℂ) * 1) := by ring
    · simp only [mat2_01, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, smul_zero, mul_zero, sub_zero, add_zero]
    · simp only [mat2_10, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, smul_zero, mul_zero, sub_zero, add_zero]
    · simp only [mat2_11, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      calc (ratePlus γ θ : ℂ) / 2 * 4 + (rateMinus γ θ : ℂ) / 2 * 0
        _ = 2 * (ratePlus γ θ : ℂ) := by ring
        _ = (γ : ℂ) + (γ : ℂ) * (meanSpin θ : ℂ) := by
          linear_combination h_rate_sum + h_rate_sub
        _ = - (γ : ℂ) * (-1 - (meanSpin θ : ℂ) * 1) := by ring
  · rw [carre_pauliGamma1_eq, gibbsDensityC]
    rw [trace_fin2]
    simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11]
    have h_bp : boltzmannPlus θ = (1 + meanSpin θ) / 2 := by
      have h1 := (boltzmann_sum_and_diff θ).1
      have h2 := (boltzmann_sum_and_diff θ).2
      linarith
    have h_bm : boltzmannMinus θ = (1 - meanSpin θ) / 2 := by
      have h1 := (boltzmann_sum_and_diff θ).1
      have h2 := (boltzmann_sum_and_diff θ).2
      linarith
    dsimp [ratePlus, rateMinus]
    push_cast
    rw [h_bp, h_bm]
    push_cast
    ring

/-!
### Section 2: $Y_1 \prec Y_2$ & Rung 2: Kolmogorov Forward ODE, Determinant, and Positivity Monoid
-/

/-- Bloch x coordinate $r_x = 2 \operatorname{Re}(\rho_{01})$. -/
def blochX (ρ : Mat2C) : ℝ := 2 * (ρ 0 1).re

/-- Bloch y coordinate $r_y = -2 \operatorname{Im}(\rho_{01})$. -/
def blochY (ρ : Mat2C) : ℝ := -2 * (ρ 0 1).im

/-- Bloch z coordinate $r_z = \operatorname{Re}(\rho_{00} - \rho_{11})$. -/
def blochZ (ρ : Mat2C) : ℝ := (ρ 0 0 - ρ 1 1).re

/-- Transverse coherence square $C^2(\rho) = 4 |\rho_{01}|^2 = r_x^2 + r_y^2$. -/
def coherenceSq (ρ : Mat2C) : ℝ := 4 * Complex.normSq (ρ 0 1)

/-- Full Bloch norm square $\|\mathbf{r}\|^2 = r_z^2 + C^2(\rho)$. -/
def blochNormSq (ρ : Mat2C) : ℝ := blochZ ρ ^ 2 + coherenceSq ρ

/-- Bloch radius $r = \sqrt{\|\mathbf{r}\|^2}$. -/
def blochRadius (ρ : Mat2C) : ℝ := Real.sqrt (blochNormSq ρ)

/-- Density matrix corresponding to Bloch vector $\mathbf{v} \in \mathbb{R}^3$. -/
def blochState (v : EuclideanSpace ℝ (Fin 3)) : Mat2C :=
  mat2 ((1 + v 2 : ℂ) / 2) ((v 0 - Complex.I * v 1 : ℂ) / 2)
       ((v 0 + Complex.I * v 1 : ℂ) / 2) ((1 - v 2 : ℂ) / 2)

/-- State lies in the open Bloch ball: self-adjoint, unit trace, $\|\mathbf{r}\|^2 < 1$. -/
def InOpenBlochBall (ρ : Mat2C) : Prop :=
  IsSelfAdjoint ρ ∧ Matrix.trace ρ = 1 ∧ blochNormSq ρ < 1

private lemma blochNormSq_nonneg (ρ : Mat2C) : 0 ≤ blochNormSq ρ := by
  dsimp [blochNormSq, coherenceSq]
  have hns : 0 ≤ Complex.normSq (ρ 0 1) := Complex.normSq_nonneg _
  positivity

private lemma blochRadius_sq (ρ : Mat2C) : (blochRadius ρ) ^ 2 = blochNormSq ρ :=
  Real.sq_sqrt (blochNormSq_nonneg ρ)

private lemma blochRadius_lt_one {ρ : Mat2C} (hb : blochNormSq ρ < 1) : blochRadius ρ < 1 := by
  dsimp [blochRadius]
  have h1 : Real.sqrt (blochNormSq ρ) < Real.sqrt 1 := Real.sqrt_lt_sqrt (blochNormSq_nonneg ρ) hb
  rwa [Real.sqrt_one] at h1

private lemma blochRadius_nonneg (ρ : Mat2C) : 0 ≤ blochRadius ρ :=
  Real.sqrt_nonneg _

private lemma blochZ_abs_lt_one {ρ : Mat2C} (hb : blochNormSq ρ < 1) :
    -1 < blochZ ρ ∧ blochZ ρ < 1 := by
  have h_sq : (blochZ ρ) ^ 2 ≤ blochNormSq ρ := by
    dsimp [blochNormSq, coherenceSq]
    have hns : 0 ≤ 4 * Complex.normSq (ρ 0 1) := mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
    linarith
  have h_lt : (blochZ ρ) ^ 2 < 1 := lt_of_le_of_lt h_sq hb
  have h_abs : |blochZ ρ| < 1 := by
    rwa [← sq_lt_one_iff_abs_lt_one]
  exact abs_lt.mp h_abs

private lemma trace_real_smul (c : ℝ) (M : Mat2C) :
    Matrix.trace (c • M) = (c : ℂ) * Matrix.trace M := by
  rw [trace_fin2, trace_fin2]
  simp only [Matrix.smul_apply, Complex.real_smul]
  ring

private lemma trace_one_mat2 : Matrix.trace (1 : Mat2C) = 2 := by
  rw [trace_fin2]; simp; norm_num

private lemma hermitian_unitTrace_entries {ρ : Mat2C}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) :
    ρ 0 0 = (((1 + blochZ ρ) / 2 : ℝ) : ℂ) ∧
    ρ 1 1 = (((1 - blochZ ρ) / 2 : ℝ) : ℂ) ∧
    ρ 1 0 = star (ρ 0 1) ∧
    Matrix.trace (ρ * pauliGamma1) = (blochZ ρ : ℂ) := by
  have hstar : star ρ = ρ := hsa.star_eq
  have h00_s : star (ρ 0 0) = ρ 0 0 := by
    have h := congrArg (fun M : Mat2C => M 0 0) hstar
    simpa [Matrix.star_apply] using h
  have h11_s : star (ρ 1 1) = ρ 1 1 := by
    have h := congrArg (fun M : Mat2C => M 1 1) hstar
    simpa [Matrix.star_apply] using h
  have h10_s : ρ 1 0 = star (ρ 0 1) := by
    have h := congrArg (fun M : Mat2C => M 1 0) hstar
    simpa [Matrix.star_apply] using h.symm
  have h00_im : (ρ 0 0).im = 0 := by
    have h := congrArg Complex.im h00_s
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have h11_im : (ρ 1 1).im = 0 := by
    have h := congrArg Complex.im h11_s
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have h_tr_c : ρ 0 0 + ρ 1 1 = 1 := by
    rw [trace_fin2] at htr; exact htr
  have h_tr_re : (ρ 0 0).re + (ρ 1 1).re = 1 := by
    have h := congrArg Complex.re h_tr_c
    simp only [Complex.add_re, Complex.one_re] at h
    exact h
  have h_pg_c : Matrix.trace (ρ * pauliGamma1) = ρ 0 0 - ρ 1 1 := by
    rw [trace_fin2, mul2_00, mul2_11, pauliGamma1_eq]
    simp only [mat2_00, mat2_01, mat2_10, mat2_11, mul_zero, add_zero]
    ring
  have h_bz_eq : blochZ ρ = (ρ 0 0).re - (ρ 1 1).re := by
    rw [blochZ, Complex.sub_re]
  have h00_re : (ρ 0 0).re = (1 + blochZ ρ) / 2 := by linarith
  have h11_re : (ρ 1 1).re = (1 - blochZ ρ) / 2 := by linarith
  have h00 : ρ 0 0 = (((1 + blochZ ρ) / 2 : ℝ) : ℂ) :=
    Complex.ext (by simp [h00_re]) (by simp [h00_im])
  have h11 : ρ 1 1 = (((1 - blochZ ρ) / 2 : ℝ) : ℂ) :=
    Complex.ext (by simp [h11_re]) (by simp [h11_im])
  have h_pg : Matrix.trace (ρ * pauliGamma1) = (blochZ ρ : ℂ) := by
    rw [h_pg_c, h00, h11]
    push_cast; ring
  exact ⟨h00, h11, h10_s, h_pg⟩

private lemma bloch_centered_sq_eq_scalar {ρ : Mat2C}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) :
    (ρ - (1 / 2 : ℝ) • (1 : Mat2C)) *
      (ρ - (1 / 2 : ℝ) • (1 : Mat2C)) =
      (blochNormSq ρ / 4 : ℝ) • (1 : Mat2C) := by
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, _⟩
  have h_norm : ρ 0 1 * star (ρ 0 1) = (Complex.normSq (ρ 0 1) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  have h_norm' : star (ρ 0 1) * ρ 0 1 = (Complex.normSq (ρ 0 1) : ℂ) := by
    rw [mul_comm, h_norm]
  apply ext_mat2
  · simp only [mul2_00, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Complex.real_smul,
      h00, h10, Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte, mul_zero, mul_one, sub_zero]
    rw [h_norm]
    dsimp [blochNormSq, coherenceSq]
    push_cast; ring_nf
  · simp only [mul2_01, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Complex.real_smul,
      h00, h11, Fin.isValue, zero_ne_one, ↓reduceIte, mul_zero, mul_one, sub_zero]
    push_cast; ring_nf
  · simp only [mul2_10, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Complex.real_smul,
      h00, h11, h10, Fin.isValue, one_ne_zero, ↓reduceIte, mul_zero, mul_one, sub_zero]
    push_cast; ring_nf
  · simp only [mul2_11, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Complex.real_smul,
      h11, h10, Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte, mul_zero, mul_one, sub_zero]
    rw [h_norm']
    dsimp [blochNormSq, coherenceSq]
    push_cast; ring_nf

/-- Entrywise Kolmogorov forward ODE for the thermal GKSL semigroup. -/
theorem forward_kolmogorov_ode (γ ω θ : ℝ) (ρ : Mat2C) (i j : Fin 2) (t : ℝ) :
    HasDerivAt (fun s => thermalSemigroupC γ ω θ s ρ i j)
      (thermalLindbladianOp γ ω θ (thermalSemigroupC γ ω θ t ρ) i j) t := by
  rw [thermalLindbladianOp_eq_thermalLindbladianC]
  have hd_id : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hd_id_c : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := hd_id.ofReal_comp
  have hd_epop : HasDerivAt (fun s : ℝ => (Real.exp (-γ * s) : ℂ))
      ((-γ * Real.exp (-γ * t) : ℝ) : ℂ) t := by
    have hd_lin : HasDerivAt (fun s : ℝ => -γ * s) (-γ) t := by
      simpa using hd_id.const_mul (-γ)
    have hr : HasDerivAt (fun s : ℝ => Real.exp (-γ * s)) (Real.exp (-γ * t) * (-γ)) t :=
      (Real.hasDerivAt_exp (-γ * t)).comp t hd_lin
    exact (hr.congr_deriv (by ring_nf)).ofReal_comp
  have hd_ecoh : HasDerivAt (fun s : ℝ => (Real.exp (-(γ / 2) * s) : ℂ))
      ((-(γ / 2) * Real.exp (-(γ / 2) * t) : ℝ) : ℂ) t := by
    have hd_lin : HasDerivAt (fun s : ℝ => -(γ / 2) * s) (-(γ / 2)) t := by
      simpa using hd_id.const_mul (-(γ / 2))
    have hr : HasDerivAt (fun s : ℝ => Real.exp (-(γ / 2) * s))
        (Real.exp (-(γ / 2) * t) * (-(γ / 2))) t :=
      (Real.hasDerivAt_exp (-(γ / 2) * t)).comp t hd_lin
    exact (hr.congr_deriv (by ring_nf)).ofReal_comp
  have hd_php : HasDerivAt (fun s : ℝ => Complex.exp (-Complex.I * (ω : ℂ) * (s : ℂ)))
      (-Complex.I * (ω : ℂ) * Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ))) t := by
    have h_arg : HasDerivAt (fun s : ℝ => -Complex.I * (ω : ℂ) * (s : ℂ))
        (-Complex.I * (ω : ℂ)) t := by
      simpa using hd_id_c.const_mul (-Complex.I * (ω : ℂ))
    exact ((Complex.hasDerivAt_exp _).comp t h_arg).congr_deriv (by ring_nf)
  have hd_phm : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * (ω : ℂ) * (s : ℂ)))
      (Complex.I * (ω : ℂ) * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) t := by
    have h_arg : HasDerivAt (fun s : ℝ => Complex.I * (ω : ℂ) * (s : ℂ))
        (Complex.I * (ω : ℂ)) t := by
      simpa using hd_id_c.const_mul (Complex.I * (ω : ℂ))
    exact ((Complex.hasDerivAt_exp _).comp t h_arg).congr_deriv (by ring_nf)
  fin_cases i <;> fin_cases j
  · have hd00 := (hasDerivAt_const t ((boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1))).fun_add
      (hd_epop.mul_const (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1)))
    refine hd00.congr_deriv ?_
    trans (-(rateMinus γ θ : ℂ) * ((boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * t) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1))) +
        (ratePlus γ θ : ℂ) * ((boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * t) : ℂ) * (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1))))
    · dsimp [ratePlus, rateMinus, boltzmannPlus, boltzmannMinus]; push_cast; ring_nf
    · rfl
  · have hd01 := (hd_ecoh.fun_mul hd_php).mul_const (ρ 0 1)
    refine hd01.congr_deriv ?_
    trans (-(((γ / 2 : ℝ) : ℂ) + Complex.I * (ω : ℂ)) *
        ((Real.exp (-(γ / 2) * t) : ℂ) * Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ)) * ρ 0 1))
    · push_cast; ring_nf
    · rfl
  · have hd10 := (hd_ecoh.fun_mul hd_phm).mul_const (ρ 1 0)
    refine hd10.congr_deriv ?_
    trans (-(((γ / 2 : ℝ) : ℂ) - Complex.I * (ω : ℂ)) *
        ((Real.exp (-(γ / 2) * t) : ℂ) * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ)) * ρ 1 0))
    · push_cast; ring_nf
    · rfl
  · have hd11 := (hasDerivAt_const t ((boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1))).fun_add
      (hd_epop.mul_const (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1)))
    refine hd11.congr_deriv ?_
    trans ((rateMinus γ θ : ℂ) * ((boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * t) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1))) -
        (ratePlus γ θ : ℂ) * ((boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * t) : ℂ) * (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1))))
    · dsimp [ratePlus, rateMinus, boltzmannPlus, boltzmannMinus]; push_cast; ring_nf
    · rfl

private def spectralProjector (ρ : Mat2C) : Mat2C :=
  if blochRadius ρ = 0 then mat2 1 0 0 0
  else (blochRadius ρ)⁻¹ • (ρ - ((1 - blochRadius ρ) / 2 : ℝ) • (1 : Mat2C))

private lemma spectralProjector_twoSheet_and_cfc_log
    {ρ : Mat2C}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (hb : blochNormSq ρ < 1) :
    IsStarProjection (spectralProjector ρ) ∧
    Matrix.trace (spectralProjector ρ) = 1 ∧
    twoSheet (spectralProjector ρ) ((1 + blochRadius ρ) / 2) ((1 - blochRadius ρ) / 2) = ρ ∧
    IsStrictlyPositive ρ ∧
    CFC.log ρ =
      twoSheet (spectralProjector ρ)
        (Real.log ((1 + blochRadius ρ) / 2))
        (Real.log ((1 - blochRadius ρ) / 2)) := by
  have h_decomp : IsStarProjection (spectralProjector ρ) ∧
      Matrix.trace (spectralProjector ρ) = 1 ∧
      twoSheet (spectralProjector ρ) ((1 + blochRadius ρ) / 2) ((1 - blochRadius ρ) / 2) = ρ := by
    by_cases hr : blochRadius ρ = 0
    · have hbn0 : blochNormSq ρ = 0 := by
        rw [← blochRadius_sq ρ, hr]; ring
      have hc0 : coherenceSq ρ = 0 ∧ blochZ ρ = 0 := by
        have hns : 0 ≤ Complex.normSq (ρ 0 1) := Complex.normSq_nonneg _
        dsimp [blochNormSq, coherenceSq] at hbn0
        constructor
        · dsimp [coherenceSq]; nlinarith [sq_nonneg (blochZ ρ)]
        · nlinarith [sq_nonneg (blochZ ρ)]
      have h01_0 : ρ 0 1 = 0 := by
        dsimp [coherenceSq] at hc0
        exact Complex.normSq_eq_zero.mp (by linarith)
      rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, _⟩
      have hρ_half : ((1 / 2 : ℝ) • (1 : Mat2C)) = ρ := by
        apply ext_mat2 <;>
          simp only [Matrix.smul_apply, Complex.real_smul, Matrix.one_apply,
            h00, h11, h10, hc0.2, h01_0, star_zero, Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte] <;>
          push_cast <;> norm_num
      have hP_def : spectralProjector ρ = mat2 1 0 0 0 := by
        simp [spectralProjector, hr]
      rw [hP_def]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · change mat2 (1 : ℂ) 0 0 0 * mat2 1 0 0 0 = mat2 1 0 0 0
        apply ext_mat2 <;> simp [mul2_00, mul2_01, mul2_10, mul2_11]
      · change star (mat2 (1 : ℂ) 0 0 0) = mat2 1 0 0 0
        apply ext_mat2 <;> simp [Matrix.star_apply]
      · rw [trace_fin2]; simp
      · have h_half_eq : (1 + blochRadius ρ) / 2 = (1 - blochRadius ρ) / 2 := by
          rw [hr]; ring
        rw [h_half_eq, twoSheet_equal]
        have h_eq1 : (1 - blochRadius ρ) / 2 = (1 / 2 : ℝ) := by rw [hr]; ring
        rw [h_eq1, hρ_half]
    · set r := blochRadius ρ
      have hP_def : spectralProjector ρ =
          r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Mat2C)) := by
        simp [spectralProjector, r, hr]
      rw [hP_def]
      have h_saP : IsSelfAdjoint
          (r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Mat2C))) := by
        rw [IsSelfAdjoint, star_smul, star_sub, star_smul, star_one, hsa.star_eq]
        simp only [star_trivial]
      let Δ := ρ - (1 / 2 : ℝ) • (1 : Mat2C)
      have h_shift : ρ - ((1 - r) / 2 : ℝ) • (1 : Mat2C) =
          Δ + (r / 2 : ℝ) • (1 : Mat2C) := by
        dsimp [Δ]
        have hs : ((1 - r) / 2 : ℝ) • (1 : Mat2C) =
            (1 / 2 : ℝ) • (1 : Mat2C) -
              (r / 2 : ℝ) • (1 : Mat2C) := by
          rw [← sub_smul]; congr 1; ring
        rw [hs]; abel
      have h_sq_shift :
          (Δ + (r / 2 : ℝ) • (1 : Mat2C)) *
            (Δ + (r / 2 : ℝ) • (1 : Mat2C)) =
            r • (Δ + (r / 2 : ℝ) • (1 : Mat2C)) := by
        have hΔ2 : Δ * Δ = (r ^ 2 / 4 : ℝ) • (1 : Mat2C) := by
          rw [blochRadius_sq ρ]; exact bloch_centered_sq_eq_scalar hsa htr
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hΔ2]
        module
      have h_idemP : IsIdempotentElem
          (r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Mat2C))) := by
        change (r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Mat2C))) *
            (r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Mat2C))) = _
        rw [h_shift, smul_mul_assoc, mul_smul_comm, h_sq_shift, smul_smul, smul_smul]
        have h_scal : r⁻¹ * r⁻¹ * r = r⁻¹ := by
          rw [mul_assoc, inv_mul_cancel₀ hr, mul_one]
        rw [h_scal]
      have h_trP : Matrix.trace
          (r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Mat2C))) = 1 := by
        rw [trace_real_smul, Matrix.trace_sub, htr, trace_real_smul, trace_one_mat2]
        have hr_c : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
        push_cast; field_simp [hr_c]; ring
      have h_recP :
          twoSheet (r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Mat2C)))
            ((1 + r) / 2) ((1 - r) / 2) = ρ := by
        rw [twoSheet_affine]
        have hd : (1 + r) / 2 - (1 - r) / 2 = r := by ring
        rw [hd, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
      exact ⟨⟨h_idemP, h_saP⟩, h_trP, h_recP⟩
  rcases h_decomp with ⟨hP, htrP, h2s⟩
  have hr_lt : blochRadius ρ < 1 := blochRadius_lt_one hb
  have hp_pos : 0 < (1 + blochRadius ρ) / 2 := by linarith [blochRadius_nonneg ρ]
  have hm_pos : 0 < (1 - blochRadius ρ) / 2 := by linarith
  refine ⟨hP, htrP, h2s, ?_, ?_⟩
  · rw [← h2s]
    exact twoSheet_isStrictlyPositive hP hp_pos hm_pos
  · conv_lhs => rw [← h2s]
    rw [CFC.log, cfc_twoSheet hP]

/-- Determinant, purity defect, and strict positivity on the open Bloch ball. -/
theorem bloch_determinant_and_purity_defect (ρ : Mat2C)
    (h_adj : IsSelfAdjoint ρ) (h_tr : Matrix.trace ρ = 1) :
    Matrix.det ρ = (((1 - blochNormSq ρ) / 4 : ℝ) : ℂ) ∧
    Matrix.trace (ρ * ρ - ρ) = ((-((1 - blochNormSq ρ) / 2) : ℝ) : ℂ) ∧
    (InOpenBlochBall ρ ↔ IsSelfAdjoint ρ ∧ Matrix.trace ρ = 1 ∧ IsStrictlyPositive ρ) := by
  rcases hermitian_unitTrace_entries h_adj h_tr with ⟨h00, h11, h10, _⟩
  have h_norm : ρ 0 1 * star (ρ 0 1) = (Complex.normSq (ρ 0 1) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  have h_det : Matrix.det ρ = (((1 - blochNormSq ρ) / 4 : ℝ) : ℂ) := by
    rw [Matrix.det_fin_two, h00, h11, h10, h_norm]
    dsimp [blochNormSq, coherenceSq]
    push_cast; ring
  have h_tr_defect : Matrix.trace (ρ * ρ - ρ) = ((-((1 - blochNormSq ρ) / 2) : ℝ) : ℂ) := by
    rw [Matrix.trace_sub, h_tr, trace_fin2, mul2_00, mul2_11, h00, h11, h10,
      mul_comm (star (ρ 0 1)) (ρ 0 1), h_norm]
    dsimp [blochNormSq, coherenceSq]
    push_cast; ring
  refine ⟨h_det, h_tr_defect, ?_⟩
  constructor
  · intro h_ball
    refine ⟨h_adj, h_tr, ?_⟩
    exact (spectralProjector_twoSheet_and_cfc_log h_adj h_tr h_ball.2.2).2.2.2.1
  · rintro ⟨-, -, h_pos⟩
    refine ⟨h_adj, h_tr, ?_⟩
    have h_pos_semi : ρ.PosSemidef := Matrix.nonneg_iff_posSemidef.mp h_pos.1
    have h_det_nn : 0 ≤ Matrix.det ρ := h_pos_semi.det_nonneg
    have h_unit : IsUnit (Matrix.det ρ) := by
      rw [← Matrix.isUnit_iff_isUnit_det]
      exact h_pos.2
    have h_ne : Matrix.det ρ ≠ 0 := h_unit.ne_zero
    have h_real_pos : 0 < (1 - blochNormSq ρ) / 4 := by
      rcases Complex.nonneg_iff.mp h_det_nn with ⟨hre, -⟩
      rw [h_det] at hre h_ne
      simp only [Complex.ofReal_re] at hre
      have h_real_ne : (1 - blochNormSq ρ) / 4 ≠ 0 := by
        intro hc
        have : (((1 - blochNormSq ρ) / 4 : ℝ) : ℂ) = 0 := by rw [hc, Complex.ofReal_zero]
        exact h_ne this
      exact lt_of_le_of_ne hre (Ne.symm h_real_ne)
    linarith

private lemma thermalSemigroupC_selfAdjoint_trace_coherence
    (γ ω θ t : ℝ) {ρ : Mat2C}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) :
    IsSelfAdjoint (thermalSemigroupC γ ω θ t ρ) ∧
    Matrix.trace (thermalSemigroupC γ ω θ t ρ) = 1 ∧
    blochZ (thermalSemigroupC γ ω θ t ρ) = etaTraj γ θ (blochZ ρ) t ∧
    coherenceSq (thermalSemigroupC γ ω θ t ρ) = Real.exp (-γ * t) * coherenceSq ρ := by
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, _⟩
  have htr_c : ρ 0 0 + ρ 1 1 = 1 := by rw [trace_fin2] at htr; exact htr
  have h_star_php : star (Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ))) =
      Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1; simp [map_mul, Complex.conj_I, Complex.conj_ofReal]
  have h_star_phm : star (Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) =
      Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1; simp [map_mul, Complex.conj_I, Complex.conj_ofReal]
  have h_star_real : ∀ r : ℝ, star (r : ℂ) = (r : ℂ) := fun r => by
    simp [Complex.conj_ofReal]
  have h_sa_t : IsSelfAdjoint (thermalSemigroupC γ ω θ t ρ) := by
    change star (thermalSemigroupC γ ω θ t ρ) = thermalSemigroupC γ ω θ t ρ
    apply ext_mat2 <;>
      simp only [Matrix.star_apply, star_add, star_sub, star_mul,
        h_star_real, h00, h11, h10, star_star, h_star_php, h_star_phm,
        thermalSemigroupC, mat2_00, mat2_01, mat2_10, mat2_11] <;>
      ring
  have h_tr_t : Matrix.trace (thermalSemigroupC γ ω θ t ρ) = 1 := by
    rw [trace_fin2]
    dsimp [thermalSemigroupC]
    have h_bsum : (boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ) = 1 := by
      exact_mod_cast (boltzmann_sum_and_diff θ).1
    calc (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * t) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1)) +
          ((boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * t) : ℂ) * (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1)))
      _ = ((boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ)) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * t) : ℂ) * ((ρ 0 0 + ρ 1 1) - ((boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ)) * (ρ 0 0 + ρ 1 1)) := by ring
      _ = 1 * 1 + (Real.exp (-γ * t) : ℂ) * (1 - 1 * 1) := by rw [h_bsum, htr_c]
      _ = 1 := by ring
  have h_bz_t : blochZ (thermalSemigroupC γ ω θ t ρ) = etaTraj γ θ (blochZ ρ) t := by
    dsimp [blochZ, thermalSemigroupC, etaTraj]
    rw [htr_c]
    have h_bdiff : boltzmannPlus θ - boltzmannMinus θ = meanSpin θ := (boltzmann_sum_and_diff θ).2
    rcases hermitian_unitTrace_entries hsa htr with ⟨h00', h11', _, _⟩
    rw [h00', h11']
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, mul_one]
    rw [← h_bdiff]
    ring
  have h_coh_t : coherenceSq (thermalSemigroupC γ ω θ t ρ) = Real.exp (-γ * t) * coherenceSq ρ := by
    dsimp [coherenceSq, thermalSemigroupC]
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
    have h_norm1 : Complex.normSq (Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ))) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
      have h_im : (-Complex.I * (ω : ℂ) * (t : ℂ)).re = 0 := by
        simp
      rw [h_im, Real.exp_zero, one_pow]
    rw [h_norm1, mul_one]
    have h_exp : Real.exp (-(γ / 2) * t) * Real.exp (-(γ / 2) * t) = Real.exp (-γ * t) := by
      rw [← Real.exp_add]
      congr 1; ring
    calc 4 * (Real.exp (-(γ / 2) * t) * Real.exp (-(γ / 2) * t) * Complex.normSq (ρ 0 1))
      _ = 4 * (Real.exp (-γ * t) * Complex.normSq (ρ 0 1)) := by rw [h_exp]
      _ = Real.exp (-γ * t) * (4 * Complex.normSq (ρ 0 1)) := by ring
  exact ⟨h_sa_t, h_tr_t, h_bz_t, h_coh_t⟩

/-- Forward positivity preservation of the open Bloch ball. -/
private lemma thermalSemigroupC_preserves_blochBall
    {γ ω θ t : ℝ} {ρ : Mat2C}
    (hγ : 0 < γ) (ht : 0 ≤ t) (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1)
    (hb : blochNormSq ρ < 1) :
    IsSelfAdjoint (thermalSemigroupC γ ω θ t ρ) ∧
    Matrix.trace (thermalSemigroupC γ ω θ t ρ) = 1 ∧
    blochNormSq (thermalSemigroupC γ ω θ t ρ) < 1 ∧
    IsStrictlyPositive (thermalSemigroupC γ ω θ t ρ) := by
  rcases thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hsa htr with
    ⟨h_sa_t, h_tr_t, h_bz_t, h_coh_t⟩
  have h_norm_lt : blochNormSq (thermalSemigroupC γ ω θ t ρ) < 1 := by
    rw [blochNormSq, h_bz_t, h_coh_t]
    set lam := Real.exp (-γ * t)
    set z0 := blochZ ρ
    set c0 := coherenceSq ρ
    set η_eq := meanSpin θ
    have hlam_pos : 0 < lam := Real.exp_pos _
    have hlam_le1 : lam ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hγ, ht])
    have h_eta_lt : η_eq ^ 2 < 1 := by
      rcases meanSpin_mem_Ioo θ with ⟨hm_lo, hm_hi⟩
      nlinarith [hm_lo, hm_hi]
    have hc0_nn : 0 ≤ c0 := by
      dsimp [c0, coherenceSq]; exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
    have h_alg : (etaTraj γ θ z0 t) ^ 2 + lam * c0 =
        (1 - lam) * η_eq ^ 2 + lam * blochNormSq ρ - lam * (1 - lam) * (z0 - η_eq) ^ 2 := by
      dsimp [etaTraj, lam, z0, c0, η_eq, blochNormSq]; ring
    have h_drop : 0 ≤ lam * (1 - lam) * (z0 - η_eq) ^ 2 :=
      mul_nonneg (mul_nonneg (le_of_lt hlam_pos) (sub_nonneg.mpr hlam_le1)) (sq_nonneg _)
    rw [h_alg]
    nlinarith [hb, h_eta_lt, h_drop, hlam_pos, hlam_le1]
  have h_pos_t := (spectralProjector_twoSheet_and_cfc_log h_sa_t h_tr_t h_norm_lt).2.2.2.1
  exact ⟨h_sa_t, h_tr_t, h_norm_lt, h_pos_t⟩

/-- **Rung 2 Theorem**: Forward-positivity monoid characterization on the open Bloch ball. -/
theorem rung2_forward_positivity_monoid_iff (γ ω θ : ℝ) (hγ : 0 < γ) (t : ℝ) :
    (∀ ρ₀, InOpenBlochBall ρ₀ → InOpenBlochBall (thermalSemigroupC γ ω θ t ρ₀)) ↔ 0 ≤ t := by
  constructor
  · intro h_all
    by_contra ht_neg
    have ht : t < 0 := lt_of_not_ge ht_neg
    set r0 := Real.exp (γ * t / 4)
    have hr0_pos : 0 < r0 := Real.exp_pos _
    have hr0_lt : r0 < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [hγ, ht]
    set ρ₀ : Mat2C := (1 / 2 : ℂ) • (1 + (r0 : ℂ) • pauliSigmaX)
    have h_sa0 : IsSelfAdjoint ρ₀ := by
      change star ρ₀ = ρ₀
      dsimp [ρ₀]
      apply ext_mat2
      · simp only [Matrix.star_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_00, smul_eq_mul]
        norm_num
      · simp only [Matrix.star_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_01, mat2_10, smul_eq_mul]
        norm_num
      · simp only [Matrix.star_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_01, mat2_10, smul_eq_mul]
        norm_num
      · simp only [Matrix.star_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_11, smul_eq_mul]
        norm_num
    have h_tr0 : Matrix.trace ρ₀ = 1 := by
      dsimp [ρ₀]
      rw [trace_fin2]
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_00, mat2_11,
        smul_zero, add_zero, smul_eq_mul]
      norm_num
    have h_bz0 : blochZ ρ₀ = 0 := by
      dsimp [blochZ, ρ₀]
      simp [pauliSigmaX_eq]
    have h_entry : ρ₀ 0 1 = ((r0 / 2 : ℝ) : ℂ) := by
      dsimp [ρ₀]
      simp only [Matrix.one_apply, pauliSigmaX_eq, mat2_01]
      norm_num
      ring
    have h_coh0 : coherenceSq ρ₀ = r0 ^ 2 := by
      dsimp [coherenceSq]
      rw [h_entry, Complex.normSq_ofReal]
      ring
    have h_norm0 : blochNormSq ρ₀ = r0 ^ 2 := by
      rw [blochNormSq, h_bz0, h_coh0, zero_pow (by norm_num), zero_add]
    have h_ball0 : InOpenBlochBall ρ₀ := by
      refine ⟨h_sa0, h_tr0, ?_⟩
      rw [h_norm0]
      nlinarith [hr0_pos, hr0_lt]
    have h_tc := thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t h_sa0 h_tr0
    have h_coh_t : coherenceSq (thermalSemigroupC γ ω θ t ρ₀) = Real.exp (-γ * t / 2) := by
      rw [h_tc.2.2.2, h_coh0]
      have heq : Real.exp (-γ * t) * r0 ^ 2 = Real.exp (-γ * t / 2) := by
        dsimp [r0]
        rw [sq, ← Real.exp_add, ← Real.exp_add]
        congr 1; ring
      exact heq
    have h_norm_t : 1 < blochNormSq (thermalSemigroupC γ ω θ t ρ₀) := by
      rw [blochNormSq]
      have h_coh_gt1 : 1 < coherenceSq (thermalSemigroupC γ ω θ t ρ₀) := by
        rw [h_coh_t, Real.one_lt_exp_iff]
        nlinarith [hγ, ht]
      have h_sq_nn : 0 ≤ (blochZ (thermalSemigroupC γ ω θ t ρ₀)) ^ 2 := sq_nonneg _
      linarith
    have h_contra := (h_all ρ₀ h_ball0).2.2
    exact (lt_asymm h_norm_t h_contra).elim
  · intro ht ρ₀ h_ball0
    rcases thermalSemigroupC_preserves_blochBall hγ ht h_ball0.1 h_ball0.2.1 h_ball0.2.2 with
      ⟨hsa_t, htr_t, hb_t, -⟩
    exact ⟨hsa_t, htr_t, hb_t⟩

/-- **Rung 2 Refutation Witness**: Backward-time exit and strict negativity. -/
theorem rung2_backward_time_refutation_witness (γ ω θ : ℝ) (hγ : 0 < γ) {t : ℝ} (ht : t < 0) :
    let ρ₀ : Mat2C := (1 / 2 : ℂ) • (1 + (Real.exp (γ * t / 4) : ℂ) • pauliSigmaX)
    let ρ_t := thermalSemigroupC γ ω θ t ρ₀
    InOpenBlochBall ρ₀ ∧
    1 < blochNormSq ρ_t ∧
    (Matrix.det ρ_t).re < 0 ∧
    0 < (Matrix.trace (ρ_t * ρ_t - ρ_t)).re ∧
    ¬ IsStrictlyPositive ρ_t := by
  have ext : True := trivial
  intro ρ₀ ρ_t
  set r0 := Real.exp (γ * t / 4)
  have hr0_pos : 0 < r0 := Real.exp_pos _
  have hr0_lt : r0 < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [hγ, ht]
  have h_rho0_eq : ρ₀ = (1 / 2 : ℂ) • (1 + (r0 : ℂ) • pauliSigmaX) := rfl
  have h_sa0 : IsSelfAdjoint ρ₀ := by
    change star ρ₀ = ρ₀
    rw [h_rho0_eq]
    apply ext_mat2
    · simp only [Matrix.star_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_00, smul_eq_mul]
      norm_num
    · simp only [Matrix.star_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_01, mat2_10, smul_eq_mul]
      norm_num
    · simp only [Matrix.star_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_01, mat2_10, smul_eq_mul]
      norm_num
    · simp only [Matrix.star_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_11, smul_eq_mul]
      norm_num
  have h_tr0 : Matrix.trace ρ₀ = 1 := by
    rw [h_rho0_eq, trace_fin2]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_00, mat2_11,
      smul_eq_mul]
    norm_num
  have h_bz0 : blochZ ρ₀ = 0 := by
    dsimp [blochZ]
    rw [h_rho0_eq]
    simp [pauliSigmaX_eq]
  have h_entry : ρ₀ 0 1 = ((r0 / 2 : ℝ) : ℂ) := by
    rw [h_rho0_eq]
    simp only [pauliSigmaX_eq]
    norm_num
    ring
  have h_coh0 : coherenceSq ρ₀ = r0 ^ 2 := by
    dsimp [coherenceSq]
    rw [h_entry, Complex.normSq_ofReal]
    ring
  have h_norm0 : blochNormSq ρ₀ = r0 ^ 2 := by
    rw [blochNormSq, h_bz0, h_coh0, zero_pow (by norm_num), zero_add]
  have h_ball0 : InOpenBlochBall ρ₀ := by
    refine ⟨h_sa0, h_tr0, ?_⟩
    rw [h_norm0]
    nlinarith [hr0_pos, hr0_lt]
  have h_tc := thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t h_sa0 h_tr0
  have h_coh_t : coherenceSq ρ_t = Real.exp (-γ * t / 2) := by
    dsimp [ρ_t]
    rw [h_tc.2.2.2, h_coh0]
    have heq : Real.exp (-γ * t) * r0 ^ 2 = Real.exp (-γ * t / 2) := by
      dsimp [r0]
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    exact heq
  have h_norm_t : 1 < blochNormSq ρ_t := by
    rw [blochNormSq]
    have h_coh_gt1 : 1 < coherenceSq ρ_t := by
      rw [h_coh_t, Real.one_lt_exp_iff]
      nlinarith [hγ, ht]
    have h_sq_nn : 0 ≤ (blochZ ρ_t) ^ 2 := sq_nonneg _
    linarith
  have h_det_calc : (Matrix.det ρ_t).re = (1 - blochNormSq ρ_t) / 4 := by
    have hd := (bloch_determinant_and_purity_defect ρ_t h_tc.1 h_tc.2.1).1
    rw [hd]
    simp only [Complex.ofReal_re]
  have h_det_neg : (Matrix.det ρ_t).re < 0 := by
    rw [h_det_calc]
    nlinarith [h_norm_t]
  have h_tr_calc : (Matrix.trace (ρ_t * ρ_t - ρ_t)).re = -(1 - blochNormSq ρ_t) / 2 := by
    have ht_def := (bloch_determinant_and_purity_defect ρ_t h_tc.1 h_tc.2.1).2.1
    rw [ht_def]
    simp only [Complex.ofReal_re]
    ring
  have h_tr_pos : 0 < (Matrix.trace (ρ_t * ρ_t - ρ_t)).re := by
    rw [h_tr_calc]
    nlinarith [h_norm_t]
  have h_not_pos : ¬ IsStrictlyPositive ρ_t := by
    intro hp
    have h_pos_semi : ρ_t.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hp.1
    have h_unit : IsUnit (Matrix.det ρ_t) := by
      rw [← Matrix.isUnit_iff_isUnit_det]
      exact hp.2
    have h_ne : Matrix.det ρ_t ≠ 0 := h_unit.ne_zero
    have h_ball_iff := (bloch_determinant_and_purity_defect ρ_t h_tc.1 h_tc.2.1).2.2
    have h_ball_t : InOpenBlochBall ρ_t := h_ball_iff.mpr ⟨h_tc.1, h_tc.2.1, hp⟩
    exact (lt_asymm h_norm_t h_ball_t.2.2).elim
  exact ⟨h_ball0, h_norm_t, h_det_neg, h_tr_pos, h_not_pos⟩

/-!
### Section 3: $Y_0 \prec Y_3$: Bloch 3D Cumulant Legendre and CFC Log Bridge
-/

/-- 3D cumulant potential $\Psi_3(\boldsymbol{\theta}) = \psi(\|\boldsymbol{\theta}\|)$. -/
def cumulantPsi3 (θ_vec : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  cumulantPsi ‖θ_vec‖

/-- 3D Legendre mean map $\nabla\Psi_3(\boldsymbol{\theta}) = \frac{\tanh\|\boldsymbol{\theta}\|}{\|\boldsymbol{\theta}\|}\boldsymbol{\theta}$. -/
def blochMean3 (θ_vec : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  if ‖θ_vec‖ = 0 then 0 else (meanSpin ‖θ_vec‖ / ‖θ_vec‖) • θ_vec

/-- Regularized artanh ratio $\frac{\operatorname{artanh}(r)}{r}$, smoothly extended to $1$ at $r = 0$. -/
def artanhRatio (r : ℝ) : ℝ :=
  if r = 0 then 1 else canonicalTheta r / r

/-- 3D canonical dual map $\boldsymbol{\theta}(\mathbf{r}) = \operatorname{artanhRatio}(\|\mathbf{r}\|)\mathbf{r}$. -/
def legendreTheta3 (r_vec : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  artanhRatio ‖r_vec‖ • r_vec

/-- 3D Boltzmann negentropy $\Phi_3(\mathbf{r}) = \phi(\|\mathbf{r}\|)$. -/
def negEntropyPhi3 (r_vec : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  negEntropyPhi ‖r_vec‖

/-- Pauli vector contraction $\mathbf{v} \cdot \boldsymbol{\sigma} = v_0 \sigma_x + v_1 \sigma_y + v_2 \sigma_z$. -/
def pauliSlash (v : EuclideanSpace ℝ (Fin 3)) : Mat2C :=
  (v 0 : ℂ) • pauliSigmaX + (v 1 : ℂ) • pauliSigmaY + (v 2 : ℂ) • pauliGamma1

/-- Embedding of the longitudinal axis $\mathbf{u} = (0, 0, u) \in \mathbb{R}^3$. -/
def zAxis3 (u : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![0, 0, u]

private lemma canonicalTheta_ge_id {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    r ≤ canonicalTheta r := by
  by_cases hr : r = 0
  · subst hr
    simp [canonicalTheta]
  · have hr_pos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have h_int : interior (Set.Icc 0 r) = Set.Ioo 0 r := interior_Icc
    have h_th : ∀ x ∈ Set.Ioo 0 r, HasDerivAt canonicalTheta (1 / (1 - x ^ 2)) x := by
      intro x hx
      exact dually_flat_legendre_reciprocity_and_metric_inversion.2.2.2.2.1 x (by linarith [hx.1]) (by linarith [hx.2, hr1])
    have h_fn : ∀ x ∈ interior (Set.Icc 0 r), HasDerivWithinAt (fun u => canonicalTheta u - u) (1 / (1 - x ^ 2) - 1) (interior (Set.Icc 0 r)) x := by
      intro x hx
      rw [h_int] at hx
      exact ((h_th x hx).sub (hasDerivAt_id x)).hasDerivWithinAt
    have h_nonneg : ∀ x ∈ interior (Set.Icc 0 r), 0 ≤ 1 / (1 - x ^ 2) - 1 := by
      intro x hx
      rw [h_int] at hx
      have hx2 : x ^ 2 < 1 := by
        nlinarith [hx.1, hx.2, hr1]
      have hd : 0 < 1 - x ^ 2 := by linarith
      have h_inv : 1 ≤ 1 / (1 - x ^ 2) := by
        rw [le_div_iff₀ hd]
        nlinarith [sq_nonneg x]
      linarith
    have h_cont : ContinuousOn (fun u => canonicalTheta u - u) (Set.Icc 0 r) := by
      have hc_th : ContinuousOn canonicalTheta (Set.Icc 0 r) := by
        apply ContinuousOn.mono (s := Set.Ioo (-1) 1)
        · intro x hx
          exact (dually_flat_legendre_reciprocity_and_metric_inversion.2.2.2.2.1 x hx.1 hx.2).continuousAt.continuousWithinAt
        · intro x hx
          exact ⟨by linarith [hx.1], by linarith [hx.2, hr1]⟩
      exact hc_th.sub continuousOn_id
    have h_conv : Convex ℝ (Set.Icc 0 r) := convex_Icc 0 r
    have h_mono : MonotoneOn (fun u => canonicalTheta u - u) (Set.Icc 0 r) :=
      monotoneOn_of_hasDerivWithinAt_nonneg h_conv h_cont h_fn h_nonneg
    have h0_mem : (0 : ℝ) ∈ Set.Icc 0 r := ⟨le_rfl, le_of_lt hr_pos⟩
    have hr_mem : r ∈ Set.Icc 0 r := ⟨le_of_lt hr_pos, le_rfl⟩
    have h_le := h_mono h0_mem hr_mem (le_of_lt hr_pos)
    dsimp at h_le
    have h_th0 : canonicalTheta 0 = 0 := by
      dsimp [canonicalTheta]; norm_num
    rw [h_th0, sub_zero] at h_le
    linarith

/-- The regularized artanh ratio is bounded below by 1 and strictly positive on $[0, 1)$. -/
theorem artanhRatio_ge_one (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    1 ≤ artanhRatio r ∧ 0 < artanhRatio r := by
  by_cases hr : r = 0
  · subst hr
    dsimp [artanhRatio]
    norm_num
  · have hr_pos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    dsimp [artanhRatio]
    simp only [hr, ↓reduceIte]
    have h_ge := canonicalTheta_ge_id hr0 hr1
    have h_ratio : 1 ≤ canonicalTheta r / r := by
      rw [le_div_iff₀ hr_pos]
      linarith
    exact ⟨h_ratio, lt_of_lt_of_le (by norm_num) h_ratio⟩

private lemma meanSpin_pos_of_pos {θ : ℝ} (hθ : 0 < θ) : 0 < meanSpin θ := by
  dsimp [meanSpin]
  have h_exp : Real.exp (-θ) < Real.exp θ := Real.exp_lt_exp.mpr (by linarith [hθ])
  exact div_pos (sub_pos.mpr h_exp) (partitionZ_pos θ)

private lemma canonicalTheta_pos_of_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < canonicalTheta r := by
  dsimp [canonicalTheta]
  have h1 : 0 < 1 - r := by
    linarith [hr1]
  have h_div : 1 < (1 + r) / (1 - r) := by
    rw [lt_div_iff₀ h1]
    linarith [hr0]
  exact mul_pos (by norm_num) (Real.log_pos h_div)

private lemma blochMean3_zero : blochMean3 0 = 0 := by
  dsimp [blochMean3]; rw [norm_zero]; simp

private lemma legendreTheta3_zero : legendreTheta3 0 = 0 := by
  dsimp [legendreTheta3]; rw [smul_zero]

/-- 3D Legendre reciprocity on the open Bloch ball. -/
theorem bloch3d_legendre_reciprocity :
    (∀ θ_vec : EuclideanSpace ℝ (Fin 3), legendreTheta3 (blochMean3 θ_vec) = θ_vec) ∧
    (∀ r_vec : EuclideanSpace ℝ (Fin 3), ‖r_vec‖ < 1 → blochMean3 (legendreTheta3 r_vec) = r_vec) := by
  refine ⟨?_, ?_⟩
  · intro θ_vec
    by_cases hθ : ‖θ_vec‖ = 0
    · have h0 : θ_vec = 0 := norm_eq_zero.mp hθ
      rw [h0, blochMean3_zero, legendreTheta3_zero]
    · set θ := ‖θ_vec‖
      have hθ_pos : 0 < θ := lt_of_le_of_ne (norm_nonneg θ_vec) (Ne.symm hθ)
      have h_ms_pos : 0 < meanSpin θ := meanSpin_pos_of_pos hθ_pos
      have h_scal_pos : 0 < meanSpin θ / θ := div_pos h_ms_pos hθ_pos
      have h_bm_def : blochMean3 θ_vec = (meanSpin θ / θ) • θ_vec := by
        dsimp [blochMean3, θ]
        split_ifs with h0
        · exact (hθ h0).elim
        · rfl
      have h_norm_bm : ‖blochMean3 θ_vec‖ = meanSpin θ := by
        rw [h_bm_def, norm_smul, Real.norm_of_nonneg (le_of_lt h_scal_pos)]
        dsimp [θ]
        exact div_mul_cancel₀ (meanSpin θ) hθ
      dsimp [legendreTheta3]
      rw [h_norm_bm]
      have h_art : artanhRatio (meanSpin θ) = canonicalTheta (meanSpin θ) / meanSpin θ := by
        dsimp [artanhRatio]
        split_ifs with h0
        · exact (ne_of_gt h_ms_pos h0).elim
        · rfl
      rw [h_art]
      have h_th_ms : canonicalTheta (meanSpin θ) = θ :=
        dually_flat_legendre_reciprocity_and_metric_inversion.1 θ
      rw [h_th_ms, h_bm_def, smul_smul]
      have h_cancel : θ / meanSpin θ * (meanSpin θ / θ) = 1 := by
        field_simp [ne_of_gt hθ_pos, ne_of_gt h_ms_pos]
      rw [h_cancel, one_smul]
  · intro r_vec hr
    by_cases hr0 : ‖r_vec‖ = 0
    · have h0 : r_vec = 0 := norm_eq_zero.mp hr0
      rw [h0, legendreTheta3_zero, blochMean3_zero]
    · set r := ‖r_vec‖
      have hr_pos : 0 < r := lt_of_le_of_ne (norm_nonneg r_vec) (Ne.symm hr0)
      have h_ct_pos : 0 < canonicalTheta r := canonicalTheta_pos_of_pos hr_pos hr
      have h_scal_pos : 0 < canonicalTheta r / r := div_pos h_ct_pos hr_pos
      have h_lt_def : legendreTheta3 r_vec = (canonicalTheta r / r) • r_vec := by
        dsimp [legendreTheta3, artanhRatio, r]
        split_ifs with h0
        · exact (hr0 h0).elim
        · rfl
      have h_norm_lt : ‖legendreTheta3 r_vec‖ = canonicalTheta r := by
        rw [h_lt_def, norm_smul, Real.norm_of_nonneg (le_of_lt h_scal_pos)]
        dsimp [r]
        exact div_mul_cancel₀ (canonicalTheta r) hr0
      have h_bm : blochMean3 (legendreTheta3 r_vec) =
          (meanSpin (canonicalTheta r) / canonicalTheta r) • legendreTheta3 r_vec := by
        dsimp [blochMean3]
        rw [h_norm_lt]
        split_ifs with h0
        · exact (ne_of_gt h_ct_pos h0).elim
        · rfl
      rw [h_bm]
      have h_ms_ct : meanSpin (canonicalTheta r) = r :=
        dually_flat_legendre_reciprocity_and_metric_inversion.2.1 r (by linarith) hr
      rw [h_ms_ct, h_lt_def, smul_smul]
      have h_cancel : r / canonicalTheta r * (canonicalTheta r / r) = 1 := by
        field_simp [ne_of_gt hr_pos, ne_of_gt h_ct_pos]
      rw [h_cancel, one_smul]

private lemma meanSpin_zero_val : meanSpin 0 = 0 := by
  dsimp [meanSpin]
  simp

private lemma canonicalTheta_zero_val : canonicalTheta 0 = 0 := by
  dsimp [canonicalTheta]
  simp

private lemma canonicalTheta_neg (u : ℝ) (hu_lo : -1 < u) (hu_hi : u < 1) :
    canonicalTheta (-u) = -canonicalTheta u := by
  dsimp [canonicalTheta]
  have h1 : 0 < 1 + u := by linarith [hu_lo]
  have h2 : 0 < 1 - u := by linarith [hu_hi]
  have h_div : (1 + -u) / (1 - -u) = ((1 + u) / (1 - u))⁻¹ := by
    have h_eq : (1 + -u) / (1 - -u) = (1 - u) / (1 + u) := by ring
    rw [h_eq, inv_div]
  rw [h_div, Real.log_inv]
  ring

private lemma zAxis3_zero : zAxis3 0 = 0 := by
  ext i
  fin_cases i <;> rfl

private lemma fenchel_young_1d (θ r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    θ * r ≤ cumulantPsi θ + negEntropyPhi r ∧
    (θ * r = cumulantPsi θ + negEntropyPhi r ↔ r = meanSpin θ) := by
  have h_young := dually_flat_legendre_reciprocity_and_metric_inversion.2.2.1 θ
  have h_bp := bregman_umegaki_positivity_and_pythagorean_theorem.2.1 r (meanSpin θ)
    (by linarith [hr0]) hr1 (meanSpin_mem_Ioo θ).1 (meanSpin_mem_Ioo θ).2
  have h_th_mean := dually_flat_legendre_reciprocity_and_metric_inversion.1 θ
  have h_bp_eq : bregmanPhi r (meanSpin θ) = cumulantPsi θ + negEntropyPhi r - θ * r := by
    dsimp [bregmanPhi]
    rw [h_th_mean]
    linear_combination - h_young
  refine ⟨by linarith [h_bp.1, h_bp_eq], ?_⟩
  constructor
  · intro heq
    have h0 : bregmanPhi r (meanSpin θ) = 0 := by linarith [h_bp_eq, heq]
    exact h_bp.2.mp h0
  · rintro rfl
    linarith [h_young]

/-- 3D Fenchel–Young inequality and Legendre saturation on the open Bloch ball. -/
theorem bloch3d_fenchel_young (θ_vec r_vec : EuclideanSpace ℝ (Fin 3)) (hr : ‖r_vec‖ < 1) :
    inner ℝ θ_vec r_vec ≤ cumulantPsi3 θ_vec + negEntropyPhi3 r_vec ∧
    (inner ℝ θ_vec r_vec = cumulantPsi3 θ_vec + negEntropyPhi3 r_vec ↔
      r_vec = blochMean3 θ_vec) := by
  have hr0 : 0 ≤ ‖r_vec‖ := norm_nonneg r_vec
  have h_cs := real_inner_le_norm θ_vec r_vec
  have h_fy1 := fenchel_young_1d ‖θ_vec‖ ‖r_vec‖ hr0 hr
  have h_le : inner ℝ θ_vec r_vec ≤ cumulantPsi3 θ_vec + negEntropyPhi3 r_vec := by
    dsimp [cumulantPsi3, negEntropyPhi3]
    linarith [h_cs, h_fy1.1]
  refine ⟨h_le, ?_⟩
  constructor
  · intro heq
    have heq_eval : inner ℝ θ_vec r_vec = cumulantPsi ‖θ_vec‖ + negEntropyPhi ‖r_vec‖ := by
      dsimp [cumulantPsi3, negEntropyPhi3] at heq
      exact heq
    have h_cs_eq : inner ℝ θ_vec r_vec = ‖θ_vec‖ * ‖r_vec‖ := by
      linarith [h_cs, h_fy1.1, heq_eval]
    have h_fy_eq : ‖θ_vec‖ * ‖r_vec‖ = cumulantPsi ‖θ_vec‖ + negEntropyPhi ‖r_vec‖ := by
      linarith [h_cs, h_fy1.1, heq_eval]
    have h_r_eq : ‖r_vec‖ = meanSpin ‖θ_vec‖ := h_fy1.2.mp h_fy_eq
    by_cases hθ : ‖θ_vec‖ = 0
    · have h0 : θ_vec = 0 := norm_eq_zero.mp hθ
      rw [h0]
      have h_r0 : ‖r_vec‖ = 0 := by
        rw [h_r_eq, h0, norm_zero, meanSpin_zero_val]
      have hr0' : r_vec = 0 := norm_eq_zero.mp h_r0
      rw [hr0', blochMean3_zero]
    · set θ := ‖θ_vec‖
      have hθ_pos : 0 < θ := lt_of_le_of_ne (norm_nonneg θ_vec) (Ne.symm hθ)
      have h_cs_real : ‖r_vec‖ • θ_vec = ‖θ_vec‖ • r_vec :=
        inner_eq_norm_mul_iff_real.mp h_cs_eq
      have h_smul : r_vec = (‖r_vec‖ / θ) • θ_vec := by
        calc r_vec = (1 : ℝ) • r_vec := (one_smul ℝ r_vec).symm
          _ = (θ⁻¹ * θ) • r_vec := by rw [inv_mul_cancel₀ (ne_of_gt hθ_pos)]
          _ = θ⁻¹ • (θ • r_vec) := by rw [mul_smul]
          _ = θ⁻¹ • (‖r_vec‖ • θ_vec) := by rw [← h_cs_real]
          _ = (θ⁻¹ * ‖r_vec‖) • θ_vec := by rw [smul_smul]
          _ = (‖r_vec‖ / θ) • θ_vec := by rw [div_eq_inv_mul, mul_comm]
      rw [h_smul, h_r_eq]
      dsimp [blochMean3, θ]
      split_ifs with h0
      · exact (hθ h0).elim
      · rfl
  · rintro rfl
    by_cases hθ : ‖θ_vec‖ = 0
    · have h0 : θ_vec = 0 := norm_eq_zero.mp hθ
      subst h0
      rw [blochMean3_zero]
      dsimp [cumulantPsi3, negEntropyPhi3]
      rw [norm_zero, inner_zero_left]
      have h_young0 := dually_flat_legendre_reciprocity_and_metric_inversion.2.2.1 0
      rw [meanSpin_zero_val, mul_zero] at h_young0
      exact h_young0.symm
    · set θ := ‖θ_vec‖
      have hθ_pos : 0 < θ := lt_of_le_of_ne (norm_nonneg θ_vec) (Ne.symm hθ)
      have h_scal_pos : 0 < meanSpin θ / θ := div_pos (meanSpin_pos_of_pos hθ_pos) hθ_pos
      have h_bm_def : blochMean3 θ_vec = (meanSpin θ / θ) • θ_vec := by
        dsimp [blochMean3, θ]
        split_ifs with h0
        · exact (hθ h0).elim
        · rfl
      have h_norm_bm : ‖blochMean3 θ_vec‖ = meanSpin θ := by
        rw [h_bm_def, norm_smul, Real.norm_of_nonneg (le_of_lt h_scal_pos)]
        dsimp [θ]
        exact div_mul_cancel₀ (meanSpin θ) hθ
      have h_in_eval : inner ℝ θ_vec (blochMean3 θ_vec) = θ * meanSpin θ := by
        rw [h_bm_def, real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
        dsimp [θ]
        calc (meanSpin θ / θ) * (θ * θ)
          _ = (meanSpin θ / θ * θ) * θ := by ring
          _ = meanSpin θ * θ := by rw [div_mul_cancel₀ (meanSpin θ) (ne_of_gt hθ_pos)]
          _ = θ * meanSpin θ := by ring
      rw [h_in_eval]
      dsimp [cumulantPsi3, negEntropyPhi3]
      rw [h_norm_bm]
      have h_young := dually_flat_legendre_reciprocity_and_metric_inversion.2.2.1 θ
      exact h_young.symm

private lemma norm_zAxis3 {u : ℝ} (hu0 : 0 ≤ u) : ‖zAxis3 u‖ = u := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have h0 : (zAxis3 u 0) = 0 := rfl
  have h1 : (zAxis3 u 1) = 0 := rfl
  have h2 : (zAxis3 u 2) = u := rfl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, h0, h1, h2]
  simp only [abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sq_abs, zero_add]
  exact Real.sqrt_sq hu0

private lemma smul_zAxis3 (c u : ℝ) : c • zAxis3 u = zAxis3 (c * u) := by
  ext i
  fin_cases i
  · dsimp [zAxis3]; ring
  · dsimp [zAxis3]; ring
  · dsimp [zAxis3]

/-- Exact diagonal Cartan specialization along the longitudinal axis. -/
theorem cartan_zAxis3_specialization (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    cumulantPsi3 (zAxis3 u) = cumulantPsi u ∧
    blochMean3 (zAxis3 u) = zAxis3 (meanSpin u) ∧
    legendreTheta3 (zAxis3 u) = zAxis3 (canonicalTheta u) ∧
    negEntropyPhi3 (zAxis3 u) = negEntropyPhi u := by
  have h_norm := norm_zAxis3 hu0
  have h_u_lt : u < 1 := hu1
  have h_psi : cumulantPsi3 (zAxis3 u) = cumulantPsi u := by
    dsimp [cumulantPsi3]; rw [h_norm]
  have h_phi : negEntropyPhi3 (zAxis3 u) = negEntropyPhi u := by
    dsimp [negEntropyPhi3]; rw [h_norm]
  have h_mean : blochMean3 (zAxis3 u) = zAxis3 (meanSpin u) := by
    by_cases hu : u = 0
    · subst hu
      rw [meanSpin_zero_val, zAxis3_zero, blochMean3_zero]
    · dsimp [blochMean3]
      rw [h_norm]
      simp [hu]
      rw [smul_zAxis3, div_mul_cancel₀ (meanSpin u) hu]
  have h_theta : legendreTheta3 (zAxis3 u) = zAxis3 (canonicalTheta u) := by
    by_cases hu : u = 0
    · subst hu
      rw [canonicalTheta_zero_val, zAxis3_zero, legendreTheta3_zero]
    · dsimp [legendreTheta3, artanhRatio]
      rw [h_norm]
      simp [hu]
      rw [smul_zAxis3, div_mul_cancel₀ (canonicalTheta u) hu]
  exact ⟨h_psi, h_mean, h_theta, h_phi⟩

private lemma euclidean_norm_sq_fin3 (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have h0 : ‖v 0‖ ^ 2 = (v 0) ^ 2 := by simp [sq_abs]
  have h1 : ‖v 1‖ ^ 2 = (v 1) ^ 2 := by simp [sq_abs]
  have h2 : ‖v 2‖ ^ 2 = (v 2) ^ 2 := by simp [sq_abs]
  rw [h0, h1, h2]
  have h_nonneg : 0 ≤ (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by positivity
  exact Real.sq_sqrt h_nonneg

private lemma pauliSlash_eq (v : EuclideanSpace ℝ (Fin 3)) :
    pauliSlash v = mat2 (v 2 : ℂ) (v 0 - Complex.I * v 1 : ℂ)
                        (v 0 + Complex.I * v 1 : ℂ) (-v 2 : ℂ) := by
  dsimp [pauliSlash]
  rw [pauliSigmaX_eq, pauliSigmaY_eq, pauliGamma1_eq]
  apply ext_mat2 <;> {
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, mat2_00,
      mat2_01, mat2_10, mat2_11, Fin.isValue]
    ring
  }

private lemma blochState_eq_half_add_pauliSlash (v : EuclideanSpace ℝ (Fin 3)) :
    blochState v = (1 / 2 : ℂ) • (1 : Mat2C) + (1 / 2 : ℂ) • pauliSlash v := by
  have ext : True := trivial
  rw [pauliSlash_eq]
  apply ext_mat2 <;> {
    simp only [blochState, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      mat2_00, mat2_01, mat2_10, mat2_11, Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte]
    ring
  }

lemma gibbsDensityC_eq_twoSheet (θ : ℝ) :
    gibbsDensityC θ = twoSheet (mat2 (1 : ℂ) 0 0 0) (boltzmannPlus θ) (boltzmannMinus θ) := by
  apply ext_mat2 <;>
    simp only [gibbsDensityC, twoSheet, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.smul_apply, Complex.real_smul, mat2_00, mat2_01, mat2_10, mat2_11,
      Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte] <;>
    ring

/-- Universal continuous functional calculus logarithm of the canonical Gibbs density. -/
theorem cfc_log_gibbsDensityC (θ : ℝ) (β ω : ℝ) :
    CFC.log (gibbsDensityC θ) = (θ : ℂ) • pauliGamma1 - (cumulantPsi θ : ℂ) • 1 ∧
    CFC.log (gibbsDensityC (boltzmannTheta β ω)) =
      -(β : ℂ) • thermalHamiltonian ω - (cumulantPsi (boltzmannTheta β ω) : ℂ) • 1 := by
  have hP0 : IsStarProjection (mat2 (1 : ℂ) 0 0 0) :=
    ⟨by change mat2 (1 : ℂ) 0 0 0 * mat2 1 0 0 0 = _; apply ext_mat2 <;> simp [mul2_00, mul2_01, mul2_10, mul2_11],
     by change star (mat2 (1 : ℂ) 0 0 0) = _; apply ext_mat2 <;> simp [Matrix.star_apply]⟩
  have h_bp_log : ∀ t : ℝ, Real.log (boltzmannPlus t) = t - cumulantPsi t := by
    intro t
    have hZ : partitionZ t ≠ 0 := ne_of_gt (partitionZ_pos t)
    have h_eq : boltzmannPlus t = Real.exp t / partitionZ t := by
      dsimp [boltzmannPlus]; rw [one_add_meanSpin]; ring
    rw [h_eq, Real.log_div (ne_of_gt (Real.exp_pos t)) hZ, Real.log_exp]; rfl
  have h_bm_log : ∀ t : ℝ, Real.log (boltzmannMinus t) = -t - cumulantPsi t := by
    intro t
    have hZ : partitionZ t ≠ 0 := ne_of_gt (partitionZ_pos t)
    have h_eq : boltzmannMinus t = Real.exp (-t) / partitionZ t := by
      dsimp [boltzmannMinus]; rw [one_sub_meanSpin]; ring
    rw [h_eq, Real.log_div (ne_of_gt (Real.exp_pos (-t))) hZ, Real.log_exp]; rfl
  have h_eval : ∀ t : ℝ, CFC.log (gibbsDensityC t) =
      (t : ℂ) • pauliGamma1 - (cumulantPsi t : ℂ) • (1 : Mat2C) := by
    intro t
    rw [gibbsDensityC_eq_twoSheet t, CFC.log, cfc_twoSheet hP0]
    apply ext_mat2
    · simp only [twoSheet, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Complex.real_smul, smul_eq_mul, pauliGamma1_eq,
        mat2_00, Fin.isValue, ↓reduceIte, h_bp_log t, h_bm_log t]
      push_cast; ring_nf
    · simp only [twoSheet, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Complex.real_smul, smul_eq_mul, pauliGamma1_eq,
        mat2_01, Fin.isValue, zero_ne_one, ↓reduceIte, h_bp_log t, h_bm_log t]
      push_cast; ring_nf
    · simp only [twoSheet, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Complex.real_smul, smul_eq_mul, pauliGamma1_eq,
        mat2_10, Fin.isValue, one_ne_zero, ↓reduceIte, h_bp_log t, h_bm_log t]
      push_cast; ring_nf
    · simp only [twoSheet, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Complex.real_smul, smul_eq_mul, pauliGamma1_eq,
        mat2_11, Fin.isValue, ↓reduceIte, h_bp_log t, h_bm_log t]
      push_cast; ring_nf
  refine ⟨h_eval θ, ?_⟩
  rw [h_eval (boltzmannTheta β ω)]
  dsimp [boltzmannTheta, thermalHamiltonian]
  congr 1
  rw [pauliGamma1_eq]
  apply ext_mat2 <;> {
    simp only [Matrix.smul_apply, Complex.real_smul, mat2_00, mat2_01,
      mat2_10, mat2_11, Fin.isValue]
    push_cast
    ring
  }

private lemma pauliSlash_zero : pauliSlash 0 = 0 := by
  apply ext_mat2 <;> simp [pauliSlash, pauliSigmaX_eq, pauliSigmaY_eq, pauliGamma1_eq, Matrix.add_apply]

private lemma blochState_isSelfAdjoint (v : EuclideanSpace ℝ (Fin 3)) :
    IsSelfAdjoint (blochState v) := by
  apply ext_mat2
  · simp [blochState, mat2_00, Matrix.star_apply]
  · simp [blochState, mat2_01, mat2_10, Matrix.star_apply]; ring
  · simp [blochState, mat2_01, mat2_10, Matrix.star_apply]
  · simp [blochState, mat2_11, Matrix.star_apply]

/-- Universal 3D continuous functional calculus logarithm of an open Bloch state. -/
theorem cfc_log_blochState_universal (r_vec : EuclideanSpace ℝ (Fin 3)) (hr : ‖r_vec‖ < 1) :
    CFC.log (blochState r_vec) =
      pauliSlash (legendreTheta3 r_vec) - (cumulantPsi3 (legendreTheta3 r_vec) : ℂ) • 1 := by
  by_cases hr0 : ‖r_vec‖ = 0
  · have h0 : r_vec = 0 := norm_eq_zero.mp hr0
    subst h0
    have h_bloch0 : blochState 0 = gibbsDensityC 0 := by
      apply ext_mat2 <;>
        simp [blochState, gibbsDensityC, boltzmannPlus, boltzmannMinus,
          meanSpin_zero_val, mat2_00, mat2_01, mat2_10, mat2_11, Fin.isValue]
    rw [h_bloch0]
    have hlog0 := (cfc_log_gibbsDensityC 0 0 0).1
    rw [hlog0]
    rw [legendreTheta3_zero, pauliSlash_zero]
    dsimp [cumulantPsi3]
    rw [norm_zero]
    simp only [zero_smul, zero_sub]
  · set r := ‖r_vec‖
    have hr_pos : 0 < r := lt_of_le_of_ne (norm_nonneg r_vec) (Ne.symm hr0)
    set n := r⁻¹ • r_vec
    have hn_sq : (n 0) ^ 2 + (n 1) ^ 2 + (n 2) ^ 2 = 1 := by
      have h_norm := euclidean_norm_sq_fin3 r_vec
      calc (n 0) ^ 2 + (n 1) ^ 2 + (n 2) ^ 2
        _ = (r⁻¹ * r_vec 0) ^ 2 + (r⁻¹ * r_vec 1) ^ 2 + (r⁻¹ * r_vec 2) ^ 2 := rfl
        _ = (r⁻¹ ^ 2) * ((r_vec 0) ^ 2 + (r_vec 1) ^ 2 + (r_vec 2) ^ 2) := by ring
        _ = (r⁻¹ ^ 2) * (r ^ 2) := by
          rw [h_norm]
        _ = (r⁻¹ * r) ^ 2 := by ring
        _ = (1 : ℝ) ^ 2 := by rw [inv_mul_cancel₀ (ne_of_gt hr_pos)]
        _ = 1 := by ring
    have hn_sq_c : (n 0 : ℂ) ^ 2 + (n 1 : ℂ) ^ 2 + (n 2 : ℂ) ^ 2 = 1 := by
      have h := congr_arg (fun x : ℝ => (x : ℂ)) hn_sq
      push_cast at h
      exact h
    have hP_idem : blochState n * blochState n = blochState n := by
      apply ext_mat2
      · simp only [blochState, mul2_00, mat2_00, mat2_01, mat2_10, Fin.isValue]
        have hI : Complex.I ^ 2 = -1 := Complex.I_sq
        linear_combination (1 / 4 : ℂ) * hn_sq_c - (1 / 4 * (n 1 : ℂ) ^ 2) * hI
      · simp only [blochState, mul2_01, mat2_00, mat2_01, mat2_11, Fin.isValue]
        ring
      · simp only [blochState, mul2_10, mat2_00, mat2_10, mat2_11, Fin.isValue]
        ring
      · simp only [blochState, mul2_11, mat2_01, mat2_10, mat2_11, Fin.isValue]
        have hI : Complex.I ^ 2 = -1 := Complex.I_sq
        linear_combination (1 / 4 : ℂ) * hn_sq_c - (1 / 4 * (n 1 : ℂ) ^ 2) * hI
    have hP_star : IsSelfAdjoint (blochState n) := blochState_isSelfAdjoint n
    have hP : IsStarProjection (blochState n) := ⟨hP_idem, hP_star⟩
    have hr_inv : (r : ℂ) * (r : ℂ)⁻¹ = 1 := by
      have hr_c : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)
      exact mul_inv_cancel₀ hr_c
    have h_twoSheet_eq : blochState r_vec =
        twoSheet (blochState n) ((1 + r) / 2) ((1 - r) / 2) := by
      apply ext_mat2
      · simp only [twoSheet, blochState, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
          Matrix.smul_apply, Complex.real_smul, mat2_00, Fin.isValue, ↓reduceIte]
        dsimp [n]
        push_cast
        linear_combination - (1 / 2 * (r_vec 2 : ℂ)) * hr_inv
      · simp only [twoSheet, blochState, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
          Matrix.smul_apply, Complex.real_smul, mat2_01, Fin.isValue, zero_ne_one, ↓reduceIte]
        dsimp [n]
        push_cast
        linear_combination - (1 / 2 * ((r_vec 0 : ℂ) - Complex.I * (r_vec 1 : ℂ))) * hr_inv
      · simp only [twoSheet, blochState, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
          Matrix.smul_apply, Complex.real_smul, mat2_10, Fin.isValue, one_ne_zero, ↓reduceIte]
        dsimp [n]
        push_cast
        linear_combination - (1 / 2 * ((r_vec 0 : ℂ) + Complex.I * (r_vec 1 : ℂ))) * hr_inv
      · simp only [twoSheet, blochState, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
          Matrix.smul_apply, Complex.real_smul, mat2_11, Fin.isValue, ↓reduceIte]
        dsimp [n]
        push_cast
        linear_combination (1 / 2 * (r_vec 2 : ℂ)) * hr_inv
    set a := Real.log ((1 + r) / 2)
    set b := Real.log ((1 - r) / 2)
    have h_cfc : CFC.log (blochState r_vec) = twoSheet (blochState n) a b := by
      rw [h_twoSheet_eq, CFC.log, cfc_twoSheet hP]
    rw [h_cfc]
    set θ := canonicalTheta r
    have h_ct_pos : 0 < θ := canonicalTheta_pos_of_pos hr_pos hr
    have h_theta_def : legendreTheta3 r_vec = (θ / r) • r_vec := by
      dsimp [legendreTheta3, artanhRatio, r]
      split_ifs with h0
      · exact (hr0 h0).elim
      · rfl
    have h_norm_th : ‖legendreTheta3 r_vec‖ = θ := by
      rw [h_theta_def, norm_smul, Real.norm_of_nonneg (le_of_lt (div_pos h_ct_pos hr_pos))]
      dsimp [r]
      exact div_mul_cancel₀ θ hr0
    have h_ms : meanSpin θ = r :=
      dually_flat_legendre_reciprocity_and_metric_inversion.2.1 r (by linarith) hr
    have h_bp_eq : (1 + r) / 2 = boltzmannPlus θ := by
      dsimp [boltzmannPlus]; rw [h_ms]
    have h_bm_eq : (1 - r) / 2 = boltzmannMinus θ := by
      dsimp [boltzmannMinus]; rw [h_ms]
    have hZ : partitionZ θ ≠ 0 := ne_of_gt (partitionZ_pos θ)
    have h_bp_exp : boltzmannPlus θ = Real.exp θ / partitionZ θ := by
      dsimp [boltzmannPlus]; rw [one_add_meanSpin]; ring
    have h_bm_exp : boltzmannMinus θ = Real.exp (-θ) / partitionZ θ := by
      dsimp [boltzmannMinus]; rw [one_sub_meanSpin]; ring
    have h_a_eq : a = θ - cumulantPsi θ := by
      dsimp [a]; rw [h_bp_eq, h_bp_exp, Real.log_div (ne_of_gt (Real.exp_pos θ)) hZ, Real.log_exp]; rfl
    have h_b_eq : b = -θ - cumulantPsi θ := by
      dsimp [b]; rw [h_bm_eq, h_bm_exp, Real.log_div (ne_of_gt (Real.exp_pos (-θ))) hZ, Real.log_exp]; rfl
    dsimp [cumulantPsi3]
    rw [h_norm_th]
    rw [pauliSlash_eq, h_theta_def]
    have hr_cancel : (θ : ℂ) * (r : ℂ)⁻¹ = (θ : ℂ) / (r : ℂ) := by
      have hr_c : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)
      field_simp [hr_c]
    apply ext_mat2
    · simp only [twoSheet, blochState, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Complex.real_smul, mat2_00, Fin.isValue, ↓reduceIte, h_a_eq, h_b_eq]
      dsimp [n]
      push_cast
      linear_combination (r_vec 2 : ℂ) * hr_cancel
    · simp only [twoSheet, blochState, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Complex.real_smul, mat2_01, Fin.isValue, zero_ne_one, ↓reduceIte, h_a_eq, h_b_eq]
      dsimp [n]
      push_cast
      linear_combination ((r_vec 0 : ℂ) - Complex.I * (r_vec 1 : ℂ)) * hr_cancel
    · simp only [twoSheet, blochState, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Complex.real_smul, mat2_10, Fin.isValue, one_ne_zero, ↓reduceIte, h_a_eq, h_b_eq]
      dsimp [n]
      push_cast
      linear_combination ((r_vec 0 : ℂ) + Complex.I * (r_vec 1 : ℂ)) * hr_cancel
    · simp only [twoSheet, blochState, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Complex.real_smul, mat2_11, Fin.isValue, ↓reduceIte, h_a_eq, h_b_eq]
      dsimp [n]
      push_cast
      linear_combination (-(r_vec 2 : ℂ)) * hr_cancel

/-!
### Section 4: $Y_1, Y_3 \prec Y_4$ & Rung 3: Diagonal Pinching, Operator Orthogonality & Quantum Pythagorean Theorem
-/

/-- Diagonal pinching (dephasing) projection $\mathcal{P}(\rho) = \frac{1}{2}(\rho + \Gamma_1 \rho \Gamma_1)$. -/
def diagPinch (ρ : Mat2C) : Mat2C :=
  (1 / 2 : ℂ) • (ρ + pauliGamma1 * ρ * pauliGamma1)

/-- Umegaki quantum relative entropy $D(\rho \| \sigma) = \operatorname{Re}(\operatorname{Tr}(\rho(\log\rho - \log\sigma)))$. -/
def umegakiDiv (ρ σ : Mat2C) : ℝ :=
  (Matrix.trace (umegakiKernel ρ σ)).re

/-- Symmetrized Umegaki–Jeffreys divergence $J(\rho, \sigma) = D(\rho \| \sigma) + D(\sigma \| \rho)$. -/
def umegakiJeffreys (ρ σ : Mat2C) : ℝ :=
  umegakiDiv ρ σ + umegakiDiv σ ρ

/-- Coherence relative entropy (information lost by pinching) $D_{\mathrm{coh}}(\rho) = \phi(\|\mathbf{r}\|) - \phi(r_z)$. -/
def coherenceRelEntropy (ρ : Mat2C) : ℝ :=
  negEntropyPhi (blochRadius ρ) - negEntropyPhi (blochZ ρ)

private lemma diagPinch_eq_mat2 (ρ : Mat2C) :
    diagPinch ρ = mat2 (ρ 0 0) 0 0 (ρ 1 1) := by
  have ext : True := trivial
  dsimp [diagPinch]
  rw [pauliGamma1_eq]
  apply ext_mat2
  · simp only [Matrix.add_apply, Matrix.smul_apply, mul2_00, mat2_00, mat2_01, mat2_10, Fin.isValue]
    ring
  · simp only [Matrix.add_apply, Matrix.smul_apply, mul2_01, mat2_00, mat2_01, mat2_11, Fin.isValue]
    ring
  · simp only [Matrix.add_apply, Matrix.smul_apply, mul2_10, mat2_00, mat2_10, mat2_11, Fin.isValue]
    ring
  · simp only [Matrix.add_apply, Matrix.smul_apply, mul2_11, mat2_01, mat2_10, mat2_11, Fin.isValue]
    ring

private lemma coherenceSq_nonneg (ρ : Mat2C) : 0 ≤ coherenceSq ρ :=
  mul_nonneg (by norm_num) (Complex.normSq_nonneg _)

private lemma trace_twoSheet_unitTrace {P : Mat2C}
    (htrP : Matrix.trace P = 1) (a b : ℝ) :
    Matrix.trace (twoSheet P a b) = ((a + b : ℝ) : ℂ) := by
  dsimp [twoSheet]
  rw [Matrix.trace_add, trace_real_smul, trace_real_smul, Matrix.trace_sub,
    trace_one_mat2, htrP]
  push_cast
  ring

private lemma negEntropyPhi_even (η : ℝ) : negEntropyPhi (-η) = negEntropyPhi η := by
  dsimp [negEntropyPhi]
  rw [show 1 + -η = 1 - η by ring, show 1 - -η = 1 + η by ring]
  ring

private lemma negEntropyPhi_mono_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    0 ≤ negEntropyPhi b - negEntropyPhi a ∧ (negEntropyPhi b - negEntropyPhi a = 0 ↔ a = b) := by
  have ha_lo : -1 < a := by linarith [ha]
  have ha_hi : a < 1 := by linarith [hab, hb]
  have hb_lo : -1 < b := by linarith
  have hb_pos := bregman_umegaki_positivity_and_pythagorean_theorem.2.1 b a hb_lo hb ha_lo ha_hi
  have h_th_nonneg : 0 ≤ canonicalTheta a := by
    dsimp [canonicalTheta]
    have h_ratio : 1 ≤ (1 + a) / (1 - a) := (one_le_div (by linarith)).mpr (by linarith)
    exact mul_nonneg (by norm_num) (Real.log_nonneg h_ratio)
  have h_breg_eq : negEntropyPhi b - negEntropyPhi a =
      bregmanPhi b a + canonicalTheta a * (b - a) := by
    dsimp [bregmanPhi]
    ring
  have h_prod_nonneg : 0 ≤ canonicalTheta a * (b - a) := mul_nonneg h_th_nonneg (sub_nonneg.mpr hab)
  refine ⟨by rw [h_breg_eq]; linarith [hb_pos.1], ?_⟩
  constructor
  · intro h_zero
    have h_breg_zero : bregmanPhi b a = 0 := by
      rw [h_breg_eq] at h_zero
      linarith [hb_pos.1]
    exact (hb_pos.2.mp h_breg_zero).symm
  · intro h_ab
    subst h_ab
    ring

private lemma blochZ_gibbsDensityC (θ : ℝ) : blochZ (gibbsDensityC θ) = meanSpin θ := by
  dsimp [blochZ, gibbsDensityC, boltzmannPlus, boltzmannMinus]
  ring

private lemma coherenceSq_gibbsDensityC (θ : ℝ) : coherenceSq (gibbsDensityC θ) = 0 := by
  dsimp [coherenceSq]
  have h01 : gibbsDensityC θ 0 1 = 0 := rfl
  rw [h01, Complex.normSq_zero, mul_zero]

private lemma umegakiKernel_trace_formula {ρ : Mat2C}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (hb : blochNormSq ρ < 1) (θ : ℝ) :
    Matrix.trace (umegakiKernel ρ (gibbsDensityC θ)) =
      ((negEntropyPhi (blochRadius ρ) + cumulantPsi θ - θ * blochZ ρ : ℝ) : ℂ) := by
  rcases spectralProjector_twoSheet_and_cfc_log hsa htr hb with ⟨hP, htrP, h2s, _, hlogρ⟩
  have hlogG := (cfc_log_gibbsDensityC θ 0 0).1
  rcases hermitian_unitTrace_entries hsa htr with ⟨-, -, -, hpg⟩
  have h_umegaki_eq : umegakiKernel ρ (gibbsDensityC θ) =
      ρ * CFC.log ρ - ρ * CFC.log (gibbsDensityC θ) := by
    rw [umegakiKernel_apply, CFC.log, CFC.log, mul_sub]
  have h_tr_ρlogρ : Matrix.trace (ρ * CFC.log ρ) = ((negEntropyPhi (blochRadius ρ) : ℝ) : ℂ) := by
    have h_mul : ρ * CFC.log ρ =
        twoSheet (spectralProjector ρ)
          (((1 + blochRadius ρ) / 2) * Real.log ((1 + blochRadius ρ) / 2))
          (((1 - blochRadius ρ) / 2) * Real.log ((1 - blochRadius ρ) / 2)) := by
      calc ρ * CFC.log ρ
        _ = twoSheet (spectralProjector ρ) ((1 + blochRadius ρ) / 2) ((1 - blochRadius ρ) / 2) *
              twoSheet (spectralProjector ρ) (Real.log ((1 + blochRadius ρ) / 2))
                (Real.log ((1 - blochRadius ρ) / 2)) := by rw [h2s, hlogρ]
        _ = _ := twoSheet_mul (spectralProjector ρ) hP.isIdempotentElem.eq _ _ _ _
    rw [h_mul, trace_twoSheet_unitTrace htrP]
    rfl
  have h_tr_ρlogG : Matrix.trace (ρ * CFC.log (gibbsDensityC θ)) =
      ((θ * blochZ ρ - cumulantPsi θ : ℝ) : ℂ) := by
    rw [hlogG, mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, hpg,
      Matrix.mul_smul, Matrix.trace_smul, mul_one, htr, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [h_umegaki_eq, Matrix.trace_sub, h_tr_ρlogρ, h_tr_ρlogG]
  push_cast
  ring

/-- Rung 3: Algebraic and metric properties of diagonal pinching. -/
theorem rung3_pinching_properties (ρ : Mat2C) :
    diagPinch (diagPinch ρ) = diagPinch ρ ∧
    diagPinch pauliSigmaX = 0 ∧ pauliSigmaX ≠ 0 ∧
    ρ - diagPinch ρ = (ρ 0 1) • wittFPlus + (ρ 1 0) • wittFMinus ∧
    (InOpenBlochBall ρ → InOpenBlochBall (diagPinch ρ)) := by
  have h_idem : diagPinch (diagPinch ρ) = diagPinch ρ := by
    rw [diagPinch_eq_mat2, diagPinch_eq_mat2]
    simp only [mat2_00, mat2_11, Fin.isValue]
  have h_sx : diagPinch pauliSigmaX = 0 := by
    rw [diagPinch_eq_mat2, pauliSigmaX_eq]
    apply ext_mat2 <;> simp [mat2_00, mat2_11]
  have h_sx_ne : pauliSigmaX ≠ 0 := by
    intro h
    have h01 := congrArg (fun M : Mat2C => M 0 1) h
    rw [pauliSigmaX_eq] at h01
    simp [mat2_01] at h01
  have h_offdiag : ρ - diagPinch ρ = (ρ 0 1) • wittFPlus + (ρ 1 0) • wittFMinus := by
    rw [diagPinch_eq_mat2, wittFPlus_eq, wittFMinus_eq]
    apply ext_mat2 <;> {
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        mat2_00, mat2_01, mat2_10, mat2_11, Fin.isValue]
      ring
    }
  have h_pres : InOpenBlochBall ρ → InOpenBlochBall (diagPinch ρ) := by
    intro hρ
    rw [diagPinch_eq_mat2]
    rcases hermitian_unitTrace_entries hρ.1 hρ.2.1 with ⟨h00, h11, -, -⟩
    have h_sa : IsSelfAdjoint (mat2 (ρ 0 0) 0 0 (ρ 1 1)) := by
      apply ext_mat2 <;> {
        simp only [Matrix.star_apply, mat2_00, mat2_01, mat2_10, mat2_11, h00, h11,
          Fin.isValue, star_zero, Complex.star_def, Complex.conj_ofReal]
      }
    have h_tr : Matrix.trace (mat2 (ρ 0 0) 0 0 (ρ 1 1)) = 1 := by
      rw [trace_fin2]
      simp only [mat2_00, mat2_11, Fin.isValue]
      have htr_ρ := hρ.2.1
      rw [trace_fin2] at htr_ρ
      exact htr_ρ
    have h_norm : blochNormSq (mat2 (ρ 0 0) 0 0 (ρ 1 1)) < 1 := by
      dsimp [blochNormSq, coherenceSq, blochZ]
      simp only [Complex.normSq_zero, mul_zero, add_zero]
      have hz_sq : ((ρ 0 0 - ρ 1 1).re) ^ 2 ≤ blochNormSq ρ := by
        dsimp [blochNormSq, blochZ]
        linarith [coherenceSq_nonneg ρ]
      exact lt_of_le_of_lt hz_sq hρ.2.2
    exact ⟨h_sa, h_tr, h_norm⟩
  exact ⟨h_idem, h_sx, h_sx_ne, h_offdiag, h_pres⟩

/-- Rung 3: Off-diagonal pinching complement is trace-orthogonal to diagonal relative log density. -/
theorem rung3_operator_trace_orthogonality (ρ : Mat2C) (θ : ℝ) (hρ : InOpenBlochBall ρ) :
    Matrix.trace ((ρ - diagPinch ρ) * (CFC.log (diagPinch ρ) - CFC.log (gibbsDensityC θ))) = 0 := by
  have hz_bounds := blochZ_abs_lt_one hρ.2.2
  set θ_z := canonicalTheta (blochZ ρ)
  have hm_z : meanSpin θ_z = blochZ ρ :=
    dually_flat_legendre_reciprocity_and_metric_inversion.2.1 (blochZ ρ) hz_bounds.1 hz_bounds.2
  rcases hermitian_unitTrace_entries hρ.1 hρ.2.1 with ⟨h00, h11, -, -⟩
  have h_pinch_gibbs : diagPinch ρ = gibbsDensityC θ_z := by
    rw [diagPinch_eq_mat2]
    apply ext_mat2
    · simp only [gibbsDensityC, boltzmannPlus, hm_z, h00, mat2_00, Fin.isValue]
    · simp only [gibbsDensityC, mat2_01, Fin.isValue]
    · simp only [gibbsDensityC, mat2_10, Fin.isValue]
    · simp only [gibbsDensityC, boltzmannMinus, hm_z, h11, mat2_11, Fin.isValue]
  have h_log_pz := (cfc_log_gibbsDensityC θ_z 0 0).1
  have h_log_g := (cfc_log_gibbsDensityC θ 0 0).1
  have h_offdiag : ρ - diagPinch ρ = (ρ 0 1) • wittFPlus + (ρ 1 0) • wittFMinus :=
    (rung3_pinching_properties ρ).2.2.2.1
  rw [h_offdiag, h_pinch_gibbs, h_log_pz, h_log_g]
  rw [trace_fin2, mul2_00, mul2_11]
  rw [pauliGamma1_eq, wittFPlus_eq, wittFMinus_eq]
  simp only [mat2_00, mat2_01, mat2_10, mat2_11, Fin.isValue,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, zero_ne_one, one_ne_zero, ↓reduceIte]
  ring

/-- Rung 3: Quantum Pythagorean pinching decomposition and divergence faithfulness. -/
theorem rung3_quantum_pythagorean_identity (ρ : Mat2C) (θ : ℝ) (hρ : InOpenBlochBall ρ) :
    umegakiDiv ρ (diagPinch ρ) = coherenceRelEntropy ρ ∧
    umegakiDiv (diagPinch ρ) (gibbsDensityC θ) = bregmanPhi (blochZ ρ) (meanSpin θ) ∧
    umegakiDiv ρ (gibbsDensityC θ) =
      umegakiDiv ρ (diagPinch ρ) + umegakiDiv (diagPinch ρ) (gibbsDensityC θ) ∧
    (0 ≤ coherenceRelEntropy ρ ∧ (coherenceRelEntropy ρ = 0 ↔ diagPinch ρ = ρ)) ∧
    (0 ≤ umegakiDiv ρ (gibbsDensityC θ) ∧ (umegakiDiv ρ (gibbsDensityC θ) = 0 ↔ ρ = gibbsDensityC θ)) := by
  have ext : True := trivial
  have hz_bounds := blochZ_abs_lt_one hρ.2.2
  set θ_z := canonicalTheta (blochZ ρ)
  have hm_z : meanSpin θ_z = blochZ ρ :=
    dually_flat_legendre_reciprocity_and_metric_inversion.2.1 (blochZ ρ) hz_bounds.1 hz_bounds.2
  rcases hermitian_unitTrace_entries hρ.1 hρ.2.1 with ⟨h00, h11, -, -⟩
  have h_pinch_gibbs : diagPinch ρ = gibbsDensityC θ_z := by
    rw [diagPinch_eq_mat2]
    apply ext_mat2
    · simp only [gibbsDensityC, boltzmannPlus, hm_z, h00, mat2_00, Fin.isValue]
    · simp only [gibbsDensityC, mat2_01, Fin.isValue]
    · simp only [gibbsDensityC, mat2_10, Fin.isValue]
    · simp only [gibbsDensityC, boltzmannMinus, hm_z, h11, mat2_11, Fin.isValue]
  have h_pinch_ball : InOpenBlochBall (diagPinch ρ) :=
    (rung3_pinching_properties ρ).2.2.2.2 hρ
  have h_tr_ρ_θz := umegakiKernel_trace_formula hρ.1 hρ.2.1 hρ.2.2 θ_z
  have h_fy_z : cumulantPsi θ_z + negEntropyPhi (meanSpin θ_z) = θ_z * meanSpin θ_z :=
    dually_flat_legendre_reciprocity_and_metric_inversion.2.2.1 θ_z
  have h_div_coh : umegakiDiv ρ (diagPinch ρ) = coherenceRelEntropy ρ := by
    change (Matrix.trace (umegakiKernel ρ (diagPinch ρ))).re = coherenceRelEntropy ρ
    rw [h_pinch_gibbs, h_tr_ρ_θz]
    simp only [Complex.ofReal_re]
    dsimp [coherenceRelEntropy]
    rw [hm_z] at h_fy_z
    linarith
  have h_pinch_z : blochZ (diagPinch ρ) = blochZ ρ := by
    rw [diagPinch_eq_mat2]
    simp only [blochZ, mat2_00, mat2_11, Fin.isValue]
  have h_pinch_norm : blochNormSq (diagPinch ρ) = (blochZ ρ) ^ 2 := by
    rw [diagPinch_eq_mat2]
    dsimp [blochNormSq, coherenceSq, blochZ]
    simp only [Complex.normSq_zero, mul_zero, add_zero]
  have h_pinch_rad : blochRadius (diagPinch ρ) = |blochZ ρ| := by
    dsimp [blochRadius]
    rw [h_pinch_norm, Real.sqrt_sq_eq_abs]
  have h_tr_pinch_θ := umegakiKernel_trace_formula h_pinch_ball.1 h_pinch_ball.2.1 h_pinch_ball.2.2 θ
  have h_th_ms : canonicalTheta (meanSpin θ) = θ :=
    dually_flat_legendre_reciprocity_and_metric_inversion.1 θ
  have h_fy_θ : cumulantPsi θ + negEntropyPhi (meanSpin θ) = θ * meanSpin θ :=
    dually_flat_legendre_reciprocity_and_metric_inversion.2.2.1 θ
  have h_div_pop : umegakiDiv (diagPinch ρ) (gibbsDensityC θ) = bregmanPhi (blochZ ρ) (meanSpin θ) := by
    change (Matrix.trace (umegakiKernel (diagPinch ρ) (gibbsDensityC θ))).re = bregmanPhi (blochZ ρ) (meanSpin θ)
    rw [h_tr_pinch_θ]
    simp only [Complex.ofReal_re]
    rw [h_pinch_z, h_pinch_rad]
    have hz_abs_phi : negEntropyPhi |blochZ ρ| = negEntropyPhi (blochZ ρ) := by
      rcases le_total 0 (blochZ ρ) with hz_nn | hz_np
      · rw [abs_of_nonneg hz_nn]
      · rw [abs_of_nonpos hz_np, negEntropyPhi_even]
    rw [hz_abs_phi]
    dsimp [bregmanPhi]
    rw [h_th_ms]
    linarith
  have h_tr_ρ_θ := umegakiKernel_trace_formula hρ.1 hρ.2.1 hρ.2.2 θ
  have h_div_tot : umegakiDiv ρ (gibbsDensityC θ) =
      umegakiDiv ρ (diagPinch ρ) + umegakiDiv (diagPinch ρ) (gibbsDensityC θ) := by
    change (Matrix.trace (umegakiKernel ρ (gibbsDensityC θ))).re =
      umegakiDiv ρ (diagPinch ρ) + umegakiDiv (diagPinch ρ) (gibbsDensityC θ)
    rw [h_tr_ρ_θ]
    simp only [Complex.ofReal_re]
    rw [h_div_coh, h_div_pop]
    dsimp [coherenceRelEntropy, bregmanPhi]
    rw [h_th_ms]
    linarith
  have h_abs_le_r : |blochZ ρ| ≤ blochRadius ρ := by
    have hsq : |blochZ ρ| ^ 2 ≤ (blochRadius ρ) ^ 2 := by
      rw [sq_abs, blochRadius_sq]
      dsimp [blochNormSq, coherenceSq]
      linarith [Complex.normSq_nonneg (ρ 0 1)]
    nlinarith [abs_nonneg (blochZ ρ), blochRadius_nonneg ρ]
  have h_mono := negEntropyPhi_mono_nonneg (abs_nonneg (blochZ ρ)) h_abs_le_r (blochRadius_lt_one hρ.2.2)
  have h_phi_abs : negEntropyPhi |blochZ ρ| = negEntropyPhi (blochZ ρ) := by
    rcases le_total 0 (blochZ ρ) with hz_nn | hz_np
    · rw [abs_of_nonneg hz_nn]
    · rw [abs_of_nonpos hz_np, negEntropyPhi_even]
  have h_coh_eq : coherenceRelEntropy ρ = negEntropyPhi (blochRadius ρ) - negEntropyPhi |blochZ ρ| := by
    dsimp [coherenceRelEntropy]
    rw [h_phi_abs]
  have h_coh_nonneg : 0 ≤ coherenceRelEntropy ρ ∧ (coherenceRelEntropy ρ = 0 ↔ diagPinch ρ = ρ) := by
    rw [h_coh_eq]
    refine ⟨h_mono.1, ?_⟩
    rw [h_mono.2]
    constructor
    · intro h_eq
      have hsq : (blochZ ρ) ^ 2 = (blochRadius ρ) ^ 2 := by
        rw [← h_eq, sq_abs]
      rw [blochRadius_sq] at hsq
      dsimp [blochNormSq, coherenceSq] at hsq
      have hns0 : Complex.normSq (ρ 0 1) = 0 := by
        linarith
      have h01 : ρ 0 1 = 0 := Complex.normSq_eq_zero.mp hns0
      rcases hermitian_unitTrace_entries hρ.1 hρ.2.1 with ⟨-, -, h10, -⟩
      have h10_zero : ρ 1 0 = 0 := by
        rw [h10, h01, star_zero]
      rw [diagPinch_eq_mat2]
      apply ext_mat2 <;> {
        simp only [mat2_00, mat2_01, mat2_10, mat2_11, h01, h10_zero, Fin.isValue]
      }
    · intro h_eq
      have h01 : ρ 0 1 = 0 := by
        have h := congrArg (fun M : Mat2C => M 0 1) h_eq
        rw [diagPinch_eq_mat2] at h
        simpa only [mat2_01] using h.symm
      have hbn : blochNormSq ρ = (blochZ ρ) ^ 2 := by
        dsimp [blochNormSq, coherenceSq]
        simp only [h01, Complex.normSq_zero, mul_zero, add_zero]
      dsimp [blochRadius]
      rw [hbn, Real.sqrt_sq_eq_abs]
  have h_breg_pos := bregman_umegaki_positivity_and_pythagorean_theorem.2.1 (blochZ ρ) (meanSpin θ)
    hz_bounds.1 hz_bounds.2 (meanSpin_mem_Ioo θ).1 (meanSpin_mem_Ioo θ).2
  have h_umegaki_nonneg : 0 ≤ umegakiDiv ρ (gibbsDensityC θ) ∧
      (umegakiDiv ρ (gibbsDensityC θ) = 0 ↔ ρ = gibbsDensityC θ) := by
    rw [h_div_tot]
    refine ⟨by linarith [h_coh_nonneg.1, h_breg_pos.1], ?_⟩
    constructor
    · intro h0
      have hc_zero : coherenceRelEntropy ρ = 0 := by
        linarith [h_coh_nonneg.1, h_breg_pos.1]
      have hb_zero : bregmanPhi (blochZ ρ) (meanSpin θ) = 0 := by
        linarith [h_coh_nonneg.1, h_breg_pos.1]
      have h_diag : diagPinch ρ = ρ := h_coh_nonneg.2.mp hc_zero
      have hz_eq : blochZ ρ = meanSpin θ := h_breg_pos.2.mp hb_zero
      rw [← h_diag, h_pinch_gibbs]
      have hth_eq : θ_z = θ := by
        dsimp [θ_z]
        rw [hz_eq, dually_flat_legendre_reciprocity_and_metric_inversion.1 θ]
      rw [hth_eq]
    · intro h_eq
      subst h_eq
      have h_c0 : coherenceRelEntropy (gibbsDensityC θ) = 0 := by
        dsimp [coherenceRelEntropy]
        have h01 : gibbsDensityC θ 0 1 = 0 := rfl
        have hbn : blochNormSq (gibbsDensityC θ) = (blochZ (gibbsDensityC θ)) ^ 2 := by
          dsimp [blochNormSq, coherenceSq]
          simp only [h01, Complex.normSq_zero, mul_zero, add_zero]
        dsimp [blochRadius]
        rw [hbn, Real.sqrt_sq_eq_abs]
        have hz_abs_phi : negEntropyPhi |blochZ (gibbsDensityC θ)| = negEntropyPhi (blochZ (gibbsDensityC θ)) := by
          rcases le_total 0 (blochZ (gibbsDensityC θ)) with hz_nn | hz_np
          · rw [abs_of_nonneg hz_nn]
          · rw [abs_of_nonpos hz_np, negEntropyPhi_even]
        rw [hz_abs_phi]
        ring
      have h_b0 : bregmanPhi (blochZ (gibbsDensityC θ)) (meanSpin θ) = 0 := by
        rw [blochZ_gibbsDensityC]
        exact (bregman_umegaki_positivity_and_pythagorean_theorem.2.1
          (meanSpin θ) (meanSpin θ) (meanSpin_mem_Ioo θ).1 (meanSpin_mem_Ioo θ).2
          (meanSpin_mem_Ioo θ).1 (meanSpin_mem_Ioo θ).2).2.mpr rfl
      rw [h_div_coh, h_div_pop, h_c0, h_b0, add_zero]
  exact ⟨h_div_coh, h_div_pop, h_div_tot, h_coh_nonneg, h_umegaki_nonneg⟩

/-!
### Section 5: $Y_2, Y_4 \prec Y_5$ & Rung 4: Larmor Equipotential Orthogonality & Affine Geodesic Characterization
-/

/-- Predicate asserting that semigroup trajectory $\rho(t)$ traces an affine mixture chord
toward $\rho_{\mathrm{Gibbs}}(\theta)$ for all $t \ge 0$. -/
def IsAffineGibbsChord (γ ω θ : ℝ) (ρ : Mat2C) : Prop :=
  ∃ lam : ℝ → ℝ, ∀ t : ℝ, 0 ≤ t →
    thermalSemigroupC γ ω θ t ρ - gibbsDensityC θ = (lam t : ℂ) • (ρ - gibbsDensityC θ)

private lemma thermalSemigroupC_00 (γ ω θ t : ℝ) (ρ : Mat2C) :
    thermalSemigroupC γ ω θ t ρ 0 0 =
      (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
        (Real.exp (-γ * t) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1)) := rfl

private lemma thermalSemigroupC_01 (γ ω θ t : ℝ) (ρ : Mat2C) :
    thermalSemigroupC γ ω θ t ρ 0 1 =
      (Real.exp (-(γ / 2) * t) : ℂ) * Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ)) * ρ 0 1 := rfl

private lemma thermalSemigroupC_10 (γ ω θ t : ℝ) (ρ : Mat2C) :
    thermalSemigroupC γ ω θ t ρ 1 0 =
      (Real.exp (-(γ / 2) * t) : ℂ) * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ)) * ρ 1 0 := rfl

private lemma thermalSemigroupC_11 (γ ω θ t : ℝ) (ρ : Mat2C) :
    thermalSemigroupC γ ω θ t ρ 1 1 =
      (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
        (Real.exp (-γ * t) : ℂ) * (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1)) := rfl

private lemma coherenceSq_eq_zero_iff (ρ : Mat2C) :
    coherenceSq ρ = 0 ↔ ρ 0 1 = 0 := by
  dsimp [coherenceSq]
  constructor
  · intro h
    have hns : Complex.normSq (ρ 0 1) = 0 := by linarith
    exact Complex.normSq_eq_zero.mp hns
  · intro h
    rw [h, Complex.normSq_zero, mul_zero]

private lemma exp_neg_half_ne_exp_neg {γ : ℝ} (hγ : 0 < γ) :
    Real.exp (-γ) ≠ Real.exp (-(γ / 2)) := by
  intro h_eq
  have h_arg := Real.exp_injective h_eq
  linarith [hγ]

/-- Transverse squared coherence decays at rate $-\gamma$ with exact $\omega$-cancellation. -/
theorem coherenceSq_deriv_eq (γ ω θ : ℝ) {ρ : Mat2C}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coherenceSq (thermalSemigroupC γ ω θ s ρ))
      (-γ * coherenceSq (thermalSemigroupC γ ω θ t ρ)) t := by
  have h_eq : (fun s : ℝ => coherenceSq (thermalSemigroupC γ ω θ s ρ)) =
      (fun s : ℝ => Real.exp (-γ * s) * coherenceSq ρ) := by
    ext s
    exact (thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ s hsa htr).2.2.2
  rw [h_eq]
  have hd_lin : HasDerivAt (fun s : ℝ => -γ * s) (-γ) t := by
    simpa using (hasDerivAt_id t).const_mul (-γ)
  have h_exp : HasDerivAt (fun s : ℝ => Real.exp (-γ * s)) (Real.exp (-γ * t) * (-γ)) t :=
    (Real.hasDerivAt_exp (-γ * t)).comp t hd_lin
  have hc_t := (thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hsa htr).2.2.2
  exact (h_exp.mul_const (coherenceSq ρ)).congr_deriv (by rw [hc_t]; ring_nf)

/-- Parabolic envelope relation preserved along all semigroup trajectories. -/
theorem parabolic_envelope_invariant (γ ω θ : ℝ) {ρ : Mat2C}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (t : ℝ) :
    (blochZ (thermalSemigroupC γ ω θ t ρ) - meanSpin θ) * coherenceSq ρ =
      (blochZ ρ - meanSpin θ) * coherenceSq (thermalSemigroupC γ ω θ t ρ) := by
  have h_tc := thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hsa htr
  rw [h_tc.2.2.1, h_tc.2.2.2]
  dsimp [etaTraj]
  ring_nf

/-- Commutator $-[\Gamma_1, \rho]$ is trace-orthogonal to relative surprisal $\log\rho - \log\rho_{\mathrm{Gibbs}}$. -/
theorem larmor_equipotential_trace_vanishing (ω θ : ℝ) {ρ : Mat2C}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (hb : blochNormSq ρ < 1) :
    Matrix.trace ((-(Complex.I * (ω : ℂ) / 2) • ⁅pauliGamma1, ρ⁆) *
      (CFC.log ρ - CFC.log (gibbsDensityC θ))) = 0 := by
  have h_comm_right : ∀ A B C : Mat2C, B * C = C * B →
      Matrix.trace (⁅A, B⁆ * C) = 0 := by
    intro A B C hBC
    rw [Ring.lie_def, sub_mul, Matrix.trace_sub, Matrix.mul_assoc A B C, hBC,
      ← Matrix.mul_assoc A C B, Matrix.trace_mul_comm (A * C) B,
      ← Matrix.mul_assoc B A C, sub_self]
  have h_comm_left : ∀ A B C : Mat2C, A * C = C * A →
      Matrix.trace (⁅A, B⁆ * C) = 0 := by
    intro A B C hAC
    rw [Ring.lie_def, sub_mul, Matrix.trace_sub, Matrix.mul_assoc, Matrix.trace_mul_comm A (B * C),
      Matrix.mul_assoc, Matrix.mul_assoc, ← hAC, ← Matrix.mul_assoc B A C, sub_self]
  have h_rho_log : ρ * CFC.log ρ = CFC.log ρ * ρ := by
    rcases spectralProjector_twoSheet_and_cfc_log hsa htr hb with ⟨hP, _, h2s, _, hlogρ⟩
    calc ρ * CFC.log ρ
      _ = twoSheet (spectralProjector ρ) ((1 + blochRadius ρ) / 2) ((1 - blochRadius ρ) / 2) *
            twoSheet (spectralProjector ρ) (Real.log ((1 + blochRadius ρ) / 2))
              (Real.log ((1 - blochRadius ρ) / 2)) := by rw [h2s, hlogρ]
      _ = twoSheet (spectralProjector ρ)
            (((1 + blochRadius ρ) / 2) * Real.log ((1 + blochRadius ρ) / 2))
            (((1 - blochRadius ρ) / 2) * Real.log ((1 - blochRadius ρ) / 2)) :=
          twoSheet_mul _ hP.isIdempotentElem.eq _ _ _ _
      _ = twoSheet (spectralProjector ρ)
            (Real.log ((1 + blochRadius ρ) / 2) * ((1 + blochRadius ρ) / 2))
            (Real.log ((1 - blochRadius ρ) / 2) * ((1 - blochRadius ρ) / 2)) := by
          rw [mul_comm ((1 + blochRadius ρ) / 2), mul_comm ((1 - blochRadius ρ) / 2)]
      _ = twoSheet (spectralProjector ρ) (Real.log ((1 + blochRadius ρ) / 2))
            (Real.log ((1 - blochRadius ρ) / 2)) *
            twoSheet (spectralProjector ρ) ((1 + blochRadius ρ) / 2) ((1 - blochRadius ρ) / 2) :=
          (twoSheet_mul _ hP.isIdempotentElem.eq _ _ _ _).symm
      _ = CFC.log ρ * ρ := by rw [← hlogρ, h2s]
  have h_pg_logG : pauliGamma1 * CFC.log (gibbsDensityC θ) =
      CFC.log (gibbsDensityC θ) * pauliGamma1 := by
    rw [(cfc_log_gibbsDensityC θ 0 0).1]
    apply ext_mat2 <;> simp [pauliGamma1_eq, mat2_00, mat2_01, mat2_10, mat2_11]
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_sub, Matrix.trace_sub,
    h_comm_right pauliGamma1 ρ (CFC.log ρ) h_rho_log,
    h_comm_left pauliGamma1 ρ (CFC.log (gibbsDensityC θ)) h_pg_logG,
    sub_zero, mul_zero]

/-- Characterization of affine Gibbs chords under the GKSL thermal flow. -/
theorem isAffineGibbsChord_iff
    {γ : ℝ} (hγ : 0 < γ) (ω θ : ℝ) {ρ : Mat2C}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) :
    IsAffineGibbsChord γ ω θ ρ ↔
      (coherenceSq ρ = 0 ∨ (blochZ ρ = meanSpin θ ∧ ω = 0)) := by
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, _⟩
  have h_tr_c : ρ 0 0 + ρ 1 1 = 1 := by rw [trace_fin2] at htr; exact htr
  constructor
  · rintro ⟨lam, hlam⟩
    by_cases h01 : ρ 0 1 = 0
    · left; rw [coherenceSq_eq_zero_iff]; exact h01
    · right
      have hω : ω = 0 := by
        by_contra hω_ne
        set t₀ : ℝ := Real.pi / (2 * |ω|)
        have habs_pos : 0 < |ω| := abs_pos.mpr hω_ne
        have ht₀_pos : 0 < t₀ := div_pos Real.pi_pos (mul_pos (by norm_num) habs_pos)
        have h_at_t₀ := congrArg (fun M : Mat2C => M 0 1)
          (hlam t₀ (le_of_lt ht₀_pos))
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          thermalSemigroupC_01, gibbsDensityC, mat2_01, sub_zero] at h_at_t₀
        have h_cancel : ((Real.exp (-(γ / 2) * t₀) : ℂ) *
            Complex.exp (-Complex.I * (ω : ℂ) * (t₀ : ℂ))) = (lam t₀ : ℂ) :=
          mul_right_cancel₀ h01 h_at_t₀
        have h_im := congrArg Complex.im h_cancel
        have h_arg : -Complex.I * (ω : ℂ) * (t₀ : ℂ) = ((-(ω * t₀) : ℝ) : ℂ) * Complex.I := by
          push_cast; ring_nf
        rw [h_arg, Complex.exp_ofReal_mul_I] at h_im
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_mul,
          zero_add, Real.sin_neg] at h_im
        have h_exp_ne : Real.exp (-(γ / 2) * t₀) ≠ 0 := ne_of_gt (Real.exp_pos _)
        have h_sin_neg : -Real.sin (ω * t₀) = 0 := by
          have := mul_eq_zero.mp h_im
          rcases this with h0 | hsin
          · exact absurd h0 h_exp_ne
          · exact hsin
        have h_sin0 : Real.sin (ω * t₀) = 0 := neg_eq_zero.mp h_sin_neg
        rcases lt_or_gt_of_ne hω_ne with hω_neg | hω_pos
        · have hwt : ω * t₀ = -(Real.pi / 2) := by
            dsimp [t₀]
            rw [abs_of_neg hω_neg]
            field_simp [hω_ne]
          rw [hwt, Real.sin_neg, Real.sin_pi_div_two] at h_sin0
          norm_num at h_sin0
        · have hwt : ω * t₀ = Real.pi / 2 := by
            dsimp [t₀]
            rw [abs_of_pos hω_pos]
            field_simp [hω_ne]
          rw [hwt, Real.sin_pi_div_two] at h_sin0
          norm_num at h_sin0
      have h_at_1_01 := congrArg (fun M : Mat2C => M 0 1) (hlam 1 zero_le_one)
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        thermalSemigroupC_01, gibbsDensityC, mat2_01, sub_zero, hω, Complex.ofReal_zero,
        mul_zero, zero_mul, Complex.exp_zero, mul_one] at h_at_1_01
      have h_lam1_c : (Real.exp (-(γ / 2)) : ℂ) = (lam 1 : ℂ) :=
        mul_right_cancel₀ h01 h_at_1_01
      have h_lam1 : lam 1 = Real.exp (-(γ / 2)) :=
        (Complex.ofReal_injective h_lam1_c).symm
      have h_at_1_00 := congrArg (fun M : Mat2C => M 0 0) (hlam 1 zero_le_one)
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        thermalSemigroupC_00, h_tr_c, mul_one, gibbsDensityC, mat2_00, h_lam1] at h_at_1_00
      have h_lhs_00 :
          (boltzmannPlus θ : ℂ) + (Real.exp (-γ) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ)) -
            (boltzmannPlus θ : ℂ) =
            (Real.exp (-γ) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ)) := by
        abel
      rw [h_lhs_00] at h_at_1_00
      have h_re_00 := congrArg Complex.re h_at_1_00
      rw [h00] at h_re_00
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
        zero_mul, sub_zero] at h_re_00
      have h_diff_0 : (Real.exp (-γ) - Real.exp (-(γ / 2))) *
          ((1 + blochZ ρ) / 2 - boltzmannPlus θ) = 0 := by
        have := sub_eq_zero.mpr h_re_00
        dsimp [boltzmannPlus] at this ⊢
        linear_combination this
      have h_exp_diff_ne : Real.exp (-γ) - Real.exp (-(γ / 2)) ≠ 0 :=
        sub_ne_zero.mpr (exp_neg_half_ne_exp_neg hγ)
      have h_bp_eq : (1 + blochZ ρ) / 2 - boltzmannPlus θ = 0 :=
        (mul_eq_zero.mp h_diff_0).resolve_left h_exp_diff_ne
      have hz_eq : blochZ ρ = meanSpin θ := by
        dsimp [boltzmannPlus] at h_bp_eq
        linear_combination 2 * h_bp_eq
      exact ⟨hz_eq, hω⟩
  · rintro (hc0 | ⟨hz_eq, hω⟩)
    · have h01 : ρ 0 1 = 0 := (coherenceSq_eq_zero_iff ρ).mp hc0
      refine ⟨fun t => Real.exp (-γ * t), fun t _ => ?_⟩
      have h10_zero : ρ 1 0 = 0 := by rw [h10, h01, star_zero]
      apply ext_mat2
      · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          thermalSemigroupC_00, h_tr_c, mul_one, gibbsDensityC, mat2_00]
        abel
      · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          thermalSemigroupC_01, gibbsDensityC, mat2_01, h01, mul_zero, sub_zero]
      · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          thermalSemigroupC_10, gibbsDensityC, mat2_10, h10_zero, mul_zero, sub_zero]
      · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          thermalSemigroupC_11, h_tr_c, mul_one, gibbsDensityC, mat2_11]
        abel
    · refine ⟨fun t => Real.exp (-(γ / 2) * t), fun t _ => ?_⟩
      have h00_eq : ρ 0 0 = (boltzmannPlus θ : ℂ) := by
        rw [h00]; dsimp [boltzmannPlus]; rw [hz_eq]
      have h11_eq : ρ 1 1 = (boltzmannMinus θ : ℂ) := by
        rw [h11]; dsimp [boltzmannMinus]; rw [hz_eq]
      apply ext_mat2
      · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          thermalSemigroupC_00, h_tr_c, mul_one, gibbsDensityC, mat2_00]
        rw [h00_eq]
        simp only [sub_self, mul_zero, add_zero]
      · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          thermalSemigroupC_01, gibbsDensityC, mat2_01, hω, Complex.ofReal_zero, mul_zero,
          zero_mul, Complex.exp_zero, mul_one, sub_zero]
      · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          thermalSemigroupC_10, gibbsDensityC, mat2_10, hω, Complex.ofReal_zero, mul_zero,
          zero_mul, Complex.exp_zero, mul_one, sub_zero]
      · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          thermalSemigroupC_11, h_tr_c, mul_one, gibbsDensityC, mat2_11]
        rw [h11_eq]
        simp only [sub_self, mul_zero, add_zero]

/-- Rung 4: Larmor equipotential orthogonality and affine geodesic characterization. -/
theorem larmor_equipotential_orthogonality_and_affine_geodesic_iff
    {γ : ℝ} (hγ : 0 < γ) (ω θ : ℝ) {ρ : Mat2C}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (hb : blochNormSq ρ < 1) :
    Matrix.trace ((-(Complex.I * (ω : ℂ) / 2) • ⁅pauliGamma1, ρ⁆) *
      (CFC.log ρ - CFC.log (gibbsDensityC θ))) = 0 ∧
    (∀ t : ℝ, (blochZ (thermalSemigroupC γ ω θ t ρ) - meanSpin θ) * coherenceSq ρ =
      (blochZ ρ - meanSpin θ) * coherenceSq (thermalSemigroupC γ ω θ t ρ)) ∧
    (IsAffineGibbsChord γ ω θ ρ ↔
      (coherenceSq ρ = 0 ∨ (blochZ ρ = meanSpin θ ∧ ω = 0))) :=
  ⟨larmor_equipotential_trace_vanishing ω θ hsa htr hb,
   parabolic_envelope_invariant γ ω θ hsa htr,
   isAffineGibbsChord_iff hγ ω θ hsa htr⟩

/-!
### Section 6: $Y_5 \prec Y_6 \prec Y_7$: Quantum Spohn-Jeffreys Coherence-Lag & Lyapunov Monotonicity
-/

private lemma gibbsDensityC_trace (θ : ℝ) : Matrix.trace (gibbsDensityC θ) = 1 := by
  rw [trace_fin2, gibbsDensityC]
  simp only [mat2_00, mat2_11, Fin.isValue]
  have h_bsum : (boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ) = 1 := by
    exact_mod_cast (boltzmann_sum_and_diff θ).1
  exact h_bsum

private lemma trace_sub_mul_cfc_log_gibbs {ρ : Mat2C}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (θ : ℝ) :
    Matrix.trace ((ρ - gibbsDensityC θ) * CFC.log (gibbsDensityC θ)) =
      ((θ * (blochZ ρ - meanSpin θ) : ℝ) : ℂ) := by
  have hlogG := (cfc_log_gibbsDensityC θ 0 0).1
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, -, -⟩
  rw [hlogG, mul_sub, Matrix.trace_sub]
  have h_tr_ρG : Matrix.trace (ρ * pauliGamma1) = ((blochZ ρ : ℝ) : ℂ) := by
    rw [trace_fin2, mul2_00, mul2_11, pauliGamma1_eq]
    simp only [mat2_00, mat2_01, mat2_10, mat2_11, Fin.isValue, mul_zero, add_zero, mul_neg, mul_one]
    rw [h00, h11]
    push_cast; ring
  have h_tr_GG : Matrix.trace (gibbsDensityC θ * pauliGamma1) = ((meanSpin θ : ℝ) : ℂ) := by
    rw [trace_fin2, mul2_00, mul2_11, pauliGamma1_eq, gibbsDensityC]
    simp only [mat2_00, mat2_01, mat2_10, mat2_11, Fin.isValue, mul_zero, add_zero, mul_neg, mul_one]
    have h_bp : boltzmannPlus θ = (1 + meanSpin θ) / 2 := by
      have h1 := (boltzmann_sum_and_diff θ).1
      have h2 := (boltzmann_sum_and_diff θ).2
      linarith
    have h_bm : boltzmannMinus θ = (1 - meanSpin θ) / 2 := by
      have h1 := (boltzmann_sum_and_diff θ).1
      have h2 := (boltzmann_sum_and_diff θ).2
      linarith
    rw [h_bp, h_bm]
    push_cast; ring
  have h_tr_ρ_sub_G : Matrix.trace (ρ - gibbsDensityC θ) = 0 := by
    rw [Matrix.trace_sub, htr, gibbsDensityC_trace θ, sub_self]
  have h1 : Matrix.trace ((ρ - gibbsDensityC θ) * ((θ : ℂ) • pauliGamma1)) =
      ((θ * (blochZ ρ - meanSpin θ) : ℝ) : ℂ) := by
    rw [Matrix.mul_smul, Matrix.trace_smul, sub_mul, Matrix.trace_sub, h_tr_ρG, h_tr_GG]
    push_cast; ring
  have h2 : Matrix.trace ((ρ - gibbsDensityC θ) * ((cumulantPsi θ : ℂ) • 1)) = 0 := by
    rw [Matrix.mul_smul, mul_one, Matrix.trace_smul, h_tr_ρ_sub_G, smul_zero]
  rw [h1, h2, sub_zero]

private lemma trace_sub_mul_cfc_log {ρ : Mat2C}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (hb : blochNormSq ρ < 1) (θ : ℝ) :
    Matrix.trace ((ρ - gibbsDensityC θ) * (CFC.log ρ - CFC.log (gibbsDensityC θ))) =
      (((blochZ ρ - meanSpin θ) * (artanhRatio (blochRadius ρ) * blochZ ρ - θ) +
        artanhRatio (blochRadius ρ) * coherenceSq ρ : ℝ) : ℂ) := by
  rw [mul_sub, Matrix.trace_sub, trace_sub_mul_cfc_log_gibbs hsa htr θ]
  rw [sub_mul, Matrix.trace_sub]
  rcases spectralProjector_twoSheet_and_cfc_log hsa htr hb with ⟨hP, htrP, h2s, _, hlogρ⟩
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, -⟩
  have h_tr_ρlogρ : Matrix.trace (ρ * CFC.log ρ) = ((negEntropyPhi (blochRadius ρ) : ℝ) : ℂ) := by
    have h_mul : ρ * CFC.log ρ =
        twoSheet (spectralProjector ρ)
          (((1 + blochRadius ρ) / 2) * Real.log ((1 + blochRadius ρ) / 2))
          (((1 - blochRadius ρ) / 2) * Real.log ((1 - blochRadius ρ) / 2)) := by
      calc ρ * CFC.log ρ
        _ = twoSheet (spectralProjector ρ) ((1 + blochRadius ρ) / 2) ((1 - blochRadius ρ) / 2) *
              twoSheet (spectralProjector ρ) (Real.log ((1 + blochRadius ρ) / 2))
                (Real.log ((1 - blochRadius ρ) / 2)) := by rw [h2s, hlogρ]
        _ = _ := twoSheet_mul (spectralProjector ρ) hP.isIdempotentElem.eq _ _ _ _
    rw [h_mul, trace_twoSheet_unitTrace htrP]
    rfl
  rw [h_tr_ρlogρ]
  have h_tr_Glogρ : Matrix.trace (gibbsDensityC θ * CFC.log ρ) =
      (boltzmannPlus θ : ℂ) * (CFC.log ρ 0 0) + (boltzmannMinus θ : ℂ) * (CFC.log ρ 1 1) := by
    rw [trace_fin2, mul2_00, mul2_11, gibbsDensityC]
    simp only [mat2_00, mat2_01, mat2_10, mat2_11, Fin.isValue, zero_mul, add_zero, zero_add]
  rw [h_tr_Glogρ, hlogρ]
  have hP00_11 : (spectralProjector ρ) 1 1 = 1 - (spectralProjector ρ) 0 0 := by
    have htr_p := htrP
    rw [trace_fin2] at htr_p
    linear_combination htr_p
  set r := blochRadius ρ
  set a := Real.log ((1 + r) / 2)
  set b := Real.log ((1 - r) / 2)
  have h_two00 : (twoSheet (spectralProjector ρ) a b) 0 0 =
      (a : ℂ) * (spectralProjector ρ 0 0) + (b : ℂ) * (1 - (spectralProjector ρ 0 0)) := by
    dsimp [twoSheet]
    simp only [Matrix.one_apply, Fin.isValue, ↓reduceIte]
  have h_two11 : (twoSheet (spectralProjector ρ) a b) 1 1 =
      (a : ℂ) * (1 - (spectralProjector ρ 0 0)) + (b : ℂ) * (spectralProjector ρ 0 0) := by
    dsimp [twoSheet]
    simp only [Matrix.one_apply, Fin.isValue, ↓reduceIte]
    rw [hP00_11]
    ring
  by_cases hr0 : r = 0
  · have hr : blochRadius ρ = 0 := hr0
    have hbn0 : blochNormSq ρ = 0 := by
      rw [← blochRadius_sq ρ, hr]; ring
    have hc0 : coherenceSq ρ = 0 ∧ blochZ ρ = 0 := by
      dsimp [blochNormSq, coherenceSq] at hbn0
      constructor
      · dsimp [coherenceSq]; nlinarith [sq_nonneg (blochZ ρ), Complex.normSq_nonneg (ρ 0 1)]
      · nlinarith [sq_nonneg (blochZ ρ), Complex.normSq_nonneg (ρ 0 1)]
    have hP_def : spectralProjector ρ = mat2 1 0 0 0 := by
      simp [spectralProjector, hr]
    have hP00 : spectralProjector ρ 0 0 = 1 := by rw [hP_def, mat2_00]
    have h_log_half : Real.log (1 / 2) = -Real.log 2 := by
      have : (1 : ℝ) / 2 = 2⁻¹ := by norm_num
      rw [this, Real.log_inv]
    have ha : a = -Real.log 2 := by
      dsimp [a, r]; rw [hr, add_zero, h_log_half]
    have hb_eq : b = -Real.log 2 := by
      dsimp [b, r]; rw [hr, sub_zero, h_log_half]
    rw [h_two00, h_two11, hP00, ha, hb_eq]
    dsimp [negEntropyPhi, r]
    rw [hr, add_zero, sub_zero, h_log_half]
    have h_bp : (boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ) = 1 := by
      exact_mod_cast (boltzmann_sum_and_diff θ).1
    have h_c0 : coherenceSq ρ = 0 := hc0.1
    have h_z0 : blochZ ρ = 0 := hc0.2
    rw [h_c0, h_z0]
    push_cast
    linear_combination (Real.log 2 : ℂ) * h_bp
  · have hr_pos : 0 < r := lt_of_le_of_ne (blochRadius_nonneg ρ) (Ne.symm hr0)
    have hr_lt : r < 1 := blochRadius_lt_one hb
    have hP_def : spectralProjector ρ = r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Mat2C)) := by
      dsimp [spectralProjector, r]
      split_ifs with h0
      · exact (hr0 h0).elim
      · rfl
    have hP00 : spectralProjector ρ 0 0 = (((1 + r⁻¹ * blochZ ρ) / 2 : ℝ) : ℂ) := by
      rw [hP_def]
      simp only [Matrix.smul_apply, Complex.real_smul, Matrix.sub_apply, Matrix.one_apply,
        Fin.isValue, ↓reduceIte, h00]
      push_cast
      have hr_inv : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)
      field_simp [hr_inv]
      ring
    have h_ab_diff : a - b = 2 * canonicalTheta r := by
      dsimp [a, b, canonicalTheta]
      have h1 : 0 < (1 + r) / 2 := by linarith
      have h2 : 0 < (1 - r) / 2 := by linarith
      rw [← Real.log_div (ne_of_gt h1) (ne_of_gt h2)]
      have h2_ne : (1 - r) / 2 ≠ 0 := ne_of_gt h2
      have h_div : ((1 + r) / 2) / ((1 - r) / 2) = (1 + r) / (1 - r) := by
        field_simp [h2_ne]
      rw [h_div]
      ring
    have h_art : artanhRatio r * r = canonicalTheta r := by
      dsimp [artanhRatio, r]
      split_ifs with h0
      · exact (hr0 h0).elim
      · exact div_mul_cancel₀ (canonicalTheta r) hr0
    have h_bp : boltzmannPlus θ = (1 + meanSpin θ) / 2 := by
      have h1 := (boltzmann_sum_and_diff θ).1
      have h2 := (boltzmann_sum_and_diff θ).2
      linarith
    have h_bm : boltzmannMinus θ = (1 - meanSpin θ) / 2 := by
      have h1 := (boltzmann_sum_and_diff θ).1
      have h2 := (boltzmann_sum_and_diff θ).2
      linarith
    have h_phi_eq : negEntropyPhi r = (a + b) / 2 + (r / 2) * (a - b) := by
      dsimp [negEntropyPhi, a, b]
      ring
    have h_two00_val : (twoSheet (spectralProjector ρ) a b) 0 0 =
        (((a + b) / 2 + canonicalTheta r * (r⁻¹ * blochZ ρ) : ℝ) : ℂ) := by
      rw [h_two00, hP00]
      push_cast
      have h_ab : (a : ℂ) = (b : ℂ) + 2 * (canonicalTheta r : ℂ) := by
        have h := congrArg (fun x : ℝ => (x : ℂ)) h_ab_diff
        push_cast at h
        linear_combination h
      rw [h_ab]
      ring
    have h_two11_val : (twoSheet (spectralProjector ρ) a b) 1 1 =
        (((a + b) / 2 - canonicalTheta r * (r⁻¹ * blochZ ρ) : ℝ) : ℂ) := by
      rw [h_two11, hP00]
      push_cast
      have h_ab : (a : ℂ) = (b : ℂ) + 2 * (canonicalTheta r : ℂ) := by
        have h := congrArg (fun x : ℝ => (x : ℂ)) h_ab_diff
        push_cast at h
        linear_combination h
      rw [h_ab]
      ring
    have h_norm_sq : r ^ 2 = (blochZ ρ) ^ 2 + coherenceSq ρ := by
      dsimp [r, blochRadius]
      rw [Real.sq_sqrt (blochNormSq_nonneg ρ)]
      dsimp [blochNormSq]
    have hr_inv_r : r * r⁻¹ = 1 := by
      exact mul_inv_cancel₀ (ne_of_gt hr_pos)
    rw [h_two00_val, h_two11_val, h_phi_eq]
    have h_bp_c := congrArg (fun x : ℝ => (x : ℂ)) h_bp
    have h_bm_c := congrArg (fun x : ℝ => (x : ℂ)) h_bm
    rw [h_bp_c, h_bm_c]
    have h_alg : (a + b) / 2 + r / 2 * (a - b) -
        ((1 + meanSpin θ) / 2 * ((a + b) / 2 + canonicalTheta r * (r⁻¹ * blochZ ρ)) +
         (1 - meanSpin θ) / 2 * ((a + b) / 2 - canonicalTheta r * (r⁻¹ * blochZ ρ))) -
        θ * (blochZ ρ - meanSpin θ) =
        (blochZ ρ - meanSpin θ) * (artanhRatio r * blochZ ρ - θ) + artanhRatio r * coherenceSq ρ := by
      linear_combination
        (r / 2) * h_ab_diff -
        (r - meanSpin θ * r⁻¹ * blochZ ρ) * h_art +
        (artanhRatio r) * h_norm_sq -
        (meanSpin θ * artanhRatio r * blochZ ρ) * hr_inv_r
    have h_alg_c := congrArg (fun x : ℝ => (x : ℂ)) h_alg
    push_cast at h_alg_c ⊢
    exact h_alg_c

lemma umegakiJeffreys_eq_trace_sub_mul_sub (ρ σ : Mat2C) :
    umegakiJeffreys ρ σ = (Matrix.trace ((ρ - σ) * (CFC.log ρ - CFC.log σ))).re := by
  dsimp [umegakiJeffreys, umegakiDiv, umegakiKernel]
  rw [← Complex.add_re, ← Matrix.trace_add]
  congr 2
  calc ρ * (CFC.log ρ - CFC.log σ) + σ * (CFC.log σ - CFC.log ρ)
    _ = ρ * (CFC.log ρ - CFC.log σ) + σ * (-(CFC.log ρ - CFC.log σ)) := by
      congr 1; rw [neg_sub]
    _ = ρ * (CFC.log ρ - CFC.log σ) - σ * (CFC.log ρ - CFC.log σ) := by
      rw [mul_neg, ← sub_eq_add_neg]
    _ = (ρ - σ) * (CFC.log ρ - CFC.log σ) := by
      rw [sub_mul]

/-- Exact evaluation of Umegaki-Jeffreys divergence on the 3D Bloch ball. -/
theorem umegakiJeffreys_eval
    (θ : ℝ) {ρ : Matrix (Fin 2) (Fin 2) ℂ} (hρ : InOpenBlochBall ρ) :
    umegakiJeffreys ρ (gibbsDensityC θ) =
      (Matrix.trace ((ρ - gibbsDensityC θ) * (CFC.log ρ - CFC.log (gibbsDensityC θ)))).re ∧
    (Matrix.trace ((ρ - gibbsDensityC θ) * (CFC.log ρ - CFC.log (gibbsDensityC θ)))).re =
      (blochZ ρ - meanSpin θ) * (artanhRatio (blochRadius ρ) * blochZ ρ - θ) +
        artanhRatio (blochRadius ρ) * coherenceSq ρ := by
  constructor
  · exact umegakiJeffreys_eq_trace_sub_mul_sub ρ (gibbsDensityC θ)
  · have htr := trace_sub_mul_cfc_log hρ.1 hρ.2.1 hρ.2.2 θ
    rw [htr, Complex.ofReal_re]

private lemma thermalLindbladianC_eq_larmor_add_dissipative
    (γ ω θ : ℝ) (ρ : Mat2C) :
    thermalLindbladianC γ ω θ ρ =
      thermalLindbladianC γ 0 θ ρ + (-Complex.I * ((ω / 2 : ℝ) : ℂ)) • ⁅pauliGamma1, ρ⁆ := by
  have ext : True := trivial
  dsimp [thermalLindbladianC, Bracket.bracket]
  rw [pauliGamma1_eq]
  apply ext_mat2
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, mul2_00, mat2_00,
      mat2_01, mat2_10, Fin.isValue]
    push_cast; ring
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, mul2_01, mat2_00,
      mat2_01, mat2_11, Fin.isValue]
    push_cast; ring
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, mul2_10, mat2_00,
      mat2_10, mat2_11, Fin.isValue]
    push_cast; ring
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, mul2_11, mat2_01,
      mat2_10, mat2_11, Fin.isValue]
    push_cast; ring

private lemma thermalLindbladianC_zero_omega_eq
    (γ θ : ℝ) (ρ : Mat2C) (htr : Matrix.trace ρ = 1) :
    thermalLindbladianC γ 0 θ ρ =
      -((γ : ℂ) • (ρ - gibbsDensityC θ)) + ((γ / 2 : ℝ) : ℂ) • mat2 0 (ρ 0 1) (ρ 1 0) 0 := by
  have ext : True := trivial
  dsimp [thermalLindbladianC, gibbsDensityC, ratePlus, rateMinus]
  have htr_p : ρ 1 1 = 1 - ρ 0 0 := by
    have h := htr
    rw [trace_fin2] at h
    linear_combination h
  have h_bp_bm : (boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ) = 1 := by
    exact_mod_cast (boltzmann_sum_and_diff θ).1
  apply ext_mat2
  · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      Complex.real_smul, mat2_00, Fin.isValue]
    rw [htr_p]
    push_cast
    linear_combination -(γ : ℂ) * (ρ 0 0) * h_bp_bm
  · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      Complex.real_smul, mat2_01, Fin.isValue]
    push_cast; ring
  · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      Complex.real_smul, mat2_10, Fin.isValue]
    push_cast; ring
  · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      Complex.real_smul, mat2_11, Fin.isValue]
    rw [htr_p]
    push_cast
    linear_combination (γ : ℂ) * (ρ 0 0 - 1) * h_bp_bm

private lemma trace_offdiag_mul_cfc_log_eq
    (θ : ℝ) {ρ : Mat2C} (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (hb : blochNormSq ρ < 1) :
    Matrix.trace (mat2 0 (ρ 0 1) (ρ 1 0) 0 * (CFC.log ρ - CFC.log (gibbsDensityC θ))) =
      ↑(artanhRatio (blochRadius ρ) * coherenceSq ρ) := by
  have hlogG := (cfc_log_gibbsDensityC θ 0 0).1
  have h_tr_G : Matrix.trace (mat2 0 (ρ 0 1) (ρ 1 0) 0 * CFC.log (gibbsDensityC θ)) = 0 := by
    rw [hlogG, mul_sub, Matrix.trace_sub]
    have hG1 : Matrix.trace (mat2 0 (ρ 0 1) (ρ 1 0) 0 * ((θ : ℂ) • pauliGamma1)) = 0 := by
      rw [Matrix.mul_smul, Matrix.trace_smul, trace_fin2, mul2_00, mul2_11, pauliGamma1_eq]
      simp only [mat2_00, mat2_01, mat2_10, mat2_11, Fin.isValue, zero_mul, mul_zero, add_zero, smul_zero]
    have hG2 : Matrix.trace (mat2 0 (ρ 0 1) (ρ 1 0) 0 * ((cumulantPsi θ : ℂ) • (1 : Mat2C))) = 0 := by
      rw [Matrix.mul_smul, mul_one, Matrix.trace_smul, trace_fin2]
      simp only [mat2_00, mat2_11, add_zero, smul_zero]
    rw [hG1, hG2, sub_self]
  rw [mul_sub, Matrix.trace_sub, h_tr_G, sub_zero]
  have ⟨hP, htrP, h2s, _, hlogρ⟩ := spectralProjector_twoSheet_and_cfc_log hsa htr hb
  rw [hlogρ]
  set r := blochRadius ρ
  set a := Real.log ((1 + r) / 2)
  set b := Real.log ((1 - r) / 2)
  have h_two01 : (twoSheet (spectralProjector ρ) a b) 0 1 = (a - b : ℂ) * (spectralProjector ρ 0 1) := by
    dsimp [twoSheet]
    simp only [Matrix.one_apply, Fin.isValue, zero_ne_one, ↓reduceIte]
    ring
  have h_two10 : (twoSheet (spectralProjector ρ) a b) 1 0 = (a - b : ℂ) * (spectralProjector ρ 1 0) := by
    dsimp [twoSheet]
    simp only [Matrix.one_apply, Fin.isValue, one_ne_zero, ↓reduceIte]
    ring
  have h_tr : Matrix.trace (mat2 0 (ρ 0 1) (ρ 1 0) 0 * twoSheet (spectralProjector ρ) a b) =
      (ρ 0 1) * ((twoSheet (spectralProjector ρ) a b) 1 0) +
      (ρ 1 0) * ((twoSheet (spectralProjector ρ) a b) 0 1) := by
    rw [trace_fin2, mul2_00, mul2_11]
    simp only [mat2_00, mat2_01, mat2_10, mat2_11, Fin.isValue, zero_mul, zero_add]
    ring
  rw [h_tr, h_two01, h_two10]
  have h10 : ρ 1 0 = (ρ 0 1)† := (hermitian_unitTrace_entries hsa htr).2.2.1
  by_cases hr0 : r = 0
  · have hr : blochRadius ρ = 0 := hr0
    have hbn0 : blochNormSq ρ = 0 := by
      rw [← blochRadius_sq ρ, hr]; ring
    have hc0 : coherenceSq ρ = 0 := by
      have hz2 : 0 ≤ blochZ ρ ^ 2 := sq_nonneg (blochZ ρ)
      have hc : 0 ≤ coherenceSq ρ := by
        dsimp [coherenceSq]
        nlinarith [Complex.normSq_nonneg (ρ 0 1)]
      dsimp [blochNormSq] at hbn0
      linarith
    have h01_zero : ρ 0 1 = 0 := by
      dsimp [coherenceSq] at hc0
      have : Complex.normSq (ρ 0 1) = 0 := by linarith
      exact Complex.normSq_eq_zero.mp this
    have h10_zero : ρ 1 0 = 0 := by rw [h10, h01_zero, star_zero]
    rw [h01_zero, h10_zero, hc0]
    push_cast; ring
  · have hr_pos : 0 < r := lt_of_le_of_ne (blochRadius_nonneg ρ) (Ne.symm hr0)
    have hP_def : spectralProjector ρ = r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Mat2C)) := by
      dsimp [spectralProjector, r]
      split_ifs with h0
      · exact (hr0 h0).elim
      · rfl
    have hP01 : spectralProjector ρ 0 1 = (r⁻¹ : ℂ) * (ρ 0 1) := by
      rw [hP_def]
      simp only [Matrix.smul_apply, Complex.real_smul, Matrix.sub_apply, Matrix.one_apply,
        Fin.isValue, zero_ne_one, ↓reduceIte]
      push_cast
      ring
    have hP10 : spectralProjector ρ 1 0 = (r⁻¹ : ℂ) * (ρ 1 0) := by
      rw [hP_def]
      simp only [Matrix.smul_apply, Complex.real_smul, Matrix.sub_apply, Matrix.one_apply,
        Fin.isValue, one_ne_zero, ↓reduceIte]
      push_cast
      ring
    rw [hP01, hP10]
    have h_ab_diff : a - b = 2 * canonicalTheta r := by
      dsimp [a, b, canonicalTheta]
      have h1 : 0 < (1 + r) / 2 := by linarith [blochRadius_lt_one hb]
      have h2 : 0 < (1 - r) / 2 := by linarith [blochRadius_lt_one hb]
      rw [← Real.log_div (ne_of_gt h1) (ne_of_gt h2)]
      have h2_ne : (1 - r) / 2 ≠ 0 := ne_of_gt h2
      have h_div : ((1 + r) / 2) / ((1 - r) / 2) = (1 + r) / (1 - r) := by
        field_simp [h2_ne]
      rw [h_div]
      ring
    have h_art : artanhRatio r * r = canonicalTheta r := by
      dsimp [artanhRatio, r]
      split_ifs with h0
      · exact (hr0 h0).elim
      · exact div_mul_cancel₀ (canonicalTheta r) hr0
    have h_norm : (ρ 0 1) * (ρ 1 0) = ((Complex.normSq (ρ 0 1) : ℝ) : ℂ) := by
      rw [h10]
      exact Complex.mul_conj (ρ 0 1)
    have h_norm' : (ρ 1 0) * (ρ 0 1) = ((Complex.normSq (ρ 0 1) : ℝ) : ℂ) := by
      rw [mul_comm, h_norm]
    have hr_inv : (r : ℂ) * (r⁻¹ : ℂ) = 1 := by
      have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)
      exact mul_inv_cancel₀ this
    have h_coh : coherenceSq ρ = 4 * Complex.normSq (ρ 0 1) := rfl
    have h_ab_c : (a - b : ℂ) = 2 * (r : ℂ) * (artanhRatio r : ℂ) := by
      have h := congrArg (fun x : ℝ => (x : ℂ)) h_ab_diff
      have h' := congrArg (fun x : ℝ => (x : ℂ)) h_art
      push_cast at h h' ⊢
      linear_combination h - 2 * h'
    rw [h_ab_c]
    have h_alg : (ρ 0 1) * (2 * (r : ℂ) * (artanhRatio r : ℂ) * ((r⁻¹ : ℂ) * (ρ 1 0))) +
        (ρ 1 0) * (2 * (r : ℂ) * (artanhRatio r : ℂ) * ((r⁻¹ : ℂ) * (ρ 0 1))) =
        (artanhRatio r : ℂ) * (4 * ((Complex.normSq (ρ 0 1) : ℝ) : ℂ)) := by
      calc (ρ 0 1) * (2 * (r : ℂ) * (artanhRatio r : ℂ) * ((r⁻¹ : ℂ) * (ρ 1 0))) +
          (ρ 1 0) * (2 * (r : ℂ) * (artanhRatio r : ℂ) * ((r⁻¹ : ℂ) * (ρ 0 1)))
        _ = 2 * (artanhRatio r : ℂ) * ((r : ℂ) * (r⁻¹ : ℂ)) * ((ρ 0 1) * (ρ 1 0) + (ρ 1 0) * (ρ 0 1)) := by ring
        _ = 2 * (artanhRatio r : ℂ) * 1 * (((Complex.normSq (ρ 0 1) : ℝ) : ℂ) + ((Complex.normSq (ρ 0 1) : ℝ) : ℂ)) := by rw [hr_inv, h_norm, h_norm']
        _ = (artanhRatio r : ℂ) * (4 * ((Complex.normSq (ρ 0 1) : ℝ) : ℂ)) := by ring
    rw [h_alg]
    push_cast [h_coh]
    ring

lemma thermalLindbladianOp_trace_cfc_log_eq
    (γ ω θ : ℝ) {ρ : Mat2C} (hρ : InOpenBlochBall ρ) :
    (Matrix.trace (thermalLindbladianOp γ ω θ ρ *
      (CFC.log ρ - CFC.log (gibbsDensityC θ)))).re =
    -γ * umegakiJeffreys ρ (gibbsDensityC θ) +
      (γ / 2) * artanhRatio (blochRadius ρ) * coherenceSq ρ := by
  rw [thermalLindbladianOp_eq_thermalLindbladianC]
  have h_dec := thermalLindbladianC_eq_larmor_add_dissipative γ ω θ ρ
  rw [h_dec]
  set Δ := CFC.log ρ - CFC.log (gibbsDensityC θ)
  have h_larmor : Matrix.trace (((-Complex.I * ((ω / 2 : ℝ) : ℂ)) • ⁅pauliGamma1, ρ⁆) * Δ) = 0 := by
    have h_van := larmor_equipotential_trace_vanishing ω θ hρ.1 hρ.2.1 hρ.2.2
    have h_eq : (-Complex.I * ((ω / 2 : ℝ) : ℂ)) = (-(Complex.I * (ω : ℂ) / 2)) := by push_cast; ring
    rw [h_eq]
    exact h_van
  rw [Matrix.add_mul, Matrix.trace_add, h_larmor, add_zero]
  have h_zero := thermalLindbladianC_zero_omega_eq γ θ ρ hρ.2.1
  rw [h_zero]
  set M_off := mat2 0 (ρ 0 1) (ρ 1 0) 0
  have h_split : (-((γ : ℂ) • (ρ - gibbsDensityC θ)) + ((γ / 2 : ℝ) : ℂ) • M_off) * Δ =
      -((γ : ℂ) • ((ρ - gibbsDensityC θ) * Δ)) + ((γ / 2 : ℝ) : ℂ) • (M_off * Δ) := by
    rw [Matrix.add_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.smul_mul]
  rw [h_split, Matrix.trace_add, Matrix.trace_neg, Matrix.trace_smul, Matrix.trace_smul,
    smul_eq_mul, smul_eq_mul, Complex.add_re]
  have h_jeff := (umegakiJeffreys_eval θ hρ).1
  have h_off : Matrix.trace (M_off * Δ) = ↑(artanhRatio (blochRadius ρ) * coherenceSq ρ) :=
    trace_offdiag_mul_cfc_log_eq θ hρ.1 hρ.2.1 hρ.2.2
  have h_re1 : (-((γ : ℂ) * Matrix.trace ((ρ - gibbsDensityC θ) * Δ))).re =
      -γ * (Matrix.trace ((ρ - gibbsDensityC θ) * Δ)).re := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h_re2 : (((γ / 2 : ℝ) : ℂ) * Matrix.trace (M_off * Δ)).re =
      (γ / 2) * (Matrix.trace (M_off * Δ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h_re1, h_re2, h_off, Complex.ofReal_re, ← h_jeff]
  ring

private lemma theta_mul_meanSpin_nonneg (θ : ℝ) :
    0 ≤ θ * meanSpin θ ∧ (θ * meanSpin θ = 0 ↔ θ = 0) := by
  dsimp [meanSpin]
  have hZ := partitionZ_pos θ
  rcases lt_trichotomy θ 0 with hneg | rfl | hpos
  · have hexp : Real.exp θ < Real.exp (-θ) := Real.exp_lt_exp.mpr (by linarith [hneg])
    have hdiff : Real.exp θ - Real.exp (-θ) < 0 := sub_neg.mpr hexp
    have hdiv : (Real.exp θ - Real.exp (-θ)) / partitionZ θ < 0 := div_neg_of_neg_of_pos hdiff hZ
    have hprod : 0 < θ * ((Real.exp θ - Real.exp (-θ)) / partitionZ θ) :=
      mul_pos_of_neg_of_neg hneg hdiv
    refine ⟨le_of_lt hprod, ⟨fun h => False.elim (ne_of_gt hprod h), fun h => False.elim (ne_of_lt hneg h)⟩⟩
  · simp
  · have hexp : Real.exp (-θ) < Real.exp θ := Real.exp_lt_exp.mpr (by linarith [hpos])
    have hdiff : 0 < Real.exp θ - Real.exp (-θ) := sub_pos.mpr hexp
    have hdiv : 0 < (Real.exp θ - Real.exp (-θ)) / partitionZ θ := div_pos hdiff hZ
    have hprod : 0 < θ * ((Real.exp θ - Real.exp (-θ)) / partitionZ θ) :=
      mul_pos hpos hdiv
    refine ⟨le_of_lt hprod, ⟨fun h => False.elim (ne_of_gt hprod h), fun h => False.elim (ne_of_gt hpos h)⟩⟩

private lemma blochZ_coherenceSq_eq_gibbsDensityC {ρ : Mat2C}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (θ : ℝ)
    (hz : blochZ ρ = meanSpin θ) (hc : coherenceSq ρ = 0) :
    ρ = gibbsDensityC θ := by
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, -⟩
  have hc01 : ρ 0 1 = 0 := by
    dsimp [coherenceSq] at hc
    have : Complex.normSq (ρ 0 1) = 0 := by linarith
    exact Complex.normSq_eq_zero.mp this
  have hc10 : ρ 1 0 = 0 := by rw [h10, hc01, star_zero]
  apply ext_mat2
  · rw [h00, hz]
    rfl
  · rw [hc01]
    rfl
  · rw [hc10]
    rfl
  · rw [h11, hz]
    rfl

private lemma negEntropyPhi_abs (x : ℝ) : negEntropyPhi |x| = negEntropyPhi x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, negEntropyPhi_even]

private lemma bregmanPhi_meanSpin_eq (η θ : ℝ) :
    negEntropyPhi η + cumulantPsi θ - θ * η = bregmanPhi η (meanSpin θ) := by
  dsimp [bregmanPhi]
  have h1 := dually_flat_legendre_reciprocity_and_metric_inversion.1 θ
  have h2 := dually_flat_legendre_reciprocity_and_metric_inversion.2.2.1 θ
  rw [h1]
  linear_combination h2

/-- **Node $Y_6$ Theorem**: Unconditional exact 3D Quantum Spohn-Jeffreys coherence-lag law. -/
theorem quantum_spohn_jeffreys_coherence_lag
    {γ ω θ : ℝ} (hγ : 0 < γ) {ρ₀ : Matrix (Fin 2) (Fin 2) ℂ} (hρ₀ : InOpenBlochBall ρ₀)
    (t : ℝ) (ht : 0 ≤ t) :
    let ρ_t := thermalSemigroupC γ ω θ t ρ₀
    HasDerivAt (fun s => umegakiDiv (thermalSemigroupC γ ω θ s ρ₀) (gibbsDensityC θ))
      (-γ * umegakiJeffreys ρ_t (gibbsDensityC θ) +
        (γ / 2) * artanhRatio (blochRadius ρ_t) * coherenceSq ρ_t) t ∧
    (-γ * umegakiJeffreys ρ_t (gibbsDensityC θ) +
        (γ / 2) * artanhRatio (blochRadius ρ_t) * coherenceSq ρ_t) =
      (Matrix.trace (thermalLindbladianOp γ ω θ ρ_t *
        (CFC.log ρ_t - CFC.log (gibbsDensityC θ)))).re := by
  have _ := hγ
  have _ := ht
  intro ρ_t
  have hρ_t : InOpenBlochBall ρ_t :=
    (rung2_forward_positivity_monoid_iff γ ω θ hγ t).mpr ht ρ₀ hρ₀
  have h_trace_eq : (-γ * umegakiJeffreys ρ_t (gibbsDensityC θ) +
      (γ / 2) * artanhRatio (blochRadius ρ_t) * coherenceSq ρ_t) =
      (Matrix.trace (thermalLindbladianOp γ ω θ ρ_t *
        (CFC.log ρ_t - CFC.log (gibbsDensityC θ)))).re :=
    (thermalLindbladianOp_trace_cfc_log_eq γ ω θ hρ_t).symm
  refine ⟨?_, h_trace_eq⟩
  set f : ℝ → ℝ := fun s => (etaTraj γ θ (blochZ ρ₀) s) ^ 2 + Real.exp (-γ * s) * coherenceSq ρ₀
  have h_bloch_formula : ∀ s : ℝ, blochNormSq (thermalSemigroupC γ ω θ s ρ₀) = f s := by
    intro s
    rcases thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ s hρ₀.1 hρ₀.2.1 with ⟨_, _, h_bz_s, h_coh_s⟩
    rw [blochNormSq, h_bz_s, h_coh_s]
  have h_radius_t_fun : ∀ s : ℝ, blochRadius (thermalSemigroupC γ ω θ s ρ₀) = Real.sqrt (f s) := by
    intro s
    rw [blochRadius, h_bloch_formula s]
  have h_cont_exp : Continuous (fun s : ℝ => Real.exp (-γ * s)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have h_cont_eta : Continuous (fun s : ℝ => etaTraj γ θ (blochZ ρ₀) s) :=
    continuous_const.add (h_cont_exp.mul continuous_const)
  have h_cont_fn : Continuous f :=
    (h_cont_eta.pow 2).add (h_cont_exp.mul continuous_const)
  have hf_lt1 : f t < 1 := by
    rw [← h_bloch_formula t]
    exact hρ_t.2.2
  have h_ev : (fun s => umegakiDiv (thermalSemigroupC γ ω θ s ρ₀) (gibbsDensityC θ)) =ᶠ[𝓝 t]
      (fun s => negEntropyPhi (Real.sqrt (f s)) + cumulantPsi θ - θ * etaTraj γ θ (blochZ ρ₀) s) := by
    have h_lt_ev : ∀ᶠ s in 𝓝 t, f s < 1 :=
      h_cont_fn.continuousAt.eventually_lt continuousAt_const hf_lt1
    filter_upwards [h_lt_ev] with s hs_lt
    rcases thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ s hρ₀.1 hρ₀.2.1 with ⟨hsa_s, htr_s, h_bz_s, _⟩
    have hb_s : blochNormSq (thermalSemigroupC γ ω θ s ρ₀) < 1 := by rwa [h_bloch_formula s]
    have h_tr_s := umegakiKernel_trace_formula hsa_s htr_s hb_s θ
    change (Matrix.trace (umegakiKernel (thermalSemigroupC γ ω θ s ρ₀) (gibbsDensityC θ))).re = _
    rw [h_tr_s, Complex.ofReal_re, h_bz_s, h_radius_t_fun s]
  have hd_eta : HasDerivAt (etaTraj γ θ (blochZ ρ₀))
      (-γ * (etaTraj γ θ (blochZ ρ₀) t - meanSpin θ)) t := by
    have hd_lin : HasDerivAt (fun s : ℝ => -γ * s) (-γ) t := by
      simpa using (hasDerivAt_id t).const_mul (-γ)
    have h_exp : HasDerivAt (fun s : ℝ => Real.exp (-γ * s)) (Real.exp (-γ * t) * (-γ)) t :=
      (Real.hasDerivAt_exp (-γ * t)).comp t hd_lin
    have h_mul := (hasDerivAt_const t (meanSpin θ)).fun_add
      (h_exp.mul_const (blochZ ρ₀ - meanSpin θ))
    unfold etaTraj
    exact h_mul.congr_deriv (by ring_nf)
  have hd_exp_c : HasDerivAt (fun s : ℝ => Real.exp (-γ * s) * coherenceSq ρ₀)
      (-γ * coherenceSq ρ_t) t := by
    have hd_lin : HasDerivAt (fun s : ℝ => -γ * s) (-γ) t := by
      simpa using (hasDerivAt_id t).const_mul (-γ)
    have h_exp : HasDerivAt (fun s : ℝ => Real.exp (-γ * s)) (Real.exp (-γ * t) * (-γ)) t :=
      (Real.hasDerivAt_exp (-γ * t)).comp t hd_lin
    have hc_t : coherenceSq ρ_t = Real.exp (-γ * t) * coherenceSq ρ₀ :=
      (thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hρ₀.1 hρ₀.2.1).2.2.2
    exact (h_exp.mul_const (coherenceSq ρ₀)).congr_deriv (by rw [hc_t]; ring_nf)
  have hd_f : HasDerivAt f
      (-γ * ((blochRadius ρ_t) ^ 2 + (blochZ ρ_t) ^ 2 - 2 * blochZ ρ_t * meanSpin θ)) t := by
    have h_sq_eta := hd_eta.pow 2
    have hd_sum := h_sq_eta.fun_add hd_exp_c
    have h_bz_t : etaTraj γ θ (blochZ ρ₀) t = blochZ ρ_t :=
      (thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hρ₀.1 hρ₀.2.1).2.2.1.symm
    have hc_r : coherenceSq ρ_t = (blochRadius ρ_t) ^ 2 - (blochZ ρ_t) ^ 2 := by
      rw [blochRadius_sq]; dsimp [blochNormSq]; ring_nf
    exact hd_sum.congr_deriv (by rw [h_bz_t, hc_r]; ring_nf)
  by_cases hr_pos : 0 < blochRadius ρ_t
  · have hf_pos : 0 < f t := by
      rw [← h_bloch_formula t, ← blochRadius_sq]
      exact sq_pos_of_pos hr_pos
    have hd_r : HasDerivAt (fun s => Real.sqrt (f s))
        ((-γ * ((blochRadius ρ_t) ^ 2 + (blochZ ρ_t) ^ 2 - 2 * blochZ ρ_t * meanSpin θ)) /
          (2 * blochRadius ρ_t)) t := by
      have h_sqrt := HasDerivAt.sqrt hd_f (ne_of_gt hf_pos)
      have h_sq_r : Real.sqrt (f t) = blochRadius ρ_t := (h_radius_t_fun t).symm
      simpa only [h_sq_r] using h_sqrt
    have hr_lo : -1 < blochRadius ρ_t :=
      lt_of_lt_of_le (by norm_num) (blochRadius_nonneg ρ_t)
    have hr_hi : blochRadius ρ_t < 1 := blochRadius_lt_one hρ_t.2.2
    have hd_phi_base : HasDerivAt negEntropyPhi
        (canonicalTheta (blochRadius ρ_t)) (Real.sqrt (f t)) := by
      rw [← h_radius_t_fun t]
      exact dually_flat_legendre_reciprocity_and_metric_inversion.2.2.2.1
        (blochRadius ρ_t) hr_lo hr_hi
    have hd_phi_r := hd_phi_base.comp t hd_r
    have hd_lin : HasDerivAt (fun s => -θ * etaTraj γ θ (blochZ ρ₀) s)
        (-θ * (-γ * (blochZ ρ_t - meanSpin θ))) t := by
      have h_bz_t : etaTraj γ θ (blochZ ρ₀) t = blochZ ρ_t :=
        (thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hρ₀.1 hρ₀.2.1).2.2.1.symm
      have hd_c := hd_eta.const_mul (-θ)
      rw [h_bz_t] at hd_c
      exact hd_c
    have hd_comb : HasDerivAt (fun s => negEntropyPhi (Real.sqrt (f s)) + cumulantPsi θ - θ * etaTraj γ θ (blochZ ρ₀) s)
        (canonicalTheta (blochRadius ρ_t) *
          ((-γ * ((blochRadius ρ_t) ^ 2 + (blochZ ρ_t) ^ 2 - 2 * blochZ ρ_t * meanSpin θ)) /
            (2 * blochRadius ρ_t)) +
          -θ * (-γ * (blochZ ρ_t - meanSpin θ))) t := by
      have h_cst : HasDerivAt (fun _ : ℝ => cumulantPsi θ) 0 t := hasDerivAt_const t (cumulantPsi θ)
      have h1 := hd_phi_r.add h_cst
      have h2 := h1.add hd_lin
      have h_fn : (fun s => negEntropyPhi (Real.sqrt (f s)) + cumulantPsi θ - θ * etaTraj γ θ (blochZ ρ₀) s) =
          fun s => (negEntropyPhi (Real.sqrt (f s)) + cumulantPsi θ) + (-θ * etaTraj γ θ (blochZ ρ₀) s) := by
        ext s; ring
      rw [h_fn]
      exact h2.congr_deriv (by ring)
    have hd_eval : (canonicalTheta (blochRadius ρ_t) *
          ((-γ * ((blochRadius ρ_t) ^ 2 + (blochZ ρ_t) ^ 2 - 2 * blochZ ρ_t * meanSpin θ)) /
            (2 * blochRadius ρ_t)) +
          -θ * (-γ * (blochZ ρ_t - meanSpin θ))) =
        -γ * umegakiJeffreys ρ_t (gibbsDensityC θ) +
          (γ / 2) * artanhRatio (blochRadius ρ_t) * coherenceSq ρ_t := by
      rw [(umegakiJeffreys_eval θ hρ_t).1, (umegakiJeffreys_eval θ hρ_t).2]
      have hr_ne : blochRadius ρ_t ≠ 0 := ne_of_gt hr_pos
      have h_art : canonicalTheta (blochRadius ρ_t) = artanhRatio (blochRadius ρ_t) * blochRadius ρ_t := by
        dsimp [artanhRatio]; split_ifs <;> [contradiction; rw [div_mul_cancel₀ _ hr_ne]]
      have hc_r : coherenceSq ρ_t = (blochRadius ρ_t) ^ 2 - (blochZ ρ_t) ^ 2 := by
        rw [blochRadius_sq]; dsimp [blochNormSq]; ring_nf
      rw [h_art, hc_r]
      field_simp [hr_ne]
      ring
    rw [hd_eval] at hd_comb
    exact hd_comb.congr_of_eventuallyEq h_ev
  · have hr_zero : blochRadius ρ_t = 0 :=
      le_antisymm (not_lt.mp hr_pos) (blochRadius_nonneg ρ_t)
    have h_sq0 : blochNormSq ρ_t = 0 := by
      rw [← blochRadius_sq, hr_zero, sq, mul_zero]
    dsimp [blochNormSq] at h_sq0
    have hz_0 : blochZ ρ_t = 0 := by
      have h1 : (blochZ ρ_t) ^ 2 ≤ 0 := by
        linarith [coherenceSq_nonneg ρ_t]
      have h2 : 0 ≤ (blochZ ρ_t) ^ 2 := sq_nonneg _
      exact sq_eq_zero_iff.mp (le_antisymm h1 h2)
    have hc_0 : coherenceSq ρ_t = 0 := by
      linarith [sq_nonneg (blochZ ρ_t), coherenceSq_nonneg ρ_t]
    have hc_t : coherenceSq ρ_t = Real.exp (-γ * t) * coherenceSq ρ₀ :=
      (thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hρ₀.1 hρ₀.2.1).2.2.2
    have hc0_0 : coherenceSq ρ₀ = 0 := by
      have h_exp_pos : 0 < Real.exp (-γ * t) := Real.exp_pos _
      rw [hc_0] at hc_t
      exact (mul_eq_zero.mp hc_t.symm).resolve_left (ne_of_gt h_exp_pos)
    have h_ev_c0 : (fun s => negEntropyPhi (Real.sqrt (f s)) + cumulantPsi θ - θ * etaTraj γ θ (blochZ ρ₀) s) =ᶠ[𝓝 t]
        (fun s => bregmanPhi (etaTraj γ θ (blochZ ρ₀) s) (meanSpin θ)) := by
      filter_upwards with s
      have h_fs : f s = (etaTraj γ θ (blochZ ρ₀) s) ^ 2 := by
        dsimp [f]; rw [hc0_0, mul_zero, add_zero]
      rw [h_fs, Real.sqrt_sq_eq_abs, negEntropyPhi_abs, bregmanPhi_meanSpin_eq]
    have hd_breg : HasDerivAt (fun s => bregmanPhi (etaTraj γ θ (blochZ ρ₀) s) (meanSpin θ))
        (-γ * (bregmanPhi (blochZ ρ_t) (meanSpin θ) + bregmanPhi (meanSpin θ) (blochZ ρ_t))) t := by
      rcases meanSpin_mem_Ioo θ with ⟨heq_lo, heq_hi⟩
      rcases dually_flat_legendre_reciprocity_and_metric_inversion with
        ⟨h_th_mean, _, _, h_deriv_phi, _, _⟩
      rcases bregman_umegaki_positivity_and_pythagorean_theorem with
        ⟨_, _, h_jeffreys, _⟩
      have h_bz_t : etaTraj γ θ (blochZ ρ₀) t = blochZ ρ_t :=
        (thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hρ₀.1 hρ₀.2.1).2.2.1.symm
      have h_in_Ioo : -1 < etaTraj γ θ (blochZ ρ₀) t ∧ etaTraj γ θ (blochZ ρ₀) t < 1 := by
        rw [h_bz_t, hz_0]; norm_num
      have hd_breg_at : ∀ u : ℝ, -1 < u → u < 1 →
          HasDerivAt (fun v => bregmanPhi v (meanSpin θ)) (canonicalTheta u - θ) u := by
        intro u hu_lo hu_hi
        have hd_phi := h_deriv_phi u hu_lo hu_hi
        have hd_sub1 := hd_phi.fun_sub (hasDerivAt_const u (negEntropyPhi (meanSpin θ)))
        have hd_lin2 : HasDerivAt (fun v : ℝ => canonicalTheta (meanSpin θ) * (v - meanSpin θ))
            (canonicalTheta (meanSpin θ)) u :=
          (((hasDerivAt_id u).fun_sub (hasDerivAt_const u (meanSpin θ))).const_mul
            (canonicalTheta (meanSpin θ))).congr_deriv (by ring)
        have hd_tot := hd_sub1.fun_sub hd_lin2
        have h_th_eq : canonicalTheta (meanSpin θ) = θ := h_th_mean θ
        unfold bregmanPhi
        simp only [h_th_eq] at hd_tot ⊢
        exact hd_tot.congr_deriv (by ring)
      have hd_breg_u := hd_breg_at (etaTraj γ θ (blochZ ρ₀) t) h_in_Ioo.1 h_in_Ioo.2
      have hd_comp := hd_breg_u.comp t hd_eta
      have h_spohn_eq : (canonicalTheta (etaTraj γ θ (blochZ ρ₀) t) - θ) *
          (-γ * (etaTraj γ θ (blochZ ρ₀) t - meanSpin θ)) =
          -γ * (bregmanPhi (blochZ ρ_t) (meanSpin θ) + bregmanPhi (meanSpin θ) (blochZ ρ_t)) := by
        rw [h_bz_t]
        have hj := h_jeffreys (blochZ ρ_t) (meanSpin θ)
        have h_th_eq : canonicalTheta (meanSpin θ) = θ := h_th_mean θ
        rw [h_th_eq] at hj
        rw [hj]; ring
      rwa [h_spohn_eq] at hd_comp
    have hd_eval : -γ * (bregmanPhi (blochZ ρ_t) (meanSpin θ) + bregmanPhi (meanSpin θ) (blochZ ρ_t)) =
        -γ * umegakiJeffreys ρ_t (gibbsDensityC θ) +
          (γ / 2) * artanhRatio (blochRadius ρ_t) * coherenceSq ρ_t := by
      rcases bregman_umegaki_positivity_and_pythagorean_theorem with ⟨_, _, h_jeffreys, _⟩
      have h_th_eq := dually_flat_legendre_reciprocity_and_metric_inversion.1 θ
      have hj := h_jeffreys 0 (meanSpin θ)
      have h_cth0 : canonicalTheta 0 = 0 := by
        dsimp [canonicalTheta]; simp
      rw [h_th_eq, h_cth0] at hj
      rw [(umegakiJeffreys_eval θ hρ_t).1, (umegakiJeffreys_eval θ hρ_t).2, hz_0, hc_0, hr_zero, hj]
      dsimp [artanhRatio]
      ring
    rw [hd_eval] at hd_breg
    have hd_ev_fn := hd_breg.congr_of_eventuallyEq h_ev_c0
    exact hd_ev_fn.congr_of_eventuallyEq h_ev

/-- Factor-of-2 coherent refutation witness at $t = 0$. -/
theorem factor_two_coherent_spohn_refutation_witness
    (γ r₀ : ℝ) (hγ : 0 < γ) (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < 1) :
    let ρ₀ : Matrix (Fin 2) (Fin 2) ℂ :=
      (1 / 2 : ℂ) • (1 + (r₀ : ℂ) • pauliSigmaX)
    let entProdRate :=
      -γ * umegakiJeffreys ρ₀ (gibbsDensityC 0) +
        (γ / 2) * artanhRatio (blochRadius ρ₀) * coherenceSq ρ₀
    let classicalSpohn := -γ * umegakiJeffreys ρ₀ (gibbsDensityC 0)
    InOpenBlochBall ρ₀ ∧
    entProdRate = -(γ / 2) * r₀ * canonicalTheta r₀ ∧
    entProdRate < 0 ∧
    classicalSpohn = 2 * entProdRate ∧
    classicalSpohn ≠ entProdRate := by
  intro ρ₀ entProdRate classicalSpohn
  have hsa : IsSelfAdjoint ρ₀ := by
    change star ρ₀ = ρ₀
    dsimp [ρ₀]
    apply ext_mat2
    · simp only [Matrix.star_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_00, smul_eq_mul]
      norm_num
    · simp only [Matrix.star_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_01, mat2_10, smul_eq_mul]
      norm_num
    · simp only [Matrix.star_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_01, mat2_10, smul_eq_mul]
      norm_num
    · simp only [Matrix.star_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_11, smul_eq_mul]
      norm_num
  have htr : Matrix.trace ρ₀ = 1 := by
    dsimp [ρ₀]
    rw [trace_fin2]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, pauliSigmaX_eq, mat2_00, mat2_11,
      smul_zero, add_zero, smul_eq_mul]
    norm_num
  have hz : blochZ ρ₀ = 0 := by
    dsimp [blochZ, ρ₀]
    simp [pauliSigmaX_eq]
  have h_entry : ρ₀ 0 1 = ((r₀ / 2 : ℝ) : ℂ) := by
    dsimp [ρ₀]
    simp only [Matrix.one_apply, pauliSigmaX_eq, mat2_01]
    norm_num
    ring
  have hc : coherenceSq ρ₀ = r₀ ^ 2 := by
    dsimp [coherenceSq]
    rw [h_entry, Complex.normSq_ofReal]
    ring
  have hnorm : blochNormSq ρ₀ = r₀ ^ 2 := by
    rw [blochNormSq, hz, hc, zero_pow (by norm_num), zero_add]
  have hb : blochNormSq ρ₀ < 1 := by
    rw [hnorm]
    nlinarith [hr₀_pos, hr₀_lt]
  have hρ₀_ball : InOpenBlochBall ρ₀ := ⟨hsa, htr, hb⟩
  have hr_eval : blochRadius ρ₀ = r₀ := by
    dsimp [blochRadius]
    rw [hnorm, Real.sqrt_sq (le_of_lt hr₀_pos)]
  have h_mean0 : meanSpin 0 = 0 := by
    dsimp [meanSpin, partitionZ]; ring
  have h_jeff : umegakiJeffreys ρ₀ (gibbsDensityC 0) =
      (blochZ ρ₀ - meanSpin 0) * (artanhRatio (blochRadius ρ₀) * blochZ ρ₀ - 0) +
        artanhRatio (blochRadius ρ₀) * coherenceSq ρ₀ := by
    rw [(umegakiJeffreys_eval 0 hρ₀_ball).1, (umegakiJeffreys_eval 0 hρ₀_ball).2]
  rw [hz, hc, hr_eval, h_mean0] at h_jeff
  have hr_ne : r₀ ≠ 0 := ne_of_gt hr₀_pos
  have h_art : artanhRatio r₀ = canonicalTheta r₀ / r₀ := by
    dsimp [artanhRatio]; split_ifs <;> [contradiction; rfl]
  have h_jeff_eval : umegakiJeffreys ρ₀ (gibbsDensityC 0) = r₀ * canonicalTheta r₀ := by
    calc umegakiJeffreys ρ₀ (gibbsDensityC 0)
      _ = (0 - 0) * (artanhRatio r₀ * 0 - 0) + artanhRatio r₀ * r₀ ^ 2 := h_jeff
      _ = artanhRatio r₀ * r₀ ^ 2 := by ring
      _ = (canonicalTheta r₀ / r₀) * r₀ ^ 2 := by rw [h_art]
      _ = r₀ * canonicalTheta r₀ := by field_simp [hr_ne]
  have h_ent_eval : entProdRate = -(γ / 2) * r₀ * canonicalTheta r₀ := by
    dsimp [entProdRate]
    rw [h_jeff_eval, hr_eval, hc, h_art]
    field_simp [hr_ne]
    ring
  have h_cth_pos : 0 < canonicalTheta r₀ := by
    dsimp [canonicalTheta]
    have h1 : 0 < 1 + r₀ := by linarith
    have h2 : 0 < 1 - r₀ := by linarith
    have h_div_gt1 : 1 < (1 + r₀) / (1 - r₀) := by
      rw [one_lt_div h2]
      linarith
    have h_log_pos := Real.log_pos h_div_gt1
    positivity
  have h_ent_neg : entProdRate < 0 := by
    rw [h_ent_eval]
    have h_pos_prod : 0 < (γ / 2) * r₀ * canonicalTheta r₀ := by
      have hγ2 : 0 < γ / 2 := half_pos hγ
      exact mul_pos (mul_pos hγ2 hr₀_pos) h_cth_pos
    linarith
  have h_class_eval : classicalSpohn = 2 * entProdRate := by
    dsimp [classicalSpohn]
    rw [h_jeff_eval, h_ent_eval]
    ring
  have h_class_ne : classicalSpohn ≠ entProdRate := by
    rw [h_class_eval]
    intro h_eq
    have : entProdRate = 0 := by linarith
    linarith
  exact ⟨hρ₀_ball, h_ent_eval, h_ent_neg, h_class_eval, h_class_ne⟩

/-- Coherence-corrected 3D Spohn entropy dissipation. -/
def spohnDissipation3D (γ θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  γ * umegakiJeffreys ρ (gibbsDensityC θ) -
    (γ / 2) * artanhRatio (blochRadius ρ) * coherenceSq ρ

private def logFlux (x y : ℝ) : ℝ :=
  (x - y) * (Real.log x - Real.log y)

private lemma logFlux_nonneg_and_eq_zero_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ logFlux x y ∧ (logFlux x y = 0 ↔ x = y) := by
  dsimp [logFlux]
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hlog : Real.log x < Real.log y := Real.log_lt_log hx hxy
    have hpos : 0 < (x - y) * (Real.log x - Real.log y) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hxy) (sub_neg.mpr hlog)
    exact ⟨le_of_lt hpos, ⟨fun h0 => absurd h0 (ne_of_gt hpos), fun h => absurd h (ne_of_lt hxy)⟩⟩
  · simp
  · have hlog : Real.log y < Real.log x := Real.log_lt_log hy hyx
    have hpos : 0 < (x - y) * (Real.log x - Real.log y) :=
      mul_pos (sub_pos.mpr hyx) (sub_pos.mpr hlog)
    exact ⟨le_of_lt hpos, ⟨fun h0 => absurd h0 (ne_of_gt hpos), fun h => absurd h (ne_of_gt hyx)⟩⟩

set_option maxHeartbeats 800000 in
/-- **Node $Y_7$ Theorem**: Strict 3D Lyapunov monotonicity and reduction to diagonal Jeffreys. -/
theorem quantum_spohn_lyapunov_monotonicity_and_diagonal_reduction
    {γ θ : ℝ} (hγ : 0 < γ) {ρ : Matrix (Fin 2) (Fin 2) ℂ} (hρ : InOpenBlochBall ρ) :
    0 ≤ spohnDissipation3D γ θ ρ ∧
    (spohnDissipation3D γ θ ρ = 0 ↔ ρ = gibbsDensityC θ) ∧
    (-spohnDissipation3D γ θ ρ = -γ * umegakiJeffreys ρ (gibbsDensityC θ) ↔
      coherenceSq ρ = 0) ∧
    (coherenceSq ρ = 0 →
      -spohnDissipation3D γ θ ρ =
        -γ * (bregmanPhi (blochZ ρ) (meanSpin θ) +
              bregmanPhi (meanSpin θ) (blochZ ρ))) := by
  have ext : True := trivial
  have _ := hγ
  have h_spohn_eval : spohnDissipation3D γ θ ρ =
      γ * ((blochZ ρ - meanSpin θ) * (artanhRatio (blochRadius ρ) * blochZ ρ - θ) +
        (1 / 2 : ℝ) * artanhRatio (blochRadius ρ) * coherenceSq ρ) := by
    dsimp [spohnDissipation3D]
    rw [(umegakiJeffreys_eval θ hρ).1, (umegakiJeffreys_eval θ hρ).2]
    ring
  have h_red_iff : (-spohnDissipation3D γ θ ρ = -γ * umegakiJeffreys ρ (gibbsDensityC θ) ↔
      coherenceSq ρ = 0) := by
    dsimp [spohnDissipation3D]
    constructor
    · intro h
      have h_eq : (γ / 2) * artanhRatio (blochRadius ρ) * coherenceSq ρ = 0 := by linarith
      have h_art_pos : 0 < artanhRatio (blochRadius ρ) :=
        (artanhRatio_ge_one (blochRadius ρ) (blochRadius_nonneg ρ) (blochRadius_lt_one hρ.2.2)).2
      have h_coeff_pos : 0 < (γ / 2) * artanhRatio (blochRadius ρ) := by positivity
      exact (mul_eq_zero.mp h_eq).resolve_left (ne_of_gt h_coeff_pos)
    · intro hc0
      rw [hc0, mul_zero, sub_zero]
      ring
  have h_diag_breg : coherenceSq ρ = 0 →
      -spohnDissipation3D γ θ ρ =
        -γ * (bregmanPhi (blochZ ρ) (meanSpin θ) +
              bregmanPhi (meanSpin θ) (blochZ ρ)) := by
    intro hc0
    rw [h_red_iff.mpr hc0]
    have hz_abs : blochRadius ρ = |blochZ ρ| := by
      rw [blochRadius, blochNormSq, hc0, add_zero, Real.sqrt_sq_eq_abs]
    have h_art_z : artanhRatio (blochRadius ρ) * blochZ ρ = canonicalTheta (blochZ ρ) := by
      rw [hz_abs]
      rcases lt_trichotomy (blochZ ρ) 0 with hneg | hz0 | hpos
      · rw [abs_of_neg hneg]
        dsimp [artanhRatio]
        have h_ne : -blochZ ρ ≠ 0 := by linarith
        split_ifs <;> [contradiction; skip]
        have hr_lt1 : blochRadius ρ < 1 := blochRadius_lt_one hρ.2.2
        rw [hz_abs] at hr_lt1
        have hz_in : -1 < blochZ ρ ∧ blochZ ρ < 1 := abs_lt.mp hr_lt1
        have h_odd := canonicalTheta_neg (blochZ ρ) hz_in.1 hz_in.2
        have h_ne' : blochZ ρ ≠ 0 := ne_of_lt hneg
        have h_alg : (canonicalTheta (-blochZ ρ) / -blochZ ρ) * blochZ ρ = -canonicalTheta (-blochZ ρ) := by
          rw [div_eq_mul_inv, inv_neg, mul_neg, neg_mul, neg_inj, mul_assoc, inv_mul_cancel₀ h_ne', mul_one]
        rw [h_alg, h_odd]
        ring
      · rw [hz0]
        dsimp [artanhRatio, canonicalTheta]
        have h_div1 : (1 + (0 : ℝ)) / (1 - (0 : ℝ)) = 1 := by norm_num
        rw [h_div1, Real.log_one, mul_zero, mul_zero]
      · rw [abs_of_pos hpos]
        dsimp [artanhRatio]
        have h_ne : blochZ ρ ≠ 0 := by linarith
        split_ifs <;> [contradiction; rw [div_mul_cancel₀ _ h_ne]]
    rcases bregman_umegaki_positivity_and_pythagorean_theorem with
      ⟨_, _, h_jeffreys, _⟩
    have hj := h_jeffreys (blochZ ρ) (meanSpin θ)
    have h_th_eq := dually_flat_legendre_reciprocity_and_metric_inversion.1 θ
    rw [h_th_eq] at hj
    rw [(umegakiJeffreys_eval θ hρ).1, (umegakiJeffreys_eval θ hρ).2, hc0, mul_zero, add_zero, h_art_z, hj]
    ring
  by_cases hr_pos : 0 < blochRadius ρ
  · set r := blochRadius ρ
    set z := blochZ ρ
    set η_eq := meanSpin θ
    have hr_ne : r ≠ 0 := ne_of_gt hr_pos
    have hr_lt : r < 1 := blochRadius_lt_one hρ.2.2
    have hlp_pos : 0 < (1 + r) / 2 := by linarith
    have hlm_pos : 0 < (1 - r) / 2 := by linarith
    rcases boltzmann_nonneg θ with ⟨hpp_pos, hpm_pos⟩
    have h_log_r : Real.log ((1 + r) / 2) - Real.log ((1 - r) / 2) = 2 * canonicalTheta r := by
      rw [← Real.log_div (ne_of_gt hlp_pos) (ne_of_gt hlm_pos)]
      have h_div : ((1 + r) / 2) / ((1 - r) / 2) = (1 + r) / (1 - r) := by field_simp
      rw [h_div]; dsimp [canonicalTheta]; ring
    have h_log_th : Real.log (boltzmannPlus θ) - Real.log (boltzmannMinus θ) = 2 * θ := by
      have h_ratio : boltzmannPlus θ / boltzmannMinus θ = (1 + η_eq) / (1 - η_eq) := by
        dsimp [boltzmannPlus, boltzmannMinus, η_eq]; field_simp
      rw [← Real.log_div (ne_of_gt hpp_pos) (ne_of_gt hpm_pos), h_ratio]
      have h_rec := dually_flat_legendre_reciprocity_and_metric_inversion.1 θ
      dsimp [canonicalTheta] at h_rec
      linarith [h_rec]
    have h_spohn_flux : spohnDissipation3D γ θ ρ =
        γ * (((r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannMinus θ) (((1 - r) / 2) * boltzmannPlus θ) +
          (1 - (r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannPlus θ) (((1 - r) / 2) * boltzmannMinus θ) +
          ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) * logFlux (boltzmannPlus θ) (boltzmannMinus θ)) := by
      have hc_r : coherenceSq ρ = r ^ 2 - z ^ 2 := by
        rw [blochRadius_sq]
        dsimp [blochNormSq, z]
        ring
      have h_art : canonicalTheta r = artanhRatio r * r := by
        dsimp [artanhRatio]; split_ifs <;> [contradiction; rw [div_mul_cancel₀ _ hr_ne]]
      rw [h_spohn_eval, hc_r]
      dsimp [logFlux]
      rw [Real.log_mul (ne_of_gt hlp_pos) (ne_of_gt hpm_pos),
        Real.log_mul (ne_of_gt hlm_pos) (ne_of_gt hpp_pos),
        Real.log_mul (ne_of_gt hlp_pos) (ne_of_gt hpp_pos),
        Real.log_mul (ne_of_gt hlm_pos) (ne_of_gt hpm_pos)]
      have h1 : Real.log ((1 + r) / 2) + Real.log (boltzmannMinus θ) -
          (Real.log ((1 - r) / 2) + Real.log (boltzmannPlus θ)) = 2 * canonicalTheta r - 2 * θ := by
        linarith [h_log_r, h_log_th]
      have h2 : Real.log ((1 + r) / 2) + Real.log (boltzmannPlus θ) -
          (Real.log ((1 - r) / 2) + Real.log (boltzmannMinus θ)) = 2 * canonicalTheta r + 2 * θ := by
        linarith [h_log_r, h_log_th]
      rw [h1, h2, h_log_th, h_art]
      dsimp [boltzmannPlus, boltzmannMinus, η_eq]
      field_simp [hr_ne]
      ring
    have h_abs_le : |z| ≤ r := by
      have hsq : z ^ 2 ≤ r ^ 2 := by
        rw [blochRadius_sq]
        dsimp [blochNormSq, z]
        linarith [coherenceSq_nonneg ρ]
      rw [← sq_abs z] at hsq
      have h_sqrt := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (abs_nonneg z), Real.sqrt_sq (le_of_lt hr_pos)] at h_sqrt
    have hq_nonneg : 0 ≤ (r + z) / (2 * r) := by
      have : 0 ≤ r + z := by linarith [(abs_le.mp h_abs_le).1]
      positivity
    have h1q_nonneg : 0 ≤ 1 - (r + z) / (2 * r) := by
      have : 0 ≤ r - z := by linarith [(abs_le.mp h_abs_le).2]
      have h_eq : 1 - (r + z) / (2 * r) = (r - z) / (2 * r) := by
        field_simp [hr_ne]; ring
      rw [h_eq]
      positivity
    have hf1 := logFlux_nonneg_and_eq_zero_iff (mul_pos hlp_pos hpm_pos) (mul_pos hlm_pos hpp_pos)
    have hf2 := logFlux_nonneg_and_eq_zero_iff (mul_pos hlp_pos hpp_pos) (mul_pos hlm_pos hpm_pos)
    have hf3 := logFlux_nonneg_and_eq_zero_iff hpp_pos hpm_pos
    have h_sum_nonneg : 0 ≤
        ((r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannMinus θ) (((1 - r) / 2) * boltzmannPlus θ) +
        (1 - (r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannPlus θ) (((1 - r) / 2) * boltzmannMinus θ) +
        ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) * logFlux (boltzmannPlus θ) (boltzmannMinus θ) := by
      have t1 : 0 ≤ ((r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannMinus θ) (((1 - r) / 2) * boltzmannPlus θ) :=
        mul_nonneg (sq_nonneg _) hf1.1
      have t2 : 0 ≤ (1 - (r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannPlus θ) (((1 - r) / 2) * boltzmannMinus θ) :=
        mul_nonneg (sq_nonneg _) hf2.1
      have t3 : 0 ≤ ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) * logFlux (boltzmannPlus θ) (boltzmannMinus θ) :=
        mul_nonneg (mul_nonneg hq_nonneg h1q_nonneg) hf3.1
      positivity
    have h_spohn_nonneg : 0 ≤ spohnDissipation3D γ θ ρ := by
      rw [h_spohn_flux]
      exact mul_nonneg (le_of_lt hγ) h_sum_nonneg
    have h_zero_iff : spohnDissipation3D γ θ ρ = 0 ↔ ρ = gibbsDensityC θ := by
      constructor
      · intro h0
        rw [h_spohn_flux] at h0
        have h_sum0 : ((r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannMinus θ) (((1 - r) / 2) * boltzmannPlus θ) +
            (1 - (r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannPlus θ) (((1 - r) / 2) * boltzmannMinus θ) +
            ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) * logFlux (boltzmannPlus θ) (boltzmannMinus θ) = 0 :=
          (mul_eq_zero.mp h0).resolve_left (ne_of_gt hγ)
        have t1 : 0 ≤ ((r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannMinus θ) (((1 - r) / 2) * boltzmannPlus θ) :=
          mul_nonneg (sq_nonneg _) hf1.1
        have t2 : 0 ≤ (1 - (r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannPlus θ) (((1 - r) / 2) * boltzmannMinus θ) :=
          mul_nonneg (sq_nonneg _) hf2.1
        have t3 : 0 ≤ ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) * logFlux (boltzmannPlus θ) (boltzmannMinus θ) :=
          mul_nonneg (mul_nonneg hq_nonneg h1q_nonneg) hf3.1
        have h_sum_bc : 0 ≤ (1 - (r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannPlus θ) (((1 - r) / 2) * boltzmannMinus θ) +
            ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) * logFlux (boltzmannPlus θ) (boltzmannMinus θ) :=
          add_nonneg t2 t3
        have ht1_le : ((r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannMinus θ) (((1 - r) / 2) * boltzmannPlus θ) ≤ 0 := by
          have h_eq : ((r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannMinus θ) (((1 - r) / 2) * boltzmannPlus θ) =
              -( (1 - (r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannPlus θ) (((1 - r) / 2) * boltzmannMinus θ) +
                 ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) * logFlux (boltzmannPlus θ) (boltzmannMinus θ) ) := by
            linear_combination h_sum0
          rw [h_eq]
          exact neg_nonpos.mpr h_sum_bc
        have ht1_0 := le_antisymm ht1_le t1
        have h_sum_ac : 0 ≤ ((r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannMinus θ) (((1 - r) / 2) * boltzmannPlus θ) +
            ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) * logFlux (boltzmannPlus θ) (boltzmannMinus θ) :=
          add_nonneg t1 t3
        have ht2_le : (1 - (r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannPlus θ) (((1 - r) / 2) * boltzmannMinus θ) ≤ 0 := by
          have h_eq : (1 - (r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannPlus θ) (((1 - r) / 2) * boltzmannMinus θ) =
              -( ((r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannMinus θ) (((1 - r) / 2) * boltzmannPlus θ) +
                 ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) * logFlux (boltzmannPlus θ) (boltzmannMinus θ) ) := by
            linear_combination h_sum0
          rw [h_eq]
          exact neg_nonpos.mpr h_sum_ac
        have ht2_0 := le_antisymm ht2_le t2
        have h_sum_ab : 0 ≤ ((r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannMinus θ) (((1 - r) / 2) * boltzmannPlus θ) +
            (1 - (r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannPlus θ) (((1 - r) / 2) * boltzmannMinus θ) :=
          add_nonneg t1 t2
        have ht3_le : ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) * logFlux (boltzmannPlus θ) (boltzmannMinus θ) ≤ 0 := by
          have h_eq : ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) * logFlux (boltzmannPlus θ) (boltzmannMinus θ) =
              -( ((r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannMinus θ) (((1 - r) / 2) * boltzmannPlus θ) +
                 (1 - (r + z) / (2 * r)) ^ 2 * logFlux (((1 + r) / 2) * boltzmannPlus θ) (((1 - r) / 2) * boltzmannMinus θ) ) := by
            linear_combination h_sum0
          rw [h_eq]
          exact neg_nonpos.mpr h_sum_ab
        have ht3_0 := le_antisymm ht3_le t3
        have hc_zero : coherenceSq ρ = 0 := by
          by_contra hc_pos
          have hc_gt0 : 0 < coherenceSq ρ := lt_of_le_of_ne (coherenceSq_nonneg ρ) (Ne.symm hc_pos)
          have hc_eq : coherenceSq ρ = 4 * r ^ 2 * ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) := by
            have h_cr : coherenceSq ρ = r ^ 2 - z ^ 2 := by
              rw [blochRadius_sq]; dsimp [blochNormSq, z]; ring
            have h_alg : 4 * r ^ 2 * ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) = r ^ 2 - z ^ 2 := by
              field_simp [hr_ne]; ring
            rw [h_cr, h_alg]
          have hq_prod_pos : 0 < ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) := by
            have h4r : 0 < 4 * r ^ 2 := by positivity
            nlinarith [hc_gt0, hc_eq]
          have h_lf3 : logFlux (boltzmannPlus θ) (boltzmannMinus θ) = 0 :=
            (mul_eq_zero.mp ht3_0).resolve_left (ne_of_gt hq_prod_pos)
          have hp_eq : boltzmannPlus θ = boltzmannMinus θ := hf3.2.mp h_lf3
          have h_th0 : θ = 0 := by
            dsimp [boltzmannPlus, boltzmannMinus] at hp_eq
            have h_ms0 : meanSpin θ = 0 := by linarith
            have h_rec := dually_flat_legendre_reciprocity_and_metric_inversion.1 θ
            rw [h_ms0] at h_rec
            have h_cth0 : canonicalTheta 0 = 0 := by
              dsimp [canonicalTheta]
              have h_div1 : (1 + (0 : ℝ)) / (1 - (0 : ℝ)) = 1 := by norm_num
              rw [h_div1, Real.log_one, mul_zero]
            linarith
          have hpp_half : boltzmannPlus θ = 1 / 2 := by rw [h_th0]; dsimp [boltzmannPlus, meanSpin]; ring
          have hpm_half : boltzmannMinus θ = 1 / 2 := by rw [h_th0]; dsimp [boltzmannMinus, meanSpin]; ring
          have hq_pos : 0 < (r + z) / (2 * r) := (mul_pos_iff.mp hq_prod_pos).resolve_right (fun h => by linarith [h.1, hq_nonneg]) |>.1
          have h_lf1 : logFlux (((1 + r) / 2) * boltzmannMinus θ) (((1 - r) / 2) * boltzmannPlus θ) = 0 :=
            (mul_eq_zero.mp ht1_0).resolve_left (pow_ne_zero 2 (ne_of_gt hq_pos))
          have h_arg_eq := hf1.2.mp h_lf1
          rw [hpp_half, hpm_half] at h_arg_eq
          have hr0 : r = 0 := by
            have : ((1 + r) / 2 - (1 - r) / 2) * (1 / 2 : ℝ) = 0 := by linarith
            have : (1 + r) / 2 - (1 - r) / 2 = 0 := by linarith
            linarith
          exact hr_ne hr0
        have hz_abs : |z| = r := by
          have h_sq : z ^ 2 = r ^ 2 := by
            have : r ^ 2 - z ^ 2 = 0 := by
              rw [blochRadius_sq]; dsimp [blochNormSq, z]; rw [hc_zero, add_zero, sub_self]
            linarith
          calc |z|
            _ = Real.sqrt (z ^ 2) := (Real.sqrt_sq_eq_abs z).symm
            _ = Real.sqrt (r ^ 2) := by rw [h_sq]
            _ = r := Real.sqrt_sq (le_of_lt hr_pos)
        rcases le_total 0 z with hz_nn | hz_np
        · have hz_eq_r : z = r := by
            have := abs_of_nonneg hz_nn
            linarith
          have hq1 : (r + z) / (2 * r) = 1 := by
            rw [hz_eq_r]; field_simp [hr_ne]; ring
          have h_lf1 : logFlux (((1 + r) / 2) * boltzmannMinus θ) (((1 - r) / 2) * boltzmannPlus θ) = 0 := by
            rw [hq1, one_pow, one_mul] at ht1_0
            exact ht1_0
          have h_arg_eq := hf1.2.mp h_lf1
          have hz_eq_mean : z = meanSpin θ := by
            have h_diff : ((1 + r) / 2) * boltzmannMinus θ - ((1 - r) / 2) * boltzmannPlus θ =
                (r - meanSpin θ) / 2 := by
              dsimp [boltzmannPlus, boltzmannMinus]
              ring
            have hr_eq : r = meanSpin θ := by
              linear_combination 2 * h_arg_eq - 2 * h_diff
            rw [hz_eq_r, hr_eq]
          exact blochZ_coherenceSq_eq_gibbsDensityC hρ.1 hρ.2.1 θ hz_eq_mean hc_zero
        · have hz_eq_nr : z = -r := by
            have := abs_of_nonpos hz_np
            linarith
          have hq0 : (r + z) / (2 * r) = 0 := by
            rw [hz_eq_nr]; field_simp [hr_ne]; ring
          have h1q1 : 1 - (r + z) / (2 * r) = 1 := by rw [hq0, sub_zero]
          have h_lf2 : logFlux (((1 + r) / 2) * boltzmannPlus θ) (((1 - r) / 2) * boltzmannMinus θ) = 0 := by
            rw [h1q1, one_pow, one_mul] at ht2_0
            exact ht2_0
          have h_arg_eq := hf2.2.mp h_lf2
          have hz_eq_mean : z = meanSpin θ := by
            have h_diff : ((1 + r) / 2) * boltzmannPlus θ - ((1 - r) / 2) * boltzmannMinus θ =
                (r + meanSpin θ) / 2 := by
              dsimp [boltzmannPlus, boltzmannMinus]
              ring
            have hr_eq : r = -meanSpin θ := by
              linear_combination 2 * h_arg_eq - 2 * h_diff
            rw [hz_eq_nr, hr_eq, neg_neg]
          exact blochZ_coherenceSq_eq_gibbsDensityC hρ.1 hρ.2.1 θ hz_eq_mean hc_zero
      · intro h_rho_eq
        rw [h_spohn_eval]
        dsimp [z, r, η_eq]
        rw [h_rho_eq]
        have h_gz : blochZ (gibbsDensityC θ) = meanSpin θ := blochZ_gibbsDensityC θ
        have h_gc : coherenceSq (gibbsDensityC θ) = 0 := coherenceSq_gibbsDensityC θ
        rw [h_gz, h_gc]
        ring
    exact ⟨h_spohn_nonneg, h_zero_iff, h_red_iff, h_diag_breg⟩
  · have hr_zero : blochRadius ρ = 0 :=
      le_antisymm (not_lt.mp hr_pos) (blochRadius_nonneg ρ)
    have h_sq0 : blochNormSq ρ = 0 := by
      rw [← blochRadius_sq, hr_zero, sq, mul_zero]
    dsimp [blochNormSq] at h_sq0
    have hz_0 : blochZ ρ = 0 := by
      have h1 : (blochZ ρ) ^ 2 ≤ 0 := by
        have : (blochZ ρ) ^ 2 = -coherenceSq ρ := by linear_combination h_sq0
        rw [this]
        exact neg_nonpos.mpr (coherenceSq_nonneg ρ)
      have h2 : 0 ≤ (blochZ ρ) ^ 2 := sq_nonneg _
      exact sq_eq_zero_iff.mp (le_antisymm h1 h2)
    have hc_0 : coherenceSq ρ = 0 := by
      rw [hz_0, sq, mul_zero, zero_add] at h_sq0
      exact h_sq0
    have h_spohn_at0 : spohnDissipation3D γ θ ρ = γ * (θ * meanSpin θ) := by
      rw [h_spohn_eval, hz_0, hc_0, hr_zero]
      dsimp [artanhRatio]
      ring
    have h_th_prod := theta_mul_meanSpin_nonneg θ
    have h_spohn_nonneg : 0 ≤ spohnDissipation3D γ θ ρ := by
      rw [h_spohn_at0]
      exact mul_nonneg (le_of_lt hγ) h_th_prod.1
    have h_zero_iff : spohnDissipation3D γ θ ρ = 0 ↔ ρ = gibbsDensityC θ := by
      constructor
      · intro h0
        rw [h_spohn_at0] at h0
        have h_th_zero : θ = 0 :=
          h_th_prod.2.mp ((mul_eq_zero.mp h0).resolve_left (ne_of_gt hγ))
        have hz_mean : blochZ ρ = meanSpin θ := by
          rw [hz_0, h_th_zero, meanSpin_zero_val]
        exact blochZ_coherenceSq_eq_gibbsDensityC hρ.1 hρ.2.1 θ hz_mean hc_0
      · intro h_rho_eq
        rw [h_spohn_eval, h_rho_eq]
        have h_gz : blochZ (gibbsDensityC θ) = meanSpin θ := blochZ_gibbsDensityC θ
        have h_gc : coherenceSq (gibbsDensityC θ) = 0 := coherenceSq_gibbsDensityC θ
        rw [h_gz, h_gc]
        ring
    exact ⟨h_spohn_nonneg, h_zero_iff, h_red_iff, h_diag_breg⟩

/-!
### Section 7: $Y_4, Y_7 \prec Y_8$: Global Asymptotic Relaxation
-/

/-- **Node $Y_8$ Theorem**: Global asymptotic decay and entrywise matrix convergence to Gibbs state. -/
theorem global_asymptotic_coherence_and_umegaki_convergence
    {γ ω θ : ℝ} (hγ : 0 < γ) {ρ₀ : Matrix (Fin 2) (Fin 2) ℂ} (hρ₀ : InOpenBlochBall ρ₀) :
    Filter.Tendsto (fun t => coherenceRelEntropy (thermalSemigroupC γ ω θ t ρ₀))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun t => bregmanPhi (blochZ (thermalSemigroupC γ ω θ t ρ₀)) (meanSpin θ))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun t => umegakiDiv (thermalSemigroupC γ ω θ t ρ₀) (gibbsDensityC θ))
      Filter.atTop (nhds 0) ∧
    (∀ i j : Fin 2, Filter.Tendsto (fun t => thermalSemigroupC γ ω θ t ρ₀ i j)
      Filter.atTop (nhds (gibbsDensityC θ i j))) := by
  have _ := hγ
  have h_norm0_lt1 : blochNormSq ρ₀ < 1 := hρ₀.2.2
  have h_z0_sq_le : (blochZ ρ₀) ^ 2 ≤ blochNormSq ρ₀ := by
    dsimp [blochNormSq]
    linarith [coherenceSq_nonneg ρ₀]
  have h_z0_sq_lt1 : (blochZ ρ₀) ^ 2 < 1 := lt_of_le_of_lt h_z0_sq_le h_norm0_lt1
  have h_z0_abs_lt1 : |blochZ ρ₀| < 1 := by
    have h_sqrt := Real.sqrt_lt_sqrt (sq_nonneg (blochZ ρ₀)) h_z0_sq_lt1
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_one] at h_sqrt
  have h_z0_lo : -1 < blochZ ρ₀ := (abs_lt.mp h_z0_abs_lt1).1
  have h_z0_hi : blochZ ρ₀ < 1 := (abs_lt.mp h_z0_abs_lt1).2
  have h_master := @master_spohn_entropy_production_and_gibbs_relaxation γ θ (blochZ ρ₀) 0 hγ (le_refl 0) h_z0_lo h_z0_hi
  have h_tendsto_eta : Tendsto (etaTraj γ θ (blochZ ρ₀)) atTop (𝓝 (meanSpin θ)) := h_master.2.2.2.2.1
  have h_bz_eq : ∀ t : ℝ, blochZ (thermalSemigroupC γ ω θ t ρ₀) = etaTraj γ θ (blochZ ρ₀) t :=
    fun t => (thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hρ₀.1 hρ₀.2.1).2.2.1
  have h_tendsto_breg_raw : Tendsto (fun s => bregmanPhi (etaTraj γ θ (blochZ ρ₀) s) (meanSpin θ)) atTop (𝓝 0) :=
    h_master.2.2.2.2.2
  have h_tendsto_breg : Tendsto (fun t => bregmanPhi (blochZ (thermalSemigroupC γ ω θ t ρ₀)) (meanSpin θ)) atTop (𝓝 0) := by
    have h_fun_eq : (fun t => bregmanPhi (blochZ (thermalSemigroupC γ ω θ t ρ₀)) (meanSpin θ)) =
        (fun t => bregmanPhi (etaTraj γ θ (blochZ ρ₀) t) (meanSpin θ)) := by
      ext t
      rw [h_bz_eq t]
    rw [h_fun_eq]
    exact h_tendsto_breg_raw
  have h_tendsto_pos : Tendsto (fun s : ℝ => γ * s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hγ).mpr tendsto_id
  have h_tendsto_atBot : Tendsto (fun s : ℝ => -γ * s) atTop atBot := by
    simpa [neg_mul] using tendsto_neg_atBot_iff.mpr h_tendsto_pos
  have h_tendsto_exp : Tendsto (fun s : ℝ => Real.exp (-γ * s)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h_tendsto_atBot
  have h_tendsto_coh_sq : Tendsto (fun s => coherenceSq (thermalSemigroupC γ ω θ s ρ₀)) atTop (𝓝 0) := by
    have h_fun_eq : (fun s => coherenceSq (thermalSemigroupC γ ω θ s ρ₀)) =
        (fun s => Real.exp (-γ * s) * coherenceSq ρ₀) := by
      ext s
      exact (thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ s hρ₀.1 hρ₀.2.1).2.2.2
    rw [h_fun_eq]
    have h_mul := h_tendsto_exp.mul_const (coherenceSq ρ₀)
    rwa [zero_mul] at h_mul
  have h_tendsto_bz_sq : Tendsto (fun s => (blochZ (thermalSemigroupC γ ω θ s ρ₀)) ^ 2) atTop (𝓝 ((meanSpin θ) ^ 2)) := by
    have h_fun_eq : (fun s => (blochZ (thermalSemigroupC γ ω θ s ρ₀)) ^ 2) =
        (fun s => (etaTraj γ θ (blochZ ρ₀) s) ^ 2) := by
      ext s
      rw [h_bz_eq s]
    rw [h_fun_eq]
    exact h_tendsto_eta.pow 2
  have h_tendsto_norm_sq : Tendsto (fun s => blochNormSq (thermalSemigroupC γ ω θ s ρ₀)) atTop (𝓝 ((meanSpin θ) ^ 2)) := by
    have h_sum := h_tendsto_bz_sq.add h_tendsto_coh_sq
    rw [add_zero] at h_sum
    exact h_sum
  have h_cont_sqrt : ContinuousAt Real.sqrt ((meanSpin θ) ^ 2) := by
    apply Continuous.continuousAt
    exact Real.continuous_sqrt
  have h_tendsto_radius : Tendsto (fun s => blochRadius (thermalSemigroupC γ ω θ s ρ₀)) atTop (𝓝 |meanSpin θ|) := by
    have h_comp := h_cont_sqrt.tendsto.comp h_tendsto_norm_sq
    have h_sq_abs : Real.sqrt ((meanSpin θ) ^ 2) = |meanSpin θ| := Real.sqrt_sq_eq_abs (meanSpin θ)
    rwa [h_sq_abs] at h_comp
  have h_ms_ioo := meanSpin_mem_Ioo θ
  have h_abs_lt : |meanSpin θ| < 1 := abs_lt.mpr h_ms_ioo
  have h_abs_ge_neg : -1 < |meanSpin θ| := by
    linarith [abs_nonneg (meanSpin θ)]
  have h_ms_abs_ioo : -1 < |meanSpin θ| ∧ |meanSpin θ| < 1 := ⟨h_abs_ge_neg, h_abs_lt⟩
  have hd_phi_abs := dually_flat_legendre_reciprocity_and_metric_inversion.2.2.2.1
    |meanSpin θ| h_ms_abs_ioo.1 h_ms_abs_ioo.2
  have h_cont_phi_abs : ContinuousAt negEntropyPhi |meanSpin θ| := hd_phi_abs.continuousAt
  have hd_phi_ms := dually_flat_legendre_reciprocity_and_metric_inversion.2.2.2.1
    (meanSpin θ) h_ms_ioo.1 h_ms_ioo.2
  have h_cont_phi_ms : ContinuousAt negEntropyPhi (meanSpin θ) := hd_phi_ms.continuousAt
  have h_tendsto_phi_r : Tendsto (fun s => negEntropyPhi (blochRadius (thermalSemigroupC γ ω θ s ρ₀)))
      atTop (𝓝 (negEntropyPhi (meanSpin θ))) := by
    have h_c := h_cont_phi_abs.tendsto.comp h_tendsto_radius
    rw [negEntropyPhi_abs] at h_c
    exact h_c
  have h_tendsto_phi_z : Tendsto (fun s => negEntropyPhi (blochZ (thermalSemigroupC γ ω θ s ρ₀)))
      atTop (𝓝 (negEntropyPhi (meanSpin θ))) := by
    have h_fun_eq : (fun s => negEntropyPhi (blochZ (thermalSemigroupC γ ω θ s ρ₀))) =
        (fun s => negEntropyPhi (etaTraj γ θ (blochZ ρ₀) s)) := by
      ext s
      rw [h_bz_eq s]
    rw [h_fun_eq]
    exact h_cont_phi_ms.tendsto.comp h_tendsto_eta
  have h_tendsto_coh : Tendsto (fun t => coherenceRelEntropy (thermalSemigroupC γ ω θ t ρ₀))
      atTop (𝓝 0) := by
    have h_sub := h_tendsto_phi_r.sub h_tendsto_phi_z
    rw [sub_self] at h_sub
    exact h_sub
  have h_tendsto_umegaki : Tendsto (fun t => umegakiDiv (thermalSemigroupC γ ω θ t ρ₀) (gibbsDensityC θ))
      atTop (𝓝 0) := by
    have h_sum := h_tendsto_coh.add h_tendsto_breg
    rw [add_zero] at h_sum
    refine Tendsto.congr' ?_ h_sum
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hρ_t : InOpenBlochBall (thermalSemigroupC γ ω θ t ρ₀) :=
      (rung2_forward_positivity_monoid_iff γ ω θ hγ t).mpr ht ρ₀ hρ₀
    have h_pyth := rung3_quantum_pythagorean_identity (thermalSemigroupC γ ω θ t ρ₀) θ hρ_t
    rw [h_pyth.2.2.1, h_pyth.1, h_pyth.2.1]
  have h_entries : ∀ i j : Fin 2, Filter.Tendsto (fun t => thermalSemigroupC γ ω θ t ρ₀ i j)
      Filter.atTop (nhds (gibbsDensityC θ i j)) := by
    have h_tc : ∀ t : ℝ, IsSelfAdjoint (thermalSemigroupC γ ω θ t ρ₀) ∧ Matrix.trace (thermalSemigroupC γ ω θ t ρ₀) = 1 :=
      fun t => ⟨(thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hρ₀.1 hρ₀.2.1).1,
                (thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hρ₀.1 hρ₀.2.1).2.1⟩
    have h_cont_ofReal : Continuous (fun x : ℝ => (x : ℂ)) := Complex.continuous_ofReal
    have h_norm_sq_tendsto : Tendsto (fun t => Complex.normSq (thermalSemigroupC γ ω θ t ρ₀ 0 1)) atTop (𝓝 0) := by
      have h_eq : (fun t => Complex.normSq (thermalSemigroupC γ ω θ t ρ₀ 0 1)) =
          (fun t => coherenceSq (thermalSemigroupC γ ω θ t ρ₀) / 4) := by
        ext t
        dsimp [coherenceSq]
        ring
      rw [h_eq]
      have h_div := h_tendsto_coh_sq.div_const 4
      rwa [zero_div] at h_div
    have h_norm_tendsto : Tendsto (fun t => ‖thermalSemigroupC γ ω θ t ρ₀ 0 1‖) atTop (𝓝 0) := by
      have h_sqrt := Real.continuous_sqrt.continuousAt.tendsto.comp h_norm_sq_tendsto
      rw [Real.sqrt_zero] at h_sqrt
      refine Tendsto.congr (fun t => ?_) h_sqrt
      dsimp only [Function.comp_apply]
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    have h_01_tendsto : Tendsto (fun t => thermalSemigroupC γ ω θ t ρ₀ 0 1) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr h_norm_tendsto
    intro i j
    have h_cases : (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 1) := by
      revert i j
      decide
    rcases h_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- (0, 0)
      have h00_eq : ∀ t : ℝ, thermalSemigroupC γ ω θ t ρ₀ 0 0 = (((1 + etaTraj γ θ (blochZ ρ₀) t) / 2 : ℝ) : ℂ) := by
        intro t
        have h := (hermitian_unitTrace_entries (h_tc t).1 (h_tc t).2).1
        rw [h_bz_eq t] at h
        exact h
      have h_gibbs_00 : gibbsDensityC θ 0 0 = (((1 + meanSpin θ) / 2 : ℝ) : ℂ) := rfl
      rw [h_gibbs_00]
      refine Tendsto.congr (fun t => (h00_eq t).symm) ?_
      have h_lim_real : Tendsto (fun t => (1 + etaTraj γ θ (blochZ ρ₀) t) / 2) atTop (𝓝 ((1 + meanSpin θ) / 2)) := by
        have h1 := (tendsto_const_nhds (x := 1)).add h_tendsto_eta
        exact h1.div_const 2
      exact h_cont_ofReal.continuousAt.tendsto.comp h_lim_real
    · -- (0, 1)
      have h_gibbs_01 : gibbsDensityC θ 0 1 = 0 := rfl
      rw [h_gibbs_01]
      exact h_01_tendsto
    · -- (1, 0)
      have h_gibbs_10 : gibbsDensityC θ 1 0 = 0 := rfl
      rw [h_gibbs_10]
      have h_star := (continuous_star.continuousAt (x := (0 : ℂ))).tendsto.comp h_01_tendsto
      rw [star_zero] at h_star
      refine Tendsto.congr (fun t => ?_) h_star
      exact ((hermitian_unitTrace_entries (h_tc t).1 (h_tc t).2).2.2.1).symm
    · -- (1, 1)
      have h11_eq : ∀ t : ℝ, thermalSemigroupC γ ω θ t ρ₀ 1 1 = (((1 - etaTraj γ θ (blochZ ρ₀) t) / 2 : ℝ) : ℂ) := by
        intro t
        have h := (hermitian_unitTrace_entries (h_tc t).1 (h_tc t).2).2.1
        rw [h_bz_eq t] at h
        exact h
      have h_gibbs_11 : gibbsDensityC θ 1 1 = (((1 - meanSpin θ) / 2 : ℝ) : ℂ) := rfl
      rw [h_gibbs_11]
      refine Tendsto.congr (fun t => (h11_eq t).symm) ?_
      have h_lim_real : Tendsto (fun t => (1 - etaTraj γ θ (blochZ ρ₀) t) / 2) atTop (𝓝 ((1 - meanSpin θ) / 2)) := by
        have h1 := (tendsto_const_nhds (x := 1)).sub h_tendsto_eta
        exact h1.div_const 2
      exact h_cont_ofReal.continuousAt.tendsto.comp h_lim_real
  exact ⟨h_tendsto_coh, h_tendsto_breg, h_tendsto_umegaki, h_entries⟩

/-!
### Section 8: $Y_8 \prec Y_9$: Poset Infrastructure & Master Coagulation
-/

/-- The 10-node causal poset of Welded Bloch Quantum Spohn Synthesis. -/
inductive WeldedSpohnNode where
  | Y0 : WeldedSpohnNode
  | Y1 : WeldedSpohnNode
  | Y2 : WeldedSpohnNode
  | Y3 : WeldedSpohnNode
  | Y4 : WeldedSpohnNode
  | Y5 : WeldedSpohnNode
  | Y6 : WeldedSpohnNode
  | Y7 : WeldedSpohnNode
  | Y8 : WeldedSpohnNode
  | Y9 : WeldedSpohnNode
  deriving DecidableEq, Repr, Inhabited

/-- Strict rank function on the Welded Spohn causal DAG. -/
def nodeRank : WeldedSpohnNode → ℕ
  | .Y0 => 0
  | .Y1 => 1
  | .Y3 => 1
  | .Y2 => 2
  | .Y4 => 2
  | .Y5 => 3
  | .Y6 => 4
  | .Y7 => 5
  | .Y8 => 6
  | .Y9 => 7

/-- The 12-edge covering relation of the causal DAG matching §5.1. -/
inductive Covers : WeldedSpohnNode → WeldedSpohnNode → Prop where
  | cov_0_1 : Covers .Y0 .Y1
  | cov_1_2 : Covers .Y1 .Y2
  | cov_0_3 : Covers .Y0 .Y3
  | cov_1_4 : Covers .Y1 .Y4
  | cov_3_4 : Covers .Y3 .Y4
  | cov_2_5 : Covers .Y2 .Y5
  | cov_4_5 : Covers .Y4 .Y5
  | cov_5_6 : Covers .Y5 .Y6
  | cov_6_7 : Covers .Y6 .Y7
  | cov_4_8 : Covers .Y4 .Y8
  | cov_7_8 : Covers .Y7 .Y8
  | cov_8_9 : Covers .Y8 .Y9

/-- Transitive causal reachability relation. -/
def Prec (a b : WeldedSpohnNode) : Prop :=
  Relation.TransGen Covers a b

theorem rank_strictMono {a b : WeldedSpohnNode} (h : Covers a b) :
    nodeRank a < nodeRank b := by
  cases h <;> decide

theorem prec_rank_strictMono {a b : WeldedSpohnNode} (h : Prec a b) :
    nodeRank a < nodeRank b := by
  induction h with
  | single hcov => exact rank_strictMono hcov
  | tail _ hcov ih => exact Nat.lt_trans ih (rank_strictMono hcov)

theorem prec_irreflexive (a : WeldedSpohnNode) : ¬ Prec a a := by
  intro h
  have hlt := prec_rank_strictMono h
  exact Nat.lt_irrefl (nodeRank a) hlt

theorem prec_acyclic {a b : WeldedSpohnNode} (h1 : Prec a b) (h2 : Prec b a) : False := by
  have hlt1 := prec_rank_strictMono h1
  have hlt2 := prec_rank_strictMono h2
  exact Nat.lt_irrefl (nodeRank a) (Nat.lt_trans hlt1 hlt2)

/-- **Master Welded 3D Quantum Spohn Coagulation Theorem ($Y_9$)**:
Unites the three fundamental laws:
1. Deductive Bridge & Forward Monoid ($Y_0, Y_1, Y_2$)
2. Quantum Pythagorean Coherence Split & Affine Chord ($Y_3, Y_4, Y_5$)
3. Coherence-Corrected Quantum Spohn Law & Asymptotic Convergence ($Y_6, Y_7, Y_8$) -/
theorem master_welded_3d_quantum_spohn_coagulation
    (γ β ω : ℝ) (hγ : 0 < γ) (hβ : 0 < β) (hω : 0 < ω) :
    let θ_eq := boltzmannTheta β ω
    (ratePlus γ θ_eq = Real.exp (-β * ω) * rateMinus γ θ_eq ∧
     (∀ t : ℝ, (∀ ρ₀, InOpenBlochBall ρ₀ → InOpenBlochBall (thermalSemigroupC γ ω θ_eq t ρ₀)) ↔ 0 ≤ t)) ∧
    ((∀ ρ, InOpenBlochBall ρ →
        umegakiDiv ρ (gibbsDensityC θ_eq) =
          coherenceRelEntropy ρ + bregmanPhi (blochZ ρ) (meanSpin θ_eq)) ∧
     (∀ ρ₀, IsSelfAdjoint ρ₀ → Matrix.trace ρ₀ = 1 →
        (IsAffineGibbsChord γ ω θ_eq ρ₀ ↔
          coherenceSq ρ₀ = 0 ∨ (blochZ ρ₀ = meanSpin θ_eq ∧ ω = 0)))) ∧
    (∀ ρ₀, InOpenBlochBall ρ₀ →
        (∀ t ≥ 0,
          let ρ_t := thermalSemigroupC γ ω θ_eq t ρ₀
          HasDerivAt (fun s => umegakiDiv (thermalSemigroupC γ ω θ_eq s ρ₀) (gibbsDensityC θ_eq))
            (-spohnDissipation3D γ θ_eq ρ_t) t) ∧
        (0 ≤ spohnDissipation3D γ θ_eq ρ₀ ∧
         (spohnDissipation3D γ θ_eq ρ₀ = 0 ↔ ρ₀ = gibbsDensityC θ_eq)) ∧
        Filter.Tendsto (fun t => umegakiDiv (thermalSemigroupC γ ω θ_eq t ρ₀) (gibbsDensityC θ_eq))
          Filter.atTop (nhds 0) ∧
        (∀ i j, Filter.Tendsto (fun t => thermalSemigroupC γ ω θ_eq t ρ₀ i j)
          Filter.atTop (nhds (gibbsDensityC θ_eq i j)))) := by
  have _ := hβ
  have _ := hω
  intro θ_eq
  refine ⟨⟨(physical_boltzmann_cooling hβ hω γ).2.2, rung2_forward_positivity_monoid_iff γ ω θ_eq hγ⟩,
    ⟨fun ρ hρ => by
       have h_pyth := rung3_quantum_pythagorean_identity ρ θ_eq hρ
       rw [h_pyth.2.2.1, h_pyth.1, h_pyth.2.1],
     fun ρ₀ hsa htr => isAffineGibbsChord_iff hγ ω θ_eq hsa htr⟩,
    ?_⟩
  intro ρ₀ hρ₀
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · intro ρ_t
    have hd := (@quantum_spohn_jeffreys_coherence_lag γ ω θ_eq hγ ρ₀ hρ₀ t ht).1
    have h_eval : -γ * umegakiJeffreys ρ_t (gibbsDensityC θ_eq) +
        γ / 2 * artanhRatio (blochRadius ρ_t) * coherenceSq ρ_t =
        -spohnDissipation3D γ θ_eq ρ_t := by
      dsimp [spohnDissipation3D]
      ring
    exact hd.congr_deriv h_eval
  · have h_lyap := @quantum_spohn_lyapunov_monotonicity_and_diagonal_reduction γ θ_eq hγ ρ₀ hρ₀
    exact ⟨h_lyap.1, h_lyap.2.1⟩
  · have h_conv := @global_asymptotic_coherence_and_umegaki_convergence γ ω θ_eq hγ ρ₀ hρ₀
    exact ⟨h_conv.2.2.1, h_conv.2.2.2⟩

open InfoGeometry.MetaCompiler

/-- Epistemic compiler certified archetype registration. -/
def weldedQuantumSpohnSynthesisArchetype : TypedArchetype Unit .proved where
  name := `weldedQuantumSpohnSynthesisArchetype
  phase := 5
  claim := fun _ =>
    ∀ (γ β ω : ℝ), 0 < γ → 0 < β → 0 < ω →
      let θ_eq := boltzmannTheta β ω
      (ratePlus γ θ_eq = Real.exp (-β * ω) * rateMinus γ θ_eq ∧
       (∀ t : ℝ, (∀ ρ₀, InOpenBlochBall ρ₀ → InOpenBlochBall (thermalSemigroupC γ ω θ_eq t ρ₀)) ↔ 0 ≤ t)) ∧
      ((∀ ρ, InOpenBlochBall ρ →
          umegakiDiv ρ (gibbsDensityC θ_eq) =
            coherenceRelEntropy ρ + bregmanPhi (blochZ ρ) (meanSpin θ_eq)) ∧
       (∀ ρ₀, IsSelfAdjoint ρ₀ → Matrix.trace ρ₀ = 1 →
          (IsAffineGibbsChord γ ω θ_eq ρ₀ ↔
            coherenceSq ρ₀ = 0 ∨ (blochZ ρ₀ = meanSpin θ_eq ∧ ω = 0)))) ∧
      (∀ ρ₀, InOpenBlochBall ρ₀ →
          (∀ t ≥ 0,
            let ρ_t := thermalSemigroupC γ ω θ_eq t ρ₀
            HasDerivAt (fun s => umegakiDiv (thermalSemigroupC γ ω θ_eq s ρ₀) (gibbsDensityC θ_eq))
              (-spohnDissipation3D γ θ_eq ρ_t) t) ∧
          (0 ≤ spohnDissipation3D γ θ_eq ρ₀ ∧
           (spohnDissipation3D γ θ_eq ρ₀ = 0 ↔ ρ₀ = gibbsDensityC θ_eq)) ∧
          Filter.Tendsto (fun t => umegakiDiv (thermalSemigroupC γ ω θ_eq t ρ₀) (gibbsDensityC θ_eq))
            Filter.atTop (nhds 0) ∧
          (∀ i j, Filter.Tendsto (fun t => thermalSemigroupC γ ω θ_eq t ρ₀ i j)
            Filter.atTop (nhds (gibbsDensityC θ_eq i j))))
  evidence := fun _ γ β ω hγ hβ hω =>
    master_welded_3d_quantum_spohn_coagulation γ β ω hγ hβ hω

#register_archetype weldedQuantumSpohnSynthesisArchetype
#audit_archetype weldedQuantumSpohnSynthesisArchetype

end InfoGeometry.Modular.WeldedBlochQuantumSpohnSynthesis
