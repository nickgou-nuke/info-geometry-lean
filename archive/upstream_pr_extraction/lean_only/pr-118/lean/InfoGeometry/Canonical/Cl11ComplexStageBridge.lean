import InfoGeometry.Clifford.Cl11TensorTower

/-!
# Complexification of the concrete real Cl(1,1) matrix stages

This owner supplies only the coefficient extension needed before a filtered
complex GNS instantiation.  It does not install C*-algebra instances on the
real stages and does not change the existing real tensor-tower colimit.
-/

namespace InfoGeometry.Canonical.Cl11ComplexStageBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open scoped Kronecker

abbrev ComplexMatStage (n : ℕ) : Type :=
  Matrix (Idx n) (Idx n) ℂ

noncomputable def complexifyStage (n : ℕ) : MatStage n →+* ComplexMatStage n :=
  RingHom.mapMatrix (algebraMap ℝ ℂ)

noncomputable def complexStageEmbed (n : ℕ) :
    ComplexMatStage n →+* ComplexMatStage (n + 1) where
  toFun A := A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := by
    exact
      (Matrix.one_kronecker_one :
        (1 : ComplexMatStage n) ⊗ₖ
            (1 : Matrix (Fin 2) (Fin 2) ℂ) =
          (1 : ComplexMatStage (n + 1)))
  map_mul' A B := by
    simpa using
      (Matrix.mul_kronecker_mul A B
        (1 : Matrix (Fin 2) (Fin 2) ℂ)
        (1 : Matrix (Fin 2) (Fin 2) ℂ))
  map_zero' := by simp
  map_add' A B := by simp [Matrix.add_kronecker]

noncomputable def complexNormalizedTrace (n : ℕ) : ComplexMatStage n →ₗ[ℂ] ℂ where
  toFun A := (2 ^ n : ℂ)⁻¹ * Matrix.trace A
  map_add' A B := by
    simp only [Matrix.trace_add]
    rw [mul_add]
  map_smul' c A := by
    simp only [Matrix.trace_smul]
    simp only [smul_eq_mul, RingHom.id_apply]
    ac_rfl

@[simp] theorem complexNormalizedTrace_apply (n : ℕ)
    (A : ComplexMatStage n) :
    complexNormalizedTrace n A = (2 ^ n : ℂ)⁻¹ * Matrix.trace A := rfl

@[simp] theorem complexNormalizedTrace_one (n : ℕ) :
    complexNormalizedTrace n (1 : ComplexMatStage n) = 1 := by
  unfold complexNormalizedTrace
  simp [Matrix.trace, Matrix.diag, InfoGeometry.Clifford.TowerMatrix.idx_card_pow_two]

theorem complexNormalizedTrace_compatible (n : ℕ) (A : ComplexMatStage n) :
    complexNormalizedTrace (n + 1) (complexStageEmbed n A) =
      complexNormalizedTrace n A := by
  dsimp [complexNormalizedTrace, complexStageEmbed]
  rw [Matrix.trace_kronecker]
  simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

theorem complexNormalizedTrace_complexify (n : ℕ) (A : MatStage n) :
    complexNormalizedTrace n (complexifyStage n A) =
      Complex.ofReal (InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n A) := by
  dsimp [complexNormalizedTrace, complexifyStage]
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
  change (2 ^ n : ℂ)⁻¹ * ∑ x, Complex.ofReal (A x x) =
    Complex.ofReal (normalizedTrace n A)
  unfold InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace
  change (2 ^ n : ℂ)⁻¹ * ∑ x, Complex.ofReal (A x x) =
    Complex.ofReal ((∑ x, A x x) / (2 ^ n : ℝ))
  rw [← Complex.ofReal_sum]
  rw [Complex.ofReal_div]
  simp [div_eq_mul_inv, mul_comm]

@[simp] theorem complexStageEmbed_apply (n : ℕ) (A : ComplexMatStage n) :
    complexStageEmbed n A = A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl

@[simp] theorem complexifyStage_apply (n : ℕ) (A : MatStage n) (i j : Idx n) :
    complexifyStage n A i j = algebraMap ℝ ℂ (A i j) := by
  rfl

@[simp] theorem complexifyStage_one (n : ℕ) :
    complexifyStage n (1 : MatStage n) = 1 := by
  exact (complexifyStage n).map_one

@[simp] theorem complexifyStage_mul (n : ℕ) (A B : MatStage n) :
    complexifyStage n (A * B) =
      complexifyStage n A * complexifyStage n B := by
  exact (complexifyStage n).map_mul A B

@[simp] theorem complexifyStage_add (n : ℕ) (A B : MatStage n) :
    complexifyStage n (A + B) =
      complexifyStage n A + complexifyStage n B := by
  exact (complexifyStage n).map_add A B

@[simp] theorem complexifyStage_stageEmbed (n : ℕ) (A : MatStage n) :
    complexifyStage (n + 1) (stageEmbed n A) =
      (stageEmbed n A).map (algebraMap ℝ ℂ) := rfl

theorem complexifyStage_compatible (n : ℕ) (A : MatStage n) :
    complexifyStage (n + 1) (stageEmbed n A) =
      complexStageEmbed n (complexifyStage n A) := by
  ext i j
  by_cases h : A i.1 j.1 = 0
  · simp [complexifyStage, complexStageEmbed, stageEmbed,
      InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed,
      Matrix.kroneckerMap_apply, Matrix.map_apply, h]
  · simp [complexifyStage, complexStageEmbed, stageEmbed,
      InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed,
      Matrix.kroneckerMap_apply, Matrix.map_apply, h]
    · by_cases h' : i.2 = j.2 <;> simp [Matrix.one_apply, h']

end InfoGeometry.Canonical.Cl11ComplexStageBridge
