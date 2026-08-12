import Mathlib
import proofs.NambuGorkovSpinor

open Matrix

noncomputable section

/-!
# Bogoliubov-Rindler Flow and Thermo Field Dynamics

This module formally constructs the O(2,2) Bogoliubov transformation 
as a one-parameter Lie group acting on the Cartan-Krein doubled space.
-/

/-- 
A Bogoliubov transformation parameterized by the hyperbolic angle (rapidity) θ.
This operator mixes the creation (signal) and annihilation (thermal dual) spaces.
-/
noncomputable def bogoliubovTransform (θ : ℝ) : Matrix4x4 :=
  fromBlocks 
    (Real.cosh θ • (1 : Patch2x2)) 
    (Real.sinh θ • (1 : Patch2x2))
    (Real.sinh θ • (1 : Patch2x2)) 
    (Real.cosh θ • (1 : Patch2x2))

/-- 
Theorem: The Bogoliubov transformation exactly preserves the 
indefinite Krein metric. It acts as an O(2,2) isometry.
-/
theorem bogoliubov_preserves_kreinMetric (θ : ℝ) :
    kreinAdjoint (bogoliubovTransform θ) * bogoliubovTransform θ = 1 := by
  dsimp [kreinAdjoint, bogoliubovTransform, kreinMetric]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [fromBlocks, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.cosh_sq_sub_sinh_sq θ]

theorem bogoliubov_preserves_kreinInnerProduct
    (θ : ℝ)
    (Ψ Φ : Spinor) :
    kreinInnerProduct
        (bogoliubovTransform θ *ᵥ Ψ)
        (bogoliubovTransform θ *ᵥ Φ) =
      kreinInnerProduct Ψ Φ := by
  dsimp [kreinInnerProduct, bogoliubovTransform, kreinMetric]
  simp [fromBlocks_mulVec, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    vecMul, Fintype.sum_sum_type, fromBlocks]
  linear_combination
    (Real.cosh_sq_sub_sinh_sq θ) *
      (Ψ (Sum.inl 0) * Φ (Sum.inl 0) - Ψ (Sum.inr 0) * Φ (Sum.inr 0) +
       Ψ (Sum.inl 1) * Φ (Sum.inl 1) - Ψ (Sum.inr 1) * Φ (Sum.inr 1))

/--
A vector is Krein-null when its indefinite quadratic norm vanishes.
-/
def IsKreinNull (Ψ : Spinor) : Prop :=
  kreinInnerProduct Ψ Ψ = 0

/--
The Bogoliubov boost preserves the Krein null cone.
-/
theorem bogoliubov_preserves_kreinNull
    (θ : ℝ)
    (Ψ : Spinor)
    (h : IsKreinNull Ψ) :
    IsKreinNull
      (bogoliubovTransform θ *ᵥ Ψ) := by
  unfold IsKreinNull at *
  rw [bogoliubov_preserves_kreinInnerProduct]
  exact h

theorem bogoliubov_zero :
    bogoliubovTransform 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bogoliubovTransform, fromBlocks]

theorem bogoliubov_add
    (θ φ : ℝ) :
    bogoliubovTransform (θ + φ) =
      bogoliubovTransform θ *
        bogoliubovTransform φ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bogoliubovTransform, fromBlocks,
      Matrix.mul_apply, Real.cosh_add, Real.sinh_add]
  all_goals ring

theorem bogoliubov_neg_mul
    (θ : ℝ) :
    bogoliubovTransform (-θ) *
        bogoliubovTransform θ =
      1 := by
  rw [← bogoliubov_add]
  simp [bogoliubov_zero]

theorem bogoliubov_mul_neg
    (θ : ℝ) :
    bogoliubovTransform θ *
        bogoliubovTransform (-θ) =
      1 := by
  rw [← bogoliubov_add]
  simp [bogoliubov_zero]

theorem kreinAdjoint_bogoliubov
    (θ : ℝ) :
    kreinAdjoint (bogoliubovTransform θ) =
      bogoliubovTransform (-θ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [kreinAdjoint, kreinMetric, bogoliubovTransform, fromBlocks,
      Matrix.mul_apply, Matrix.conjTranspose, Fin.sum_univ_two,
      Real.sinh_neg, Real.cosh_neg] <;>
    ring

theorem bogoliubov_krein_unitary
    (θ : ℝ) :
    kreinAdjoint (bogoliubovTransform θ) *
        bogoliubovTransform θ =
      1 := by
  rw [kreinAdjoint_bogoliubov]
  exact bogoliubov_neg_mul θ

def bogoliubovGenerator : Matrix4x4 :=
  fromBlocks
    (0 : Patch2x2)
    (1 : Patch2x2)
    (1 : Patch2x2)
    (0 : Patch2x2)

theorem bogoliubovGenerator_sq :
    bogoliubovGenerator * bogoliubovGenerator = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bogoliubovGenerator, fromBlocks, Matrix.mul_apply]

theorem kreinAdjoint_bogoliubovGenerator :
    kreinAdjoint bogoliubovGenerator =
      -bogoliubovGenerator := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [kreinAdjoint, kreinMetric, bogoliubovGenerator, fromBlocks,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem bogoliubovTransform_eq
    (θ : ℝ) :
    bogoliubovTransform θ =
      Real.cosh θ • (1 : Matrix4x4) +
        Real.sinh θ • bogoliubovGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bogoliubovTransform,
      bogoliubovGenerator, fromBlocks]

structure BogoliubovRindlerFlowData where
  transform : ℝ → Matrix4x4
  generator : Matrix4x4
  map_zero :
    transform 0 = 1
  map_add :
    ∀ θ φ, transform (θ + φ) = transform θ * transform φ
  kreinAdjoint_eq_neg :
    ∀ θ, kreinAdjoint (transform θ) = transform (-θ)
  generator_sq :
    generator * generator = 1
  generator_krein_skew :
    kreinAdjoint generator = -generator
  closed_form :
    ∀ θ,
      transform θ =
        Real.cosh θ • (1 : Matrix4x4) +
        Real.sinh θ • generator

def canonicalBogoliubovRindlerFlow :
    BogoliubovRindlerFlowData where
  transform := bogoliubovTransform
  generator := bogoliubovGenerator
  map_zero := bogoliubov_zero
  map_add := bogoliubov_add
  kreinAdjoint_eq_neg := kreinAdjoint_bogoliubov
  generator_sq := bogoliubovGenerator_sq
  generator_krein_skew :=
    kreinAdjoint_bogoliubovGenerator
  closed_form := bogoliubovTransform_eq

end
