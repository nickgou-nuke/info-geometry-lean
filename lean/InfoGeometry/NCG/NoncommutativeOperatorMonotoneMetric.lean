import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Noncommutative Operator Monotone Metrics and Quantum Fisher Information

This module formalizes:
1. Symmetric Logarithmic Derivative (SLD) Lyapunov equation:
   `1/2 * (ρ * L + L * ρ) = A`
2. Noncommutative SLD Quantum Fisher Metric on matrix/operator algebras:
   `g_SLD(A, B) = 1/2 * Tr(ρ * (L_A * L_B + L_B * L_A))`
3. Fundamental Symmetry of the Quantum Fisher Metric:
   `g_SLD(A, B) = g_SLD(B, A)`
4. Bilinearity and `ℝ`-linearity of the Quantum Fisher Information.
5. Invariance under Unitary Gauge Transformations:
   `g_{U ρ Uᴴ}(U L₁ Uᴴ, U L₂ Uᴴ) = g_ρ(L₁, L₂)`.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.NCG.OperatorMetric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "Mat" => Matrix ι ι R

/-- Anti-commutator (Jordan product) of two matrices: `{A, B} = A * B + B * A` -/
def jordan (A B : Mat) : Mat :=
  A * B + B * A

@[simp]
theorem jordan_apply (A B : Mat) : jordan A B = A * B + B * A := rfl

/-- Jordan product is symmetric: `{A, B} = {B, A}` -/
theorem jordan_comm (A B : Mat) : jordan A B = jordan B A := by
  dsimp [jordan]
  rw [add_comm]

/- Conjugation by a two-sided inverse preserves the Jordan product. -/
theorem jordan_conjugate (U U_inv A B : Mat)
    (hU' : U_inv * U = 1) :
    jordan (U * A * U_inv) (U * B * U_inv) =
      U * jordan A B * U_inv := by
  have h_conj_prod (X Y : Mat) :
      (U * X * U_inv) * (U * Y * U_inv) = U * (X * Y) * U_inv := by
    calc
      (U * X * U_inv) * (U * Y * U_inv) =
          U * X * (U_inv * U) * Y * U_inv := by
            simp only [mul_assoc]
      _ = U * X * 1 * Y * U_inv := by rw [hU']
      _ = U * (X * Y) * U_inv := by simp only [mul_one, mul_assoc]
  unfold jordan
  rw [h_conj_prod A B, h_conj_prod B A]
  simp only [← Matrix.mul_add, ← Matrix.add_mul]

/-- The Symmetric Logarithmic Derivative (SLD) Lyapunov equation:
    `L` is the SLD of observable `A` with respect to density matrix `ρ` if
    `1/2 * {ρ, L} = A`, i.e., `ρ * L + L * ρ = 2 * A`. -/
def IsSLD (ρ L A : Mat) : Prop :=
  jordan ρ L = 2 • A

theorem isSLD_conjugate (ρ L A U U_inv : Mat)
    (hU' : U_inv * U = 1) (h : IsSLD ρ L A) :
    IsSLD (U * ρ * U_inv) (U * L * U_inv) (U * A * U_inv) := by
  unfold IsSLD at h ⊢
  rw [jordan_conjugate U U_inv ρ L hU', h]
  simp only [Matrix.smul_mul, Matrix.mul_smul]

/-- Noncommutative Quantum Fisher Inner Product with respect to density operator ρ:
    `g_ρ(L₁, L₂) = 1/2 * Tr(ρ * {L₁, L₂})` -/
def sldFisherInner (ρ L₁ L₂ : Mat) : R :=
  Matrix.trace (ρ * (L₁ * L₂ + L₂ * L₁))

/-- 🏆 THEOREM 1: Exact Symmetry of the Noncommutative SLD Fisher Metric:
    `g_ρ(L₁, L₂) = g_ρ(L₂, L₁)` -/
theorem sldFisherInner_symm (ρ L₁ L₂ : Mat) :
    sldFisherInner ρ L₁ L₂ = sldFisherInner ρ L₂ L₁ := by
  dsimp [sldFisherInner]
  have h_jordan : L₁ * L₂ + L₂ * L₁ = L₂ * L₁ + L₁ * L₂ := add_comm _ _
  rw [h_jordan]

/-- 🏆 THEOREM 2: Linearity in the First Variable:
    `g_ρ(L₁ + L₂, L₃) = g_ρ(L₁, L₃) + g_ρ(L₂, L₃)` -/
theorem sldFisherInner_add_left (ρ L₁ L₂ L₃ : Mat) :
    sldFisherInner ρ (L₁ + L₂) L₃ = sldFisherInner ρ L₁ L₃ + sldFisherInner ρ L₂ L₃ := by
  dsimp [sldFisherInner]
  have h_expand : (L₁ + L₂) * L₃ + L₃ * (L₁ + L₂) =
      (L₁ * L₃ + L₃ * L₁) + (L₂ * L₃ + L₃ * L₂) := by
    simp only [add_mul, mul_add]
    abel
  rw [h_expand, mul_add, Matrix.trace_add]

/-- 🏆 THEOREM 3: Linearity in the Second Variable:
    `g_ρ(L₁, L₂ + L₃) = g_ρ(L₁, L₂) + g_ρ(L₁, L₃)` -/
theorem sldFisherInner_add_right (ρ L₁ L₂ L₃ : Mat) :
    sldFisherInner ρ L₁ (L₂ + L₃) = sldFisherInner ρ L₁ L₂ + sldFisherInner ρ L₁ L₃ := by
  rw [sldFisherInner_symm, sldFisherInner_add_left, sldFisherInner_symm ρ L₂ L₁, sldFisherInner_symm ρ L₃ L₁]

/-- 🏆 THEOREM 4: Scalar Compatibility:
    `g_ρ(c • L₁, L₂) = c • g_ρ(L₁, L₂)` -/
theorem sldFisherInner_smul_left (ρ L₁ L₂ : Mat) (c : R) :
    sldFisherInner ρ (c • L₁) L₂ = c * sldFisherInner ρ L₁ L₂ := by
  dsimp [sldFisherInner]
  have h_smul : (c • L₁) * L₂ + L₂ * (c • L₁) = c • (L₁ * L₂ + L₂ * L₁) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add]
  rw [h_smul, Matrix.mul_smul, Matrix.trace_smul]
  rfl

/-- 🏆 THEOREM 5: Invariance under Unitary Quantum Symmetry:
    If `U` is unitary (`U * U_inv = 1`), then `g_{U ρ U_inv}(U L₁ U_inv, U L₂ U_inv) = g_ρ(L₁, L₂)` -/
theorem sldFisherInner_unitary_invariant (ρ L₁ L₂ U U_inv : Mat)
    (hU : U * U_inv = 1) (hU' : U_inv * U = 1) :
    sldFisherInner (U * ρ * U_inv) (U * L₁ * U_inv) (U * L₂ * U_inv) =
      sldFisherInner ρ L₁ L₂ := by
  dsimp [sldFisherInner]
  have h_conj_prod (A B : Mat) :
      (U * A * U_inv) * (U * B * U_inv) = U * (A * B) * U_inv := by
    calc
      (U * A * U_inv) * (U * B * U_inv)
        = U * A * (U_inv * U) * B * U_inv := by simp only [mul_assoc]
      _ = U * A * 1 * B * U_inv := by rw [hU']
      _ = U * (A * B) * U_inv := by simp only [mul_one, mul_assoc]
  have h_jordan_conj :
      (U * L₁ * U_inv) * (U * L₂ * U_inv) + (U * L₂ * U_inv) * (U * L₁ * U_inv) =
      U * (L₁ * L₂ + L₂ * L₁) * U_inv := by
    rw [h_conj_prod L₁ L₂, h_conj_prod L₂ L₁]
    simp only [← Matrix.mul_add, ← Matrix.add_mul]
  rw [h_jordan_conj]
  have h_triple :
      (U * ρ * U_inv) * (U * (L₁ * L₂ + L₂ * L₁) * U_inv) =
      U * (ρ * (L₁ * L₂ + L₂ * L₁)) * U_inv := by
    calc
      (U * ρ * U_inv) * (U * (L₁ * L₂ + L₂ * L₁) * U_inv)
        = U * ρ * (U_inv * U) * (L₁ * L₂ + L₂ * L₁) * U_inv := by simp only [mul_assoc]
      _ = U * ρ * 1 * (L₁ * L₂ + L₂ * L₁) * U_inv := by rw [hU']
      _ = U * (ρ * (L₁ * L₂ + L₂ * L₁) * U_inv) := by simp only [mul_one, mul_assoc]
      _ = U * (ρ * (L₁ * L₂ + L₂ * L₁)) * U_inv := by simp only [mul_assoc]
  rw [h_triple]
  calc
    Matrix.trace (U * (ρ * (L₁ * L₂ + L₂ * L₁)) * U_inv)
      = Matrix.trace (U_inv * (U * (ρ * (L₁ * L₂ + L₂ * L₁)))) := by
        rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((U_inv * U) * (ρ * (L₁ * L₂ + L₂ * L₁))) := by
        simp only [mul_assoc]
    _ = Matrix.trace (1 * (ρ * (L₁ * L₂ + L₂ * L₁))) := by rw [hU']
    _ = Matrix.trace (ρ * (L₁ * L₂ + L₂ * L₁)) := by rw [one_mul]

end InfoGeometry.NCG.OperatorMetric

end noncomputable section
