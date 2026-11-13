/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic

namespace InfoGeometry.Clifford

variable {B : Type*} [Ring B]

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem operatorValuedJones_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

def I_mat : Matrix (Fin 2) (Fin 2) B := !![1, 0; 0, 1]
def Gamma_mat : Matrix (Fin 2) (Fin 2) B := !![1, 0; 0, -1]
def J_mat : Matrix (Fin 2) (Fin 2) B := !![0, 1; 1, 0]
def K_mat : Matrix (Fin 2) (Fin 2) B := !![0, 1; -1, 0]

@[simp] theorem Gamma_sq : Gamma_mat (B := B) * Gamma_mat = I_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gamma_mat, I_mat, Matrix.mul_apply]

@[simp] theorem J_sq : J_mat (B := B) * J_mat = I_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_mat, I_mat, Matrix.mul_apply]

@[simp] theorem K_sq : K_mat (B := B) * K_mat = - I_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K_mat, I_mat, Matrix.mul_apply]

theorem J_Gamma : J_mat (B := B) * Gamma_mat = -(Gamma_mat * J_mat) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_mat, Gamma_mat, Matrix.mul_apply]

theorem J_Gamma_anticomm :
    J_mat (B := B) * Gamma_mat (B := B) + Gamma_mat (B := B) * J_mat (B := B) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_mat, Gamma_mat, Matrix.mul_apply]

theorem K_eq_Gamma_J : K_mat (B := B) = Gamma_mat * J_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K_mat, Gamma_mat, J_mat, Matrix.mul_apply]

/-- Reconstruction of an operator in M₂(B) from its four B-valued Stokes components. -/
def reconstruct_jones (a0 a3 a1 a2 : B) : Matrix (Fin 2) (Fin 2) B :=
  a0 • I_mat + a3 • Gamma_mat + a1 • J_mat + a2 • K_mat

/-- The fundamental decomposition mapping abstract Stokes coordinate entries onto the Cl(1, 1) sheet grading. -/
theorem jones_decomposition_eq (a0 a3 a1 a2 : B) :
    reconstruct_jones a0 a3 a1 a2 = !![a0 + a3, a1 + a2; a1 - a2, a0 - a3] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [reconstruct_jones, I_mat, Gamma_mat, J_mat, K_mat] <;> abel

/-! ## Complex circular coordinates with operator coefficients -/

/-- A sheet packet with coefficients in an arbitrary complex module `B`.
When `B = Module.End ℂ W`, these are operator-valued rather than scalar
coordinates. -/
@[ext] structure CausalOperatorCoordinates (B : Type*) where
  scalar : B
  chiral : B
  exchange : B
  circular : B

section ComplexCoordinates

variable [Module ℂ B]

/--
Reconstruction in the ordered causal packet `(1, Γ, J, -i ΓJ)`.
The entrywise form is valid for noncommuting operator coefficients because no
products between distinct coefficients are introduced.
-/
def reconstruct_causal (A : CausalOperatorCoordinates B) :
    Matrix (Fin 2) (Fin 2) B :=
  !![A.scalar + A.chiral, A.exchange - Complex.I • A.circular;
     A.exchange + Complex.I • A.circular, A.scalar - A.chiral]

/-- Extract the four operator-valued causal coordinates of a sheet matrix. -/
noncomputable def causalCoordinates (A : Matrix (Fin 2) (Fin 2) B) :
    CausalOperatorCoordinates B where
  scalar := (1 / 2 : ℂ) • (A 0 0 + A 1 1)
  chiral := (1 / 2 : ℂ) • (A 0 0 - A 1 1)
  exchange := (1 / 2 : ℂ) • (A 0 1 + A 1 0)
  circular := (Complex.I / 2 : ℂ) • (A 0 1 - A 1 0)

/-- Every operator-valued sheet matrix is recovered from its causal coordinates. -/
@[simp] theorem reconstruct_causalCoordinates
    (A : Matrix (Fin 2) (Fin 2) B) :
    reconstruct_causal (causalCoordinates A) = A := by
  have hIhalf : Complex.I * (Complex.I / 2) = -(1 / 2 : ℂ) := by
    rw [div_eq_mul_inv, ← mul_assoc, Complex.I_mul_I]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reconstruct_causal, causalCoordinates, smul_smul, hIhalf] <;>
    module

/-- Causal coordinates are unique. -/
@[simp] theorem causalCoordinates_reconstruct
    (A : CausalOperatorCoordinates B) :
    causalCoordinates (reconstruct_causal A) = A := by
  rcases A with ⟨A0, A3, A1, A2⟩
  apply CausalOperatorCoordinates.ext
  · change (1 / 2 : ℂ) • ((A0 + A3) + (A0 - A3)) = A0
    rw [show (A0 + A3) + (A0 - A3) = (2 : ℂ) • A0 by module]
    simp [smul_smul]
  · change (1 / 2 : ℂ) • ((A0 + A3) - (A0 - A3)) = A3
    rw [show (A0 + A3) - (A0 - A3) = (2 : ℂ) • A3 by module]
    simp [smul_smul]
  · change (1 / 2 : ℂ) •
      ((A1 - Complex.I • A2) + (A1 + Complex.I • A2)) = A1
    rw [show (A1 - Complex.I • A2) + (A1 + Complex.I • A2) =
      (2 : ℂ) • A1 by module]
    simp [smul_smul]
  · change (Complex.I / 2 : ℂ) •
      ((A1 - Complex.I • A2) - (A1 + Complex.I • A2)) = A2
    rw [show (A1 - Complex.I • A2) - (A1 + Complex.I • A2) =
      (-2 * Complex.I : ℂ) • A2 by module]
    rw [smul_smul]
    have hc : (Complex.I / 2 : ℂ) * (-2 * Complex.I) = 1 := by
      field_simp
      rw [Complex.I_sq]
      norm_num
    rw [hc, one_smul]

/-- The causal packet is exactly the full operator-valued `2 × 2` space. -/
noncomputable def causalOperatorCoordinatesEquiv :
    CausalOperatorCoordinates B ≃ Matrix (Fin 2) (Fin 2) B where
  toFun := reconstruct_causal
  invFun := causalCoordinates
  left_inv := causalCoordinates_reconstruct
  right_inv := reconstruct_causalCoordinates

/-- The requested specialization `M₂(End W)` of the coefficient theorem. -/
abbrev SheetEndomorphismMatrix
    (W : Type*) [AddCommMonoid W] [Module ℂ W] :=
  Matrix (Fin 2) (Fin 2) (Module.End ℂ W)

end ComplexCoordinates

/-! ## Strict Dirac/Clifford theorem boundary -/

section DiracBoundary

variable {ι R Op : Type*}

/-- Anticommutator in the represented operator algebra. -/
def operatorAnticommutator [Semiring Op] (A C : Op) : Op := A * C + C * A

variable [CommSemiring R] [Semiring Op] [Algebra R Op]

/--
An operator family is a Dirac-matrix system precisely when the metric
anticommutation relation is supplied. Coordinate expansion alone does not
construct a value of this predicate.
-/
def IsDiracMatrixSystem (g : ι → ι → R) (gamma : ι → Op) : Prop :=
  ∀ a b, operatorAnticommutator (gamma a) (gamma b) =
    algebraMap R Op (2 * g a b)

/-- Read back one Clifford relation from a proved Dirac-matrix system. -/
theorem anticommutator_eq_metric
    {g : ι → ι → R} {gamma : ι → Op}
    (h : IsDiracMatrixSystem g gamma) (a b : ι) :
    operatorAnticommutator (gamma a) (gamma b) =
      algebraMap R Op (2 * g a b) :=
  h a b

end DiracBoundary

/-! ## Iterated operator coefficients and the quaternion Lie triple -/

section NestedQuaternionOperators

variable {B : Type*} [Ring B]

/-- A two-stage operator matrix algebra.  Its coefficient ring is itself the
noncommutative operator ring `M₂(B)`. -/
abbrev NestedOperatorMatrix :=
  Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-- The first negative-square generator, acting on the outer operator index. -/
def quaternionE₁ : NestedOperatorMatrix (B := B) :=
  K_mat (B := Matrix (Fin 2) (Fin 2) B)

/-- The second negative-square generator is the Klein twist of the inner
negative-square operator. -/
def quaternionE₂ : NestedOperatorMatrix (B := B) :=
  !![K_mat, 0; 0, -K_mat]

/-- The third quaternion generator is the ordered product `E₁ E₂`. -/
def quaternionE₃ : NestedOperatorMatrix (B := B) :=
  quaternionE₁ * quaternionE₂

/-- The two generators square to `-1` and anticommute, with no commutativity
assumption on the coefficient ring `B`. -/
theorem quaternionE₁_E₂_relations :
    quaternionE₁ (B := B) * quaternionE₁ = -1 ∧
    quaternionE₂ (B := B) * quaternionE₂ = -1 ∧
    quaternionE₁ (B := B) * quaternionE₂ +
      quaternionE₂ (B := B) * quaternionE₁ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    ext i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [quaternionE₁, quaternionE₂, K_mat,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- The ordered product is also negative-square. -/
theorem quaternionE₃_sq :
    quaternionE₃ (B := B) * quaternionE₃ (B := B) = -1 := by
  rcases quaternionE₁_E₂_relations (B := B) with ⟨h₁, h₂, h₁₂⟩
  have h₂₁ : quaternionE₂ (B := B) * quaternionE₁ =
      -(quaternionE₁ (B := B) * quaternionE₂ (B := B)) := by
    calc
      quaternionE₂ * quaternionE₁ =
          (quaternionE₁ * quaternionE₂ + quaternionE₂ * quaternionE₁) -
            quaternionE₁ (B := B) * quaternionE₂ (B := B) := by noncomm_ring
      _ = -(quaternionE₁ (B := B) * quaternionE₂ (B := B)) := by rw [h₁₂]; noncomm_ring
  dsimp [quaternionE₃]
  calc
    (quaternionE₁ (B := B) * quaternionE₂) * (quaternionE₁ * quaternionE₂) =
        quaternionE₁ * (quaternionE₂ * quaternionE₁) * quaternionE₂ := by noncomm_ring
    _ = quaternionE₁ * (-(quaternionE₁ * quaternionE₂)) * quaternionE₂ := by rw [h₂₁]
    _ = -((quaternionE₁ * quaternionE₁) * (quaternionE₂ * quaternionE₂)) := by noncomm_ring
    _ = -((-1) * (-1)) := by rw [h₁, h₂]
    _ = -1 := by noncomm_ring

/-- The first associative commutator of the embedded quaternion triple is
twice its ordered product. -/
theorem quaternionE₁_E₂_commutator :
    quaternionE₁ (B := B) * quaternionE₂ (B := B) -
        quaternionE₂ (B := B) * quaternionE₁ (B := B) =
        2 • quaternionE₃ (B := B) := by
  rcases quaternionE₁_E₂_relations (B := B) with ⟨h₁, h₂, h₁₂⟩
  have h₂₁ : quaternionE₂ (B := B) * quaternionE₁ =
      -(quaternionE₁ (B := B) * quaternionE₂ (B := B)) := by
    calc
      quaternionE₂ * quaternionE₁ =
          (quaternionE₁ * quaternionE₂ + quaternionE₂ * quaternionE₁) -
            quaternionE₁ (B := B) * quaternionE₂ (B := B) := by noncomm_ring
      _ = -(quaternionE₁ (B := B) * quaternionE₂ (B := B)) := by rw [h₁₂]; noncomm_ring
  dsimp [quaternionE₃]
  rw [h₂₁, two_smul]
  noncomm_ring

/-- The cyclic bracket of the second and third quaternion generators. -/
theorem quaternionE₂_E₃_commutator :
    quaternionE₂ (B := B) * quaternionE₃ (B := B) -
        quaternionE₃ (B := B) * quaternionE₂ (B := B) =
        2 • quaternionE₁ (B := B) := by
  rcases quaternionE₁_E₂_relations (B := B) with ⟨h₁, h₂, h₁₂⟩
  have h₂₁ : quaternionE₂ (B := B) * quaternionE₁ (B := B) =
      -(quaternionE₁ (B := B) * quaternionE₂ (B := B)) := by
    calc
      quaternionE₂ (B := B) * quaternionE₁ (B := B) =
          (quaternionE₁ (B := B) * quaternionE₂ (B := B) +
            quaternionE₂ (B := B) * quaternionE₁ (B := B)) -
            quaternionE₁ (B := B) * quaternionE₂ (B := B) := by noncomm_ring
      _ = -(quaternionE₁ * quaternionE₂) := by rw [h₁₂]; noncomm_ring
  have hleft : quaternionE₂ (B := B) * (quaternionE₁ (B := B) *
      quaternionE₂ (B := B)) = quaternionE₁ (B := B) := by
    calc
      quaternionE₂ (B := B) * (quaternionE₁ (B := B) * quaternionE₂ (B := B)) =
          (quaternionE₂ (B := B) * quaternionE₁ (B := B)) * quaternionE₂ (B := B) := by noncomm_ring
      _ = -(quaternionE₁ (B := B) * quaternionE₂ (B := B)) * quaternionE₂ (B := B) := by rw [h₂₁]
      _ = -(quaternionE₁ (B := B) * (quaternionE₂ (B := B) * quaternionE₂ (B := B))) := by noncomm_ring
      _ = quaternionE₁ := by rw [h₂]; noncomm_ring
  have hright : (quaternionE₁ (B := B) * quaternionE₂ (B := B)) *
      quaternionE₂ (B := B) = -quaternionE₁ (B := B) := by
    calc
      (quaternionE₁ (B := B) * quaternionE₂ (B := B)) * quaternionE₂ (B := B) =
          quaternionE₁ (B := B) * (quaternionE₂ (B := B) * quaternionE₂ (B := B)) := by noncomm_ring
      _ = quaternionE₁ (B := B) * (-1) := by rw [h₂]
      _ = -quaternionE₁ := by noncomm_ring
  dsimp [quaternionE₃]
  rw [hleft, hright, two_smul]
  noncomm_ring

/-- The cyclic bracket of the third and first quaternion generators. -/
theorem quaternionE₃_E₁_commutator :
    quaternionE₃ (B := B) * quaternionE₁ (B := B) -
        quaternionE₁ (B := B) * quaternionE₃ (B := B) =
        2 • quaternionE₂ (B := B) := by
  rcases quaternionE₁_E₂_relations (B := B) with ⟨h₁, h₂, h₁₂⟩
  have h₂₁ : quaternionE₂ (B := B) * quaternionE₁ (B := B) =
      -(quaternionE₁ (B := B) * quaternionE₂ (B := B)) := by
    calc
      quaternionE₂ (B := B) * quaternionE₁ (B := B) =
          (quaternionE₁ (B := B) * quaternionE₂ (B := B) +
            quaternionE₂ (B := B) * quaternionE₁ (B := B)) -
            quaternionE₁ (B := B) * quaternionE₂ (B := B) := by noncomm_ring
      _ = -(quaternionE₁ * quaternionE₂) := by rw [h₁₂]; noncomm_ring
  have hleft : (quaternionE₁ (B := B) * quaternionE₂ (B := B)) *
      quaternionE₁ (B := B) = quaternionE₂ (B := B) := by
    calc
      (quaternionE₁ (B := B) * quaternionE₂ (B := B)) * quaternionE₁ (B := B) =
          quaternionE₁ (B := B) * (quaternionE₂ (B := B) * quaternionE₁ (B := B)) := by noncomm_ring
      _ = quaternionE₁ (B := B) * (-(quaternionE₁ (B := B) * quaternionE₂ (B := B))) := by rw [h₂₁]
      _ = -((quaternionE₁ (B := B) * quaternionE₁ (B := B)) * quaternionE₂ (B := B)) := by noncomm_ring
      _ = quaternionE₂ := by rw [h₁]; noncomm_ring
  have hright : quaternionE₁ (B := B) * (quaternionE₁ (B := B) *
      quaternionE₂ (B := B)) = -quaternionE₂ (B := B) := by
    calc
      quaternionE₁ (B := B) * (quaternionE₁ (B := B) * quaternionE₂ (B := B)) =
          (quaternionE₁ (B := B) * quaternionE₁ (B := B)) * quaternionE₂ (B := B) := by noncomm_ring
      _ = (-1) * quaternionE₂ (B := B) := by rw [h₁]
      _ = -quaternionE₂ := by noncomm_ring
  dsimp [quaternionE₃]
  rw [hleft, hright, two_smul]
  noncomm_ring

/-- The unnormalised Cayley elements associated to two quaternion directions. -/
def quaternionRotorPlus (E : NestedOperatorMatrix (B := B)) := 1 + E

def quaternionRotorMinus (E : NestedOperatorMatrix (B := B)) := 1 - E

/-- The two unnormalised Cayley factors multiply to twice the identity on
either side. The statement records the normalization needed before treating
the sandwich as a conjugation. -/
theorem quaternionRotor_product_E₁ :
    quaternionRotorPlus (quaternionE₁ (B := B)) *
        quaternionRotorMinus (quaternionE₁ (B := B)) = 1 + 1 ∧
      quaternionRotorMinus (quaternionE₁ (B := B)) *
        quaternionRotorPlus (quaternionE₁ (B := B)) = 1 + 1 := by
  have hsq := quaternionE₁_E₂_relations (B := B)
  have h₁ : quaternionE₁ (B := B) * quaternionE₁ (B := B) = -1 := hsq.1
  dsimp [quaternionRotorPlus, quaternionRotorMinus]
  constructor
  · calc
      (1 + quaternionE₁ (B := B)) * (1 - quaternionE₁ (B := B)) =
          1 - quaternionE₁ (B := B) * quaternionE₁ (B := B) := by noncomm_ring
      _ = 1 + 1 := by rw [h₁]; simp
  · calc
      (1 - quaternionE₁ (B := B)) * (1 + quaternionE₁ (B := B)) =
          1 - quaternionE₁ (B := B) * quaternionE₁ (B := B) := by noncomm_ring
      _ = 1 + 1 := by rw [h₁]; simp

/-- Distinct quaternion Cayley elements retain the noncommutative direction
of their ordered product. This is an operator-ring identity, with no
commutativity assumption on the coefficient ring. -/
theorem quaternionRotor_commutator :
    quaternionRotorPlus (quaternionE₁ (B := B)) *
        quaternionRotorPlus (quaternionE₂ (B := B)) -
      quaternionRotorPlus (quaternionE₂ (B := B)) *
        quaternionRotorPlus (quaternionE₁ (B := B)) =
      2 • quaternionE₃ (B := B) := by
  dsimp [quaternionRotorPlus]
  calc
    (1 + quaternionE₁ (B := B)) * (1 + quaternionE₂ (B := B)) -
        (1 + quaternionE₂ (B := B)) * (1 + quaternionE₁ (B := B))
        = quaternionE₁ (B := B) * quaternionE₂ (B := B) -
          quaternionE₂ (B := B) * quaternionE₁ (B := B) := by noncomm_ring
    _ = 2 • quaternionE₃ (B := B) := quaternionE₁_E₂_commutator

/-- The unnormalised Cayley sandwich rotates the second quaternion generator
to twice the third. Since the two Cayley factors multiply to `2`, this states
the exact algebraic sandwich and does not assert a normalized group action. -/
theorem quaternionRotor_sandwich_E₁_E₂ :
    quaternionRotorPlus (quaternionE₁ (B := B)) *
        quaternionE₂ (B := B) *
      quaternionRotorMinus (quaternionE₁ (B := B)) =
      2 • quaternionE₃ (B := B) := by
  rcases quaternionE₁_E₂_relations (B := B) with ⟨h₁, h₂, h₁₂⟩
  have h₂₁ : quaternionE₂ (B := B) * quaternionE₁ (B := B) =
      -(quaternionE₁ (B := B) * quaternionE₂ (B := B)) := by
    calc
      quaternionE₂ (B := B) * quaternionE₁ (B := B) =
          (quaternionE₁ (B := B) * quaternionE₂ (B := B) +
            quaternionE₂ (B := B) * quaternionE₁ (B := B)) -
            quaternionE₁ (B := B) * quaternionE₂ (B := B) := by noncomm_ring
      _ = -(quaternionE₁ (B := B) * quaternionE₂ (B := B)) := by
        rw [h₁₂]
        noncomm_ring
  have hlast : quaternionE₁ (B := B) * quaternionE₂ (B := B) *
      quaternionE₁ (B := B) = quaternionE₂ (B := B) := by
    calc
      quaternionE₁ (B := B) * quaternionE₂ (B := B) * quaternionE₁ (B := B) =
          quaternionE₁ (B := B) *
            (quaternionE₂ (B := B) * quaternionE₁ (B := B)) := by noncomm_ring
      _ = quaternionE₁ (B := B) *
            (-(quaternionE₁ (B := B) * quaternionE₂ (B := B))) := by rw [h₂₁]
      _ = quaternionE₂ (B := B) := by
        calc
          quaternionE₁ (B := B) *
              (-(quaternionE₁ (B := B) * quaternionE₂ (B := B))) =
              -(quaternionE₁ (B := B) *
                (quaternionE₁ (B := B) * quaternionE₂ (B := B))) := by
                  rw [mul_neg]
          _ = -((quaternionE₁ (B := B) * quaternionE₁ (B := B)) *
                quaternionE₂ (B := B)) := by
                  congr 1
                  noncomm_ring
          _ = quaternionE₂ (B := B) := by rw [h₁]; noncomm_ring
  dsimp [quaternionRotorPlus, quaternionRotorMinus, quaternionE₃]
  rw [two_smul]
  calc
    (1 + quaternionE₁ (B := B)) * quaternionE₂ (B := B) *
        (1 - quaternionE₁ (B := B))
        = quaternionE₂ (B := B) -
          quaternionE₂ (B := B) * quaternionE₁ (B := B) +
          quaternionE₁ (B := B) * quaternionE₂ (B := B) -
          quaternionE₁ (B := B) * quaternionE₂ (B := B) *
            quaternionE₁ (B := B) := by noncomm_ring
    _ = 2 * (quaternionE₁ (B := B) * quaternionE₂ (B := B)) := by
      rw [h₂₁, hlast]
      noncomm_ring
    _ = quaternionE₁ (B := B) * quaternionE₂ (B := B) +
        quaternionE₁ (B := B) * quaternionE₂ (B := B) := by rw [two_mul]

end NestedQuaternionOperators

end InfoGeometry.Clifford
