/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.ContinuousDerivationExponential
import InfoGeometry.OperatorAlgebra.ThermalBogoliubovCAR

/-!
# Operator-valued Möbius action on projective pairs

This is the denominator-free noncommutative form of a Möbius action.  A
projective coordinate is represented by a pair of operators, and a `2 × 2`
operator matrix acts by its native matrix-vector product.  Composition is
proved by the matrix multiplication law; no commutativity or scalar
diagonalization is used.
-/

namespace InfoGeometry.OperatorAlgebra

section

variable {A : Type*} [Semiring A]

abbrev OperatorPair (A : Type*) := Fin 2 → A
abbrev OperatorMatrix (A : Type*) := Matrix (Fin 2) (Fin 2) A

/-- Directed matrix units in the operator-valued Möbius matrix carrier. -/
def mobiusForwardUnit : OperatorMatrix A := Matrix.single 0 1 1

def mobiusBackwardUnit : OperatorMatrix A := Matrix.single 1 0 1

/-- The full operator-matrix carrier is noncommutative whenever its coefficient
semiring is nontrivial: the two directed matrix units multiply to different
diagonal matrix units. -/
theorem operatorMatrix_noncommutative [Nontrivial A] :
    mobiusForwardUnit (A := A) * mobiusBackwardUnit (A := A) ≠
      mobiusBackwardUnit (A := A) * mobiusForwardUnit (A := A) := by
  intro h
  change (Matrix.single 0 1 (1 : A) * Matrix.single 1 0 (1 : A)) =
    Matrix.single 1 0 (1 : A) * Matrix.single 0 1 (1 : A) at h
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h
  have h00 := congrArg (fun M : OperatorMatrix A => M 0 0) h
  have hOne : (1 : A) = 0 := by simpa [Matrix.single] using h00
  exact one_ne_zero hOne

def operatorMobiusAction (g : OperatorMatrix A) (v : OperatorPair A) : OperatorPair A :=
  Matrix.mulVec g v

theorem operatorMobiusAction_apply (g : OperatorMatrix A) (v : OperatorPair A)
    (i : Fin 2) :
    operatorMobiusAction g v i = ∑ j, g i j * v j := by
  rfl

theorem operatorMobiusAction_mul (g h : OperatorMatrix A) (v : OperatorPair A) :
    operatorMobiusAction (g * h) v =
      operatorMobiusAction g (operatorMobiusAction h v) := by
  exact (Matrix.mulVec_mulVec v g h).symm

theorem operatorMobiusAction_one (v : OperatorPair A) :
    operatorMobiusAction (1 : OperatorMatrix A) v = v := by
  exact Matrix.one_mulVec v

theorem operatorMobiusAction_add (g h : OperatorMatrix A) (v : OperatorPair A) :
    operatorMobiusAction (g + h) v =
      operatorMobiusAction g v + operatorMobiusAction h v := by
  exact Matrix.add_mulVec g h v

section ThermalBogoliubov

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The operator-valued Möbius matrix carrying the thermal Bogoliubov
    coefficients.  Its entries are operators in `A`, not external scalar
    coordinates. -/
def thermalBogoliubovMatrix (u v : ℂ) : OperatorMatrix A :=
  !![algebraMap ℂ A u, algebraMap ℂ A v;
     algebraMap ℂ A v, algebraMap ℂ A u]

theorem thermalAnnihilator_eq_operatorMobiusAction
    (a d : A) (u v : ℂ) :
    operatorMobiusAction (thermalBogoliubovMatrix (A := A) u v)
        ![a, d] 0 = thermalAnnihilator a d u v := by
  simp [operatorMobiusAction_apply, thermalBogoliubovMatrix,
    thermalAnnihilator, Algebra.smul_def]

theorem thermalCreator_eq_operatorMobiusAction
    (c b : A) (u v : ℂ) :
    operatorMobiusAction (thermalBogoliubovMatrix (A := A) u v)
        ![b, c] 1 = thermalCreator c b u v := by
  simp [operatorMobiusAction_apply, thermalBogoliubovMatrix,
    thermalCreator, Algebra.smul_def, add_comm]

end ThermalBogoliubov

theorem operatorMobiusAction_map
    {B : Type*} [Semiring B]
    (φ : A →+* B) (g : OperatorMatrix A) (v : OperatorPair A) :
    (fun i => φ (operatorMobiusAction g v i)) =
      operatorMobiusAction (fun i j => φ (g i j)) (fun i => φ (v i)) := by
  funext i
  change φ (∑ j, g i j * v j) =
    ∑ j, φ (g i j) * φ (v j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact map_mul φ (g i j) (v j)

section DerivationFlowTransport

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- A continuous derivation flow transports the operator-valued Möbius action
entrywise. Each coefficient remains on the left of its operator coordinate. -/
theorem derivationFlow_operatorMobiusAction
    (D : A →L[ℝ] A)
    (hD : InfoGeometry.Lie.ContinuousDerivationExponential.IsDerivation
      (ContinuousLinearMap.mul ℝ A) D)
    (t : ℝ) (g : OperatorMatrix A) (v : OperatorPair A) (i : Fin 2) :
    InfoGeometry.Lie.ContinuousDerivationExponential.flowLinearEquiv D t
        (operatorMobiusAction g v i) =
      operatorMobiusAction
        (fun r c => InfoGeometry.Lie.ContinuousDerivationExponential.flowLinearEquiv D t (g r c))
        (fun r => InfoGeometry.Lie.ContinuousDerivationExponential.flowLinearEquiv D t (v r)) i := by
  change InfoGeometry.Lie.ContinuousDerivationExponential.flowLinearEquiv D t
      (∑ j, g i j * v j) =
    ∑ j,
      InfoGeometry.Lie.ContinuousDerivationExponential.flowLinearEquiv D t (g i j) *
        InfoGeometry.Lie.ContinuousDerivationExponential.flowLinearEquiv D t (v j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simpa using
    (InfoGeometry.Lie.ContinuousDerivationExponential.exponential_derivation_is_automorphism
      (ContinuousLinearMap.mul ℝ A) D hD t (g i j) (v j))

end DerivationFlowTransport

section ThermalBogoliubovTransport

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem AlgHom.map_thermalAnnihilator_operatorMobiusAction
    {B : Type*} [Ring B] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) (a d : A) (u v : ℂ) :
    φ (operatorMobiusAction
        (thermalBogoliubovMatrix (A := A) u v) ![a, d] 0) =
      operatorMobiusAction
        (thermalBogoliubovMatrix (A := B) u v) ![φ a, φ d] 0 := by
  calc
    φ (operatorMobiusAction
        (thermalBogoliubovMatrix (A := A) u v) ![a, d] 0) =
        φ (thermalAnnihilator a d u v) := by
          rw [thermalAnnihilator_eq_operatorMobiusAction]
    _ = thermalAnnihilator (φ a) (φ d) u v := by
          exact thermalAnnihilator_map φ a d u v
    _ = operatorMobiusAction
        (thermalBogoliubovMatrix (A := B) u v) ![φ a, φ d] 0 := by
          rw [thermalAnnihilator_eq_operatorMobiusAction]

theorem AlgHom.map_thermalCreator_operatorMobiusAction
    {B : Type*} [Ring B] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) (c b : A) (u v : ℂ) :
    φ (operatorMobiusAction
        (thermalBogoliubovMatrix (A := A) u v) ![b, c] 1) =
      operatorMobiusAction
        (thermalBogoliubovMatrix (A := B) u v) ![φ b, φ c] 1 := by
  calc
    φ (operatorMobiusAction
        (thermalBogoliubovMatrix (A := A) u v) ![b, c] 1) =
        φ (thermalCreator c b u v) := by
          rw [thermalCreator_eq_operatorMobiusAction]
    _ = thermalCreator (φ c) (φ b) u v := by
          exact thermalCreator_map φ c b u v
    _ = operatorMobiusAction
        (thermalBogoliubovMatrix (A := B) u v) ![φ b, φ c] 1 := by
          rw [thermalCreator_eq_operatorMobiusAction]

end ThermalBogoliubovTransport

theorem operatorMobiusAction_unit_inverse_left
    (g : (OperatorMatrix A)ˣ) (v : OperatorPair A) :
    operatorMobiusAction (↑(g⁻¹) : OperatorMatrix A)
        (operatorMobiusAction (↑g : OperatorMatrix A) v) = v := by
  rw [← operatorMobiusAction_mul]
  have h : (↑(g⁻¹) : OperatorMatrix A) * (↑g : OperatorMatrix A) = 1 :=
    Units.inv_mul g
  rw [h]
  exact operatorMobiusAction_one v

theorem operatorMobiusAction_unit_inverse_right
    (g : (OperatorMatrix A)ˣ) (v : OperatorPair A) :
    operatorMobiusAction (↑g : OperatorMatrix A)
        (operatorMobiusAction (↑(g⁻¹) : OperatorMatrix A) v) = v := by
  rw [← operatorMobiusAction_mul]
  have h : (↑g : OperatorMatrix A) * (↑(g⁻¹) : OperatorMatrix A) = 1 :=
    Units.mul_inv g
  rw [h]
  exact operatorMobiusAction_one v

end

end InfoGeometry.OperatorAlgebra
