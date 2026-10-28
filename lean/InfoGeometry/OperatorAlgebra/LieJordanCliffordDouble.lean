/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanDualTransport

/-!
# A genuine doubled endomorphism and its order-sensitive square

All blocks act on the full associative algebra `A`. The two coefficient
operators need not commute. The square retains the mixed Lie--Jordan defect.
The Clifford identities are identities of actual endomorphisms of `A × A`;
no spacetime Dirac equation, curvature tensor, or analytic domain is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.LieJordanDualTransport

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Componentwise lift of an actual algebra endomorphism. -/
def liftOp (t : Module.End R A) : Module.End R (A × A) where
  toFun v := (t v.1, t v.2)
  map_add' v w := by simp
  map_smul' r v := by simp

/-- Exchange of the two copies of the algebra. -/
def swapOp : Module.End R (A × A) where
  toFun v := (v.2, v.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The two-sheet grading, acting on the full product module. -/
def gradingOp : Module.End R (A × A) where
  toFun v := (v.1, -v.2)
  map_add' _ _ := by simp [add_comm]
  map_smul' _ _ := by simp

/-- Internal square-minus-one phase, with no external imaginary scalar. -/
def phaseOp : Module.End R (A × A) := swapOp * gradingOp

theorem swapOp_sq : (swapOp : Module.End R (A × A)) * swapOp = 1 := by
  apply LinearMap.ext
  intro v
  rfl

theorem gradingOp_sq : (gradingOp : Module.End R (A × A)) * gradingOp = 1 := by
  apply LinearMap.ext
  intro v
  change (v.1, -(-v.2)) = v
  simp

theorem swap_grading_anticommute :
    (swapOp : Module.End R (A × A)) * gradingOp + gradingOp * swapOp = 0 := by
  apply LinearMap.ext
  intro v
  change (-v.2 + v.2, v.1 + -v.1) = (0, 0)
  simp

@[simp] theorem phaseOp_apply (v : A × A) :
    (phaseOp : Module.End R (A × A)) v = (-v.2, v.1) := rfl

theorem phaseOp_sq : (phaseOp : Module.End R (A × A)) * phaseOp = -1 := by
  apply LinearMap.ext
  intro v
  change (-v.1, -v.2) = -v
  rfl

/-- The positive/negative transport acts in opposite off-diagonal blocks. -/
def doubled (h s : A) : Module.End R (A × A) where
  toFun v := (minus (R := R) h s v.2, plus (R := R) h s v.1)
  map_add' v w := by
    change (minus (R := R) h s (v.2 + w.2), plus (R := R) h s (v.1 + w.1)) = _
    rw [map_add, map_add]
    rfl
  map_smul' r v := by
    change (minus (R := R) h s (r • v.2), plus (R := R) h s (r • v.1)) = _
    rw [map_smul, map_smul]
    rfl

@[simp] theorem doubled_apply (h s : A) (v : A × A) :
    doubled (R := R) h s v = (minus (R := R) h s v.2, plus (R := R) h s v.1) := rfl

/-- The two summands use actual Clifford generators on the product module. -/
theorem doubled_clifford_decomposition (h s : A) :
    doubled (R := R) h s =
      swapOp * liftOp (LieAlgebra.ad R A h) + phaseOp * liftOp (jordanLeft (R := R) s) := by
  apply LinearMap.ext
  intro v
  change (LieAlgebra.ad R A h v.2 - jordanLeft (R := R) s v.2,
      LieAlgebra.ad R A h v.1 + jordanLeft (R := R) s v.1) =
    (LieAlgebra.ad R A h v.2 + -(jordanLeft (R := R) s v.2),
      LieAlgebra.ad R A h v.1 + jordanLeft (R := R) s v.1)
  simp only [sub_eq_add_neg]

theorem grading_anticommutes_doubled (h s : A) :
    gradingOp * doubled (R := R) h s + doubled (R := R) h s * gradingOp = 0 := by
  apply LinearMap.ext
  intro v
  change (minus (R := R) h s v.2 + minus (R := R) h s (-v.2),
    -(plus (R := R) h s v.1) + plus (R := R) h s v.1) = (0, 0)
  simp only [map_neg, add_neg_cancel, neg_add_cancel]

/-- The square has different diagonal blocks unless the exact obstruction
vanishes; neither block is replaced by scalar multiplication. -/
theorem doubled_square_apply (h s : A) (v : A × A) :
    (doubled (R := R) h s * doubled (R := R) h s) v =
      ((LieAlgebra.ad R A h * LieAlgebra.ad R A h -
          jordanLeft (R := R) s * jordanLeft (R := R) s + jordanLeft (R := R) (h * s - s * h)) v.1,
       (LieAlgebra.ad R A h * LieAlgebra.ad R A h -
          jordanLeft (R := R) s * jordanLeft (R := R) s - jordanLeft (R := R) (h * s - s * h)) v.2) := by
  apply Prod.ext
  · exact congrArg (fun t : Module.End R A => t v.1) (minus_mul_plus h s)
  · exact congrArg (fun t : Module.End R A => t v.2) (plus_mul_minus h s)

end InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble
