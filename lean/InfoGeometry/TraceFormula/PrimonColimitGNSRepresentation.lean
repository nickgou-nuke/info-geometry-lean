import InfoGeometry.Algebra.PrimonColimitAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite left actions and their lift to the Primon colimit

The finite carrier is the matrix stage itself.  Its representation is left
multiplication, expressed by Mathlib's `LinearMap.mulLeft`.  The colimit only
has the ring structure currently provided by `PrimonColimitAlgebra`, so its
lift is stated as an additive left action rather than as a linear or bounded
operator representation.  This keeps the interface honest until a scalar
action and a Hilbert carrier are supplied by a separate owner.
-/

noncomputable section

namespace InfoGeometry.TraceFormula.PrimonColimitGNSRepresentation

open InfoGeometry.Algebra.PrimonColimitAlgebra

/-! ## Finite carrier -/

/-- Left multiplication by a stage element on the finite matrix carrier. -/
def finiteLeftAction (n : ℕ) (a : MatrixStage n) :
    MatrixStage n →ₗ[ℝ] MatrixStage n :=
  LinearMap.mulLeft ℝ a

@[simp] theorem finiteLeftAction_apply
    (n : ℕ) (a x : MatrixStage n) :
    finiteLeftAction n a x = a * x := by
  rfl

theorem finiteLeftAction_mul_apply
    (n : ℕ) (a b x : MatrixStage n) :
    finiteLeftAction n (a * b) x =
      finiteLeftAction n a (finiteLeftAction n b x) := by
  simp [finiteLeftAction, mul_assoc]

@[simp] theorem finiteLeftAction_one_apply
    (n : ℕ) (x : MatrixStage n) :
    finiteLeftAction n 1 x = x := by
  simp [finiteLeftAction]

/-! ## Colimit lift -/

/-- Additive left multiplication on the algebraic ring colimit. -/
def colimitLeftAction (a : PrimonUHFAlgebra) :
    PrimonUHFAlgebra →+ PrimonUHFAlgebra where
  toFun := fun x => a * x
  map_zero' := by simp
  map_add' := by intro x y; simp [mul_add]

@[simp] theorem colimitLeftAction_apply
    (a x : PrimonUHFAlgebra) :
    colimitLeftAction a x = a * x :=
  rfl

theorem colimitLeftAction_mul_apply
    (a b x : PrimonUHFAlgebra) :
    colimitLeftAction (a * b) x =
      colimitLeftAction a (colimitLeftAction b x) := by
  simp [colimitLeftAction, mul_assoc]

@[simp] theorem colimitLeftAction_one_apply
    (x : PrimonUHFAlgebra) :
    colimitLeftAction 1 x = x := by
  simp [colimitLeftAction]

/-- The colimit action agrees with finite left multiplication on each stage. -/
theorem colimitLeftAction_stage
    (n : ℕ) (a x : MatrixStage n) :
    colimitLeftAction (toColimit n a) (toColimit n x) =
      toColimit n (a * x) := by
  simp [colimitLeftAction]

/-- The lifted action is independent of the representative stage. -/
theorem colimitLeftAction_bond
    (n : ℕ) (a x : MatrixStage n) :
    colimitLeftAction
        (toColimit (n + 1) (matrixBond n a))
        (toColimit (n + 1) (matrixBond n x)) =
      colimitLeftAction (toColimit n a) (toColimit n x) := by
  rw [toColimit_bond, toColimit_bond]

end InfoGeometry.TraceFormula.PrimonColimitGNSRepresentation
