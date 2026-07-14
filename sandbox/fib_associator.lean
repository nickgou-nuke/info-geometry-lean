import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import InfoGeometry.Categorical.FibonacciBraidedCategory

open InfoGeometry.Categorical.FibonacciFusionCategoryData
open InfoGeometry.Categorical.FibonacciHomSpace
open InfoGeometry.Categorical.FibonacciBraidedCategory

noncomputable def fibAssociator_unit_dim_eq (X Y Z : FibCat) :
  ((fibTensorObj (fibTensorObj X Y) Z) FibSimple.unit) =
  ((fibTensorObj X (fibTensorObj Y Z)) FibSimple.unit) := by
  dsimp [fibTensorObj, Finsupp.single, Finsupp.add_apply]
  ring

noncomputable def fibAssociator_tau_dim_eq (X Y Z : FibCat) :
  ((fibTensorObj (fibTensorObj X Y) Z) FibSimple.tau) =
  ((fibTensorObj X (fibTensorObj Y Z)) FibSimple.tau) := by
  dsimp [fibTensorObj, Finsupp.single, Finsupp.add_apply]
  ring

