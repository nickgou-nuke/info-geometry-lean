import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Clifford.Clifford55

open InfoGeometry.Clifford
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.Clifford55

noncomputable section

abbrev E5 := Fin 5 → ℝ
abbrev PhaseSpace5 := PhaseSpaceCarrier E5

-- The generic split form from the evaluation pairing
def genericSplitForm5 : QuadraticForm ℝ PhaseSpace5 :=
  canonicalNeutralBilin.toQuadraticForm

-- The standard Euclidean inner product gives an isomorphism E5 ≃ₗ[ℝ] Module.Dual ℝ E5
def euclideanDual : E5 →ₗ[ℝ] Module.Dual ℝ E5 where
  toFun v := 
    { toFun := fun u => ∑ i, v i * u i
      map_add' := by sorry
      map_smul' := by sorry }
  map_add' := by sorry
  map_smul' := by sorry

-- The coordinate transformation V55 ≃ₗ[ℝ] PhaseSpace5
def coordinateRotation : V55 ≃ₗ[ℝ] PhaseSpace5 where
  toFun v := (v.1 + v.2, euclideanDual (v.1 - v.2))
  invFun := by sorry
  left_inv := by sorry
  right_inv := by sorry
  map_add' := by sorry
  map_smul' := by sorry

-- The isometry between Q55 and the Generic form
def splitIsometry : Q55 ≃q genericSplitForm5 where
  toEquiv := coordinateRotation.toEquiv
  map_app' := by sorry

-- The algebra isomorphism proving the representations are strictly equivalent
def Cl55_equiv_generic : Cl55 ≃ₐ[ℝ] CliffordAlgebra genericSplitForm5 :=
  CliffordAlgebra.equivOfIsometry splitIsometry
