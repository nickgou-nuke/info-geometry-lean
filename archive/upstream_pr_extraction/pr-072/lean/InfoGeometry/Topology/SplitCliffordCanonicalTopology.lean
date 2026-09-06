import Mathlib
import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Clifford.Cl11Matrix

/-!
# Canonical finite-dimensional topology for the split Clifford tower

This owner supplies the missing finite-dimensional structure and a coordinate
topology for the finite stages `SplitClNNAlg n`.  The topology is induced along
a finite-basis coordinate equivalence; no norm or analytic structure is
asserted for the direct limit.
-/

noncomputable section

namespace InfoGeometry.Topology.SplitCliffordCanonicalTopology

open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.Cl11Matrix

private noncomputable def splitZeroToUnit : SplitSpace 0 ≃ₗ[ℝ] Unit where
  toFun := fun _ => ()
  invFun := fun _ => 0
  left_inv := by
    intro x
    funext i
    exact Fin.elim0 i
  right_inv := by
    intro x
    cases x
    rfl
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro r x
    rfl

private noncomputable def splitZeroIsometry :
    QuadraticMap.IsometryEquiv (Qsplit 0) (0 : QuadraticForm ℝ Unit) where
  toLinearEquiv := splitZeroToUnit
  map_app' := by
    intro x
    simp [Qsplit]

private noncomputable def splitZeroAlgEquiv : SplitClNNAlg 0 ≃ₐ[ℝ] ℝ :=
  (CliffordAlgebra.equivOfIsometry splitZeroIsometry).trans
    CliffordAlgebraRing.equiv

private theorem cl11_finiteDimensional :
    FiniteDimensional ℝ (CliffordAlgebra InfoGeometry.CliffordTower.Q11) := by
  have hq : InfoGeometry.CliffordTower.Q11 = q11 := by
    ext v
    simp [InfoGeometry.CliffordTower.Q11,
      InfoGeometry.Clifford.Cl11Matrix.q11,
      InfoGeometry.Clifford.splitQ11_apply,
      CliffordAlgebraQuaternion.Q]
    ring
  rw [hq]
  exact LinearEquiv.finiteDimensional cl11EquivMat.toLinearEquiv.symm

/-- Every finite stage of the split Clifford tower is finite-dimensional. -/
noncomputable instance splitClNNAlg_finiteDimensional :
    ∀ n : ℕ, FiniteDimensional ℝ (SplitClNNAlg n)
  | 0 => LinearEquiv.finiteDimensional splitZeroAlgEquiv.symm.toLinearEquiv
  | n + 1 => by
      letI : FiniteDimensional ℝ (SplitClNNAlg n) :=
        splitClNNAlg_finiteDimensional n
      letI : FiniteDimensional ℝ
          (CliffordAlgebra InfoGeometry.CliffordTower.Q11) :=
        cl11_finiteDimensional
      let e : SplitClNNTensorStep n ≃ₗ[ℝ]
          TensorProduct ℝ
            (CliffordAlgebra InfoGeometry.CliffordTower.Q11)
            (CliffordAlgebra (Qsplit n)) :=
        (GradedTensorProduct.of ℝ
          (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
          (CliffordAlgebra.evenOdd (Qsplit n))).symm
      letI : FiniteDimensional ℝ (SplitClNNTensorStep n) :=
        LinearEquiv.finiteDimensional e.symm
      exact LinearEquiv.finiteDimensional
        (splitCliffordTensorStepEquiv n).symm.toLinearEquiv

private noncomputable def splitClNNAlgCoordinateBasis (n : ℕ) :
    Module.Basis (Fin (Module.finrank ℝ (SplitClNNAlg n)))
      ℝ (SplitClNNAlg n) :=
  Module.finBasis ℝ (SplitClNNAlg n)

/- The finite basis coordinate map transports the standard Euclidean topology.
This deliberately installs only `TopologicalSpace`: installing a global
`NormedAddCommGroup` would also install a second inherited `AddCommGroup` and
create a typeclass diamond with the algebraic Clifford instance. -/
noncomputable instance splitClNNAlg_topologicalSpace (n : ℕ) :
    TopologicalSpace (SplitClNNAlg n) :=
  TopologicalSpace.induced
    (splitClNNAlgCoordinateBasis n).equivFun
    inferInstance

theorem splitClNNAlg_finiteDimensional_available (n : ℕ) :
    FiniteDimensional ℝ (SplitClNNAlg n) :=
  inferInstance

theorem splitClNNAlg_coordinateBasis_finite (n : ℕ) :
    Finite (Fin (Module.finrank ℝ (SplitClNNAlg n))) :=
  inferInstance

end InfoGeometry.Topology.SplitCliffordCanonicalTopology
