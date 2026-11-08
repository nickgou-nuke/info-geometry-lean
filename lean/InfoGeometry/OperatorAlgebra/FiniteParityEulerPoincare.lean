import InfoGeometry.OperatorAlgebra.FiniteParityComplex
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteParityComplex

namespace TwoPeriodicComplex

variable {Vplus Vminus : Type*}
variable [AddCommGroup Vplus] [Module ℝ Vplus]
variable [AddCommGroup Vminus] [Module ℝ Vminus]

theorem range_dMinus_le_ker_dPlus
    (C : TwoPeriodicComplex Vplus Vminus) :
    LinearMap.range C.dMinus ≤ LinearMap.ker C.dPlus := by
  rw [LinearMap.range_le_ker_iff]
  exact C.dPlus_comp_dMinus

theorem range_dPlus_le_ker_dMinus
    (C : TwoPeriodicComplex Vplus Vminus) :
    LinearMap.range C.dPlus ≤ LinearMap.ker C.dMinus := by
  rw [LinearMap.range_le_ker_iff]
  exact C.dMinus_comp_dPlus

def positiveBoundaryEquivRange
    (C : TwoPeriodicComplex Vplus Vminus) :
    C.positiveBoundaries ≃ₗ[ℝ] LinearMap.range C.dMinus where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x :=
    ⟨⟨x.1, C.range_dMinus_le_ker_dPlus x.2⟩, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def negativeBoundaryEquivRange
    (C : TwoPeriodicComplex Vplus Vminus) :
    C.negativeBoundaries ≃ₗ[ℝ] LinearMap.range C.dPlus where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x :=
    ⟨⟨x.1, C.range_dPlus_le_ker_dMinus x.2⟩, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_positiveBoundaries
    (C : TwoPeriodicComplex Vplus Vminus) :
    Module.finrank ℝ C.positiveBoundaries =
      Module.finrank ℝ (LinearMap.range C.dMinus) :=
  C.positiveBoundaryEquivRange.finrank_eq

theorem finrank_negativeBoundaries
    (C : TwoPeriodicComplex Vplus Vminus) :
    Module.finrank ℝ C.negativeBoundaries =
      Module.finrank ℝ (LinearMap.range C.dPlus) :=
  C.negativeBoundaryEquivRange.finrank_eq

theorem positiveCohomology_finrank_add_range
    (C : TwoPeriodicComplex Vplus Vminus)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    Module.finrank ℝ C.PositiveCohomology +
        Module.finrank ℝ (LinearMap.range C.dMinus) =
      Module.finrank ℝ (LinearMap.ker C.dPlus) := by
  rw [← C.finrank_positiveBoundaries]
  exact Submodule.finrank_quotient_add_finrank C.positiveBoundaries

theorem negativeCohomology_finrank_add_range
    (C : TwoPeriodicComplex Vplus Vminus)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    Module.finrank ℝ C.NegativeCohomology +
        Module.finrank ℝ (LinearMap.range C.dPlus) =
      Module.finrank ℝ (LinearMap.ker C.dMinus) := by
  rw [← C.finrank_negativeBoundaries]
  exact Submodule.finrank_quotient_add_finrank C.negativeBoundaries

theorem eulerPoincare
    (C : TwoPeriodicComplex Vplus Vminus)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    Module.finrank ℝ Vplus + Module.finrank ℝ C.NegativeCohomology =
      Module.finrank ℝ Vminus + Module.finrank ℝ C.PositiveCohomology := by
  have hPlus := LinearMap.finrank_range_add_finrank_ker C.dPlus
  have hMinus := LinearMap.finrank_range_add_finrank_ker C.dMinus
  have hCohPlus := C.positiveCohomology_finrank_add_range
  have hCohMinus := C.negativeCohomology_finrank_add_range
  omega

theorem eulerCharacteristic_eq
    (C : TwoPeriodicComplex Vplus Vminus)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    (Module.finrank ℝ Vplus : ℤ) - Module.finrank ℝ Vminus =
      Module.finrank ℝ C.PositiveCohomology -
        Module.finrank ℝ C.NegativeCohomology := by
  have h := C.eulerPoincare
  omega

end TwoPeriodicComplex

end InfoGeometry.OperatorAlgebra.FiniteParityComplex
