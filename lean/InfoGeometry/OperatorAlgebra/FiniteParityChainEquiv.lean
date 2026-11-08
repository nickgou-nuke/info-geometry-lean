import InfoGeometry.OperatorAlgebra.FiniteParityChainMap
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteParityComplex

namespace TwoPeriodicComplex

variable {Vplus Vminus Wplus Wminus : Type*}
variable [AddCommGroup Vplus] [Module ℝ Vplus]
variable [AddCommGroup Vminus] [Module ℝ Vminus]
variable [AddCommGroup Wplus] [Module ℝ Wplus]
variable [AddCommGroup Wminus] [Module ℝ Wminus]

structure Equiv
    (C : TwoPeriodicComplex Vplus Vminus)
    (D : TwoPeriodicComplex Wplus Wminus) where
  toHom : Hom C D
  invHom : Hom D C
  inv_comp_positive :
    invHom.positive.comp toHom.positive = LinearMap.id
  hom_comp_positive :
    toHom.positive.comp invHom.positive = LinearMap.id
  inv_comp_negative :
    invHom.negative.comp toHom.negative = LinearMap.id
  hom_comp_negative :
    toHom.negative.comp invHom.negative = LinearMap.id

namespace Equiv

variable {C : TwoPeriodicComplex Vplus Vminus}
variable {D : TwoPeriodicComplex Wplus Wminus}

def positiveCarrierEquiv (e : Equiv C D) : Vplus ≃ₗ[ℝ] Wplus where
  toLinearMap := e.toHom.positive
  invFun := e.invHom.positive
  left_inv x := by
    have h := LinearMap.congr_fun e.inv_comp_positive x
    simpa [LinearMap.comp_apply] using h
  right_inv x := by
    have h := LinearMap.congr_fun e.hom_comp_positive x
    simpa [LinearMap.comp_apply] using h

def negativeCarrierEquiv (e : Equiv C D) : Vminus ≃ₗ[ℝ] Wminus where
  toLinearMap := e.toHom.negative
  invFun := e.invHom.negative
  left_inv x := by
    have h := LinearMap.congr_fun e.inv_comp_negative x
    simpa [LinearMap.comp_apply] using h
  right_inv x := by
    have h := LinearMap.congr_fun e.hom_comp_negative x
    simpa [LinearMap.comp_apply] using h

def positiveCohomologyEquiv (e : Equiv C D) :
    C.PositiveCohomology ≃ₗ[ℝ] D.PositiveCohomology where
  toLinearMap := e.toHom.positiveCohomologyMap
  invFun := e.invHom.positiveCohomologyMap
  left_inv q := by
    obtain ⟨x, rfl⟩ := C.positiveBoundaries.mkQ_surjective q
    change e.invHom.positiveCohomologyMap
      (e.toHom.positiveCohomologyMap (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk x
    rw [Hom.positiveCohomologyMap_mk, Hom.positiveCohomologyMap_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    have h := LinearMap.congr_fun e.inv_comp_positive x
    simpa [LinearMap.comp_apply] using h
  right_inv q := by
    obtain ⟨x, rfl⟩ := D.positiveBoundaries.mkQ_surjective q
    change e.toHom.positiveCohomologyMap
      (e.invHom.positiveCohomologyMap (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk x
    rw [Hom.positiveCohomologyMap_mk, Hom.positiveCohomologyMap_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    have h := LinearMap.congr_fun e.hom_comp_positive x
    simpa [LinearMap.comp_apply] using h

def negativeCohomologyEquiv (e : Equiv C D) :
    C.NegativeCohomology ≃ₗ[ℝ] D.NegativeCohomology where
  toLinearMap := e.toHom.negativeCohomologyMap
  invFun := e.invHom.negativeCohomologyMap
  left_inv q := by
    obtain ⟨x, rfl⟩ := C.negativeBoundaries.mkQ_surjective q
    change e.invHom.negativeCohomologyMap
      (e.toHom.negativeCohomologyMap (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk x
    rw [Hom.negativeCohomologyMap_mk, Hom.negativeCohomologyMap_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    have h := LinearMap.congr_fun e.inv_comp_negative x
    simpa [LinearMap.comp_apply] using h
  right_inv q := by
    obtain ⟨x, rfl⟩ := D.negativeBoundaries.mkQ_surjective q
    change e.toHom.negativeCohomologyMap
      (e.invHom.negativeCohomologyMap (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk x
    rw [Hom.negativeCohomologyMap_mk, Hom.negativeCohomologyMap_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    have h := LinearMap.congr_fun e.hom_comp_negative x
    simpa [LinearMap.comp_apply] using h

theorem positiveCohomology_finrank_eq (e : Equiv C D) :
    Module.finrank ℝ C.PositiveCohomology =
      Module.finrank ℝ D.PositiveCohomology :=
  e.positiveCohomologyEquiv.finrank_eq

theorem negativeCohomology_finrank_eq (e : Equiv C D) :
    Module.finrank ℝ C.NegativeCohomology =
      Module.finrank ℝ D.NegativeCohomology :=
  e.negativeCohomologyEquiv.finrank_eq

theorem eulerCharacteristic_invariant (e : Equiv C D) :
    (Module.finrank ℝ C.PositiveCohomology : ℤ) -
        Module.finrank ℝ C.NegativeCohomology =
      Module.finrank ℝ D.PositiveCohomology -
        Module.finrank ℝ D.NegativeCohomology := by
  rw [e.positiveCohomology_finrank_eq, e.negativeCohomology_finrank_eq]

end Equiv

end TwoPeriodicComplex

end InfoGeometry.OperatorAlgebra.FiniteParityComplex
