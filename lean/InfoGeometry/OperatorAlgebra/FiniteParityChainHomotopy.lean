import InfoGeometry.OperatorAlgebra.FiniteParityChainEquiv
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteParityComplex

namespace TwoPeriodicComplex

variable {Vplus Vminus Wplus Wminus : Type*}
variable [AddCommGroup Vplus] [Module ℝ Vplus]
variable [AddCommGroup Vminus] [Module ℝ Vminus]
variable [AddCommGroup Wplus] [Module ℝ Wplus]
variable [AddCommGroup Wminus] [Module ℝ Wminus]

structure Homotopy
    {C : TwoPeriodicComplex Vplus Vminus}
    {D : TwoPeriodicComplex Wplus Wminus}
    (f g : Hom C D) where
  hPlus : Vplus →ₗ[ℝ] Wminus
  hMinus : Vminus →ₗ[ℝ] Wplus
  positive_identity :
    f.positive - g.positive =
      D.dMinus.comp hPlus + hMinus.comp C.dPlus
  negative_identity :
    f.negative - g.negative =
      D.dPlus.comp hMinus + hPlus.comp C.dMinus

namespace Homotopy

variable {C : TwoPeriodicComplex Vplus Vminus}
variable {D : TwoPeriodicComplex Wplus Wminus}
variable {f g : Hom C D}

theorem positiveCycle_difference_mem_boundary
    (H : Homotopy f g)
    (x : LinearMap.ker C.dPlus) :
    f.positiveCycleMap x - g.positiveCycleMap x ∈
      D.positiveBoundaries := by
  change
    (f.positive x : Wplus) - g.positive x ∈
      LinearMap.range D.dMinus
  refine ⟨H.hPlus x, ?_⟩
  have h := LinearMap.congr_fun H.positive_identity x
  simpa [LinearMap.comp_apply, LinearMap.mem_ker.mp x.2] using h.symm

theorem negativeCycle_difference_mem_boundary
    (H : Homotopy f g)
    (x : LinearMap.ker C.dMinus) :
    f.negativeCycleMap x - g.negativeCycleMap x ∈
      D.negativeBoundaries := by
  change
    (f.negative x : Wminus) - g.negative x ∈
      LinearMap.range D.dPlus
  refine ⟨H.hMinus x, ?_⟩
  have h := LinearMap.congr_fun H.negative_identity x
  simpa [LinearMap.comp_apply, LinearMap.mem_ker.mp x.2] using h.symm

theorem positiveCohomologyMap_eq (H : Homotopy f g) :
    f.positiveCohomologyMap = g.positiveCohomologyMap := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := C.positiveBoundaries.mkQ_surjective q
  change f.positiveCohomologyMap (Submodule.Quotient.mk x) =
    g.positiveCohomologyMap (Submodule.Quotient.mk x)
  rw [Hom.positiveCohomologyMap_mk, Hom.positiveCohomologyMap_mk]
  exact (Submodule.Quotient.eq D.positiveBoundaries).2
    (H.positiveCycle_difference_mem_boundary x)

theorem negativeCohomologyMap_eq (H : Homotopy f g) :
    f.negativeCohomologyMap = g.negativeCohomologyMap := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := C.negativeBoundaries.mkQ_surjective q
  change f.negativeCohomologyMap (Submodule.Quotient.mk x) =
    g.negativeCohomologyMap (Submodule.Quotient.mk x)
  rw [Hom.negativeCohomologyMap_mk, Hom.negativeCohomologyMap_mk]
  exact (Submodule.Quotient.eq D.negativeBoundaries).2
    (H.negativeCycle_difference_mem_boundary x)

end Homotopy

structure HomotopyEquiv
    (C : TwoPeriodicComplex Vplus Vminus)
    (D : TwoPeriodicComplex Wplus Wminus) where
  toHom : Hom C D
  invHom : Hom D C
  leftHomotopy : Homotopy (Hom.comp invHom toHom) (Hom.id C)
  rightHomotopy : Homotopy (Hom.comp toHom invHom) (Hom.id D)

namespace HomotopyEquiv

variable {C : TwoPeriodicComplex Vplus Vminus}
variable {D : TwoPeriodicComplex Wplus Wminus}

def positiveCohomologyEquiv (e : HomotopyEquiv C D) :
    C.PositiveCohomology ≃ₗ[ℝ] D.PositiveCohomology where
  toLinearMap := e.toHom.positiveCohomologyMap
  invFun := e.invHom.positiveCohomologyMap
  left_inv q := by
    have h := LinearMap.congr_fun
      e.leftHomotopy.positiveCohomologyMap_eq q
    rw [Hom.positiveCohomologyMap_comp,
      Hom.positiveCohomologyMap_id] at h
    exact h
  right_inv q := by
    have h := LinearMap.congr_fun
      e.rightHomotopy.positiveCohomologyMap_eq q
    rw [Hom.positiveCohomologyMap_comp,
      Hom.positiveCohomologyMap_id] at h
    exact h

def negativeCohomologyEquiv (e : HomotopyEquiv C D) :
    C.NegativeCohomology ≃ₗ[ℝ] D.NegativeCohomology where
  toLinearMap := e.toHom.negativeCohomologyMap
  invFun := e.invHom.negativeCohomologyMap
  left_inv q := by
    have h := LinearMap.congr_fun
      e.leftHomotopy.negativeCohomologyMap_eq q
    rw [Hom.negativeCohomologyMap_comp,
      Hom.negativeCohomologyMap_id] at h
    exact h
  right_inv q := by
    have h := LinearMap.congr_fun
      e.rightHomotopy.negativeCohomologyMap_eq q
    rw [Hom.negativeCohomologyMap_comp,
      Hom.negativeCohomologyMap_id] at h
    exact h

theorem positiveCohomology_finrank_eq (e : HomotopyEquiv C D) :
    Module.finrank ℝ C.PositiveCohomology =
      Module.finrank ℝ D.PositiveCohomology :=
  e.positiveCohomologyEquiv.finrank_eq

theorem negativeCohomology_finrank_eq (e : HomotopyEquiv C D) :
    Module.finrank ℝ C.NegativeCohomology =
      Module.finrank ℝ D.NegativeCohomology :=
  e.negativeCohomologyEquiv.finrank_eq

theorem eulerCharacteristic_invariant (e : HomotopyEquiv C D) :
    (Module.finrank ℝ C.PositiveCohomology : ℤ) -
        Module.finrank ℝ C.NegativeCohomology =
      Module.finrank ℝ D.PositiveCohomology -
        Module.finrank ℝ D.NegativeCohomology := by
  rw [e.positiveCohomology_finrank_eq, e.negativeCohomology_finrank_eq]

end HomotopyEquiv

end TwoPeriodicComplex

end InfoGeometry.OperatorAlgebra.FiniteParityComplex
