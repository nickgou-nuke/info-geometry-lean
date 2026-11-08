import InfoGeometry.OperatorAlgebra.FiniteParityEulerPoincare
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteParityComplex

namespace TwoPeriodicComplex

variable {Vplus Vminus Wplus Wminus Uplus Uminus : Type*}
variable [AddCommGroup Vplus] [Module ℝ Vplus]
variable [AddCommGroup Vminus] [Module ℝ Vminus]
variable [AddCommGroup Wplus] [Module ℝ Wplus]
variable [AddCommGroup Wminus] [Module ℝ Wminus]
variable [AddCommGroup Uplus] [Module ℝ Uplus]
variable [AddCommGroup Uminus] [Module ℝ Uminus]

structure Hom
    (C : TwoPeriodicComplex Vplus Vminus)
    (D : TwoPeriodicComplex Wplus Wminus) where
  positive : Vplus →ₗ[ℝ] Wplus
  negative : Vminus →ₗ[ℝ] Wminus
  commutes_dPlus :
    D.dPlus.comp positive = negative.comp C.dPlus
  commutes_dMinus :
    D.dMinus.comp negative = positive.comp C.dMinus

namespace Hom

variable {C : TwoPeriodicComplex Vplus Vminus}
variable {D : TwoPeriodicComplex Wplus Wminus}
variable {E : TwoPeriodicComplex Uplus Uminus}

def id (C : TwoPeriodicComplex Vplus Vminus) : Hom C C where
  positive := LinearMap.id
  negative := LinearMap.id
  commutes_dPlus := by simp
  commutes_dMinus := by simp

def comp (g : Hom D E) (f : Hom C D) : Hom C E where
  positive := g.positive.comp f.positive
  negative := g.negative.comp f.negative
  commutes_dPlus := by
    ext x
    simp only [LinearMap.comp_apply]
    calc
      E.dPlus (g.positive (f.positive x)) =
          g.negative (D.dPlus (f.positive x)) := by
        simpa only [LinearMap.comp_apply] using
          LinearMap.congr_fun g.commutes_dPlus (f.positive x)
      _ = g.negative (f.negative (C.dPlus x)) := by
        rw [show D.dPlus (f.positive x) =
            f.negative (C.dPlus x) by
          simpa only [LinearMap.comp_apply] using
            LinearMap.congr_fun f.commutes_dPlus x]
  commutes_dMinus := by
    ext x
    simp only [LinearMap.comp_apply]
    calc
      E.dMinus (g.negative (f.negative x)) =
          g.positive (D.dMinus (f.negative x)) := by
        simpa only [LinearMap.comp_apply] using
          LinearMap.congr_fun g.commutes_dMinus (f.negative x)
      _ = g.positive (f.positive (C.dMinus x)) := by
        rw [show D.dMinus (f.negative x) =
            f.positive (C.dMinus x) by
          simpa only [LinearMap.comp_apply] using
            LinearMap.congr_fun f.commutes_dMinus x]

def positiveCycleMap (f : Hom C D) :
    LinearMap.ker C.dPlus →ₗ[ℝ] LinearMap.ker D.dPlus :=
  LinearMap.codRestrict (LinearMap.ker D.dPlus)
    (f.positive.comp (LinearMap.ker C.dPlus).subtype)
    (by
      intro x
      rw [LinearMap.mem_ker]
      have h := LinearMap.congr_fun f.commutes_dPlus x
      simpa [LinearMap.comp_apply, LinearMap.mem_ker.mp x.2] using h)

def negativeCycleMap (f : Hom C D) :
    LinearMap.ker C.dMinus →ₗ[ℝ] LinearMap.ker D.dMinus :=
  LinearMap.codRestrict (LinearMap.ker D.dMinus)
    (f.negative.comp (LinearMap.ker C.dMinus).subtype)
    (by
      intro x
      rw [LinearMap.mem_ker]
      have h := LinearMap.congr_fun f.commutes_dMinus x
      simpa [LinearMap.comp_apply, LinearMap.mem_ker.mp x.2] using h)

@[simp]
theorem positiveCycleMap_apply (f : Hom C D)
    (x : LinearMap.ker C.dPlus) :
    (f.positiveCycleMap x : Wplus) = f.positive x :=
  rfl

@[simp]
theorem negativeCycleMap_apply (f : Hom C D)
    (x : LinearMap.ker C.dMinus) :
    (f.negativeCycleMap x : Wminus) = f.negative x :=
  rfl

theorem maps_positiveBoundaries (f : Hom C D) :
    C.positiveBoundaries ≤
      Submodule.comap f.positiveCycleMap D.positiveBoundaries := by
  intro x hx
  change (f.positive x : Wplus) ∈ LinearMap.range D.dMinus
  change (x : Vplus) ∈ LinearMap.range C.dMinus at hx
  rcases hx with ⟨y, hy⟩
  refine ⟨f.negative y, ?_⟩
  have h := LinearMap.congr_fun f.commutes_dMinus y
  simpa [LinearMap.comp_apply, hy] using h

theorem maps_negativeBoundaries (f : Hom C D) :
    C.negativeBoundaries ≤
      Submodule.comap f.negativeCycleMap D.negativeBoundaries := by
  intro x hx
  change (f.negative x : Wminus) ∈ LinearMap.range D.dPlus
  change (x : Vminus) ∈ LinearMap.range C.dPlus at hx
  rcases hx with ⟨y, hy⟩
  refine ⟨f.positive y, ?_⟩
  have h := LinearMap.congr_fun f.commutes_dPlus y
  simpa [LinearMap.comp_apply, hy] using h

def positiveCohomologyMap (f : Hom C D) :
    C.PositiveCohomology →ₗ[ℝ] D.PositiveCohomology :=
  Submodule.mapQ C.positiveBoundaries D.positiveBoundaries
    f.positiveCycleMap f.maps_positiveBoundaries

def negativeCohomologyMap (f : Hom C D) :
    C.NegativeCohomology →ₗ[ℝ] D.NegativeCohomology :=
  Submodule.mapQ C.negativeBoundaries D.negativeBoundaries
    f.negativeCycleMap f.maps_negativeBoundaries

@[simp]
theorem positiveCohomologyMap_mk (f : Hom C D)
    (x : LinearMap.ker C.dPlus) :
    f.positiveCohomologyMap (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.positiveCycleMap x) :=
  Submodule.mapQ_apply _ _ _ _

@[simp]
theorem negativeCohomologyMap_mk (f : Hom C D)
    (x : LinearMap.ker C.dMinus) :
    f.negativeCohomologyMap (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.negativeCycleMap x) :=
  Submodule.mapQ_apply _ _ _ _

@[simp]
theorem positiveCohomologyMap_id
    (C : TwoPeriodicComplex Vplus Vminus) :
    (id C).positiveCohomologyMap = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := C.positiveBoundaries.mkQ_surjective q
  rfl

@[simp]
theorem negativeCohomologyMap_id
    (C : TwoPeriodicComplex Vplus Vminus) :
    (id C).negativeCohomologyMap = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := C.negativeBoundaries.mkQ_surjective q
  rfl

theorem positiveCohomologyMap_comp
    (g : Hom D E) (f : Hom C D) :
    (comp g f).positiveCohomologyMap =
      g.positiveCohomologyMap.comp f.positiveCohomologyMap := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := C.positiveBoundaries.mkQ_surjective q
  rfl

theorem negativeCohomologyMap_comp
    (g : Hom D E) (f : Hom C D) :
    (comp g f).negativeCohomologyMap =
      g.negativeCohomologyMap.comp f.negativeCohomologyMap := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := C.negativeBoundaries.mkQ_surjective q
  rfl

end Hom

end TwoPeriodicComplex

end InfoGeometry.OperatorAlgebra.FiniteParityComplex
