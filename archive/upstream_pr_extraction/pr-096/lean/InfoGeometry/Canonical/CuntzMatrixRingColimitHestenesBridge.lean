import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.HasLimits
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Physics.HestenesKreinBilingualCarrier

/-!
# Concrete RingCat colimit for the matrix tower

`ModuleCat` is the correct carrier for the compatible normalized trace, but it
forgets multiplication.  This owner supplies the parallel native `RingCat`
filtered colimit of the same matrix stages, so the Hestenes bilingual left and
opposite-right actions live on an actual algebraic colimit carrier.

The trace remains the separate compatible linear readout from
`CuntzMatrixTraceTower`; no multiplicative state claim is made.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixRingColimitHestenesBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Physics

def ringDiagram : ℕ ⥤ RingCat where
  obj n := RingCat.of (MatrixStage n)
  map {m n} f := RingCat.ofHom
    (concreteMap (leOfHom f)).toRingHom
  map_id n := by
    apply RingCat.hom_ext
    ext A
    have hid : (concreteMap (le_refl n)) A = A := by
      rw [concreteMap_id]
      rfl
    exact congrFun (congrFun hid _) _
  map_comp {m n k} f g := by
    apply RingCat.hom_ext
    ext A
    have hcomp : (concreteMap (leOfHom (f ≫ g))) A =
        (concreteMap (leOfHom g)) ((concreteMap (leOfHom f)) A) := by
      have h := concreteMap_comp (leOfHom f) (leOfHom g)
      exact (congrArg (fun F => F A) h).symm
    exact congrFun (congrFun hcomp _) _

abbrev RingColimit : Type := ((colimit ringDiagram : RingCat) : Type)

abbrev RingColimitObject : RingCat := (colimit.cocone ringDiagram).pt

/-- The native categorical colimit certificate for the matrix tower. -/
def ringColimit_isColimit :
    IsColimit (colimit.cocone ringDiagram) := by
  exact colimit.isColimit ringDiagram

def ringColimitInclusion (n : ℕ) : MatrixStage n →+* RingColimit :=
  (colimit.ι ringDiagram n).hom

/-- The universal lift from any compatible `RingCat` cocone on the matrix tower. -/
def ringColimitLift (c : Cocone ringDiagram) :
    (colimit.cocone ringDiagram).pt ⟶ c.pt :=
  ringColimit_isColimit.desc c

@[simp] theorem ringColimitLift_fac (c : Cocone ringDiagram) (n : ℕ) :
    (colimit.cocone ringDiagram).ι.app n ≫ ringColimitLift c = c.ι.app n := by
  exact ringColimit_isColimit.fac c n

/-- Maps out of the matrix colimit are determined by their stage restrictions. -/
theorem ringColimit_hom_ext {X : RingCat}
    (f g : (colimit.cocone ringDiagram).pt ⟶ X)
    (h : ∀ n, (colimit.cocone ringDiagram).ι.app n ≫ f =
      (colimit.cocone ringDiagram).ι.app n ≫ g) :
    f = g := by
  exact ringColimit_isColimit.hom_ext h

theorem ringColimitInclusion_mul (n : ℕ) (A B : MatrixStage n) :
    ringColimitInclusion n (A * B) =
      ringColimitInclusion n A * ringColimitInclusion n B := by
  exact (ringColimitInclusion n).map_mul A B

theorem ringColimitInclusion_one (n : ℕ) :
    ringColimitInclusion n (1 : MatrixStage n) = 1 := by
  exact (ringColimitInclusion n).map_one

theorem ringColimitInclusion_zero (n : ℕ) :
    ringColimitInclusion n (0 : MatrixStage n) = 0 := by
  exact (ringColimitInclusion n).map_zero

theorem ringColimitInclusion_add (n : ℕ) (A B : MatrixStage n) :
    ringColimitInclusion n (A + B) =
      ringColimitInclusion n A + ringColimitInclusion n B := by
  exact (ringColimitInclusion n).map_add A B

theorem ringColimit_bilingual_left_right_commute
    (a x : RingColimit) (b : RingColimitᵐᵒᵖ) :
    bilingualLeftAction a (bilingualRightOppositeAction x b) =
      bilingualRightOppositeAction (bilingualLeftAction a x) b := by
  exact InfoGeometry.Physics.bilingual_left_right_commute a x b

theorem ringColimit_stage_transition
    {m n : ℕ} (hmn : m ≤ n) (A : MatrixStage m) :
    ringColimitInclusion n (concreteMap hmn A) =
      ringColimitInclusion m A := by
  have h := (colimit.cocone ringDiagram).w (homOfLE hmn)
  have h_eval := congrArg (fun (f : ringDiagram.obj m ⟶ colimit ringDiagram) => f.hom A) h
  exact h_eval

end InfoGeometry.Canonical.CuntzMatrixRingColimitHestenesBridge
