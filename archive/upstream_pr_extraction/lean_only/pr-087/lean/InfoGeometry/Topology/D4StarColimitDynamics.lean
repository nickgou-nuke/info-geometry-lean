import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import InfoGeometry.Topology.ContinuousModularFlowQuotientDescent

namespace InfoGeometry.Topology.ColimitDynamics

open CategoryTheory Limits
open InfoGeometry.Topology.ContinuousQuotientDescent

variable {J : Type*} [Category J]

/-!
# Colimit dynamics and stationary observational readouts

This owner descends a genuine discrete flow through an arbitrary existing
`TopCat` colimit.  The carrier is topological only: it does not claim to be a
noncommutative algebraic direct limit.

No KMS condition, analytic continuation, crossed-product algebra, or orbifold
structure is asserted here.
-/

structure TopologicalDiscreteFlowSystem where
  carrier : J ⥤ TopCat
  flow : ∀ j, ℤ → (carrier.obj j ⟶ carrier.obj j)
  flow_zero : ∀ j, flow j 0 = 𝟙 (carrier.obj j)
  flow_add : ∀ (j : J) (s t : ℤ),
    flow j (s + t) = flow j t ≫ flow j s
  flow_natural : ∀ {i j : J} (f : i ⟶ j) (t : ℤ),
    flow i t ≫ carrier.map f = carrier.map f ≫ flow j t

variable (D : TopologicalDiscreteFlowSystem (J := J))
variable (C : Cocone D.carrier)
variable (hC : IsColimit C)

noncomputable def colimitEndomorphism (t : ℤ) : C.pt ⟶ C.pt :=
  hC.desc {
    pt := C.pt
    ι := {
      app := fun j => D.flow j t ≫ C.ι.app j
      naturality := fun i j f => by
        dsimp
        rw [Category.comp_id]
        rw [← Category.assoc]
        rw [← D.flow_natural f t]
        rw [Category.assoc]
        rw [C.w f]
    }
  }

@[simp] theorem colimitEndomorphism_ι (j : J) (t : ℤ) :
    C.ι.app j ≫ colimitEndomorphism D C hC t =
      D.flow j t ≫ C.ι.app j := by
  exact hC.fac _ j

@[simp] theorem colimitEndomorphism_zero :
    colimitEndomorphism D C hC 0 = 𝟙 C.pt := by
  apply hC.hom_ext
  intro j
  rw [colimitEndomorphism_ι, D.flow_zero]
  simp

theorem colimitEndomorphism_add (s t : ℤ) :
    colimitEndomorphism D C hC (s + t) =
      colimitEndomorphism D C hC t ≫
        colimitEndomorphism D C hC s := by
  apply hC.hom_ext
  intro j
  calc
    C.ι.app j ≫ colimitEndomorphism D C hC (s + t) =
        D.flow j (s + t) ≫ C.ι.app j := by
          rw [colimitEndomorphism_ι]
    _ = (D.flow j t ≫ D.flow j s) ≫ C.ι.app j := by
          rw [D.flow_add]
    _ = D.flow j t ≫ (D.flow j s ≫ C.ι.app j) := by
          rw [Category.assoc]
    _ = D.flow j t ≫
        (C.ι.app j ≫ colimitEndomorphism D C hC s) := by
          rw [colimitEndomorphism_ι]
    _ = (D.flow j t ≫ C.ι.app j) ≫
        colimitEndomorphism D C hC s := by
          rw [Category.assoc]
    _ = (C.ι.app j ≫ colimitEndomorphism D C hC t) ≫
        colimitEndomorphism D C hC s := by
          rw [colimitEndomorphism_ι]
    _ = C.ι.app j ≫
        (colimitEndomorphism D C hC t ≫
          colimitEndomorphism D C hC s) := by
          rw [Category.assoc]

noncomputable def colimitFlow : ContinuousFlow C.pt where
  flow := fun t => colimitEndomorphism D C hC t
  zero_law := by
    intro x
    have h := congrArg (fun f : C.pt ⟶ C.pt => f x)
      (colimitEndomorphism_zero (D := D) (C := C) (hC := hC))
    exact h
  add_law := by
    intro s t x
    have h := congrArg (fun f : C.pt ⟶ C.pt => f x)
      (colimitEndomorphism_add (D := D) (C := C) (hC := hC) s t)
    exact h
  continuous := by
    intro t
    exact (colimitEndomorphism D C hC t).hom.continuous

structure FlowInvariantObservableData (BoolCat : TopCat) where
  stageObservable :
    D.carrier ⟶ ((Functor.const J : TopCat ⥤ J ⥤ TopCat).obj BoolCat)
  observable_invariant : ∀ (j : J) (t : ℤ),
    D.flow j t ≫ stageObservable.app j = stageObservable.app j

variable (BoolCat : TopCat)
variable (Obs : FlowInvariantObservableData D BoolCat)

def observableCocone : Cocone D.carrier where
  pt := BoolCat
  ι := Obs.stageObservable

noncomputable def colimitObservable : C.pt ⟶ BoolCat :=
  hC.desc (observableCocone D BoolCat Obs)

@[simp] theorem colimitObservable_stage (j : J) :
    C.ι.app j ≫ colimitObservable D C hC BoolCat Obs =
      Obs.stageObservable.app j := by
  exact hC.fac _ j

theorem colimitObservable_invariant (t : ℤ) :
    colimitEndomorphism D C hC t ≫
        colimitObservable D C hC BoolCat Obs =
      colimitObservable D C hC BoolCat Obs := by
  apply hC.hom_ext
  intro j
  calc
    C.ι.app j ≫
        (colimitEndomorphism D C hC t ≫
          colimitObservable D C hC BoolCat Obs)
        = (C.ι.app j ≫ colimitEndomorphism D C hC t) ≫
          colimitObservable D C hC BoolCat Obs := by
            rw [← Category.assoc]
    _ = (D.flow j t ≫ C.ι.app j) ≫
          colimitObservable D C hC BoolCat Obs := by
            rw [colimitEndomorphism_ι]
    _ = D.flow j t ≫
          (C.ι.app j ≫ colimitObservable D C hC BoolCat Obs) := by
            rw [Category.assoc]
    _ = D.flow j t ≫ Obs.stageObservable.app j := by
            rw [colimitObservable_stage D C hC BoolCat Obs j]
    _ = Obs.stageObservable.app j := Obs.observable_invariant j t
    _ = C.ι.app j ≫ colimitObservable D C hC BoolCat Obs := by
            exact (colimitObservable_stage D C hC BoolCat Obs j).symm

end InfoGeometry.Topology.ColimitDynamics
