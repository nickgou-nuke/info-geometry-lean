import InfoGeometry.Topology.D4StarGraphContinuousAction
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-!
## The orbit quotient of the finite D₄ star

The quotient remembers exactly two observational classes: the centre and the
outer orbit.  This is a set-theoretic quotient equipped with Lean's quotient
topology; no stronger orbifold claim is made here.
-/

def starOrbitRel : FourPlaneVertex → FourPlaneVertex → Prop
  | Sum.inr _, Sum.inr _ => True
  | Sum.inl _, Sum.inl _ => True
  | _, _ => False

theorem starOrbitRel_refl (v : FourPlaneVertex) : starOrbitRel v v := by
  cases v <;> simp [starOrbitRel]

theorem starOrbitRel_symm {v w : FourPlaneVertex} :
    starOrbitRel v w → starOrbitRel w v := by
  cases v <;> cases w <;> simp [starOrbitRel]

theorem starOrbitRel_trans {u v w : FourPlaneVertex} :
    starOrbitRel u v → starOrbitRel v w → starOrbitRel u w := by
  cases u <;> cases v <;> cases w <;> simp [starOrbitRel]

instance starOrbitSetoid : Setoid FourPlaneVertex where
  r := starOrbitRel
  iseqv :=
    { refl := starOrbitRel_refl
      symm := starOrbitRel_symm
      trans := starOrbitRel_trans }

abbrev D4StarQuotient := Quotient starOrbitSetoid

def starQuotientMap : FourPlaneVertex → D4StarQuotient :=
  Quotient.mk'

theorem outer_vertices_same_class (c d : ColorChannel) :
    starQuotientMap (outerVertex c) = starQuotientMap (outerVertex d) := by
  exact Quotient.sound (by
    change starOrbitRel (outerVertex c) (outerVertex d)
    cases c <;> cases d <;> simp [starOrbitRel, outerVertex])

theorem centre_not_outer_class (c : ColorChannel) :
    starQuotientMap centralVertex ≠ starQuotientMap (outerVertex c) := by
  intro h
  have hr : starOrbitRel centralVertex (outerVertex c) := Quotient.exact h
  simpa [centralVertex, outerVertex, starOrbitRel] using hr

theorem centre_class_eq_iff {v : FourPlaneVertex} :
    starQuotientMap v = starQuotientMap centralVertex ↔ v = centralVertex := by
  constructor
  · intro h
    cases v with
    | inl c =>
        exact False.elim (centre_not_outer_class c (h.symm))
    | inr u => rfl
  · intro h
    simpa [h]

def quotientColorAction (σ : Equiv.Perm ColorChannel) :
    D4StarQuotient → D4StarQuotient :=
  Quotient.map (vertexPermutation σ) (by
    intro v w h
    cases v <;> cases w <;> simpa [starOrbitRel, vertexPermutation] using h)

theorem quotientColorAction_centre (σ : Equiv.Perm ColorChannel) :
    quotientColorAction σ (starQuotientMap centralVertex) =
      starQuotientMap centralVertex := by
  rfl

theorem quotientColorAction_outer_moved (σ : Equiv.Perm ColorChannel) (c : ColorChannel) :
    quotientColorAction σ (starQuotientMap (outerVertex c)) =
      starQuotientMap (outerVertex (σ c)) := by
  rfl

theorem quotientColorAction_outer_orbit (σ : Equiv.Perm ColorChannel) :
    ∀ c d : ColorChannel,
      quotientColorAction σ (starQuotientMap (outerVertex c)) =
        starQuotientMap (outerVertex d) := by
  intro c d
  rw [quotientColorAction_outer_moved, outer_vertices_same_class]

end InfoGeometry.Topology.PauliJungD4Star
