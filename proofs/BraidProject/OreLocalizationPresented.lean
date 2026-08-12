import proofs.BraidProject.PresentedMonoid_mine
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.PresentedGroup

variable {α : Type} {rels : FreeMonoid' α → FreeMonoid' α → Prop}

def convert_rels (rels : FreeMonoid' α → FreeMonoid' α → Prop) : Set (FreeGroup α) :=
  {FreeMonoid'.lift (FreeGroup.of) x.1 * (FreeMonoid'.lift (FreeGroup.of) x.2)⁻¹ |
    x ∈ setOf (fun (a : FreeMonoid' α × FreeMonoid' α) => rels a.1 a.2)}

theorem presented_identity_works : ∀ r ∈ convert_rels rels,
    (FreeGroup.lift PresentedGroup.of r : PresentedGroup (convert_rels rels)) = 1 := by
  intro r h
  rw [← (QuotientGroup.eq_one_iff r).mpr (Subgroup.subset_normalClosure h)]
  apply @FreeGroup.induction_on α _ r
  · rfl
  · exact fun x => rfl
  · exact fun x _ => rfl
  intro _ _ hx hy
  rw [map_mul, hx, hy]
  rfl

theorem lift_eq_lift_lift_of {G : Type} {a : FreeMonoid' α} [Group G] (f : α → G) :
    FreeMonoid'.lift f a = (FreeGroup.lift f) (FreeMonoid'.lift (FreeGroup.of) a) := by
  induction a using FreeMonoid'.inductionOn' with
  | one => rfl
  | mul_of a b ha =>
      simpa [ha]
