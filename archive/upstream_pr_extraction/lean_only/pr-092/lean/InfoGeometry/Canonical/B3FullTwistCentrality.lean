import Mathlib.GroupTheory.PresentedGroup
import InfoGeometry.Physics.B3PresentedGroup

/-!
# Native full-twist centrality for the presented Artin group `B₃`

This owner uses Mathlib's presented-group generation theorem directly.  It does
not package the representation or its hypotheses in an auxiliary structure.
-/

namespace InfoGeometry.Canonical.B3FullTwistCentrality

open InfoGeometry.Physics.B3PresentedGroup

def fullTwistWord : InfoGeometry.Physics.B3PresentedGroup.B3 :=
  (PresentedGroup.of B3Gen.sig1 * PresentedGroup.of B3Gen.sig0) ^ 3

def centralizerSubgroup {G : Type*} [Group G]
    (ρ : InfoGeometry.Physics.B3PresentedGroup.B3 →* G) (z : G) :
    Subgroup InfoGeometry.Physics.B3PresentedGroup.B3 where
  carrier := {x | Commute z (ρ x)}
  one_mem' := by
    simpa using (Commute.one_right z)
  mul_mem' := by
    intro x y hx hy
    change Commute z (ρ (x * y)) at *
    rw [map_mul]
    exact hx.mul_right hy
  inv_mem' := by
    intro x hx
    change Commute z (ρ x) at hx
    change Commute z (ρ x⁻¹)
    rw [map_inv]
    exact hx.inv_right

theorem fullTwist_central_of_generator_commute
    {G : Type*} [Group G]
    (ρ : InfoGeometry.Physics.B3PresentedGroup.B3 →* G)
    (h₀ : Commute (ρ (fullTwistWord))
      (ρ (PresentedGroup.of B3Gen.sig0)))
    (h₁ : Commute (ρ (fullTwistWord))
      (ρ (PresentedGroup.of B3Gen.sig1))) :
    ∀ x : InfoGeometry.Physics.B3PresentedGroup.B3,
      Commute (ρ (fullTwistWord)) (ρ x) := by
  intro x
  let C := centralizerSubgroup ρ (ρ (fullTwistWord))
  have hgen : ∀ j : B3Gen, PresentedGroup.of j ∈ C := by
    intro j
    cases j with
    | sig0 => exact h₀
    | sig1 => exact h₁
  exact PresentedGroup.generated_by b3Relations C hgen x

end InfoGeometry.Canonical.B3FullTwistCentrality
