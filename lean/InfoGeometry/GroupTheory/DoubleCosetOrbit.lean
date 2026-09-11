import InfoGeometry.GroupTheory.DoubleCoset
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Double cosets as product-group orbits

The product group `H × K` acts on `G` by
`(h, k) • x = h * x * k⁻¹`.  Its orbit through `g` is exactly `H g K`.
This owner stops at the native orbit--stabilizer identity; identifying the
stabilizer with `H ∩ g K g⁻¹` is a separate conjugation-equivalence layer.
-/

namespace InfoGeometry.GroupTheory.DoubleCoset

variable {G : Type*} [Group G]

namespace ProductAction

instance (H K : Subgroup G) : SMul (H × K) G where
  smul hk x := (hk.1 : G) * x * (hk.2 : G)⁻¹

instance (H K : Subgroup G) : MulAction (H × K) G where
  one_smul x := by
    change (1 : G) * x * (1 : G)⁻¹ = x
    simp
  mul_smul a b x := by
    change ((a.1 : G) * b.1) * x * ((a.2 : G) * b.2)⁻¹ =
      (a.1 : G) * ((b.1 : G) * x * (b.2 : G)⁻¹) * (a.2 : G)⁻¹
    simp only [mul_inv_rev]
    group

theorem orbit_eq_doubleCoset (H K : Subgroup G) (g : G) :
    MulAction.orbit (H × K) g = doubleCoset H g K := by
  ext x
  constructor
  · intro hx
    rcases MulAction.mem_orbit_iff.mp hx with ⟨hk, rfl⟩
    refine ⟨hk.1, hk.1.property, hk.2⁻¹, K.inv_mem hk.2.property, ?_⟩
    rfl
  · intro hx
    rcases hx with ⟨h, hh, k, hk, rfl⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨⟨h, hh⟩, ⟨k⁻¹, K.inv_mem hk⟩⟩, ?_⟩
    change h * g * (↑(k⁻¹) : G)⁻¹ = h * g * k
    simp

end ProductAction

def conjugateSubgroup (g : G) (K : Subgroup G) : Subgroup G where
  carrier := {x : G | g⁻¹ * x * g ∈ K}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simpa [mul_assoc] using K.mul_mem hx hy
  inv_mem' := by
    intro x hx
    simpa [mul_assoc] using K.inv_mem hx

def intersectionSubgroup (H K : Subgroup G) : Subgroup G where
  carrier := {x : G | x ∈ H ∧ x ∈ K}
  one_mem' := ⟨H.one_mem, K.one_mem⟩
  mul_mem' := by
    intro x y hx hy
    exact ⟨H.mul_mem hx.1 hy.1, K.mul_mem hx.2 hy.2⟩
  inv_mem' := by
    intro x hx
    exact ⟨H.inv_mem hx.1, K.inv_mem hx.2⟩

def stabilizerEquivIntersection (H K : Subgroup G) (g : G) :
    MulAction.stabilizer (H × K) g ≃
      intersectionSubgroup H (conjugateSubgroup g K) where
  toFun p :=
    ⟨p.1.1, p.1.1.property, by
      have hp := p.2
      change (p.1.1 : G) * g * (p.1.2 : G)⁻¹ = g at hp
      change g⁻¹ * (p.1.1 : G) * g ∈ K
      rw [show g⁻¹ * (p.1.1 : G) * g = (p.1.2 : G) by
        calc
          g⁻¹ * (p.1.1 : G) * g =
              g⁻¹ * ((p.1.1 : G) * g * (p.1.2 : G)⁻¹) *
                (p.1.2 : G) := by group
          _ = g⁻¹ * g * (p.1.2 : G) := by rw [hp]
          _ = (p.1.2 : G) := by group]
      exact p.1.2.property⟩
  invFun x :=
    ⟨⟨⟨x.1, x.2.1⟩,
        ⟨g⁻¹ * (x.1 : G) * g, by
          exact x.2.2⟩⟩,
      by
        change (x.1 : G) * g * (g⁻¹ * (x.1 : G) * g)⁻¹ = g
        group⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change g⁻¹ * (p.1.1 : G) * g = (p.1.2 : G)
      have hp := p.2
      change (p.1.1 : G) * g * (p.1.2 : G)⁻¹ = g at hp
      calc
        g⁻¹ * (p.1.1 : G) * g =
            g⁻¹ * ((p.1.1 : G) * g * (p.1.2 : G)⁻¹) *
              (p.1.2 : G) := by group
        _ = g⁻¹ * g * (p.1.2 : G) := by rw [hp]
        _ = (p.1.2 : G) := by group
  right_inv x := by
    apply Subtype.ext
    rfl

section Finite

variable (H K : Subgroup G) (g : G)

theorem doubleCoset_card_mul_stabilizer_card
    [Fintype H] [Fintype K]
    [Fintype (MulAction.orbit (H × K) g)]
    [Fintype (MulAction.stabilizer (H × K) g)]
    [Fintype {x : G // x ∈ doubleCoset H g K}] :
    Fintype.card {x : G // x ∈ doubleCoset H g K} *
        Fintype.card (MulAction.stabilizer (H × K) g) =
      Fintype.card (H × K) := by
  rw [← Fintype.card_congr (Equiv.setCongr
    (ProductAction.orbit_eq_doubleCoset H K g))]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (H × K) g

theorem doubleCoset_card_mul_intersection_card
    [Fintype H] [Fintype K]
    [Fintype (MulAction.orbit (H × K) g)]
    [Fintype (MulAction.stabilizer (H × K) g)]
    [Fintype {x : G // x ∈ doubleCoset H g K}]
    [Fintype (intersectionSubgroup H (conjugateSubgroup g K))] :
    Fintype.card {x : G // x ∈ doubleCoset H g K} *
        Fintype.card (intersectionSubgroup H (conjugateSubgroup g K)) =
      Fintype.card H * Fintype.card K := by
  have h := doubleCoset_card_mul_stabilizer_card H K g
  calc
    Fintype.card {x : G // x ∈ doubleCoset H g K} *
          Fintype.card (intersectionSubgroup H (conjugateSubgroup g K)) =
        Fintype.card {x : G // x ∈ doubleCoset H g K} *
          Fintype.card (MulAction.stabilizer (H × K) g) := by
            rw [Fintype.card_congr (stabilizerEquivIntersection H K g)]
    _ = Fintype.card (H × K) := h
    _ = Fintype.card H * Fintype.card K := by
      simp [Fintype.card_prod]

theorem doubleCoset_card_eq_card_mul_of_intersection_bot
    [Fintype H] [Fintype K]
    [Fintype (MulAction.orbit (H × K) g)]
    [Fintype (MulAction.stabilizer (H × K) g)]
    [Fintype {x : G // x ∈ doubleCoset H g K}]
    [Fintype (intersectionSubgroup H (conjugateSubgroup g K))]
    (hbot : intersectionSubgroup H (conjugateSubgroup g K) = ⊥) :
    Fintype.card {x : G // x ∈ doubleCoset H g K} =
      Fintype.card H * Fintype.card K := by
  have h := doubleCoset_card_mul_intersection_card H K g
  have hcard :
      Fintype.card (intersectionSubgroup H (conjugateSubgroup g K)) = 1 := by
    rw [← Nat.card_eq_fintype_card, Subgroup.card_eq_one.mpr hbot]
  rw [hcard, mul_one] at h
  exact h

end Finite

end InfoGeometry.GroupTheory.DoubleCoset
