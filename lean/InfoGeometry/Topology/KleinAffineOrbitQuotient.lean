import InfoGeometry.Topology.KleinQuotientDeckInvariants
import InfoGeometry.Topology.KleinDeckNormalForm
import Mathlib.Topology.Constructions

/-!
# The affine orbit quotient of the Klein deck group

This file constructs the literal topological quotient of `ℝ²` by the free
normal-form deck action.  It proves the orbit equivalence relation, continuity
and quotient-map property of the projection, and the exact fibre criterion.

Proper discontinuity, local triviality as a covering, smooth-manifold charts,
fundamental-group identification, and singular-homology computations remain
separate theorems.  They are not inferred merely from forming a quotient.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinAffineOrbitQuotient

open InfoGeometry.Topology.KleinQuotientDeckInvariants

abbrev Plane := PlanePoint
abbrev Deck := KleinDeckGroup

local instance : Mul Deck := ⟨KleinDeckGroup.mul⟩
local instance : One Deck := ⟨KleinDeckGroup.one⟩
local instance : Inv Deck := ⟨KleinDeckGroup.inv⟩

def deckAct (g : Deck) (p : Plane) : Plane := deckAction g p

@[simp] theorem deckAct_one (p : Plane) : deckAct 1 p = p :=
  deckAction_one p

theorem deckAct_mul (g h : Deck) (p : Plane) :
    deckAct (g * h) p = deckAct g (deckAct h p) :=
  deckAction_mul g h p

theorem deckAct_eq_self_iff (g : Deck) (p : Plane) :
    deckAct g p = p ↔ g = 1 := by
  constructor
  · intro h
    exact action_free g p h
  · intro h
    rw [h]
    exact deckAct_one p

theorem deck_mul_right_inv (g : Deck) : g * g⁻¹ = 1 := by
  rcases g with ⟨m, n⟩
  change KleinDeckGroup.mul ⟨m, n⟩ (KleinDeckGroup.inv ⟨m, n⟩) =
    KleinDeckGroup.one
  simp only [KleinDeckGroup.mul, KleinDeckGroup.inv, KleinDeckGroup.one]
  have hs : signZ n * signZ n = 1 := by
    have h : signZ n = 1 ∨ signZ n = -1 := by simp [signZ]; omega
    rcases h with h | h <;> simp [h]
  congr 1
  · calc
      m + signZ n * (-signZ n * m) = m - (signZ n * signZ n) * m := by ring
      _ = 0 := by rw [hs]; ring
  · ring

/-- Orbit relation for the full affine deck group. -/
def orbitSetoid : Setoid Plane where
  r p q := ∃ g : Deck, deckAct g p = q
  iseqv := by
    constructor
    · intro p
      exact ⟨1, deckAct_one p⟩
    · intro p q hpq
      rcases hpq with ⟨g, rfl⟩
      refine ⟨g⁻¹, ?_⟩
      calc
        deckAct g⁻¹ (deckAct g p) = deckAct (g⁻¹ * g) p :=
          (deckAct_mul g⁻¹ g p).symm
        _ = p := by
          rw [show g⁻¹ * g = 1 by exact KleinDeckGroup.mul_left_inv g]
          exact deckAct_one p
    · intro p q r hpq hqr
      rcases hpq with ⟨g, rfl⟩
      rcases hqr with ⟨h, rfl⟩
      exact ⟨h * g, deckAct_mul h g p⟩

/-- Topological orbit quotient. -/
abbrev KleinAffineQuotient := Quotient orbitSetoid

/-- Canonical quotient projection. -/
def quotientMap : Plane → KleinAffineQuotient :=
  @Quotient.mk' Plane orbitSetoid

/-- Every quotient class has a representative. -/
theorem quotientMap_surjective : Function.Surjective quotientMap := by
  intro q
  refine Quotient.inductionOn q ?_
  intro p
  exact ⟨p, rfl⟩

/-- The canonical projection is continuous for the quotient topology. -/
theorem quotientMap_continuous : Continuous quotientMap :=
  continuous_quotient_mk'

/-- The canonical projection is a quotient map. -/
theorem quotientMap_isQuotient : Topology.IsQuotientMap quotientMap :=
  isQuotientMap_quotient_mk'

/-- Every deck transformation is invisible after projection. -/
@[simp] theorem quotientMap_deckAct (g : Deck) (p : Plane) :
    quotientMap (deckAct g p) = quotientMap p := by
  apply Quotient.sound
  exact ⟨g⁻¹, by
    calc
      deckAct g⁻¹ (deckAct g p) = deckAct (g⁻¹ * g) p :=
        (deckAct_mul g⁻¹ g p).symm
      _ = p := by
        rw [show g⁻¹ * g = 1 by exact KleinDeckGroup.mul_left_inv g]
        exact deckAct_one p⟩

/-- Equality in the quotient is exactly membership in one affine orbit. -/
theorem quotientMap_eq_iff (p q : Plane) :
    quotientMap p = quotientMap q ↔
      ∃ g : Deck, deckAct g p = q := by
  exact Quotient.eq''

/-- Freeness gives uniqueness of a deck element carrying one point to another. -/
theorem deck_element_unique {g h : Deck} {p q : Plane}
    (hg : deckAct g p = q) (hh : deckAct h p = q) :
    g = h := by
  have hfix : deckAct (h⁻¹ * g) p = p := by
    calc
      deckAct (h⁻¹ * g) p = deckAct h⁻¹ (deckAct g p) :=
        deckAct_mul h⁻¹ g p
      _ = deckAct h⁻¹ q := by rw [hg]
      _ = deckAct h⁻¹ (deckAct h p) := by rw [hh]
      _ = deckAct (h⁻¹ * h) p := (deckAct_mul h⁻¹ h p).symm
      _ = p := by
        rw [show h⁻¹ * h = 1 by exact KleinDeckGroup.mul_left_inv h]
        exact deckAct_one p
  have hid : h⁻¹ * g = 1 :=
    (deckAct_eq_self_iff (h⁻¹ * g) p).mp hfix
  apply_fun fun k => h * k at hid
  calc
    g = 1 * g := (KleinDeckGroup.one_mul g).symm
    _ = (h * h⁻¹) * g := by rw [deck_mul_right_inv h]
    _ = h * (h⁻¹ * g) := KleinDeckGroup.mul_assoc h h⁻¹ g
    _ = h * 1 := by rw [hid]
    _ = h := KleinDeckGroup.mul_one h

/-- Exact quotient packet. -/
theorem affine_orbit_quotient_packet :
    Function.Surjective quotientMap ∧
      Continuous quotientMap ∧
      Topology.IsQuotientMap quotientMap ∧
      (∀ g p, quotientMap (deckAct g p) = quotientMap p) ∧
      (∀ p q, quotientMap p = quotientMap q ↔
        ∃ g : Deck, deckAct g p = q) := by
  exact ⟨quotientMap_surjective,
    quotientMap_continuous,
    quotientMap_isQuotient,
    quotientMap_deckAct,
    quotientMap_eq_iff⟩

end InfoGeometry.Topology.KleinAffineOrbitQuotient
