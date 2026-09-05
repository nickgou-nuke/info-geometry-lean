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

open InfoGeometry.Topology.KleinDeckNormalForm

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
        _ = p := by simp [deckAct_one]
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
      _ = p := by simp [deckAct_one]⟩

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
      _ = p := by simp [deckAct_one]
  have hid : h⁻¹ * g = 1 :=
    (deckAct_eq_self_iff (h⁻¹ * g) p).mp hfix
  apply_fun fun k => h * k at hid
  simpa [mul_assoc] using hid

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
