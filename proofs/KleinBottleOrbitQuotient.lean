import proofs.KleinBrillouinBase
import Mathlib.Topology.Constructions

/-! # The literal orbit quotient of the Brillouin torus by its glide -/

noncomputable section
namespace KleinBottleOrbitQuotient

open KleinBrillouinBase

/-- Orbit equivalence for the involution `torusGlide`. -/
def glideSetoid : Setoid BrillouinTorus where
  r x y := y = x ∨ y = torusGlide x
  iseqv := by
    constructor
    · intro x; exact Or.inl rfl
    · intro x y h
      rcases h with rfl | h
      · exact Or.inl rfl
      · right
        rw [h, torusGlide_involutive]
    · intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      · rcases hyz with rfl | hyz
        · exact Or.inr hxy
        · left
          rw [hyz, hxy, torusGlide_involutive]

/-- The topological orbit quotient.  This is the literal Klein Brillouin
quotient carrier; a separate classification theorem may identify it with a
chosen library model of the Klein bottle. -/
abbrev KleinBrillouinQuotient := Quotient glideSetoid

def quotientMap : BrillouinTorus → KleinBrillouinQuotient :=
  @Quotient.mk' BrillouinTorus glideSetoid

theorem quotientMap_surjective : Function.Surjective quotientMap :=
  by
    intro q
    refine Quotient.inductionOn q ?_
    intro k
    exact ⟨k, rfl⟩

theorem quotientMap_continuous : Continuous quotientMap :=
  continuous_quotient_mk'

theorem quotientMap_isQuotient : Topology.IsQuotientMap quotientMap :=
  isQuotientMap_quotient_mk'

@[simp] theorem quotientMap_glide (k : BrillouinTorus) :
    quotientMap (torusGlide k) = quotientMap k := by
  apply Quotient.sound
  exact Or.inr (torusGlide_involutive k).symm

theorem quotientMap_eq_iff (k q : BrillouinTorus) :
    quotientMap k = quotientMap q ↔ q = k ∨ q = torusGlide k := by
  exact Quotient.eq''

theorem torusGlide_continuous : Continuous torusGlide := by
  apply Continuous.prodMk
  · exact (continuous_fst.add continuous_const)
  · exact continuous_snd.neg

theorem klein_orbit_quotient_packet :
    Function.Surjective quotientMap ∧
    Continuous quotientMap ∧
    Topology.IsQuotientMap quotientMap ∧
    (∀ k, quotientMap (torusGlide k) = quotientMap k) :=
  ⟨quotientMap_surjective, quotientMap_continuous,
    quotientMap_isQuotient, quotientMap_glide⟩

end KleinBottleOrbitQuotient
end noncomputable section
