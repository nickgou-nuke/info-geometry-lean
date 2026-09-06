import proofs.KleinBottleOrbitQuotient
import proofs.KleinSixStateBundle
import Mathlib.Topology.Constructions

/-!
# Six-state associated quotient over the Klein Brillouin orbit space

This file constructs the literal quotient of the trivial six-state carrier by
the simultaneous base glide and internal sheet reflection.  It deliberately
does not claim local triviality; that is a separate `VectorBundle` theorem.
-/

noncomputable section
namespace KleinSixStateAssociatedQuotient

open KleinBrillouinBase KleinBottleOrbitQuotient
open KleinSixStateBundle TwoSheetThreeColorWeyl

abbrev State := Fin 2 × Fin 3 → ℂ

/-- Simultaneous glide on the Brillouin base and the six-state fibre. -/
def totalGlide (p : BrillouinTorus × State) : BrillouinTorus × State :=
  (torusGlide p.1, theta.mulVec p.2)

theorem totalGlide_involutive (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Involutive totalGlide := by
  intro p
  rcases p with ⟨k, v⟩
  apply Prod.ext
  · exact torusGlide_involutive k
  · change theta.mulVec (theta.mulVec v) = v
    rw [Matrix.mulVec_mulVec, theta_sq ω hω]
    exact Matrix.one_mulVec v

theorem totalGlide_ne_self (p : BrillouinTorus × State) :
    totalGlide p ≠ p := by
  intro h
  have hbase := congrArg Prod.fst h
  exact torusGlide_ne_self p.1 hbase

/-- Orbit relation of the simultaneous base/fibre involution. -/
def totalGlideSetoid (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    Setoid (BrillouinTorus × State) where
  r x y := y = x ∨ y = totalGlide x
  iseqv := by
    constructor
    · intro x; exact Or.inl rfl
    · intro x y h
      rcases h with rfl | h
      · exact Or.inl rfl
      · right
        rw [h, totalGlide_involutive ω hω]
    · intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      · rcases hyz with rfl | hyz
        · exact Or.inr hxy
        · left
          rw [hyz, hxy, totalGlide_involutive ω hω]

/-- Total carrier of the associated six-state orbit quotient. -/
abbrev AssociatedSixState (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :=
  Quotient (totalGlideSetoid ω hω)

def totalQuotientMap (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    BrillouinTorus × State → AssociatedSixState ω hω :=
  @Quotient.mk' _ (totalGlideSetoid ω hω)

theorem totalQuotientMap_surjective (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Surjective (totalQuotientMap ω hω) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro p
  exact ⟨p, rfl⟩

private def representativeBase (p : BrillouinTorus × State) :
    KleinBrillouinQuotient := quotientMap p.1

private theorem representativeBase_respects (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (x y : BrillouinTorus × State)
    (h : (totalGlideSetoid ω hω).r x y) :
    representativeBase x = representativeBase y := by
  rcases h with rfl | h
  · rfl
  · rw [h]
    exact (quotientMap_glide x.1).symm

/-- Projection of the associated quotient to the literal Klein orbit base. -/
def bundleProjection (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    AssociatedSixState ω hω → KleinBrillouinQuotient :=
  Quotient.lift representativeBase (representativeBase_respects ω hω)

@[simp] theorem bundleProjection_mk (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (p : BrillouinTorus × State) :
    bundleProjection ω hω (totalQuotientMap ω hω p) = quotientMap p.1 := rfl

theorem bundleProjection_continuous (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    Continuous (bundleProjection ω hω) := by
  apply continuous_quot_lift
  exact quotientMap_continuous.comp continuous_fst

theorem bundleProjection_surjective (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Surjective (bundleProjection ω hω) := by
  intro q
  obtain ⟨k, rfl⟩ := quotientMap_surjective q
  exact ⟨totalQuotientMap ω hω (k, 0), rfl⟩

theorem associated_quotient_packet (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Surjective (bundleProjection ω hω) ∧
    Continuous (bundleProjection ω hω) :=
  ⟨bundleProjection_surjective ω hω, bundleProjection_continuous ω hω⟩

end KleinSixStateAssociatedQuotient
end noncomputable section
