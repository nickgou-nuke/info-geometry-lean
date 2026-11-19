/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CentralPowerLocalization
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCentralizer

/-!
# Faithful centralizer localization and the Cayley unitary

This instantiates the native Ore construction at `1 + V` inside the native
star centralizer. The degree-zero map is injective under three-square
faithfulness. The Cayley numerator gives a genuine unitary in that localized
ring, and on shell its fraction is exactly the image of the integral Weyl
element. The off-shell localization is not asserted to act on the original
ambient ring without an additional representation of the inverse denominator.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.GramCentralLocalization

open _root_.OperatorAlgebra.PeirceSpine.RealBdGKreinChiralIdealBridge
open CentralPowerLocalization PeirceCentralizer IntegralWeyl

variable {B : Type*} [Ring B] [StarRing B]

/-- The actual noncommutative Ore localization of the support centralizer. -/
abbrev Localization (N : B) :=
  RingLocalization (denominator N) (denominator_central N)

instance (N : B) : StarRing (Localization N) :=
  localizationStarRing (denominator N) (denominator_central N)
    (denominator_selfAdjoint N).star_eq

/-- The canonical ring map into the centralizer localization. -/
def embedding (N : B) : supportCentralizer N →+* Localization N :=
  degreeZero (denominator N) (denominator_central N)

theorem embedding_injective (hF : ThreeSumStarFaithful B) (N : B) :
    Function.Injective (embedding N) :=
  degreeZero_injective _ _ (denominator_left_injective hF N)

theorem embedding_star (N : B) (X : supportCentralizer N) :
    embedding N (star X) = star (embedding N X) :=
  (degreeZero_star (denominator N) (denominator_central N)
    (denominator_selfAdjoint N).star_eq X).symm

theorem fraction_star (N : B) (a : ℕ × supportCentralizer N) :
    star (ofPair (denominator N) (denominator_central N) a) =
      ofPair (denominator N) (denominator_central N) (dayStar a) := rfl

/-- The class `[1,1]` is an actual two-sided inverse of the embedded denominator. -/
theorem denominator_inverse (N : B) :
    embedding N (denominator N) *
        ofPair (denominator N) (denominator_central N) (1, 1) = 1 ∧
      ofPair (denominator N) (denominator_central N) (1, 1) *
        embedding N (denominator N) = 1 := by
  simp only [embedding, degreeZero_apply]
  let s := denominator N
  let hs := denominator_central N
  constructor
  · calc
      _ = ofPair s hs (dayMul (0, s) (1, 1)) := (ofPair_mul s hs _ _).symm
      _ = ofPair s hs (0, 1) := (ofPair_eq_iff s hs _ _).mpr ⟨0, by simp [dayMul]⟩
      _ = 1 := ofPair_one s hs
  · calc
      _ = ofPair s hs (dayMul (1, 1) (0, s)) := (ofPair_mul s hs _ _).symm
      _ = ofPair s hs (0, 1) := (ofPair_eq_iff s hs _ _).mpr ⟨0, by simp [dayMul]⟩
      _ = 1 := ofPair_one s hs

/-- The polynomial Cayley numerator belongs to the lawful coefficient algebra. -/
def cayleyNumerator (N : B) (hN : N * N = 0) : supportCentralizer N :=
  ⟨1 - V N + (J N + J N), mem_supportCentralizer.mpr (by
    change V N * (1 - V N + (J N + J N)) = (1 - V N + (J N + J N)) * V N
    have hc := (support_commute_rotor hN).eq
    noncomm_ring [hc])⟩

/-- The integral element also belongs to the centralizer before normalization. -/
def integralElement (N : B) (hN : N * N = 0) : supportCentralizer N :=
  ⟨1 - V N + J N, mem_supportCentralizer.mpr (by
    change V N * (1 - V N + J N) = (1 - V N + J N) * V N
    have hc := (support_commute_rotor hN).eq
    noncomm_ring [hc])⟩

theorem cayleyNumerator_grams (N : B) (hN : N * N = 0) :
    star (cayleyNumerator N hN) * cayleyNumerator N hN = denominator N * denominator N ∧
      cayleyNumerator N hN * star (cayleyNumerator N hN) = denominator N * denominator N := by
  constructor
  · apply Subtype.ext
    exact (cayley_numerator_grams hN).1
  · apply Subtype.ext
    exact (cayley_numerator_grams hN).2

/-- The actual fraction `[1,1-V+2J]`, with its denominator in the centralizer. -/
def cayleyFraction (N : B) (hN : N * N = 0) : Localization N :=
  ofPair (denominator N) (denominator_central N) (1, cayleyNumerator N hN)

theorem cayleyFraction_mem_unitary (N : B) (hN : N * N = 0) :
    cayleyFraction N hN ∈ unitary (Localization N) := by
  let s := denominator N
  let hs := denominator_central N
  have hn := cayleyNumerator_grams N hN
  constructor
  · change star (ofPair s hs (1, cayleyNumerator N hN)) *
        ofPair s hs (1, cayleyNumerator N hN) = 1
    rw [fraction_star, ← ofPair_mul, ← ofPair_one s hs]
    apply (ofPair_eq_iff s hs _ _).mpr
    exact ⟨0, by simpa only [dayStar, dayMul, pow_zero, pow_one, one_mul,
      mul_one, pow_add] using hn.1⟩
  · change ofPair s hs (1, cayleyNumerator N hN) *
        star (ofPair s hs (1, cayleyNumerator N hN)) = 1
    rw [fraction_star, ← ofPair_mul, ← ofPair_one s hs]
    apply (ofPair_eq_iff s hs _ _).mpr
    exact ⟨0, by simpa only [dayStar, dayMul, pow_zero, pow_one, one_mul,
      mul_one, pow_add] using hn.2⟩

/-- The localized Cayley fraction, bundled as a native unitary. -/
def cayleyUnitary (N : B) (hN : N * N = 0) : unitary (Localization N) :=
  ⟨cayleyFraction N hN, cayleyFraction_mem_unitary N hN⟩

/-- On shell the localized Cayley unitary is already the image of the integral element. -/
theorem cayleyFraction_eq_integral_image (hF : ThreeSumStarFaithful B)
    {N : B} (hN : N * N = 0) (hV : V N * V N = V N) :
    cayleyFraction N hN = embedding N (integralElement N hN) := by
  simp only [cayleyFraction, embedding, degreeZero_apply]
  apply (ofPair_eq_iff _ _ _ _).mpr
  refine ⟨0, ?_⟩
  simp only [pow_zero, pow_one, one_mul]
  apply Subtype.ext
  exact (cayley_numerator_on_shell hN (regular_of_support_idempotent hF hN hV)).symm

/-- Adding the identity does not change the centralizer. -/
theorem commute_denominator_iff {N X : B} :
    Commute (1 + V N) X ↔ X ∈ supportCentralizer N := by
  rw [mem_supportCentralizer]
  constructor
  · intro h
    apply add_left_cancel (a := X)
    simpa only [add_mul, mul_add, one_mul, mul_one] using h.eq
  · intro h
    change (1 + V N) * X = X * (1 + V N)
    simp only [add_mul, mul_add, one_mul, mul_one, h.eq]

/-- Exact ambient multiplication obstruction, identified with the actual centralizer. -/
theorem ambient_multiplication_iff (hF : ThreeSumStarFaithful B) (N X : B) :
    DayRel (1 + V N) (dayMul (0, X) (0, 1)) (dayMul (0, X) (1, 1 + V N)) ↔
      X ∈ supportCentralizer N := by
  have hreg : Function.Injective (fun Y : B => (1 + V N) * Y) :=
    hF.one_add_gram_left_injective N
  exact (dayMul_identity_shift_iff hreg X).trans
    (commute_denominator_iff (N := N) (X := X))

theorem ambient_star_iff (hF : ThreeSumStarFaithful B) (N X : B) :
    DayRel (1 + V N) (dayStar (0, X)) (dayStar (1, (1 + V N) * X)) ↔
      X ∈ supportCentralizer N := by
  have hreg : Function.Injective (fun Y : B => (1 + V N) * Y) :=
    hF.one_add_gram_left_injective N
  have hself : star (1 + V N) = 1 + V N := by
    simp only [star_add, star_one, V_star]
  exact (dayStar_numerator_shift_iff hself hreg X).trans
    (commute_denominator_iff (N := N) (X := X))

end InfoGeometry.OperatorAlgebra.PeirceSpine.GramCentralLocalization
