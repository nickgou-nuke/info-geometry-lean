/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceStarNaturality

/-!
# Peirce parity under exchange of the complementary sheets

A ring homomorphism sending `p` to `1 - p` reverses the Peirce reflection,
but commutes with its conjugation action.  It also preserves the existing
division-free even and odd Peirce projections.  These identities retain the
order of multiplication in an arbitrary associative ring.

The identities themselves do not require idempotence.  When `p` is
idempotent, `PeirceGrading` supplies the complementary projection and grading
laws.  This owner supplies algebraic compatibility; continuity and descent
to spaces of equivariant sections are separate constructions.
-/

namespace InfoGeometry.Core.PeirceSheetExchange

open PeirceDecomposition PeirceGrading

variable {A B : Type*} [Ring A] [Ring B]

/-- Reversing the sheet labels negates their reflection. -/
theorem reflection_complement (p : A) :
    reflection (1 - p) = -reflection p := by
  unfold reflection
  noncomm_ring

/-- The two diagonal corners are exchanged, so their sum is unchanged. -/
theorem even_complement (p x : A) :
    even (1 - p) x = even p x := by
  simp only [even_apply, sub_sub_cancel]
  exact add_comm _ _

/-- The complementary odd projection is unchanged by relabelling. -/
theorem odd_complement (p x : A) :
    odd (1 - p) x = odd p x := by
  change x - even (1 - p) x = x - even p x
  rw [even_complement]

/-- The two sign reversals cancel in reflection conjugation. -/
theorem conjugation_complement (p x : A) :
    conjugation (1 - p) x = conjugation p x := by
  simp only [conjugation_apply, reflection_complement, neg_mul, mul_neg, neg_neg]

/-- Naturality of the native even Peirce projection. -/
theorem map_even (f : A →+* B) (p x : A) :
    f (even p x) = even (f p) (f x) := by
  simp only [even_apply, map_add, map_mul, map_sub, map_one]

/-- Naturality of the native odd Peirce projection. -/
theorem map_odd (f : A →+* B) (p x : A) :
    f (odd p x) = odd (f p) (f x) := by
  change f (x - even p x) = f x - even (f p) (f x)
  rw [map_sub, map_even]

/-- Naturality of reflection conjugation, using the existing reflection map. -/
theorem map_conjugation (f : A →+* B) (p x : A) :
    f (conjugation p x) = conjugation (f p) (f x) := by
  simp only [conjugation_apply, map_mul, PeirceStarNaturality.map_reflection]

/-- Sheet exchange reverses the cut in the ambient ring. -/
theorem map_reflection_of_sheet_exchange (f : A →+* A) {p : A}
    (hf : f p = 1 - p) :
    f (reflection p) = -reflection p := by
  rw [PeirceStarNaturality.map_reflection, hf, reflection_complement]

/-- Sheet exchange preserves operator parity: `rho (Pi x) = Pi (rho x)`. -/
theorem map_conjugation_of_sheet_exchange (f : A →+* A) {p : A}
    (hf : f p = 1 - p) (x : A) :
    f (conjugation p x) = conjugation p (f x) := by
  rw [map_conjugation, hf, conjugation_complement]

/-- The same compatibility as a native commutation predicate on functions. -/
theorem conjugation_commute_of_sheet_exchange (f : A →+* A) {p : A}
    (hf : f p = 1 - p) :
    Function.Commute f (conjugation p) :=
  map_conjugation_of_sheet_exchange f hf

/-- The even projection preserves the same sheet-exchange equivariance law. -/
theorem map_even_of_sheet_exchange (f : A →+* A) {p : A}
    (hf : f p = 1 - p) (x : A) :
    f (even p x) = even p (f x) := by
  rw [map_even, hf, even_complement]

/-- The odd projection preserves the same sheet-exchange equivariance law. -/
theorem map_odd_of_sheet_exchange (f : A →+* A) {p : A}
    (hf : f p = 1 - p) (x : A) :
    f (odd p x) = odd p (f x) := by
  rw [map_odd, hf, odd_complement]

/-- A sheet-exchanging homomorphism exchanges the directed off-diagonal corners. -/
theorem map_component10_of_sheet_exchange (f : A →+* A) {p : A}
    (hf : f p = 1 - p) (x : A) :
    f (component10 p x) = component01 p (f x) := by
  rw [PeirceStarNaturality.map_component10, hf]
  simp only [component10, component01, complementIdempotent, sub_sub_cancel]

/-- The reverse corner is exchanged in the opposite direction. -/
theorem map_component01_of_sheet_exchange (f : A →+* A) {p : A}
    (hf : f p = 1 - p) (x : A) :
    f (component01 p x) = component10 p (f x) := by
  rw [PeirceStarNaturality.map_component01, hf]
  simp only [component10, component01, complementIdempotent, sub_sub_cancel]

end InfoGeometry.Core.PeirceSheetExchange
