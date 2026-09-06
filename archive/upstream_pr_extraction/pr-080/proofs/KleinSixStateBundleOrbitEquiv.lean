import proofs.KleinSixStateVectorBundleCore
import proofs.KleinSixStateAssociatedQuotient

/-!
# Algebraic identification of the vector-bundle core and orbit quotient

This file constructs the underlying equivalence.  The subsequent owner upgrades
it to a homeomorphism by checking it in the local trivializations of the
`VectorBundleCore`.
-/

noncomputable section
namespace KleinSixStateBundleOrbitEquiv

open KleinBrillouinBase KleinBottleOrbitQuotient KleinGlideCovering
open KleinGlideCoveringAtlas KleinSixStateBundle TwoSheetThreeColorWeyl
open KleinSixStateAssociatedQuotient KleinSixStateVectorBundleCore

abbrev Base := KleinBrillouinQuotient
abbrev State := Fin 2 × Fin 3 → ℂ

/-- Coordinate of a covering point in the chart selected at its image. -/
def coverCoord (k : BrillouinTorus) : Deck2 :=
  ((coverTriv (quotientMap k)) k).2

/-- Zero-coordinate lift in the chart selected at `b`. -/
def selectedSection (b : Base) : BrillouinTorus :=
  (coverTriv b).toOpenPartialHomeomorph.symm (b, 0)

private theorem cover_mem_selected_source (k : BrillouinTorus) :
    k ∈ (coverTriv (quotientMap k)).source := by
  rw [(coverTriv (quotientMap k)).mem_source]
  exact mem_coverTriv_baseSet (quotientMap k)

theorem coverCoord_selectedSection (b : Base) :
    coverCoord (selectedSection b) = 0 := by
  have hb := mem_coverTriv_baseSet b
  have hq : quotientMap (selectedSection b) = b :=
    (coverTriv b).proj_symm_apply' hb
  unfold coverCoord
  rw [hq]
  exact congrArg Prod.snd ((coverTriv b).apply_symm_apply' hb)

private theorem coverCoord_ne_glide (k : BrillouinTorus) :
    coverCoord (torusGlide k) ≠ coverCoord k := by
  intro hcoord
  have hq : quotientMap (torusGlide k) = quotientMap k := quotientMap_glide k
  have hgsource : torusGlide k ∈ (coverTriv (quotientMap k)).source := by
    rw [(coverTriv (quotientMap k)).mem_source]
    simpa using mem_coverTriv_baseSet (quotientMap k)
  have himage :
      (coverTriv (quotientMap k)) (torusGlide k) =
        (coverTriv (quotientMap k)) k := by
    apply Prod.ext
    · rw [(coverTriv (quotientMap k)).coe_fst' hgsource,
        (coverTriv (quotientMap k)).coe_fst' (cover_mem_selected_source k)]
      exact hq
    · simpa [coverCoord, hq] using hcoord
  have heq := (coverTriv (quotientMap k)).toPartialEquiv.injOn
    hgsource (cover_mem_selected_source k) himage
  exact torusGlide_ne_self k heq

theorem coverCoord_glide (k : BrillouinTorus) :
    coverCoord (torusGlide k) = coverCoord k + 1 := by
  have h11 : (1 + 1 : Deck2) = 0 := by native_decide
  have hne := coverCoord_ne_glide k
  generalize h0 : coverCoord k = a
  generalize h1 : coverCoord (torusGlide k) = b
  fin_cases a <;> fin_cases b
  · exact False.elim (hne (h1.trans h0.symm))
  · simp_all
  · simp_all
  · exact False.elim (hne (h1.trans h0.symm))

theorem fibreCoordinate_glide_invariant (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (k : BrillouinTorus) (v : State) :
    deckFiberMap (coverCoord (torusGlide k)) (theta.mulVec v) =
      deckFiberMap (coverCoord k) v := by
  rw [coverCoord_glide]
  have h11 : (1 + 1 : Deck2) = 0 := by native_decide
  generalize hg : coverCoord k = g
  fin_cases g
  · change theta.mulVec (theta.mulVec v) = v
    rw [Matrix.mulVec_mulVec, theta_sq omega homega]
    exact Matrix.one_mulVec v
  · change (deckFiberMap (1 + 1)) (theta.mulVec v) = theta.mulVec v
    rw [h11, deckFiberMap_zero]
    rfl

abbrev Core (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0) :=
  kleinSixStateVectorBundleCore omega homega

abbrev CoreTotal (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0) :=
  (Core omega homega).TotalSpace

private def representativeToCore (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (p : BrillouinTorus × State) : CoreTotal omega homega :=
  ⟨quotientMap p.1, deckFiberMap (coverCoord p.1) p.2⟩

private theorem representativeToCore_respects (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (x y : BrillouinTorus × State)
    (h : (totalGlideSetoid omega homega).r x y) :
    representativeToCore omega homega x = representativeToCore omega homega y := by
  rcases h with rfl | h
  · rfl
  · rw [h]
    rcases x with ⟨k, v⟩
    apply Bundle.TotalSpace.ext
    · exact (quotientMap_glide k).symm
    · simpa [representativeToCore, totalGlide] using
        (fibreCoordinate_glide_invariant omega homega k v).symm

/-- Orbit quotient to the native vector-bundle core total space. -/
def orbitToCore (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0) :
    AssociatedSixState omega homega → CoreTotal omega homega :=
  Quotient.lift (representativeToCore omega homega)
    (representativeToCore_respects omega homega)

/-- The inverse candidate uses the selected zero-coordinate sheet. -/
def coreToOrbit (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0) :
    CoreTotal omega homega → AssociatedSixState omega homega :=
  fun p ↦ totalQuotientMap omega homega
    (selectedSection p.1, p.2)

theorem orbitToCore_coreToOrbit (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (p : CoreTotal omega homega) :
    orbitToCore omega homega (coreToOrbit omega homega p) = p := by
  rcases p with ⟨b, v⟩
  change (⟨quotientMap (selectedSection b),
      deckFiberMap (coverCoord (selectedSection b)) v⟩ : CoreTotal omega homega) = ⟨b, v⟩
  have hq : quotientMap (selectedSection b) = b :=
    (coverTriv b).proj_symm_apply' (mem_coverTriv_baseSet b)
  apply Bundle.TotalSpace.ext hq
  exact (by
    rw [coverCoord_selectedSection, deckFiberMap_zero]
    rfl : _ = _).heq

private theorem selectedSection_eq_of_coverCoord_zero (k : BrillouinTorus)
    (hcoord : coverCoord k = 0) :
    selectedSection (quotientMap k) = k := by
  apply (coverTriv (quotientMap k)).toPartialEquiv.injOn
  · unfold selectedSection
    rw [(coverTriv (quotientMap k)).mem_source,
      (coverTriv (quotientMap k)).proj_symm_apply'
        (mem_coverTriv_baseSet (quotientMap k))]
    exact mem_coverTriv_baseSet (quotientMap k)
  · exact cover_mem_selected_source k
  · unfold selectedSection
    change (coverTriv (quotientMap k))
      ((coverTriv (quotientMap k)).toOpenPartialHomeomorph.symm
        (quotientMap k, 0)) = (coverTriv (quotientMap k)) k
    rw [(coverTriv (quotientMap k)).apply_symm_apply'
      (mem_coverTriv_baseSet (quotientMap k))]
    apply Prod.ext
    · exact (coverTriv (quotientMap k)).coe_fst'
        (cover_mem_selected_source k)
    · exact hcoord.symm

private theorem glide_selectedSection_eq_of_coverCoord_one (k : BrillouinTorus)
    (hcoord : coverCoord k = 1) :
    torusGlide (selectedSection (quotientMap k)) = k := by
  let s := selectedSection (quotientMap k)
  have hs0 : coverCoord s = 0 := coverCoord_selectedSection (quotientMap k)
  have hqs : quotientMap s = quotientMap k :=
    (coverTriv (quotientMap k)).proj_symm_apply'
      (mem_coverTriv_baseSet (quotientMap k))
  have hcg : coverCoord (torusGlide s) = 1 := by
    rw [coverCoord_glide, hs0]
    native_decide
  apply (coverTriv (quotientMap k)).toPartialEquiv.injOn
  · rw [(coverTriv (quotientMap k)).mem_source]
    rw [quotientMap_glide, hqs]
    exact mem_coverTriv_baseSet (quotientMap k)
  · exact cover_mem_selected_source k
  · apply Prod.ext
    · change quotientMap (torusGlide s) = quotientMap k
      exact (quotientMap_glide s).trans hqs
    · simpa [coverCoord, hqs, quotientMap_glide s] using hcg.trans hcoord.symm

theorem coreToOrbit_orbitToCore_mk (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (k : BrillouinTorus) (v : State) :
    coreToOrbit omega homega
      (orbitToCore omega homega (totalQuotientMap omega homega (k, v))) =
      totalQuotientMap omega homega (k, v) := by
  change totalQuotientMap omega homega
      (selectedSection (quotientMap k), deckFiberMap (coverCoord k) v) =
    totalQuotientMap omega homega (k, v)
  generalize hg : coverCoord k = g
  fin_cases g
  · change totalQuotientMap omega homega
      (selectedSection (quotientMap k), v) = totalQuotientMap omega homega (k, v)
    rw [selectedSection_eq_of_coverCoord_zero k hg]
  · change totalQuotientMap omega homega
      (selectedSection (quotientMap k), theta.mulVec v) = totalQuotientMap omega homega (k, v)
    apply Quotient.sound
    right
    symm
    apply Prod.ext
    · exact glide_selectedSection_eq_of_coverCoord_one k hg
    · change theta.mulVec (theta.mulVec v) = v
      rw [Matrix.mulVec_mulVec, theta_sq omega homega]
      exact Matrix.one_mulVec v

theorem coreToOrbit_orbitToCore (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0)
    (q : AssociatedSixState omega homega) :
    coreToOrbit omega homega (orbitToCore omega homega q) = q := by
  refine Quotient.inductionOn q ?_
  rintro ⟨k, v⟩
  exact coreToOrbit_orbitToCore_mk omega homega k v

/-- Underlying equivalence between the existing orbit quotient and the native
Mathlib vector-bundle core total carrier. -/
def bundleTotalOrbitEquiv (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    CoreTotal omega homega ≃ AssociatedSixState omega homega where
  toFun := coreToOrbit omega homega
  invFun := orbitToCore omega homega
  left_inv := orbitToCore_coreToOrbit omega homega
  right_inv := coreToOrbit_orbitToCore omega homega

end KleinSixStateBundleOrbitEquiv
end noncomputable section
