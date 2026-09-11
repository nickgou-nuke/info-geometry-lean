import InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Incidence of real two-planes on the projective Klein locus

This owner equips the set-level real Grassmannian carrier with its native line
incidence relation.  Two real two-planes are incident precisely when their
intersection contains a nonzero vector.  For nondegenerate ordered frames,
this is equivalent to vanishing of their combined top exterior product.

The established Plücker equivalence transports that intrinsic relation to the
projective Klein locus.  No twistor-space, positive-Grassmannian, or
amplituhedron identification is asserted here.
-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorKleinTwoPlaneIncidence

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorKleinProjective
open InfoGeometry.Projective.ExteriorKleinFrameSurjection
open InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient
open InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv

/-- Intrinsic incidence of real two-planes: their intersection is nontrivial. -/
def PlanesIncident (P Q : RealTwoPlane) : Prop :=
  ¬ Disjoint P.1 Q.1

/-- Intrinsic incidence means exactly that the two planes contain a common
nonzero vector. -/
theorem planesIncident_iff_exists_nonzero_mem
    (P Q : RealTwoPlane) :
    PlanesIncident P Q ↔
      ∃ x : Vec4, x ≠ 0 ∧ x ∈ P.1 ∧ x ∈ Q.1 := by
  constructor
  · intro h
    by_contra hn
    apply h
    rw [Submodule.disjoint_def]
    intro x hxP hxQ
    by_contra hx
    exact hn ⟨x, hx, hxP, hxQ⟩
  · rintro ⟨x, hx, hxP, hxQ⟩ hdisjoint
    exact hx ((Submodule.disjoint_def.1 hdisjoint) x hxP hxQ)

/-- Canonical reindexing of two ordered pairs as one ordered four-frame. -/
def finFourEquivSumTwo : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
  (finCongr (show 4 = 2 + 2 by decide)).trans finSumFinEquiv.symm

/-- The ordered four-frame obtained by concatenating two ordered two-frames. -/
def combinedFrame (uv st : NondegenerateExteriorFrame) : Fin 4 → Vec4 :=
  Sum.elim uv.1 st.1 ∘ finFourEquivSumTwo

/-- The combined four-frame is linearly independent exactly when the two
spanned planes are disjoint. -/
theorem combinedFrame_linearIndependent_iff_disjoint
    (uv st : NondegenerateExteriorFrame) :
    LinearIndependent ℝ (combinedFrame uv st) ↔
      Disjoint (frameSpan uv).1 (frameSpan st).1 := by
  rw [combinedFrame, linearIndependent_equiv]
  rw [linearIndependent_sum]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    nondegenerateExteriorFrame_linearIndependent, true_and]
  rfl

/-- The top exterior product of two frames vanishes exactly when their
two-planes are incident. -/
theorem combinedFrame_wedge_eq_zero_iff_incident
    (uv st : NondegenerateExteriorFrame) :
    exteriorPower.ιMulti ℝ 4 (combinedFrame uv st) = 0 ↔
      PlanesIncident (frameSpan uv) (frameSpan st) := by
  rw [PlanesIncident, ← combinedFrame_linearIndependent_iff_disjoint]
  constructor
  · intro hw hli
    exact (exterior_ιMulti_ne_zero_of_linearIndependent _ hli) hw
  · intro hli
    exact (exteriorPower.ιMulti ℝ 4).map_linearDependent _ hli

/-- The set-level Plücker equivalence sends a framed plane to its native
projective Klein ray. -/
theorem realTwoPlaneEquivKleinLocus_frameSpan
    (uv : NondegenerateExteriorFrame) :
    realTwoPlaneEquivKleinLocus (frameSpan uv) = frameToKleinLocus uv := by
  change framePlaneQuotientEquivKleinLocus
      (framePlaneQuotientEquivTwoPlane.symm (frameSpan uv)) = _
  have hq : framePlaneQuotientEquivTwoPlane.symm (frameSpan uv) =
      Quotient.mk framePlaneSetoid uv := by
    apply framePlaneQuotientEquivTwoPlane.injective
    simp
  rw [hq]
  rfl

/-- Klein-locus incidence transported from the intrinsic intersection
relation on real two-planes. -/
def KleinIncident (p q : KleinLocus) : Prop :=
  PlanesIncident (realTwoPlaneEquivKleinLocus.symm p)
    (realTwoPlaneEquivKleinLocus.symm q)

/-- On concrete Plücker representatives, Klein incidence is exactly
vanishing of the combined top exterior product. -/
theorem kleinIncident_frameToKleinLocus_iff_wedge_eq_zero
    (uv st : NondegenerateExteriorFrame) :
    KleinIncident (frameToKleinLocus uv) (frameToKleinLocus st) ↔
      exteriorPower.ιMulti ℝ 4 (combinedFrame uv st) = 0 := by
  rw [KleinIncident,
    ← realTwoPlaneEquivKleinLocus_frameSpan uv,
    ← realTwoPlaneEquivKleinLocus_frameSpan st]
  simp only [Equiv.symm_apply_apply]
  exact (combinedFrame_wedge_eq_zero_iff_incident uv st).symm

end InfoGeometry.Projective.ExteriorKleinTwoPlaneIncidence
