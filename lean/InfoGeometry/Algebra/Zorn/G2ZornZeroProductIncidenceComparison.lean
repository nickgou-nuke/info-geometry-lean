import InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2CASNativePointEnumeration
import InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate

/-!
# Comparison of the intrinsic zero-product relation with exported incidence

This owner records the concrete finite comparison.  It does not promote the
relation to a flag carrier until the line/clique uniqueness facts are proved.
-/

namespace InfoGeometry.Algebra.Zorn.G2ZornZeroProductIncidenceComparison

open InfoGeometry.Algebra.Zorn.G2CASNativePointEnumeration
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate

def exportedLineSharing (i j : Fin 63) : Prop :=
  ∃ l : Fin 63, l ∈ incidence i ∧ l ∈ incidence j

instance (i j : Fin 63) : Decidable (exportedLineSharing i j) := by
  unfold exportedLineSharing
  infer_instance

def exportedPointNeighbor (i j : Fin 63) : Prop :=
  i ≠ j ∧ exportedLineSharing i j

instance (i j : Fin 63) : Decidable (exportedPointNeighbor i j) := by
  unfold exportedPointNeighbor
  infer_instance

@[simp] theorem exportedPointNeighbor_iff (i j : Fin 63) :
    exportedPointNeighbor i j ↔
      i ≠ j ∧ exportedLineSharing i j := Iff.rfl

theorem exportedLineSharing_symmetric (i j : Fin 63) :
    exportedLineSharing i j ↔ exportedLineSharing j i := by
  constructor
  · rintro ⟨l, hil, hjl⟩
    exact ⟨l, hjl, hil⟩
  · rintro ⟨l, hjl, hil⟩
    exact ⟨l, hil, hjl⟩

theorem exportedPointNeighbor_symmetric (i j : Fin 63) :
    exportedPointNeighbor i j ↔ exportedPointNeighbor j i := by
  constructor
  · intro h
    exact ⟨h.1.symm, (exportedLineSharing_symmetric i j).mp h.2⟩
  · intro h
    exact ⟨h.1.symm, (exportedLineSharing_symmetric i j).mpr h.2⟩

end InfoGeometry.Algebra.Zorn.G2ZornZeroProductIncidenceComparison
