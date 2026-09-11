import InfoGeometry.Canonical.GradedRationalSubcomplex
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

variable {V : ℕ → Type*}
  [∀ p, AddCommGroup (V p)]
  [∀ p, Module ℚ (V p)]

/-- Degreewise intersection of two graded sectors. -/
def gradedSectorInf
    (S T : GradedSector V) : GradedSector V :=
  fun p => S p ⊓ T p

theorem differential_preserves_sector_inf
    (D : GradedRationalDifferential V)
    (S T : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector D T) :
    DifferentialPreservesSector D (gradedSectorInf S T) := by
  intro p x hx
  change (D.d p x ∈ S (p + 1)) ∧ (D.d p x ∈ T (p + 1))
  exact And.intro (hS p x hx.1) (hT p x hx.2)

theorem restrictedDifferential_sq_zero_on_sector_inf
    (D : GradedRationalDifferential V)
    (S T : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector D T)
    (p : ℕ) (x : gradedSectorInf S T p) :
    restrictedDifferential D (gradedSectorInf S T)
        (differential_preserves_sector_inf D S T hS hT) (p + 1)
      (restrictedDifferential D (gradedSectorInf S T)
        (differential_preserves_sector_inf D S T hS hT) p x) = 0 := by
  exact restrictedDifferential_sq_zero D (gradedSectorInf S T)
    (differential_preserves_sector_inf D S T hS hT) p x

/-- Degreewise intersection of three graded sectors. -/
def gradedSectorInf3
    (S T U : GradedSector V) : GradedSector V :=
  fun p => S p ⊓ T p ⊓ U p

theorem differential_preserves_sector_inf3
    (D : GradedRationalDifferential V)
    (S T U : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector D T)
    (hU : DifferentialPreservesSector D U) :
    DifferentialPreservesSector D (gradedSectorInf3 S T U) := by
  intro p x hx
  simpa [gradedSectorInf3] using
    (show ((D.d p x ∈ S (p + 1)) ∧
      (D.d p x ∈ T (p + 1))) ∧ (D.d p x ∈ U (p + 1)) from
      ⟨⟨hS p x hx.1.1, hT p x hx.1.2⟩, hU p x hx.2⟩)

theorem restrictedDifferential_sq_zero_on_sector_inf3
    (D : GradedRationalDifferential V)
    (S T U : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector D T)
    (hU : DifferentialPreservesSector D U)
    (p : ℕ) (x : gradedSectorInf3 S T U p) :
    restrictedDifferential D (gradedSectorInf3 S T U)
        (differential_preserves_sector_inf3 D S T U hS hT hU) (p + 1)
      (restrictedDifferential D (gradedSectorInf3 S T U)
        (differential_preserves_sector_inf3 D S T U hS hT hU) p x) = 0 := by
  exact restrictedDifferential_sq_zero D (gradedSectorInf3 S T U)
    (differential_preserves_sector_inf3 D S T U hS hT hU) p x

theorem codifferential_preserves_sector_inf
    (C : GradedRationalCodifferential V)
    (S T : GradedSector V)
    (hS : CodifferentialPreservesSector C S)
    (hT : CodifferentialPreservesSector C T) :
    CodifferentialPreservesSector C (gradedSectorInf S T) := by
  intro p x hx
  change (C.cod p x ∈ S p) ∧ (C.cod p x ∈ T p)
  exact And.intro (hS p x hx.1) (hT p x hx.2)

theorem codifferential_preserves_sector_inf3
    (C : GradedRationalCodifferential V)
    (S T U : GradedSector V)
    (hS : CodifferentialPreservesSector C S)
    (hT : CodifferentialPreservesSector C T)
    (hU : CodifferentialPreservesSector C U) :
    CodifferentialPreservesSector C (gradedSectorInf3 S T U) := by
  intro p x hx
  simpa [gradedSectorInf3] using
    (show ((C.cod p x ∈ S p) ∧
      (C.cod p x ∈ T p)) ∧ (C.cod p x ∈ U p) from
      ⟨⟨hS p x hx.1.1, hT p x hx.1.2⟩, hU p x hx.2⟩)

end InfoGeometry.Canonical
