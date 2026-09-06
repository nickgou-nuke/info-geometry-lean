import InfoGeometry.Canonical.GradedRationalSectorPreservation

namespace InfoGeometry.Canonical

variable {V : ℕ → Type*}
  [∀ p, AddCommGroup (V p)]
  [∀ p, Module ℚ (V p)]

/-- A graded subcomplex for a differential whose square is zero. -/
structure GradedRationalSubcomplex
    (D : GradedRationalDifferential V) where
  carrier : GradedSector V
  preserved : DifferentialPreservesSector D carrier

/-- The differential restricted to a preserved graded sector. -/
def restrictedDifferential
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (p : ℕ) : S p →ₗ[ℚ] S (p + 1) :=
  { toFun := fun x => ⟨D.d p x.1, hS p x.1 x.2⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      simpa using (D.d p).map_add x.1 y.1
    map_smul' := by
      intro a x
      apply Subtype.ext
      simpa using (D.d p).map_smul a x.1 }

theorem restrictedDifferential_mem
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (p : ℕ) (x : S p) :
    (restrictedDifferential D S hS p x).1 ∈ S (p + 1) :=
  (restrictedDifferential D S hS p x).property

theorem restrictedDifferential_sq_zero
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (p : ℕ) (x : S p) :
    restrictedDifferential D S hS (p + 1)
        (restrictedDifferential D S hS p x) = 0 := by
  apply Subtype.ext
  exact D.d_sq_zero p x.1

theorem subcomplex_restricted_differential_sq_zero
    (D : GradedRationalDifferential V)
    (C : GradedRationalSubcomplex D)
    (p : ℕ) (x : C.carrier p) :
    restrictedDifferential D C.carrier C.preserved (p + 1)
        (restrictedDifferential D C.carrier C.preserved p x) = 0 :=
  restrictedDifferential_sq_zero D C.carrier C.preserved p x

end InfoGeometry.Canonical
