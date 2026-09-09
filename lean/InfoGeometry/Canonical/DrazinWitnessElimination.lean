import InfoGeometry.Canonical.DrazinInfiniteCore

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.DrazinWitnessElimination

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinInfiniteCore

section FiniteDimensional

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

local notation "EndH" => E →L[ℝ] E

/-- Canonical finite-dimensional Drazin index. -/
noncomputable abbrev drazinIndex (A : EndH) : ℕ :=
  Classical.choose
    (InfoGeometry.Canonical.DrazinExistenceBridge.exists_canonicalDrazinInverse_global_endCLM A)

/-- Canonical finite-dimensional Drazin inverse. -/
noncomputable abbrev drazinInverse (A : EndH) : EndH :=
  Classical.choose
    (Classical.choose_spec
      (InfoGeometry.Canonical.DrazinExistenceBridge.exists_canonicalDrazinInverse_global_endCLM A))

/-- Canonical finite-dimensional Drazin witness. -/
theorem isDrazinInverse_drazinInverse
    (A : EndH) :
    Drazin.IsDrazinInverse A
      (drazinInverse (E := E) A)
      (drazinIndex (E := E) A) := by
  exact Classical.choose_spec
    (Classical.choose_spec
      (InfoGeometry.Canonical.DrazinExistenceBridge.exists_canonicalDrazinInverse_global_endCLM A))

/-- Canonical finite-dimensional Drazin projector. -/
noncomputable def drazinProjector (A : EndH) : EndH :=
  Drazin.IsDrazinInverse.projection A (drazinInverse (E := E) A)

/-- Canonical finite-dimensional complementary Drazin projector. -/
noncomputable def drazinComplementaryProjector (A : EndH) : EndH :=
  Drazin.IsDrazinInverse.complementaryProjection A (drazinInverse (E := E) A)

@[simp] theorem drazinProjector_idempotent
    (A : EndH) :
    drazinProjector (E := E) A * drazinProjector (E := E) A
      = drazinProjector (E := E) A := by
  exact Drazin.IsDrazinInverse.projection_is_idempotent
    (isDrazinInverse_drazinInverse (E := E) A)

@[simp] theorem drazinComplementaryProjector_idempotent
    (A : EndH) :
    drazinComplementaryProjector (E := E) A * drazinComplementaryProjector (E := E) A
      = drazinComplementaryProjector (E := E) A := by
  exact Drazin.IsDrazinInverse.complementaryProjection_is_idempotent
    (isDrazinInverse_drazinInverse (E := E) A)

@[simp] theorem drazinProjector_mul_drazinComplementaryProjector
    (A : EndH) :
    drazinProjector (E := E) A * drazinComplementaryProjector (E := E) A = 0 := by
  exact Drazin.IsDrazinInverse.projection_mul_complementaryProjection
    (isDrazinInverse_drazinInverse (E := E) A)

@[simp] theorem drazinComplementaryProjector_mul_drazinProjector
    (A : EndH) :
    drazinComplementaryProjector (E := E) A * drazinProjector (E := E) A = 0 := by
  exact Drazin.IsDrazinInverse.complementaryProjection_mul_projection
    (isDrazinInverse_drazinInverse (E := E) A)

end FiniteDimensional

end InfoGeometry.Canonical.DrazinWitnessElimination
