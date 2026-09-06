import InfoGeometry.Canonical.GradedRationalSectorIntersections

namespace InfoGeometry.Canonical

variable {V : ℕ → Type*}
  [∀ p, AddCommGroup (V p)]
  [∀ p, Module ℚ (V p)]

/-- The degree-`p` cycles of a graded differential. -/
def gradedCycleSubmodule
    (D : GradedRationalDifferential V) (p : ℕ) : Submodule ℚ (V p) where
  carrier := {x | D.d p x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change D.d p (x + y) = 0
    rw [map_add, hx, hy, add_zero]
  smul_mem' := by
    intro a x hx
    change D.d p (a • x) = 0
    rw [map_smul, hx, smul_zero]

/-- The degree-`p+1` boundaries are the range of `d : V p -> V (p+1)`. -/
def gradedBoundarySubmodule
    (D : GradedRationalDifferential V) (p : ℕ) : Submodule ℚ (V (p + 1)) :=
  LinearMap.range (D.d p)

theorem gradedBoundary_le_cycle
    (D : GradedRationalDifferential V) (p : ℕ) :
    gradedBoundarySubmodule D p ≤ gradedCycleSubmodule D (p + 1) := by
  rintro x ⟨y, rfl⟩
  exact D.d_sq_zero p y

theorem gradedBoundary_is_cycle
    (D : GradedRationalDifferential V) (p : ℕ)
    {x : V (p + 1)}
    (hx : x ∈ gradedBoundarySubmodule D p) :
    x ∈ gradedCycleSubmodule D (p + 1) :=
  gradedBoundary_le_cycle D p hx

/-- Boundaries viewed as a submodule of the cycle submodule. -/
def gradedBoundaryInCycles
    (D : GradedRationalDifferential V) (p : ℕ) :
    Submodule ℚ (gradedCycleSubmodule D (p + 1)) :=
  (gradedBoundarySubmodule D p).comap
    (Submodule.subtype (gradedCycleSubmodule D (p + 1)))

/-- The quotient carrier for degree-`p+1` cohomological information.

This is only the native quotient type; no choice of representatives or
finite-dimensional dimension statement is asserted here.
-/
def gradedCohomologyShadow
    (D : GradedRationalDifferential V) (p : ℕ) :=
  (gradedCycleSubmodule D (p + 1)) ⧸ gradedBoundaryInCycles D p

instance gradedCohomologyShadow.instAddCommGroup
    (D : GradedRationalDifferential V) (p : ℕ) :
    AddCommGroup (gradedCohomologyShadow D p) := by
  dsimp [gradedCohomologyShadow]
  infer_instance

instance gradedCohomologyShadow.instModule
    (D : GradedRationalDifferential V) (p : ℕ) :
    Module ℚ (gradedCohomologyShadow D p) := by
  dsimp [gradedCohomologyShadow]
  infer_instance

end InfoGeometry.Canonical
