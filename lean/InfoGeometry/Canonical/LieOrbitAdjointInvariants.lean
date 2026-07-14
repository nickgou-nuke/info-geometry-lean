import Mathlib

/-!
# InfoGeometry.Canonical.LieOrbitAdjointInvariants

Owner-side Lie-group orbit corridor: adjoint action of `GL(n,R)` on matrices and
orbit invariants.

This file proves concrete non-scalar facts:
1. group action law for matrix conjugation,
2. trace and determinant are constant on adjoint orbits.

No wrappers. No `sorry`.
-/

namespace LieOrbitAdjointInvariants

open Matrix

section

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- Adjoint action of `GL(n,R)` on `Matrix n n R` by conjugation. -/
def adjointAction (g : GL n R) (A : Matrix n n R) : Matrix n n R :=
  (g : Matrix n n R) * A * ((g⁻¹ : GL n R) : Matrix n n R)

/-- Orbit through `A` under the adjoint action. -/
def adjointOrbit (A : Matrix n n R) : Set (Matrix n n R) :=
  Set.range fun g : GL n R => adjointAction g A

@[simp] theorem adjointAction_one (A : Matrix n n R) :
    adjointAction (1 : GL n R) A = A := by
  simp [adjointAction]

theorem adjointAction_mul (g h : GL n R) (A : Matrix n n R) :
    adjointAction (g * h) A = adjointAction g (adjointAction h A) := by
  ext i j
  simp [adjointAction, Matrix.mul_assoc]

theorem trace_adjointAction (g : GL n R) (A : Matrix n n R) :
    Matrix.trace (adjointAction g A) = Matrix.trace A := by
  simpa [adjointAction] using Matrix.trace_units_conj (M := g) (N := A)

theorem det_adjointAction (g : GL n R) (A : Matrix n n R) :
    Matrix.det (adjointAction g A) = Matrix.det A := by
  simpa [adjointAction] using Matrix.det_units_conj (M := g) (N := A)

theorem trace_constant_on_adjointOrbit (A B : Matrix n n R)
    (hB : B ∈ adjointOrbit A) :
    Matrix.trace B = Matrix.trace A := by
  rcases hB with ⟨g, rfl⟩
  exact trace_adjointAction g A

theorem det_constant_on_adjointOrbit (A B : Matrix n n R)
    (hB : B ∈ adjointOrbit A) :
    Matrix.det B = Matrix.det A := by
  rcases hB with ⟨g, rfl⟩
  exact det_adjointAction g A

end

end LieOrbitAdjointInvariants

