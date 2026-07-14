import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix Complex

namespace KreinBornRule

set_option autoImplicit false

/-!
# Finite-dimensional Krein-Born trace surface

This file is a finite-dimensional matrix model of a Krein-twisted Born trace.
It does not claim a full QFT or AQFT Born rule. It only packages a concrete
matrix-level trace functional with explicit normalization and positivity
readbacks.
-/

section FiniteDimensional

variable {n : ℕ}

/--
A split Krein symmetry on a `2n`-dimensional complex matrix carrier.

This stores only the finite-dimensional matrix conditions used by the local
Krein-Born trace surface: involutivity, Hermitian symmetry, and trace zero.
-/
structure SplitKreinSymmetry
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Prop where
  involutive : J * J = 1
  hermitian : IsHermitian J
  trace_zero : Matrix.trace J = 0

/--
A finite-dimensional state compatible with a fixed Krein symmetry `J`.

The positivity stored here is exactly the positivity needed for the identity
observable in the Krein-Born readback theorem below.
-/
structure KreinState
    (ρ J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Prop where
  hermitian : IsHermitian ρ
  trace_one : Matrix.trace ρ = 1
  j_positive : 0 ≤ (Matrix.trace (ρ * J)).re

/--
The finite-dimensional Krein-Born probability readout.

This is the real part of the `J`-twisted trace of the state `ρ` against an
observable/event matrix `E`.
-/
noncomputable def modifiedBornProbability
    (ρ E J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : ℝ :=
  (Matrix.trace (ρ * E * J)).re

/--
Normalization readback at the identity observable.

For `E = 1`, the Krein-Born readout reduces definitionally to the real part of
`trace (ρ * J)`.
-/
theorem modifiedBornProbability_one
    (ρ J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    modifiedBornProbability ρ 1 J = (Matrix.trace (ρ * J)).re := by
  simp [modifiedBornProbability]

/--
Identity-event nonnegativity is exactly the stored `J`-positivity of the state.
-/
theorem modifiedBornProbability_one_nonneg
    {ρ J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ}
    (hρ : KreinState ρ J) :
    0 ≤ modifiedBornProbability ρ 1 J := by
  simpa [modifiedBornProbability_one] using hρ.j_positive

/--
The split Krein symmetry readback exposes the trace-zero condition as a theorem.
-/
theorem SplitKreinSymmetry.trace_eq_zero
    {J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ}
    (hJ : SplitKreinSymmetry J) :
    Matrix.trace J = 0 := by
  rcases hJ with ⟨_, _, htrace_zero⟩
  exact htrace_zero

/--
The Krein state readback exposes the unit-trace condition as a theorem.
-/
theorem KreinState.trace_eq_one
    {ρ J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ}
    (hρ : KreinState ρ J) :
    Matrix.trace ρ = 1 := by
  rcases hρ with ⟨_, htrace_one, _⟩
  exact htrace_one

end FiniteDimensional

end KreinBornRule
