/-
InfoGeometry/Optics/FiniteJonesBrewsterCollapse.lean

Constructive finite Brewster rank-collapse readouts.

This file replaces the prose claim

  "Brewster reflection is a rank collapse / divisor event"

with explicit finite matrix facts:

  trace (brewsterMatrix r_s) = r_s
  det2 (brewsterMatrix r_s) = 0
  Matrix.det (brewsterMatrix r_s) = 0
  the p-channel is killed
  the s-channel is scaled by r_s.
-/

import Mathlib.Tactic
import InfoGeometry.Optics.FiniteJonesModel
import InfoGeometry.Optics.FiniteJonesErlanger

noncomputable section

namespace InfoGeometry.Optics.FiniteJonesBrewsterCollapse

open Matrix
open InfoGeometry.Optics.FiniteJonesModel
open InfoGeometry.Optics.FiniteJonesErlanger

/-! ## 1. Explicit determinant readout -/

/--
The explicit `det2` readout agrees with Mathlib's determinant.
-/
theorem det2_eq_matrix_det
    (A : JonesMat) :
    det2 A = Matrix.det A := by
  dsimp [det2]
  rw [Matrix.det_fin_two]

/-! ## 2. Brewster trace and determinant collapse -/

/--
The Brewster matrix has trace `r_s`.
-/
theorem brewsterMatrix_trace
    (r_s : ℂ) :
    Matrix.trace (brewsterMatrix r_s) = r_s := by
  simp [brewsterMatrix, diagJones, Matrix.trace]

/--
The explicit `2 × 2` determinant readout of the Brewster matrix vanishes.
-/
theorem brewsterMatrix_det2_eq_zero
    (r_s : ℂ) :
    det2 (brewsterMatrix r_s) = 0 :=
  det2_brewsterMatrix r_s

/--
The Mathlib determinant of the Brewster matrix vanishes.
-/
theorem brewsterMatrix_det_eq_zero
    (r_s : ℂ) :
    Matrix.det (brewsterMatrix r_s) = 0 := by
  rw [← det2_eq_matrix_det]
  exact brewsterMatrix_det2_eq_zero r_s

/--
Brewster determinant collapse is independent of the surviving `s` amplitude.
-/
theorem brewsterMatrix_det_eq_zero_for_all_amplitudes :
    ∀ r_s : ℂ, Matrix.det (brewsterMatrix r_s) = 0 := by
  intro r_s
  exact brewsterMatrix_det_eq_zero r_s

/-! ## 3. Channel action readouts -/

/--
The Brewster matrix kills the p-channel projector.
-/
theorem brewsterMatrix_kills_p_basis
    (r_s : ℂ) :
    brewsterMatrix r_s * pProjector = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [brewsterMatrix, pProjector, diagJones, Matrix.mul_apply]

/--
The Brewster matrix preserves the s-channel as scalar multiplication by `r_s`.
-/
theorem brewsterMatrix_on_s_projector
    (r_s : ℂ) :
    brewsterMatrix r_s * sProjector = r_s • sProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [brewsterMatrix, sProjector, diagJones, Matrix.mul_apply]

/--
The Brewster matrix is the surviving s-channel core amplitude.
-/
theorem brewsterMatrix_eq_s_core
    (r_s : ℂ) :
    brewsterMatrix r_s = r_s • sProjector :=
  brewster_eq_scaled_sProjector r_s

/-! ## 4. Collapse package -/

/--
A constructive Brewster collapse event.

No `Prop` certificate is needed for trace/determinant collapse; those are
proved theorems from the matrix definition.
-/
abbrev ConstructiveBrewsterCollapse := ℂ

namespace ConstructiveBrewsterCollapse

variable (B : ConstructiveBrewsterCollapse)

/--
Trace readout of the collapse event.
-/
theorem trace_readout :
    Matrix.trace (brewsterMatrix B) = B :=
  brewsterMatrix_trace B

/--
Determinant readout of the collapse event.
-/
theorem determinant_collapse :
    Matrix.det (brewsterMatrix B) = 0 :=
  brewsterMatrix_det_eq_zero B

/--
The killed p-channel theorem for the collapse event.
-/
theorem p_channel_killed :
    brewsterMatrix B * pProjector = 0 :=
  brewsterMatrix_kills_p_basis B

/--
The surviving s-channel core theorem for the collapse event.
-/
theorem s_channel_survives :
    brewsterMatrix B * sProjector = B • sProjector :=
  brewsterMatrix_on_s_projector B

end ConstructiveBrewsterCollapse

end InfoGeometry.Optics.FiniteJonesBrewsterCollapse
