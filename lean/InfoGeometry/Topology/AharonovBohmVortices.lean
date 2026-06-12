import Mathlib

/-!
# Finite Aharonov--Bohm vortex phase certificates

This module records a theorem-safe finite phase socket: a supplied phase whose
third power is `1` gives a stable triple-winding identity, and the corresponding
`3 × 3` diagonal vortex operator cubes to the identity.

It does **not** prove physical color confinement, Hawking radiation dynamics,
LLM hallucination confinement, or a derivation of `SU(3)` from parafermions.
Those interpretations require additional models outside this finite algebraic
certificate.
-/

namespace InfoGeometry.Topology.Parafermion

open Matrix

/--
A finite Aharonov--Bohm vortex phase certificate.

The carrier stores an explicitly supplied nontrivial third root of unity.
-/
structure AharonovBohmVortex where
  phase : ℂ
  h_fractional_winding : phase ^ 3 = 1
  h_non_trivial : phase ≠ 1

/-- Triple winding of a certified third-root phase returns to the identity phase. -/
theorem baryon_vortex_confinement (v : AharonovBohmVortex) :
    v.phase * v.phase * v.phase = 1 := by
  have h : v.phase * v.phase * v.phase = v.phase ^ 3 := by ring
  rw [h]
  exact v.h_fractional_winding

/-- The finite `3 × 3` diagonal vortex operator associated to a certified phase. -/
def vortexOperator (v : AharonovBohmVortex) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![1, 0, 0],
    ![0, 1, 0],
    ![0, 0, v.phase]]

/-- The diagonal vortex operator has order dividing three. -/
theorem vortexOperator_cube_eq_one (v : AharonovBohmVortex) :
    vortexOperator v * vortexOperator v * vortexOperator v = 1 := by
  have hmul : v.phase * v.phase * v.phase = 1 := baryon_vortex_confinement v
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vortexOperator, Matrix.mul_apply, Fin.sum_univ_three, hmul]

end InfoGeometry.Topology.Parafermion
