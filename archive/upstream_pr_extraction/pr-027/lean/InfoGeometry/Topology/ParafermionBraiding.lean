import Mathlib.Tactic

/-!
# Finite parafermion-style Artin braid matrices

This module records the finite `3 x 3` matrix identity behind the
parafermion-braiding interpretation.

It does not prove a physical `SU(2) -> SU(3)` breaking theorem, Lorentz
covariance, a parafermion quantum field theory, or color confinement.  It proves
only the Artin braid relation for two explicit Burau-style matrices.

#### BUCKET 1: CLOSED FINITE THEOREMS

`su3_parafermion_braiding`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

Physical parafermions, Lorentz symmetry, `SU(2)`/`SU(3)` representation theory,
and braid statistics for a Hilbert-space model remain outside this finite
matrix file.
-/

noncomputable section

namespace InfoGeometry.Topology.Parafermion

open Matrix

/-- The `3 x 3` projective carrier used by the finite braid matrices. -/
abbrev ProjMatrix := Matrix (Fin 3) (Fin 3) ℂ

/-- The unreduced Burau-style first Artin braid generator `σ₁`. -/
def sigma_1 (t : ℂ) : ProjMatrix :=
  ![![1 - t, t, 0],
    ![1,     0, 0],
    ![0,     0, 1]]

/-- The unreduced Burau-style second Artin braid generator `σ₂`. -/
def sigma_2 (t : ℂ) : ProjMatrix :=
  ![![1, 0,     0],
    ![0, 1 - t, t],
    ![0, 1,     0]]

/--
Finite Artin braid relation.

For the explicit matrices above, `σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂`.
-/
theorem su3_parafermion_braiding (t : ℂ) :
    sigma_1 t * sigma_2 t * sigma_1 t = sigma_2 t * sigma_1 t * sigma_2 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma_1, sigma_2, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring_nf

end InfoGeometry.Topology.Parafermion

end noncomputable section
