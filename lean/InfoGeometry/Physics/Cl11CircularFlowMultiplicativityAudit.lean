/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.Cl11CircularFlowMultiplicativity

open InfoGeometry.Physics.BostConnesThermalTime
open InfoGeometry.Clifford.Cl11CoordinateAlgebra

#print axioms modularFlowCl11_multiplicative_iff
#print axioms modularFlowCl11_multiplicative_iff_half_period
#print axioms modularFlowCl11_half_period_eq_conjugation
#print axioms modularFlowCl11_eq_id_or_conjugation
#print axioms modularFlowCl11RingEquiv
#print axioms modularFlowCl11RingEquiv_apply
#print axioms modularFlowCl11_not_mul_at_pi_div_four

example (q r : Cl11) : modularFlowCl11 (Real.pi / 2) (q * r) =
    modularFlowCl11 (Real.pi / 2) q * modularFlowCl11 (Real.pi / 2) r := by
  apply (modularFlowCl11_multiplicative_iff_half_period _).mpr
    (show ∃ k : ℤ, Real.pi / 2 = (k : ℝ) * Real.pi / 2 from ⟨1, by simp⟩)

example : ¬ ∀ q r : Cl11, modularFlowCl11 (Real.pi / 4) (q * r) =
    modularFlowCl11 (Real.pi / 4) q * modularFlowCl11 (Real.pi / 4) r := by
  rw [modularFlowCl11_multiplicative_iff]
  norm_num [show 2 * (Real.pi / 4) = Real.pi / 2 by ring]

example (t : ℝ) (ht : Real.sin (2 * t) = 0) (q : Cl11) :
    (modularFlowCl11RingEquiv t ht).symm (modularFlowCl11RingEquiv t ht q) = q :=
  (modularFlowCl11RingEquiv t ht).symm_apply_apply q

example : modularFlowCl11 (Real.pi / 2) e2Basis = -e2Basis :=
  modularFlowCl11_e2Basis_pi_div_two
