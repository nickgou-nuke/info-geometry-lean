/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CuntzComplexStarGeneratorCyclicity
import InfoGeometry.NCG.CuntzColimitKMSTiltGNS

/-! The existing canonical Cuntz shift preserves the actual uniform quotient functional. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Algebra.CuntzComplexification
open InfoGeometry.NCG

local notation "φ" => quotientProductFunctional (fun _ => (1 / 2 : ℝ)) (by norm_num)

/-- The canonical quotient generators inhabit the existing Cuntz-system interface. -/
def quotientCuntzSystem : CuntzSystem Bool (ComplexStarCuntzAlg Bool) where
  S := Sℂ
  isometry' i j := by simpa only [star_Sℂ] using complexified_ortho i j
  completeness' := by simpa only [star_Sℂ] using (complexified_partition (ι := Bool))

theorem uniform_canonical_branch_scaling (b : Bool) (x : ComplexStarCuntzAlg Bool) :
    φ (Sℂ b * x * Tℂ b) = (1 / 2 : ℂ) * φ x := by
  rw [mul_assoc, uniform_generator_twisted_S]
  simp only [mul_assoc, complexified_ortho, ite_true, mul_one]

theorem uniform_canonicalShift_invariant (x : ComplexStarCuntzAlg Bool) :
    φ (quotientCuntzSystem.canonicalShift x) = φ x := by
  change φ (∑ b : Bool, Sℂ b * x * star (Sℂ b)) = φ x
  simp only [Fintype.sum_bool, map_add, star_Sℂ, uniform_canonical_branch_scaling]
  ring

theorem uniform_canonicalShift_iterate (n : ℕ) (x : ComplexStarCuntzAlg Bool) :
    φ (quotientCuntzSystem.canonicalShift^[n] x) = φ x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, uniform_canonicalShift_invariant]

end InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional
end
