/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized

/-!
# Noninjectivity of the four homogenized channels

Contract: the existing channels on an arbitrary nontrivial associative ring,
with an idempotent Peirce endpoint for the `V` channel. Use the proved A3
square identity and A13 generator selection. No zero-corner specialization,
characteristic restriction, or scalar replacement is needed. These are
additive channels with weighted generator identities, not ring automorphisms.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

theorem hProj_zero (P A C : B) :
    hProjV P A C 0 = 0 ∧ hProjPhi P A C 0 = 0 ∧
      hProjJ P A C 0 = 0 ∧ hProjSig P A C 0 = 0 := by
  simp [hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig, comm]

theorem hProj_one (P A C : B) :
    hProjV P A C 1 = (8 : ℤ) • (genV P A C * genV P A C) ∧
      hProjPhi P A C 1 = 0 ∧ hProjJ P A C 1 = 0 ∧ hProjSig P A C 1 = 0 := by
  simp [hProjV, hProjPhi, hProjJ, hProjSig, derivSqPhi, derivSqJ, derivSqSig, comm]

variable [Nontrivial B]

theorem hProjV_not_injective {P : B} (hP : P * P = P) (A C : B) :
    ¬ Function.Injective (hProjV P A C) := by
  intro hi
  by_cases hPhi : genPhi P A C = 0
  · have hV : genV P A C = 0 := by
      have hs := (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1
      simpa only [hPhi, zero_mul] using hs.symm
    apply one_ne_zero (hi (a₁ := 1) (a₂ := 0) ?_)
    rw [(hProj_one P A C).1, (hProj_zero P A C).1, hV, zero_mul, smul_zero]
  · apply hPhi (hi (a₁ := genPhi P A C) (a₂ := 0) ?_)
    rw [(archetype_A13_homogenized_projectors hP A C 0).2.2.1,
      (hProj_zero P A C).1]

theorem hProjPhi_not_injective (P A C : B) :
    ¬ Function.Injective (hProjPhi P A C) := by
  intro hi
  exact one_ne_zero (hi ((hProj_one P A C).2.1.trans (hProj_zero P A C).2.1.symm))

theorem hProjJ_not_injective (P A C : B) :
    ¬ Function.Injective (hProjJ P A C) := by
  intro hi
  exact one_ne_zero (hi ((hProj_one P A C).2.2.1.trans (hProj_zero P A C).2.2.1.symm))

theorem hProjSig_not_injective (P A C : B) :
    ¬ Function.Injective (hProjSig P A C) := by
  intro hi
  exact one_ne_zero (hi ((hProj_one P A C).2.2.2.trans (hProj_zero P A C).2.2.2.symm))

end InfoGeometry.OperatorAlgebra.PeirceSpine
