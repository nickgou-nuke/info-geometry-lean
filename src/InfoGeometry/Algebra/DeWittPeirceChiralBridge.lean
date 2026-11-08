/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.DeWittPeirceSuperalgebra
import InfoGeometry.Algebra.PeirceDeWittChiralSplit
import InfoGeometry.Algebra.IdempotentProjector
import InfoGeometry.Algebra.OperatorCyclotomicParafermions
import InfoGeometry.Algebra.OperatorCyclotomicCoxeterBridge

/-!
# DeWitt body/soul and Peirce parity are the same four-corner split

This bridge identifies two existing presentations on one associative ring.
The complementary chiral idempotent is derived from the DeWitt partition of
unity; it is not introduced as an independent choice.
-/

namespace InfoGeometry.Algebra.DeWittPeirceChiralBridge

open InfoGeometry.Algebra.DeWittPeirceSuperalgebra
open InfoGeometry.Algebra.PeirceDeWittChiralSplit
open InfoGeometry.Algebra.OperatorCyclotomicParafermions
open InfoGeometry.Algebra.IsotropicCyclotomicGalois

variable {A : Type*} [Ring A] [S : ChiralPeirceSystem A]

/-- The right chiral idempotent is the complement of the left one, as forced
by the partition of unity. -/
theorem right_is_complement : S.PR = compIdempotent S.PL := by
  dsimp [compIdempotent]
  calc
    S.PR = (S.PL + S.PR) - S.PL := by abel
    _ = 1 - S.PL := by rw [S.h_sum]

/-- DeWitt's diagonal body is exactly the even Peirce projection. -/
theorem body_eq_evenPart (x : A) :
    body x = evenPart S.PL x := by
  change S.PL * x * S.PL + S.PR * x * S.PR =
    peirce11 S.PL x + peirce00 S.PL x
  rw [peirce11, peirce00, right_is_complement]

/-- DeWitt's off-diagonal soul is exactly the odd Peirce projection. -/
theorem soul_eq_oddPart (x : A) :
    soul x = oddPart S.PL x := by
  change S.PL * x * S.PR + S.PR * x * S.PL =
    peirce10 S.PL x + peirce01 S.PL x
  rw [peirce10, peirce01, right_is_complement]

/-- The DeWitt chiral grading and the complementary-idempotent Peirce
grading are the same operator. -/
theorem chiralGrading_eq_peirceGrading :
    G (A := A) = grading S.PL := by
  change S.PL - S.PR = S.PL - compIdempotent S.PL
  rw [right_is_complement]

/-- The decompositions agree term by term on the common ring carrier. -/
theorem bodySoul_split_eq_peirce_split (x : A) :
    x = body x + soul x ∧
    x = evenPart S.PL x + oddPart S.PL x ∧
    body x = evenPart S.PL x ∧ soul x = oddPart S.PL x := by
  refine ⟨dewitt_split x, peirce_even_odd_decomposition S.PL x,
    body_eq_evenPart x, soul_eq_oddPart x⟩

/-! ### Peirce corner to cyclotomic bridge -/

/-- The ordered Bruhat unit built from the two Peirce off-diagonal corners
has the generic square-zero cyclotomic defect, with its operator-valued
coefficient identified exactly as the Peirce interband metric. -/
theorem peirce_bruhat_cyclotomic_defect (a c : A) :
    cyclo6 (bruhat (peirce10 S.PL a) (peirce01 S.PL c)) =
      (1 - interbandMetric S.PL a c) *
        bruhat (peirce10 S.PL a) (peirce01 S.PL c) := by
  have hu : peirce10 S.PL a * peirce10 S.PL a = 0 :=
    peirce10_square_zero S.h_PL_sq a
  have hv : peirce01 S.PL c * peirce01 S.PL c = 0 :=
    peirce01_square_zero S.h_PL_sq c
  obtain ⟨_, _, _, _, _, h6, _, _⟩ :=
    bruhat_cyclotomic_characteristic
      (peirce10 S.PL a) (peirce01 S.PL c) hu hv
  simpa [anticommutator, interbandMetric] using h6

/-- On the unit interband-metric shell, the Peirce Bruhat operator is a
sixth-cyclotomic root and its cube is `-1`. This specializes the generic
cyclotomic theorem through the actual Peirce/DeWitt corner construction. -/
theorem peirce_bruhat_sixth_root_on_metric_shell (a c : A)
    (hV : interbandMetric S.PL a c = 1) :
    cyclo6 (bruhat (peirce10 S.PL a) (peirce01 S.PL c)) = 0 ∧
    bruhat (peirce10 S.PL a) (peirce01 S.PL c) *
      bruhat (peirce10 S.PL a) (peirce01 S.PL c) *
      bruhat (peirce10 S.PL a) (peirce01 S.PL c) = -1 := by
  have hroot : cyclo6 (bruhat (peirce10 S.PL a) (peirce01 S.PL c)) = 0 := by
    rw [peirce_bruhat_cyclotomic_defect]
    rw [hV]
    simp
  exact ⟨hroot, cyclo6_root_cube_eq_neg_one _ hroot⟩

/-- On the unit interband-metric shell, the actual Peirce corner pair gives
the existing rank-two Coxeter representation on the doubled operator
carrier. The shell equation supplies the coefficient-unit relation required
by the reflection lift. -/
noncomputable def peirceBruhatG2Rep (a c : A)
    (hV : interbandMetric S.PL a c = 1) :
    (CoxeterMatrix.G₂).Group →* Equiv.Perm (A × A) := by
  let u := peirce10 S.PL a
  let v := peirce01 S.PL c
  have hu : u * u = 0 := peirce10_square_zero S.h_PL_sq a
  have hv : v * v = 0 := peirce01_square_zero S.h_PL_sq c
  have hunit : anticommutator u v = 1 := by
    simpa [u, v, anticommutator, interbandMetric] using hV
  have hsix := bruhatUnit_sixth_power_on_shell u v hu hv hunit |>.1
  exact OperatorCyclotomicCoxeterBridge.g2BlockOperatorRep
    (bruhatUnit u v hu hv) hsix

@[simp] theorem peirceBruhatG2Rep_apply_simple_zero (a c : A)
    (hV : interbandMetric S.PL a c = 1) :
    peirceBruhatG2Rep a c hV ((CoxeterMatrix.G₂).simple 0) =
      OperatorCyclotomicCoxeterBridge.blockSwap := by
  unfold peirceBruhatG2Rep
  simp

@[simp] theorem peirceBruhatG2Rep_apply_simple_one (a c : A)
    (hV : interbandMetric S.PL a c = 1) :
    peirceBruhatG2Rep a c hV ((CoxeterMatrix.G₂).simple 1) =
      OperatorCyclotomicCoxeterBridge.blockTwistedReflection
        (bruhatUnit (peirce10 S.PL a) (peirce01 S.PL c)
          (peirce10_square_zero S.h_PL_sq a)
          (peirce01_square_zero S.h_PL_sq c)) := by
  unfold peirceBruhatG2Rep
  simp

/-- The Coxeter rotation on the Peirce carrier is exactly the block rotation
of the Bruhat unit built from its two off-diagonal corners. -/
theorem peirceBruhatG2Rep_simple_product (a c : A)
    (hV : interbandMetric S.PL a c = 1) :
    peirceBruhatG2Rep a c hV
        ((CoxeterMatrix.G₂).simple 0 * (CoxeterMatrix.G₂).simple 1) =
      OperatorCyclotomicCoxeterBridge.blockRotation
        (bruhatUnit (peirce10 S.PL a) (peirce01 S.PL c)
          (peirce10_square_zero S.h_PL_sq a)
          (peirce01_square_zero S.h_PL_sq c))⁻¹ := by
  let u := peirce10 S.PL a
  let v := peirce01 S.PL c
  have hu : u * u = 0 := peirce10_square_zero S.h_PL_sq a
  have hv : v * v = 0 := peirce01_square_zero S.h_PL_sq c
  have hunit : anticommutator u v = 1 := by
    simpa [u, v, anticommutator, interbandMetric] using hV
  have hsix := bruhatUnit_sixth_power_on_shell u v hu hv hunit |>.1
  simpa [peirceBruhatG2Rep, u, v] using
    (OperatorCyclotomicCoxeterBridge.g2BlockOperatorRep_simple_product
      (bruhatUnit u v hu hv) hsix)

theorem peirce_bruhat_g2_coxeter_representation (a c : A)
    (hV : interbandMetric S.PL a c = 1) :
    Nonempty ((CoxeterMatrix.G₂).Group →* Equiv.Perm (A × A)) := by
  exact ⟨peirceBruhatG2Rep a c hV⟩

end InfoGeometry.Algebra.DeWittPeirceChiralBridge
