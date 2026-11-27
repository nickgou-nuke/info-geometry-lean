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

/-! ### Peirce–DeWitt sheet-swap holonomy and Pin^± antiperiodicity obstruction -/

section PinSheetSwapHolonomy

/-- Adjoint transport by a lift element `(R, Rinv)` on the common associative ring `A`. -/
def sheetSwapAd (R Rinv X : A) : A := R * X * Rinv

/-- Conjugation swapping `P_L` to `P_R` automatically swaps `P_R` back to `P_L`. -/
theorem sheetSwap_PR (R Rinv : A) (hRL : R * Rinv = 1) (hSwapL : R * S.PL * Rinv = S.PR) :
    R * S.PR * Rinv = S.PL := by
  calc
    R * S.PR * Rinv = R * (1 - S.PL) * Rinv := by rw [right_is_complement]; rfl
    _ = R * Rinv - R * S.PL * Rinv := by noncomm_ring
    _ = 1 - S.PR := by rw [hRL, hSwapL]
    _ = (S.PL + S.PR) - S.PR := by rw [S.h_sum]
    _ = S.PL := by abel

/-- Sheet-swap adjoint negates the DeWitt chiral grading `G = P_L - P_R`. -/
theorem sheetSwap_chiralGrading (R Rinv : A) (hRL : R * Rinv = 1)
    (hSwapL : R * S.PL * Rinv = S.PR) :
    sheetSwapAd R Rinv (G (A := A)) = -(G (A := A)) := by
  have hSwapR := sheetSwap_PR R Rinv hRL hSwapL
  dsimp [sheetSwapAd, G]
  calc
    R * (S.PL - S.PR) * Rinv = R * S.PL * Rinv - R * S.PR * Rinv := by noncomm_ring
    _ = S.PR - S.PL := by rw [hSwapL, hSwapR]
    _ = -(S.PL - S.PR) := by abel

private lemma sheetSwap_intertwines_left (R Rinv : A) (hLR : Rinv * R = 1)
    (hSwapL : R * S.PL * Rinv = S.PR) :
    R * S.PL = S.PR * R := by
  calc
    R * S.PL = R * S.PL * (Rinv * R) := by rw [hLR, mul_one]
    _ = (R * S.PL * Rinv) * R := by simp only [mul_assoc]
    _ = S.PR * R := by rw [hSwapL]

private lemma sheetSwap_intertwines_right (R Rinv : A) (hLR : Rinv * R = 1)
    (hSwapL : R * S.PL * Rinv = S.PR) :
    S.PL * Rinv = Rinv * S.PR := by
  calc
    S.PL * Rinv = (Rinv * R) * S.PL * Rinv := by rw [hLR, one_mul]
    _ = Rinv * (R * S.PL * Rinv) := by simp only [mul_assoc]
    _ = Rinv * S.PR := by rw [hSwapL]

private lemma sheetSwap_PR_intertwines_left (R Rinv : A) (hRL : R * Rinv = 1)
    (hLR : Rinv * R = 1) (hSwapL : R * S.PL * Rinv = S.PR) :
    R * S.PR = S.PL * R := by
  have hSwapR := sheetSwap_PR R Rinv hRL hSwapL
  calc
    R * S.PR = R * S.PR * (Rinv * R) := by rw [hLR, mul_one]
    _ = (R * S.PR * Rinv) * R := by simp only [mul_assoc]
    _ = S.PL * R := by rw [hSwapR]

private lemma sheetSwap_PR_intertwines_right (R Rinv : A) (hRL : R * Rinv = 1)
    (hLR : Rinv * R = 1) (hSwapL : R * S.PL * Rinv = S.PR) :
    S.PR * Rinv = Rinv * S.PL := by
  have hSwapR := sheetSwap_PR R Rinv hRL hSwapL
  calc
    S.PR * Rinv = (Rinv * R) * S.PR * Rinv := by rw [hLR, one_mul]
    _ = Rinv * (R * S.PR * Rinv) := by simp only [mul_assoc]
    _ = Rinv * S.PL := by rw [hSwapR]

/-- Sheet-swap adjoint preserves the even DeWitt `body` subspace (`body(Ad_R X) = Ad_R(body X)`). -/
theorem sheetSwap_body (R Rinv : A) (hRL : R * Rinv = 1) (hLR : Rinv * R = 1)
    (hSwapL : R * S.PL * Rinv = S.PR) (X : A) :
    sheetSwapAd R Rinv (body X) = body (sheetSwapAd R Rinv X) := by
  have hL1 := sheetSwap_intertwines_left R Rinv hLR hSwapL
  have hL2 := sheetSwap_intertwines_right R Rinv hLR hSwapL
  have hR1 := sheetSwap_PR_intertwines_left R Rinv hRL hLR hSwapL
  have hR2 := sheetSwap_PR_intertwines_right R Rinv hRL hLR hSwapL
  dsimp [sheetSwapAd, body]
  calc
    R * (S.PL * X * S.PL + S.PR * X * S.PR) * Rinv
        = (R * S.PL) * X * (S.PL * Rinv) + (R * S.PR) * X * (S.PR * Rinv) := by
          simp only [mul_add, add_mul, mul_assoc]
    _ = (S.PR * R) * X * (Rinv * S.PR) + (S.PL * R) * X * (Rinv * S.PL) := by
          rw [hL1, hL2, hR1, hR2]
    _ = S.PL * (R * X * Rinv) * S.PL + S.PR * (R * X * Rinv) * S.PR := by
          simp only [mul_assoc]; exact add_comm _ _

/-- Sheet-swap adjoint exchanges the two odd nilpotent Peirce–DeWitt soul corners `soul_LR ↔ soul_RL`. -/
theorem sheetSwap_soul_corners (R Rinv : A) (hRL : R * Rinv = 1) (hLR : Rinv * R = 1)
    (hSwapL : R * S.PL * Rinv = S.PR) (X : A) :
    sheetSwapAd R Rinv (soul_LR X) = soul_RL (sheetSwapAd R Rinv X) ∧
    sheetSwapAd R Rinv (soul_RL X) = soul_LR (sheetSwapAd R Rinv X) := by
  have hL1 := sheetSwap_intertwines_left R Rinv hLR hSwapL
  have hL2 := sheetSwap_intertwines_right R Rinv hLR hSwapL
  have hR1 := sheetSwap_PR_intertwines_left R Rinv hRL hLR hSwapL
  have hR2 := sheetSwap_PR_intertwines_right R Rinv hRL hLR hSwapL
  dsimp [sheetSwapAd, soul_LR, soul_RL]
  refine ⟨?_, ?_⟩
  · calc
      R * (S.PL * X * S.PR) * Rinv = (R * S.PL) * X * (S.PR * Rinv) := by simp only [mul_assoc]
      _ = (S.PR * R) * X * (Rinv * S.PL) := by rw [hL1, hR2]
      _ = S.PR * (R * X * Rinv) * S.PL := by simp only [mul_assoc]
  · calc
      R * (S.PR * X * S.PL) * Rinv = (R * S.PR) * X * (S.PL * Rinv) := by simp only [mul_assoc]
      _ = (S.PL * R) * X * (Rinv * S.PR) := by rw [hR1, hL2]
      _ = S.PL * (R * X * Rinv) * S.PR := by simp only [mul_assoc]

/-- Sheet-swap adjoint preserves the odd DeWitt `soul` bimodule (`soul(Ad_R X) = Ad_R(soul X)`). -/
theorem sheetSwap_soul (R Rinv : A) (hRL : R * Rinv = 1) (hLR : Rinv * R = 1)
    (hSwapL : R * S.PL * Rinv = S.PR) (X : A) :
    sheetSwapAd R Rinv (soul X) = soul (sheetSwapAd R Rinv X) := by
  have hc := sheetSwap_soul_corners R Rinv hRL hLR hSwapL X
  dsimp [sheetSwapAd, soul] at *
  calc
    R * (soul_LR X + soul_RL X) * Rinv
        = R * soul_LR X * Rinv + R * soul_RL X * Rinv := by noncomm_ring
    _ = soul_RL (R * X * Rinv) + soul_LR (R * X * Rinv) := by rw [hc.1, hc.2]
    _ = soul_LR (R * X * Rinv) + soul_RL (R * X * Rinv) := add_comm _ _

omit S in
/-- Both `Pin⁺` (`R² = +1`) and `Pin⁻` (`R² = -1`) induce periodic adjoint holonomy on observables. -/
theorem sheetSwapAd_sq_periodic_of_pin_plus (R Rinv : A)
    (hLR : Rinv * R = 1) (hSq : R * R = 1) (X : A) :
    sheetSwapAd R Rinv (sheetSwapAd R Rinv X) = X := by
  have hInv : Rinv = R := by
    calc
      Rinv = Rinv * (R * R) := by rw [hSq, mul_one]
      _ = (Rinv * R) * R := by rw [mul_assoc]
      _ = R := by rw [hLR, one_mul]
  dsimp [sheetSwapAd]
  calc
    R * (R * X * Rinv) * Rinv = (R * R) * X * (Rinv * Rinv) := by simp only [mul_assoc]
    _ = 1 * X * 1 := by simp only [hInv, hSq]
    _ = X := by rw [one_mul, mul_one]

omit S in
/-- On `Pin⁻` (`R² = -1`), the double-glide minus signs cancel on the bilinear/adjoint observable sector. -/
theorem sheetSwapAd_sq_periodic_of_pin_minus (R Rinv : A)
    (hLR : Rinv * R = 1) (hSq : R * R = -1) (X : A) :
    sheetSwapAd R Rinv (sheetSwapAd R Rinv X) = X := by
  have hInv : Rinv = -R := by
    calc
      Rinv = -(Rinv * (-1)) := by rw [mul_neg, mul_one, neg_neg]
      _ = -(Rinv * (R * R)) := by rw [hSq]
      _ = -((Rinv * R) * R) := by rw [mul_assoc]
      _ = -R := by rw [hLR, one_mul]
  have hInvSq : Rinv * Rinv = -1 := by
    rw [hInv, neg_mul_neg, hSq]
  dsimp [sheetSwapAd]
  calc
    R * (R * X * Rinv) * Rinv = (R * R) * X * (Rinv * Rinv) := by simp only [mul_assoc]
    _ = (-1) * X * (-1) := by rw [hSq, hInvSq]
    _ = X := by noncomm_ring

omit S in
/-- Under a `Pin⁻` (`R² = -1`) equivariant glide law, linear fields `u, v` acquire double-glide
antiperiodicity `-1` while the coupled bilinear `u * v` transforms by `sheetSwapAd` and is strictly periodic. -/
theorem pin_minus_left_antiperiodic_and_bilinear_body_periodic {Base : Type*} (g : Base → Base)
    (R Rinv : A) (hLR : Rinv * R = 1) (hSq : R * R = -1)
    (u v : Base → A) (hu : ∀ x, u (g x) = R * u x) (hv : ∀ x, v (g x) = v x * Rinv) (x : Base) :
    u (g (g x)) = -u x ∧
    v (g (g x)) = -v x ∧
    (u (g x) * v (g x) = sheetSwapAd R Rinv (u x * v x)) ∧
    (u (g (g x)) * v (g (g x)) = u x * v x) := by
  have hInv : Rinv = -R := by
    calc
      Rinv = -(Rinv * (-1)) := by rw [mul_neg, mul_one, neg_neg]
      _ = -(Rinv * (R * R)) := by rw [hSq]
      _ = -((Rinv * R) * R) := by rw [mul_assoc]
      _ = -R := by rw [hLR, one_mul]
  have hInvSq : Rinv * Rinv = -1 := by rw [hInv, neg_mul_neg, hSq]
  have hu2 : u (g (g x)) = -u x := by
    rw [hu (g x), hu x, ← mul_assoc, hSq, neg_one_mul]
  have hv2 : v (g (g x)) = -v x := by
    rw [hv (g x), hv x, mul_assoc, hInvSq, mul_neg_one]
  refine ⟨hu2, hv2, ?_, ?_⟩
  · rw [hu x, hv x]
    dsimp [sheetSwapAd]
    simp only [mul_assoc]
  · rw [hu2, hv2, neg_mul_neg]

omit S in
/-- A `Pin⁻` (`R² = -1`) equivariant field cannot satisfy ordinary torus periodicity unless it vanishes identically. -/
theorem pin_minus_periodic_obstruction {Base : Type*} (g : Base → Base) (R : A)
    (hSq : R * R = -1) (hTwo : ∀ a : A, a + a = 0 → a = 0)
    (u : Base → A) (hu : ∀ x, u (g x) = R * u x) (hper : ∀ x, u (g (g x)) = u x) :
    u = 0 := by
  funext x
  have hAnti : u (g (g x)) = -u x := by
    rw [hu (g x), hu x, ← mul_assoc, hSq, neg_one_mul]
  have hEq : -(u x) = u x := hAnti.symm.trans (hper x)
  have hSum : u x + u x = 0 := by
    calc
      u x + u x = u x + -(u x) := by conv_rhs => rw [hEq]
      _ = 0 := add_neg_cancel _
  exact hTwo (u x) hSum

/-- The DeWitt chiral grading `G = P_L - P_R` squares to `1`. -/
theorem G_sq : (G (A := A)) * G = 1 := by
  dsimp [G]
  have hPRPL := PR_PL_ortho (A := A)
  calc (S.PL - S.PR) * (S.PL - S.PR)
    _ = S.PL * S.PL - S.PL * S.PR - S.PR * S.PL + S.PR * S.PR := by noncomm_ring
    _ = S.PL + S.PR := by rw [S.h_PL_sq, S.h_PL_PR, hPRPL, S.h_PR_sq]; abel
    _ = 1 := S.h_sum

/-- A sheet-swapping lift `R` anticommutes with the DeWitt chiral grading `G = P_L - P_R`. -/
theorem sheetSwap_chirality_anticomm (R Rinv : A) (hRL : R * Rinv = 1) (hLR : Rinv * R = 1)
    (hSwapL : R * S.PL * Rinv = S.PR) :
    R * G (A := A) = -(G (A := A) * R) := by
  have hAd := sheetSwap_chiralGrading R Rinv hRL hSwapL
  dsimp [sheetSwapAd] at hAd
  calc R * G (A := A) = (R * G (A := A)) * (Rinv * R) := by rw [hLR, mul_one]
    _ = (R * G (A := A) * Rinv) * R := by simp only [mul_assoc]
    _ = (-(G (A := A))) * R := by rw [hAd]
    _ = -(G (A := A) * R) := by rw [neg_mul]

/-- Dressing any sheet-swap lift `R` by the DeWitt chiral grading `G = P_L - P_R` flips the
double-glide holonomy sign `(G * R)² = -(R²)`: a `Pin⁺` sheet swap (`R² = +1`) dressed by `G`
is automatically `Pin⁻` (`(G * R)² = -1`), and conversely `Pin⁻` dressed by `G` is `Pin⁺`. -/
theorem sheetSwap_pin_lift_chirality_sign (R Rinv : A) (hRL : R * Rinv = 1) (hLR : Rinv * R = 1)
    (hSwapL : R * S.PL * Rinv = S.PR) :
    (G (A := A) * R) * (G (A := A) * R) = -(R * R) := by
  have hAnti := sheetSwap_chirality_anticomm R Rinv hRL hLR hSwapL
  calc (G (A := A) * R) * (G (A := A) * R)
    _ = G (A := A) * (R * G (A := A)) * R := by simp only [mul_assoc]
    _ = G (A := A) * (-(G (A := A) * R)) * R := by rw [hAnti]
    _ = -((G (A := A) * G (A := A)) * (R * R)) := by noncomm_ring
    _ = -(R * R) := by rw [G_sq, one_mul]

/-- Chirality-dressed sheet-swap adjoint `Ad_{G * R}` leaves the even `body` sign unchanged (`+1`)
while inverting the sign of the odd `soul` bimodule and both chiral corners (`-1`). -/
theorem chiralityDressedSheetSwap_body_vs_soul (R Rinv : A) (hRL : R * Rinv = 1)
    (hLR : Rinv * R = 1) (hSwapL : R * S.PL * Rinv = S.PR) (X : A) :
    (G (A := A) * R) * (Rinv * G (A := A)) = 1 ∧
    (Rinv * G (A := A)) * (G (A := A) * R) = 1 ∧
    sheetSwapAd (G (A := A) * R) (Rinv * G (A := A)) (body X) = sheetSwapAd R Rinv (body X) ∧
    sheetSwapAd (G (A := A) * R) (Rinv * G (A := A)) (soul X) = -(sheetSwapAd R Rinv (soul X)) ∧
    sheetSwapAd (G (A := A) * R) (Rinv * G (A := A)) (soul_LR X) =
      -(sheetSwapAd R Rinv (soul_LR X)) ∧
    sheetSwapAd (G (A := A) * R) (Rinv * G (A := A)) (soul_RL X) =
      -(sheetSwapAd R Rinv (soul_RL X)) := by
  have hBodySwap := sheetSwap_body R Rinv hRL hLR hSwapL X
  have hSoulSwap := sheetSwap_soul R Rinv hRL hLR hSwapL X
  have hCorners := sheetSwap_soul_corners R Rinv hRL hLR hSwapL X
  dsimp [sheetSwapAd] at hBodySwap hSoulSwap hCorners
  have hGR : (G (A := A) * R) * (Rinv * G (A := A)) = 1 := by
    calc (G (A := A) * R) * (Rinv * G (A := A))
      _ = G (A := A) * (R * Rinv) * G (A := A) := by simp only [mul_assoc]
      _ = G (A := A) * G (A := A) := by rw [hRL, mul_one]
      _ = 1 := G_sq
  have hRG : (Rinv * G (A := A)) * (G (A := A) * R) = 1 := by
    calc (Rinv * G (A := A)) * (G (A := A) * R)
      _ = Rinv * (G (A := A) * G (A := A)) * R := by simp only [mul_assoc]
      _ = Rinv * R := by rw [G_sq, mul_one]
      _ = 1 := hLR
  refine ⟨hGR, hRG, ?_, ?_, ?_, ?_⟩
  · dsimp [sheetSwapAd]
    calc (G (A := A) * R) * body X * (Rinv * G (A := A))
      _ = G (A := A) * (R * body X * Rinv) * G (A := A) := by simp only [mul_assoc]
      _ = G (A := A) * body (R * X * Rinv) * G (A := A) := by rw [← hBodySwap]
      _ = body (R * X * Rinv) := G_body_parity_even _
      _ = R * body X * Rinv := by rw [← hBodySwap]
  · dsimp [sheetSwapAd]
    calc (G (A := A) * R) * soul X * (Rinv * G (A := A))
      _ = G (A := A) * (R * soul X * Rinv) * G (A := A) := by simp only [mul_assoc]
      _ = G (A := A) * soul (R * X * Rinv) * G (A := A) := by rw [← hSoulSwap]
      _ = -soul (R * X * Rinv) := G_soul_parity_odd _
      _ = -(R * soul X * Rinv) := by rw [← hSoulSwap]
  · dsimp [sheetSwapAd]
    calc (G (A := A) * R) * soul_LR X * (Rinv * G (A := A))
      _ = G (A := A) * (R * soul_LR X * Rinv) * G (A := A) := by simp only [mul_assoc]
      _ = G (A := A) * soul_RL (R * X * Rinv) * G (A := A) := by rw [← hCorners.1]
      _ = -soul_RL (R * X * Rinv) := by
          dsimp [soul_RL]
          calc G (A := A) * (S.PR * (R * X * Rinv) * S.PL) * G (A := A)
            _ = (G (A := A) * S.PR) * (R * X * Rinv) * (S.PL * G (A := A)) := by
                simp only [mul_assoc]
            _ = (-S.PR) * (R * X * Rinv) * S.PL := by rw [G_mul_PR, PL_mul_G]
            _ = -(S.PR * (R * X * Rinv) * S.PL) := by rw [neg_mul, neg_mul]
      _ = -(R * soul_LR X * Rinv) := by rw [← hCorners.1]
  · dsimp [sheetSwapAd]
    calc (G (A := A) * R) * soul_RL X * (Rinv * G (A := A))
      _ = G (A := A) * (R * soul_RL X * Rinv) * G (A := A) := by simp only [mul_assoc]
      _ = G (A := A) * soul_LR (R * X * Rinv) * G (A := A) := by rw [← hCorners.2]
      _ = -soul_LR (R * X * Rinv) := G_soul_LR_parity_odd _
      _ = -(R * soul_RL X * Rinv) := by rw [← hCorners.2]

/-- On a `ChiralPeirceSystem A`, a `Pin⁻` (`R² = -1`) sheet-swapping equivariant spinor
transforms sheets `P_L → P_R` with `-1` double-glide holonomy, while its bilinear `body`
is strictly `+1` periodic and the chirality-dressed adjoint flips `soul` relative to `body`. -/
theorem pin_minus_chiral_body_periodic_soul_antiperiodic
    {Base : Type*} (g : Base → Base) (R Rinv : A)
    (hRL : R * Rinv = 1) (hLR : Rinv * R = 1)
    (hSwapL : R * S.PL * Rinv = S.PR) (hSq : R * R = -1)
    (ψ ψbar : Base → A) (hψ : ∀ p, ψ (g p) = R * ψ p)
    (hψbar : ∀ p, ψbar (g p) = ψbar p * Rinv) (p : Base) :
    (S.PL * ψ p = ψ p → S.PR * ψ (g p) = ψ (g p)) ∧
    (ψ (g (g p)) = -ψ p) ∧
    (body (ψ (g p) * ψbar (g p)) = sheetSwapAd R Rinv (body (ψ p * ψbar p))) ∧
    (body (ψ (g (g p)) * ψbar (g (g p))) = body (ψ p * ψbar p)) ∧
    (sheetSwapAd (G (A := A) * R) (Rinv * G (A := A)) (soul (ψ p * ψbar p)) =
      -(soul (ψ (g p) * ψbar (g p)))) := by
  have hPin := pin_minus_left_antiperiodic_and_bilinear_body_periodic
    g R Rinv hLR hSq ψ ψbar hψ hψbar p
  have hBodySwap := sheetSwap_body R Rinv hRL hLR hSwapL (ψ p * ψbar p)
  have hSoulSwap := sheetSwap_soul R Rinv hRL hLR hSwapL (ψ p * ψbar p)
  have hDress := (chiralityDressedSheetSwap_body_vs_soul R Rinv hRL hLR hSwapL (ψ p * ψbar p)).2.2.2.1
  have hL1 := sheetSwap_intertwines_left R Rinv hLR hSwapL
  refine ⟨?_, hPin.1, ?_, ?_, ?_⟩
  · intro hL
    calc S.PR * ψ (g p) = S.PR * (R * ψ p) := by rw [hψ p]
      _ = (S.PR * R) * ψ p := by rw [mul_assoc]
      _ = (R * S.PL) * ψ p := by rw [hL1]
      _ = R * (S.PL * ψ p) := by rw [mul_assoc]
      _ = R * ψ p := by rw [hL]
      _ = ψ (g p) := (hψ p).symm
  · rw [hPin.2.2.1, hBodySwap]
  · rw [hPin.2.2.2]
  · rw [hDress, hSoulSwap, ← hPin.2.2.1]

/-- A periodic `Pin⁻` equivariant field in a 2-torsion-free `ChiralPeirceSystem A`
vanishes on every Peirce–DeWitt sector (`body`, `soul_LR`, `soul_RL`). -/
theorem pin_minus_periodic_vanishes_on_peirce_sectors
    {Base : Type*} (g : Base → Base) (R : A)
    (hSq : R * R = -1) (hTwo : ∀ a : A, a + a = 0 → a = 0)
    (ψ : Base → A) (hψ : ∀ p, ψ (g p) = R * ψ p)
    (hper : ∀ p, ψ (g (g p)) = ψ p) (p : Base) :
    body (ψ p) = 0 ∧ soul_LR (ψ p) = 0 ∧ soul_RL (ψ p) = 0 := by
  have hZero : ψ = 0 := pin_minus_periodic_obstruction g R hSq hTwo ψ hψ hper
  have hp : ψ p = 0 := congrFun hZero p
  refine ⟨?_, ?_, ?_⟩
  · simp [body, hp]
  · simp [soul_LR, hp]
  · simp [soul_RL, hp]

end PinSheetSwapHolonomy

end InfoGeometry.Algebra.DeWittPeirceChiralBridge
