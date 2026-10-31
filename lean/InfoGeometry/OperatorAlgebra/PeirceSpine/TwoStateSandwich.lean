/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.ConeSheetBraiding
import Mathlib.Algebra.Star.Basic

/-!
# Ordered two-chart sandwiches

For the graph-chart elements `P - N₊` and `P + N₋`, this file records their
ordered products with the four Peirce generators and with all finite defect
iterates of the Peirce cycles. These are identities in an arbitrary associative
ring; no group action or scalar-valued transition probability is inferred.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B)
include hP

def chartBruhatConj (P A C X : B) : B :=
  (1 + conePlus P A) * (1 - coneMinus P C) * X *
    (1 + coneMinus P C) * (1 - conePlus P A)

/-- Conjugation by the inverse of the two-factor chart element. -/
def chartBruhatConjInv (P A C X : B) : B :=
  (1 + coneMinus P C) * (1 - conePlus P A) * X *
    (1 + conePlus P A) * (1 - coneMinus P C)

/-- The chart sandwich readout on the four generators `(Φ, J, V, Σ)`. -/
theorem chart_two_state_generator_sandwich :
    (P - conePlus P A) * genPhi P A C * (P + coneMinus P C) = 0 ∧
    (P - conePlus P A) * genJ P A C * (P + coneMinus P C) =
      (2 : ℤ) • (conePlus P A * coneMinus P C) ∧
    (P - conePlus P A) * genV P A C * (P + coneMinus P C) =
      -((conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C) -
        conePlus P A * coneMinus P C) ∧
    (P - conePlus P A) * genSig P A C * (P + coneMinus P C) =
      conePlus P A * coneMinus P C +
        (conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- Products of the two chart elements with the linear combinations `Φ ± J`. -/
theorem chart_spinor_selection_products :
    (genPhi P A C + genJ P A C) * (P + coneMinus P C) =
      (2 : ℤ) • (conePlus P A * coneMinus P C) ∧
    (genPhi P A C - genJ P A C) * (P + coneMinus P C) =
      (2 : ℤ) • coneMinus P C ∧
    (P - conePlus P A) * (genPhi P A C - genJ P A C) =
      -((2 : ℤ) • (conePlus P A * coneMinus P C)) ∧
    (P - conePlus P A) * (genPhi P A C + genJ P A C) =
      (2 : ℤ) • conePlus P A := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- The product of the two chart points is the base corner minus the upper
cycle; the off-diagonal terms vanish by Peirce support. -/
theorem chart_point_product :
    (P - conePlus P A) * (P + coneMinus P C) =
      P - conePlus P A * coneMinus P C := by
  peirce_nf hP

/-- The two-factor chart conjugation sends the lower chart point to the upper
chart point. -/
theorem chart_bruhat_conjugation_transition :
    chartBruhatConj P A C (P + coneMinus P C) = P - conePlus P A ∧
    chartBruhatConjInv P A C (P - conePlus P A) = P + coneMinus P C := by
  constructor
  · unfold chartBruhatConj
    peirce_nf hP
  · unfold chartBruhatConjInv
    peirce_nf hP

/-- The two-factor unipotent products `(1 + N₊)(1 - N₋)` and `(1 + N₋)(1 - N₊)`
are two-sided inverses. -/
theorem chart_bruhat_factor_mul_inv :
    ((1 + conePlus P A) * (1 - coneMinus P C)) *
        ((1 + coneMinus P C) * (1 - conePlus P A)) = 1 ∧
    ((1 + coneMinus P C) * (1 - conePlus P A)) *
        ((1 + conePlus P A) * (1 - coneMinus P C)) = 1 := by
  constructor <;> peirce_nf hP

/-- `chartBruhatConj P A C` is a multiplicative homomorphism of `B`. -/
theorem chartBruhatConj_mul (X Y : B) :
    chartBruhatConj P A C (X * Y) =
      chartBruhatConj P A C X * chartBruhatConj P A C Y := by
  have hInv := (chart_bruhat_factor_mul_inv hP A C).2
  unfold chartBruhatConj
  calc
    (1 + conePlus P A) * (1 - coneMinus P C) * (X * Y) *
        (1 + coneMinus P C) * (1 - conePlus P A) =
      (1 + conePlus P A) * (1 - coneMinus P C) * X * 1 * Y *
        (1 + coneMinus P C) * (1 - conePlus P A) := by
      rw [mul_one]; simp only [mul_assoc]
    _ = (1 + conePlus P A) * (1 - coneMinus P C) * X *
        (((1 + coneMinus P C) * (1 - conePlus P A)) *
          ((1 + conePlus P A) * (1 - coneMinus P C))) * Y *
        (1 + coneMinus P C) * (1 - conePlus P A) := by
      rw [hInv]
    _ = ((1 + conePlus P A) * (1 - coneMinus P C) * X *
          (1 + coneMinus P C) * (1 - conePlus P A)) *
        ((1 + conePlus P A) * (1 - coneMinus P C) * Y *
          (1 + coneMinus P C) * (1 - conePlus P A)) := by
      simp only [mul_assoc]

/-- `chartBruhatConj P A C` fixes the quadratic Peirce metric `genV P A C`. -/
theorem chartBruhatConj_genV :
    chartBruhatConj P A C (genV P A C) = genV P A C := by
  unfold chartBruhatConj
  peirce_nf hP

/-- The `Σ` chart sandwich differs from the Euler-compressed `Q₊` value by
exactly twice the quadratic cycle. This is the finite-depth obstruction to
the A82 transcript's proposed `Σ` sandwich formula at depth zero. -/
theorem chart_sigma_euler_compression_residual :
    (P - conePlus P A) * genSig P A C * (P + coneMinus P C) -
      (1 - genV P A C) * (conePlus P A * coneMinus P C) =
        (2 : ℤ) •
          ((conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C)) := by
  peirce_nf hP

/-! ### All-Depth Two-State Sandwiches (`A80`, `A82`) -/

/-- At every defect depth `n`, the upper-cycle iterate `δ^[n](Q₊)` is fixed
under the two-state chart sandwich `(P - N₊) · (P + N₋)`. -/
theorem chart_two_state_qgtPlus_defect_iterate (n : ℕ) :
    (P - conePlus P A) * idempotencyDefect^[n] (qgtPlus P A C) *
        (P + coneMinus P C) =
      idempotencyDefect^[n] (qgtPlus P A C) := by
  have hPL := qgtPlus_defect_iterates_left hP A C n
  have hPR := qgtPlus_defect_iterates_right hP A C n
  have hNL := (qgt_defect_iterates_cone_relations hP A C n).1
  have hNR := (qgt_defect_iterates_cone_relations hP A C n).2.2.2.2.1
  have hLeft : (P - conePlus P A) * idempotencyDefect^[n] (qgtPlus P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) := by
    rw [sub_mul, hPL, hNL, sub_zero]
  rw [hLeft, mul_add, hPR, hNR, add_zero]

/-- Left multiplication by `genV P A C` on the upper iterated cycle `δ^[n](Q₊)`
agrees with left or right multiplication by `qgtPlus P A C`. -/
theorem genV_mul_qgtPlus_defect_iterate (n : ℕ) :
    genV P A C * idempotencyDefect^[n] (qgtPlus P A C) =
      qgtPlus P A C * idempotencyDefect^[n] (qgtPlus P A C) ∧
    qgtPlus P A C * idempotencyDefect^[n] (qgtPlus P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) * qgtPlus P A C := by
  have hYX := (qgt_defect_iterates_cross_orthogonal hP A C 0 n).2
  simp only [Function.iterate_zero_apply] at hYX
  have hV : genV P A C = qgtPlus P A C + qgtMinus P A C := by
    simp only [qgtPlus, qgtMinus]; peirce_nf hP
  refine ⟨?_, comm_idempotencyDefect_iterate (qgtPlus P A C) n⟩
  rw [hV, add_mul, hYX, add_zero]

/-- At every defect depth `n`, the two-state chart sandwich maps the lower-cycle
iterate `δ^[n](Q₋)` to `-genV P A C * δ^[n](Q₊)`. -/
theorem chart_two_state_qgtMinus_defect_iterate (n : ℕ) :
    (P - conePlus P A) * idempotencyDefect^[n] (qgtMinus P A C) *
        (P + coneMinus P C) =
      -(genV P A C * idempotencyDefect^[n] (qgtPlus P A C)) := by
  have hPL : P * idempotencyDefect^[n] (qgtMinus P A C) = 0 := by
    have h := qgtMinus_defect_iterates_left hP A C n
    simpa [sub_mul, one_mul, sub_eq_self] using h
  have hInter := (qgt_defect_iterates_cone_relations hP A C n).2.2.1
  have hNP : conePlus P A * P = 0 := conePlus_mul_P hP A
  have hLeft : (P - conePlus P A) * idempotencyDefect^[n] (qgtMinus P A C) =
      -(idempotencyDefect^[n] (qgtPlus P A C) * conePlus P A) := by
    rw [sub_mul, hPL, hInter, zero_sub]
  rw [hLeft]
  calc
    -(idempotencyDefect^[n] (qgtPlus P A C) * conePlus P A) *
        (P + coneMinus P C) =
      -(idempotencyDefect^[n] (qgtPlus P A C) *
          (conePlus P A * P + conePlus P A * coneMinus P C)) := by
      noncomm_ring
    _ = -(idempotencyDefect^[n] (qgtPlus P A C) * qgtPlus P A C) := by
      rw [hNP, zero_add]; rfl
    _ = -(genV P A C * idempotencyDefect^[n] (qgtPlus P A C)) := by
      rw [← (genV_mul_qgtPlus_defect_iterate hP A C n).2,
        ← (genV_mul_qgtPlus_defect_iterate hP A C n).1]

/-- All-depth local chart sandwiches on the symmetric defect tower `δ^[n](V)`
and chiral defect tower `qgtDefectDiff P A C n`. The final identity compares
the two chart outputs. No identification with the transcript's separate
`P_{k+1}` / `P_{C,k}` tower sandwich is asserted here. -/
theorem chart_two_state_genV_and_qgtDefectDiff_iterates (n : ℕ) :
    (P - conePlus P A) * idempotencyDefect^[n] (genV P A C) *
        (P + coneMinus P C) =
      (1 - genV P A C) * idempotencyDefect^[n] (qgtPlus P A C) ∧
    (P - conePlus P A) * qgtDefectDiff P A C n *
        (P + coneMinus P C) =
      (1 + genV P A C) * idempotencyDefect^[n] (qgtPlus P A C) ∧
    (P - conePlus P A) * qgtDefectDiff P A C n *
        (P + coneMinus P C) -
      (1 - genV P A C) * idempotencyDefect^[n] (qgtPlus P A C) =
        (2 : ℤ) • (genV P A C * idempotencyDefect^[n] (qgtPlus P A C)) := by
  have hX := chart_two_state_qgtPlus_defect_iterate hP A C n
  have hY := chart_two_state_qgtMinus_defect_iterate hP A C n
  have hV : (P - conePlus P A) * idempotencyDefect^[n] (genV P A C) *
      (P + coneMinus P C) =
      (1 - genV P A C) * idempotencyDefect^[n] (qgtPlus P A C) := by
    rw [genV_defect_iterates_cycle_split hP A C n]
    calc
      (P - conePlus P A) *
          (idempotencyDefect^[n] (qgtPlus P A C) +
            idempotencyDefect^[n] (qgtMinus P A C)) *
          (P + coneMinus P C) =
        (P - conePlus P A) * idempotencyDefect^[n] (qgtPlus P A C) *
            (P + coneMinus P C) +
          (P - conePlus P A) * idempotencyDefect^[n] (qgtMinus P A C) *
            (P + coneMinus P C) := by noncomm_ring
      _ = idempotencyDefect^[n] (qgtPlus P A C) -
          genV P A C * idempotencyDefect^[n] (qgtPlus P A C) := by
        rw [hX, hY]; abel
      _ = (1 - genV P A C) * idempotencyDefect^[n] (qgtPlus P A C) := by
        noncomm_ring
  have hSig : (P - conePlus P A) * qgtDefectDiff P A C n *
      (P + coneMinus P C) =
      (1 + genV P A C) * idempotencyDefect^[n] (qgtPlus P A C) := by
    unfold qgtDefectDiff
    calc
      (P - conePlus P A) *
          (idempotencyDefect^[n] (qgtPlus P A C) -
            idempotencyDefect^[n] (qgtMinus P A C)) *
          (P + coneMinus P C) =
        (P - conePlus P A) * idempotencyDefect^[n] (qgtPlus P A C) *
            (P + coneMinus P C) -
          (P - conePlus P A) * idempotencyDefect^[n] (qgtMinus P A C) *
            (P + coneMinus P C) := by noncomm_ring
      _ = idempotencyDefect^[n] (qgtPlus P A C) +
          genV P A C * idempotencyDefect^[n] (qgtPlus P A C) := by
        rw [hX, hY]; abel
      _ = (1 + genV P A C) * idempotencyDefect^[n] (qgtPlus P A C) := by
        noncomm_ring
  refine ⟨hV, hSig, ?_⟩
  rw [hSig]
  noncomm_ring

/-- At every defect depth `n`, the symmetric defect iterate `δ^[n](V)` commutes
with the right chart factor `P + coneMinus P C`. -/
theorem genV_defect_iterate_comm_chart_right (n : ℕ) :
    idempotencyDefect^[n] (genV P A C) * (P + coneMinus P C) =
      (P + coneMinus P C) * idempotencyDefect^[n] (genV P A C) := by
  have hPcomm : idempotencyDefect^[n] (genV P A C) * P =
      P * idempotencyDefect^[n] (genV P A C) := by
    rw [genV_defect_iterates_right_projection hP A C n,
      genV_defect_iterates_left_projection hP A C n]
  have hNcomm : idempotencyDefect^[n] (genV P A C) * coneMinus P C =
      coneMinus P C * idempotencyDefect^[n] (genV P A C) := by
    rw [genV_defect_iterates_cycle_split hP A C n]
    exact (sub_eq_zero.mp (qgt_defect_iterate_sum_commutes_with_cones hP A C n).2).symm
  rw [mul_add, add_mul, hPcomm, hNcomm]

/-- At every defect depth `n`, the two-state chart sandwich annihilates the
odd symmetric mode `Φ δ^[n](V)` and maps `J δ^[n](V)` to `2 V δ^[n](Q₊)` (`A80`). -/
theorem chart_two_state_odd_defect_iterates (n : ℕ) :
    (P - conePlus P A) *
        (genPhi P A C * idempotencyDefect^[n] (genV P A C)) *
        (P + coneMinus P C) = 0 ∧
    (P - conePlus P A) *
        (genJ P A C * idempotencyDefect^[n] (genV P A C)) *
        (P + coneMinus P C) =
      (2 : ℤ) • (genV P A C * idempotencyDefect^[n] (qgtPlus P A C)) := by
  have hComm := genV_defect_iterate_comm_chart_right hP A C n
  have hPhi0 := (chart_two_state_generator_sandwich hP A C).1
  have hJ0 := (chart_two_state_generator_sandwich hP A C).2.1
  constructor
  · calc
      (P - conePlus P A) *
          (genPhi P A C * idempotencyDefect^[n] (genV P A C)) *
          (P + coneMinus P C) =
        (P - conePlus P A) * genPhi P A C *
          (idempotencyDefect^[n] (genV P A C) * (P + coneMinus P C)) := by
        simp only [mul_assoc]
      _ = ((P - conePlus P A) * genPhi P A C * (P + coneMinus P C)) *
          idempotencyDefect^[n] (genV P A C) := by
        rw [hComm]; simp only [mul_assoc]
      _ = 0 := by rw [hPhi0, zero_mul]
  · have hQ : (conePlus P A * coneMinus P C) * idempotencyDefect^[n] (genV P A C) =
        genV P A C * idempotencyDefect^[n] (qgtPlus P A C) := by
      have hQP : conePlus P A * coneMinus P C = qgtPlus P A C * P := by
        simp only [qgtPlus]; peirce_nf hP
      rw [hQP, mul_assoc, genV_defect_iterates_left_projection hP A C n,
        ← (genV_mul_qgtPlus_defect_iterate hP A C n).1]
    calc
      (P - conePlus P A) *
          (genJ P A C * idempotencyDefect^[n] (genV P A C)) *
          (P + coneMinus P C) =
        (P - conePlus P A) * genJ P A C *
          (idempotencyDefect^[n] (genV P A C) * (P + coneMinus P C)) := by
        simp only [mul_assoc]
      _ = ((P - conePlus P A) * genJ P A C * (P + coneMinus P C)) *
          idempotencyDefect^[n] (genV P A C) := by
        rw [hComm]; simp only [mul_assoc]
      _ = ((2 : ℤ) • (conePlus P A * coneMinus P C)) *
          idempotencyDefect^[n] (genV P A C) := by
        rw [hJ0]
      _ = (2 : ℤ) • ((conePlus P A * coneMinus P C) *
          idempotencyDefect^[n] (genV P A C)) := by
        rw [smul_mul_assoc]
      _ = (2 : ℤ) • (genV P A C * idempotencyDefect^[n] (qgtPlus P A C)) := by
        rw [hQ]

variable [StarRing B] (hPs : star P = P) (X : B)
include hPs

/-- The complementary ideal pairing with the left cycle in its actual order. -/
theorem complementary_twisted_ideal_pairing :
    (invS P * star (X * (1 - P)) * invS P) * (X * (1 - P)) =
      peirce00 P (star X) * peirce00 P X -
        coneMinus P (star X) * conePlus P X := by
  simp only [invS, star_mul, star_sub, star_one, hPs,
    peirce00, coneMinus, conePlus]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
