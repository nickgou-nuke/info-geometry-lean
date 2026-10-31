/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Defect-iterate braiding between the two Peirce cycles

The upper and lower cycle defect towers retain their six ordered cone
relations. Their sum therefore commutes with each cone. No commutativity of
the ambient ring is assumed.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

theorem defect_iterates_left_annihilated {a x : B} (h : a * x = 0) (n : ℕ) :
    a * idempotencyDefect^[n] x = 0 := by
  induction n with
  | zero => exact h
  | succ n ih =>
      simp only [Function.iterate_succ_apply']
      unfold idempotencyDefect
      calc
        a * (idempotencyDefect^[n] x * idempotencyDefect^[n] x -
            idempotencyDefect^[n] x) =
            (a * idempotencyDefect^[n] x) * idempotencyDefect^[n] x -
              a * idempotencyDefect^[n] x := by noncomm_ring
        _ = 0 := by rw [ih]; simp

theorem defect_iterates_right_annihilated {a x : B} (h : x * a = 0) (n : ℕ) :
    idempotencyDefect^[n] x * a = 0 := by
  induction n with
  | zero => exact h
  | succ n ih =>
      simp only [Function.iterate_succ_apply']
      unfold idempotencyDefect
      calc
        (idempotencyDefect^[n] x * idempotencyDefect^[n] x -
            idempotencyDefect^[n] x) * a =
            idempotencyDefect^[n] x * (idempotencyDefect^[n] x * a) -
              idempotencyDefect^[n] x * a := by noncomm_ring
        _ = 0 := by rw [ih]; simp

/-- Every iterate of `idempotencyDefect` on `x` commutes with `x`. -/
theorem comm_idempotencyDefect_iterate (x : B) (n : ℕ) :
    x * idempotencyDefect^[n] x = idempotencyDefect^[n] x * x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply']
      unfold idempotencyDefect
      calc
        x * (idempotencyDefect^[n] x * idempotencyDefect^[n] x -
            idempotencyDefect^[n] x) =
          (x * idempotencyDefect^[n] x) * idempotencyDefect^[n] x -
            x * idempotencyDefect^[n] x := by noncomm_ring
        _ = (idempotencyDefect^[n] x * x) * idempotencyDefect^[n] x -
            idempotencyDefect^[n] x * x := by rw [ih]
        _ = idempotencyDefect^[n] x * (x * idempotencyDefect^[n] x) -
            idempotencyDefect^[n] x * x := by noncomm_ring
        _ = idempotencyDefect^[n] x * (idempotencyDefect^[n] x * x) -
            idempotencyDefect^[n] x * x := by rw [ih]
        _ = (idempotencyDefect^[n] x * idempotencyDefect^[n] x -
            idempotencyDefect^[n] x) * x := by noncomm_ring

/-- The chiral difference `Σ_n = δ^[n](Q₊) - δ^[n](Q₋)` of the two iterated
Peirce cycles at defect depth `n`. -/
def qgtDefectDiff (P A C : B) (n : ℕ) : B :=
  idempotencyDefect^[n] (qgtPlus P A C) -
    idempotencyDefect^[n] (qgtMinus P A C)

variable {P : B} (hP : P * P = P) (A C : B)
include hP

theorem qgt_cycles_cone_relations :
    conePlus P A * qgtPlus P A C = 0 ∧
    qgtMinus P A C * conePlus P A = 0 ∧
    conePlus P A * qgtMinus P A C = qgtPlus P A C * conePlus P A ∧
    coneMinus P C * qgtMinus P A C = 0 ∧
    qgtPlus P A C * coneMinus P C = 0 ∧
    coneMinus P C * qgtPlus P A C = qgtMinus P A C * coneMinus P C := by
  simp only [qgtPlus, qgtMinus]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

theorem qgt_defect_iterates_cone_relations (n : ℕ) :
    conePlus P A * idempotencyDefect^[n] (qgtPlus P A C) = 0 ∧
    idempotencyDefect^[n] (qgtMinus P A C) * conePlus P A = 0 ∧
    conePlus P A * idempotencyDefect^[n] (qgtMinus P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) * conePlus P A ∧
    coneMinus P C * idempotencyDefect^[n] (qgtMinus P A C) = 0 ∧
    idempotencyDefect^[n] (qgtPlus P A C) * coneMinus P C = 0 ∧
    coneMinus P C * idempotencyDefect^[n] (qgtPlus P A C) =
      idempotencyDefect^[n] (qgtMinus P A C) * coneMinus P C := by
  have h := qgt_cycles_cone_relations hP A C
  refine ⟨defect_iterates_left_annihilated h.1 n,
    defect_iterates_right_annihilated h.2.1 n,
    (idempotencyDefect_iterates_intertwines h.2.2.1.symm n).symm,
    defect_iterates_left_annihilated h.2.2.2.1 n,
    defect_iterates_right_annihilated h.2.2.2.2.1 n,
    (idempotencyDefect_iterates_intertwines h.2.2.2.2.2.symm n).symm⟩

theorem qgt_defect_iterate_sum_commutes_with_cones (n : ℕ) :
    comm (conePlus P A)
        (idempotencyDefect^[n] (qgtPlus P A C) +
          idempotencyDefect^[n] (qgtMinus P A C)) = 0 ∧
    comm (coneMinus P C)
        (idempotencyDefect^[n] (qgtPlus P A C) +
          idempotencyDefect^[n] (qgtMinus P A C)) = 0 := by
  rcases qgt_defect_iterates_cone_relations hP A C n with
    ⟨hax, hxb, hay, hby, hxb', hbx⟩
  constructor
  · unfold comm
    apply sub_eq_zero.mpr
    rw [mul_add, add_mul, hax, hay, hxb]
    abel
  · unfold comm
    apply sub_eq_zero.mpr
    rw [mul_add, add_mul, hbx, hby, hxb']
    abel

theorem qgt_defect_iterate_sum_commutes_with_generators (n : ℕ) :
    comm (genPhi P A C)
        (idempotencyDefect^[n] (qgtPlus P A C) +
          idempotencyDefect^[n] (qgtMinus P A C)) = 0 ∧
    comm (genJ P A C)
        (idempotencyDefect^[n] (qgtPlus P A C) +
          idempotencyDefect^[n] (qgtMinus P A C)) = 0 := by
  rcases qgt_defect_iterate_sum_commutes_with_cones hP A C n with
    ⟨hPlus, hMinus⟩
  have hPlus' : conePlus P A *
      (idempotencyDefect^[n] (qgtPlus P A C) +
        idempotencyDefect^[n] (qgtMinus P A C)) =
      (idempotencyDefect^[n] (qgtPlus P A C) +
        idempotencyDefect^[n] (qgtMinus P A C)) * conePlus P A :=
    sub_eq_zero.mp hPlus
  have hMinus' : coneMinus P C *
      (idempotencyDefect^[n] (qgtPlus P A C) +
        idempotencyDefect^[n] (qgtMinus P A C)) =
      (idempotencyDefect^[n] (qgtPlus P A C) +
        idempotencyDefect^[n] (qgtMinus P A C)) * coneMinus P C :=
    sub_eq_zero.mp hMinus
  constructor
  · unfold comm genPhi
    rw [add_mul, hPlus', hMinus', mul_add, sub_self]
  · unfold comm genJ
    rw [sub_mul, hPlus', hMinus', mul_sub, sub_self]

omit hP in
/-- At defect depth zero, `qgtDefectDiff` is the chiral generator `genSig`. -/
theorem qgtDefectDiff_zero :
    qgtDefectDiff P A C 0 = genSig P A C := by
  simp only [qgtDefectDiff, Function.iterate_zero_apply, qgtPlus, qgtMinus,
    genSig, comm]

/-- The chiral iterated cycle difference `qgtDefectDiff P A C n` anticommutes
with both Peirce cones at every defect depth `n` (`A66`). -/
theorem qgtDefectDiff_anticomm_cones (n : ℕ) :
    anticomm (conePlus P A) (qgtDefectDiff P A C n) = 0 ∧
    anticomm (coneMinus P C) (qgtDefectDiff P A C n) = 0 := by
  rcases qgt_defect_iterates_cone_relations hP A C n with
    ⟨hax, hxb, hay, hby, hxb', hbx⟩
  constructor
  · unfold anticomm qgtDefectDiff
    rw [mul_sub, sub_mul, hax, hay, hxb]
    abel
  · unfold anticomm qgtDefectDiff
    rw [mul_sub, sub_mul, hbx, hby, hxb']
    abel

/-- The chiral iterated cycle difference `qgtDefectDiff P A C n` anticommutes
with both odd generators `Φ` and `J` at every defect depth `n` (`A66`). -/
theorem qgtDefectDiff_anticomm_generators (n : ℕ) :
    anticomm (genPhi P A C) (qgtDefectDiff P A C n) = 0 ∧
    anticomm (genJ P A C) (qgtDefectDiff P A C n) = 0 := by
  rcases qgtDefectDiff_anticomm_cones hP A C n with ⟨hPlus, hMinus⟩
  unfold anticomm at hPlus hMinus ⊢
  constructor
  · unfold genPhi
    calc
      (conePlus P A + coneMinus P C) * qgtDefectDiff P A C n +
          qgtDefectDiff P A C n * (conePlus P A + coneMinus P C) =
        (conePlus P A * qgtDefectDiff P A C n +
            qgtDefectDiff P A C n * conePlus P A) +
          (coneMinus P C * qgtDefectDiff P A C n +
            qgtDefectDiff P A C n * coneMinus P C) := by noncomm_ring
      _ = 0 := by rw [hPlus, hMinus, add_zero]
  · unfold genJ
    calc
      (conePlus P A - coneMinus P C) * qgtDefectDiff P A C n +
          qgtDefectDiff P A C n * (conePlus P A - coneMinus P C) =
        (conePlus P A * qgtDefectDiff P A C n +
            qgtDefectDiff P A C n * conePlus P A) -
          (coneMinus P C * qgtDefectDiff P A C n +
            qgtDefectDiff P A C n * coneMinus P C) := by noncomm_ring
      _ = 0 := by rw [hPlus, hMinus, sub_zero]

/-- Iterated upper and lower Peirce cycles annihilate each other across
arbitrary pairs of defect depths `(n, m)` (`A75`). -/
theorem qgt_defect_iterates_cross_orthogonal (n m : ℕ) :
    idempotencyDefect^[n] (qgtPlus P A C) *
        idempotencyDefect^[m] (qgtMinus P A C) = 0 ∧
    idempotencyDefect^[n] (qgtMinus P A C) *
        idempotencyDefect^[m] (qgtPlus P A C) = 0 := by
  have hP1 : P * (1 - P) = 0 := by noncomm_ring [hP]
  have h1P : (1 - P) * P = 0 := by noncomm_ring [hP]
  constructor
  · rw [← qgtPlus_defect_iterates_right hP A C n,
      ← qgtMinus_defect_iterates_left hP A C m]
    calc
      (idempotencyDefect^[n] (qgtPlus P A C) * P) *
          ((1 - P) * idempotencyDefect^[m] (qgtMinus P A C)) =
        idempotencyDefect^[n] (qgtPlus P A C) * (P * (1 - P)) *
          idempotencyDefect^[m] (qgtMinus P A C) := by noncomm_ring
      _ = 0 := by rw [hP1, mul_zero, zero_mul]
  · rw [← qgtMinus_defect_iterates_right hP A C n,
      ← qgtPlus_defect_iterates_left hP A C m]
    calc
      (idempotencyDefect^[n] (qgtMinus P A C) * (1 - P)) *
          (P * idempotencyDefect^[m] (qgtPlus P A C)) =
        idempotencyDefect^[n] (qgtMinus P A C) * ((1 - P) * P) *
          idempotencyDefect^[m] (qgtPlus P A C) := by noncomm_ring
      _ = 0 := by rw [h1P, mul_zero, zero_mul]

/-- Multi-depth graded product table for the symmetric defect tower `δ^[n](V)`
and chiral defect tower `qgtDefectDiff P A C n` (`A75`). -/
theorem qgt_defect_iterates_graded_products (n m : ℕ) :
    idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[m] (genV P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtPlus P A C) +
        idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtMinus P A C) ∧
    qgtDefectDiff P A C n * qgtDefectDiff P A C m =
      idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[m] (genV P A C) ∧
    qgtDefectDiff P A C n * idempotencyDefect^[m] (genV P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtPlus P A C) -
        idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtMinus P A C) ∧
    idempotencyDefect^[n] (genV P A C) * qgtDefectDiff P A C m =
      idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtPlus P A C) -
        idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtMinus P A C) := by
  rcases qgt_defect_iterates_cross_orthogonal hP A C n m with ⟨hXY, hYX⟩
  have hVn := genV_defect_iterates_cycle_split hP A C n
  have hVm := genV_defect_iterates_cycle_split hP A C m
  have hVV : idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[m] (genV P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtPlus P A C) +
        idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtMinus P A C) := by
    rw [hVn, hVm]
    calc
      (idempotencyDefect^[n] (qgtPlus P A C) + idempotencyDefect^[n] (qgtMinus P A C)) *
          (idempotencyDefect^[m] (qgtPlus P A C) + idempotencyDefect^[m] (qgtMinus P A C)) =
        idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtPlus P A C) +
          idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtMinus P A C) +
          idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtPlus P A C) +
          idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtMinus P A C) := by
        noncomm_ring
      _ = idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtPlus P A C) +
          idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtMinus P A C) := by
        rw [hXY, hYX]; abel
  refine ⟨hVV, ?_, ?_, ?_⟩
  · rw [hVV]
    unfold qgtDefectDiff
    calc
      (idempotencyDefect^[n] (qgtPlus P A C) - idempotencyDefect^[n] (qgtMinus P A C)) *
          (idempotencyDefect^[m] (qgtPlus P A C) - idempotencyDefect^[m] (qgtMinus P A C)) =
        idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtPlus P A C) -
          idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtMinus P A C) -
          idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtPlus P A C) +
          idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtMinus P A C) := by
        noncomm_ring
      _ = idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtPlus P A C) +
          idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtMinus P A C) := by
        rw [hXY, hYX]; abel
  · rw [hVm]
    unfold qgtDefectDiff
    calc
      (idempotencyDefect^[n] (qgtPlus P A C) - idempotencyDefect^[n] (qgtMinus P A C)) *
          (idempotencyDefect^[m] (qgtPlus P A C) + idempotencyDefect^[m] (qgtMinus P A C)) =
        idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtPlus P A C) +
          idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtMinus P A C) -
          idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtPlus P A C) -
          idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtMinus P A C) := by
        noncomm_ring
      _ = idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtPlus P A C) -
          idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtMinus P A C) := by
        rw [hXY, hYX]; abel
  · rw [hVn]
    unfold qgtDefectDiff
    calc
      (idempotencyDefect^[n] (qgtPlus P A C) + idempotencyDefect^[n] (qgtMinus P A C)) *
          (idempotencyDefect^[m] (qgtPlus P A C) - idempotencyDefect^[m] (qgtMinus P A C)) =
        idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtPlus P A C) -
          idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtMinus P A C) +
          idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtPlus P A C) -
          idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtMinus P A C) := by
        noncomm_ring
      _ = idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[m] (qgtPlus P A C) -
          idempotencyDefect^[n] (qgtMinus P A C) * idempotencyDefect^[m] (qgtMinus P A C) := by
        rw [hXY, hYX]; abel

/-- Grading action of `invS P = 2P - 1` and `parityConj` invariance on the
iterated Peirce cycles at all defect depths `n` (transcript labels A74/A75).
This theorem defines no Hodge-star operator. -/
theorem qgt_defect_iterates_invS_and_parity (n : ℕ) :
    invS P * idempotencyDefect^[n] (qgtPlus P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) ∧
    invS P * idempotencyDefect^[n] (qgtMinus P A C) =
      -idempotencyDefect^[n] (qgtMinus P A C) ∧
    invS P * idempotencyDefect^[n] (genV P A C) =
      qgtDefectDiff P A C n ∧
    invS P * qgtDefectDiff P A C n =
      idempotencyDefect^[n] (genV P A C) ∧
    parityConj P (idempotencyDefect^[n] (genV P A C)) =
      idempotencyDefect^[n] (genV P A C) ∧
    parityConj P (qgtDefectDiff P A C n) =
      qgtDefectDiff P A C n := by
  have hXL := qgtPlus_defect_iterates_left hP A C n
  have hXR := qgtPlus_defect_iterates_right hP A C n
  have hYL : P * idempotencyDefect^[n] (qgtMinus P A C) = 0 := by
    have h := qgtMinus_defect_iterates_left hP A C n
    simpa [sub_mul, one_mul, sub_eq_self] using h
  have hYR : idempotencyDefect^[n] (qgtMinus P A C) * P = 0 := by
    have h := qgtMinus_defect_iterates_right hP A C n
    simpa [mul_sub, mul_one, sub_eq_self] using h
  have hSX : invS P * idempotencyDefect^[n] (qgtPlus P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) := by
    unfold invS
    calc
      (P - (1 - P)) * idempotencyDefect^[n] (qgtPlus P A C) =
        P * idempotencyDefect^[n] (qgtPlus P A C) -
          idempotencyDefect^[n] (qgtPlus P A C) +
          P * idempotencyDefect^[n] (qgtPlus P A C) := by noncomm_ring
      _ = idempotencyDefect^[n] (qgtPlus P A C) := by rw [hXL]; abel
  have hXS : idempotencyDefect^[n] (qgtPlus P A C) * invS P =
      idempotencyDefect^[n] (qgtPlus P A C) := by
    unfold invS
    calc
      idempotencyDefect^[n] (qgtPlus P A C) * (P - (1 - P)) =
        idempotencyDefect^[n] (qgtPlus P A C) * P -
          idempotencyDefect^[n] (qgtPlus P A C) +
          idempotencyDefect^[n] (qgtPlus P A C) * P := by noncomm_ring
      _ = idempotencyDefect^[n] (qgtPlus P A C) := by rw [hXR]; abel
  have hSY : invS P * idempotencyDefect^[n] (qgtMinus P A C) =
      -idempotencyDefect^[n] (qgtMinus P A C) := by
    unfold invS
    calc
      (P - (1 - P)) * idempotencyDefect^[n] (qgtMinus P A C) =
        P * idempotencyDefect^[n] (qgtMinus P A C) -
          idempotencyDefect^[n] (qgtMinus P A C) +
          P * idempotencyDefect^[n] (qgtMinus P A C) := by noncomm_ring
      _ = -idempotencyDefect^[n] (qgtMinus P A C) := by rw [hYL]; abel
  have hYS : idempotencyDefect^[n] (qgtMinus P A C) * invS P =
      -idempotencyDefect^[n] (qgtMinus P A C) := by
    unfold invS
    calc
      idempotencyDefect^[n] (qgtMinus P A C) * (P - (1 - P)) =
        idempotencyDefect^[n] (qgtMinus P A C) * P -
          idempotencyDefect^[n] (qgtMinus P A C) +
          idempotencyDefect^[n] (qgtMinus P A C) * P := by noncomm_ring
      _ = -idempotencyDefect^[n] (qgtMinus P A C) := by rw [hYR]; abel
  have hSV : invS P * idempotencyDefect^[n] (genV P A C) =
      qgtDefectDiff P A C n := by
    rw [genV_defect_iterates_cycle_split hP A C n, mul_add, hSX, hSY]
    unfold qgtDefectDiff
    abel
  have hSSig : invS P * qgtDefectDiff P A C n =
      idempotencyDefect^[n] (genV P A C) := by
    unfold qgtDefectDiff
    rw [mul_sub, hSX, hSY, sub_neg_eq_add,
      ← genV_defect_iterates_cycle_split hP A C n]
  refine ⟨hSX, hSY, hSV, hSSig, ?_, ?_⟩
  · unfold parityConj
    rw [hSV]
    unfold qgtDefectDiff
    rw [sub_mul, hXS, hYS, sub_neg_eq_add,
      ← genV_defect_iterates_cycle_split hP A C n]
  · unfold parityConj
    rw [hSSig, genV_defect_iterates_cycle_split hP A C n, add_mul, hXS, hYS]
    unfold qgtDefectDiff
    abel

/-- Chiral parity action of `genSig` and `genV` on single-sheet and combined
defect iterates at every depth `n` (transcript labels A68/A69/A75). -/
theorem qgt_defect_iterates_chiral_eigenvalues (n : ℕ) :
    genSig P A C * idempotencyDefect^[n] (qgtPlus P A C) =
      genV P A C * idempotencyDefect^[n] (qgtPlus P A C) ∧
    genSig P A C * idempotencyDefect^[n] (qgtMinus P A C) =
      -(genV P A C * idempotencyDefect^[n] (qgtMinus P A C)) ∧
    (genV P A C - genSig P A C) * idempotencyDefect^[n] (qgtPlus P A C) = 0 ∧
    (genV P A C + genSig P A C) * idempotencyDefect^[n] (qgtMinus P A C) = 0 ∧
    genSig P A C * qgtDefectDiff P A C n =
      genV P A C * idempotencyDefect^[n] (genV P A C) ∧
    genSig P A C * idempotencyDefect^[n] (genV P A C) =
      genV P A C * qgtDefectDiff P A C n := by
  have hOrth := qgt_defect_iterates_cross_orthogonal hP A C 0 n
  simp only [Function.iterate_zero, id_eq] at hOrth
  rcases hOrth with ⟨hXY, hYX⟩
  have hSig : genSig P A C = qgtPlus P A C - qgtMinus P A C := by
    simp only [genSig, comm, qgtPlus, qgtMinus]
  have hV : genV P A C = qgtPlus P A C + qgtMinus P A C := by
    simp only [genV, anticomm, qgtPlus, qgtMinus]
  have hSigX : genSig P A C * idempotencyDefect^[n] (qgtPlus P A C) =
      genV P A C * idempotencyDefect^[n] (qgtPlus P A C) := by
    rw [hSig, hV, sub_mul, add_mul, hYX, sub_zero, add_zero]
  have hSigY : genSig P A C * idempotencyDefect^[n] (qgtMinus P A C) =
      -(genV P A C * idempotencyDefect^[n] (qgtMinus P A C)) := by
    rw [hSig, hV, sub_mul, add_mul, hXY, zero_sub, zero_add]
  refine ⟨hSigX, hSigY, ?_, ?_, ?_, ?_⟩
  · rw [sub_mul, hSigX, sub_self]
  · rw [add_mul, hSigY, add_neg_cancel]
  · unfold qgtDefectDiff
    rw [mul_sub, hSigX, hSigY, sub_neg_eq_add, ← mul_add,
      ← genV_defect_iterates_cycle_split hP A C n]
  · rw [genV_defect_iterates_cycle_split hP A C n, mul_add, hSigX, hSigY]
    unfold qgtDefectDiff
    rw [mul_sub]
    abel

/-- Iterated `sandwichSame` action on the off-diagonal cones and `genPhi`,
isolating the idempotency defect `idempotencyDefect (genV P A C)` (transcript
labels A70/A72). -/
theorem sandwichSame_multipass_idempotencyDefect :
    sandwichSame P A C (coneMinus P C) -
        sandwichSame P A C (sandwichSame P A C (conePlus P A)) =
      -(idempotencyDefect (genV P A C) * conePlus P A) ∧
    sandwichSame P A C (conePlus P A) -
        sandwichSame P A C (sandwichSame P A C (coneMinus P C)) =
      -(idempotencyDefect (genV P A C) * coneMinus P C) ∧
    sandwichSame P A C (genPhi P A C) -
        sandwichSame P A C (sandwichSame P A C (genPhi P A C)) =
      -(idempotencyDefect (genV P A C) * genPhi P A C) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (unfold sandwichSame idempotencyDefect; peirce_nf hP)

/-- Cross-sandwich `sandwichCross P A C` sheet-swapping on `δ^[n](Q₊)` and
`δ^[n](Q₋)` and opposite eigenvalues `± genV P A C` on `δ^[n](V)` and
`qgtDefectDiff P A C n` at every defect depth `n` (transcript labels A66–A68). -/
theorem qgt_defect_iterates_sandwichCross (n : ℕ) :
    sandwichCross P A C (idempotencyDefect^[n] (qgtPlus P A C)) =
      genV P A C * idempotencyDefect^[n] (qgtMinus P A C) ∧
    sandwichCross P A C (idempotencyDefect^[n] (qgtMinus P A C)) =
      genV P A C * idempotencyDefect^[n] (qgtPlus P A C) ∧
    sandwichCross P A C (idempotencyDefect^[n] (genV P A C)) =
      genV P A C * idempotencyDefect^[n] (genV P A C) ∧
    sandwichCross P A C (qgtDefectDiff P A C n) =
      -(genV P A C * qgtDefectDiff P A C n) := by
  rcases qgt_defect_iterates_cone_relations hP A C n with ⟨h1, _h2, h6, h3, _h4, h5⟩
  have hOrth := qgt_defect_iterates_cross_orthogonal hP A C 0 n
  simp only [Function.iterate_zero, id_eq] at hOrth
  rcases hOrth with ⟨hXY, hYX⟩
  have hV : genV P A C = conePlus P A * coneMinus P C + coneMinus P C * conePlus P A := by
    simp only [genV, anticomm]
  have hQp : qgtPlus P A C = conePlus P A * coneMinus P C := rfl
  have hQm : qgtMinus P A C = coneMinus P C * conePlus P A := rfl
  have hSX : sandwichCross P A C (idempotencyDefect^[n] (qgtPlus P A C)) =
      genV P A C * idempotencyDefect^[n] (qgtMinus P A C) := by
    unfold sandwichCross
    rw [h1, zero_mul, zero_add, h5]
    calc
      idempotencyDefect^[n] (qgtMinus P A C) * coneMinus P C * conePlus P A =
        (coneMinus P C * idempotencyDefect^[n] (qgtPlus P A C)) * conePlus P A := by rw [← h5]
      _ = coneMinus P C * (idempotencyDefect^[n] (qgtPlus P A C) * conePlus P A) := by noncomm_ring
      _ = coneMinus P C * (conePlus P A * idempotencyDefect^[n] (qgtMinus P A C)) := by rw [← h6]
      _ = qgtMinus P A C * idempotencyDefect^[n] (qgtMinus P A C) := by
        rw [hQm, mul_assoc]
      _ = (qgtPlus P A C + qgtMinus P A C) * idempotencyDefect^[n] (qgtMinus P A C) := by
        rw [add_mul, hXY, zero_add]
      _ = genV P A C * idempotencyDefect^[n] (qgtMinus P A C) := by
        rw [hV, hQp, hQm]
  have hSY : sandwichCross P A C (idempotencyDefect^[n] (qgtMinus P A C)) =
      genV P A C * idempotencyDefect^[n] (qgtPlus P A C) := by
    unfold sandwichCross
    rw [h3, zero_mul, add_zero]
    calc
      conePlus P A * idempotencyDefect^[n] (qgtMinus P A C) * coneMinus P C =
        conePlus P A * (idempotencyDefect^[n] (qgtMinus P A C) * coneMinus P C) := by noncomm_ring
      _ = conePlus P A * (coneMinus P C * idempotencyDefect^[n] (qgtPlus P A C)) := by rw [← h5]
      _ = qgtPlus P A C * idempotencyDefect^[n] (qgtPlus P A C) := by
        rw [hQp, mul_assoc]
      _ = (qgtPlus P A C + qgtMinus P A C) * idempotencyDefect^[n] (qgtPlus P A C) := by
        rw [add_mul, hYX, add_zero]
      _ = genV P A C * idempotencyDefect^[n] (qgtPlus P A C) := by
        rw [hV, hQp, hQm]
  refine ⟨hSX, hSY, ?_, ?_⟩
  · rw [genV_defect_iterates_cycle_split hP A C n]
    calc
      sandwichCross P A C
          (idempotencyDefect^[n] (qgtPlus P A C) + idempotencyDefect^[n] (qgtMinus P A C)) =
        sandwichCross P A C (idempotencyDefect^[n] (qgtPlus P A C)) +
          sandwichCross P A C (idempotencyDefect^[n] (qgtMinus P A C)) := by
        unfold sandwichCross; noncomm_ring
      _ = genV P A C *
          (idempotencyDefect^[n] (qgtPlus P A C) + idempotencyDefect^[n] (qgtMinus P A C)) := by
        rw [hSX, hSY, mul_add, add_comm]
  · unfold qgtDefectDiff
    calc
      sandwichCross P A C
          (idempotencyDefect^[n] (qgtPlus P A C) - idempotencyDefect^[n] (qgtMinus P A C)) =
        sandwichCross P A C (idempotencyDefect^[n] (qgtPlus P A C)) -
          sandwichCross P A C (idempotencyDefect^[n] (qgtMinus P A C)) := by
        unfold sandwichCross; noncomm_ring
      _ = -(genV P A C *
          (idempotencyDefect^[n] (qgtPlus P A C) - idempotencyDefect^[n] (qgtMinus P A C))) := by
        rw [hSX, hSY, mul_sub]; abel

/-- Square-zero property of the defect-scaled cones `N_± δ^[n](V)`, their
handshake sum `V δ^[n](V)`, and the cubic relations for `Φ δ^[n](V)` and
`J δ^[n](V)` at every defect depth `n` (transcript label A70). -/
theorem qgt_defect_iterates_cone_echo_and_cubic (n : ℕ) :
    (conePlus P A * idempotencyDefect^[n] (genV P A C)) *
        (conePlus P A * idempotencyDefect^[n] (genV P A C)) = 0 ∧
    (coneMinus P C * idempotencyDefect^[n] (genV P A C)) *
        (coneMinus P C * idempotencyDefect^[n] (genV P A C)) = 0 ∧
    (conePlus P A * idempotencyDefect^[n] (genV P A C)) * coneMinus P C +
        (coneMinus P C * idempotencyDefect^[n] (genV P A C)) * conePlus P A =
      genV P A C * idempotencyDefect^[n] (genV P A C) ∧
    (genPhi P A C * idempotencyDefect^[n] (genV P A C)) *
        (genPhi P A C * idempotencyDefect^[n] (genV P A C)) *
        (genPhi P A C * idempotencyDefect^[n] (genV P A C)) =
      (genV P A C * genPhi P A C) *
        (idempotencyDefect^[n] (genV P A C) *
          idempotencyDefect^[n] (genV P A C) *
          idempotencyDefect^[n] (genV P A C)) ∧
    (genJ P A C * idempotencyDefect^[n] (genV P A C)) *
        (genJ P A C * idempotencyDefect^[n] (genV P A C)) *
        (genJ P A C * idempotencyDefect^[n] (genV P A C)) =
      -((genV P A C * genJ P A C) *
        (idempotencyDefect^[n] (genV P A C) *
          idempotencyDefect^[n] (genV P A C) *
          idempotencyDefect^[n] (genV P A C))) := by
  have hSplit := genV_defect_iterates_cycle_split hP A C n
  have hCones := qgt_defect_iterate_sum_commutes_with_cones hP A C n
  have hGens := qgt_defect_iterate_sum_commutes_with_generators hP A C n
  have hNp : conePlus P A * idempotencyDefect^[n] (genV P A C) =
      idempotencyDefect^[n] (genV P A C) * conePlus P A := by
    rw [hSplit]; exact sub_eq_zero.mp hCones.1
  have hNm : coneMinus P C * idempotencyDefect^[n] (genV P A C) =
      idempotencyDefect^[n] (genV P A C) * coneMinus P C := by
    rw [hSplit]; exact sub_eq_zero.mp hCones.2
  have hPhi : genPhi P A C * idempotencyDefect^[n] (genV P A C) =
      idempotencyDefect^[n] (genV P A C) * genPhi P A C := by
    rw [hSplit]; exact sub_eq_zero.mp hGens.1
  have hJ : genJ P A C * idempotencyDefect^[n] (genV P A C) =
      idempotencyDefect^[n] (genV P A C) * genJ P A C := by
    rw [hSplit]; exact sub_eq_zero.mp hGens.2
  have hNpSq : conePlus P A * conePlus P A = 0 := conePlus_mul_conePlus hP A A
  have hNmSq : coneMinus P C * coneMinus P C = 0 := coneMinus_mul_coneMinus hP C C
  have hPhiSq : genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
  have hJSq : genJ P A C * genJ P A C = -genV P A C := by peirce_nf hP
  have hPhiV2 : (genPhi P A C * idempotencyDefect^[n] (genV P A C)) *
      (genPhi P A C * idempotencyDefect^[n] (genV P A C)) =
      genV P A C * (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C)) := by
    calc
      (genPhi P A C * idempotencyDefect^[n] (genV P A C)) *
          (genPhi P A C * idempotencyDefect^[n] (genV P A C)) =
        genPhi P A C * (idempotencyDefect^[n] (genV P A C) * genPhi P A C) *
          idempotencyDefect^[n] (genV P A C) := by noncomm_ring
      _ = genPhi P A C * (genPhi P A C * idempotencyDefect^[n] (genV P A C)) *
          idempotencyDefect^[n] (genV P A C) := by rw [← hPhi]
      _ = (genPhi P A C * genPhi P A C) *
          (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C)) := by
        noncomm_ring
      _ = genV P A C *
          (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C)) := by
        rw [hPhiSq]
  have hJV2 : (genJ P A C * idempotencyDefect^[n] (genV P A C)) *
      (genJ P A C * idempotencyDefect^[n] (genV P A C)) =
      -(genV P A C * (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C))) := by
    calc
      (genJ P A C * idempotencyDefect^[n] (genV P A C)) *
          (genJ P A C * idempotencyDefect^[n] (genV P A C)) =
        genJ P A C * (idempotencyDefect^[n] (genV P A C) * genJ P A C) *
          idempotencyDefect^[n] (genV P A C) := by noncomm_ring
      _ = genJ P A C * (genJ P A C * idempotencyDefect^[n] (genV P A C)) *
          idempotencyDefect^[n] (genV P A C) := by rw [← hJ]
      _ = (genJ P A C * genJ P A C) *
          (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C)) := by
        noncomm_ring
      _ = -(genV P A C *
          (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C))) := by
        rw [hJSq]; noncomm_ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      (conePlus P A * idempotencyDefect^[n] (genV P A C)) *
          (conePlus P A * idempotencyDefect^[n] (genV P A C)) =
        conePlus P A * (idempotencyDefect^[n] (genV P A C) * conePlus P A) *
          idempotencyDefect^[n] (genV P A C) := by noncomm_ring
      _ = conePlus P A * (conePlus P A * idempotencyDefect^[n] (genV P A C)) *
          idempotencyDefect^[n] (genV P A C) := by rw [← hNp]
      _ = (conePlus P A * conePlus P A) *
          (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C)) := by
        noncomm_ring
      _ = 0 := by rw [hNpSq, zero_mul]
  · calc
      (coneMinus P C * idempotencyDefect^[n] (genV P A C)) *
          (coneMinus P C * idempotencyDefect^[n] (genV P A C)) =
        coneMinus P C * (idempotencyDefect^[n] (genV P A C) * coneMinus P C) *
          idempotencyDefect^[n] (genV P A C) := by noncomm_ring
      _ = coneMinus P C * (coneMinus P C * idempotencyDefect^[n] (genV P A C)) *
          idempotencyDefect^[n] (genV P A C) := by rw [← hNm]
      _ = (coneMinus P C * coneMinus P C) *
          (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C)) := by
        noncomm_ring
      _ = 0 := by rw [hNmSq, zero_mul]
  · calc
      (conePlus P A * idempotencyDefect^[n] (genV P A C)) * coneMinus P C +
          (coneMinus P C * idempotencyDefect^[n] (genV P A C)) * conePlus P A =
        conePlus P A * (idempotencyDefect^[n] (genV P A C) * coneMinus P C) +
          coneMinus P C * (idempotencyDefect^[n] (genV P A C) * conePlus P A) := by
        noncomm_ring
      _ = conePlus P A * (coneMinus P C * idempotencyDefect^[n] (genV P A C)) +
          coneMinus P C * (conePlus P A * idempotencyDefect^[n] (genV P A C)) := by
        rw [← hNm, ← hNp]
      _ = genV P A C * idempotencyDefect^[n] (genV P A C) := by
        simp only [genV, anticomm]; noncomm_ring
  · rw [hPhiV2]
    calc
      genV P A C * (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C)) *
          (genPhi P A C * idempotencyDefect^[n] (genV P A C)) =
        genV P A C * idempotencyDefect^[n] (genV P A C) *
          (idempotencyDefect^[n] (genV P A C) * genPhi P A C) *
          idempotencyDefect^[n] (genV P A C) := by noncomm_ring
      _ = genV P A C * idempotencyDefect^[n] (genV P A C) *
          (genPhi P A C * idempotencyDefect^[n] (genV P A C)) *
          idempotencyDefect^[n] (genV P A C) := by rw [← hPhi]
      _ = genV P A C * (idempotencyDefect^[n] (genV P A C) * genPhi P A C) *
          (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C)) := by
        noncomm_ring
      _ = genV P A C * (genPhi P A C * idempotencyDefect^[n] (genV P A C)) *
          (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C)) := by
        rw [← hPhi]
      _ = (genV P A C * genPhi P A C) *
          (idempotencyDefect^[n] (genV P A C) *
            idempotencyDefect^[n] (genV P A C) *
            idempotencyDefect^[n] (genV P A C)) := by noncomm_ring
  · rw [hJV2]
    calc
      -(genV P A C * (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C))) *
          (genJ P A C * idempotencyDefect^[n] (genV P A C)) =
        -(genV P A C * idempotencyDefect^[n] (genV P A C) *
          (idempotencyDefect^[n] (genV P A C) * genJ P A C) *
          idempotencyDefect^[n] (genV P A C)) := by noncomm_ring
      _ = -(genV P A C * idempotencyDefect^[n] (genV P A C) *
          (genJ P A C * idempotencyDefect^[n] (genV P A C)) *
          idempotencyDefect^[n] (genV P A C)) := by rw [← hJ]
      _ = -(genV P A C * (idempotencyDefect^[n] (genV P A C) * genJ P A C) *
          (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C))) := by
        noncomm_ring
      _ = -(genV P A C * (genJ P A C * idempotencyDefect^[n] (genV P A C)) *
          (idempotencyDefect^[n] (genV P A C) * idempotencyDefect^[n] (genV P A C))) := by
        rw [← hJ]
      _ = -((genV P A C * genJ P A C) *
          (idempotencyDefect^[n] (genV P A C) *
            idempotencyDefect^[n] (genV P A C) *
            idempotencyDefect^[n] (genV P A C))) := by noncomm_ring

end InfoGeometry.OperatorAlgebra.PeirceSpine
