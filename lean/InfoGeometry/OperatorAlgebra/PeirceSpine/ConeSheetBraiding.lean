/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower

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

end InfoGeometry.OperatorAlgebra.PeirceSpine
