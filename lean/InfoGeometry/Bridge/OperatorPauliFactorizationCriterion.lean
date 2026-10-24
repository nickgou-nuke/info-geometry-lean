/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Bridge.OperatorPauliFactorizationDefect

/-! Exact conditions for the ordered Pauli scalar channel. No division by two
and no pairwise commutation assumption on all four entries is needed. -/

namespace InfoGeometry.Bridge.OperatorPauliFactorizationDefect

variable {A : Type*} [Ring A]

theorem factorizationDefect_eq_zero_iff (t z u v : A) :
    factorizationDefect t z u v = 0 ↔
      Commute t z ∧ Commute u v ∧ Commute u (t + z) ∧ Commute v (t - z) := by
  have hc (x y : A) : commutator x y = 0 ↔ Commute x y := sub_eq_zero
  have ha : commutator u t + commutator u z = commutator u (t + z) := by
    unfold commutator; noncomm_ring
  have hs : commutator v t - commutator v z = commutator v (t - z) := by
    unfold commutator; noncomm_ring
  constructor
  · intro h
    have h00 := congrArg (fun M : OperatorBlock A => M 0 0) h
    have h01 := congrArg (fun M : OperatorBlock A => M 0 1) h
    have h10 := congrArg (fun M : OperatorBlock A => M 1 0) h
    have h11 := congrArg (fun M : OperatorBlock A => M 1 1) h
    simp [factorizationDefect] at h00 h01 h10 h11
    have htz := ((hc z t).mp h00).symm
    have htz0 := (hc t z).mpr htz
    rw [htz0, zero_add] at h11
    exact ⟨htz, (hc u v).mp h11, (hc _ _).mp (ha ▸ h01),
      (hc _ _).mp (hs ▸ h10)⟩
  · rintro ⟨htz, huv, hu, hv⟩
    have hzt0 := (hc z t).mpr htz.symm
    have htz0 := (hc t z).mpr htz
    have huv0 := (hc u v).mpr huv
    have hu0 := (hc u (t + z)).mpr hu
    have hv0 := (hc v (t - z)).mpr hv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [factorizationDefect, ha, hs, hzt0, htz0, huv0, hu0, hv0]

theorem operator_factorization_iff (t z u v : A) :
    operatorSigma t z u v * operatorBarSigma t z u v =
      diagonalBlock (orderedQuadratic t z u v) ↔
      Commute t z ∧ Commute u v ∧ Commute u (t + z) ∧ Commute v (t - z) := by
  rw [operator_factorization_with_defect, add_eq_left, factorizationDefect_eq_zero_iff]

end InfoGeometry.Bridge.OperatorPauliFactorizationDefect
