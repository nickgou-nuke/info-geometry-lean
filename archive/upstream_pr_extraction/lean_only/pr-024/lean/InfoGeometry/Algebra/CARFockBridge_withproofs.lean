import InfoGeometry.Algebra.FiniteSingleModeCAR
import InfoGeometry.Arithmetic.PrimonFockTraceFinite

/-!
# CAR/Fock bridge with checked finite proofs

This file replaces the earlier false spectral shortcut for many-mode number
operators.  Distinct fermion number operators commute; they are not mutually
orthogonal on the full Fock space because simultaneous occupation exists.  The
checked finite trace factorization lives in `PrimonFockTraceFinite`, and the
one-mode CAR representation lives in `FiniteSingleModeCAR`.
-/

noncomputable section

namespace InfoGeometry.Algebra.CARFockBridgeWithProofs

open InfoGeometry.Algebra.FiniteSingleModeCAR
open InfoGeometry.Arithmetic.PrimonFockTraceFinite

/-- Concrete one-mode CAR packet: nilpotence plus `{c,c†}=1`. -/
theorem one_mode_car_packet :
    opComp ann ann = (fun _ : OneModeVec => 0) ∧
    opComp cre cre = (fun _ : OneModeVec => 0) ∧
    opAdd (opComp ann cre) (opComp cre ann) = idOp := by
  exact ⟨ann_nilpotent, cre_nilpotent, ann_cre_anticommutator⟩

/-- Concrete one-mode number-projector packet. -/
theorem one_mode_number_packet :
    opComp num num = num ∧
    (∀ ψ occ, num ψ occ = if occ then ψ true else 0) := by
  exact ⟨num_idempotent, num_apply⟩

/-- Finite many-mode diagonal Fock trace theorem, imported as the correct spectral fact. -/
theorem finite_many_mode_trace_packet (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) :
    fockTraceExp n ε β = ∏ i : Fin n, (1 + localBoltzmann (ε i) β) := by
  exact fockTraceExp_eq_product n ε β

end InfoGeometry.Algebra.CARFockBridgeWithProofs
