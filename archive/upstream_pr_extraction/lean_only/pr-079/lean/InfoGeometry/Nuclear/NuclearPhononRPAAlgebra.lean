import Mathlib

/-!
# Finite RPA / quasiboson algebra boundary

Exact bosonic canonical commutation relations cannot be represented by finite
matrices over a characteristic-zero field: every matrix commutator has zero
trace, whereas the identity has nonzero trace.  This file records that boundary
concretely for the smallest `2 × 2` carrier and packages the RPA quasiboson
error as an explicit commutator defect rather than silently asserting an exact
boson algebra.
-/

noncomputable section

namespace InfoGeometry.Nuclear.NuclearPhononRPAAlgebra

abbrev Mode2 := Fin 2
abbrev Mat2 := Matrix Mode2 Mode2 ℝ

/-- Associative matrix commutator. -/
def commutator (A B : Mat2) : Mat2 := A * B - B * A

/-- Every concrete `2 × 2` matrix commutator has zero trace. -/
theorem trace_commutator_zero (A B : Mat2) :
    Matrix.trace (commutator A B) = 0 := by
  simp [commutator, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The `2 × 2` identity has trace two. -/
@[simp] theorem trace_one_eq_two :
    Matrix.trace (1 : Mat2) = 2 := by
  simp [Matrix.trace, Fin.sum_univ_two]

/-- No exact finite `2 × 2` representation of `[Q,Q†]=1` exists. -/
theorem no_exact_boson_ccr_2x2 :
    ¬ ∃ Q Qdag : Mat2, commutator Q Qdag = 1 := by
  rintro ⟨Q, Qdag, hccr⟩
  have htrace := congrArg Matrix.trace hccr
  rw [trace_commutator_zero, trace_one_eq_two] at htrace
  norm_num at htrace

/-- Explicit RPA/quasiboson packet.  `defect = 0` would be exact CCR; the
no-go theorem above shows that cannot occur on this finite carrier. -/
structure QuasibosonRPADatum where
  Q : Mat2
  Qdag : Mat2

/-- Deviation from the formal bosonic relation `[Q,Q†]=1`. -/
def QuasibosonRPADatum.defect (R : QuasibosonRPADatum) : Mat2 :=
  commutator R.Q R.Qdag - 1

/-- Vanishing defect is equivalent to exact CCR. -/
theorem QuasibosonRPADatum.defect_eq_zero_iff (R : QuasibosonRPADatum) :
    R.defect = 0 ↔ commutator R.Q R.Qdag = 1 := by
  unfold QuasibosonRPADatum.defect
  exact sub_eq_zero

/-- On the finite `2 × 2` carrier the RPA defect can never vanish exactly. -/
theorem QuasibosonRPADatum.defect_ne_zero (R : QuasibosonRPADatum) :
    R.defect ≠ 0 := by
  intro h
  have hccr := (R.defect_eq_zero_iff).mp h
  exact no_exact_boson_ccr_2x2 ⟨R.Q, R.Qdag, hccr⟩

end InfoGeometry.Nuclear.NuclearPhononRPAAlgebra

end noncomputable section
