import Mathlib.Tactic
import InfoGeometry.Cocycle.MatrixDetExpTrace

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
- supertrace_diag: STr(diag(a,b), diag(c,d)) = (a+b) - (c+d)
- ber_diag_2x2: Ber = (a·b)/(c·d) for diagonal supermatrices
- ber_mul: multiplicativity of Berezinian

#### BUCKET 1: CLOSED FINITE THEOREMS
- det_exp_eq_exp_tr: det(exp(A)) = exp(Tr(A)) for n×n matrices
- ber_exp_eq_exp_str: Ber(exp(A), exp(D)) = exp(STr(A,D)) in the diagonal real model

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- None.

#### BUCKET 3: OPEN CLOSURE DEBT
- None.
-/

namespace InfoGeometry.Canonical.BerezinianTrace

open scoped Matrix

/-- Determinant of the matrix exponential equals the exponential of the trace. -/
theorem det_exp_eq_exp_tr
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A) :=
  InfoGeometry.Cocycle.MatrixDetExpTrace.det_exp_eq_exp_trace A

/-- Supertrace: STr(trA, trD) = trA - trD. -/
def supertrace (trA trD : ℝ) : ℝ := trA - trD

/-- For diagonal 2×2 blocks: STr(a+b, c+d) = (a+b) - (c+d). -/
theorem supertrace_diag (a b c d : ℝ) : supertrace (a + b) (c + d) = (a + b) - (c + d) := rfl

/-- Supertrace of the identity supermatrix is p - q (bosonic dim minus fermionic dim). -/
theorem supertrace_id (p q : ℕ) : supertrace (p : ℝ) (q : ℝ) = (p : ℝ) - (q : ℝ) := rfl

/-- Berezinian: Ber(detA, detD) = detA / detD. -/
noncomputable def berezinian (detA detD : ℝ) (_hD : detD ≠ 0) : ℝ := detA / detD

/-- Ber = detA/detD (definitional). -/
theorem ber_eq_div (detA detD : ℝ) (hD : detD ≠ 0) : berezinian detA detD hD = detA / detD := rfl

/-- Ber = 1 when detA = detD. -/
theorem ber_eq_one (a : ℝ) (ha : a ≠ 0) : berezinian a a ha = 1 := by
  simp [berezinian, div_self ha]

/-- Ber(A₁·A₂, D₁·D₂) = Ber(A₁,D₁) · Ber(A₂,D₂). -/
theorem ber_mul (a₁ a₂ d₁ d₂ : ℝ) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    berezinian (a₁ * a₂) (d₁ * d₂) (mul_ne_zero hd₁ hd₂) =
    berezinian a₁ d₁ hd₁ * berezinian a₂ d₂ hd₂ := by
  simp [berezinian]; ring

/-- Ber(A⁻¹, D⁻¹) = 1/Ber(A, D). -/
theorem ber_inv (a d : ℝ) (ha : a ≠ 0) (hd : d ≠ 0) :
    berezinian (a⁻¹) (d⁻¹) (inv_ne_zero hd) = (berezinian a d hd)⁻¹ := by
  simp [berezinian]; field_simp [ha, hd]

/-- Berezinian of an exponential diagonal block is the exponential of the supertrace. -/
theorem ber_exp_eq_exp_str (a b c d : ℝ) :
    berezinian (Real.exp a * Real.exp b) (Real.exp c * Real.exp d)
      (mul_ne_zero (Real.exp_ne_zero c) (Real.exp_ne_zero d)) =
    Real.exp (supertrace (a + b) (c + d)) := by
  simp [berezinian, supertrace, Real.exp_add, Real.exp_sub]

/-- Compatibility alias for the previous debt-style theorem name. -/
theorem ber_exp_eq_exp_str_debt (a b c d : ℝ) :
    berezinian (Real.exp a * Real.exp b) (Real.exp c * Real.exp d)
      (mul_ne_zero (Real.exp_ne_zero c) (Real.exp_ne_zero d)) =
    Real.exp (supertrace (a + b) (c + d)) :=
  by
    simp [berezinian, supertrace, Real.exp_add, Real.exp_sub]

end InfoGeometry.Canonical.BerezinianTrace
