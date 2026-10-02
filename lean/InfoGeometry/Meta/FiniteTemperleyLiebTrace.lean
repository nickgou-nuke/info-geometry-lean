import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Finite normalized traces and a Temperley--Lieb pair

This file formalizes the finite matrix layer behind the normalized-trace
discussion. A normalized trace is defined on a finite matrix algebra over
ℚ; it sends the identity to 1 and is cyclic. The explicit two-dimensional
pair below gives a finite witness for

e₀² = e₀, e₁² = e₁, e₀ e₁ e₀ = (1/2) • e₀,
e₁ e₀ e₁ = (1/2) • e₁,

and both projectors have normalized trace 1/2. Thus this is the
δ² = 2 Temperley--Lieb parameter.

The file makes no claim about a C*-completion, a II₁ factor, a Jones tower,
or a knot invariant. Those require additional analytic and categorical
constructions.
-/

namespace InfoGeometry.Meta.FiniteTemperleyLiebTrace

open Matrix

section NormalizedTrace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The finite normalized matrix trace over ℚ. -/
def normalizedTrace (A : Matrix ι ι ℚ) : ℚ :=
  (Fintype.card ι : ℚ)⁻¹ * Matrix.trace A

@[simp]
theorem normalizedTrace_one : normalizedTrace (1 : Matrix ι ι ℚ) = 1 := by
  unfold normalizedTrace
  rw [Matrix.trace_one]
  have hcard : (Fintype.card ι : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact inv_mul_cancel₀ hcard

theorem normalizedTrace_mul_cycle
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B C : Matrix ι ι ℚ) :
    normalizedTrace (A * B * C) = normalizedTrace (C * A * B) := by
  unfold normalizedTrace
  rw [Matrix.trace_mul_cycle]

end NormalizedTrace

section TwoStateWitness

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℚ

/-- The first rank-one Temperley--Lieb projector. -/
def e₀ : Mat2 := !![(1 : ℚ), 0; 0, 0]

/-- The projector onto the equal-weight state (1,1). -/
def e₁ : Mat2 := !![(1 / 2 : ℚ), 1 / 2; 1 / 2, 1 / 2]

theorem e₀_idempotent : e₀ * e₀ = e₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₀, Matrix.mul_apply, Fin.sum_univ_two]

theorem e₁_idempotent : e₁ * e₁ = e₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₁, Matrix.mul_apply, Fin.sum_univ_two]

/-- The adjacent Temperley--Lieb relation for the first projector. -/
theorem e₀_e₁_e₀ :
    e₀ * e₁ * e₀ = (1 / 2 : ℚ) • e₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₀, e₁, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two]

/-- The reflected adjacent Temperley--Lieb relation. -/
theorem e₁_e₀_e₁ :
    e₁ * e₀ * e₁ = (1 / 2 : ℚ) • e₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₀, e₁, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two]

@[simp]
theorem normalizedTrace_e₀ : normalizedTrace e₀ = (1 / 2 : ℚ) := by
  norm_num [normalizedTrace, e₀, Matrix.trace, Fin.sum_univ_two]

@[simp]
theorem normalizedTrace_e₁ : normalizedTrace e₁ = (1 / 2 : ℚ) := by
  norm_num [normalizedTrace, e₁, Matrix.trace, Fin.sum_univ_two]

/-- The squared Jones parameter for this finite witness. -/
def deltaSquared : ℚ := 2

@[simp]
theorem deltaSquared_ne_zero : deltaSquared ≠ 0 := by
  norm_num [deltaSquared]

theorem normalizedTrace_projector :
    normalizedTrace e₀ = deltaSquared⁻¹ ∧
      normalizedTrace e₁ = deltaSquared⁻¹ := by
  constructor <;> simp [deltaSquared]

theorem finite_temperley_lieb_packet :
    e₀ * e₀ = e₀ ∧
      e₁ * e₁ = e₁ ∧
      e₀ * e₁ * e₀ = (deltaSquared⁻¹ : ℚ) • e₀ ∧
      e₁ * e₀ * e₁ = (deltaSquared⁻¹ : ℚ) • e₁ ∧
      normalizedTrace e₀ = deltaSquared⁻¹ ∧
      normalizedTrace e₁ = deltaSquared⁻¹ := by
  rw [e₀_idempotent, e₁_idempotent, e₀_e₁_e₀, e₁_e₀_e₁,
    normalizedTrace_projector.1, normalizedTrace_projector.2]
  simp [deltaSquared]

end TwoStateWitness

end InfoGeometry.Meta.FiniteTemperleyLiebTrace
