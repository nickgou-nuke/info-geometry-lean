import Mathlib.Tactic
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.Canonical.ChiralHodgeCone

open Matrix Complex

/-!
# Chiral Hodge Cone

Finite algebraic trace cancellation for a chiral Hodge grading acting on a
sewn state.

The cone/natural-cone geometry supplies the state `ρ`; it is not needed for the
pure trace cancellation.  The algebraic mechanism is:

* an involutive chiral Hodge operator `γ`, `γ * γ = 1`;
* an orientation-reversing sewing law `γ * ρ * γ = -ρ`;
* cyclicity of the finite matrix trace.

From these, `trace (γ * ρ) = 0`.

#### BUCKET 1: CLOSED FINITE THEOREMS

[Fully verified lemmas with zero remaining dependencies or open goals. Fully
checked by the kernel.]

* `trace_rotate3`
* `chiralTrace_eq_neg_of_sewn`
* `chiralTrace_vanishes_of_sewn`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported
verified premises.]

* `chiralTrace_eq_neg_of_sewn`
* `chiralTrace_vanishes_of_sewn`

#### BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, interfaces, fields,
witnesses, certificates, or renamed placeholders.]

* Construct the infinite-dimensional standard-form natural cone.
* Prove that the selected boundary state belongs to that natural cone.
* Prove the orientation-reversing sewing law for the concrete Klein/V₄
  boundary action rather than supplying it as an explicit property.
-/

/-- Finite complex matrix carrier. -/
@[rep_depth operator]
abbrev Mat (n : ℕ) : Type :=
  Matrix (Fin n) (Fin n) ℂ

/-- Chiral trace/anomaly functional associated to a grading `γ`. -/
@[rep_depth operator]
def chiralTrace {n : ℕ} (γ ρ : Mat n) : ℂ :=
  Matrix.trace (γ * ρ)

/-- The finite chiral Hodge star is an involutive grading. -/
@[rep_depth operator]
def IsChiralHodgeStar {n : ℕ} (γ : Mat n) : Prop :=
  γ * γ = 1

/-- Orientation-reversing sewing at the non-orientable throat. -/
@[rep_depth operator]
def IsSewnAtThroat {n : ℕ} (γ ρ : Mat n) : Prop :=
  γ * ρ * γ = -ρ

/-- Three-factor cyclic rotation for the finite matrix trace. -/
@[rep_depth operator]
theorem trace_rotate3 {n : ℕ} (A B C : Mat n) :
    Matrix.trace (A * B * C) = Matrix.trace (B * C * A) := by
  calc
    Matrix.trace (A * B * C) = Matrix.trace ((A * B) * C) := by simp [mul_assoc]
    _ = Matrix.trace (C * (A * B)) := Matrix.trace_mul_comm (A * B) C
    _ = Matrix.trace (C * A * B) := by simp [mul_assoc]
    _ = Matrix.trace (B * (C * A)) := (Matrix.trace_mul_comm B (C * A)).symm
    _ = Matrix.trace (B * C * A) := by simp [mul_assoc]

/-- Anticommutation with the grading is already sufficient for cancellation. -/
@[rep_depth operator]
theorem chiralTrace_vanishes_of_anticommute {n : ℕ} (γ ρ : Mat n)
    (hanti : γ * ρ = -(ρ * γ)) :
    chiralTrace γ ρ = 0 := by
  unfold chiralTrace
  have hneg : Matrix.trace (γ * ρ) = -Matrix.trace (γ * ρ) := by
    calc
      Matrix.trace (γ * ρ) = Matrix.trace (-(ρ * γ)) := by
        rw [hanti]
      _ = -Matrix.trace (ρ * γ) := by simp
      _ = -Matrix.trace (γ * ρ) := by rw [Matrix.trace_mul_comm]
  have htwo : (2 : ℂ) * Matrix.trace (γ * ρ) = 0 := by
    calc
      (2 : ℂ) * Matrix.trace (γ * ρ) =
          Matrix.trace (γ * ρ) + Matrix.trace (γ * ρ) := by ring
      _ = Matrix.trace (γ * ρ) + (-Matrix.trace (γ * ρ)) := by
        nth_rw 2 [hneg]
      _ = 0 := by simp
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/--
The sewn state has chiral trace equal to its own negative.
-/
@[rep_depth operator]
theorem chiralTrace_eq_neg_of_sewn {n : ℕ} (γ ρ : Mat n)
    (hγ : IsChiralHodgeStar γ)
    (hsewn : IsSewnAtThroat γ ρ) :
    chiralTrace γ ρ = -chiralTrace γ ρ := by
  unfold IsChiralHodgeStar at hγ
  unfold IsSewnAtThroat at hsewn
  unfold chiralTrace
  calc
    Matrix.trace (γ * ρ)
        = Matrix.trace ((γ * ρ) * 1) := by simp
    _ = Matrix.trace ((γ * ρ) * (γ * γ)) := by rw [hγ]
    _ = Matrix.trace ((γ * ρ * γ) * γ) := by simp [mul_assoc]
    _ = Matrix.trace ((-ρ) * γ) := by rw [hsewn]
    _ = -Matrix.trace (ρ * γ) := by simp
    _ = -Matrix.trace (γ * ρ) := by rw [Matrix.trace_mul_comm ρ γ]

/--
Finite chiral-Hodge anomaly cancellation from involutivity and sewing.
-/
@[rep_depth operator]
theorem chiralTrace_vanishes_of_sewn {n : ℕ} (γ ρ : Mat n)
    (hγ : IsChiralHodgeStar γ)
    (hsewn : IsSewnAtThroat γ ρ) :
    chiralTrace γ ρ = 0 := by
  have hneg := chiralTrace_eq_neg_of_sewn γ ρ hγ hsewn
  have htwo :
      (2 : ℂ) * chiralTrace γ ρ = 0 := by
    calc
      (2 : ℂ) * chiralTrace γ ρ
          = chiralTrace γ ρ + chiralTrace γ ρ := by ring
      _ = chiralTrace γ ρ + (-chiralTrace γ ρ) := by nth_rw 2 [hneg]
      _ = 0 := by simp
  have htwo_ne : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp htwo).resolve_left htwo_ne

end InfoGeometry.Canonical.ChiralHodgeCone
