import Mathlib

section TemperleyLieb

variable {F : Type*} [Field F]
variable {A_alg : Type*} [Ring A_alg] [Algebra F A_alg]

/-- The Kauffman bracket loop value. -/
def tlLoop (A : F) : F := -A ^ 2 - (A⁻¹) ^ 2

/-- Temperley-Lieb relations for generators `e i`. -/
class TemperleyLieb (d : F) (e : ℕ → A_alg) : Prop where
  e_sq : ∀ i, e i * e i = algebraMap F A_alg d * e i
  e_comm : ∀ i j, i + 1 < j ∨ j + 1 < i → e i * e j = e j * e i
  e_adj : ∀ i j, (i = j + 1 ∨ j = i + 1) → e i * e j * e i = e i

variable (A : F) (e : ℕ → A_alg)
variable [TemperleyLieb (tlLoop A) e]

/-- Jones generator candidate attached to a Temperley-Lieb generator. -/
def σ (i : ℕ) : A_alg := algebraMap F A_alg A + algebraMap F A_alg A⁻¹ * e i

/-- Formal inverse candidate for the Jones generator. -/
def σInv (i : ℕ) : A_alg := algebraMap F A_alg A⁻¹ + algebraMap F A_alg A * e i

theorem square_reduction (i : ℕ) :
    e i * e i = algebraMap F A_alg (tlLoop A) * e i :=
  TemperleyLieb.e_sq i

theorem far_commutation (q : F) [TemperleyLieb (tlLoop q) e]
    (i j : ℕ) (h : i + 1 < j ∨ j + 1 < i) :
    e i * e j = e j * e i :=
  TemperleyLieb.e_comm (d := tlLoop q) (e := e) i j h

theorem adjacent_reduction (q : F) [TemperleyLieb (tlLoop q) e]
    (i j : ℕ) (h : i = j + 1 ∨ j = i + 1) :
    e i * e j * e i = e i :=
  TemperleyLieb.e_adj (d := tlLoop q) (e := e) i j h

theorem loop_value_neg : tlLoop A = -(A ^ 2 + A⁻¹ ^ 2) := by
  unfold tlLoop
  ring

end TemperleyLieb
