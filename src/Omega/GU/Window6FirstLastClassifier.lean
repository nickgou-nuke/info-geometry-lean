import Mathlib.Tactic

namespace Omega.GU

/-- Binary magma terms labelled by variables in `Fin n`. -/
inductive window6_first_last_classifier_term (n : Nat) : Type where
  | window6_first_last_classifier_var : Fin n → window6_first_last_classifier_term n
  | window6_first_last_classifier_mul :
      window6_first_last_classifier_term n →
      window6_first_last_classifier_term n →
      window6_first_last_classifier_term n

/-- The first variable encountered by the left-to-right traversal of a binary term. -/
def window6_first_last_classifier_first {n : Nat} :
    window6_first_last_classifier_term n → Fin n
  | .window6_first_last_classifier_var i => i
  | .window6_first_last_classifier_mul u _ => window6_first_last_classifier_first u

/-- The last variable encountered by the left-to-right traversal of a binary term. -/
def window6_first_last_classifier_last {n : Nat} :
    window6_first_last_classifier_term n → Fin n
  | .window6_first_last_classifier_var i => i
  | .window6_first_last_classifier_mul _ v => window6_first_last_classifier_last v

/-- Evaluation in the CRT rectangular-band model `(a₃, a₇) ⋄ (b₃, b₇) = (a₃, b₇)`. -/
def window6_first_last_classifier_eval {n : Nat} (ρ : Fin n → Fin 3 × Fin 7) :
    window6_first_last_classifier_term n → Fin 3 × Fin 7
  | .window6_first_last_classifier_var i => ρ i
  | .window6_first_last_classifier_mul u v =>
      ((window6_first_last_classifier_eval ρ u).1,
        (window6_first_last_classifier_eval ρ v).2)

/-- In the window-6 rectangular-band model, every term is classified by its first and last
variables: the `Fin 3` coordinate comes from the first variable and the `Fin 7` coordinate from the
last variable.
    lem:window6-first-last-classifier -/
theorem paper_window6_first_last_classifier {n : ℕ}
    (t : window6_first_last_classifier_term n) (ρ : Fin n → Fin 3 × Fin 7) :
    window6_first_last_classifier_eval ρ t =
      ((ρ (window6_first_last_classifier_first t)).1,
        (ρ (window6_first_last_classifier_last t)).2) := by
  induction t with
  | window6_first_last_classifier_var i =>
      rfl
  | window6_first_last_classifier_mul u v hu hv =>
      simp [window6_first_last_classifier_eval, window6_first_last_classifier_first,
        window6_first_last_classifier_last, hu, hv]

/-- The rectangular-band operation is not commutative: the first output
coordinate remembers the left input, so two inputs with distinct `Fin 3`
coordinates give an explicit counterexample. -/
theorem window6_rectangular_band_not_commutative :
    ∃ ρ : Fin 2 → Fin 3 × Fin 7,
      ∃ x y : window6_first_last_classifier_term 2,
        window6_first_last_classifier_eval ρ
            (.window6_first_last_classifier_mul x y) ≠
          window6_first_last_classifier_eval ρ
            (.window6_first_last_classifier_mul y x) := by
  refine ⟨fun i => if i = (0 : Fin 2) then (0, 0) else (1, 0),
    .window6_first_last_classifier_var 0,
    .window6_first_last_classifier_var 1, ?_⟩
  decide

/-- The rectangular-band operation also fails the unrestricted equation
`x ⋄ y = z ⋄ w`; distinct first coordinates of `x` and `z` witness failure. -/
theorem window6_rectangular_band_not_unrestricted_product_equality :
    ∃ ρ : Fin 4 → Fin 3 × Fin 7,
      ∃ x y z w : window6_first_last_classifier_term 4,
        window6_first_last_classifier_eval ρ
            (.window6_first_last_classifier_mul x y) ≠
          window6_first_last_classifier_eval ρ
            (.window6_first_last_classifier_mul z w) := by
  refine ⟨fun i => if i = (2 : Fin 4) then (1, 0) else (0, 0),
    .window6_first_last_classifier_var 0,
    .window6_first_last_classifier_var 1,
    .window6_first_last_classifier_var 2,
    .window6_first_last_classifier_var 3, ?_⟩
  decide

end Omega.GU
