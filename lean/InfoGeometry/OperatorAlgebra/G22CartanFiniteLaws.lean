import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Cartan split laws for the doubled `5 + 5` carrier

This module is the Lean twin of `tools/sympy/g22_cartan_finite_laws.py`.

It proves explicit finite block laws for a doubled five-coordinate integer carrier:
* the off-diagonal block swap is skew for the split `(5,5)` bilinear form;
* the grading involution makes that block odd;
* the diagonal grading core is involutive/even.

Honesty boundary: this does **not** prove a full `PO(5,5)`, `Pin(5,5)`,
Super-TKK, `SU(3)`, or `Aut(𝕆_s)=G₂(2)` classification theorem.  It is the
kernel-checked finite block layer those larger statements would have to consume.
-/

namespace InfoGeometry.OperatorAlgebra.G22CartanFiniteLaws

abbrev Sector := Fin 2
abbrev Color5 := Fin 5
abbrev Doubled5 := Sector × Color5
abbrev Vec10 := Doubled5 → ℤ

/-- Off-diagonal block swap on the doubled `5 + 5` carrier. -/
def boost (v : Vec10) : Vec10 := fun p =>
  match p.1 with
  | 0 => v (1, p.2)
  | 1 => v (0, p.2)

/-- Grading-sign involution: positive on the first five slots, negative on the second five. -/
def theta (v : Vec10) : Vec10 := fun p =>
  match p.1 with
  | 0 => v p
  | 1 => -v p

/-- Split `(5,5)` bilinear pairing in coordinates. -/
def etaPair (u v : Vec10) : ℤ :=
  ∑ i : Color5,
    (u ((0 : Sector), i) * v ((0 : Sector), i) -
      u ((1 : Sector), i) * v ((1 : Sector), i))

/-- The off-diagonal block swap is skew for the split `(5,5)` form. -/
theorem boost_so55_skew (u v : Vec10) :
    etaPair (boost u) v + etaPair u (boost v) = 0 := by
  simp [etaPair, boost, Fin.sum_univ_five]

/-- The grading involution makes the off-diagonal block swap odd. -/
theorem theta_boost_theta_odd (v : Vec10) : theta (boost (theta v)) = -boost v := by
  funext p
  rcases p with ⟨s, i⟩
  fin_cases s <;> simp [theta, boost]

/-- The grading-sign core is an involution. -/
theorem theta_involutive (v : Vec10) : theta (theta v) = v := by
  funext p
  rcases p with ⟨s, i⟩
  fin_cases s <;> simp [theta]

/-- The grading-sign core is fixed by conjugation with itself. -/
theorem theta_core_even (v : Vec10) : theta (theta (theta v)) = theta v := by
  rw [theta_involutive]

/-- Closed finite packet for the Cartan split block laws. -/
theorem cartan_finite_laws_packet :
    (∀ u v : Vec10, etaPair (boost u) v + etaPair u (boost v) = 0) ∧
      (∀ v : Vec10, theta (boost (theta v)) = -boost v) ∧
      (∀ v : Vec10, theta (theta v) = v) ∧
      (∀ v : Vec10, theta (theta (theta v)) = theta v) := by
  exact ⟨boost_so55_skew, theta_boost_theta_odd, theta_involutive, theta_core_even⟩

end InfoGeometry.OperatorAlgebra.G22CartanFiniteLaws
