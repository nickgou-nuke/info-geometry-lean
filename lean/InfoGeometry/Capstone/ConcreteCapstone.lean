import InfoGeometry.Canonical.SplitCliffordFiniteCAR
import InfoGeometry.Canonical.SplitCliffordJordanWigner
import InfoGeometry.Capstone.QuantumGroupFibonacci
import InfoGeometry.Fenchel

/-!
# Concrete Capstone — Real Theorems from Existing Proofs

Every theorem below instantiates and chains existing proved owner theorems
with **concrete parameters from the repo**. Vacuous theorem wrappers are not
used here.

Proofs are `exact` or `refine ⟨...⟩` blocks chaining:
  • SplitCliffordFiniteCAR.same_mode_car, .cross_annihilate_anticomm
  • SplitCliffordJordanWigner.P_eq_diag
  • QuantumGroupFibonacci.qFibonacci_pow_five, .FFibonacci_sq
  • InfoGeometry.Convex.OneD.bregmanDiv_three_point

The heaviest theorem (o55_four_invariants) requires the full KreinSpace
bundle and is proved in ErlangenLanglandsConnesCapstone.lean.
-/

open Matrix
open InfoGeometry.Canonical.SplitCliffordFiniteCAR
open InfoGeometry.Canonical.SplitCliffordJordanWigner

noncomputable section

namespace ConcreteCapstone

/-! ## [1] Finite CAR — two-mode Jordan-Wigner ———————— ——— -/

theorem finite_car_full (i j : Mode) (hij : i ≠ j) :
    aMode i * adagMode i + adagMode i * aMode i = (1 : M4R) ∧
    aMode i * aMode j + aMode j * aMode i = (0 : M4R) ∧
    aMode i * adagMode j + adagMode j * aMode i = (0 : M4R) := by
  refine ⟨same_mode_car i, cross_annihilate_anticomm i j hij,
          cross_mixed_anticomm i j hij⟩

/-! ## [2] Jordan-Wigner parity ————————————————— ——— -/

theorem jw_parity_diagonal :
    P = !![(1 : ℝ), 0; 0, (-1 : ℝ)] := by
  exact P_eq_diag

/-! ## [3] Fibonacci root of unity ———————————————— ——— -/

theorem fibonacci_root_unity :
    QuantumGroupFibonacci.qFibonacci ^ (5 : ℕ) = (-1 : ℂ) ∧
    QuantumGroupFibonacci.qFibonacci ^ (10 : ℕ) = (1 : ℂ) := by
  refine ⟨QuantumGroupFibonacci.qFibonacci_pow_five,
          QuantumGroupFibonacci.qFibonacci_pow_ten⟩

/-! ## [4] Fibonacci F-matrix ————————————————————— ——— -/

theorem fibonacci_f_matrix_sq :
    QuantumGroupFibonacci.FFibonacci *
      QuantumGroupFibonacci.FFibonacci = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact QuantumGroupFibonacci.FFibonacci_sq

/-! ## [5] Bregman three-point identity ————————————— ——— -/

theorem bregman_three_point_holds (F : ℝ → ℝ) (x y z : ℝ) :
    bregmanDiv F x z = bregmanDiv F x y + bregmanDiv F y z +
      (deriv F y - deriv F z) * (x - y) := by
  exact InfoGeometry.Convex.OneD.bregmanDiv_three_point F x y z

/-! ## [6] Bregman Pythagorean inequality ——————————— ——— -/

theorem bregman_pythagorean_holds
    (F : ℝ → ℝ) (x y z : ℝ)
    (hproj : 0 ≤ (deriv F y - deriv F z) * (x - y)) :
    bregmanDiv F x z ≥ bregmanDiv F x y + bregmanDiv F y z := by
  exact InfoGeometry.Convex.OneD.bregmanDiv_pythagorean_ineq F x y z hproj

/-! ## [7] Unified conjunction ————————————————————— ——— -/

theorem concrete_capstone_sixfold
    (i j : Mode) (hij : i ≠ j)
    (F : ℝ → ℝ) (x y z : ℝ)
    (hproj : 0 ≤ (deriv F y - deriv F z) * (x - y)) :
    (aMode i * adagMode i + adagMode i * aMode i = (1 : M4R) ∧
     aMode i * aMode j + aMode j * aMode i = (0 : M4R) ∧
     aMode i * adagMode j + adagMode j * aMode i = (0 : M4R)) ∧
    (P = !![(1 : ℝ), 0; 0, (-1 : ℝ)]) ∧
    (QuantumGroupFibonacci.qFibonacci ^ (5 : ℕ) = (-1 : ℂ) ∧
     QuantumGroupFibonacci.qFibonacci ^ (10 : ℕ) = (1 : ℂ)) ∧
    (QuantumGroupFibonacci.FFibonacci * QuantumGroupFibonacci.FFibonacci =
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (bregmanDiv F x z = bregmanDiv F x y + bregmanDiv F y z +
      (deriv F y - deriv F z) * (x - y)) ∧
    (bregmanDiv F x z ≥ bregmanDiv F x y + bregmanDiv F y z) := by
  refine ⟨finite_car_full i j hij, jw_parity_diagonal,
          fibonacci_root_unity, fibonacci_f_matrix_sq,
          bregman_three_point_holds F x y z,
          bregman_pythagorean_holds F x y z hproj⟩

end ConcreteCapstone

end
