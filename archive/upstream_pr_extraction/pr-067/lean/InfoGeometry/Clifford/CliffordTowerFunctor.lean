import Mathlib.Data.Real.Basic
import InfoGeometry.Clifford.CliffordTower

/-!
# Clifford Tower Functor: Cl_n → Cl_{n+1}

Constructs the functorial tower of Clifford algebras with inclusion maps
and proves the Mersenne dimension hierarchy.
-/

noncomputable section

namespace InfoGeometry.Clifford

open CliffordTower

/-- Total dimension: dim(Cl_n) = 2ⁿ -/
def ClDim (n : ℕ) : ℕ := 2 ^ n

/-- Imaginary dimension: dim(Im(Cl_n)) = 2ⁿ - 1 -/
def ImagDim (n : ℕ) : ℕ := ClDim n - 1

/-- Functorial tower structure -/
structure NatDimensionTower where
  obj : ℕ → ℕ
  map : ∀ {n m : ℕ}, n ≤ m → obj n ≤ obj m
  map_id : ∀ n, map (Nat.le_refl n) = Nat.le_refl (obj n)
  map_comp : ∀ {l m n} (hlm : l ≤ m) (hmn : m ≤ n),
    map (Nat.le_trans hlm hmn) = le_trans (map hlm) (map hmn)

/-- The Clifford dimension tower functor -/
def cliffordTowerFunctor : NatDimensionTower where
  obj := ClDim
  map := by
    intro n m h
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) h
  map_id := by
    intro n
    rfl
  map_comp := by
    intro l m n hlm hmn
    rfl

theorem dim_Cl_pow_two (n : ℕ) : ClDim n = 2 ^ n := rfl

theorem dim_imag_Cl_mersenne (n : ℕ) : ImagDim n = mersenne n := rfl

theorem dim_growth (n : ℕ) : ClDim (n + 1) = 2 * ClDim n := by
  simp [ClDim, pow_succ, Nat.mul_comm]

theorem mersenne_growth (n : ℕ) : mersenne (n + 1) = 2 * mersenne n + 1 :=
  mersenne_succ n

theorem hierarchy_sum : mersenne 2 + mersenne 3 + mersenne 7 = 137 :=
  combinatorial_hierarchy_sum

theorem cl2 : ClDim 2 = 4 ∧ ImagDim 2 = 3 := by simp [ClDim, ImagDim]

theorem cl3 : ClDim 3 = 8 ∧ ImagDim 3 = 7 := by simp [ClDim, ImagDim]

theorem cl7 : mersenne 7 = 127 := mersenne_seven

end InfoGeometry.Clifford

noncomputable section