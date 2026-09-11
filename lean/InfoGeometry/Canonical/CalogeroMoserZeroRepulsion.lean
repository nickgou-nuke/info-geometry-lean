import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Calogero--Moser pair kernel

This owner records the finite real algebra behind the inverse-distance
interaction used in zero-flow heuristics.  It does not define a zero flow,
differentiate roots, or assert collision avoidance for an analytic family.
-/

namespace InfoGeometry.Canonical.CalogeroMoserZeroRepulsion

noncomputable section

/-- Signed inverse-distance interaction between two distinct real ordinates. -/
def pairForce (x y : ℝ) : ℝ := 2 / (x - y)

/-- The squared inverse-distance interaction, used as the finite repulsion
energy. -/
def pairEnergy (x y : ℝ) : ℝ := 2 / (x - y) ^ 2

theorem pairForce_swap (x y : ℝ) :
    pairForce y x = -pairForce x y := by
  unfold pairForce
  rw [show y - x = -(x - y) by ring, div_neg]

theorem pairForce_pos {x y : ℝ} (hxy : y < x) :
    0 < pairForce x y := by
  unfold pairForce
  exact div_pos (by norm_num) (sub_pos.mpr hxy)

theorem pairForce_neg {x y : ℝ} (hxy : x < y) :
    pairForce x y < 0 := by
  unfold pairForce
  exact div_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr hxy)

theorem pairForce_ne_zero {x y : ℝ} (hxy : x ≠ y) :
    pairForce x y ≠ 0 := by
  unfold pairForce
  exact div_ne_zero (by norm_num) (sub_ne_zero.mpr hxy)

theorem pairEnergy_nonneg (x y : ℝ) :
    0 ≤ pairEnergy x y := by
  unfold pairEnergy
  exact div_nonneg (by norm_num) (sq_nonneg (x - y))

theorem pairEnergy_pos {x y : ℝ} (hxy : x ≠ y) :
    0 < pairEnergy x y := by
  unfold pairEnergy
  exact div_pos (by norm_num) (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy))

theorem pairEnergy_swap (x y : ℝ) :
    pairEnergy y x = pairEnergy x y := by
  unfold pairEnergy
  congr 1
  ring

/-! ## Finite collision-free interaction energy -/

/-- Sum of pair energies over distinct ordered indices with `i < j`. -/
def finitePairEnergy {n : ℕ} (t : Fin n → ℝ) : ℝ :=
  ∑ ij ∈ (Finset.univ.product Finset.univ).filter
    (fun ij : Fin n × Fin n => ij.1 < ij.2),
    pairEnergy (t ij.1) (t ij.2)

theorem finitePairEnergy_nonneg {n : ℕ} (t : Fin n → ℝ) :
    0 ≤ finitePairEnergy t := by
  unfold finitePairEnergy
  exact Finset.sum_nonneg fun ij hij => pairEnergy_nonneg (t ij.1) (t ij.2)

theorem finitePairEnergy_eq_zero_of_constant {n : ℕ} (t : Fin n → ℝ)
    (ht : ∀ i j, t i = t j) :
    finitePairEnergy t = 0 := by
  unfold finitePairEnergy
  apply Finset.sum_eq_zero
  intro ij hij
  rw [ht ij.1 ij.2]
  simp [pairEnergy]

end

end InfoGeometry.Canonical.CalogeroMoserZeroRepulsion
