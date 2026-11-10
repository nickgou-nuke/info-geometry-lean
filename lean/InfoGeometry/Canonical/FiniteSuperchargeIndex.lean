import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# A concrete finite supercharge index

This owner supplies an actual finite `Z₂`-graded complex with zero
supercharges.  Its index is computed from kernel dimensions, not assigned by
definition to a divisor or a spectral count.  No infinite-dimensional index
or analytic divisor correspondence is asserted.
-/

namespace InfoGeometry.Canonical.FiniteSuperchargeIndex

noncomputable section

abbrev Plus (m : ℕ) := Fin m → ℝ
abbrev Minus (n : ℕ) := Fin n → ℝ

structure FiniteSupercharge (m n : ℕ) where
  qPlus : Plus m →ₗ[ℝ] Minus n
  qMinus : Minus n →ₗ[ℝ] Plus m
  qMinus_qPlus : qMinus.comp qPlus = 0
  qPlus_qMinus : qPlus.comp qMinus = 0

/-- The kernel-dimension Euler/Witten index of a finite supercharge pair. -/
def wittenIndex {m n : ℕ} (Q : FiniteSupercharge m n) : ℤ :=
  (Module.finrank ℝ (LinearMap.ker Q.qPlus) : ℤ) -
    (Module.finrank ℝ (LinearMap.ker Q.qMinus) : ℤ)

/-- Rank–nullity identifies the kernel index with the grading-dimension
difference whenever the two odd maps have equal rank.  The square-zero fields
in `FiniteSupercharge` alone do not imply this rank balance; it is an explicit
condition supplied, for example, by an intertwining equivalence. -/
theorem wittenIndex_eq_dimension_difference_of_range_finrank_eq
    {m n : ℕ} (Q : FiniteSupercharge m n)
    (hRank : Module.finrank ℝ (LinearMap.range Q.qPlus) =
      Module.finrank ℝ (LinearMap.range Q.qMinus)) :
    wittenIndex Q = (m : ℤ) - n := by
  let rPlus := Module.finrank ℝ (LinearMap.range Q.qPlus)
  let rMinus := Module.finrank ℝ (LinearMap.range Q.qMinus)
  let kPlus := Module.finrank ℝ (LinearMap.ker Q.qPlus)
  let kMinus := Module.finrank ℝ (LinearMap.ker Q.qMinus)
  have hPlus : rPlus + kPlus = m := by
    simpa [rPlus, kPlus, Plus, Module.finrank_fin_fun] using
      (LinearMap.finrank_range_add_finrank_ker Q.qPlus)
  have hMinus : rMinus + kMinus = n := by
    simpa [rMinus, kMinus, Minus, Module.finrank_fin_fun] using
      (LinearMap.finrank_range_add_finrank_ker Q.qMinus)
  have hRank' : (rPlus : ℤ) = rMinus := by
    exact_mod_cast hRank
  have hPlus' : (rPlus : ℤ) + kPlus = m := by
    exact_mod_cast hPlus
  have hMinus' : (rMinus : ℤ) + kMinus = n := by
    exact_mod_cast hMinus
  change (kPlus : ℤ) - kMinus = (m : ℤ) - n
  omega

/-- The canonical finite complex with vanishing odd supercharges. -/
def zeroSupercharge (m n : ℕ) : FiniteSupercharge m n where
  qPlus := 0
  qMinus := 0
  qMinus_qPlus := by simp
  qPlus_qMinus := by simp

theorem zeroSupercharge_qPlus_ker (m n : ℕ) :
    Module.finrank ℝ (LinearMap.ker (zeroSupercharge m n).qPlus) = m := by
  rw [show (zeroSupercharge m n).qPlus = 0 by rfl]
  have hker : LinearMap.ker (0 : Plus m →ₗ[ℝ] Minus n) = ⊤ := by
    ext x
    simp
  rw [hker, finrank_top, Module.finrank_fin_fun]

theorem zeroSupercharge_qMinus_ker (m n : ℕ) :
    Module.finrank ℝ (LinearMap.ker (zeroSupercharge m n).qMinus) = n := by
  rw [show (zeroSupercharge m n).qMinus = 0 by rfl]
  have hker : LinearMap.ker (0 : Minus n →ₗ[ℝ] Plus m) = ⊤ := by
    ext x
    simp
  rw [hker, finrank_top, Module.finrank_fin_fun]

theorem zeroSupercharge_wittenIndex (m n : ℕ) :
    wittenIndex (zeroSupercharge m n) = (m : ℤ) - n := by
  apply wittenIndex_eq_dimension_difference_of_range_finrank_eq
  change Module.finrank ℝ (LinearMap.range (0 : Plus m →ₗ[ℝ] Minus n)) =
    Module.finrank ℝ (LinearMap.range (0 : Minus n →ₗ[ℝ] Plus m))
  rw [LinearMap.range_zero, LinearMap.range_zero, finrank_bot, finrank_bot]

theorem zeroSupercharge_wittenIndex_add
    (m n p q : ℕ) :
    wittenIndex (zeroSupercharge (m + p) (n + q)) =
      wittenIndex (zeroSupercharge m n) +
        wittenIndex (zeroSupercharge p q) := by
  rw [zeroSupercharge_wittenIndex, zeroSupercharge_wittenIndex,
    zeroSupercharge_wittenIndex]
  push_cast
  ring

end

end InfoGeometry.Canonical.FiniteSuperchargeIndex
