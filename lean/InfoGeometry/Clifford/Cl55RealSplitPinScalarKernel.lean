import InfoGeometry.Clifford.Cl55CenterMatrixBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55RealSplitPinKernelCenter

namespace InfoGeometry.Clifford.Clifford55

/-!
# Scalar normalization for the corrected split-Pin kernel

This file isolates the final scalar arithmetic.  A central kernel unit is
first read as an algebra scalar, and a reversion norm in `{1,-1}` then forces
that scalar to be `1` or `-1` over `ℝ`.
-/

theorem realSplitPin_scalar_coe_eq_pm_one_of_reverse_norm
    (g : realSplitPin55)
    (hscalar : ∃ r : ℝ, algebraMap ℝ Cl55 r = ((g : Cl55ˣ) : Cl55))
    (hnorm : CliffordAlgebra.reverse (Q := Q55)
          ((g : Cl55ˣ) : Cl55) * ((g : Cl55ˣ) : Cl55) = 1 ∨
        CliffordAlgebra.reverse (Q := Q55)
          ((g : Cl55ˣ) : Cl55) * ((g : Cl55ˣ) : Cl55) = -1) :
    (g : Cl55ˣ) = 1 ∨ (g : Cl55ˣ) = -1 := by
  rcases hscalar with ⟨r, hr⟩
  have hsq : r * r = 1 ∨ r * r = -1 := by
    rcases hnorm with hnorm | hnorm
    · left
      apply (algebraMap ℝ Cl55).injective
      calc
        algebraMap ℝ Cl55 (r * r) =
            algebraMap ℝ Cl55 r * algebraMap ℝ Cl55 r := by rw [map_mul]
        _ = CliffordAlgebra.reverse (algebraMap ℝ Cl55 r) *
              algebraMap ℝ Cl55 r := by
          rw [CliffordAlgebra.reverse.commutes]
        _ = CliffordAlgebra.reverse ((g : Cl55ˣ) : Cl55) *
              ((g : Cl55ˣ) : Cl55) := by rw [hr]
        _ = algebraMap ℝ Cl55 1 := hnorm
    · right
      apply (algebraMap ℝ Cl55).injective
      calc
        algebraMap ℝ Cl55 (r * r) =
            algebraMap ℝ Cl55 r * algebraMap ℝ Cl55 r := by rw [map_mul]
        _ = CliffordAlgebra.reverse (algebraMap ℝ Cl55 r) *
              algebraMap ℝ Cl55 r := by
          rw [CliffordAlgebra.reverse.commutes]
        _ = CliffordAlgebra.reverse ((g : Cl55ˣ) : Cl55) *
              ((g : Cl55ˣ) : Cl55) := by rw [hr]
        _ = algebraMap ℝ Cl55 (-1) := by simpa using hnorm
  rcases hsq with hsq | hsq
  · have hrpm : r = 1 ∨ r = -1 := by
      by_cases hnonneg : 0 ≤ r
      · left
        nlinarith
      · right
        nlinarith
    rcases hrpm with rfl | rfl
    · left
      apply Units.ext
      simpa using hr.symm
    · right
      apply Units.ext
      simpa using hr.symm
  · have : False := by
      have hnonneg : 0 ≤ r * r := mul_self_nonneg r
      linarith
    exact this.elim

end InfoGeometry.Clifford.Clifford55
