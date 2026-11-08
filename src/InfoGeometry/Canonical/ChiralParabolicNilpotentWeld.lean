import InfoGeometry.Physics.ParabolicClock
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.ChiralCausalCone

/-!
# Native chiral/parabolic nilpotent weld

This file records only equalities between existing finite matrix owners.  The
parabolic clock generator is the upper chiral Jordan block, while its transpose
is the lower chiral block.  No new Clifford, projective, or Lie-theoretic
carrier is introduced here.
-/

namespace InfoGeometry.Canonical.ChiralParabolicNilpotentWeld

open InfoGeometry.Physics
open InfoGeometry.Physics.ChiralCausalCone

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

@[simp] theorem parabolicClock_K_eq_sigmaPlus :
    InfoGeometry.Physics.K (R := ℂ) = σPlus := by
  rfl

@[simp] theorem parabolicClock_K_sq_zero :
    InfoGeometry.Physics.K (R := ℂ) * InfoGeometry.Physics.K (R := ℂ) = 0 := by
  exact InfoGeometry.Physics.K_sq_eq_zero (R := ℂ)

@[simp] theorem parabolicClock_K_det_zero :
    (InfoGeometry.Physics.K (R := ℂ)).det = 0 := by
  simpa using (InfoGeometry.Physics.K_det_eq_zero (R := ℂ))

@[simp] theorem parabolicClock_K_trace_zero :
    Matrix.trace (InfoGeometry.Physics.K (R := ℂ)) = 0 := by
  simpa using (InfoGeometry.Physics.K_trace_eq_zero (R := ℂ))

theorem sigmaPlus_eq_parabolicClock_K :
    σPlus = InfoGeometry.Physics.K (R := ℂ) := by
  symm
  exact parabolicClock_K_eq_sigmaPlus

@[simp] theorem transpose_parabolicClock_K_eq_sigmaMinus :
    (InfoGeometry.Physics.K (R := ℂ)).transpose = σMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.K, σMinus, Matrix.transpose_apply]

@[simp] theorem sigmaMinus_sq_via_parabolicClock :
    σMinus * σMinus = 0 := by
  exact σMinus_sq

theorem parabolicFlow_eq_chiral_upper (t : ℂ) :
    InfoGeometry.Physics.parabolicFlow t = 1 + t • σPlus := by
  rfl

theorem parabolicFlow_sub_one_is_square_zero (t : ℂ) :
    (InfoGeometry.Physics.parabolicFlow t - 1) *
        (InfoGeometry.Physics.parabolicFlow t - 1) = 0 := by
  exact InfoGeometry.Physics.parabolicFlow_sub_one_sq_eq_zero (R := ℂ) t

theorem chiral_upper_is_parabolic_nilpotent :
    σPlus * σPlus = 0 ∧
    σPlus.det = 0 ∧
    Matrix.trace σPlus = 0 := by
  exact ⟨σPlus_sq, (chiral_transition_determinants_zero).1,
    by rw [← parabolicClock_K_eq_sigmaPlus]
       exact parabolicClock_K_trace_zero⟩

theorem chiral_lower_is_transpose_parabolic_nilpotent :
    σMinus = (InfoGeometry.Physics.K (R := ℂ)).transpose ∧
    σMinus * σMinus = 0 := by
  exact ⟨transpose_parabolicClock_K_eq_sigmaMinus.symm,
    sigmaMinus_sq_via_parabolicClock⟩

end InfoGeometry.Canonical.ChiralParabolicNilpotentWeld
