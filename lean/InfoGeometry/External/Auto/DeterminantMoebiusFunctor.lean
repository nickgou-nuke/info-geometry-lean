import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Sign
import InfoGeometry.External.Auto.DeterminantSupergrading
import InfoGeometry.External.Auto.TrifactorGeometry
import InfoGeometry.External.Auto.MobiusInversion

noncomputable section

open Matrix
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Canonical.DeterminantMoebiusFunctor

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- Weyl scale sector of a finite gauge block: absolute determinant. -/
def detScale (A : M2R) : ℝ := |A.det|

/-- Chiral parity sector of a finite gauge block: sign(det). -/
def detParity (A : M2R) : SignType := superGrade A

theorem det_scale_nonneg (A : M2R) : 0 ≤ detScale A := by
  simp [detScale]

/-- Multiplicativity of the continuous Weyl sector. -/
theorem detScale_mul (A B : M2R) :
    detScale (A * B) = detScale A * detScale B := by
  simp [detScale, Matrix.det_mul, abs_mul]

/-- Multiplicativity of the discrete chiral sector. -/
theorem detParity_mul (A B : M2R) :
    detParity (A * B) = detParity A * detParity B := by
  simpa [detParity] using superGrade_mul A B

/-- `Real.sign` matches the determinant parity as a scalar. -/
theorem detParity_eq_real_sign (A : M2R) :
    (detParity A : ℝ) = Real.sign A.det := by
  by_cases hA : A.det = 0
  · have hcast : (detParity A : ℝ) = 0 := by
      change (SignType.sign A.det : ℝ) = 0
      exact congrArg (fun s : SignType => (s : ℝ)) (sign_eq_zero_iff.mpr hA)
    simp [hcast, hA]
  · by_cases hpos : 0 < A.det
    · have hcast : (detParity A : ℝ) = 1 := by
        change (SignType.sign A.det : ℝ) = 1
        simpa using congrArg (fun s : SignType => (s : ℝ)) (sign_pos hpos)
      simp [hcast, Real.sign_of_pos hpos]
    · have hneg : A.det < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (by simpa [eq_comm] using hA)
      have hcast : (detParity A : ℝ) = -1 := by
        change (SignType.sign A.det : ℝ) = -1
        simpa using congrArg (fun s : SignType => (s : ℝ)) (sign_neg hneg)
      simp [hcast, Real.sign_of_neg hneg]

/-- Exact factorization: `det = |det| · sign(det)` for real 2×2 matrices. -/
theorem det_scale_factorization (A : M2R) :
    A.det = detScale A * (detParity A : ℝ) := by
  have hreal : A.det = |A.det| * Real.sign A.det := by
    by_cases hA : A.det = 0
    · rw [hA]
      simp
    · by_cases hpos : 0 < A.det
      · rw [abs_of_nonneg (le_of_lt hpos), Real.sign_of_pos hpos]
        ring
      · have hneg : A.det < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (by simpa [eq_comm] using hA)
        rw [abs_of_neg hneg, Real.sign_of_neg hneg]
        ring
  rw [detScale, detParity_eq_real_sign A]
  exact hreal

/-- Finite Möbius sector function valued in `SignType`. -/
def moebiusSector (n : ℕ) : SignType :=
  if _h0 : ArithmeticFunction.moebius n = 0 then 0
  else if _h1 : ArithmeticFunction.moebius n = 1 then 1
  else -1

/-- Möbius values are exactly in the three chiral sectors. -/
theorem moebius_sector_triple (n : ℕ) :
    moebiusSector n = 0 ∨ moebiusSector n = 1 ∨ moebiusSector n = -1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [moebiusSector, h]

/-- Determinant parity and Möbius parity both realize the same trichotomy pattern. -/
theorem parity_trichotomy (A : M2R) :
    detParity A = 0 ∨ detParity A = 1 ∨ detParity A = -1 := by
  rcases SignType.trichotomy (detParity A) with hneg | hzero | hpos
  · exact Or.inr <| Or.inr hneg
  · exact Or.inl hzero
  · exact Or.inr <| Or.inl hpos

/-- The Möbius inversion layer is available as a discrete inverse transform. -/
theorem moebius_duality_layer :
    dirichletConvolution bosonicKernel fermionicMobiusKernel = vacuumKernel := by
  simpa using mobius_is_dirichlet_inverse

/-- Tripotent/chirality compatibility from the cubic spectrum `q^3 = q`. -/
theorem trifactor_to_discrete_sector {q : ℝ} (hq : q ^ 3 = q) :
    (q = -1 ∨ q = 0 ∨ q = 1) :=
  TrifactorGeometry.cubic_real_roots (q := q) hq

end InfoGeometry.Canonical.DeterminantMoebiusFunctor
