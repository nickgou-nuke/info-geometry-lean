import InfoGeometry.Clifford.Cl55ThreeColorChiralSums
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exact finite spectral calculus for the three-colour `Cl(5,5)` Dirac sum

`Cl55ThreeColorChiralSums` proves the native identity
`chiralDiracSum * chiralDiracSum = 3`.  This owner records only its exact
algebraic consequences on that same Clifford carrier.  It does not claim a
Connes spectral triple, compact resolvent on an arbitrary Hilbert space, or a
KMS state.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

def chiralDiracSumUnit : Cl55ˣ where
  val := chiralDiracSum
  inv := ((1 : ℝ) / 3) • chiralDiracSum
  val_inv := by
    calc
      chiralDiracSum * (((1 : ℝ) / 3) • chiralDiracSum) =
          algebraMap ℝ Cl55 ((1 : ℝ) / 3) *
            (chiralDiracSum * chiralDiracSum) := by
            rw [Algebra.smul_def]
            calc
              chiralDiracSum *
                    (algebraMap ℝ Cl55 ((1 : ℝ) / 3) * chiralDiracSum) =
                  (chiralDiracSum * algebraMap ℝ Cl55 ((1 : ℝ) / 3)) *
                    chiralDiracSum := by rw [mul_assoc]
              _ = (algebraMap ℝ Cl55 ((1 : ℝ) / 3) * chiralDiracSum) *
                    chiralDiracSum := by rw [Algebra.commutes]
              _ = algebraMap ℝ Cl55 ((1 : ℝ) / 3) *
                    (chiralDiracSum * chiralDiracSum) := by rw [mul_assoc]
      _ = 1 := by
        rw [chiralDiracSum_sq]
        have h3 : (3 : Cl55) = algebraMap ℝ Cl55 (3 : ℝ) := by
          simpa using (map_natCast (algebraMap ℝ Cl55) 3).symm
        rw [h3, ← map_mul]
        norm_num
  inv_val := by
    calc
      (((1 : ℝ) / 3) • chiralDiracSum) * chiralDiracSum =
          algebraMap ℝ Cl55 ((1 : ℝ) / 3) *
            (chiralDiracSum * chiralDiracSum) := by
            rw [Algebra.smul_def, mul_assoc]
      _ = 1 := by
        rw [chiralDiracSum_sq]
        have h3 : (3 : Cl55) = algebraMap ℝ Cl55 (3 : ℝ) := by
          simpa using (map_natCast (algebraMap ℝ Cl55) 3).symm
        rw [h3, ← map_mul]
        norm_num

@[simp] theorem chiralDiracSumUnit_val :
    (chiralDiracSumUnit : Cl55) = chiralDiracSum := rfl

theorem chiralDiracSumUnit_inv_val :
    ((chiralDiracSumUnit⁻¹ : Cl55ˣ) : Cl55) =
      ((1 : ℝ) / 3) • chiralDiracSum := rfl

theorem chiralDiracSum_pow_even (m : ℕ) :
    chiralDiracSum ^ (2 * m) = (algebraMap ℝ Cl55 3) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, pow_add, pow_two, ih, chiralDiracSum_sq,
        pow_succ]
      have h3 : (3 : Cl55) = algebraMap ℝ Cl55 (3 : ℝ) := by
        simpa using (map_natCast (algebraMap ℝ Cl55) 3).symm
      rw [h3]

theorem chiralDiracSum_pow_odd (m : ℕ) :
    chiralDiracSum ^ (2 * m + 1) =
      (algebraMap ℝ Cl55 3) ^ m * chiralDiracSum := by
  rw [pow_succ, chiralDiracSum_pow_even]

theorem chiralDiracSum_shifted_square :
    chiralDiracSum * chiralDiracSum + 1 = (4 : Cl55) := by
  rw [chiralDiracSum_sq]
  norm_num

theorem chiralDiracSum_shifted_resolvent_left :
    ((1 : ℝ) / 4) • (1 : Cl55) *
        (chiralDiracSum * chiralDiracSum + 1) = 1 := by
  rw [chiralDiracSum_shifted_square]
  rw [Algebra.smul_def]
  have h4 : (4 : Cl55) = algebraMap ℝ Cl55 (4 : ℝ) := by
    simpa using (map_natCast (algebraMap ℝ Cl55) 4).symm
  rw [h4]
  simp only [mul_one]
  rw [← map_mul]
  norm_num

theorem chiralDiracSum_shifted_resolvent_right :
    (chiralDiracSum * chiralDiracSum + 1) *
        (((1 : ℝ) / 4) • (1 : Cl55)) = 1 := by
  rw [chiralDiracSum_shifted_square]
  rw [Algebra.smul_def]
  have h4 : (4 : Cl55) = algebraMap ℝ Cl55 (4 : ℝ) := by
    simpa using (map_natCast (algebraMap ℝ Cl55) 4).symm
  rw [h4]
  simp only [mul_one]
  rw [← map_mul]
  norm_num

def chiralDiracSumShiftedUnit : Cl55ˣ where
  val := chiralDiracSum * chiralDiracSum + 1
  inv := ((1 : ℝ) / 4) • (1 : Cl55)
  val_inv := chiralDiracSum_shifted_resolvent_right
  inv_val := chiralDiracSum_shifted_resolvent_left

@[simp] theorem chiralDiracSumShiftedUnit_val :
    (chiralDiracSumShiftedUnit : Cl55) =
      chiralDiracSum * chiralDiracSum + 1 := rfl

theorem chiralDiracSumShiftedUnit_inv_val :
    ((chiralDiracSumShiftedUnit⁻¹ : Cl55ˣ) : Cl55) =
      ((1 : ℝ) / 4) • (1 : Cl55) := rfl

end InfoGeometry.Clifford.Clifford55
