import InfoGeometry.Clifford.Cl11Matrix

namespace InfoGeometry.Algebra.SplitCliffordOperatorIdentities

section AssociativeOperators

variable {Carrier : Type*} [Ring Carrier]
variable (elliptic split : Carrier)
variable (hanti : elliptic * split = -(split * elliptic))
variable (helliptic : elliptic * elliptic = -1) (hsplit : split * split = 1)

include hanti helliptic hsplit

theorem reverse_anticommutation : split * elliptic = -(elliptic * split) := by
  simpa using (congrArg Neg.neg hanti).symm

theorem mixed_product_square : (elliptic * split) * (elliptic * split) = 1 := by
  calc
    (elliptic * split) * (elliptic * split) =
        elliptic * (split * elliptic) * split := by simp only [mul_assoc]
    _ = -((elliptic * elliptic) * (split * split)) := by
      rw [reverse_anticommutation elliptic split hanti]
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = 1 := by rw [helliptic, hsplit]; simp

theorem mixed_product_conjugates_elliptic :
    (elliptic * split) * elliptic * (elliptic * split) = -elliptic := by
  calc
    (elliptic * split) * elliptic * (elliptic * split) =
        elliptic * (split * elliptic) * (elliptic * split) := by simp only [mul_assoc]
    _ = -(elliptic * ((elliptic * split) * (elliptic * split))) := by
      rw [reverse_anticommutation elliptic split hanti]
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = -elliptic := by
      rw [mixed_product_square elliptic split hanti helliptic hsplit, mul_one]

theorem null_sum_square : (elliptic + split) ^ 2 = 0 := by
  calc
    (elliptic + split) ^ 2 =
        elliptic * elliptic + (elliptic * split + split * elliptic) + split * split := by
      noncomm_ring
    _ = 0 := by rw [helliptic, hsplit, hanti]; simp

end AssociativeOperators

noncomputable section

open InfoGeometry.Clifford.Cl11Matrix

theorem mixed_generator_square (angle boost : ℝ) :
    (angle • Eminus + boost • Eplus) ^ 2 = (boost ^ 2 - angle ^ 2) • (1 : Mat2) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Eminus, Eplus, pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem half_sum_nilpotent : ((1 / 2 : ℝ) • (Eminus + Eplus)) ^ 2 = 0 := by
  rw [smul_add, mixed_generator_square]
  simp

theorem projector_not_nilpotent :
    ¬ IsNilpotent (!![(1 : ℝ), 0; 0, 0] : Mat2) := by
  intro hnilpotent
  obtain ⟨exponent, hzero⟩ := hnilpotent
  have hentry : ∀ power : ℕ, ((!![(1 : ℝ), 0; 0, 0] : Mat2) ^ power) 0 0 = 1 := by
    intro power
    induction power with
    | zero => simp
    | succ power inductionHypothesis =>
        simpa [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] using inductionHypothesis
  have hcontradiction := hentry exponent
  rw [hzero] at hcontradiction
  norm_num at hcontradiction

end

end InfoGeometry.Algebra.SplitCliffordOperatorIdentities
