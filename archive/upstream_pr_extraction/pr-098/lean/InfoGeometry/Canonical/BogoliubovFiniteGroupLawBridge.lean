import InfoGeometry.Canonical.BogoliubovCovariantMellinKreinQuantizationBridge

/-!
# Finite inverse law for the phase-squeezing Bogoliubov matrix

The existing Mellin owner proves the inverse law for the hyperbolic squeezing
factor.  This file supplies the missing finite matrix composition law for the
full displayed product `R(θ) * B_sq(r)`.  The inverse is ordered as
`B_sq(-r) * R(-θ)`; it is not obtained by simply changing both parameters in
the original product.  No Fock implementability or infinite-dimensional
quantization statement is made.
-/

noncomputable section

namespace InfoGeometry.Canonical.BogoliubovFiniteGroupLawBridge

open InfoGeometry.Canonical.BogoliubovMellinKrein

theorem phaseRotorMatrix_neg_mul (theta : ℝ) :
    phaseRotorMatrix (-theta) * phaseRotorMatrix theta = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseRotorMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      ← Complex.exp_add] <;>
    congr 1 <;> ring

theorem bogoliubovMatrix_inverse_factorization
    (u t log_n : ℝ) :
    squeezingMatrix (-(u * log_n)) * phaseRotorMatrix (-(t * log_n)) *
        bogoliubovMatrix u t log_n = 1 := by
  calc
    squeezingMatrix (-(u * log_n)) * phaseRotorMatrix (-(t * log_n)) *
          bogoliubovMatrix u t log_n =
        squeezingMatrix (-(u * log_n)) *
          ((phaseRotorMatrix (-(t * log_n)) *
            phaseRotorMatrix (t * log_n)) *
              squeezingMatrix (u * log_n)) := by
            simp only [bogoliubovMatrix, Matrix.mul_assoc]
    _ = squeezingMatrix (-(u * log_n)) * squeezingMatrix (u * log_n) := by
      rw [phaseRotorMatrix_neg_mul]
      simp
    _ = 1 := squeezingMatrix_mul_inv (u * log_n)

theorem phaseRotorMatrix_mul_neg (theta : ℝ) :
    phaseRotorMatrix theta * phaseRotorMatrix (-theta) = 1 := by
  simpa [neg_neg] using phaseRotorMatrix_neg_mul (-theta)

theorem bogoliubovMatrix_inverse_factorization_right
    (u t log_n : ℝ) :
    bogoliubovMatrix u t log_n *
        (squeezingMatrix (-(u * log_n)) * phaseRotorMatrix (-(t * log_n))) = 1 := by
  have hsq : squeezingMatrix (u * log_n) *
      squeezingMatrix (-(u * log_n)) = 1 := by
    simpa using squeezingMatrix_mul_inv (-(u * log_n))
  calc
    bogoliubovMatrix u t log_n *
          (squeezingMatrix (-(u * log_n)) * phaseRotorMatrix (-(t * log_n))) =
        phaseRotorMatrix (t * log_n) *
          ((squeezingMatrix (u * log_n) *
            squeezingMatrix (-(u * log_n))) *
              phaseRotorMatrix (-(t * log_n))) := by
            simp only [bogoliubovMatrix, Matrix.mul_assoc]
    _ = 1 := by
      rw [hsq]
      simp [phaseRotorMatrix_mul_neg]

end InfoGeometry.Canonical.BogoliubovFiniteGroupLawBridge
