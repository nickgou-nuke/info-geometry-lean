import InfoGeometry.Canonical.ModularFlowGeneratorDerivative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib

/-!
# Exponential generator specialization

This file specializes the product-rule owner to the native Banach-algebra
exponential.  It proves the commutator derivative from explicit exponential
derivative lemmas; it does not assert Stone's theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.ModularFlowExponentialGenerator

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def exponentialConjugationPath (G x : A) (t : ℝ) : A :=
  NormedSpace.exp (t • G) * x * NormedSpace.exp (-(t • G))

theorem hasDerivAt_exponentialConjugationPath_zero (G x : A) :
    HasDerivAt (exponentialConjugationPath G x)
      (G * x - x * G) 0 := by
  have hU : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • G)) G 0 := by
    simpa using (hasDerivAt_exp_smul_const (𝕂 := ℝ) G 0)
  have hV : HasDerivAt (fun t : ℝ => NormedSpace.exp (-t • G)) (-G) 0 := by
    have hbase : HasDerivAt
        (fun t : ℝ => NormedSpace.exp (t • (-G))) (-G) 0 := by
      simpa using (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-G) 0)
    simpa [exponentialConjugationPath, neg_smul] using hbase
  simpa [exponentialConjugationPath,
    ModularFlowGeneratorDerivative.conjugationPath,
    sub_eq_add_neg, neg_smul, mul_neg] using
    ModularFlowGeneratorDerivative.hasDerivAt_conjugationPath_zero
      (U := fun t : ℝ => NormedSpace.exp (t • G))
      (V := fun t : ℝ => NormedSpace.exp (-t • G))
      (U' := G) (V' := -G) x (by simp) (by simp) hU hV

end InfoGeometry.Canonical.ModularFlowExponentialGenerator

namespace InfoGeometry.Canonical.ModularFlowExponentialGenerator

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

def complexExponentialConjugationPath (G x : B) (t : ℝ) : B :=
  NormedSpace.exp (t • (Complex.I • G)) * x *
    NormedSpace.exp (-(t • (Complex.I • G)))

theorem hasDerivAt_complexExponentialConjugationPath_zero (G x : B) :
    HasDerivAt (complexExponentialConjugationPath G x)
      (Complex.I • (G * x - x * G)) 0 := by
  have h := hasDerivAt_exponentialConjugationPath_zero
    (A := B) (Complex.I • G) x
  simpa [complexExponentialConjugationPath, exponentialConjugationPath,
    sub_eq_add_neg, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    smul_add, smul_neg] using h

end InfoGeometry.Canonical.ModularFlowExponentialGenerator
