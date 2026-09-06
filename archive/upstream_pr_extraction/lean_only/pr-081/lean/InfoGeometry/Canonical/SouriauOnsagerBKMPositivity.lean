import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.BilinearForm.Properties
import InfoGeometry.Canonical.SouriauOnsagerBKMRealForm

noncomputable section

namespace SouriauOnsagerBKM

open Matrix
open scoped ComplexOrder
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {n : ℕ}

/-- The finite operator trace is nonnegative on a canonical square `X†X`.

This is the basis-independent operator statement proved through the existing
matrix/operator equivalence and Mathlib's positive-semidefinite trace theorem.
-/
theorem finiteOperatorTrace_star_mul_self_re_nonneg
    (X : FiniteOperatorAlgebra n) :
    0 ≤ (finiteOperatorTrace (star X * X)).re := by
  unfold finiteOperatorTrace
  change
    0 ≤
      (Matrix.trace
        (matrixOfOp ((ContinuousLinearMap.adjoint X).comp X))).re
  rw [matrixOfOp_comp, matrixOfOp_adjoint]
  have hpsd :
      ((matrixOfOp X)ᴴ * matrixOfOp X).PosSemidef :=
    posSemidef_conjTranspose_mul_self (matrixOfOp X)
  exact (RCLike.nonneg_iff.mp hpsd.trace_nonneg).1

/-- The finite operator trace of `X†X` vanishes exactly when `X` vanishes. -/
theorem finiteOperatorTrace_star_mul_self_re_eq_zero_iff
    (X : FiniteOperatorAlgebra n) :
    (finiteOperatorTrace (star X * X)).re = 0 ↔ X = 0 := by
  constructor
  · intro hre
    have hpsd :
        ((matrixOfOp X)ᴴ * matrixOfOp X).PosSemidef :=
      posSemidef_conjTranspose_mul_self (matrixOfOp X)
    have hnonneg :
        0 ≤ Matrix.trace ((matrixOfOp X)ᴴ * matrixOfOp X) :=
      hpsd.trace_nonneg
    have him :
        (Matrix.trace ((matrixOfOp X)ᴴ * matrixOfOp X)).im = 0 :=
      (RCLike.nonneg_iff.mp hnonneg).2
    have htrace :
        Matrix.trace ((matrixOfOp X)ᴴ * matrixOfOp X) = 0 := by
      apply Complex.ext
      · simpa [finiteOperatorTrace, matrixOfOp_comp, matrixOfOp_adjoint] using hre
      · simpa using him
    have hmat : (matrixOfOp X)ᴴ * matrixOfOp X = 0 :=
      hpsd.trace_eq_zero_iff.mp htrace
    have hop : star X * X = 0 := by
      apply matrixOfOp_injective
      change matrixOfOp ((ContinuousLinearMap.adjoint X).comp X) = 0
      rw [matrixOfOp_comp, matrixOfOp_adjoint, hmat, matrixOfOp_zero]
    exact (star_mul_self_eq_zero.mp hop)
  · rintro rfl
    simp [finiteOperatorTrace]

/-- Strict positivity of the finite trace square away from zero. -/
theorem finiteOperatorTrace_star_mul_self_re_pos
    (X : FiniteOperatorAlgebra n) (hX : X ≠ 0) :
    0 < (finiteOperatorTrace (star X * X)).re := by
  exact lt_of_le_of_ne
    (finiteOperatorTrace_star_mul_self_re_nonneg X)
    (Ne.symm ((finiteOperatorTrace_star_mul_self_re_eq_zero_iff X).not.mpr hX))

/-- The self Kubo--Mori integrand is the trace of an explicit operator square.

For
`X_s = ρ^((1-s)/2) A ρ^(s/2)`, cyclicity of the finite trace gives

`Tr(ρ^s A† ρ^(1-s) A) = Tr(X_s† X_s)`.

No simultaneous diagonalization or commutativity of `A` with `ρ` is used.
-/
theorem FaithfulDensityOperator.kuboMoriIntegrand_self_eq_trace_star_mul_self
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (s : ℝ) :
    D.kuboMoriIntegrand A A s =
      finiteOperatorTrace
        (star
            (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2)) *
          (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2))) := by
  have hleft :
      D.rpow ((1 - s) / 2) * D.rpow ((1 - s) / 2) =
        D.rpow (1 - s) := by
    rw [← D.rpow_add]
    congr 1
    ring
  have hright :
      D.rpow (s / 2) * D.rpow (s / 2) = D.rpow s := by
    rw [← D.rpow_add]
    congr 1
    ring
  calc
    D.kuboMoriIntegrand A A s =
        finiteOperatorTrace
          (D.rpow s * star A * D.rpow (1 - s) * A) := by
            rfl
    _ = finiteOperatorTrace
          ((D.rpow (s / 2) * D.rpow (s / 2)) *
            star A * D.rpow (1 - s) * A) := by
          rw [hright]
    _ = finiteOperatorTrace
          (D.rpow (s / 2) *
            (D.rpow (s / 2) * star A * D.rpow (1 - s) * A)) := by
          congr 1
          noncomm_ring
    _ = finiteOperatorTrace
          ((D.rpow (s / 2) * star A * D.rpow (1 - s) * A) *
            D.rpow (s / 2)) :=
          finiteOperatorTrace_mul_comm _ _
    _ = finiteOperatorTrace
          ((D.rpow (s / 2) * star A *
              (D.rpow ((1 - s) / 2) * D.rpow ((1 - s) / 2)) * A) *
            D.rpow (s / 2)) := by
          rw [hleft]
    _ = finiteOperatorTrace
          ((D.rpow (s / 2) * star A * D.rpow ((1 - s) / 2)) *
            (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2))) := by
          congr 1
          noncomm_ring
    _ = finiteOperatorTrace
          (star
              (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2)) *
            (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2))) := by
          congr 1
          simp [mul_assoc]

/-- Multiplication by the two faithful density powers used in the BKM
factorization does not annihilate a nonzero operator. -/
theorem FaithfulDensityOperator.rpow_sandwich_ne_zero
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (a b : ℝ)
    (hA : A ≠ 0) :
    D.rpow a * A * D.rpow b ≠ 0 := by
  intro hzero
  have hla : D.rpow (-a) * D.rpow a = 1 := by
    rw [← D.rpow_add]
    have : -a + a = 0 := by ring
    rw [this, D.rpow_zero]
  have hrb : D.rpow b * D.rpow (-b) = 1 := by
    rw [← D.rpow_add]
    have : b + -b = 0 := by ring
    rw [this, D.rpow_zero]
  apply hA
  calc
    A = (1 : FiniteOperatorAlgebra n) * A * 1 := by simp
    _ = (D.rpow (-a) * D.rpow a) * A *
          (D.rpow b * D.rpow (-b)) := by rw [hla, hrb]
    _ = D.rpow (-a) * (D.rpow a * A * D.rpow b) * D.rpow (-b) := by
          noncomm_ring
    _ = 0 := by rw [hzero]; simp

/-- Pointwise positivity of the full noncommutative Kubo--Mori self-integrand. -/
theorem FaithfulDensityOperator.kuboMoriIntegrand_self_re_nonneg
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (s : ℝ) :
    0 ≤ (D.kuboMoriIntegrand A A s).re := by
  rw [D.kuboMoriIntegrand_self_eq_trace_star_mul_self A s]
  exact finiteOperatorTrace_star_mul_self_re_nonneg _

/-- Pointwise strict definiteness of the full noncommutative Kubo--Mori
self-integrand. -/
theorem FaithfulDensityOperator.kuboMoriIntegrand_self_re_pos
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (s : ℝ)
    (hA : A ≠ 0) :
    0 < (D.kuboMoriIntegrand A A s).re := by
  rw [D.kuboMoriIntegrand_self_eq_trace_star_mul_self A s]
  exact finiteOperatorTrace_star_mul_self_re_pos _
    (D.rpow_sandwich_ne_zero A ((1 - s) / 2) (s / 2) hA)

/-- The real part of the integrated full noncommutative Kubo--Mori self-pairing
is nonnegative.

The only analytic input is the continuity hypothesis on the existing CFC
real-power path, already used by the BKM integrability owner.
-/
theorem FaithfulDensityOperator.kuboMoriPairing_self_re_nonneg
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow) :
    0 ≤ (D.kuboMoriPairing A A).re := by
  have h_integrable :
      IntervalIntegrable
        (D.kuboMoriIntegrand A A) MeasureTheory.volume 0 1 :=
    (D.continuous_kuboMoriIntegrand_of_continuous_rpow A A h_rpow).intervalIntegrable 0 1
  have hre :
      (D.kuboMoriPairing A A).re =
        ∫ s in (0 : ℝ)..1, (D.kuboMoriIntegrand A A s).re := by
    unfold FaithfulDensityOperator.kuboMoriPairing
    symm
    exact
      ContinuousLinearMap.intervalIntegral_comp_comm
        (RCLike.reCLM : ℂ →L[ℝ] ℝ) h_integrable
  rw [hre]
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num) fun s =>
    D.kuboMoriIntegrand_self_re_nonneg A s

/-- The existing real BKM response form is a genuine positive-semidefinite
symmetric bilinear form on the full finite noncommutative operator algebra. -/
theorem FaithfulDensityOperator.bkmRealBilinForm_isPosSemidef
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    (D.bkmRealBilinForm h_rpow).IsPosSemidef where
  isSymm := D.bkmRealBilinForm_symm h_rpow
  isNonneg := ⟨fun A => by
    simpa only [D.bkmRealBilinForm_apply h_rpow A A] using
      D.kuboMoriPairing_self_re_nonneg A h_rpow⟩

/-- The existing Onsager constructor specialized to the now-proved BKM
nonnegativity theorem.  No external positivity hypothesis is required. -/
noncomputable def FaithfulDensityOperator.bkmOnsagerFormCanonical
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    InfoGeometry.Thermo.SusceptibilityOnsagerStress.OnsagerTwoOperatorForm
      (FiniteOperatorAlgebra n) :=
  D.bkmOnsagerForm h_rpow (fun A => D.kuboMoriPairing_self_re_nonneg A h_rpow)

@[simp] theorem FaithfulDensityOperator.bkmOnsagerFormCanonical_apply
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A B : FiniteOperatorAlgebra n) :
    (D.bkmOnsagerFormCanonical h_rpow).form A B =
      (D.kuboMoriPairing A B).re :=
  rfl

end SouriauOnsagerBKM
