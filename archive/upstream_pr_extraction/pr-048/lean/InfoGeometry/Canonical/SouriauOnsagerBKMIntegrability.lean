import InfoGeometry.Canonical.SouriauOnsagerBKMBridge

noncomputable section

/-!
# Automatic interval-integrability interface for the finite BKM pairing

The finite Kubo--Mori owner proves Hermitian symmetry from an explicit
`IntervalIntegrable` hypothesis.  This adapter discharges that hypothesis
from the native Mathlib continuity criterion, without asserting continuity of
the `CFC.rpow` parameter unless a model supplies it.
-/

namespace SouriauOnsagerBKM

variable {n : ℕ}

/-- The finite trace, promoted to the native continuous-linear-map API. -/
def finiteOperatorTraceCLM (n : ℕ) :
    FiniteOperatorAlgebra n →L[ℂ] ℂ :=
  (finiteOperatorTraceLinear n).toContinuousLinearMap

@[simp] theorem finiteOperatorTraceCLM_apply
    (T : FiniteOperatorAlgebra n) :
    finiteOperatorTraceCLM n T = finiteOperatorTrace T :=
  rfl

/-- The coordinate matrix trace used by the finite BKM owner is exactly
Mathlib's basis-independent trace of the underlying linear endomorphism. -/
theorem finiteOperatorTrace_eq_linearMap_trace
    (T : FiniteOperatorAlgebra n) :
    finiteOperatorTrace T =
      LinearMap.trace ℂ (FiniteHilbertSpace n) T.toLinearMap := by
  unfold finiteOperatorTrace
  exact (LinearMap.trace_eq_matrix_trace ℂ
    (InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix.ketBasis
      (Fin n)) T.toLinearMap).symm

/--
Continuity of the finite Kubo--Mori integrand follows from continuity of the
`CFC.rpow` parameter path.  The latter remains an explicit model hypothesis:
this theorem does not claim continuity of `CFC.rpow` in its exponent.
-/
theorem FaithfulDensityOperator.continuous_kuboMoriIntegrand_of_continuous_rpow
    (D : FaithfulDensityOperator n)
    (A B : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow) :
    Continuous (D.kuboMoriIntegrand A B) := by
  unfold FaithfulDensityOperator.kuboMoriIntegrand
  change Continuous (fun s =>
    finiteOperatorTraceCLM n
      (D.rpow s * star A * D.rpow (1 - s) * B))
  fun_prop

theorem FaithfulDensityOperator.kuboMoriPairing_conj_symm_of_continuous
    (D : FaithfulDensityOperator n)
    (A B : FiniteOperatorAlgebra n)
    (hcont : Continuous (D.kuboMoriIntegrand A B)) :
    star (D.kuboMoriPairing A B) =
      D.kuboMoriPairing B A := by
  exact D.kuboMoriPairing_conj_symm A B (hcont.intervalIntegrable 0 1)

theorem FaithfulDensityOperator.kuboMoriPairing_conj_symm_of_continuous_rpow
    (D : FaithfulDensityOperator n)
    (A B : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow) :
    star (D.kuboMoriPairing A B) =
      D.kuboMoriPairing B A := by
  exact D.kuboMoriPairing_conj_symm_of_continuous A B
    (D.continuous_kuboMoriIntegrand_of_continuous_rpow A B h_rpow)

/-! ## Operator-valued Kubo--Mori transform -/

/--
The genuine operator-valued Kubo--Mori transform
`∫₀¹ ρˢ A ρ¹⁻ˢ ds` on the full finite noncommutative operator algebra.
-/
def FaithfulDensityOperator.kuboMoriTransform
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n) : FiniteOperatorAlgebra n :=
  ∫ s in (0 : ℝ)..1, D.modularInterpolation s A

/-- Continuity of the operator-valued modular interpolation follows from the
explicit continuity hypothesis on the real-power path. -/
theorem FaithfulDensityOperator.continuous_modularInterpolation_of_continuous_rpow
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow) :
    Continuous (fun s : ℝ => D.modularInterpolation s A) := by
  unfold FaithfulDensityOperator.modularInterpolation
  fun_prop

/-- The operator-valued Kubo--Mori integrand is interval-integrable whenever
the density real-power path is continuous. -/
theorem FaithfulDensityOperator.intervalIntegrable_modularInterpolation_of_continuous_rpow
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow) :
    IntervalIntegrable
      (fun s : ℝ => D.modularInterpolation s A)
      MeasureTheory.volume 0 1 :=
  (D.continuous_modularInterpolation_of_continuous_rpow A h_rpow).intervalIntegrable 0 1

/-- The integrated Kubo--Mori transform as a genuine complex-linear operator
on the full finite operator algebra. -/
noncomputable def FaithfulDensityOperator.kuboMoriTransformLinear
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    FiniteOperatorAlgebra n →ₗ[ℂ] FiniteOperatorAlgebra n where
  toFun := D.kuboMoriTransform
  map_add' A B := by
    unfold FaithfulDensityOperator.kuboMoriTransform
    rw [← intervalIntegral.integral_add
      (D.intervalIntegrable_modularInterpolation_of_continuous_rpow A h_rpow)
      (D.intervalIntegrable_modularInterpolation_of_continuous_rpow B h_rpow)]
    apply intervalIntegral.integral_congr
    intro s hs
    simp [FaithfulDensityOperator.modularInterpolation, mul_add, add_mul]
  map_smul' c A := by
    unfold FaithfulDensityOperator.kuboMoriTransform
    change (∫ s in (0 : ℝ)..1, D.modularInterpolation s (c • A)) =
      c • (∫ s in (0 : ℝ)..1, D.modularInterpolation s A)
    rw [← intervalIntegral.integral_smul c]
    apply intervalIntegral.integral_congr
    intro s hs
    simp [FaithfulDensityOperator.modularInterpolation, mul_smul_comm, smul_mul_assoc]

@[simp] theorem FaithfulDensityOperator.kuboMoriTransformLinear_apply
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : FiniteOperatorAlgebra n) :
    D.kuboMoriTransformLinear h_rpow A = D.kuboMoriTransform A :=
  rfl

/-- Finite dimensionality upgrades the integrated BKM linear operator to a
bounded continuous-linear operator without integrating in a function space. -/
noncomputable def FaithfulDensityOperator.kuboMoriTransformCLM
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    FiniteOperatorAlgebra n →L[ℂ] FiniteOperatorAlgebra n :=
  LinearMap.toContinuousLinearMap (D.kuboMoriTransformLinear h_rpow)

@[simp] theorem FaithfulDensityOperator.kuboMoriTransformCLM_apply
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : FiniteOperatorAlgebra n) :
    D.kuboMoriTransformCLM h_rpow A = D.kuboMoriTransform A :=
  rfl

theorem FaithfulDensityOperator.norm_kuboMoriTransform_le
    [NeZero n]
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow)
    (A : FiniteOperatorAlgebra n) :
    ‖D.kuboMoriTransform A‖ ≤
      ‖D.kuboMoriTransformCLM h_rpow‖ * ‖A‖ := by
  simpa using (D.kuboMoriTransformCLM h_rpow).le_opNorm A

/-- Continuous functional applying right multiplication by `B` and then the
finite operator trace. -/
def rightTraceCLM (B : FiniteOperatorAlgebra n) :
    FiniteOperatorAlgebra n →L[ℂ] ℂ :=
  (finiteOperatorTraceCLM n).comp
    ((ContinuousLinearMap.mul ℂ (FiniteOperatorAlgebra n)).flip B)

@[simp] theorem rightTraceCLM_apply
    (A B : FiniteOperatorAlgebra n) :
    rightTraceCLM B A = finiteOperatorTrace (A * B) :=
  rfl

/--
The scalar BKM pairing is exactly the finite trace pairing against the
operator-valued Kubo--Mori transform of `A†`.  This is the strict bridge from
the integrated operator channel to the existing scalar information metric.
-/
theorem FaithfulDensityOperator.kuboMoriPairing_eq_trace_kuboMoriTransform
    (D : FaithfulDensityOperator n)
    (A B : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow) :
    D.kuboMoriPairing A B =
      finiteOperatorTrace (D.kuboMoriTransform (star A) * B) := by
  have hIntegrable :=
    D.intervalIntegrable_modularInterpolation_of_continuous_rpow (star A) h_rpow
  calc
    D.kuboMoriPairing A B =
        ∫ s in (0 : ℝ)..1,
          rightTraceCLM B (D.modularInterpolation s (star A)) := by
            rfl
    _ = rightTraceCLM B
          (∫ s in (0 : ℝ)..1, D.modularInterpolation s (star A)) := by
            exact ContinuousLinearMap.intervalIntegral_comp_comm
              (rightTraceCLM B) hIntegrable
    _ = finiteOperatorTrace (D.kuboMoriTransform (star A) * B) := by
          rfl

end SouriauOnsagerBKM
