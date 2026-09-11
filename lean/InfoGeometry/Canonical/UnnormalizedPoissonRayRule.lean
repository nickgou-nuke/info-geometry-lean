import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PowerVarianceCumulants
import InfoGeometry.External.Auto.PoissonGaussianGNSColimit
import InfoGeometry.Inference.FisherPositivity
import InfoGeometry.Neurosymbolic.BornNMFEngine
import InfoGeometry.Quantum.QutritMeasurement
import Mathlib.Data.Matrix.Basic

/-!
# Unnormalized states and rays

This owner separates two pieces of finite positive data:

* `ray`, supplied by the existing positive projective quotient;
* `intensity`, retained as a positive scalar and therefore not quotiented away.

The matrix layer records the corresponding Poisson mean decomposition
`Λ = R • K + B`, while adapters below reuse the existing Poisson PMF,
cumulant, Fisher, and qutrit Born owners. Bundle-level structures remain
owned by the prequantum and Klein associated-bundle modules; this file only
supplies the scale-preserving coordinate bridge.
-/

namespace InfoGeometry.Canonical.UnnormalizedPoissonRayRule

open InfoGeometry.Canonical.PositiveRayCore

universe u

section PositiveRays

variable {α : Type u} [Fintype α] [Nonempty α]

/-- A positive projective ray together with its retained evidence scale. -/
structure UnnormalizedRayState where
  ray : PositiveRay α
  intensity : ℝ
  intensity_pos : 0 < intensity

/-- The canonical positive representative carrying the retained intensity. -/
noncomputable def representative (s : UnnormalizedRayState (α := α)) :
    InfoGeometry.PositiveMeasure α ℝ :=
  InfoGeometry.PositiveMeasure.scale s.intensity s.intensity_pos
    (gaugeSection (α := α) s.ray)

theorem representative_mass (s : UnnormalizedRayState (α := α)) :
    InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) (representative s) =
      s.intensity := by
  rw [representative, InfoGeometry.PositiveMeasure.Z_scale]
  rw [Z_gaugeSection]
  simp

theorem representative_normalize (s : UnnormalizedRayState (α := α)) :
    InfoGeometry.PositiveMeasure.normalize (representative s) =
      gaugeSection (α := α) s.ray := by
  ext a
  rw [InfoGeometry.PositiveMeasure.normalize_apply]
  change (s.intensity * gaugeSection (α := α) s.ray a) /
      InfoGeometry.PositiveMeasure.Z
        (InfoGeometry.PositiveMeasure.scale s.intensity s.intensity_pos
          (gaugeSection (α := α) s.ray)) = gaugeSection (α := α) s.ray a
  rw [InfoGeometry.PositiveMeasure.Z_scale, Z_gaugeSection]
  rw [mul_one]
  apply (div_eq_iff s.intensity_pos.ne').2
  ring

end PositiveRays

section PoissonIntensity

open InfoGeometry.Neurosymbolic.BornNMFEngine

variable {m n : Type*}

/-- Unnormalized Poisson mean: a retained scale times a ray kernel plus background. -/
def poissonIntensity (R : ℝ) (K B : Matrix m n ℝ) : Matrix m n ℝ :=
  R • K + B

@[simp] theorem poissonIntensity_apply (R : ℝ) (K B : Matrix m n ℝ)
    (i : m) (j : n) :
    poissonIntensity R K B i j = R * K i j + B i j := by
  rfl

theorem poissonIntensity_nonneg
    (R : ℝ) (K B : Matrix m n ℝ)
    (hR : 0 ≤ R) (hK : MatrixNonneg K) (hB : MatrixNonneg B) :
    MatrixNonneg (poissonIntensity R K B) := by
  intro i j
  rw [poissonIntensity_apply]
  exact add_nonneg (mul_nonneg hR (hK i j)) (hB i j)

theorem poissonIntensity_scale_injective
    {R S : ℝ} {K B : Matrix m n ℝ}
    (hK : ∃ i j, K i j ≠ 0)
    (h : poissonIntensity R K B = poissonIntensity S K B) :
    R = S := by
  rcases hK with ⟨i, j, hij⟩
  have hentry := congrArg (fun M : Matrix m n ℝ => M i j) h
  change R * K i j + B i j = S * K i j + B i j at hentry
  have hdiff : (R - S) * K i j = 0 := by
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right hij)

/-- A normalized kernel alone does not encode the retained intensity. -/
theorem poissonIntensity_same_kernel_different_scale
    {R S : ℝ} (hRS : R ≠ S) (K B : Matrix m n ℝ)
    (hK : ∃ i j, K i j ≠ 0) :
    poissonIntensity R K B ≠ poissonIntensity S K B := by
  intro h
  exact hRS (poissonIntensity_scale_injective (K := K) (B := B) hK h)

end PoissonIntensity

/-! Existing statistical owners, exposed here without redefining them. -/

theorem poisson_cumulant_two_eq_mean (μ : ℝ) :
    InfoGeometry.Canonical.poissonCumulant μ 2 = μ := by
  exact InfoGeometry.Canonical.poissonCumulant_eq μ (by omega)

theorem poisson_mass_nonneg_of_nonneg_rate
    (lam : ℝ) (hLam : 0 ≤ lam) (k : ℕ) :
    0 ≤ poissonPMF lam k := by
  exact poissonPMF_nonneg lam hLam k

theorem fisher_quadratic_nonneg_of_nonneg_weights
    {Data : Type*} [Fintype Data]
    (w : Data → ℝ) (sensitivity : Data → Fin 2 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (v : Fin 2 → ℝ) :
    0 ≤ ∑ a : Fin 2, ∑ b : Fin 2,
      v a * InfoGeometry.Inference.fisherInformation w sensitivity a b * v b := by
  exact InfoGeometry.Inference.fisherInformation_quadratic_nonneg
    w sensitivity hw v

section QutritBornScale

open InfoGeometry.Quantum.Qutrit

/-- The Born probabilities supply the ray shape; `R` retains its mass. -/
noncomputable def unnormalizedQutritIntensity
    (R : ℝ) (ψ : QutritState) (i : Fin 3) : ℝ :=
  R * computationalProbability ψ i

theorem unnormalizedQutritIntensity_nonneg
    (R : ℝ) (hR : 0 ≤ R) (ψ : QutritState) (i : Fin 3) :
    0 ≤ unnormalizedQutritIntensity R ψ i := by
  exact mul_nonneg hR (computationalProbability_nonneg ψ i)

theorem unnormalizedQutritIntensity_sum
    (R : ℝ) (ψ : QutritState) :
    ∑ i : Fin 3, unnormalizedQutritIntensity R ψ i = R := by
  simp only [unnormalizedQutritIntensity, ← Finset.mul_sum]
  rw [sum_computationalProbability]
  simp

end QutritBornScale

end InfoGeometry.Canonical.UnnormalizedPoissonRayRule
