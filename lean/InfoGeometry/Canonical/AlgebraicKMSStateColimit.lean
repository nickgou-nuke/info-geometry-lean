import InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Delta-first algebraic KMS identity on the matrix colimit

This file starts from an invertible density element `δ`, not from a logarithmic
generator.  Mathlib's conjugation action supplies the imaginary-time algebra
automorphism

`x ↦ δ * x * δ⁻¹`.

Cyclicity of the normalized trace then proves the algebraic KMS boundary
identity directly.  No logarithm, one-parameter flow, analytic continuation,
or completed C*-algebra KMS state is inferred here.  Positivity and
normalization of a compatible weighted functional remain the separate finite
hypotheses proved by `CuntzMatrixCompatibleStateNet`.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.AlgebraicKMSStateColimit

open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

abbrev Carrier := CuntzMatrixAlgebraicStarColimit.Carrier

/-- The native inner algebra automorphism determined directly by an invertible
colimit density.  This is the `-i` boundary convention used below. -/
def deltaImaginaryTimeAlgEquiv (δ : Carrierˣ) : Carrier ≃ₐ[ℂ] Carrier :=
  MulSemiringAction.toAlgEquiv ℂ Carrier (ConjAct.toConjAct δ)

@[simp]
theorem deltaImaginaryTimeAlgEquiv_apply (δ : Carrierˣ) (x : Carrier) :
    deltaImaginaryTimeAlgEquiv δ x =
      (δ : Carrier) * x * ((δ⁻¹ : Carrierˣ) : Carrier) :=
  rfl

/-- The trace weighted on the right by the primary density element `δ`.
Cyclicity identifies this with the usual `x ↦ τ(δ * x)`. -/
def deltaWeightedFunctional (δ : Carrierˣ) : Carrier →ₗ[ℂ] ℂ :=
  traceFunctional ∘ₗ LinearMap.mulRight ℂ (δ : Carrier)

@[simp]
theorem deltaWeightedFunctional_apply (δ : Carrierˣ) (x : Carrier) :
    deltaWeightedFunctional δ x = traceFunctional (x * (δ : Carrier)) :=
  rfl

theorem deltaWeightedFunctional_eq_left_weight (δ : Carrierˣ) (x : Carrier) :
    deltaWeightedFunctional δ x = traceFunctional ((δ : Carrier) * x) := by
  rw [deltaWeightedFunctional_apply, traceFunctional_cyclic]

/-- Delta-first algebraic KMS boundary identity.  With the convention
`σ₋ᵢ(x) = δ * x * δ⁻¹`, one has `ωδ(xy) = ωδ(y σ₋ᵢ(x))`. -/
theorem deltaWeightedFunctional_kms (δ : Carrierˣ) (x y : Carrier) :
    deltaWeightedFunctional δ (x * y) =
      deltaWeightedFunctional δ (y * deltaImaginaryTimeAlgEquiv δ x) := by
  rw [deltaWeightedFunctional_eq_left_weight]
  rw [deltaWeightedFunctional_apply, deltaImaginaryTimeAlgEquiv_apply]
  calc
    traceFunctional ((δ : Carrier) * (x * y)) =
        traceFunctional (((δ : Carrier) * x) * y) := by rw [mul_assoc]
    _ = traceFunctional (y * ((δ : Carrier) * x)) :=
      traceFunctional_cyclic _ _
    _ = traceFunctional
        ((y * ((δ : Carrier) * x * ((δ⁻¹ : Carrierˣ) : Carrier))) *
          (δ : Carrier)) := by
      congr 1
      simp only [mul_assoc, Units.inv_mul, mul_one]

/-- Scalar normalization does not alter the algebraic KMS identity. -/
def normalizedDeltaWeightedFunctional (δ : Carrierˣ) : Carrier →ₗ[ℂ] ℂ :=
  (traceFunctional (δ : Carrier))⁻¹ • deltaWeightedFunctional δ

@[simp]
theorem normalizedDeltaWeightedFunctional_apply (δ : Carrierˣ) (x : Carrier) :
    normalizedDeltaWeightedFunctional δ x =
      (traceFunctional (δ : Carrier))⁻¹ * deltaWeightedFunctional δ x := by
  rfl

theorem normalizedDeltaWeightedFunctional_one (δ : Carrierˣ)
    (hδ : traceFunctional (δ : Carrier) ≠ 0) :
    normalizedDeltaWeightedFunctional δ (1 : Carrier) = 1 := by
  rw [normalizedDeltaWeightedFunctional_apply, deltaWeightedFunctional_apply,
    one_mul, inv_mul_cancel₀ hδ]

theorem normalizedDeltaWeightedFunctional_kms (δ : Carrierˣ) (x y : Carrier) :
    normalizedDeltaWeightedFunctional δ (x * y) =
      normalizedDeltaWeightedFunctional δ
        (y * deltaImaginaryTimeAlgEquiv δ x) := by
  rw [normalizedDeltaWeightedFunctional_apply,
    normalizedDeltaWeightedFunctional_apply, deltaWeightedFunctional_kms]

/-- A nonzero normalization trace packages the two defining properties of
the algebraic normalized KMS functional: normalization on the unit and the
imaginary-time boundary identity. -/
theorem normalizedDeltaWeightedFunctional_normalized_kms
    (δ : Carrierˣ) (hδ : traceFunctional (δ : Carrier) ≠ 0) :
    normalizedDeltaWeightedFunctional δ (1 : Carrier) = 1 ∧
      ∀ x y : Carrier,
        normalizedDeltaWeightedFunctional δ (x * y) =
          normalizedDeltaWeightedFunctional δ
            (y * deltaImaginaryTimeAlgEquiv δ x) := by
  constructor
  · exact normalizedDeltaWeightedFunctional_one δ hδ
  · intro x y
    exact normalizedDeltaWeightedFunctional_kms δ x y

/-- A finite-stage unit maps to a genuine unit of the algebraic colimit by the
native `Units.map` construction. -/
def stageUnitToColimit (n : ℕ) (δ : (MatrixStage n)ˣ) : Carrierˣ :=
  Units.map (stageInjection n).toMonoidHom δ

@[simp]
theorem stageUnitToColimit_coe (n : ℕ) (δ : (MatrixStage n)ˣ) :
    (stageUnitToColimit n δ : Carrier) =
      stageInjection n (δ : MatrixStage n) :=
  rfl

@[simp]
theorem deltaWeightedFunctional_stage (n : ℕ) (δ : (MatrixStage n)ˣ)
    (x : MatrixStage n) :
    deltaWeightedFunctional (stageUnitToColimit n δ) (stageInjection n x) =
      matrixTraceFunctional n (x * (δ : MatrixStage n)) := by
  rw [deltaWeightedFunctional_apply, stageUnitToColimit_coe,
    ← stageInjection_mul, traceFunctional_stage]
  rfl

/-- Normalized stage readback for the delta-weighted colimit functional. -/
theorem normalizedDeltaWeightedFunctional_stage
    (n : ℕ) (δ : (MatrixStage n)ˣ)
    (x : MatrixStage n) :
    normalizedDeltaWeightedFunctional (stageUnitToColimit n δ)
        (stageInjection n x) =
      (traceFunctional (stageUnitToColimit n δ : Carrier))⁻¹ *
        matrixTraceFunctional n (x * (δ : MatrixStage n)) := by
  rw [normalizedDeltaWeightedFunctional_apply,
    deltaWeightedFunctional_stage]

/-- A compatible density family has one well-defined image in the algebraic
colimit. -/
theorem densityCompatible_stageInjection
    (D : ∀ n : ℕ, MatrixStage n) (hD : DensityCompatible D) :
    ∀ n, stageInjection n (D n) = stageInjection 0 (D 0)
  | 0 => rfl
  | n + 1 => by
      rw [hD n]
      have hstep :
          stageInjection (n + 1) (concreteStep n (D n)) =
            stageInjection n (D n) := by
        simpa [concreteMap, map_succ, map_id] using
          (stageInjection_concrete_transition
            (Nat.le.step (le_refl n)) (D n))
      exact hstep.trans (densityCompatible_stageInjection D hD n)

/-- An invertible initial density gives the corresponding primary colimit
unit. -/
def densityColimitUnit (D : ∀ n : ℕ, MatrixStage n)
    (hD0 : IsUnit (D 0)) : Carrierˣ :=
  Units.map (stageInjection 0).toMonoidHom hD0.unit

@[simp]
theorem densityColimitUnit_coe (D : ∀ n : ℕ, MatrixStage n)
    (hD0 : IsUnit (D 0)) :
    (densityColimitUnit D hD0 : Carrier) = stageInjection 0 (D 0) := by
  simp [densityColimitUnit]

/-- The descended compatible weighted functional is exactly weighting by the
single colimit density unit. -/
theorem weightedColimitFunctional_eq_deltaWeighted
    (D : ∀ n : ℕ, MatrixStage n) (hD : DensityCompatible D)
    (hD0 : IsUnit (D 0)) :
    weightedColimitFunctional D
        (weightedStageFunctional_compatible_of_density_compatible D hD) =
      deltaWeightedFunctional (densityColimitUnit D hD0) := by
  apply LinearMap.ext
  intro x
  induction x using DirectLimit.induction with
  | _ n a =>
      change weightedColimitFunctional D
          (weightedStageFunctional_compatible_of_density_compatible D hD)
          (stageInjection n a) =
        deltaWeightedFunctional (densityColimitUnit D hD0)
          (stageInjection n a)
      rw [weightedColimitFunctional_stage, deltaWeightedFunctional_apply,
        densityColimitUnit_coe, ← densityCompatible_stageInjection D hD n,
        ← stageInjection_mul, traceFunctional_stage]
      rfl

/-- The compatible density-net functional satisfies the algebraic KMS
boundary identity without constructing `log δ`. -/
theorem weightedColimitFunctional_kms_of_density_compatible
    (D : ∀ n : ℕ, MatrixStage n) (hD : DensityCompatible D)
    (hD0 : IsUnit (D 0)) (x y : Carrier) :
    weightedColimitFunctional D
        (weightedStageFunctional_compatible_of_density_compatible D hD) (x * y) =
      weightedColimitFunctional D
        (weightedStageFunctional_compatible_of_density_compatible D hD)
        (y * deltaImaginaryTimeAlgEquiv (densityColimitUnit D hD0) x) := by
  rw [weightedColimitFunctional_eq_deltaWeighted D hD hD0,
    deltaWeightedFunctional_kms]

/-! ### The propagated finite Gibbs family

For the concrete tensor-propagated Hamiltonian, the density net is no longer
an external input: its compatibility follows from the native CFC transport
theorem and the actual matrix embeddings.
-/

def propagatedGibbsDensity
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) :
    ∀ n, MatrixStage n :=
  fun n => gibbsDensity (propagatedHamiltonian H₀ n)
    (propagatedHamiltonian_isHermitian H₀ h₀ n) β

theorem propagatedGibbsDensity_compatible
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) :
    DensityCompatible (propagatedGibbsDensity H₀ h₀ β) := by
  intro n
  exact (gibbsDensity_concreteStep n
    (propagatedHamiltonian H₀ n)
    (propagatedHamiltonian H₀ (n + 1))
    (propagatedHamiltonian_isHermitian H₀ h₀ n)
    (propagatedHamiltonian_isHermitian H₀ h₀ (n + 1))
    (propagatedHamiltonian_compatible H₀ n) β).symm

theorem propagatedGibbsDensity_unit_zero
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) :
    IsUnit (propagatedGibbsDensity H₀ h₀ β 0) := by
  exact gibbsDensity_isUnit H₀ h₀ β

/-- The propagated Gibbs density has a nonzero colimit trace normalizer.
This is read back from the finite stage, where the Gibbs partition function
is nonzero. -/
theorem propagatedGibbsDensity_colimit_trace_ne_zero
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) :
    traceFunctional
        (densityColimitUnit
          (propagatedGibbsDensity H₀ h₀ β)
          (propagatedGibbsDensity_unit_zero H₀ h₀ β) : Carrier) ≠ 0 := by
  rw [densityColimitUnit_coe, traceFunctional_stage,
    matrixTraceState_apply]
  apply mul_ne_zero
  · norm_num
  · exact gibbsPartition_ne_zero
      (propagatedHamiltonian H₀ 0)
      (propagatedHamiltonian_isHermitian H₀ h₀ 0) β

/-- The propagated Gibbs density therefore gives a normalized algebraic KMS
functional on the colimit. -/
theorem propagatedGibbsDensity_normalized_one
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) :
    normalizedDeltaWeightedFunctional
        (densityColimitUnit
          (propagatedGibbsDensity H₀ h₀ β)
          (propagatedGibbsDensity_unit_zero H₀ h₀ β))
        (1 : Carrier) = 1 := by
  apply normalizedDeltaWeightedFunctional_one
  exact propagatedGibbsDensity_colimit_trace_ne_zero H₀ h₀ β

/-! The positivity proof is stagewise and genuinely noncommutative: it uses
the positive-semidefinite Gibbs density and cyclicity of the matrix trace.
This is the finite witness required by the direct-limit positivity theorem. -/

theorem propagatedGibbsDensity_stage_positive
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ)
    (n : ℕ) (x : MatrixStage n) :
    0 ≤
      (matrixTraceFunctional n
        (star x * x * propagatedGibbsDensity H₀ h₀ β n)).re := by
  have hD := Matrix.nonneg_iff_posSemidef.mp
    (gibbsDensity_nonneg
      (propagatedHamiltonian H₀ n)
      (propagatedHamiltonian_isHermitian H₀ h₀ n) β)
  have htrace :
      0 ≤
        (Matrix.trace
          (propagatedGibbsDensity H₀ h₀ β n * (star x * x))).re := by
    have h := weightedTrace_nonneg
      (propagatedGibbsDensity H₀ h₀ β n) hD x
    simpa [weightedTrace_apply] using h
  have hcycle :
      Matrix.trace
          (star x * x * propagatedGibbsDensity H₀ h₀ β n) =
        Matrix.trace
          (propagatedGibbsDensity H₀ h₀ β n * (star x * x)) := by
    exact Matrix.trace_mul_comm
      (star x * x) (propagatedGibbsDensity H₀ h₀ β n)
  rw [matrixTraceFunctional_apply, hcycle]
  have hcast :
      (1 / (2 ^ n : ℂ)) =
        ((1 / (2 ^ n : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hcre : (1 / (2 ^ n : ℂ)).re = 1 / (2 ^ n : ℝ) := by
    rw [hcast, Complex.ofReal_re]
  have hcim : (1 / (2 ^ n : ℂ)).im = 0 := by
    rw [hcast, Complex.ofReal_im]
  rw [Complex.mul_re, hcre, hcim, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) htrace

theorem propagatedGibbsDensity_colimit_positive
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ)
    (x : Carrier) :
    0 ≤
      (weightedColimitFunctional
        (propagatedGibbsDensity H₀ h₀ β)
        (weightedStageFunctional_compatible_of_density_compatible
          (propagatedGibbsDensity H₀ h₀ β)
          (propagatedGibbsDensity_compatible H₀ h₀ β))
        (star x * x)).re := by
  exact weightedColimitFunctional_positive
    (propagatedGibbsDensity H₀ h₀ β)
    (weightedStageFunctional_compatible_of_density_compatible
      (propagatedGibbsDensity H₀ h₀ β)
      (propagatedGibbsDensity_compatible H₀ h₀ β))
    (fun n y => propagatedGibbsDensity_stage_positive H₀ h₀ β n y) x

theorem propagatedGibbsDensity_kms
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ)
    (x y : Carrier) :
    weightedColimitFunctional (propagatedGibbsDensity H₀ h₀ β)
        (weightedStageFunctional_compatible_of_density_compatible
          (propagatedGibbsDensity H₀ h₀ β)
          (propagatedGibbsDensity_compatible H₀ h₀ β)) (x * y) =
      weightedColimitFunctional (propagatedGibbsDensity H₀ h₀ β)
        (weightedStageFunctional_compatible_of_density_compatible
          (propagatedGibbsDensity H₀ h₀ β)
          (propagatedGibbsDensity_compatible H₀ h₀ β))
        (y * deltaImaginaryTimeAlgEquiv
          (densityColimitUnit (propagatedGibbsDensity H₀ h₀ β)
            (propagatedGibbsDensity_unit_zero H₀ h₀ β)) x) := by
  exact weightedColimitFunctional_kms_of_density_compatible
    (propagatedGibbsDensity H₀ h₀ β)
    (propagatedGibbsDensity_compatible H₀ h₀ β)
    (propagatedGibbsDensity_unit_zero H₀ h₀ β) x y

/-- The propagated finite Gibbs family gives the complete normalized KMS
packet on the native algebraic colimit. -/
theorem propagatedGibbsDensity_normalized_kms
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) :
    normalizedDeltaWeightedFunctional
        (densityColimitUnit
          (propagatedGibbsDensity H₀ h₀ β)
          (propagatedGibbsDensity_unit_zero H₀ h₀ β))
        (1 : Carrier) = 1 ∧
      ∀ x y : Carrier,
        normalizedDeltaWeightedFunctional
            (densityColimitUnit
              (propagatedGibbsDensity H₀ h₀ β)
              (propagatedGibbsDensity_unit_zero H₀ h₀ β)) (x * y) =
          normalizedDeltaWeightedFunctional
            (densityColimitUnit
              (propagatedGibbsDensity H₀ h₀ β)
              (propagatedGibbsDensity_unit_zero H₀ h₀ β))
            (y * deltaImaginaryTimeAlgEquiv
              (densityColimitUnit
                (propagatedGibbsDensity H₀ h₀ β)
                (propagatedGibbsDensity_unit_zero H₀ h₀ β)) x) := by
  exact normalizedDeltaWeightedFunctional_normalized_kms _
    (propagatedGibbsDensity_colimit_trace_ne_zero H₀ h₀ β)

end InfoGeometry.Canonical.AlgebraicKMSStateColimit
