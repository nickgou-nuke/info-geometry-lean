import InfoGeometry.Canonical.JaynesRNMaxEnt
import InfoGeometry.Canonical.RelativePotentialScalarBridge

open MeasureTheory

/-!
# InfoGeometry.Canonical.JaynesRNModularBridge

Bridges the Jaynes/Gibbs exponential-family lane to the canonical scalar
modular-potential language.

The foundational object is the negative logarithmic Radon-Nikodym derivative.
The Jaynes potential appears here only as an affine presentation of that
modular potential, shifted by the logarithm of the partition function.
In the projective/Weyl reading, that logarithmic partition term is the scalar
gauge-fixing contribution selecting the normalized slice of the density ray.
-/

namespace InfoGeometry.Canonical.JaynesRNMaxEnt

open _root_.JaynesRNMaxEnt
open RelativePotentialScalarBridge

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ₀ : Measure Ω) [IsProbabilityMeasure μ₀]

section GibbsModular

variable {ι : Type*} [Fintype ι]
variable (C : MomentFamily (Ω := Ω) ι)

/--
Scalar modular potential of the explicit Gibbs RN density `exp(Φ) / Z`.

This is the pointwise scalar form of the negative logarithmic
Radon-Nikodym derivative. The `log Z` term is the scalar normalization mode:
it is the Weyl gauge correction coming from fixing the unit-mass section.
-/
theorem scalarModularPotential_exp_potential_div_partition
    (lam : ι → ℝ)
    (hInt : PartitionIntegrable (μ₀ := μ₀) (C := C) lam)
    (x : Ω) :
    scalarModularPotential
        (Real.exp (_root_.JaynesRNMaxEnt.potential (C := C) lam x) /
          partitionFunction (μ₀ := μ₀) (C := C) lam)
        (div_pos (Real.exp_pos _)
          (by
            simpa [partitionFunction, PartitionIntegrable] using
              (MeasureTheory.integral_exp_pos
                (μ := μ₀)
                (f := _root_.JaynesRNMaxEnt.potential (C := C) lam)
                hInt)))
      =
        -(_root_.JaynesRNMaxEnt.potential (C := C) lam x) +
          Real.log (partitionFunction (μ₀ := μ₀) (C := C) lam) := by
  have hZpos : 0 < partitionFunction (μ₀ := μ₀) (C := C) lam :=
    partitionFunction_pos (μ₀ := μ₀) (C := C) lam hInt
  rw [scalarModularPotential_eq_neg_log]
  rw [Real.log_div (Real.exp_pos _).ne'
      hZpos.ne',
    Real.log_exp]
  ring

/--
The negative logarithmic RN derivative of the Gibbs measure is the Jaynes
potential with the universal partition-function shift added.

This is the precise sense in which the Jaynes potential is not foundational:
it is an affine presentation of the modular potential, and the partition
term is the scalar gauge contribution rather than the essential generator.
-/
theorem neg_log_rnDeriv_gibbsMeasure_toReal_eq_neg_potential_add_logPartition
    (lam : ι → ℝ)
    (hInt : PartitionIntegrable (μ₀ := μ₀) (C := C) lam) :
    (fun x =>
      -Real.log (((gibbsMeasure (μ₀ := μ₀) (C := C) lam).rnDeriv μ₀ x).toReal))
      =ᵐ[μ₀]
        fun x =>
          -(_root_.JaynesRNMaxEnt.potential (C := C) lam x) +
            Real.log (partitionFunction (μ₀ := μ₀) (C := C) lam) := by
  have hZpos : 0 < partitionFunction (μ₀ := μ₀) (C := C) lam :=
    partitionFunction_pos (μ₀ := μ₀) (C := C) lam hInt
  filter_upwards
      [rnDeriv_gibbsMeasure_toReal_eq (μ₀ := μ₀) (C := C) lam] with x hx
  rw [hx]
  rw [Real.log_div (Real.exp_pos _).ne'
      hZpos.ne',
    Real.log_exp]
  ring

/--
Equivalent affine presentation: the Jaynes potential is the logarithmic
RN density plus the partition-function shift. This separates the invariant
modular content from the normalization chosen on the positive ray.
-/
theorem potential_eq_log_rnDeriv_gibbsMeasure_toReal_add_logPartition
    (lam : ι → ℝ)
    (hInt : PartitionIntegrable (μ₀ := μ₀) (C := C) lam) :
    (_root_.JaynesRNMaxEnt.potential (C := C) lam)
      =ᵐ[μ₀]
        fun x =>
          Real.log (((gibbsMeasure (μ₀ := μ₀) (C := C) lam).rnDeriv μ₀ x).toReal) +
            Real.log (partitionFunction (μ₀ := μ₀) (C := C) lam) := by
  have hZpos : 0 < partitionFunction (μ₀ := μ₀) (C := C) lam :=
    partitionFunction_pos (μ₀ := μ₀) (C := C) lam hInt
  filter_upwards
      [rnDeriv_gibbsMeasure_toReal_eq (μ₀ := μ₀) (C := C) lam] with x hx
  rw [hx]
  rw [Real.log_div (Real.exp_pos _).ne'
      hZpos.ne',
    Real.log_exp]
  ring

end GibbsModular

end InfoGeometry.Canonical.JaynesRNMaxEnt
