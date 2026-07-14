import InfoGeometry.Canonical.JaynesRNMaxEnt
import InfoGeometry.MaxEnt.Core
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.PrimeGasMaxEnt

Owner-facing MaxEnt bridge for the prime-occupation gas.

This module keeps the prime gas on the actual JaynesRNMaxEnt surface:

- the carrier is an arbitrary measurable space,
- the constraints are two explicit moments: energy and particle number,
- the partition function and Gibbs measure are the existing Jaynes objects,
- the Euler-product claim remains an explicit hypothesis and is not promoted
  to a theorem.

The intent is to provide the missing partition-function owner surface without
collapsing the infinite carrier into a finite toy model.
-/

namespace PrimeGasMaxEnt

open MeasureTheory
open InfoGeometry.MaxEnt
open InfoGeometry.MaxEnt.JaynesRNMaxEnt

universe u

/--
Discrete symmetry packet for the prime-occupation Jaynes problem.

The `V4` field is the primitive Klein-four reflection skeleton.  The tensor
flags record product copies of that discrete symmetry.  The Möbius/Klein fields
record the nonorientable discrete twist separately from the reflection skeleton.
-/
@[rep_depth transport]
structure PrimeGasSymmetry where
  V4_Weyl : Prop
  V4_tensor_V4 : Prop
  V4_tensor_V4_tensor_V4 : Prop
  kleinBottleQuotient : Prop
  moebiusDiscreteTwist : Prop
  splitCl11Atom : Prop

/--
Explicit Jaynes data for the prime-occupation gas.

The carrier is arbitrary and measurable.  The energy and particle-number
readouts are explicit moment constraints.  The analytic number theory claim
(`eulerProductPartition`) remains quarantined as a hypothesis.
-/
@[rep_depth thermo]
structure PrimeGasJaynesData where
  Ω : Type u
  instMeasurableSpace : MeasurableSpace Ω
  μ₀ : ProbabilityMeasure Ω
  energy : LinearConstraint Ω
  particleNumber : LinearConstraint Ω
  symmetry : PrimeGasSymmetry
  idealFermionGas : Prop
  primeOccupationLogEnergy : Prop
  eulerProductPartition : Prop

namespace PrimeGasJaynesData

variable (D : PrimeGasJaynesData)

instance : MeasurableSpace D.Ω := D.instMeasurableSpace

/--
Two-constraint Jaynes family for the prime gas.

We keep the family finite (energy, particle number) while the carrier remains
dimension-agnostic and measure-theoretic.
-/
@[rep_depth thermo]
noncomputable def momentFamily : MomentFamily (Ω := D.Ω) Bool where
  f := fun b => if b then D.energy.f else D.particleNumber.f
  measurable_f := by
    intro b
    cases b
    · simpa using D.particleNumber.measurable_f
    · simpa using D.energy.measurable_f
  d := fun b => if b then D.energy.c else D.particleNumber.c

/-- The prime gas Jaynes partition function. -/
@[rep_depth thermo]
noncomputable def partitionFunction (lam : Bool → ℝ) : ℝ :=
  InfoGeometry.MaxEnt.JaynesRNMaxEnt.partitionFunction
    (μ₀ := (D.μ₀ : Measure D.Ω)) (C := D.momentFamily) lam

/-- Integrability gate for the prime gas partition function. -/
@[rep_depth thermo]
def PartitionIntegrable (lam : Bool → ℝ) : Prop :=
  InfoGeometry.MaxEnt.JaynesRNMaxEnt.PartitionIntegrable
    (μ₀ := (D.μ₀ : Measure D.Ω)) (C := D.momentFamily) lam

/-- The prime gas Gibbs measure as a Jaynes measure on the explicit carrier. -/
@[rep_depth thermo]
noncomputable def gibbsMeasure (lam : Bool → ℝ) : Measure D.Ω :=
  InfoGeometry.MaxEnt.JaynesRNMaxEnt.gibbsMeasure
    (μ₀ := (D.μ₀ : Measure D.Ω)) (C := D.momentFamily) lam

/-- The prime gas Gibbs probability measure. -/
@[rep_depth thermo]
noncomputable def gibbsProbability (lam : Bool → ℝ)
    (hInt : PartitionIntegrable (D := D) lam) : ProbabilityMeasure D.Ω :=
  InfoGeometry.MaxEnt.JaynesRNMaxEnt.gibbs
    (μ₀ := (D.μ₀ : Measure D.Ω)) (C := D.momentFamily) lam hInt

/-- The prime gas partition function is strictly positive on the integrable branch. -/
@[rep_depth thermo]
theorem partitionFunction_pos (lam : Bool → ℝ)
    (hInt : PartitionIntegrable (D := D) lam) :
    0 < partitionFunction (D := D) lam := by
  simpa [partitionFunction, PartitionIntegrable] using
    (InfoGeometry.MaxEnt.JaynesRNMaxEnt.partitionFunction_pos
      (μ₀ := (D.μ₀ : Measure D.Ω)) (C := D.momentFamily) lam hInt)

/-- The prime gas Gibbs measure is absolutely continuous w.r.t. the prior. -/
@[rep_depth thermo]
theorem gibbsMeasure_ac (lam : Bool → ℝ) :
    gibbsMeasure (D := D) lam ≪ (D.μ₀ : Measure D.Ω) := by
  simpa [gibbsMeasure] using
    (InfoGeometry.MaxEnt.JaynesRNMaxEnt.gibbsMeasure_ac
      (μ₀ := (D.μ₀ : Measure D.Ω)) (C := D.momentFamily) lam)

/-- The Gibbs RN-derivative is the exponential family density over the prime gas. -/
@[rep_depth thermo]
theorem rnDeriv_gibbsMeasure_eq (lam : Bool → ℝ) :
    (gibbsMeasure (D := D) lam).rnDeriv (D.μ₀ : Measure D.Ω)
      =ᵐ[(D.μ₀ : Measure D.Ω)] fun x =>
        ENNReal.ofReal
          (Real.exp (potential (C := D.momentFamily) lam x)
            / partitionFunction (D := D) lam) := by
  simpa [gibbsMeasure, partitionFunction] using
    (InfoGeometry.MaxEnt.JaynesRNMaxEnt.rnDeriv_gibbsMeasure_eq
      (μ₀ := (D.μ₀ : Measure D.Ω)) (C := D.momentFamily) lam)

/-- Scalar RN-density form for the prime gas Gibbs measure. -/
@[rep_depth thermo]
theorem rnDeriv_gibbsMeasure_toReal_eq (lam : Bool → ℝ) :
    (fun x => ((gibbsMeasure (D := D) lam).rnDeriv (D.μ₀ : Measure D.Ω) x).toReal)
      =ᵐ[(D.μ₀ : Measure D.Ω)] fun x =>
        Real.exp (potential (C := D.momentFamily) lam x)
          / partitionFunction (D := D) lam := by
  simpa [gibbsMeasure, partitionFunction] using
    (InfoGeometry.MaxEnt.JaynesRNMaxEnt.rnDeriv_gibbsMeasure_toReal_eq
      (μ₀ := (D.μ₀ : Measure D.Ω)) (C := D.momentFamily) lam)

/--
The prime gas partition-function bridge.

This packages the MaxEnt, Gibbs, and symmetry surfaces together while keeping
the Euler-product claim quarantined as a separate hypothesis field.
-/
@[rep_depth thermo]
structure PrimeGasPartitionPacket where
  lam : Bool → ℝ
  hInt : PartitionIntegrable (D := D) lam
  partitionFunction_pos : 0 < partitionFunction (D := D) lam
  gibbsProbability : ProbabilityMeasure D.Ω
  rnDeriv_gibbsMeasure_eq :
    (gibbsMeasure (D := D) lam).rnDeriv (D.μ₀ : Measure D.Ω)
      =ᵐ[(D.μ₀ : Measure D.Ω)] fun x =>
        ENNReal.ofReal
          (Real.exp (potential (C := D.momentFamily) lam x)
            / partitionFunction (D := D) lam)

/--
Explicit prime-gas Jaynes hypothesis packet.

The analytic number theory claim is still a hypothesis; the MaxEnt partition
and Gibbs surfaces are owned by the module above.
-/
@[rep_depth thermo]
def PrimeGasJaynesConjecture : Prop :=
  ∃ (P : ProbabilityMeasure D.Ω) (lam : Bool → ℝ)
      (hInt : PartitionIntegrable (D := D) lam),
    P = gibbsProbability (D := D) lam hInt ∧
      D.symmetry.V4_Weyl ∧
      D.symmetry.V4_tensor_V4 ∧
      D.symmetry.V4_tensor_V4_tensor_V4 ∧
      D.symmetry.kleinBottleQuotient ∧
      D.symmetry.moebiusDiscreteTwist ∧
      D.symmetry.splitCl11Atom ∧
      D.idealFermionGas ∧
      D.primeOccupationLogEnergy ∧
      D.eulerProductPartition

end PrimeGasJaynesData

end PrimeGasMaxEnt
