import InfoGeometry.Canonical.JaynesRNMaxEnt
import InfoGeometry.MaxEnt.Core
import InfoGeometry.Meta.Architecture
import InfoGeometry.BostConnes.BostConnesParity
import InfoGeometry.Topology.V4RootSystem

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

namespace InfoGeometry.Canonical.PrimeGasMaxEnt

open MeasureTheory
open InfoGeometry.MaxEnt
open _root_.JaynesRNMaxEnt

universe u

/--
Discrete symmetry packet for the prime-occupation Jaynes problem.

The `V4` field is the primitive Klein-four reflection skeleton.  The tensor
flags record product copies of that discrete symmetry.  The Möbius/Klein fields
record the nonorientable discrete twist separately from the reflection skeleton.
-/
@[rep_depth transport]
structure PrimeGasSymmetry where
  weyl : InfoGeometry.Topology.V4RootSystem.V4Group
  weyl_involution :
    weyl * weyl = InfoGeometry.Topology.V4RootSystem.V4Group.I
  moebiusParity : ℕ → ℤ
  moebiusParity_spec :
    ∀ n,
      ArithmeticFunction.moebius n =
        InfoGeometry.BostConnes.squarefreeProj n * moebiusParity n

/-- Canonical V4/Möbius symmetry data owned by the finite source modules. -/
def canonicalPrimeGasSymmetry : PrimeGasSymmetry where
  weyl := InfoGeometry.Topology.V4RootSystem.V4Group.W12
  weyl_involution :=
    InfoGeometry.Topology.V4RootSystem.v4_point_inversion_involution
  moebiusParity := InfoGeometry.BostConnes.liouvilleParity
  moebiusParity_spec :=
    InfoGeometry.BostConnes.moebius_eq_squarefreeProj_mul_liouvilleParity

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

namespace PrimeGasJaynesData

variable (D : PrimeGasJaynesData)

instance : MeasurableSpace D.Ω := D.instMeasurableSpace

/--
Two-constraint Jaynes family for the prime gas.

We keep the family finite (energy, particle number) while the carrier remains
dimension-agnostic and measure-theoretic.
-/
@[rep_depth thermo]
noncomputable def momentFamily :
    @JaynesRNMaxEnt.MomentFamily D.Ω inferInstance Bool inferInstance := by
  refine
    { f := fun b => if b then D.energy.f else D.particleNumber.f
      measurable_f := ?_
      d := fun b => if b then D.energy.c else D.particleNumber.c }
  intro b
  cases b
  · simpa using D.particleNumber.measurable_f
  · simpa using D.energy.measurable_f

/-- The prime gas Jaynes partition function. -/
@[rep_depth thermo]
noncomputable def partitionFunction (lam : Bool → ℝ) : ℝ :=
  JaynesRNMaxEnt.partitionFunction
    (μ₀ := (D.μ₀ : Measure D.Ω)) (C := momentFamily D) lam

/-- Integrability gate for the prime gas partition function. -/
@[rep_depth thermo]
def PartitionIntegrable (lam : Bool → ℝ) : Prop :=
  JaynesRNMaxEnt.PartitionIntegrable
    (μ₀ := (D.μ₀ : Measure D.Ω)) (C := momentFamily D) lam

/-- The prime gas Gibbs measure as a Jaynes measure on the explicit carrier. -/
@[rep_depth thermo]
noncomputable def gibbsMeasure (lam : Bool → ℝ) : Measure D.Ω :=
  JaynesRNMaxEnt.gibbsMeasure
    (μ₀ := (D.μ₀ : Measure D.Ω)) (C := momentFamily D) lam

/-- The prime gas Gibbs probability measure. -/
@[rep_depth thermo]
noncomputable def gibbsProbability (lam : Bool → ℝ)
    (hInt : PartitionIntegrable D lam) : ProbabilityMeasure D.Ω :=
  JaynesRNMaxEnt.gibbs
    (μ₀ := (D.μ₀ : Measure D.Ω)) (C := momentFamily D) lam hInt

/-- The prime gas partition function is strictly positive on the integrable branch. -/
@[rep_depth thermo]
theorem partitionFunction_pos (lam : Bool → ℝ)
    (hInt : PartitionIntegrable D lam) :
    0 < partitionFunction D lam := by
  simpa [partitionFunction, PartitionIntegrable] using
    (JaynesRNMaxEnt.partitionFunction_pos
      (μ₀ := (D.μ₀ : Measure D.Ω)) (C := momentFamily D) lam hInt)

/-- The prime gas Gibbs measure is absolutely continuous w.r.t. the prior. -/
@[rep_depth thermo]
theorem gibbsMeasure_ac (lam : Bool → ℝ) :
    gibbsMeasure D lam ≪ (D.μ₀ : Measure D.Ω) := by
  simpa [gibbsMeasure] using
    (JaynesRNMaxEnt.gibbsMeasure_ac
      (μ₀ := (D.μ₀ : Measure D.Ω)) (C := momentFamily D) lam)

/-- The Gibbs RN-derivative is the exponential family density over the prime gas. -/
@[rep_depth thermo]
theorem rnDeriv_gibbsMeasure_eq (lam : Bool → ℝ) :
    (gibbsMeasure D lam).rnDeriv (D.μ₀ : Measure D.Ω)
      =ᵐ[(D.μ₀ : Measure D.Ω)] fun x =>
        ENNReal.ofReal
          (Real.exp (potential (C := momentFamily D) lam x)
            / partitionFunction D lam) := by
  simpa [gibbsMeasure, partitionFunction] using
    (JaynesRNMaxEnt.rnDeriv_gibbsMeasure_eq
      (μ₀ := (D.μ₀ : Measure D.Ω)) (C := momentFamily D) lam)

/-- Scalar RN-density form for the prime gas Gibbs measure. -/
@[rep_depth thermo]
theorem rnDeriv_gibbsMeasure_toReal_eq (lam : Bool → ℝ) :
    (fun x => ((gibbsMeasure D lam).rnDeriv (D.μ₀ : Measure D.Ω) x).toReal)
      =ᵐ[(D.μ₀ : Measure D.Ω)] fun x =>
        Real.exp (potential (C := momentFamily D) lam x)
          / partitionFunction D lam := by
  simpa [gibbsMeasure, partitionFunction] using
    (JaynesRNMaxEnt.rnDeriv_gibbsMeasure_toReal_eq
      (μ₀ := (D.μ₀ : Measure D.Ω)) (C := momentFamily D) lam)

/--
The prime gas partition-function bridge.

This packages the MaxEnt, Gibbs, and symmetry surfaces together while keeping
the Euler-product claim quarantined as a separate hypothesis field.
-/
@[rep_depth thermo]
structure PrimeGasPartitionPacket where
  lam : Bool → ℝ
  hInt : PartitionIntegrable D lam
  partitionFunction_pos : 0 < partitionFunction D lam
  gibbsProbability : ProbabilityMeasure D.Ω
  rnDeriv_gibbsMeasure_eq :
    (gibbsMeasure D lam).rnDeriv (D.μ₀ : Measure D.Ω)
      =ᵐ[(D.μ₀ : Measure D.Ω)] fun x =>
        ENNReal.ofReal
          (Real.exp (potential (C := momentFamily D) lam x)
            / partitionFunction D lam)

/--
Explicit prime-gas Jaynes hypothesis packet.

The analytic number theory claim is still a hypothesis; the MaxEnt partition
and Gibbs surfaces are owned by the module above.
-/
@[rep_depth thermo]
def PrimeGasJaynesConjecture : Prop :=
  ∃ (P : ProbabilityMeasure D.Ω) (lam : Bool → ℝ)
      (hInt : PartitionIntegrable D lam),
    P = gibbsProbability D lam hInt

end PrimeGasJaynesData

end InfoGeometry.Canonical.PrimeGasMaxEnt
