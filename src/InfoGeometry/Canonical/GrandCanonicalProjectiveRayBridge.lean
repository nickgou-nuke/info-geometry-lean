/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.GrandCanonicalPrimeEnsembleFormulas
import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Projective.GibbsRayGeometry

/-!
# Grand-canonical finite ensembles on positive projective rays

The Boltzmann weights define a strictly positive finite measure.  Its total
mass is the partition function, while its positive ray forgets that radial
scale.  The canonical gauge section of the ray recovers exactly the Gibbs
probability distribution.

This file identifies the existing ensemble and projective owners; it does not
identify the operator-valued Peirce logistic element with a scalar state
readout.
-/

noncomputable section

namespace InfoGeometry.Canonical.GrandCanonicalProjectiveRayBridge

open scoped BigOperators
open InfoGeometry.Canonical.GrandCanonicalPrimeEnsembleFormulas
open InfoGeometry.Projective.GibbsRayGeometry
open InfoGeometry.Projective.ExpectationRatioMetric
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.GrandCanonical

variable {State : Type*} [Fintype State] [Nonempty State]

/-- The unnormalized grand-canonical Boltzmann weights as a positive measure. -/
def boltzmannMeasure (energy particleNumber : State → ℝ)
    (beta chemicalPotential : ℝ) : InfoGeometry.PositiveMeasure State ℝ where
  mass x := boltzmannWeight energy particleNumber beta chemicalPotential x
  pos x := boltzmannWeight_pos energy particleNumber beta chemicalPotential x

/-- The projective positive ray represented by the finite Boltzmann measure. -/
def ensembleRay (energy particleNumber : State → ℝ)
    (beta chemicalPotential : ℝ) : PositiveRay State :=
  ray (boltzmannMeasure energy particleNumber beta chemicalPotential)

/-- The finite partition function is the total mass of the Boltzmann representative. -/
theorem partitionFunction_eq_measureMass
    (energy particleNumber : State → ℝ) (beta chemicalPotential : ℝ) :
    partitionFunction energy particleNumber beta chemicalPotential =
      InfoGeometry.PositiveMeasure.Z
        (boltzmannMeasure energy particleNumber beta chemicalPotential) := by
  rfl

/-- Normalizing the ensemble ray recovers the existing Gibbs probabilities pointwise. -/
@[simp] theorem gaugeSection_ensembleRay_apply
    (energy particleNumber : State → ℝ) (beta chemicalPotential : ℝ)
    (hZ : 0 < partitionFunction energy particleNumber beta chemicalPotential)
    (x : State) :
    gaugeSection (ensembleRay energy particleNumber beta chemicalPotential) x =
      gibbsProbability energy particleNumber beta chemicalPotential hZ x := by
  simp [ensembleRay, gaugeSection, boltzmannMeasure,
    InfoGeometry.Projective.ExpectationRatioMetric.ray,
    InfoGeometry.Projective.Normalize.normalizeOnProj_mk,
    InfoGeometry.PositiveMeasure.normalize_apply,
    InfoGeometry.PositiveMeasure.Z, partitionFunction, gibbsProbability]

/-- The canonical ensemble as a grand-canonical ensemble with zero number
observable and zero chemical potential. -/
def canonicalEnsembleRay (params : GrandCanonicalParams State) (beta : ℝ) :
    PositiveRay State :=
  ensembleRay params.energy (fun _ => 0) beta 0

/-- The canonical projective ray's normalized representative is the existing
finite canonical Gibbs weight. -/
@[simp] theorem gaugeSection_canonicalEnsembleRay_apply
    (params : GrandCanonicalParams State) (beta : ℝ) (x : State) :
    gaugeSection (canonicalEnsembleRay params beta) x = gibbsWeight params beta x := by
  have hZ : 0 < partitionFunction params.energy (fun _ => 0) beta 0 := by
    simpa [partitionFunction, boltzmannWeight, effectiveEnergy, partition] using
      (partition_pos params beta)
  rw [canonicalEnsembleRay, gaugeSection_ensembleRay_apply
    params.energy (fun _ => 0) beta 0 hZ x]
  simp [gibbsWeight, gibbsProbability, partitionFunction, boltzmannWeight,
    effectiveEnergy, partition]

/-- The ensemble ray has a unique unit-mass representative given by its Gibbs law. -/
theorem gaugeSection_ensembleRay_eq_gibbsMeasure
    (energy particleNumber : State → ℝ) (beta chemicalPotential : ℝ)
    (hZ : 0 < partitionFunction energy particleNumber beta chemicalPotential) :
    gaugeSection (ensembleRay energy particleNumber beta chemicalPotential) =
      ⟨gibbsProbability energy particleNumber beta chemicalPotential hZ,
        fun x => by
          rw [gibbsProbability]
          exact div_pos
            (boltzmannWeight_pos energy particleNumber beta chemicalPotential x) hZ⟩ := by
  apply InfoGeometry.PositiveMeasure.ext
  funext x
  exact gaugeSection_ensembleRay_apply energy particleNumber beta chemicalPotential hZ x

/-- The same ensemble ray is the unit-reference exponential tilt of negative
effective energy in the existing generic Gibbs-ray construction. -/
theorem ensembleRay_eq_unitReference_gibbsRay
    (energy particleNumber : State → ℝ) (beta chemicalPotential : ℝ) :
    ensembleRay energy particleNumber beta chemicalPotential =
      gibbsRay (unitReference (ι := State))
        (fun x => -effectiveEnergy energy particleNumber chemicalPotential x) beta := by
  unfold ensembleRay gibbsRay
  apply congrArg ray
  apply InfoGeometry.PositiveMeasure.ext
  funext x
  change Real.exp (-(beta * effectiveEnergy energy particleNumber chemicalPotential x)) =
    (1 : ℝ) * Real.exp (beta * (-effectiveEnergy energy particleNumber chemicalPotential x))
  rw [one_mul]
  congr 1
  ring

/-- A uniform energy offset changes the unnormalized ensemble only by a
positive scalar and therefore leaves its projective state unchanged. -/
theorem ensembleRay_energyShift
    (energy particleNumber : State → ℝ) (beta chemicalPotential offset : ℝ) :
    ensembleRay (fun x => energy x + offset) particleNumber beta chemicalPotential =
      ensembleRay energy particleNumber beta chemicalPotential := by
  have hmeasure :
      boltzmannMeasure (fun x => energy x + offset) particleNumber beta chemicalPotential =
        InfoGeometry.PositiveMeasure.scale (Real.exp (-beta * offset))
          (Real.exp_pos _) (boltzmannMeasure energy particleNumber beta chemicalPotential) := by
    apply InfoGeometry.PositiveMeasure.ext
    funext x
    change Real.exp
        (-(beta * ((energy x + offset) - chemicalPotential * particleNumber x))) =
      Real.exp (-beta * offset) *
        Real.exp (-(beta * (energy x - chemicalPotential * particleNumber x)))
    have hexp :
        -(beta * ((energy x + offset) - chemicalPotential * particleNumber x)) =
          (-beta * offset) + (-(beta * (energy x - chemicalPotential * particleNumber x))) := by
      ring
    rw [hexp, Real.exp_add]
  unfold ensembleRay
  rw [hmeasure, ray_scale]

end InfoGeometry.Canonical.GrandCanonicalProjectiveRayBridge
