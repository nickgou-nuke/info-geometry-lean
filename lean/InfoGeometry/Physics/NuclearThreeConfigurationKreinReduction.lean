/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearThreeConfigurationResolvent
import InfoGeometry.Physics.NuclearThreeConfigurationDual

/-!
# Concrete Feshbach reduction on the native real doubled Krein carrier

The actual complementary inverse, wave graph, and effective operator are
transported by the owned paired configuration lift. Its inverse equations
instantiate the generic native Krein-adjoint theorem. Both model legs are
retained; the signed Krein splitting is not used as the Feshbach projection.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction

open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace
open NuclearThreeConfiguration NuclearThreeConfigurationDual
open NuclearDoubledConfiguration NuclearThreeConfigurationResolvent

abbrev DoubledModelSpace := DoubledSpace ModelSpace

def doubledResolvent (c E : ℝ) : DoubledCarrier →L[ℝ] DoubledCarrier :=
  pairedLift (resolvent c E)

def doubledInclusion : DoubledModelSpace →L[ℝ] DoubledCarrier := pairedLift inclusion

def doubledGraphMap (c g E : ℝ) : DoubledModelSpace →L[ℝ] DoubledCarrier :=
  pairedLift (graphMap c g E)

def doubledReducedHamiltonian (a c g E : ℝ) : DoubledModelSpace →L[ℝ] DoubledModelSpace :=
  pairedLift (reducedHamiltonian a c g E)

private theorem pairedLift_one_configuration :
    pairedLift (1 : ConfigurationSpace →L[ℝ] ConfigurationSpace) = 1 :=
  pairedLift_id

private theorem pairedLift_mul_configuration
    (A B : ConfigurationSpace →L[ℝ] ConfigurationSpace) :
    pairedLift (A * B) = pairedLift A * pairedLift B := pairedLift_comp A B

theorem pairedLift_complement : pairedLift complement = 1 - doubledProjection := by
  rw [complement, pairedLift_sub, pairedLift_one_configuration]
  rfl

/-- The doubled denominator is the same owned Feshbach expression after lifting. -/
theorem doubled_denominator (a c g E : ℝ) :
    NuclearRealKreinFeshbach.denominator doubledProjection (doubledHamiltonian a c g) E =
      pairedLift (NuclearRealKreinFeshbach.denominator projection (hamiltonian a c g) E) := by
  simp only [NuclearRealKreinFeshbach.denominator, doubledProjection, doubledHamiltonian,
    pairedLift_sub, pairedLift_smul, pairedLift_mul_configuration, pairedLift_one_configuration]

theorem doubled_effectiveHamiltonian (a c g E : ℝ) :
    NuclearRealKreinFeshbach.effectiveHamiltonian doubledProjection
        (doubledHamiltonian a c g) (doubledResolvent c E) =
      pairedLift (NuclearRealKreinFeshbach.effectiveHamiltonian projection
        (hamiltonian a c g) (resolvent c E)) := by
  simp only [NuclearRealKreinFeshbach.effectiveHamiltonian, doubledProjection,
    doubledHamiltonian, doubledResolvent, pairedLift_add, pairedLift_mul_configuration]

theorem doubled_waveOperator (a c g E : ℝ) :
    NuclearRealKreinFeshbach.waveOperator doubledProjection
        (doubledHamiltonian a c g) (doubledResolvent c E) =
      pairedLift (NuclearRealKreinFeshbach.waveOperator projection
        (hamiltonian a c g) (resolvent c E)) := by
  simp only [NuclearRealKreinFeshbach.waveOperator, doubledProjection,
    doubledHamiltonian, doubledResolvent, pairedLift_add, pairedLift_mul_configuration]

theorem doubled_resolvent_support (c E : ℝ) :
    (1 - doubledProjection) * doubledResolvent c E = doubledResolvent c E ∧
      doubledResolvent c E * (1 - doubledProjection) = doubledResolvent c E := by
  constructor
  · rw [doubledResolvent, ← pairedLift_complement, ← pairedLift_mul_configuration,
      complement_mul_resolvent]
  · rw [doubledResolvent, ← pairedLift_complement, ← pairedLift_mul_configuration,
      resolvent_mul_complement]

/-- Actual two-sided corner inverse equations, with the exact real pole excluded. -/
theorem doubled_corner_inverse (a c g E : ℝ) (hE : E ≠ c) :
    NuclearRealKreinFeshbach.denominator doubledProjection (doubledHamiltonian a c g) E *
        doubledResolvent c E = 1 - doubledProjection ∧
      doubledResolvent c E *
        NuclearRealKreinFeshbach.denominator doubledProjection (doubledHamiltonian a c g) E =
          1 - doubledProjection := by
  constructor
  · rw [doubled_denominator, doubledResolvent, ← pairedLift_mul_configuration,
      denominator_mul_resolvent a c g E hE, pairedLift_complement]
  · rw [doubled_denominator, doubledResolvent, ← pairedLift_mul_configuration,
      resolvent_mul_denominator a c g E hE, pairedLift_complement]

theorem doubledResolvent_kreinAdjoint (a c g E : ℝ) (hE : E ≠ c) :
    kreinAdjoint (doubledResolvent c E) = doubledResolvent c E :=
  NuclearRealKreinFeshbach.resolvent_kreinAdjoint doubledProjection
    (doubledHamiltonian a c g) (doubledResolvent c E) E
    doubledProjection_kreinAdjoint (doubledHamiltonian_kreinAdjoint a c g)
    (doubled_resolvent_support c E).1 (doubled_corner_inverse a c g E hE).1

/-- The generic Krein theorem is instantiated with the proved concrete inverse. -/
theorem doubled_effectiveHamiltonian_kreinSelfAdjoint (a c g E : ℝ) (hE : E ≠ c) :
    IsKreinSelfAdjoint (NuclearRealKreinFeshbach.effectiveHamiltonian doubledProjection
      (doubledHamiltonian a c g) (doubledResolvent c E)) :=
  NuclearRealKreinFeshbach.effectiveHamiltonian_kreinSelfAdjoint doubledProjection
    (doubledHamiltonian a c g) (doubledResolvent c E) E
    doubledProjection_kreinAdjoint (doubledHamiltonian_kreinAdjoint a c g)
    (doubled_resolvent_support c E).1 (doubled_corner_inverse a c g E hE).1

theorem doubledGraphMap_eq_waveOperator (a c g E : ℝ) :
    doubledGraphMap c g E =
      (NuclearRealKreinFeshbach.waveOperator doubledProjection
        (doubledHamiltonian a c g) (doubledResolvent c E)).comp doubledInclusion := by
  rw [doubled_waveOperator, doubledInclusion, ← pairedLift_comp,
    ← graphMap_eq_waveOperator]
  rfl

theorem doubled_effectiveHamiltonian_inclusion (a c g E : ℝ) :
    (NuclearRealKreinFeshbach.effectiveHamiltonian doubledProjection
      (doubledHamiltonian a c g) (doubledResolvent c E)).comp doubledInclusion =
        doubledInclusion.comp (doubledReducedHamiltonian a c g E) := by
  rw [doubled_effectiveHamiltonian, doubledInclusion, doubledReducedHamiltonian,
    ← pairedLift_comp, effectiveHamiltonian_inclusion, pairedLift_comp]

theorem doubledGraphMap_injective (c g E : ℝ) :
    Function.Injective (doubledGraphMap c g E) :=
  pairedLift_injective_of _ (graphMap_injective c g E)

/-- Exact graph eigen correspondence on both actual real model legs. -/
theorem doubledGraphMap_eigen_equation_iff (a c g E : ℝ) (hE : E ≠ c)
    (x : DoubledModelSpace) :
    doubledHamiltonian a c g (doubledGraphMap c g E x) = E • doubledGraphMap c g E x ↔
      doubledReducedHamiltonian a c g E x = E • x := by
  have hmodel : doubledProjection (doubledInclusion x) = doubledInclusion x := by
    apply DoubledSpace.ext <;> simp [doubledProjection, doubledInclusion]
  have h := NuclearRealKreinFeshbach.eigen_equation_iff doubledProjection
    (doubledHamiltonian a c g) (doubledResolvent c E) E
    (doubled_resolvent_support c E).1 (doubled_corner_inverse a c g E hE).1
    (doubledInclusion x) hmodel
  have hw := congrArg (fun T : DoubledModelSpace →L[ℝ] DoubledCarrier => T x)
    (doubledGraphMap_eq_waveOperator a c g E)
  have heff := congrArg (fun T : DoubledModelSpace →L[ℝ] DoubledCarrier => T x)
    (doubled_effectiveHamiltonian_inclusion a c g E)
  change doubledGraphMap c g E x =
    NuclearRealKreinFeshbach.waveOperator doubledProjection
      (doubledHamiltonian a c g) (doubledResolvent c E) (doubledInclusion x) at hw
  change NuclearRealKreinFeshbach.effectiveHamiltonian doubledProjection
      (doubledHamiltonian a c g) (doubledResolvent c E) (doubledInclusion x) =
    doubledInclusion (doubledReducedHamiltonian a c g E x) at heff
  rw [← hw, heff] at h
  refine h.trans ?_
  constructor
  · intro he
    apply pairedLift_injective_of inclusion inclusion_injective
    simpa only [doubledInclusion, map_smul] using he
  · intro he
    rw [he, map_smul]

end InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction
