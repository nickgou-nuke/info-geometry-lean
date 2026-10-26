/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CARModuleDecomposition
import InfoGeometry.Canonical.PhaseFlowCARBridge

/-!
# Intertwining an actual CAR module with the doubled-space phase flow

The map is explicit once a linear identification of the multiplicity space
with `ker ann` is supplied.  No topological or metric structure on the target
is presumed.  Only the source carries the Hilbert-space phase flow.
-/

noncomputable section
namespace InfoGeometry.Canonical.DoubledCARIntertwiner

open InfoGeometry.Krein
open InfoGeometry.Canonical.ProjectorEquivariance
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovClosedForms
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.RealDoubledWaveplate
open InfoGeometry.Canonical.PhaseFlowCARBridge
open InfoGeometry.Algebra.CARModuleDecomposition

variable {E V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommGroup V] [Module ℝ V]
variable (C : SplitClifford.CARPair (Module.End ℝ V))
variable (e : E ≃ₗ[ℝ] C.ann.ker)

/-- Occupied/unoccupied coordinates, not an arbitrary equivalence of total spaces. -/
def doubledCAREquiv : DoubledSpace E ≃ₗ[ℝ] V :=
  ((doubledCoordinates (E := E)).trans (e.prodCongr e)).trans (splitEquiv C)

@[simp] theorem doubledCAREquiv_pair (x y : E) :
    doubledCAREquiv C e (to_doubled x y) = C.cre (e x) + e y := rfl

theorem annihilation_intertwines (z : DoubledSpace E) :
    C.ann (doubledCAREquiv C e z) =
      doubledCAREquiv C e (concreteCARAnnihilation (E := E) z) := by
  have hz : to_doubled (WithLp.fst z) (WithLp.snd z) = z := by
    apply DoubledSpace.ext <;> rfl
  rw [← hz]
  change C.ann (splitEquiv C (e (WithLp.fst z), e (WithLp.snd z))) = _
  rw [ann_split]
  simp only [concreteCARAnnihilation, cliffordConcreteAnnihilation_apply_to_doubled,
    doubledCAREquiv_pair, splitEquiv_apply, map_zero, zero_add]

theorem creation_intertwines (z : DoubledSpace E) :
    C.cre (doubledCAREquiv C e z) =
      doubledCAREquiv C e (concreteCARCreation (E := E) z) := by
  have hz : to_doubled (WithLp.fst z) (WithLp.snd z) = z := by
    apply DoubledSpace.ext <;> rfl
  rw [← hz]
  change C.cre (splitEquiv C (e (WithLp.fst z), e (WithLp.snd z))) = _
  rw [cre_split]
  simp only [concreteCARCreation, cliffordConcreteCreation_apply_to_doubled,
    doubledCAREquiv_pair, splitEquiv_apply, map_zero, add_zero]

/-- The transported phase axis is annihilation minus creation. -/
theorem phase_axis_intertwines (z : DoubledSpace E) :
    (C.ann - C.cre) (doubledCAREquiv C e z) =
      doubledCAREquiv C e (HestenesI (E := E) z) := by
  rw [LinearMap.sub_apply, annihilation_intertwines, creation_intertwines, ← map_sub]
  congr 1
  have hz : to_doubled (WithLp.fst z) (WithLp.snd z) = z := by
    apply DoubledSpace.ext <;> rfl
  rw [← hz]
  apply DoubledSpace.ext <;>
    simp [concreteCARAnnihilation, concreteCARCreation,
      cliffordConcreteAnnihilation_apply_to_doubled,
      cliffordConcreteCreation_apply_to_doubled,
      HestenesI, ContinuousLinearMap.mul_apply, modular_j_apply,
      spectral_epsilon_apply, to_doubled]

/-- The source grading is transported as `cre ann - ann cre`. -/
theorem grading_intertwines (z : DoubledSpace E) :
    (C.cre * C.ann - C.ann * C.cre) (doubledCAREquiv C e z) =
      doubledCAREquiv C e (spectral_epsilon (E := E) z) := by
  simp only [LinearMap.sub_apply, Module.End.mul_apply,
    annihilation_intertwines, creation_intertwines, ← map_sub]
  congr 1
  have hz : to_doubled (WithLp.fst z) (WithLp.snd z) = z := by
    apply DoubledSpace.ext <;> rfl
  rw [← hz]
  apply DoubledSpace.ext <;>
    simp [concreteCARAnnihilation, concreteCARCreation,
      cliffordConcreteAnnihilation_apply_to_doubled,
      cliffordConcreteCreation_apply_to_doubled, spectral_epsilon_apply, to_doubled]

/-- Phase flow on the target's associative endomorphism algebra. -/
def carPhase (θ : ℝ) : Module.End ℝ V :=
  Real.cos θ • 1 + Real.sin θ • (C.ann - C.cre)

theorem phase_intertwines (θ : ℝ) (z : DoubledSpace E) :
    carPhase C θ (doubledCAREquiv C e z) =
      doubledCAREquiv C e (phaseFlow (E := E) θ z) := by
  have haxis := phase_axis_intertwines C e z
  change Real.cos θ • doubledCAREquiv C e z +
    Real.sin θ • ((C.ann - C.cre) (doubledCAREquiv C e z)) = _
  rw [haxis, ← map_smul, ← map_smul, ← map_add]
  congr 1
  rw [phaseFlow_eq_KRotation, KRotation_apply]

/-- Full operator covariance, not merely generator agreement. -/
theorem conjugation_intertwines (θ : ℝ)
    (T : DoubledSpace E →L[ℝ] DoubledSpace E) (z : DoubledSpace E) :
    carPhase C (-θ)
        (doubledCAREquiv C e (T (phaseFlow (E := E) θ z))) =
      doubledCAREquiv C e (phaseConjugation (E := E) θ T z) := by
  rw [phase_intertwines]
  rfl

end InfoGeometry.Canonical.DoubledCARIntertwiner
