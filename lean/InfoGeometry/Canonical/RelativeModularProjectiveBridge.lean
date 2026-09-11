import InfoGeometry.Canonical.RelativeModularCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RelativePotentialDiscreteBridge
import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.RelativeModularProjectiveBridge

Bridge from the restricted relative-modular carrier to the existing
projective/discrete/count representation surfaces.

This file adds no new modular ontology. It only transports the owner data from
`RelativeModularCore` into:
- the discrete projective-state logarithmic generator surface,
- the count-ray/projective-count representation layer.
-/

namespace InfoGeometry.Canonical.RelativeModularProjectiveBridge

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.RelativeModularCore
open InfoGeometry.Canonical.StandardFormCore
open MeasureTheory

section Discrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {β : Type*} [Fintype β] [Nonempty β]
variable [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]

/--
On the finite discrete slice, the projective logarithmic generator attached to
the restricted pair is exactly the restricted modular potential.
-/
@[rep_depth projective]
theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_local_modularPotential_ae
    (R : RestrictedRelativeModularData H α β) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := β) R.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := β) R.localSource)
      =ᶠ[ae
          (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.gaugeSectionFinProb
            (α := β) R.localSource).toMeasure]
        fun b => R.localPair.modularPotential b := by
  change
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := β) R.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := β) R.localSource)
      =ᶠ[ae
          (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.gaugeSectionFinProb
            (α := β) R.localSource).toMeasure]
        fun b => relativeModularPotential (α := β) R.localSource R.localTarget b
  exact
    InfoGeometry.Canonical.RelativePotentialDiscreteBridge.projectiveLogGenerator_eq_relativeModularPotential_ae
      (α := β) (q := R.localSource) (q0 := R.localTarget)

/--
Pointwise discrete projective logarithmic generator formula for the restricted
pair.
-/
@[rep_depth projective, simp]
theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_local_modularPotential
    (R : RestrictedRelativeModularData H α β) (b : β) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := β) R.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := β) R.localSource) b
      = R.localPair.modularPotential b := by
  change
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := β) R.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := β) R.localSource) b
      = relativeModularPotential (α := β) R.localSource R.localTarget b
  exact
    InfoGeometry.Canonical.RelativePotentialDiscreteBridge.projectiveLogGenerator_eq_relativeModularPotential
      (α := β) (q := R.localSource) (q0 := R.localTarget) (a := b)

/--
The restricted discrete projective logarithmic generator is the ambient
projective modular potential pulled back along the subsystem embedding, shifted
by the local reweighting defect.
-/
@[rep_depth projective]
theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift_ae
    (R : RestrictedRelativeModularData H α β) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := β) R.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := β) R.localSource)
      =ᶠ[ae
          (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.gaugeSectionFinProb
            (α := β) R.localSource).toMeasure]
        fun b =>
          R.carrier.projectiveModularPotential (R.embed b)
            + (R.targetLogShift - R.sourceLogShift) := by
  filter_upwards
    [RestrictedRelativeModularData.local_projectiveLogGenerator_eq_local_modularPotential_ae
      (R := R)] with b hb
  rw [hb, RestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff
    (R := R) (b := b)]

/--
Pointwise pullback-plus-shift formula for the restricted discrete projective
logarithmic generator.
-/
@[rep_depth projective, simp]
theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift
    (R : RestrictedRelativeModularData H α β) (b : β) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := β) R.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := β) R.localSource) b
      = R.carrier.projectiveModularPotential (R.embed b)
          + (R.targetLogShift - R.sourceLogShift) := by
  rw [RestrictedRelativeModularData.local_projectiveLogGenerator_eq_local_modularPotential
    (R := R) (b := b)]
  exact RestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff
    (R := R) (b := b)

end Discrete

section Count

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {n : Nat} [Nonempty (Fin n)]

/--
If the restricted pair is realized by positive count rays, its restricted
modular potential is exactly the projective count Hamiltonian profile.
-/
@[rep_depth projective, simp]
theorem RestrictedRelativeModularData.local_modularPotential_eq_projectiveCountHamiltonianProfile_of_countRays
    (R : RestrictedRelativeModularData H α (Fin n))
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i)
    (hsource : R.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay counts hcounts)
    (htarget : R.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay ref href)
    (i : Fin n) :
    R.localPair.modularPotential i =
      InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
        counts ref hcounts href i := by
  unfold RestrictedRelativeModularData.localPair RelativeStatePair.modularPotential
  rw [hsource, htarget]
  unfold InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
  rfl

/--
For restricted count rays, the ambient pulled-back modular potential plus the
local reweighting defect equals the projective count Hamiltonian profile.
-/
@[rep_depth projective, simp]
theorem RestrictedRelativeModularData.projectiveCountHamiltonianProfile_eq_pullback_ambient_add_shift
    (R : RestrictedRelativeModularData H α (Fin n))
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i)
    (hsource : R.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay counts hcounts)
    (htarget : R.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay ref href)
    (i : Fin n) :
    InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
        counts ref hcounts href i
      = R.carrier.projectiveModularPotential (R.embed i)
          + (R.targetLogShift - R.sourceLogShift) := by
  rw [← RestrictedRelativeModularData.local_modularPotential_eq_projectiveCountHamiltonianProfile_of_countRays
      (R := R)
      (counts := counts) (ref := ref) (hcounts := hcounts) (href := href)
      (hsource := hsource) (htarget := htarget)]
  exact RestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff
    (R := R) (b := i)

end Count

section CountDiscrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {n : Nat} [Nonempty (Fin n)]
variable [MeasurableSpace (Fin n)] [MeasurableSingletonClass (Fin n)] [Countable (Fin n)]

/--
For restricted count rays, the discrete projective logarithmic generator is
exactly the projective count Hamiltonian profile.
-/
@[rep_depth projective, simp]
theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_projectiveCountHamiltonianProfile_of_countRays
    (R : RestrictedRelativeModularData H α (Fin n))
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i)
    (hsource : R.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay counts hcounts)
    (htarget : R.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay ref href)
    (i : Fin n) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin n) R.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin n) R.localSource) i
      = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
          counts ref hcounts href i := by
  rw [RestrictedRelativeModularData.local_projectiveLogGenerator_eq_local_modularPotential
    (R := R) (b := i)]
  exact RestrictedRelativeModularData.local_modularPotential_eq_projectiveCountHamiltonianProfile_of_countRays
    (R := R)
    (counts := counts) (ref := ref) (hcounts := hcounts) (href := href)
    (hsource := hsource) (htarget := htarget) i

end CountDiscrete

end InfoGeometry.Canonical.RelativeModularProjectiveBridge
