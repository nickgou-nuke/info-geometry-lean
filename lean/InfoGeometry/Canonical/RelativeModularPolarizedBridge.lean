import InfoGeometry.Canonical.RelativeModularProjectiveBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.PolarizedSector
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.RelativeModularPolarizedBridge

Bridge from the restricted relative-modular carrier to the actual polarized
plus/minus split on doubled space.

This file does three things:
- identifies the standard-form seed grading with the current spectral grading,
- packages plus/minus restricted relative-modular data on a shared carrier,
- lifts the existing projective/discrete/count bridge formulas to the polarized
  sector packaging.
-/

namespace InfoGeometry.Canonical.RelativeModularPolarizedBridge

open InfoGeometry.Canonical.StandardFormCore
open InfoGeometry.Canonical.RelativeModularCore
open InfoGeometry.Canonical.RelativeModularProjectiveBridge
open InfoGeometry.Krein
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Krein.SplitQuadraticSheets
open MeasureTheory

section PolarizedRestriction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {betaPlus : Type*} [Fintype betaPlus] [Nonempty betaPlus]
variable {betaMinus : Type*} [Fintype betaMinus] [Nonempty betaMinus]

structure PlusRestrictedRelativeModularData
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (α : Type*) [Fintype α] [Nonempty α]
    (betaPlus : Type*) [Fintype betaPlus] [Nonempty betaPlus] where
  data : RestrictedRelativeModularData H α betaPlus
  lift : betaPlus → InfoGeometry.Krein.DoubledSpace H
  lift_mem : ∀ b : betaPlus, lift b ∈ plusSheet (E := H)

structure MinusRestrictedRelativeModularData
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (α : Type*) [Fintype α] [Nonempty α]
    (betaMinus : Type*) [Fintype betaMinus] [Nonempty betaMinus] where
  data : RestrictedRelativeModularData H α betaMinus
  lift : betaMinus → InfoGeometry.Krein.DoubledSpace H
  lift_mem : ∀ b : betaMinus, lift b ∈ minusSheet (E := H)

structure PolarizedRelativeModularPair
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (α : Type*) [Fintype α] [Nonempty α]
    (betaPlus : Type*) [Fintype betaPlus] [Nonempty betaPlus]
    (betaMinus : Type*) [Fintype betaMinus] [Nonempty betaMinus] where
  plus : PlusRestrictedRelativeModularData H α betaPlus
  minus : MinusRestrictedRelativeModularData H α betaMinus
  sameCarrier : plus.data.carrier = minus.data.carrier

theorem PlusRestrictedRelativeModularData.lift_eq_plusPoint_fst
    (R : PlusRestrictedRelativeModularData H α betaPlus) (b : betaPlus) :
    R.lift b = plusPoint (E := H) (WithLp.fst (R.lift b)) :=
  eq_plusPoint_of_mem_plusSheet (E := H) (R.lift_mem b)

theorem MinusRestrictedRelativeModularData.lift_eq_minusPoint_snd
    (R : MinusRestrictedRelativeModularData H α betaMinus) (b : betaMinus) :
    R.lift b = minusPoint (E := H) (WithLp.snd (R.lift b)) :=
  eq_minusPoint_of_mem_minusSheet (E := H) (R.lift_mem b)

@[rep_depth projective, simp] theorem
    PlusRestrictedRelativeModularData.local_logDensity_eq_pullback_add_shiftDiff
    (R : PlusRestrictedRelativeModularData H α betaPlus) (b : betaPlus) :
    R.data.localPair.logDensity b
      = R.data.carrier.projectiveLogDensity (R.data.embed b)
          + (R.data.sourceLogShift - R.data.targetLogShift) := by
  exact RestrictedRelativeModularData.local_logDensity_eq_pullback_add_shiftDiff
    (R := R.data) (b := b)

@[rep_depth projective, simp] theorem
    PlusRestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff
    (R : PlusRestrictedRelativeModularData H α betaPlus) (b : betaPlus) :
    R.data.localPair.modularPotential b
      = R.data.carrier.projectiveModularPotential (R.data.embed b)
          + (R.data.targetLogShift - R.data.sourceLogShift) := by
  exact RestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff
    (R := R.data) (b := b)

@[rep_depth projective, simp] theorem
    MinusRestrictedRelativeModularData.local_logDensity_eq_pullback_add_shiftDiff
    (R : MinusRestrictedRelativeModularData H α betaMinus) (b : betaMinus) :
    R.data.localPair.logDensity b
      = R.data.carrier.projectiveLogDensity (R.data.embed b)
          + (R.data.sourceLogShift - R.data.targetLogShift) := by
  exact RestrictedRelativeModularData.local_logDensity_eq_pullback_add_shiftDiff
    (R := R.data) (b := b)

@[rep_depth projective, simp] theorem
    MinusRestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff
    (R : MinusRestrictedRelativeModularData H α betaMinus) (b : betaMinus) :
    R.data.localPair.modularPotential b
      = R.data.carrier.projectiveModularPotential (R.data.embed b)
          + (R.data.targetLogShift - R.data.sourceLogShift) := by
  exact RestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff
    (R := R.data) (b := b)

@[rep_depth projective, simp] theorem
    PlusRestrictedRelativeModularData.local_logDensity_eq_pullback_of_equal_shift
    (R : PlusRestrictedRelativeModularData H α betaPlus)
    (hshift : R.data.sourceLogShift = R.data.targetLogShift) (b : betaPlus) :
    R.data.localPair.logDensity b = R.data.carrier.projectiveLogDensity (R.data.embed b) := by
  exact RestrictedRelativeModularData.local_logDensity_eq_pullback_of_equal_shift
    (R := R.data) hshift b

@[rep_depth projective, simp] theorem
    MinusRestrictedRelativeModularData.local_logDensity_eq_pullback_of_equal_shift
    (R : MinusRestrictedRelativeModularData H α betaMinus)
    (hshift : R.data.sourceLogShift = R.data.targetLogShift) (b : betaMinus) :
    R.data.localPair.logDensity b = R.data.carrier.projectiveLogDensity (R.data.embed b) := by
  exact RestrictedRelativeModularData.local_logDensity_eq_pullback_of_equal_shift
    (R := R.data) hshift b

@[rep_depth projective, simp] theorem
    PlusRestrictedRelativeModularData.local_modularPotential_eq_pullback_of_equal_shift
    (R : PlusRestrictedRelativeModularData H α betaPlus)
    (hshift : R.data.sourceLogShift = R.data.targetLogShift) (b : betaPlus) :
    R.data.localPair.modularPotential b
      = R.data.carrier.projectiveModularPotential (R.data.embed b) := by
  exact RestrictedRelativeModularData.local_modularPotential_eq_pullback_of_equal_shift
    (R := R.data) hshift b

@[rep_depth projective, simp] theorem
    MinusRestrictedRelativeModularData.local_modularPotential_eq_pullback_of_equal_shift
    (R : MinusRestrictedRelativeModularData H α betaMinus)
    (hshift : R.data.sourceLogShift = R.data.targetLogShift) (b : betaMinus) :
    R.data.localPair.modularPotential b
      = R.data.carrier.projectiveModularPotential (R.data.embed b) := by
  exact RestrictedRelativeModularData.local_modularPotential_eq_pullback_of_equal_shift
    (R := R.data) hshift b

end PolarizedRestriction

section Discrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {betaPlus : Type*} [Fintype betaPlus] [Nonempty betaPlus]
variable {betaMinus : Type*} [Fintype betaMinus] [Nonempty betaMinus]
variable [MeasurableSpace betaPlus] [MeasurableSingletonClass betaPlus] [Countable betaPlus]
variable [MeasurableSpace betaMinus] [MeasurableSingletonClass betaMinus] [Countable betaMinus]

@[rep_depth projective, simp] theorem
    PlusRestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift
    (R : PlusRestrictedRelativeModularData H α betaPlus) (b : betaPlus) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := betaPlus) R.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := betaPlus) R.data.localSource) b
      = R.data.carrier.projectiveModularPotential (R.data.embed b)
          + (R.data.targetLogShift - R.data.sourceLogShift) := by
  rw [RestrictedRelativeModularData.local_projectiveLogGenerator_eq_local_modularPotential
    (R := R.data) (b := b)]
  exact PlusRestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff
    (R := R) (b := b)

@[rep_depth projective, simp] theorem
    MinusRestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift
    (R : MinusRestrictedRelativeModularData H α betaMinus) (b : betaMinus) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := betaMinus) R.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := betaMinus) R.data.localSource) b
      = R.data.carrier.projectiveModularPotential (R.data.embed b)
          + (R.data.targetLogShift - R.data.sourceLogShift) := by
  rw [RestrictedRelativeModularData.local_projectiveLogGenerator_eq_local_modularPotential
    (R := R.data) (b := b)]
  exact MinusRestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff
    (R := R) (b := b)

end Discrete

section Count

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {betaMinus : Type*} [Fintype betaMinus] [Nonempty betaMinus]
variable {betaPlus : Type*} [Fintype betaPlus] [Nonempty betaPlus]
variable {nPlus : Nat} [Nonempty (Fin nPlus)]
variable {nMinus : Nat} [Nonempty (Fin nMinus)]

@[rep_depth projective, simp] theorem
    PlusRestrictedRelativeModularData.local_projectiveLogGenerator_eq_projectiveCountHamiltonianProfile_of_countRays
    (R : PlusRestrictedRelativeModularData H α (Fin nPlus))
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nPlus)
    (hcounts : ∀ i : Fin nPlus, 0 < counts i)
    (href : ∀ i : Fin nPlus, 0 < ref i)
    (hsource : R.data.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay counts hcounts)
    (htarget : R.data.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay ref href)
    [MeasurableSpace (Fin nPlus)] [MeasurableSingletonClass (Fin nPlus)] [Countable (Fin nPlus)]
    (i : Fin nPlus) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nPlus) R.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nPlus) R.data.localSource) i
      = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
          counts ref hcounts href i := by
  exact RestrictedRelativeModularData.local_projectiveLogGenerator_eq_projectiveCountHamiltonianProfile_of_countRays
    (R := R.data) (counts := counts) (ref := ref)
    (hcounts := hcounts) (href := href) (hsource := hsource) (htarget := htarget) i

@[rep_depth projective, simp] theorem
    MinusRestrictedRelativeModularData.local_projectiveLogGenerator_eq_projectiveCountHamiltonianProfile_of_countRays
    (R : MinusRestrictedRelativeModularData H α (Fin nMinus))
    (counts ref : InfoGeometry.Canonical.RelativePotentialCountBridge.RelativeCounts nMinus)
    (hcounts : ∀ i : Fin nMinus, 0 < counts i)
    (href : ∀ i : Fin nMinus, 0 < ref i)
    (hsource : R.data.localSource =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay counts hcounts)
    (htarget : R.data.localTarget =
      InfoGeometry.Canonical.RelativePotentialCountBridge.countRay ref href)
    [MeasurableSpace (Fin nMinus)] [MeasurableSingletonClass (Fin nMinus)] [Countable (Fin nMinus)]
    (i : Fin nMinus) :
    InfoGeometry.MeasureProjective.ProjectiveState.logGenerator
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nMinus) R.data.localTarget)
        (InfoGeometry.Canonical.RelativePotentialDiscreteBridge.toProjectiveState
          (α := Fin nMinus) R.data.localSource) i
      = InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile
          counts ref hcounts href i := by
  exact RestrictedRelativeModularData.local_projectiveLogGenerator_eq_projectiveCountHamiltonianProfile_of_countRays
    (R := R.data) (counts := counts) (ref := ref)
    (hcounts := hcounts) (href := href) (hsource := hsource) (htarget := htarget) i

end Count

end InfoGeometry.Canonical.RelativeModularPolarizedBridge
