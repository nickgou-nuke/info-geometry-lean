import InfoGeometry.Canonical.FilteredGNSRepresentedCStarCompletion
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Modular automorphisms on the completed represented GNS carrier

The completed represented carrier is already a native `CStarAlgebra` via
`FilteredGNSRepresentedCStarCompletion`.  Any concrete modular automorphism on
its operator-closure model transports back along
`representedRangeCompletionStarAlgEquiv`.

This file packages that transport and records the key structural facts used by
KMS/Tomita layers: the lifted map is a star-algebra automorphism, hence
isometric and norm-preserving.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSRepresentedCStarModularAutomorphism

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient
open CStarStateColimit.Native.FilteredGNSRepresentedRangeCompletion
open CStarStateColimit.Native.FilteredGNSRepresentedAlgebraCompletion
open CStarStateColimit.Native.FilteredGNSRepresentedCStarCompletion

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)

/-- Completed faithful represented carrier. -/
abbrev CompletedCarrier : Type _ :=
  representedAlgebraicRangeCompletion Stage sys ω

/-- Concrete represented operator-closure carrier. -/
abbrev ConcreteCarrier : Type _ :=
  representedCStarClosure Stage sys ω

/-- Canonical star-algebra equivalence from the completed represented carrier
onto the concrete represented closure. -/
abbrev completionToConcreteStarAlgEquiv :
    CompletedCarrier Stage sys ω ≃⋆ₐ[ℂ]
      ConcreteCarrier Stage sys ω :=
  representedRangeCompletionStarAlgEquiv Stage sys ω

/--
Transport a concrete represented-closure automorphism back to the completed
represented carrier.
-/
def modularAutOnCompletion
    (σ : ConcreteCarrier Stage sys ω ≃⋆ₐ[ℂ]
      ConcreteCarrier Stage sys ω) :
    CompletedCarrier Stage sys ω ≃⋆ₐ[ℂ]
      CompletedCarrier Stage sys ω :=
  ((completionToConcreteStarAlgEquiv Stage sys ω).trans σ).trans
    (completionToConcreteStarAlgEquiv Stage sys ω).symm

@[simp] theorem modularAutOnCompletion_apply
    (σ : ConcreteCarrier Stage sys ω ≃⋆ₐ[ℂ]
      ConcreteCarrier Stage sys ω)
    (x : CompletedCarrier Stage sys ω) :
    modularAutOnCompletion Stage sys ω σ x =
      (completionToConcreteStarAlgEquiv Stage sys ω).symm
        (σ ((completionToConcreteStarAlgEquiv Stage sys ω) x)) :=
  rfl

@[simp] theorem modularAutOnCompletion_map_star
    (σ : ConcreteCarrier Stage sys ω ≃⋆ₐ[ℂ]
      ConcreteCarrier Stage sys ω)
    (x : CompletedCarrier Stage sys ω) :
    modularAutOnCompletion Stage sys ω σ (star x) =
      star (modularAutOnCompletion Stage sys ω σ x) :=
  map_star (modularAutOnCompletion Stage sys ω σ) x

/-- Any lifted modular automorphism is isometric. -/
theorem modularAutOnCompletion_isometry
    (σ : ConcreteCarrier Stage sys ω ≃⋆ₐ[ℂ]
      ConcreteCarrier Stage sys ω) :
    Isometry (modularAutOnCompletion Stage sys ω σ) :=
  StarAlgEquiv.isometry (modularAutOnCompletion Stage sys ω σ)

/-- Norm invariance of the lifted modular automorphism. -/
@[simp] theorem norm_modularAutOnCompletion
    (σ : ConcreteCarrier Stage sys ω ≃⋆ₐ[ℂ]
      ConcreteCarrier Stage sys ω)
    (x : CompletedCarrier Stage sys ω) :
    ‖modularAutOnCompletion Stage sys ω σ x‖ = ‖x‖ :=
  StarAlgEquiv.norm_map (modularAutOnCompletion Stage sys ω σ) x

/-- Continuity of the lifted modular automorphism follows from isometry. -/
theorem modularAutOnCompletion_continuous
    (σ : ConcreteCarrier Stage sys ω ≃⋆ₐ[ℂ]
      ConcreteCarrier Stage sys ω) :
    Continuous (modularAutOnCompletion Stage sys ω σ) :=
  (modularAutOnCompletion_isometry Stage sys ω σ).continuous

/-- Packaged star-isometric automorphism on the completed represented
carrier. -/
structure StarIsometricMap where
  toAut : CompletedCarrier Stage sys ω ≃⋆ₐ[ℂ]
    CompletedCarrier Stage sys ω
  isometry : Isometry (toAut : CompletedCarrier Stage sys ω →
    CompletedCarrier Stage sys ω)

/-- Any concrete represented-closure automorphism yields a star-isometric
automorphism on the completed represented carrier. -/
def modularStarIsometricMap
    (σ : ConcreteCarrier Stage sys ω ≃⋆ₐ[ℂ]
      ConcreteCarrier Stage sys ω) :
    StarIsometricMap Stage sys ω where
  toAut := modularAutOnCompletion Stage sys ω σ
  isometry := modularAutOnCompletion_isometry Stage sys ω σ

/-- A concrete modular flow on the represented operator closure. -/
structure ClosureModularFlow where
  toAut : ℝ →
    ConcreteCarrier Stage sys ω ≃⋆ₐ[ℂ]
      ConcreteCarrier Stage sys ω
  map_zero :
    toAut 0 = StarAlgEquiv.refl (R := ℂ)
      (A := ConcreteCarrier Stage sys ω)
  map_add :
    ∀ t s : ℝ,
      toAut (t + s) = (toAut t).trans (toAut s)

/-- A one-parameter concrete unitary flow on the represented closure carrier.

The multiplication law is oriented so that conjugation by `U (t + s)` matches
`(σ_t).trans (σ_s)` for the induced modular automorphisms. -/
structure ClosureUnitaryFlow where
  U : ℝ → unitary (ConcreteCarrier Stage sys ω)
  map_zero : U 0 = 1
  map_add : ∀ t s : ℝ, U (t + s) = U s * U t

/-- Standard one-parameter concrete unitary flow law `U (t + s) = U t * U s`.

This is the physicists' group-law orientation. It is converted below to the
`ClosureUnitaryFlow` orientation by time reversal `t ↦ -t`. -/
structure ClosureUnitaryFlowStd where
  U : ℝ → unitary (ConcreteCarrier Stage sys ω)
  map_zero : U 0 = 1
  map_add : ∀ t s : ℝ, U (t + s) = U t * U s

/-- Convert the standard group-law unitary flow to the modular-composition
orientation used by `ClosureUnitaryFlow`. -/
def ClosureUnitaryFlowStd.toClosureUnitaryFlow
    (UF : ClosureUnitaryFlowStd Stage sys ω) :
    ClosureUnitaryFlow Stage sys ω where
  U := fun t => UF.U (-t)
  map_zero := by
    simpa using UF.map_zero
  map_add := by
    intro t s
    simpa [neg_add, add_comm, add_left_comm, add_assoc] using
      UF.map_add (-s) (-t)

/-- Build a concrete modular flow by unitary conjugation:
`x ↦ U_t * x * U_t⋆`. -/
def closureModularFlowOfUnitaryFlow
    (UF : ClosureUnitaryFlow Stage sys ω) :
    ClosureModularFlow Stage sys ω where
  toAut := fun t =>
    Unitary.conjStarAlgAut (S := ℂ)
      (R := ConcreteCarrier Stage sys ω) (UF.U t)
  map_zero := by
    ext x
    simp [UF.map_zero]
  map_add := by
    intro t s
    calc
      Unitary.conjStarAlgAut (S := ℂ)
          (R := ConcreteCarrier Stage sys ω)
          (UF.U (t + s))
        = Unitary.conjStarAlgAut (S := ℂ)
            (R := ConcreteCarrier Stage sys ω)
            (UF.U s * UF.U t) := by
              simp [UF.map_add t s]
      _ =
        (Unitary.conjStarAlgAut (S := ℂ)
            (R := ConcreteCarrier Stage sys ω)
            (UF.U t)).trans
          (Unitary.conjStarAlgAut (S := ℂ)
            (R := ConcreteCarrier Stage sys ω)
            (UF.U s)) := by
              symm
              exact
                Unitary.conjStarAlgAut_trans_conjStarAlgAut
                  (S := ℂ)
                  (R := ConcreteCarrier Stage sys ω)
                  (UF.U t) (UF.U s)

@[simp] theorem closureModularFlowOfUnitaryFlow_apply
    (UF : ClosureUnitaryFlow Stage sys ω)
    (t : ℝ)
    (x : ConcreteCarrier Stage sys ω) :
    (closureModularFlowOfUnitaryFlow Stage sys ω UF).toAut t x =
      (UF.U t : ConcreteCarrier Stage sys ω) * x *
        (star (UF.U t) : ConcreteCarrier Stage sys ω) := by
  rfl

/-- Transport a concrete modular flow to the completed represented carrier. -/
def liftedCompletionFlow
    (F : ClosureModularFlow Stage sys ω) :
    ℝ → CompletedCarrier Stage sys ω ≃⋆ₐ[ℂ]
      CompletedCarrier Stage sys ω :=
  fun t => modularAutOnCompletion Stage sys ω (F.toAut t)

@[simp] theorem liftedCompletionFlow_zero
    (F : ClosureModularFlow Stage sys ω) :
    liftedCompletionFlow Stage sys ω F 0 =
      StarAlgEquiv.refl (R := ℂ)
        (A := CompletedCarrier Stage sys ω) := by
  ext x
  change
    (completionToConcreteStarAlgEquiv Stage sys ω).symm
      ((F.toAut 0) ((completionToConcreteStarAlgEquiv Stage sys ω) x)) = x
  rw [F.map_zero]
  exact
    (completionToConcreteStarAlgEquiv Stage sys ω).left_inv x

theorem liftedCompletionFlow_add
    (F : ClosureModularFlow Stage sys ω)
    (t s : ℝ) :
    liftedCompletionFlow Stage sys ω F (t + s) =
      (liftedCompletionFlow Stage sys ω F t).trans
        (liftedCompletionFlow Stage sys ω F s) := by
  ext x
  simp [liftedCompletionFlow, modularAutOnCompletion, F.map_add]

/-- Every transported time-slice is a star-isometric automorphism. -/
theorem liftedCompletionFlow_isometry
    (F : ClosureModularFlow Stage sys ω)
    (t : ℝ) :
    Isometry (liftedCompletionFlow Stage sys ω F t) :=
  modularAutOnCompletion_isometry Stage sys ω (F.toAut t)

/-- Time-slice packaging of the transported modular flow as a star-isometric
automorphism. -/
def liftedCompletionFlowStarIsometricMap
    (F : ClosureModularFlow Stage sys ω)
    (t : ℝ) :
    StarIsometricMap Stage sys ω where
  toAut := liftedCompletionFlow Stage sys ω F t
  isometry := liftedCompletionFlow_isometry Stage sys ω F t

@[simp] theorem norm_liftedCompletionFlow
    (F : ClosureModularFlow Stage sys ω)
    (t : ℝ)
    (x : CompletedCarrier Stage sys ω) :
    ‖liftedCompletionFlow Stage sys ω F t x‖ = ‖x‖ :=
  StarAlgEquiv.norm_map (liftedCompletionFlow Stage sys ω F t) x

/-- Packaged one-parameter star-automorphism flow on the completed represented
carrier. -/
structure CompletionModularFlow where
  toAut : ℝ →
    CompletedCarrier Stage sys ω ≃⋆ₐ[ℂ]
      CompletedCarrier Stage sys ω
  map_zero :
    toAut 0 = StarAlgEquiv.refl (R := ℂ)
      (A := CompletedCarrier Stage sys ω)
  map_add :
    ∀ t s : ℝ,
      toAut (t + s) = (toAut t).trans (toAut s)

/-- Transport turns a concrete represented-closure modular flow into a completed
carrier modular flow. -/
def closureFlowToCompletionFlow
    (F : ClosureModularFlow Stage sys ω) :
    CompletionModularFlow Stage sys ω where
  toAut := liftedCompletionFlow Stage sys ω F
  map_zero := liftedCompletionFlow_zero Stage sys ω F
  map_add := liftedCompletionFlow_add Stage sys ω F

/-- Direct pipeline: a concrete unitary flow induces a modular flow on the
completed represented carrier. -/
def closureUnitaryFlowToCompletionFlow
    (UF : ClosureUnitaryFlow Stage sys ω) :
    CompletionModularFlow Stage sys ω :=
  closureFlowToCompletionFlow Stage sys ω
    (closureModularFlowOfUnitaryFlow Stage sys ω UF)

/-- Direct pipeline from the standard group-law orientation
`U (t + s) = U t * U s` to the completed represented modular flow. -/
def closureUnitaryFlowStdToCompletionFlow
    (UF : ClosureUnitaryFlowStd Stage sys ω) :
    CompletionModularFlow Stage sys ω :=
  closureUnitaryFlowToCompletionFlow Stage sys ω
    (ClosureUnitaryFlowStd.toClosureUnitaryFlow Stage sys ω UF)

@[simp] theorem closureUnitaryFlowStdToCompletionFlow_apply
    (UF : ClosureUnitaryFlowStd Stage sys ω)
    (t : ℝ) :
    (closureUnitaryFlowStdToCompletionFlow Stage sys ω UF).toAut t =
      liftedCompletionFlow Stage sys ω
        (closureModularFlowOfUnitaryFlow Stage sys ω
          (ClosureUnitaryFlowStd.toClosureUnitaryFlow Stage sys ω UF)) t :=
  rfl

end CStarStateColimit.Native.FilteredGNSRepresentedCStarModularAutomorphism
