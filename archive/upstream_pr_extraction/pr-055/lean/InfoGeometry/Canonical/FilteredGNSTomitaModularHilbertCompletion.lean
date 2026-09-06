import InfoGeometry.Canonical.FilteredGNSTomitaModularQuotient

/-!
# Hilbert completion of the filtered Tomita modular quotient

The modular null-space quotient carries a positive-definite Hermitian
sesquilinear form.  This file installs that form as Mathlib's native
`InnerProductSpace.Core`, derives the corresponding normed complex space, and
takes its uniform completion.  The canonical map into the completion is
isometric and has dense range.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaModularHilbertCompletion

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaModularFormColimit
open CStarStateColimit.Native.FilteredGNSTomitaComplexColimit
open CStarStateColimit.Native.FilteredGNSTomitaModularQuotient

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
variable
  (hclos :
    ∀ i, IsClosableTomitaCore (ω.state i))

local notation "Q∞" =>
  ModularFormQuotient Stage sys ω hclos
local notation "qQ" =>
  quotientModularForm Stage sys ω hclos

/-- Native inner-product core induced by the positive-definite quotient
modular form. -/
def modularQuotientInnerProductCore :
    InnerProductSpace.Core ℂ Q∞ where
  inner := fun x y => qQ x y
  conj_inner_symm :=
    quotientModularForm_conj_symm
      Stage sys ω hclos
  re_inner_nonneg :=
    quotientModularForm_nonneg
      Stage sys ω hclos
  add_left := by
    intro x y z
    exact
      LinearMap.congr_fun
        ((quotientModularForm
          Stage sys ω hclos).map_add x y) z
  smul_left := by
    intro x y c
    have h :=
      (quotientModularForm
        Stage sys ω hclos).map_smulₛₗ c x
    have happ := LinearMap.congr_fun h y
    simpa only [LinearMap.smul_apply, smul_eq_mul] using happ
  definite := by
    intro x hx
    exact
      (quotientModularForm_self_eq_zero_iff
        Stage sys ω hclos x).mp hx

/-- Install the verified modular quotient core. -/
noncomputable instance modularQuotientInnerProductCoreInst :
    InnerProductSpace.Core ℂ Q∞ :=
  modularQuotientInnerProductCore Stage sys ω hclos

/-- The corresponding pre-inner-product core used by Mathlib's norm
construction. -/
noncomputable instance modularQuotientPreInnerProductCoreInst :
    PreInnerProductSpace.Core ℂ Q∞ :=
  (modularQuotientInnerProductCore
    Stage sys ω hclos).toCore

/-- The norm is derived from the positive-definite modular form. -/
noncomputable instance modularQuotientNormedAddCommGroup :
    NormedAddCommGroup Q∞ :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

/-- The resulting native complex inner-product space. -/
noncomputable instance modularQuotientInnerProductSpace :
    InnerProductSpace ℂ Q∞ :=
  InnerProductSpace.ofCore
    (modularQuotientInnerProductCore
      Stage sys ω hclos).toCore

/-- The installed inner product is exactly the descended quotient modular
form. -/
@[simp] theorem modularQuotient_inner_eq
    (x y : Q∞) :
    inner ℂ x y = qQ x y :=
  rfl

/-- Positive definiteness in native inner-product notation. -/
theorem modularQuotient_inner_self_eq_zero_iff
    (x : Q∞) :
    inner ℂ x x = 0 ↔ x = 0 := by
  rw [modularQuotient_inner_eq]
  exact
    quotientModularForm_self_eq_zero_iff
      Stage sys ω hclos x

/-- Hilbert completion of the filtered modular quotient. -/
abbrev ModularHilbertCompletion : Type u :=
  UniformSpace.Completion Q∞

/-- Canonical dense embedding into the modular Hilbert completion. -/
def modularQuotientToCompletion :
    Q∞ → ModularHilbertCompletion Stage sys ω hclos :=
  UniformSpace.Completion.coe'

/-- The canonical completion map is an isometry. -/
theorem modularQuotientToCompletion_isometry :
    Isometry
      (modularQuotientToCompletion Stage sys ω hclos) :=
  UniformSpace.Completion.coe_isometry

/-- The canonical modular quotient has dense image in its Hilbert
completion. -/
theorem modularQuotientToCompletion_denseRange :
    DenseRange
      (modularQuotientToCompletion Stage sys ω hclos) :=
  UniformSpace.Completion.denseRange_coe

/-- The canonical embedding as a native complex-linear map. -/
def modularQuotientToCompletionLinearMap :
    Q∞ →ₗ[ℂ]
      ModularHilbertCompletion Stage sys ω hclos where
  toFun := modularQuotientToCompletion Stage sys ω hclos
  map_add' := by
    intro x y
    exact UniformSpace.Completion.coe_add x y
  map_smul' := by
    intro c x
    exact UniformSpace.Completion.coe_smul c x

/-- The canonical dense embedding bundled as a complex linear isometry. -/
def modularQuotientToCompletionLinearIsometry :
    Q∞ →ₗᵢ[ℂ]
      ModularHilbertCompletion Stage sys ω hclos :=
  LinearIsometry.mk
    (modularQuotientToCompletionLinearMap
      Stage sys ω hclos)
    (fun x => by
      have h :=
        (modularQuotientToCompletion_isometry
          Stage sys ω hclos).dist_eq x 0
      simpa only [modularQuotientToCompletion,
        UniformSpace.Completion.coe_zero,
        dist_zero_right] using h)

@[simp] theorem modularQuotientToCompletionLinearIsometry_apply
    (x : Q∞) :
    modularQuotientToCompletionLinearIsometry
        Stage sys ω hclos x =
      modularQuotientToCompletion
        Stage sys ω hclos x :=
  rfl

/-- The completed modular carrier is complete. -/
theorem modularHilbertCompletion_complete :
    CompleteSpace
      (ModularHilbertCompletion Stage sys ω hclos) :=
  inferInstance

end CStarStateColimit.Native.FilteredGNSTomitaModularHilbertCompletion
