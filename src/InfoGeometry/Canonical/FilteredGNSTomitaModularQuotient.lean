import InfoGeometry.Canonical.FilteredGNSTomitaComplexColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Null-space quotient of the filtered Tomita modular form

The positive Hermitian colimit form can be degenerate.  This file identifies
its diagonal null space with its full radical, proves that the null space is a
complex submodule, and descends the form to the corresponding quotient.  The
quotient form is positive definite.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaModularQuotient

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
open CStarStateColimit.Native.FilteredGNSTomitaModularFormColimit
open CStarStateColimit.Native.FilteredGNSTomitaComplexColimit

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

local notation "D∞" =>
  ClosedDomainDirectLimit Stage sys ω
local notation "q∞" =>
  complexDirectLimitModularForm Stage sys ω hclos

/-- A diagonal-zero vector is in the left radical of the colimit modular
form.  The proof returns to a common filtered stage and uses the actual
closed Tomita image, not an abstract scalar inequality. -/
theorem diagonal_zero_implies_left_radical
    (z : D∞) (hz : q∞ z z = 0)
    (w : D∞) :
    q∞ z w = 0 := by
  induction z using Module.DirectLimit.induction_on with
  | ih i x =>
      induction w using Module.DirectLimit.induction_on with
      | ih j y =>
          let k := commonUpper i j
          have hik : i ≤ k := le_commonUpper_left i j
          have hjk : j ≤ k := le_commonUpper_right i j
          have hxk :
              closedTomitaModularForm Stage sys ω hclos k
                  (domainTransition Stage sys ω hik x)
                  (domainTransition Stage sys ω hik x) = 0 := by
            have h := hz
            simp only [complexDirectLimitModularForm_apply,
              directLimitModularForm_of_of] at h
            rw [commonStageModularPairing_eq_at
              Stage sys ω hclos i i k hik hik] at h
            exact h
          have hS :
              closedTomitaOperator
                  (ω.state k) (hclos k)
                  (domainTransition Stage sys ω hik x) = 0 := by
            rw [closedTomitaModularForm_apply] at hxk
            exact (inner_self_eq_zero (𝕜 := ℂ)).mp hxk
          simp only [complexDirectLimitModularForm_apply,
            directLimitModularForm_of_of]
          rw [commonStageModularPairing_eq_at
            Stage sys ω hclos i j k hik hjk]
          rw [closedTomitaModularForm_apply, hS]
          exact inner_zero_right (𝕜 := ℂ) _

/-- Diagonal-zero also implies membership in the right radical. -/
theorem diagonal_zero_implies_right_radical
    (z : D∞) (hz : q∞ z z = 0)
    (w : D∞) :
    q∞ w z = 0 := by
  have hleft :=
    diagonal_zero_implies_left_radical
      Stage sys ω hclos z hz w
  have hsymm :=
    complexDirectLimitModularForm_conj_symm
      Stage sys ω hclos z w
  rw [hleft] at hsymm
  exact star_eq_zero.mp hsymm

/-- The diagonal null space of the filtered modular form. -/
def modularNullSubmodule : Submodule ℂ D∞ where
  carrier := {z | q∞ z z = 0}
  zero_mem' := by
    simp
  add_mem' := by
    intro z w hz hw
    have hzw :=
      diagonal_zero_implies_left_radical
        Stage sys ω hclos z hz w
    have hwz :=
      diagonal_zero_implies_left_radical
        Stage sys ω hclos w hw z
    change q∞ (z + w) (z + w) = 0
    simp only [map_add, LinearMap.add_apply]
    rw [hz, hw, hzw, hwz]
    simp
  smul_mem' := by
    intro c z hz
    change
      directLimitModularForm Stage sys ω hclos
        (c • z) (c • z) = 0
    rw [directLimitModularForm_smul_left_complex,
      directLimitModularForm_smul_right_complex]
    have hraw :
        directLimitModularForm Stage sys ω hclos z z = 0 :=
      hz
    rw [hraw]
    simp

@[simp] theorem mem_modularNullSubmodule_iff
    (z : D∞) :
    z ∈ modularNullSubmodule Stage sys ω hclos ↔
      q∞ z z = 0 :=
  Iff.rfl

/-- Quotient by the modular null space. -/
abbrev ModularFormQuotient : Type u :=
  D∞ ⧸ modularNullSubmodule Stage sys ω hclos

/-- For a fixed first argument, the modular form descends through the null
quotient in its second argument. -/
def quotientModularFormRight
    (z : D∞) :
    ModularFormQuotient Stage sys ω hclos →ₗ[ℂ] ℂ :=
  (modularNullSubmodule Stage sys ω hclos).liftQ
    (q∞ z)
    (by
      intro w hw
      change q∞ z w = 0
      exact
        diagonal_zero_implies_right_radical
          Stage sys ω hclos w hw z)

@[simp] theorem quotientModularFormRight_mk
    (z w : D∞) :
    quotientModularFormRight Stage sys ω hclos z
        (Submodule.Quotient.mk w) =
      q∞ z w := by
  exact Submodule.liftQ_apply _ _ w

/-- The first argument as a conjugate-linear map into quotient
functionals. -/
def quotientModularFormOuter :
    D∞ →ₛₗ[starRingEnd ℂ]
      ModularFormQuotient Stage sys ω hclos →ₗ[ℂ] ℂ where
  toFun := quotientModularFormRight Stage sys ω hclos
  map_add' := by
    intro z₁ z₂
    ext qw
    simp only [LinearMap.comp_apply,
      Submodule.mkQ_apply, quotientModularFormRight_mk,
      map_add, LinearMap.add_apply]
  map_smul' := by
    intro c z
    ext qw
    simp only [LinearMap.comp_apply,
      Submodule.mkQ_apply, quotientModularFormRight_mk,
      LinearMap.smul_apply, map_smulₛₗ]

/-- The outer conjugate-linear map vanishes on the null submodule. -/
theorem modularNullSubmodule_le_quotientModularFormOuter_ker :
    modularNullSubmodule Stage sys ω hclos ≤
      (quotientModularFormOuter Stage sys ω hclos).ker := by
  intro z hz
  apply LinearMap.ext
  intro qw
  refine Submodule.Quotient.induction_on
    (modularNullSubmodule Stage sys ω hclos) qw ?_
  intro w
  simp only [quotientModularFormOuter,
    LinearMap.zero_apply]
  exact
    diagonal_zero_implies_left_radical
      Stage sys ω hclos z hz w

/-- Positive Hermitian modular form descended to the null-space quotient. -/
def quotientModularForm :
    ModularFormQuotient Stage sys ω hclos →ₛₗ[starRingEnd ℂ]
      ModularFormQuotient Stage sys ω hclos →ₗ[ℂ] ℂ :=
  (modularNullSubmodule Stage sys ω hclos).liftQ
    (quotientModularFormOuter Stage sys ω hclos)
    (modularNullSubmodule_le_quotientModularFormOuter_ker
      Stage sys ω hclos)

@[simp] theorem quotientModularForm_mk_mk
    (z w : D∞) :
    quotientModularForm Stage sys ω hclos
        (Submodule.Quotient.mk z)
        (Submodule.Quotient.mk w) =
      q∞ z w := by
  rw [quotientModularForm, Submodule.liftQ_apply]
  exact quotientModularFormRight_mk
    Stage sys ω hclos z w

/-- The quotient modular form is positive definite. -/
theorem quotientModularForm_self_eq_zero_iff
    (qz : ModularFormQuotient Stage sys ω hclos) :
    quotientModularForm Stage sys ω hclos qz qz = 0 ↔
      qz = 0 := by
  refine Submodule.Quotient.induction_on
    (modularNullSubmodule Stage sys ω hclos) qz ?_
  intro z
  rw [quotientModularForm_mk_mk]
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/-- Positivity descends to the modular quotient. -/
theorem quotientModularForm_nonneg
    (qz : ModularFormQuotient Stage sys ω hclos) :
    0 ≤
      Complex.re
        (quotientModularForm Stage sys ω hclos qz qz) := by
  refine Submodule.Quotient.induction_on
    (modularNullSubmodule Stage sys ω hclos) qz ?_
  intro z
  rw [quotientModularForm_mk_mk]
  exact
    complexDirectLimitModularForm_nonneg
      Stage sys ω hclos z

/-- Hermitian symmetry descends to the modular quotient. -/
theorem quotientModularForm_conj_symm
    (qz qw : ModularFormQuotient Stage sys ω hclos) :
    star
        (quotientModularForm
          Stage sys ω hclos qw qz) =
      quotientModularForm
        Stage sys ω hclos qz qw := by
  refine Submodule.Quotient.induction_on
    (modularNullSubmodule Stage sys ω hclos) qz ?_
  intro z
  refine Submodule.Quotient.induction_on
    (modularNullSubmodule Stage sys ω hclos) qw ?_
  intro w
  rw [quotientModularForm_mk_mk,
    quotientModularForm_mk_mk]
  exact
    complexDirectLimitModularForm_conj_symm
      Stage sys ω hclos z w

end CStarStateColimit.Native.FilteredGNSTomitaModularQuotient
