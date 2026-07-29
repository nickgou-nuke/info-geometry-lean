import InfoGeometry.Canonical.FilteredGNSTomitaModularForm
import Mathlib.Algebra.Colimit.Module

/-!
# Filtered direct-limit descent of the Tomita modular form

The stage modular forms are preserved by the filtered closed-domain
transitions.  Filteredness lets any two representatives be compared at a
common upper stage.  This file uses that comparison to descend the full
complex-valued two-variable form to Mathlib's genuine algebraic module direct
limit.

The descended map is real-bilinear.  This is not a scalar reduction: its value
is still complex and both operator-domain variables remain present.  The
realification is forced by the conjugate-linearity of the Tomita operator.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaModularFormColimit

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaClosedTransport
open CStarStateColimit.Native.FilteredGNSTomitaRealColimit
open CStarStateColimit.Native.FilteredGNSTomitaModularForm

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

/-- A chosen common upper stage in the filtered index. -/
noncomputable def commonUpper (i j : I) : I :=
  Classical.choose (exists_ge_ge i j)

theorem le_commonUpper_left (i j : I) :
    i ≤ commonUpper i j :=
  (Classical.choose_spec (exists_ge_ge i j)).1

theorem le_commonUpper_right (i j : I) :
    j ≤ commonUpper i j :=
  (Classical.choose_spec (exists_ge_ge i j)).2

/-- Real-linear transition used by Mathlib's algebraic module direct limit. -/
def domainTransition {i j : I} (hij : i ≤ j) :
    closedTomitaDomain (ω.state i) →ₗ[ℝ]
      closedTomitaDomain (ω.state j) :=
  filteredClosedTomitaDomainRealMap Stage sys ω hij

set_option synthInstance.maxHeartbeats 80000 in
/-- The algebraic filtered direct limit of the realified closed Tomita
domains. -/
abbrev ClosedDomainDirectLimit : Type u :=
  Module.DirectLimit
    (fun i => closedTomitaDomain (ω.state i))
    (fun _ _ hij => domainTransition Stage sys ω hij)

/-- Composition of closed-domain transitions, evaluated on a vector. -/
theorem domainTransition_comp_apply
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (x : closedTomitaDomain (ω.state i)) :
    domainTransition Stage sys ω hjk
        (domainTransition Stage sys ω hij x) =
      domainTransition Stage sys ω (le_trans hij hjk) x := by
  exact congrArg
    (fun f :
      closedTomitaDomain (ω.state i) →ₗ[ℝ]
        closedTomitaDomain (ω.state k) => f x)
    ((closedTomitaDomainRealDirectSystem
      Stage sys ω).f_comp hij hjk)

/-- Evaluate two stage representatives at the chosen common upper stage. -/
def commonStageModularPairing
    (i j : I)
    (x : closedTomitaDomain (ω.state i))
    (y : closedTomitaDomain (ω.state j)) : ℂ :=
  let k := commonUpper i j
  closedTomitaModularForm Stage sys ω hclos k
    (domainTransition Stage sys ω
      (le_commonUpper_left i j) x)
    (domainTransition Stage sys ω
      (le_commonUpper_right i j) y)

/-- Evaluation at any common upper stage agrees with the chosen-stage
definition.  This is the representative-independence theorem on which the
direct-limit descent rests. -/
theorem commonStageModularPairing_eq_at
    (i j k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (x : closedTomitaDomain (ω.state i))
    (y : closedTomitaDomain (ω.state j)) :
    commonStageModularPairing Stage sys ω hclos i j x y =
      closedTomitaModularForm Stage sys ω hclos k
        (domainTransition Stage sys ω hik x)
        (domainTransition Stage sys ω hjk y) := by
  let c := commonUpper i j
  obtain ⟨m, hcm, hkm⟩ := exists_ge_ge c k
  have hc :
      closedTomitaModularForm Stage sys ω hclos c
          (domainTransition Stage sys ω
            (le_commonUpper_left i j) x)
          (domainTransition Stage sys ω
            (le_commonUpper_right i j) y) =
        closedTomitaModularForm Stage sys ω hclos m
          (domainTransition Stage sys ω
            (le_trans (le_commonUpper_left i j) hcm) x)
          (domainTransition Stage sys ω
            (le_trans (le_commonUpper_right i j) hcm) y) := by
    rw [← domainTransition_comp_apply
      Stage sys ω (le_commonUpper_left i j) hcm x]
    rw [← domainTransition_comp_apply
      Stage sys ω (le_commonUpper_right i j) hcm y]
    exact
      (filteredClosedTomitaDomainMap_preserves_modularForm
        Stage sys ω hclos hcm
        (domainTransition Stage sys ω
          (le_commonUpper_left i j) x)
        (domainTransition Stage sys ω
          (le_commonUpper_right i j) y)).symm
  have hk :
      closedTomitaModularForm Stage sys ω hclos k
          (domainTransition Stage sys ω hik x)
          (domainTransition Stage sys ω hjk y) =
        closedTomitaModularForm Stage sys ω hclos m
          (domainTransition Stage sys ω
            (le_trans hik hkm) x)
          (domainTransition Stage sys ω
            (le_trans hjk hkm) y) := by
    rw [← domainTransition_comp_apply
      Stage sys ω hik hkm x]
    rw [← domainTransition_comp_apply
      Stage sys ω hjk hkm y]
    exact
      (filteredClosedTomitaDomainMap_preserves_modularForm
        Stage sys ω hclos hkm
        (domainTransition Stage sys ω hik x)
        (domainTransition Stage sys ω hjk y)).symm
  unfold commonStageModularPairing
  dsimp only
  rw [hc, hk]

end CStarStateColimit.Native.FilteredGNSTomitaModularFormColimit
