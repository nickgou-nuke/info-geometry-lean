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

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

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

/-- Additivity in the first representative. -/
theorem commonStageModularPairing_add_left
    (i j : I)
    (x₁ x₂ : closedTomitaDomain (ω.state i))
    (y : closedTomitaDomain (ω.state j)) :
    commonStageModularPairing Stage sys ω hclos i j
        (x₁ + x₂) y =
      commonStageModularPairing Stage sys ω hclos i j x₁ y +
        commonStageModularPairing Stage sys ω hclos i j x₂ y := by
  unfold commonStageModularPairing
  simp only [map_add, LinearMap.add_apply]

/-- Real homogeneity in the first representative. -/
theorem commonStageModularPairing_smul_left
    (i j : I) (r : ℝ)
    (x : closedTomitaDomain (ω.state i))
    (y : closedTomitaDomain (ω.state j)) :
    commonStageModularPairing Stage sys ω hclos i j
        (r • x) y =
      r • commonStageModularPairing
        Stage sys ω hclos i j x y := by
  unfold commonStageModularPairing
  rw [map_smul]
  change
    closedTomitaModularForm Stage sys ω hclos
        (commonUpper i j)
        ((r : ℂ) •
          domainTransition Stage sys ω
            (le_commonUpper_left i j) x)
        (domainTransition Stage sys ω
          (le_commonUpper_right i j) y) =
      (r : ℂ) •
        closedTomitaModularForm Stage sys ω hclos
          (commonUpper i j)
          (domainTransition Stage sys ω
            (le_commonUpper_left i j) x)
          (domainTransition Stage sys ω
            (le_commonUpper_right i j) y)
  rw [map_smulₛₗ]
  simp

/-- Additivity in the second representative. -/
theorem commonStageModularPairing_add_right
    (i j : I)
    (x : closedTomitaDomain (ω.state i))
    (y₁ y₂ : closedTomitaDomain (ω.state j)) :
    commonStageModularPairing Stage sys ω hclos i j
        x (y₁ + y₂) =
      commonStageModularPairing Stage sys ω hclos i j x y₁ +
        commonStageModularPairing Stage sys ω hclos i j x y₂ := by
  unfold commonStageModularPairing
  simp only [map_add]

/-- Real homogeneity in the second representative. -/
theorem commonStageModularPairing_smul_right
    (i j : I) (r : ℝ)
    (x : closedTomitaDomain (ω.state i))
    (y : closedTomitaDomain (ω.state j)) :
    commonStageModularPairing Stage sys ω hclos i j
        x (r • y) =
      r • commonStageModularPairing
        Stage sys ω hclos i j x y := by
  unfold commonStageModularPairing
  rw [map_smul]
  change
    closedTomitaModularForm Stage sys ω hclos
        (commonUpper i j)
        (domainTransition Stage sys ω
          (le_commonUpper_left i j) x)
        ((r : ℂ) •
          domainTransition Stage sys ω
            (le_commonUpper_right i j) y) =
      (r : ℂ) •
        closedTomitaModularForm Stage sys ω hclos
          (commonUpper i j)
          (domainTransition Stage sys ω
            (le_commonUpper_left i j) x)
          (domainTransition Stage sys ω
            (le_commonUpper_right i j) y)
  rw [map_smul]

/-- Compatibility when the second representative is transported forward. -/
theorem commonStageModularPairing_map_right
    (i j k : I) (hjk : j ≤ k)
    (x : closedTomitaDomain (ω.state i))
    (y : closedTomitaDomain (ω.state j)) :
    commonStageModularPairing Stage sys ω hclos i k x
        (domainTransition Stage sys ω hjk y) =
      commonStageModularPairing Stage sys ω hclos i j x y := by
  let m := commonUpper i k
  have him : i ≤ m := le_commonUpper_left i k
  have hkm : k ≤ m := le_commonUpper_right i k
  rw [commonStageModularPairing_eq_at
    Stage sys ω hclos i k m him hkm]
  rw [commonStageModularPairing_eq_at
    Stage sys ω hclos i j m him (le_trans hjk hkm)]
  rw [domainTransition_comp_apply Stage sys ω hjk hkm y]

/-- Compatibility when the first representative is transported forward. -/
theorem commonStageModularPairing_map_left
    (i j k : I) (hij : i ≤ j)
    (x : closedTomitaDomain (ω.state i))
    (y : closedTomitaDomain (ω.state k)) :
    commonStageModularPairing Stage sys ω hclos j k
        (domainTransition Stage sys ω hij x) y =
      commonStageModularPairing Stage sys ω hclos i k x y := by
  let m := commonUpper j k
  have hjm : j ≤ m := le_commonUpper_left j k
  have hkm : k ≤ m := le_commonUpper_right j k
  rw [commonStageModularPairing_eq_at
    Stage sys ω hclos j k m hjm hkm]
  rw [commonStageModularPairing_eq_at
    Stage sys ω hclos i k m (le_trans hij hjm) hkm]
  rw [domainTransition_comp_apply Stage sys ω hij hjm x]

/-- For a fixed first-stage representative, pairing against one later stage is
a real-linear functional. -/
def pairingRightAtStage
    (i : I) (x : closedTomitaDomain (ω.state i))
    (j : I) :
    closedTomitaDomain (ω.state j) →ₗ[ℝ] ℂ where
  toFun := commonStageModularPairing Stage sys ω hclos i j x
  map_add' :=
    commonStageModularPairing_add_right
      Stage sys ω hclos i j x
  map_smul' := by
    intro r y
    exact
      commonStageModularPairing_smul_right
        Stage sys ω hclos i j r x y

/-- The right-stage functionals form a cocone over the real domain system. -/
theorem pairingRightAtStage_compatible
    (i : I) (x : closedTomitaDomain (ω.state i))
    (j k : I) (hjk : j ≤ k)
    (y : closedTomitaDomain (ω.state j)) :
    pairingRightAtStage Stage sys ω hclos i x k
        (domainTransition Stage sys ω hjk y) =
      pairingRightAtStage Stage sys ω hclos i x j y :=
  commonStageModularPairing_map_right
    Stage sys ω hclos i j k hjk x y

/-- Pair a fixed stage representative against the genuine real module direct
limit. -/
def pairStageAgainstDirectLimit
    (i : I) (x : closedTomitaDomain (ω.state i)) :
    ClosedDomainDirectLimit Stage sys ω →ₗ[ℝ] ℂ :=
  Module.DirectLimit.lift
    ℝ I
    (fun j => closedTomitaDomain (ω.state j))
    (fun _ _ hjk => domainTransition Stage sys ω hjk)
    (pairingRightAtStage
      Stage sys ω (hclos := hclos) i x)
    (pairingRightAtStage_compatible
      Stage sys ω (hclos := hclos) i x)

@[simp] theorem pairStageAgainstDirectLimit_of
    (i j : I)
    (x : closedTomitaDomain (ω.state i))
    (y : closedTomitaDomain (ω.state j)) :
    pairStageAgainstDirectLimit Stage sys ω hclos i x
        (Module.DirectLimit.of
          ℝ I
          (fun k => closedTomitaDomain (ω.state k))
          (fun _ _ h => domainTransition Stage sys ω h)
          j y) =
      commonStageModularPairing Stage sys ω hclos i j x y := by
  simpa only [pairingRightAtStage] using
    (Module.DirectLimit.lift_of
      (g := pairingRightAtStage
        Stage sys ω (hclos := hclos) i x)
      (pairingRightAtStage_compatible
        Stage sys ω (hclos := hclos) i x)
      (i := j) y)

/-- A first-stage vector determines a real-linear functional on the direct
limit. -/
def stageToDirectLimitFunctional
    (i : I) :
    closedTomitaDomain (ω.state i) →ₗ[ℝ]
      (ClosedDomainDirectLimit Stage sys ω →ₗ[ℝ] ℂ) where
  toFun :=
    pairStageAgainstDirectLimit
      Stage sys ω (hclos := hclos) i
  map_add' := by
    intro x₁ x₂
    apply LinearMap.ext
    intro z
    induction z using Module.DirectLimit.induction_on with
    | ih j y =>
        simp only [pairStageAgainstDirectLimit_of,
          LinearMap.add_apply]
        exact
          commonStageModularPairing_add_left
            Stage sys ω hclos i j x₁ x₂ y
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro z
    induction z using Module.DirectLimit.induction_on with
    | ih j y =>
        simp only [pairStageAgainstDirectLimit_of,
          LinearMap.smul_apply]
        exact
          commonStageModularPairing_smul_left
            Stage sys ω hclos i j r x y

/-- The first-stage functionals also form a cocone. -/
theorem stageToDirectLimitFunctional_compatible
    (i j : I) (hij : i ≤ j)
    (x : closedTomitaDomain (ω.state i)) :
    stageToDirectLimitFunctional
        Stage sys ω (hclos := hclos) j
        (domainTransition Stage sys ω hij x) =
      stageToDirectLimitFunctional
        Stage sys ω (hclos := hclos) i x := by
  apply LinearMap.ext
  intro z
  induction z using Module.DirectLimit.induction_on with
  | ih k y =>
      change
        pairStageAgainstDirectLimit
            Stage sys ω hclos j
            (domainTransition Stage sys ω hij x)
            (Module.DirectLimit.of
              ℝ I
              (fun l => closedTomitaDomain (ω.state l))
              (fun _ _ h => domainTransition Stage sys ω h)
              k y) =
          pairStageAgainstDirectLimit
            Stage sys ω hclos i x
            (Module.DirectLimit.of
              ℝ I
              (fun l => closedTomitaDomain (ω.state l))
              (fun _ _ h => domainTransition Stage sys ω h)
              k y)
      rw [pairStageAgainstDirectLimit_of,
        pairStageAgainstDirectLimit_of]
      exact
        commonStageModularPairing_map_left
          Stage sys ω hclos i j k hij x y

/-- The full complex-valued Tomita modular form descended to the genuine
filtered real module direct limit. -/
def directLimitModularForm :
    ClosedDomainDirectLimit Stage sys ω →ₗ[ℝ]
      ClosedDomainDirectLimit Stage sys ω →ₗ[ℝ] ℂ :=
  Module.DirectLimit.lift
    ℝ I
    (fun i => closedTomitaDomain (ω.state i))
    (fun _ _ hij => domainTransition Stage sys ω hij)
    (stageToDirectLimitFunctional
      Stage sys ω (hclos := hclos))
    (stageToDirectLimitFunctional_compatible
      Stage sys ω (hclos := hclos))

/-- The descended form evaluates on canonical representatives by transporting
them to any common upper stage. -/
@[simp] theorem directLimitModularForm_of_of
    (i j : I)
    (x : closedTomitaDomain (ω.state i))
    (y : closedTomitaDomain (ω.state j)) :
    directLimitModularForm Stage sys ω hclos
        (Module.DirectLimit.of
          ℝ I
          (fun k => closedTomitaDomain (ω.state k))
          (fun _ _ h => domainTransition Stage sys ω h)
          i x)
        (Module.DirectLimit.of
          ℝ I
          (fun k => closedTomitaDomain (ω.state k))
          (fun _ _ h => domainTransition Stage sys ω h)
          j y) =
      commonStageModularPairing Stage sys ω hclos i j x y := by
  change
    (Module.DirectLimit.lift
      ℝ I
      (fun k => closedTomitaDomain (ω.state k))
      (fun _ _ h => domainTransition Stage sys ω h)
      (stageToDirectLimitFunctional
        Stage sys ω (hclos := hclos))
      (stageToDirectLimitFunctional_compatible
        Stage sys ω (hclos := hclos)))
      (Module.DirectLimit.of
        ℝ I
        (fun k => closedTomitaDomain (ω.state k))
        (fun _ _ h => domainTransition Stage sys ω h)
        i x)
      (Module.DirectLimit.of
        ℝ I
        (fun k => closedTomitaDomain (ω.state k))
        (fun _ _ h => domainTransition Stage sys ω h)
        j y) =
      commonStageModularPairing Stage sys ω hclos i j x y
  rw [Module.DirectLimit.lift_of]
  exact
    pairStageAgainstDirectLimit_of
      Stage sys ω hclos i j x y

/-- Positivity survives passage to the filtered direct limit.  The proof uses
the native representative induction principle, not a chosen global
coordinate presentation. -/
theorem directLimitModularForm_nonneg
    (z : ClosedDomainDirectLimit Stage sys ω) :
    0 ≤
      Complex.re
        (directLimitModularForm Stage sys ω hclos z z) := by
  induction z using Module.DirectLimit.induction_on with
  | ih i x =>
      rw [directLimitModularForm_of_of]
      unfold commonStageModularPairing
      exact
        closedTomitaModularForm_nonneg
          Stage sys ω hclos
          (commonUpper i i)
          (domainTransition Stage sys ω
            (le_commonUpper_left i i) x)

end CStarStateColimit.Native.FilteredGNSTomitaModularFormColimit
