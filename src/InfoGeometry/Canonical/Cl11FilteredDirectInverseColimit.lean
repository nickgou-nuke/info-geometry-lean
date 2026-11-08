/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredDirectInverseColimit
import InfoGeometry.Canonical.FilteredDirectInverseColimitReadback

/-!
# Cl(1,1) forward/dual filtered colimit bridge

The matrix tower already has its algebraic forward maps and its compatible
normalized trace.  This owner exposes that data through the native
`DirectInductiveSystem` interface and proves the corresponding inverse system
law for the trace functionals.  No analytic completion or second colimit
carrier is introduced.

### Audit Classification (BUCKET 1 / BUCKET 2 / BUCKET 3)
- **BUCKET 1 (Genuine Constructive Theorems)**:
  - `cl11DirectSystem`, `cl11DirectSystem_one_step`
  - `normalizedTrace_dual_inverse_one_step`, `normalizedTrace_dual_inverse`,
    `normalizedTrace_isDualInverseFamily`
  - `cl11TraceCocone`, `cl11TraceColimitMap`, `cl11TraceColimitMap_stage`,
    `cl11TraceColimitMap_unique`, `cl11TraceFromInverseFamily`,
    `cl11TraceColimitMap_eq_inverseFamilyMap`
- **BUCKET 2 (Honest Numeric/Finite Certificates)**: None (all results are universally quantified over `m, n : ℕ`).
- **BUCKET 3 (Eliminated Debt)**: `0` `sorry`, `0` `admit`, `0` wrapper structures.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11FilteredDirectInverseColimit

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge
open FilteredColimit
open CategoryTheory
open CategoryTheory.Limits

/-- The existing Cl(1,1) matrix embeddings as a native module direct system. -/
def cl11DirectSystem :
    DirectInductiveSystem ℝ ℕ Stage :=
  DirectInductiveSystem.mk
    (fun {m n} h => (stageMapAlg m n h).toLinearMap)
    (by
      intro n
      apply LinearMap.ext
      intro x
      rw [stageMapAlg_refl]
      rfl)
    (by
      intro m n k hmn hnk
      apply LinearMap.ext
      intro x
      change stageMapAlg n k hnk (stageMapAlg m n hmn x) =
        stageMapAlg m k (hmn.trans hnk) x
      exact (stageMapAlg_apply_trans m n k hmn hnk x).symm)

/-- Evaluating `cl11DirectSystem.f (Nat.le_succ n)` agrees with `stageMapAlg n (n + 1)`. -/
@[simp] theorem cl11DirectSystem_one_step (n : ℕ) (A : Stage n) :
    cl11DirectSystem.f (Nat.le_succ n) A = stageMapAlg n (n + 1) (Nat.le_succ n) A := by
  have h : cl11DirectSystem.f (Nat.le_succ n) A = stageMapAlg n (n + 1) (Nat.le_succ n) A := rfl
  exact h

/-- The normalized trace is transported by the dual inverse transition. -/
theorem normalizedTrace_dual_inverse_one_step (n : ℕ) :
    FilteredColimit.InductiveCocone.dualInverseTransition
      cl11DirectSystem (Nat.le_succ n)
        (normalizedTraceLinear (n + 2)) = normalizedTraceLinear (n + 1) := by
  apply LinearMap.ext
  intro A
  change normalizedTrace (n + 2)
      (stageMapAlg n (n + 1) (Nat.le_succ n) A) = normalizedTrace (n + 1) A
  rw [stageMapAlg_succ n n le_rfl]
  rw [stageMapAlg_refl n]
  exact normalizedTrace_matStageEmbed (n + 1) A

/-- The same trace functional is stable along every finite inverse transition. -/
theorem normalizedTrace_dual_inverse (m n : ℕ) (h : m ≤ n) :
    FilteredColimit.InductiveCocone.dualInverseTransition
      cl11DirectSystem h
        (normalizedTraceLinear (n + 1)) = normalizedTraceLinear (m + 1) := by
  apply LinearMap.ext
  intro A
  change normalizedTrace (n + 1)
      (stageMapAlg m n h A) = normalizedTrace (m + 1) A
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n h ih =>
      rw [stageMapAlg_succ]
      simpa [stageMapAlg_succ] using
        (normalizedTrace_matStageEmbed (n + 1) (stageMapAlg m n h A)).trans ih

/-! ## Native filtered-colimit trace lift -/

/-- The inductive cocone formed by the normalized stage traces `(normalizedTraceLinear (n + 1))`. -/
def cl11TraceCocone :
    InductiveCocone ℝ cl11DirectSystem ℝ :=
  InductiveCocone.mk
    (fun n => normalizedTraceLinear (n + 1))
    (by
      intro m n h
      apply LinearMap.ext
      intro A
      change normalizedTrace (n + 1) (stageMapAlg m n h A) =
        normalizedTrace (m + 1) A
      exact congrArg (fun f => f A)
        (normalizedTrace_dual_inverse m n h))

/-- Universal colimit morphism descending `cl11TraceCocone` to `colimit (moduleDiagram cl11DirectSystem)`. -/
noncomputable def cl11TraceColimitMap :
    colimit (FilteredColimit.Native.moduleDiagram cl11DirectSystem) ⟶
      ModuleCat.of ℝ ℝ :=
  FilteredColimit.Native.descendModuleCocone
    cl11DirectSystem cl11TraceCocone

/-- The normalized trace stages form an inverse-compatible family in the
dual system, using the generic duality interface. -/
theorem normalizedTrace_isDualInverseFamily :
    FilteredColimit.InductiveCocone.IsDualInverseFamily
      (sys := cl11DirectSystem) (fun n => normalizedTraceLinear (n + 1)) := by
  intro m n h
  exact normalizedTrace_dual_inverse m n h

/-- Evaluating `cl11TraceColimitMap` on the `n`-th stage injection recovers `normalizedTraceLinear (n + 1)`. -/
@[simp] theorem cl11TraceColimitMap_stage (n : ℕ) (A : Stage n) :
    cl11TraceColimitMap.hom
      ((CategoryTheory.Limits.colimit.ι
          (FilteredColimit.Native.moduleDiagram cl11DirectSystem) n).hom A) =
      normalizedTraceLinear (n + 1) A := by
  have hfac := FilteredColimit.Native.moduleColimit_desc_stage
    cl11DirectSystem cl11TraceCocone n
  exact congrArg (fun f => f A) hfac

/-- Uniqueness of `cl11TraceColimitMap` as the universal morphism agreeing with the stage traces. -/
theorem cl11TraceColimitMap_unique
    (g : colimit (FilteredColimit.Native.moduleDiagram cl11DirectSystem) ⟶
      ModuleCat.of ℝ ℝ)
    (hg : ∀ n,
      colimit.ι (FilteredColimit.Native.moduleDiagram cl11DirectSystem) n ≫ g =
        (FilteredColimit.Native.moduleCocone
          cl11DirectSystem cl11TraceCocone).ι.app n) :
    g = cl11TraceColimitMap := by
  apply colimit.hom_ext
  intro n
  rw [hg n]
  exact (FilteredColimit.Native.moduleColimit_desc_stage
    cl11DirectSystem cl11TraceCocone n).symm

/-- The trace cocone map and the map reconstructed from its inverse family
are equal by their finite-stage readouts and categorical colimit uniqueness. -/
noncomputable def cl11TraceFromInverseFamily :
    colimit (FilteredColimit.Native.moduleDiagram cl11DirectSystem) ⟶
      ModuleCat.of ℝ ℝ :=
  FilteredColimit.InductiveCocone.dualInverseFamilyColimitMap
    (sys := cl11DirectSystem) (fun n => normalizedTraceLinear (n + 1))
    normalizedTrace_isDualInverseFamily

/-- Identity between `cl11TraceColimitMap` and `cl11TraceFromInverseFamily`. -/
theorem cl11TraceColimitMap_eq_inverseFamilyMap :
    cl11TraceColimitMap = cl11TraceFromInverseFamily := by
  apply colimit.hom_ext
  intro n
  ext A
  change cl11TraceColimitMap.hom
      ((colimit.ι (FilteredColimit.Native.moduleDiagram cl11DirectSystem) n).hom A) =
    cl11TraceFromInverseFamily.hom
      ((colimit.ι (FilteredColimit.Native.moduleDiagram cl11DirectSystem) n).hom A)
  exact (cl11TraceColimitMap_stage n A).trans
    (FilteredColimit.InductiveCocone.dualInverseFamilyColimitMap_stage
      (sys := cl11DirectSystem) (fun n => normalizedTraceLinear (n + 1))
      normalizedTrace_isDualInverseFamily n A).symm

end InfoGeometry.Canonical.Cl11FilteredDirectInverseColimit
