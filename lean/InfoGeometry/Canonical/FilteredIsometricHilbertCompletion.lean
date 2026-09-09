import InfoGeometry.Canonical.FilteredIsometricInnerProductDirectLimit

/-!
# Hilbert completion of a filtered isometric direct system

An isometric filtered system of complex inner-product spaces has a genuine
Mathlib module direct limit.  The common-stage inner product constructed in
`FilteredIsometricInnerProductDirectLimit` is positive definite on that
carrier.  This file installs it as a native `InnerProductSpace.Core` and takes
the uniform completion.

No ambient Hilbert space or compatibility witness is assumed: the inner
product and complex scalar action are both descended from the transition
isometries.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricInnerProductDirectLimit

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (E : I → Type u)
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, InnerProductSpace ℂ (E i)]
variable (sys : IsometricDirectSystem E)

local notation "D∞" => RealDirectLimit E sys

/-- The positive-definite common-stage pairing, installed as Mathlib's native
inner-product core on the algebraic filtered colimit. -/
def directLimitInnerProductCore :
    InnerProductSpace.Core ℂ D∞ where
  inner := fun x y => directLimitInner E sys x y
  conj_inner_symm := directLimitInner_conj_symm E sys
  re_inner_nonneg := directLimitInner_nonneg E sys
  add_left := by
    intro x y z
    exact LinearMap.congr_fun
      ((directLimitInner E sys).map_add x y) z
  smul_left := by
    intro x y c
    have h := (directLimitInner E sys).map_smulₛₗ c x
    have happ := LinearMap.congr_fun h y
    simpa only [LinearMap.smul_apply, smul_eq_mul] using happ
  definite := by
    intro x hx
    exact (directLimitInner_self_eq_zero_iff E sys x).mp hx

noncomputable instance directLimitInnerProductCoreInst :
    InnerProductSpace.Core ℂ D∞ :=
  directLimitInnerProductCore E sys

noncomputable instance directLimitPreInnerProductCoreInst :
    PreInnerProductSpace.Core ℂ D∞ :=
  (directLimitInnerProductCore E sys).toCore

noncomputable instance directLimitNormedAddCommGroup :
    NormedAddCommGroup D∞ :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

noncomputable instance directLimitInnerProductSpace :
    InnerProductSpace ℂ D∞ :=
  InnerProductSpace.ofCore
    (directLimitInnerProductCore E sys).toCore

@[simp] theorem directLimit_inner_eq
    (x y : D∞) :
    inner ℂ x y = directLimitInner E sys x y :=
  rfl

theorem directLimit_inner_self_eq_zero_iff
    (x : D∞) :
    inner ℂ x x = 0 ↔ x = 0 := by
  rw [directLimit_inner_eq]
  exact directLimitInner_self_eq_zero_iff E sys x

/-- Canonical complex-linear inclusion of one stage into the algebraic
filtered colimit. -/
def stageToDirectLimitLinearMap
    (i : I) :
    E i →ₗ[ℂ] D∞ where
  toFun :=
    Module.DirectLimit.of
      ℝ I E
      (fun _ _ h => realTransition E sys h)
      i
  map_add' := by
    intro x y
    exact map_add _ x y
  map_smul' := by
    intro c x
    exact (complex_smul_of E sys c i x).symm

/-- Stage inclusions preserve the inner product exactly. -/
@[simp] theorem stageToDirectLimitLinearMap_inner
    (i : I) (x y : E i) :
    inner ℂ
        (stageToDirectLimitLinearMap E sys i x)
        (stageToDirectLimitLinearMap E sys i y) =
      inner ℂ x y := by
  change
    inner ℂ
        (Module.DirectLimit.of
          ℝ I E
          (fun _ _ h => realTransition E sys h)
          i x)
        (Module.DirectLimit.of
          ℝ I E
          (fun _ _ h => realTransition E sys h)
          i y) =
      inner ℂ x y
  rw [directLimit_inner_eq, directLimitInner_apply,
    realDirectLimitInner_of_of]
  unfold commonStageInner
  exact
    (sys.map (le_commonUpper_left i i)).inner_map_map x y

/-- Canonical stage inclusion bundled as a complex linear isometry. -/
def stageToDirectLimitLinearIsometry
    (i : I) :
    E i →ₗᵢ[ℂ] D∞ :=
  LinearIsometry.mk
    (stageToDirectLimitLinearMap E sys i)
    (fun x => by
      have hinner :=
        stageToDirectLimitLinearMap_inner E sys i x x
      have hsource := inner_self_eq_norm_sq (𝕜 := ℂ) x
      have htarget :=
        inner_self_eq_norm_sq (𝕜 := ℂ)
          (stageToDirectLimitLinearMap E sys i x)
      have hnonneg_source : 0 ≤ ‖x‖ := norm_nonneg x
      have hnonneg_target :
          0 ≤ ‖stageToDirectLimitLinearMap E sys i x‖ :=
        norm_nonneg _
      rw [hinner] at htarget
      nlinarith)

@[simp] theorem stageToDirectLimitLinearIsometry_apply
    (i : I) (x : E i) :
    stageToDirectLimitLinearIsometry E sys i x =
      stageToDirectLimitLinearMap E sys i x :=
  rfl

/-- The algebraic stage inclusions satisfy the defining colimit relation. -/
theorem stageToDirectLimitLinearMap_transition
    {i j : I} (hij : i ≤ j) (x : E i) :
    stageToDirectLimitLinearMap E sys j (sys.map hij x) =
      stageToDirectLimitLinearMap E sys i x := by
  exact Module.DirectLimit.of_f

/-- Hilbert completion of the algebraic filtered isometric colimit. -/
abbrev HilbertDirectLimit : Type u :=
  UniformSpace.Completion D∞

/-- Canonical dense embedding of the algebraic colimit into its Hilbert
completion. -/
def directLimitToCompletion :
    D∞ → HilbertDirectLimit E sys :=
  UniformSpace.Completion.coe'

theorem directLimitToCompletion_isometry :
    Isometry (directLimitToCompletion E sys) :=
  UniformSpace.Completion.coe_isometry

theorem directLimitToCompletion_denseRange :
    DenseRange (directLimitToCompletion E sys) :=
  UniformSpace.Completion.denseRange_coe

/-- The canonical completion map as a complex-linear map. -/
def directLimitToCompletionLinearMap :
    D∞ →ₗ[ℂ] HilbertDirectLimit E sys where
  toFun := directLimitToCompletion E sys
  map_add' := by
    intro x y
    exact UniformSpace.Completion.coe_add x y
  map_smul' := by
    intro c x
    exact UniformSpace.Completion.coe_smul c x

/-- The canonical dense embedding bundled as a complex linear isometry. -/
def directLimitToCompletionLinearIsometry :
    D∞ →ₗᵢ[ℂ] HilbertDirectLimit E sys :=
  LinearIsometry.mk
    (directLimitToCompletionLinearMap E sys)
    (fun x => by
      have h := (directLimitToCompletion_isometry E sys).dist_eq x 0
      simpa only [directLimitToCompletion,
        UniformSpace.Completion.coe_zero,
        dist_zero_right] using h)

@[simp] theorem directLimitToCompletionLinearIsometry_apply
    (x : D∞) :
    directLimitToCompletionLinearIsometry E sys x =
      directLimitToCompletion E sys x :=
  rfl

theorem hilbertDirectLimit_complete :
    CompleteSpace (HilbertDirectLimit E sys) :=
  inferInstance

/-- Canonical isometric inclusion of each stage into the completed filtered
Hilbert colimit. -/
def stageToHilbertDirectLimit
    (i : I) :
    E i →ₗᵢ[ℂ] HilbertDirectLimit E sys :=
  LinearIsometry.mk
    ((directLimitToCompletionLinearIsometry E sys).toLinearMap.comp
      (stageToDirectLimitLinearIsometry E sys i).toLinearMap)
    (fun x => by
      change
        ‖directLimitToCompletionLinearIsometry E sys
            (stageToDirectLimitLinearIsometry E sys i x)‖ =
          ‖x‖
      rw [(directLimitToCompletionLinearIsometry E sys).norm_map,
        (stageToDirectLimitLinearIsometry E sys i).norm_map])

@[simp] theorem stageToHilbertDirectLimit_apply
    (i : I) (x : E i) :
    stageToHilbertDirectLimit E sys i x =
      directLimitToCompletion E sys
        (stageToDirectLimitLinearMap E sys i x) :=
  rfl

/-- The completed stage embeddings retain the exact colimit transition
relation. -/
theorem stageToHilbertDirectLimit_transition
    {i j : I} (hij : i ≤ j) (x : E i) :
    stageToHilbertDirectLimit E sys j (sys.map hij x) =
      stageToHilbertDirectLimit E sys i x := by
  rw [stageToHilbertDirectLimit_apply,
    stageToHilbertDirectLimit_apply]
  exact congrArg
    (directLimitToCompletion E sys)
    (stageToDirectLimitLinearMap_transition E sys hij x)

/-- The union of the stage images is dense in the completed filtered Hilbert
colimit.  Thus the completion introduces no extra finite-stage generators. -/
theorem dense_iUnion_range_stageToHilbertDirectLimit :
    Dense
      (⋃ i : I,
        Set.range (stageToHilbertDirectLimit E sys i)) := by
  apply (directLimitToCompletion_denseRange E sys).mono
  rintro y ⟨z, rfl⟩
  induction z using Module.DirectLimit.induction_on with
  | ih i x =>
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      refine ⟨x, ?_⟩
      rfl

end InfoGeometry.Canonical.FilteredIsometricHilbertCompletion
