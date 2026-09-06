import Mathlib.Algebra.Colimit.Module
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Filtered colimits of complex inner-product spaces

Mathlib provides algebraic module direct limits but no owner specialized to
directed systems of inner-product spaces and linear isometries.  This file
begins that missing reusable layer.  It defines coherent isometric systems,
their algebraic real direct-limit carrier, and the common-stage inner pairing
with a proof that its value is independent of the chosen upper stage.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredIsometricInnerProductColimit

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

universe u

variable {I : Type u} [Preorder I]
variable (E : I → Type u)
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, InnerProductSpace ℂ (E i)]

/-- A coherent directed system whose transition maps are complex linear
isometries. -/
structure IsometricDirectSystem where
  map : ∀ {i j : I}, i ≤ j → E i →ₗᵢ[ℂ] E j
  map_id : ∀ i, map (le_refl i) = LinearIsometry.id
  map_comp :
    ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k),
      (map hjk).comp (map hij) = map (le_trans hij hjk)

variable (sys : IsometricDirectSystem E)

/-- Transition composition evaluated on a vector. -/
theorem map_comp_apply
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (x : E i) :
    sys.map hjk (sys.map hij x) =
      sys.map (le_trans hij hjk) x := by
  exact congrArg
    (fun f : E i →ₗᵢ[ℂ] E k => f x)
    (sys.map_comp hij hjk)

/-- Real-linear restriction of an isometric transition. -/
def realTransition
    {i j : I} (hij : i ≤ j) :
    E i →ₗ[ℝ] E j where
  toFun := sys.map hij
  map_add' := (sys.map hij).map_add
  map_smul' := by
    intro r x
    have h := (sys.map hij).map_smul (r : ℂ) x
    simpa using h

variable [Nonempty I] [IsDirectedOrder I] [DecidableEq I]

/-- Algebraic real module direct limit of the isometric system. -/
abbrev RealDirectLimit : Type u :=
  Module.DirectLimit E
    (fun _ _ hij => realTransition E sys hij)

/-- A chosen common upper index. -/
def commonUpper (i j : I) : I :=
  Classical.choose (exists_ge_ge i j)

theorem le_commonUpper_left (i j : I) :
    i ≤ commonUpper i j :=
  (Classical.choose_spec (exists_ge_ge i j)).1

theorem le_commonUpper_right (i j : I) :
    j ≤ commonUpper i j :=
  (Classical.choose_spec (exists_ge_ge i j)).2

/-- Inner product of two representatives after transport to the chosen common
upper stage. -/
def commonStageInner
    (i j : I) (x : E i) (y : E j) : ℂ :=
  inner ℂ
    (sys.map (le_commonUpper_left i j) x)
    (sys.map (le_commonUpper_right i j) y)

/-- Evaluation at any common upper stage agrees with `commonStageInner`. -/
theorem commonStageInner_eq_at
    (i j k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (x : E i) (y : E j) :
    commonStageInner E sys i j x y =
      inner ℂ (sys.map hik x) (sys.map hjk y) := by
  let c := commonUpper i j
  obtain ⟨m, hcm, hkm⟩ := exists_ge_ge c k
  have hc :
      inner ℂ
          (sys.map (le_commonUpper_left i j) x)
          (sys.map (le_commonUpper_right i j) y) =
        inner ℂ
          (sys.map (le_trans (le_commonUpper_left i j) hcm) x)
          (sys.map (le_trans (le_commonUpper_right i j) hcm) y) := by
    rw [← map_comp_apply E sys
      (le_commonUpper_left i j) hcm x]
    rw [← map_comp_apply E sys
      (le_commonUpper_right i j) hcm y]
    exact
      ((sys.map hcm).inner_map_map
        (sys.map (le_commonUpper_left i j) x)
        (sys.map (le_commonUpper_right i j) y)).symm
  have hk :
      inner ℂ (sys.map hik x) (sys.map hjk y) =
        inner ℂ
          (sys.map (le_trans hik hkm) x)
          (sys.map (le_trans hjk hkm) y) := by
    rw [← map_comp_apply E sys hik hkm x]
    rw [← map_comp_apply E sys hjk hkm y]
    exact
      ((sys.map hkm).inner_map_map
        (sys.map hik x) (sys.map hjk y)).symm
  unfold commonStageInner
  rw [hc, hk]

/-- Transporting the first representative does not change the common-stage
inner product. -/
theorem commonStageInner_map_left
    (i j k : I) (hij : i ≤ j)
    (x : E i) (y : E k) :
    commonStageInner E sys j k (sys.map hij x) y =
      commonStageInner E sys i k x y := by
  let m := commonUpper j k
  have hjm : j ≤ m := le_commonUpper_left j k
  have hkm : k ≤ m := le_commonUpper_right j k
  rw [commonStageInner_eq_at E sys j k m hjm hkm]
  rw [commonStageInner_eq_at E sys i k m
    (le_trans hij hjm) hkm]
  rw [map_comp_apply E sys hij hjm x]

/-- Transporting the second representative does not change the common-stage
inner product. -/
theorem commonStageInner_map_right
    (i j k : I) (hjk : j ≤ k)
    (x : E i) (y : E j) :
    commonStageInner E sys i k x (sys.map hjk y) =
      commonStageInner E sys i j x y := by
  let m := commonUpper i k
  have him : i ≤ m := le_commonUpper_left i k
  have hkm : k ≤ m := le_commonUpper_right i k
  rw [commonStageInner_eq_at E sys i k m him hkm]
  rw [commonStageInner_eq_at E sys i j m him
    (le_trans hjk hkm)]
  rw [map_comp_apply E sys hjk hkm y]

theorem commonStageInner_conj_symm
    (i j : I) (x : E i) (y : E j) :
    star (commonStageInner E sys j i y x) =
      commonStageInner E sys i j x y := by
  let k := commonUpper i j
  rw [commonStageInner_eq_at E sys j i k
    (le_commonUpper_right i j) (le_commonUpper_left i j)]
  rw [commonStageInner_eq_at E sys i j k
    (le_commonUpper_left i j) (le_commonUpper_right i j)]
  exact inner_conj_symm (𝕜 := ℂ) _ _

end InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
