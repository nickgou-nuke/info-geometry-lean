/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
Authors: InfoGeometry Engine Contributors, Hampus Nyberg, Yaël Dillies
-/
module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.style.header.license
  "Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0." in
/-!
# Finite Gram quotients of a positive complex kernel

The scalar pre-inner-product construction adapts
`Mathlib.Analysis.InnerProductSpace.Reproducing` by Hampus Nyberg and Yaël Dillies
(Copyright (c) 2026 Hampus Nyberg, Apache 2.0).

The input is a Hermitian positive semidefinite complex kernel on arbitrary test labels.
The construction retains its full complex sesquilinear values. It constructs the Hilbert
space from the kernel, realizes each finite Gram quotient in that space, and constructs
the actual `Module.DirectLimit` of these finite stages. Its canonical map is injective
and dense, and its completion is linearly isometric to the kernel Hilbert space.

For Wilson-loop applications, the admissible labels, normalization, reflection operation,
convergence of cutoff kernels, and positivity of the limiting kernel are inputs. The finite
index here enumerates test labels; it is independent of the analytic cutoff index. The
transition maps use one fixed limiting kernel, so their form compatibility is exact.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder ComplexConjugate InnerProductSpace Topology
open UniformSpace

namespace CoreLean.PositiveKernel

universe u
variable {X : Type u} (K : Matrix X X ℂ)

/-- A type copy makes the seminorm depend on the chosen kernel. -/
def PreHilbert (_K : Matrix X X ℂ) : Type u := X →₀ ℂ

instance : AddCommGroup (PreHilbert K) := inferInstanceAs (AddCommGroup (X →₀ ℂ))
instance : Module ℂ (PreHilbert K) := inferInstanceAs (Module ℂ (X →₀ ℂ))

/-- Read and write coefficients without assigning the kernel norm to the untagged carrier. -/
def coefficients : PreHilbert K ≃ₗ[ℂ] (X →₀ ℂ) where
  toFun c := c
  invFun c := c
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The full complex Gram form, conjugate-linear in the first argument. -/
def gram (c d : X →₀ ℂ) : ℂ :=
  c.sum fun x a => d.sum fun y b => star a * K x y * b

variable [Fact K.PosSemidef]

instance : PreInnerProductSpace.Core ℂ (PreHilbert K) where
  inner c d := gram K (coefficients K c) (coefficients K d)
  conj_inner_symm c d := by
    change star (gram K (coefficients K d) (coefficients K c)) =
      gram K (coefficients K c) (coefficients K d)
    simp only [gram, star_finsuppSum, Pi.star_apply, star_mul, star_star]
    rw [Finsupp.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact (congrArg
      (fun z : ℂ => star (coefficients K c x) * (z * coefficients K d y))
      ((Fact.out : K.PosSemidef).isHermitian.apply x y)).trans (mul_assoc _ _ _).symm
  re_inner_nonneg c :=
    (Complex.nonneg_iff.mp ((Fact.out : K.PosSemidef).2 (coefficients K c))).1
  add_left c d e := by
    change gram K (coefficients K (c + d)) (coefficients K e) =
      gram K (coefficients K c) (coefficients K e) +
        gram K (coefficients K d) (coefficients K e)
    rw [map_add]
    simp only [gram]
    rw [Finsupp.sum_add_index'] <;>
      simp [← Finsupp.sum_add, add_mul, star_add]
  smul_left c d z := by
    change gram K (coefficients K (z • c)) (coefficients K d) =
      star z * gram K (coefficients K c) (coefficients K d)
    rw [map_smul]
    simp only [gram]
    rw [Finsupp.sum_smul_index] <;>
      simp [Finsupp.mul_sum, ← mul_assoc]

instance : SeminormedAddCommGroup (PreHilbert K) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (PreHilbert K) := .ofCore _

/-- Native separated completion of the Gram seminormed space. -/
abbrev Hilbert := Completion (PreHilbert K)

/-- The canonical map includes separation by zero Gram seminorm. -/
def preToHilbert : PreHilbert K →ₗ[ℂ] Hilbert K :=
  Completion.toComplₗᵢ.toLinearMap

/-- The vector represented by a test label. -/
def feature (x : X) : Hilbert K :=
  preToHilbert K ((coefficients K).symm (Finsupp.single x 1))

@[simp] theorem inner_preToHilbert (c d : PreHilbert K) :
    ⟪preToHilbert K c, preToHilbert K d⟫_ℂ =
      gram K (coefficients K c) (coefficients K d) := by
  exact Completion.inner_coe c d

@[simp] theorem inner_feature (x y : X) :
    ⟪feature K x, feature K y⟫_ℂ = K x y := by
  simp [feature, gram]

/-- A finite linear combination of kernel vectors, with ordinary complex coefficients. -/
def finiteEval (F : Finset X) : (F → ℂ) →ₗ[ℂ] Hilbert K :=
  Fintype.linearCombination ℂ (fun x : F => feature K x)

/-- Finite Gram form. No real-part projection is used in this definition. -/
def finiteGram (F : Finset X) (c d : F → ℂ) : ℂ :=
  ∑ x : F, ∑ y : F, star (c x) * K x y * d y

@[simp] theorem inner_finiteEval (F : Finset X) (c d : F → ℂ) :
    ⟪finiteEval K F c, finiteEval K F d⟫_ℂ = finiteGram K F c d := by
  change ⟪∑ x : F, c x • feature K x, ∑ y : F, d y • feature K y⟫_ℂ =
    ∑ x : F, ∑ y : F, star (c x) * K x y * d y
  rw [sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right, inner_feature, starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ac_rfl

/-- The radical of the finite Gram form is precisely the kernel of its realization. -/
theorem mem_ker_finiteEval_iff (F : Finset X) (c : F → ℂ) :
    c ∈ (finiteEval K F).ker ↔ finiteGram K F c c = 0 := by
  rw [LinearMap.mem_ker, ← inner_self_eq_zero (𝕜 := ℂ), inner_finiteEval]

/-- Zero norm is equivalent to being orthogonal to every finite coefficient vector. -/
theorem mem_ker_finiteEval_iff_radical (F : Finset X) (c : F → ℂ) :
    c ∈ (finiteEval K F).ker ↔ ∀ d, finiteGram K F c d = 0 := by
  constructor
  · intro hc d
    rw [← inner_finiteEval, LinearMap.mem_ker.mp hc, inner_zero_left]
  · intro hc
    exact (mem_ker_finiteEval_iff K F c).2 (hc c)

/-- A concrete realization of the finite Gram quotient, with its inherited inner product. -/
def stage (F : Finset X) : Submodule ℂ (Hilbert K) := (finiteEval K F).range

/-- The native algebraic quotient by the nullspace is exactly the concrete finite stage. -/
def quotientEquivStage (F : Finset X) :
    ((F → ℂ) ⧸ (finiteEval K F).ker) ≃ₗ[ℂ] stage K F :=
  (finiteEval K F).quotKerEquivRange

/-- An actual injective map from the nullspace quotient to the constructed Hilbert space. -/
def quotientEmbedding (F : Finset X) :
    ((F → ℂ) ⧸ (finiteEval K F).ker) →ₗ[ℂ] Hilbert K :=
  (stage K F).subtype.comp (quotientEquivStage K F).toLinearMap

theorem quotientEmbedding_injective (F : Finset X) :
    Function.Injective (quotientEmbedding K F) :=
  Subtype.val_injective.comp (quotientEquivStage K F).injective

@[simp] theorem quotientEmbedding_mk (F : Finset X) (c : F → ℂ) :
    quotientEmbedding K F (Submodule.Quotient.mk c) = finiteEval K F c := rfl

/-- Exact complex Gram readback on quotient representatives. -/
theorem inner_quotientEmbedding_mk (F : Finset X) (c d : F → ℂ) :
    ⟪quotientEmbedding K F (Submodule.Quotient.mk c),
      quotientEmbedding K F (Submodule.Quotient.mk d)⟫_ℂ = finiteGram K F c d := by
  simp

variable [DecidableEq X]

/-- Extend a coefficient family by zero along an inclusion of finite test families. -/
def zeroExtend {F G : Finset X} (h : F ⊆ G) : (F → ℂ) →ₗ[ℂ] (G → ℂ) :=
  Fintype.linearCombination ℂ (fun x : F => Pi.single (⟨x, h x.property⟩ : G) 1)

@[simp] theorem finiteEval_zeroExtend {F G : Finset X} (h : F ⊆ G) (c : F → ℂ) :
    finiteEval K G (zeroExtend h c) = finiteEval K F c := by
  change finiteEval K G (∑ x : F, c x • Pi.single (⟨x, h x.property⟩ : G) 1) =
    ∑ x : F, c x • feature K x
  rw [map_sum]
  simp only [map_smul, finiteEval, Fintype.linearCombination_apply_single, one_smul]

/-- The complete sesquilinear form is preserved by extension of the finite test family. -/
theorem finiteGram_zeroExtend {F G : Finset X} (h : F ⊆ G) (c d : F → ℂ) :
    finiteGram K G (zeroExtend h c) (zeroExtend h d) = finiteGram K F c d := by
  rw [← inner_finiteEval, finiteEval_zeroExtend, finiteEval_zeroExtend, inner_finiteEval]

omit [DecidableEq X] in
theorem stage_mono {F G : Finset X} (h : F ⊆ G) : stage K F ≤ stage K G := by
  classical
  rintro _ ⟨c, rfl⟩
  exact ⟨zeroExtend h c, finiteEval_zeroExtend K h c⟩

/-- The structure maps of the finite-family system are linear isometries. -/
def stageMap {F G : Finset X} (h : F ⊆ G) : stage K F →ₗᵢ[ℂ] stage K G where
  toLinearMap := Submodule.inclusion (stage_mono K h)
  norm_map' _ := rfl

omit [DecidableEq X] in
@[simp] theorem stageMap_self (F : Finset X) (v : stage K F) :
    stageMap K (Finset.Subset.refl F) v = v := rfl

omit [DecidableEq X] in
@[simp] theorem stageMap_comp {F G H : Finset X} (hFG : F ⊆ G) (hGH : G ⊆ H)
    (v : stage K F) : stageMap K hGH (stageMap K hFG v) =
      stageMap K (hFG.trans hGH) v := rfl

instance : DirectedSystem (fun F : Finset X => stage K F)
    (fun {_ _} h => stageMap K h) where
  map_self := by intro F v; rfl
  map_map := by intro H G F hFG hGH v; rfl

/-- The same structure map, on the native nullspace quotients. -/
def quotientMap {F G : Finset X} (h : F ⊆ G) :
    ((F → ℂ) ⧸ (finiteEval K F).ker) →ₗ[ℂ] ((G → ℂ) ⧸ (finiteEval K G).ker) :=
  (quotientEquivStage K G).symm.toLinearMap.comp
    ((stageMap K h).toLinearMap.comp (quotientEquivStage K F).toLinearMap)

omit [DecidableEq X] in
@[simp] theorem quotientEmbedding_quotientMap {F G : Finset X} (h : F ⊆ G)
    (v : (F → ℂ) ⧸ (finiteEval K F).ker) :
    quotientEmbedding K G (quotientMap K h v) = quotientEmbedding K F v := by
  change ((quotientEquivStage K G)
    ((quotientEquivStage K G).symm (stageMap K h (quotientEquivStage K F v))) : Hilbert K) =
      (quotientEquivStage K F v : Hilbert K)
  simp only [LinearEquiv.apply_symm_apply]
  rfl

theorem quotientMap_mk {F G : Finset X} (h : F ⊆ G) (c : F → ℂ) :
    quotientMap K h (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (zeroExtend h c) := by
  apply quotientEmbedding_injective K G
  simp

omit [DecidableEq X] in
theorem quotientMap_injective {F G : Finset X} (h : F ⊆ G) :
    Function.Injective (quotientMap K h) := by
  intro v w hvw
  apply quotientEmbedding_injective K F
  simpa using congrArg (quotientEmbedding K G) hvw

/-- An actual native algebraic direct limit, indexed by all finite test families. -/
abbrev Colimit := Module.DirectLimit (fun F : Finset X => stage K F)
  (fun _ _ h => (stageMap K h).toLinearMap)

/-- Canonical inclusion of a finite Gram quotient realization in the algebraic direct limit. -/
def stageToColimit (F : Finset X) : stage K F →ₗ[ℂ] Colimit K :=
  Module.DirectLimit.of ℂ (Finset X) (fun G : Finset X => stage K G)
    (fun _ _ h => (stageMap K h).toLinearMap) F

/-- The canonical map out of the actual algebraic direct limit. -/
def colimitToHilbert : Colimit K →ₗ[ℂ] Hilbert K :=
  Module.DirectLimit.lift ℂ (Finset X) (fun F : Finset X => stage K F)
    (fun _ _ h => (stageMap K h).toLinearMap) (fun F => (stage K F).subtype)
    (fun _ _ _ _ => rfl)

@[simp] theorem colimitToHilbert_stage (F : Finset X) (v : stage K F) :
    colimitToHilbert K (stageToColimit K F v) = v := by
  exact Module.DirectLimit.lift_of (R := ℂ) (ι := Finset X)
    (G := fun G : Finset X => stage K G)
    (f := fun _ _ h => (stageMap K h).toLinearMap)
    (fun G => (stage K G).subtype) (fun _ _ _ _ => rfl) v

theorem colimitToHilbert_injective : Function.Injective (colimitToHilbert K) := by
  exact Module.DirectLimit.lift_injective (fun F => (stage K F).subtype)
    (fun _ _ _ _ => rfl) (fun _ => Subtype.val_injective)

/-- The algebraic universal property: every compatible family has a unique linear extension. -/
theorem existsUnique_lift {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (f : ∀ F, stage K F →ₗ[ℂ] V)
    (hf : ∀ F G (h : F ⊆ G) v, f G (stageMap K h v) = f F v) :
    ∃! L : Colimit K →ₗ[ℂ] V, ∀ F v, L (stageToColimit K F v) = f F v := by
  refine ⟨Module.DirectLimit.lift ℂ (Finset X) (fun F : Finset X => stage K F)
    (fun _ _ h => (stageMap K h).toLinearMap) f hf, ?_, ?_⟩
  · intro F v
    simp only [stageToColimit, Module.DirectLimit.lift_of]
  · intro L hL
    apply Module.DirectLimit.hom_ext
    intro F
    ext v
    simpa only [LinearMap.comp_apply, stageToColimit, Module.DirectLimit.lift_of] using hL F v

theorem feature_mem_range_colimit (x : X) :
    feature K x ∈ (colimitToHilbert K).range := by
  let i : ({x} : Finset X) := ⟨x, Finset.mem_singleton_self x⟩
  have hx : feature K x ∈ stage K {x} := by
    refine ⟨Pi.single i 1, ?_⟩
    simp [finiteEval, i]
  exact ⟨stageToColimit K {x} ⟨feature K x, hx⟩, colimitToHilbert_stage K _ _⟩

theorem preToHilbert_mem_range_colimit (c : PreHilbert K) :
    preToHilbert K c ∈ (colimitToHilbert K).range := by
  let f := coefficients K c
  have hc : preToHilbert K c =
      f.sum (fun x a => preToHilbert K ((coefficients K).symm (Finsupp.single x a))) := by
    let L := (preToHilbert K).comp (coefficients K).symm.toLinearMap
    have hL := map_finsuppSum L f Finsupp.single
    simpa only [Finsupp.sum_single, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, L, f] using hL
  rw [hc]
  change (∑ x ∈ f.support, preToHilbert K ((coefficients K).symm (Finsupp.single x (f x)))) ∈
    (colimitToHilbert K).range
  exact Submodule.sum_mem _ fun x _ => by
    have hx := (colimitToHilbert K).range.smul_mem (f x) (feature_mem_range_colimit K x)
    simpa [feature, ← map_smul, Finsupp.smul_single, smul_eq_mul] using hx

/-- The directed finite-stage union is dense in the Hilbert space constructed from the kernel. -/
theorem denseRange_colimitToHilbert : DenseRange (colimitToHilbert K) := by
  apply Completion.denseRange_coe.mono
  rintro _ ⟨c, rfl⟩
  exact preToHilbert_mem_range_colimit K c

/-- Every algebraic colimit element belongs to one finite stage, and conversely. -/
theorem range_colimitToHilbert_eq_union :
    Set.range (colimitToHilbert K) = ⋃ F : Finset X, (stage K F : Set (Hilbert K)) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨F, x, rfl⟩ := Module.DirectLimit.exists_of w
    rw [show colimitToHilbert K
      (Module.DirectLimit.of ℂ (Finset X) _ _ F x) = x from by
        simpa only [stageToColimit] using colimitToHilbert_stage K F x]
    exact Set.mem_iUnion.2 ⟨F, x.property⟩
  · intro hv
    obtain ⟨F, hF⟩ := Set.mem_iUnion.1 hv
    exact ⟨stageToColimit K F ⟨v, hF⟩, colimitToHilbert_stage K F ⟨v, hF⟩⟩

omit [DecidableEq X] in
theorem dense_stageUnion : Dense (⋃ F : Finset X, (stage K F : Set (Hilbert K))) := by
  classical
  rw [← range_colimitToHilbert_eq_union]
  exact denseRange_colimitToHilbert K

/-- The canonical Hilbert-space map gives the algebraic direct limit its Gram norm. -/
instance : NormedAddCommGroup (Colimit K) :=
  NormedAddCommGroup.induced _ _ (colimitToHilbert K) (colimitToHilbert_injective K)

instance : InnerProductSpace ℂ (Colimit K) := InnerProductSpace.induced (colimitToHilbert K)

def colimitIsometry : Colimit K →ₗᵢ[ℂ] Hilbert K where
  toLinearMap := colimitToHilbert K
  norm_map' _ := rfl

/-- The native colimit inclusions preserve the Gram norm. -/
def stageToColimitIsometry (F : Finset X) : stage K F →ₗᵢ[ℂ] Colimit K where
  toLinearMap := stageToColimit K F
  norm_map' v := by
    change ‖colimitToHilbert K (stageToColimit K F v)‖ = ‖v‖
    exact congrArg norm (colimitToHilbert_stage K F v)

/-- The completion map is obtained from the native extension of a linear isometry. -/
def completionToHilbert : Completion (Colimit K) →ₗᵢ[ℂ] Hilbert K :=
  (colimitIsometry K).fromCompletion

theorem completionToHilbert_surjective : Function.Surjective (completionToHilbert K) := by
  intro v
  have hr : Set.range (colimitToHilbert K) ⊆ Set.range (completionToHilbert K) := by
    rintro _ ⟨c, rfl⟩
    exact ⟨(c : Completion (Colimit K)), LinearIsometry.fromCompletion_apply_coe _ c⟩
  exact closure_minimal hr (completionToHilbert K).isometry.isClosedEmbedding.isClosed_range
    (denseRange_colimitToHilbert K v)

/-- The kernel Hilbert space is the completion of the actual finite Gram quotient colimit. -/
def completionEquiv : Completion (Colimit K) ≃ₗᵢ[ℂ] Hilbert K :=
  LinearIsometryEquiv.ofSurjective (completionToHilbert K) (completionToHilbert_surjective K)

@[simp] theorem completionEquiv_stage (F : Finset X) (v : stage K F) :
    completionEquiv K (stageToColimit K F v : Completion (Colimit K)) = v := by
  change completionToHilbert K (stageToColimit K F v : Completion (Colimit K)) = v
  rw [completionToHilbert, LinearIsometry.fromCompletion_apply_coe]
  exact colimitToHilbert_stage K F v

end CoreLean.PositiveKernel
