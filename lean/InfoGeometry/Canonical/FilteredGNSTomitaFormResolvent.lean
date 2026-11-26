/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredGNSTomitaModularForm
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Infinite-Dimensional Closed-Graph Modular Form Resolvent `R = (1 + Δ)⁻¹` (`F1`)

On an arbitrary `[CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]` with
state `ω : State A` and closable Tomita core `hclos : IsClosableTomitaCore ω`,
this module bridges the closed Tomita operator `S = closedTomitaOperator ω hclos`
(`D(S) = closedTomitaDomain ω`) and Mathlib's Riesz–Hilbert adjoint machinery to
construct the bounded positive self-adjoint form resolvent `R := (1 + Δ)⁻¹`:

1. **`TomitaGraphSpace ω hclos`**:
   Equips `closedTomitaDomain ω` with the graph inner product
   `⟪x, y⟫_G := ⟪(x : GNS), (y : GNS)⟫_ℂ + ⟪S y, S x⟫_ℂ`, proving full
   `InnerProductSpace ℂ` and completeness `CompleteSpace (TomitaGraphSpace ω hclos)`
   directly from topological closedness of `closedTomitaCoreGraph ω` in `GNS × GNS`.
2. **Contractive Inclusion `graphIncl` and Resolvent `tomitaFormResolvent := ι ∘ ι*`**:
   Constructs `graphIncl : TomitaGraphSpace ω hclos →L[ℂ] ω.functional.GNS` with
   `‖graphIncl‖ ≤ 1`, and defines `tomitaFormResolvent := graphIncl ∘L graphIncl.adjoint`.
3. **Exact Resolvent Theorems (`0 ≤ R ≤ 1`, Weak Identity, Injectivity)**:
   - `tomitaFormResolvent_isSelfAdjoint`: `IsSelfAdjoint (tomitaFormResolvent ω hclos)`
   - `tomitaFormResolvent_inner_nonneg` & `tomitaFormResolvent_inner_le`: `0 ≤ (⟪x, R x⟫_ℂ).re ≤ ‖x‖^2`
   - `tomitaFormResolvent_weak_identity`: `⟪R x, y⟫_ℂ + ⟪S y, S (R x)⟫_ℂ = ⟪x, y⟫_ℂ`
   - `tomitaFormResolvent_injective`: `R x = 0 → x = 0` (via density of `toPreGNS` in GNS)
   - `tomitaBoundedPolarFactor x := S (graphIncl.adjoint x)` is anti-linear with
     `‖tomitaBoundedPolarFactor x‖^2 + ‖R x‖^2 = (⟪x, R x⟫_ℂ).re ≤ ‖x‖^2`.

Honest scope note: because `0 ∈ spectrum ℝ R` for unbounded `Δ`, constructing the
unbounded one-parameter unitary group `Δ^{it}` requires spectral-cutoff strong limits
on `ran(R)` (or Stone's theorem), and infinite-dimensional `J M J = M'` via van Daele (1974)
/ Rieffel–van Daele (1977) builds directly on `R` in the next layer.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaFormResolvent

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaCore
open CStarStateColimit.Native.FilteredGNSTomitaGraph
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open scoped InnerProductSpace

universe u

variable {A : Type u}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! =========================================================================
    1. Closed-Graph Hilbert Space D(S) with ⟪x, y⟫_G = ⟪x, y⟫ + ⟪S y, S x⟫
    ========================================================================= -/

/-- Wrapper around `closedTomitaDomain ω` carrying the graph inner-product Hilbert
space structure for `S = closedTomitaOperator ω hclos`. -/
structure TomitaGraphSpace (ω : State A) (hclos : IsClosableTomitaCore ω) : Type u where
  val : closedTomitaDomain ω

namespace TomitaGraphSpace

variable (ω : State A) (hclos : IsClosableTomitaCore ω)

@[ext]
theorem ext {x y : TomitaGraphSpace ω hclos} (h : x.val = y.val) : x = y := by
  cases x; cases y; congr

instance : Zero (TomitaGraphSpace ω hclos) := ⟨⟨0⟩⟩
instance : Add (TomitaGraphSpace ω hclos) := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance : Neg (TomitaGraphSpace ω hclos) := ⟨fun x => ⟨-x.val⟩⟩
instance : Sub (TomitaGraphSpace ω hclos) := ⟨fun x y => ⟨x.val - y.val⟩⟩

instance : AddCommGroup (TomitaGraphSpace ω hclos) where
  add x y := ⟨x.val + y.val⟩
  add_assoc x y z := by ext; exact add_assoc _ _ _
  zero := ⟨0⟩
  zero_add x := by ext; exact zero_add _
  add_zero x := by ext; exact add_zero _
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  neg x := ⟨-x.val⟩
  zsmul := zsmulRec
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl
  neg_add_cancel x := by ext; exact neg_add_cancel _
  add_comm x y := by ext; exact add_comm _ _
  sub x y := ⟨x.val - y.val⟩
  sub_eq_add_neg x y := by ext; exact sub_eq_add_neg _ _

@[simp] theorem coe_add (x y : TomitaGraphSpace ω hclos) :
    ((x + y).val : ω.functional.GNS) = (x.val : ω.functional.GNS) + (y.val : ω.functional.GNS) :=
  rfl

@[simp] theorem coe_sub (x y : TomitaGraphSpace ω hclos) :
    ((x - y).val : ω.functional.GNS) = (x.val : ω.functional.GNS) - (y.val : ω.functional.GNS) :=
  rfl

@[simp] theorem coe_zero : ((0 : TomitaGraphSpace ω hclos).val : ω.functional.GNS) = 0 :=
  rfl

instance : Module ℂ (TomitaGraphSpace ω hclos) where
  smul c x := ⟨c • x.val⟩
  one_smul x := by ext; exact one_smul _ _
  mul_smul c d x := by ext; exact mul_smul c d _
  smul_zero c := by ext; exact smul_zero c
  smul_add c x y := by ext; exact smul_add c _ _
  add_smul c d x := by ext; exact add_smul c d _
  zero_smul x := by ext; exact zero_smul _ _

@[simp] theorem coe_smul (c : ℂ) (x : TomitaGraphSpace ω hclos) :
    ((c • x).val : ω.functional.GNS) = c • (x.val : ω.functional.GNS) :=
  rfl

private lemma graph_inner_self_re_eq (x : TomitaGraphSpace ω hclos) :
    (inner ℂ (x.val : ω.functional.GNS) (x.val : ω.functional.GNS) +
      inner ℂ (closedTomitaOperator ω hclos x.val) (closedTomitaOperator ω hclos x.val)).re =
      ‖(x.val : ω.functional.GNS)‖ ^ 2 + ‖closedTomitaOperator ω hclos x.val‖ ^ 2 := by
  rw [Complex.add_re]
  congr 1
  · exact inner_self_eq_norm_sq (𝕜 := ℂ) (x.val : ω.functional.GNS)
  · exact inner_self_eq_norm_sq (𝕜 := ℂ) (closedTomitaOperator ω hclos x.val)

@[instance_reducible]
private def graphCore : InnerProductSpace.Core ℂ (TomitaGraphSpace ω hclos) where
  inner x y :=
    inner ℂ (x.val : ω.functional.GNS) (y.val : ω.functional.GNS) +
      inner ℂ (closedTomitaOperator ω hclos y.val) (closedTomitaOperator ω hclos x.val)
  conj_inner_symm x y := by
    rw [map_add, inner_conj_symm, inner_conj_symm, add_comm]
  re_inner_nonneg x := by
    simp only [RCLike.re_to_complex]
    rw [graph_inner_self_re_eq]
    positivity
  definite x hx := by
    have hre := congrArg Complex.re hx
    rw [Complex.zero_re, graph_inner_self_re_eq] at hre
    have h0 : ‖(x.val : ω.functional.GNS)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖(x.val : ω.functional.GNS)‖,
        sq_nonneg ‖closedTomitaOperator ω hclos x.val‖]
    have hnorm : ‖(x.val : ω.functional.GNS)‖ = 0 := sq_eq_zero_iff.mp h0
    have hval : (x.val : ω.functional.GNS) = 0 := norm_eq_zero.mp hnorm
    exact TomitaGraphSpace.ext ω hclos (Subtype.ext hval)
  add_left x y z := by
    change inner ℂ ((x.val : ω.functional.GNS) + (y.val : ω.functional.GNS)) (z.val : ω.functional.GNS) +
        inner ℂ (closedTomitaOperator ω hclos z.val)
          (closedTomitaOperator ω hclos (x.val + y.val)) =
      (inner ℂ (x.val : ω.functional.GNS) (z.val : ω.functional.GNS) +
        inner ℂ (closedTomitaOperator ω hclos z.val) (closedTomitaOperator ω hclos x.val)) +
      (inner ℂ (y.val : ω.functional.GNS) (z.val : ω.functional.GNS) +
        inner ℂ (closedTomitaOperator ω hclos z.val) (closedTomitaOperator ω hclos y.val))
    rw [map_add, inner_add_left, inner_add_right]
    ring
  smul_left x y c := by
    change inner ℂ (c • (x.val : ω.functional.GNS)) (y.val : ω.functional.GNS) +
        inner ℂ (closedTomitaOperator ω hclos y.val)
          (closedTomitaOperator ω hclos (c • x.val)) =
      starRingEnd ℂ c *
        (inner ℂ (x.val : ω.functional.GNS) (y.val : ω.functional.GNS) +
          inner ℂ (closedTomitaOperator ω hclos y.val)
            (closedTomitaOperator ω hclos x.val))
    rw [inner_smul_left, map_smulₛₗ, inner_smul_right]
    ring

instance : NormedAddCommGroup (TomitaGraphSpace ω hclos) :=
  (graphCore ω hclos).toNormedAddCommGroup

instance : InnerProductSpace ℂ (TomitaGraphSpace ω hclos) :=
  InnerProductSpace.ofCore (graphCore ω hclos).toCore

theorem inner_apply (x y : TomitaGraphSpace ω hclos) :
    ⟪x, y⟫_ℂ =
      inner ℂ (x.val : ω.functional.GNS) (y.val : ω.functional.GNS) +
        inner ℂ (closedTomitaOperator ω hclos y.val) (closedTomitaOperator ω hclos x.val) :=
  rfl

theorem norm_sq_eq (x : TomitaGraphSpace ω hclos) :
    ‖x‖ ^ 2 =
      ‖(x.val : ω.functional.GNS)‖ ^ 2 + ‖closedTomitaOperator ω hclos x.val‖ ^ 2 := by
  have h : Complex.re ⟪x, x⟫_ℂ = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [inner_apply, graph_inner_self_re_eq] at h
  exact h.symm

theorem norm_val_le (x : TomitaGraphSpace ω hclos) :
    ‖(x.val : ω.functional.GNS)‖ ≤ ‖x‖ := by
  have hsq : ‖(x.val : ω.functional.GNS)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eq]
    exact le_add_of_nonneg_right (sq_nonneg _)
  nlinarith [norm_nonneg (x.val : ω.functional.GNS), norm_nonneg x]

theorem norm_S_le (x : TomitaGraphSpace ω hclos) :
    ‖closedTomitaOperator ω hclos x.val‖ ≤ ‖x‖ := by
  have hsq : ‖closedTomitaOperator ω hclos x.val‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eq]
    exact le_add_of_nonneg_left (sq_nonneg _)
  nlinarith [norm_nonneg (closedTomitaOperator ω hclos x.val), norm_nonneg x]

/-- Completeness of `TomitaGraphSpace ω hclos` derived from the topological
closedness of `closedTomitaCoreGraph ω` inside `ω.functional.GNS × ω.functional.GNS`. -/
instance : CompleteSpace (TomitaGraphSpace ω hclos) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro f hf
  have hf1 : CauchySeq (fun n => ((f n).val : ω.functional.GNS)) := by
    rw [Metric.cauchySeq_iff] at hf ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hf ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    calc
      dist (((f m).val : ω.functional.GNS)) (((f n).val : ω.functional.GNS))
          = ‖(((f m - f n).val : ω.functional.GNS))‖ := by
        rw [dist_eq_norm, coe_sub]
      _ ≤ ‖f m - f n‖ := norm_val_le ω hclos (f m - f n)
      _ = dist (f m) (f n) := (dist_eq_norm _ _).symm
      _ < ε := hN m hm n hn
  have hf2 : CauchySeq (fun n => closedTomitaOperator ω hclos (f n).val) := by
    rw [Metric.cauchySeq_iff] at hf ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hf ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    calc
      dist (closedTomitaOperator ω hclos (f m).val) (closedTomitaOperator ω hclos (f n).val)
          = ‖closedTomitaOperator ω hclos (f m - f n).val‖ := by
        rw [dist_eq_norm]
        congr 1
        change _ = closedTomitaOperator ω hclos ((f m).val - (f n).val)
        rw [map_sub]
      _ ≤ ‖f m - f n‖ := norm_S_le ω hclos (f m - f n)
      _ = dist (f m) (f n) := (dist_eq_norm _ _).symm
      _ < ε := hN m hm n hn
  obtain ⟨ξ, hξ⟩ := cauchySeq_tendsto_of_complete hf1
  obtain ⟨η, hη⟩ := cauchySeq_tendsto_of_complete hf2
  have hmem : (ξ, η) ∈ closedTomitaCoreGraph ω := by
    refine isClosed_closedTomitaCoreGraph ω |>.mem_of_tendsto (hξ.prodMk_nhds hη) ?_
    exact Filter.Eventually.of_forall fun n =>
      closedTomitaValue_mem_graph ω (f n).val
  have hξ_dom : ξ ∈ closedTomitaDomain ω := ⟨η, hmem⟩
  have hS_eq : closedTomitaOperator ω hclos ⟨ξ, hξ_dom⟩ = η :=
    closedTomitaValue_eq_of_mem ω hclos ⟨ξ, hξ_dom⟩ η hmem
  refine ⟨⟨⟨ξ, hξ_dom⟩⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hξ hη
  obtain ⟨N₁, hN₁⟩ := hξ (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := hη (ε / 2) (half_pos hε)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 := hN₁ n (le_trans (le_max_left _ _) hn)
  have hn2 := hN₂ n (le_trans (le_max_right _ _) hn)
  have h1 : ‖((f n).val : ω.functional.GNS) - ξ‖ < ε / 2 := by
    simpa [dist_eq_norm] using hn1
  have h2 : ‖closedTomitaOperator ω hclos (f n).val - η‖ < ε / 2 := by
    simpa [dist_eq_norm] using hn2
  have hsq : ‖f n - ⟨⟨ξ, hξ_dom⟩⟩‖ ^ 2 < ε ^ 2 := by
    rw [norm_sq_eq]
    have ha : ‖((f n - ⟨⟨ξ, hξ_dom⟩⟩).val : ω.functional.GNS)‖ ^ 2 < (ε / 2) ^ 2 := by
      rw [coe_sub]
      nlinarith [norm_nonneg (((f n).val : ω.functional.GNS) - ξ)]
    have hb : ‖closedTomitaOperator ω hclos (f n - ⟨⟨ξ, hξ_dom⟩⟩).val‖ ^ 2 < (ε / 2) ^ 2 := by
      have heq : closedTomitaOperator ω hclos (f n - ⟨⟨ξ, hξ_dom⟩⟩).val =
          closedTomitaOperator ω hclos (f n).val - η := by
        change closedTomitaOperator ω hclos ((f n).val - ⟨ξ, hξ_dom⟩) = _
        rw [map_sub, hS_eq]
      rw [heq]
      nlinarith [norm_nonneg (closedTomitaOperator ω hclos (f n).val - η)]
    linarith [sq_pos_of_pos hε]
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (f n - ⟨⟨ξ, hξ_dom⟩⟩), hε]

/-! =========================================================================
    2. Contractive Inclusion ι : D(S)_G →L[ℂ] GNS and Form Resolvent R = ι ∘ ι*
    ========================================================================= -/

/-- Contractive continuous linear inclusion `ι : TomitaGraphSpace ω hclos →L[ℂ] ω.functional.GNS`. -/
def graphIncl : TomitaGraphSpace ω hclos →L[ℂ] ω.functional.GNS :=
  LinearMap.mkContinuous
    { toFun := fun x => (x.val : ω.functional.GNS)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1
    (fun x => by
      rw [one_mul]
      exact norm_val_le ω hclos x)

@[simp]
theorem graphIncl_apply (x : TomitaGraphSpace ω hclos) :
    graphIncl ω hclos x = (x.val : ω.functional.GNS) := rfl

theorem graphIncl_norm_le : ‖graphIncl ω hclos‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Bounded positive self-adjoint form resolvent `R = (1 + Δ)⁻¹ = ι ∘ ι*` on `ω.functional.GNS`. -/
def tomitaFormResolvent : ω.functional.GNS →L[ℂ] ω.functional.GNS :=
  (graphIncl ω hclos).comp (graphIncl ω hclos).adjoint

theorem tomitaFormResolvent_isSelfAdjoint :
    IsSelfAdjoint (tomitaFormResolvent ω hclos) := by
  change (tomitaFormResolvent ω hclos).adjoint = tomitaFormResolvent ω hclos
  unfold tomitaFormResolvent
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem tomitaFormResolvent_inner_eq (x : ω.functional.GNS) :
    inner ℂ x (tomitaFormResolvent ω hclos x) =
      inner ℂ ((graphIncl ω hclos).adjoint x) ((graphIncl ω hclos).adjoint x) := by
  unfold tomitaFormResolvent
  rw [ContinuousLinearMap.comp_apply]
  exact (ContinuousLinearMap.adjoint_inner_left (graphIncl ω hclos)
    ((graphIncl ω hclos).adjoint x) x).symm

theorem tomitaFormResolvent_inner_nonneg (x : ω.functional.GNS) :
    0 ≤ (inner ℂ x (tomitaFormResolvent ω hclos x)).re := by
  rw [tomitaFormResolvent_inner_eq]
  change 0 ≤ RCLike.re (inner ℂ ((graphIncl ω hclos).adjoint x) ((graphIncl ω hclos).adjoint x))
  exact inner_self_nonneg

theorem tomitaFormResolvent_inner_le (x : ω.functional.GNS) :
    (inner ℂ x (tomitaFormResolvent ω hclos x)).re ≤ ‖x‖ ^ 2 := by
  rw [tomitaFormResolvent_inner_eq]
  change RCLike.re (inner ℂ ((graphIncl ω hclos).adjoint x) ((graphIncl ω hclos).adjoint x)) ≤ ‖x‖ ^ 2
  rw [inner_self_eq_norm_sq]
  have hadj : ‖(graphIncl ω hclos).adjoint x‖ ≤ ‖(graphIncl ω hclos).adjoint‖ * ‖x‖ :=
    ContinuousLinearMap.le_opNorm _ x
  have hnorm : ‖(graphIncl ω hclos).adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact graphIncl_norm_le ω hclos
  have hle : ‖(graphIncl ω hclos).adjoint x‖ ≤ ‖x‖ := by
    calc
      ‖(graphIncl ω hclos).adjoint x‖ ≤ ‖(graphIncl ω hclos).adjoint‖ * ‖x‖ := hadj
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  nlinarith [norm_nonneg ((graphIncl ω hclos).adjoint x), norm_nonneg x]

/-- Weak resolvent identity:
`⟪R x, y⟫ + ⟪S y, S (R x)⟫ = ⟪x, y⟫` for all `x ∈ GNS` and `y ∈ D(S)`. -/
theorem tomitaFormResolvent_weak_identity (x : ω.functional.GNS)
    (y : closedTomitaDomain ω) :
    inner ℂ (tomitaFormResolvent ω hclos x) (y : ω.functional.GNS) +
      inner ℂ (closedTomitaOperator ω hclos y)
        (closedTomitaOperator ω hclos ((graphIncl ω hclos).adjoint x).val) =
      inner ℂ x (y : ω.functional.GNS) := by
  have hadj := ContinuousLinearMap.adjoint_inner_left (graphIncl ω hclos) ⟨y⟩ x
  change inner ℂ ((graphIncl ω hclos).adjoint x) (⟨y⟩ : TomitaGraphSpace ω hclos) =
    inner ℂ x (graphIncl ω hclos ⟨y⟩) at hadj
  rw [inner_apply] at hadj
  exact hadj

/-- Injectivity of `R = (1 + Δ)⁻¹`: `R x = 0 → x = 0`, proved via density of
`ω.functional.toPreGNS` in `ω.functional.GNS`. -/
theorem tomitaFormResolvent_injective (x : ω.functional.GNS)
    (hx : tomitaFormResolvent ω hclos x = 0) : x = 0 := by
  have hre : (inner ℂ x (tomitaFormResolvent ω hclos x)).re = 0 := by
    rw [hx, inner_zero_right, Complex.zero_re]
  rw [tomitaFormResolvent_inner_eq] at hre
  change RCLike.re (inner ℂ ((graphIncl ω hclos).adjoint x) ((graphIncl ω hclos).adjoint x)) = 0
    at hre
  rw [inner_self_eq_norm_sq] at hre
  have hadj : (graphIncl ω hclos).adjoint x = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hre)
  have horth_core : ∀ a : ω.functional.PreGNS,
      inner ℂ x (a : ω.functional.GNS) = 0 := by
    intro a
    let y : closedTomitaDomain ω := ⟨(a : ω.functional.GNS), ⟨(tomitaCore ω a : ω.functional.GNS),
      subset_closure ⟨a, rfl⟩⟩⟩
    have hw := tomitaFormResolvent_weak_identity ω hclos x y
    have hzeroS :
        closedTomitaOperator ω hclos ((graphIncl ω hclos).adjoint x).val = 0 := by
      rw [hadj]
      exact map_zero _
    rw [hx, hzeroS, inner_zero_left, inner_zero_right, zero_add] at hw
    exact hw.symm
  have hdense : DenseRange (fun a : ω.functional.PreGNS => (a : ω.functional.GNS)) :=
    UniformSpace.Completion.denseRange_coe
  have hzero_fun : Continuous (fun z : ω.functional.GNS => inner ℂ x z) :=
    continuous_const.inner continuous_id
  have hfun : (fun z : ω.functional.GNS => inner ℂ x z) = fun _ => (0 : ℂ) :=
    hdense.equalizer hzero_fun continuous_const (funext horth_core)
  exact inner_self_eq_zero.mp (congrFun hfun x)

/-- Bounded anti-linear polar companion `T x := S ((graphIncl).adjoint x)` satisfying
`‖T x‖^2 + ‖R x‖^2 = (⟪x, R x⟫).re ≤ ‖x‖^2`. -/
def tomitaBoundedPolarFactor (x : ω.functional.GNS) : ω.functional.GNS :=
  closedTomitaOperator ω hclos ((graphIncl ω hclos).adjoint x).val

theorem tomitaBoundedPolarFactor_add (x y : ω.functional.GNS) :
    tomitaBoundedPolarFactor ω hclos (x + y) =
      tomitaBoundedPolarFactor ω hclos x + tomitaBoundedPolarFactor ω hclos y := by
  unfold tomitaBoundedPolarFactor
  rw [map_add]
  change closedTomitaOperator ω hclos
    (((graphIncl ω hclos).adjoint x).val + ((graphIncl ω hclos).adjoint y).val) = _
  rw [map_add]

theorem tomitaBoundedPolarFactor_smul (c : ℂ) (x : ω.functional.GNS) :
    tomitaBoundedPolarFactor ω hclos (c • x) =
      star c • tomitaBoundedPolarFactor ω hclos x := by
  unfold tomitaBoundedPolarFactor
  rw [map_smul]
  change closedTomitaOperator ω hclos (c • ((graphIncl ω hclos).adjoint x).val) = _
  rw [map_smulₛₗ, starRingEnd_apply]

theorem tomitaBoundedPolarFactor_norm_sq_add_resolvent (x : ω.functional.GNS) :
    ‖tomitaBoundedPolarFactor ω hclos x‖ ^ 2 + ‖tomitaFormResolvent ω hclos x‖ ^ 2 =
      (inner ℂ x (tomitaFormResolvent ω hclos x)).re := by
  rw [tomitaFormResolvent_inner_eq]
  symm
  change RCLike.re (inner ℂ ((graphIncl ω hclos).adjoint x) ((graphIncl ω hclos).adjoint x)) = _
  rw [inner_self_eq_norm_sq, norm_sq_eq, add_comm]
  rfl

end TomitaGraphSpace

end CStarStateColimit.Native.FilteredGNSTomitaFormResolvent
