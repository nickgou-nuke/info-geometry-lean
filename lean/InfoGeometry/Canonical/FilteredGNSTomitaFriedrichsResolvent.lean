/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredGNSTomitaClosedOperator
import InfoGeometry.Canonical.FilteredGNSTomitaModularForm
import InfoGeometry.Canonical.FilteredGNSTomitaModularHilbertCompletion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Filtered GNS Tomita Friedrichs Resolvent `R = (1 + Δ)⁻¹` (`TT-F1B`)

For any C⋆-algebra `A` with state `ω : State A` and closable Tomita core
`hclos : IsClosableTomitaCore ω`, this module constructs the closed-graph
Hilbert space `TomitaGraphDom ω hclos`, the Friedrichs form resolvent
`R = (1 + Δ)⁻¹` via Mathlib's Riesz representation (`InnerProductSpace.toDual`),
and the filtered stage compatibility bridges to `closedTomitaModularForm` and
`ModularHilbertCompletion`.

## Main Components

0. **Graph Hilbert Space & Friedrichs Resolvent**:
   - `TomitaGraphDom ω hclos`: equips `closedTomitaDomain ω` with the graph inner
     product `⟪x, y⟫_G = ⟪x.val, y.val⟫_ℂ + ⟪S y.val, S x.val⟫_ℂ` and
     derives `CompleteSpace` from `isClosed_closedTomitaCoreGraph ω`.
   - `graphDomInclCLM ω hclos : TomitaGraphDom ω hclos →L[ℂ] ω.functional.GNS`.
   - `gnsToGraphDual` and `tomitaFormResolventDomCLM` via
     `(InnerProductSpace.toDual ℂ (TomitaGraphDom ω hclos)).symm`, proved equal
     to `(graphDomInclCLM ω hclos).adjoint`.
   - `tomitaFormResolventCLM := (graphDomInclCLM ω hclos).comp (tomitaFormResolventDomCLM ω hclos)`
     with variational identity, energy identity, self-adjointness, `0 ≤ R ≤ 1`,
     and injectivity.
1. **Range & Density**: `Set.range R ⊆ closedTomitaDomain ω`, `DenseRange R`, and
   `Dense (closedTomitaDomain ω : Set ω.functional.GNS)`.
2. **Antilinear `S ∘ R` & Complementary Resolvent `1 - R`**:
   - `tomitaSCompResolventRLM : ω.functional.GNS →L[ℝ] ω.functional.GNS` (`‖S(R_dom ξ)‖ ≤ ‖ξ‖`).
   - `tomitaFormComplementaryResolventCLM := 1 - R` (`IsSelfAdjoint`, `[0, 1]` bounds,
     contraction `‖(1 - R) ξ‖ ≤ ‖ξ‖`).
3. **Bridge to `closedTomitaModularForm`**:
   - `tomitaGraphInner_eq_inner_add_modularForm`
   - `tomitaFormResolvent_modularForm_variational`
4. **Contractions to `ModularHilbertCompletion`**:
   - `tomitaGraphDom_to_modularHilbertCompletion` (`‖·‖ ≤ 1`, exact `‖f x‖^2 = (q_i(x, x)).re`)
   - `gns_to_modularHilbertCompletion_via_resolvent` (`‖·‖ ≤ 1`)
5. **Filtered Stage Transition Compatibility (`i ≤ j`)**:
   - `filteredTomitaGraphDomMap : TomitaGraphDom (ω.state i) (hclos i) →ₗᵢ[ℂ] TomitaGraphDom (ω.state j) (hclos j)`
   - Variational compatibility, orthogonal projection characterization, quadratic-form
     monotonicity `R_i ≤ U^* R_j U`, and `ModularHilbertCompletion` compatibility.

## Separation & Scope Note

This module (`TT-F1B`) belongs strictly to the closed-graph / quadratic-form
Friedrichs resolvent route on `FilteredGNSTomitaClosedOperator`,
`FilteredGNSTomitaModularForm`, and `FilteredGNSTomitaModularHilbertCompletion`,
and is kept strictly distinct from the Rieffel–van Daele bounded real-subspace
projection route (`TT-F1A`).
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaFriedrichsResolvent

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTomitaCore
open CStarStateColimit.Native.FilteredGNSTomitaGraph
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaClosedTransport
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
open CStarStateColimit.Native.FilteredGNSTomitaModularFormColimit
open CStarStateColimit.Native.FilteredGNSTomitaComplexColimit
open CStarStateColimit.Native.FilteredGNSTomitaModularQuotient
open CStarStateColimit.Native.FilteredGNSTomitaModularHilbertCompletion
open scoped InnerProductSpace

universe u

/-! =========================================================================
    0. Graph Hilbert Space & Riesz Friedrichs Resolvent
    ========================================================================= -/

section SingleStage

variable {A : Type u}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Wrapper around `closedTomitaDomain ω` carrying the graph Hilbert space structure
associated to the closed Tomita operator `S = closedTomitaOperator ω hclos`. -/
structure TomitaGraphDom (ω : State A) (hclos : IsClosableTomitaCore ω) : Type u where
  val : closedTomitaDomain ω

namespace TomitaGraphDom

variable (ω : State A) (hclos : IsClosableTomitaCore ω)

instance : Inhabited (TomitaGraphDom ω hclos) :=
  ⟨⟨0⟩⟩

@[ext]
theorem ext {x y : TomitaGraphDom ω hclos} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  exact congrArg TomitaGraphDom.mk h

instance : AddCommGroup (TomitaGraphDom ω hclos) where
  add x y := ⟨x.val + y.val⟩
  add_assoc x y z := by ext; exact add_assoc _ _ _
  zero := ⟨0⟩
  zero_add x := by ext; exact zero_add _
  add_zero x := by ext; exact add_zero _
  nsmul n x := ⟨n • x.val⟩
  nsmul_zero x := by ext; exact zero_nsmul _
  nsmul_succ n x := by ext; exact succ_nsmul _ _
  neg x := ⟨-x.val⟩
  zsmul n x := ⟨n • x.val⟩
  zsmul_zero' x := by ext; exact zero_zsmul _
  zsmul_succ' n x := by
    apply TomitaGraphDom.ext
    change ((n.succ : ℕ) : ℤ) • x.val = (n : ℤ) • x.val + x.val
    rw [Nat.cast_succ, add_zsmul, one_zsmul]
  zsmul_neg' n x := by
    apply TomitaGraphDom.ext
    change Int.negSucc n • x.val = -(((n.succ : ℕ) : ℤ) • x.val)
    rw [Int.negSucc_eq, neg_smul, Nat.cast_succ]
  neg_add_cancel x := by ext; exact neg_add_cancel _
  add_comm x y := by ext; exact add_comm _ _
  sub x y := ⟨x.val - y.val⟩
  sub_eq_add_neg x y := by ext; exact sub_eq_add_neg _ _

instance : Module ℂ (TomitaGraphDom ω hclos) where
  smul c x := ⟨c • x.val⟩
  one_smul x := by ext; exact one_smul _ _
  mul_smul c d x := by ext; exact mul_smul c d _
  smul_zero c := by ext; exact smul_zero c
  smul_add c x y := by ext; exact smul_add c _ _
  add_smul c d x := by ext; exact add_smul c d _
  zero_smul x := by ext; exact zero_smul _ _

private lemma graph_inner_self_re_eq (x : TomitaGraphDom ω hclos) :
    (inner ℂ (x.val : ω.functional.GNS) (x.val : ω.functional.GNS) +
      inner ℂ (closedTomitaOperator ω hclos x.val) (closedTomitaOperator ω hclos x.val)).re =
      ‖(x.val : ω.functional.GNS)‖ ^ 2 + ‖closedTomitaOperator ω hclos x.val‖ ^ 2 := by
  rw [Complex.add_re, ← RCLike.re_to_complex, ← RCLike.re_to_complex,
    ← InnerProductSpace.norm_sq_eq_re_inner, ← InnerProductSpace.norm_sq_eq_re_inner]

/-- Complex inner-product core `⟪x, y⟫_G = ⟪x.val, y.val⟫ + ⟪S y.val, S x.val⟫` on
`TomitaGraphDom ω hclos`. -/
@[instance_reducible]
def graphInnerCore : InnerProductSpace.Core ℂ (TomitaGraphDom ω hclos) where
  inner x y :=
    inner ℂ (x.val : ω.functional.GNS) (y.val : ω.functional.GNS) +
      inner ℂ (closedTomitaOperator ω hclos y.val) (closedTomitaOperator ω hclos x.val)
  conj_inner_symm x y := by
    rw [map_add, inner_conj_symm, inner_conj_symm, add_comm]
  re_inner_nonneg x := by
    rw [RCLike.re_to_complex, graph_inner_self_re_eq]
    positivity
  definite x hx := by
    have hre := congrArg Complex.re hx
    rw [Complex.zero_re, graph_inner_self_re_eq] at hre
    have h0 : ‖(x.val : ω.functional.GNS)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖(x.val : ω.functional.GNS)‖,
        sq_nonneg ‖closedTomitaOperator ω hclos x.val‖]
    have hnorm : ‖(x.val : ω.functional.GNS)‖ = 0 := sq_eq_zero_iff.mp h0
    have hval : (x.val : ω.functional.GNS) = 0 := norm_eq_zero.mp hnorm
    exact TomitaGraphDom.ext ω hclos (Subtype.ext hval)
  add_left x y z := by
    change inner ℂ ((x.val : ω.functional.GNS) + (y.val : ω.functional.GNS))
          (z.val : ω.functional.GNS) +
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
    rw [inner_smul_left, map_smulₛₗ, inner_smul_right, starRingEnd_apply]
    ring

instance : NormedAddCommGroup (TomitaGraphDom ω hclos) :=
  (graphInnerCore ω hclos).toNormedAddCommGroup

instance : InnerProductSpace ℂ (TomitaGraphDom ω hclos) :=
  InnerProductSpace.ofCore (graphInnerCore ω hclos).toCore

theorem inner_apply (x y : TomitaGraphDom ω hclos) :
    ⟪x, y⟫_ℂ =
      inner ℂ (x.val : ω.functional.GNS) (y.val : ω.functional.GNS) +
        inner ℂ (closedTomitaOperator ω hclos y.val) (closedTomitaOperator ω hclos x.val) :=
  rfl

theorem norm_sq_eq (x : TomitaGraphDom ω hclos) :
    ‖x‖ ^ 2 =
      ‖(x.val : ω.functional.GNS)‖ ^ 2 + ‖closedTomitaOperator ω hclos x.val‖ ^ 2 := by
  have h : ‖x‖ ^ 2 = (⟪x, x⟫_ℂ).re := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x, RCLike.re_to_complex]
  rw [h, inner_apply, graph_inner_self_re_eq]

theorem norm_val_le (x : TomitaGraphDom ω hclos) :
    ‖(x.val : ω.functional.GNS)‖ ≤ ‖x‖ := by
  have hsq : ‖(x.val : ω.functional.GNS)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eq]
    exact le_add_of_nonneg_right (sq_nonneg _)
  nlinarith [norm_nonneg (x.val : ω.functional.GNS), norm_nonneg x]

theorem norm_S_le (x : TomitaGraphDom ω hclos) :
    ‖closedTomitaOperator ω hclos x.val‖ ≤ ‖x‖ := by
  have hsq : ‖closedTomitaOperator ω hclos x.val‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eq]
    exact le_add_of_nonneg_left (sq_nonneg _)
  nlinarith [norm_nonneg (closedTomitaOperator ω hclos x.val), norm_nonneg x]

/-- Underlying `ℂ`-linear projection `x ↦ x.val` from `TomitaGraphDom ω hclos` to
`closedTomitaDomain ω`. -/
def valLM : TomitaGraphDom ω hclos →ₗ[ℂ] closedTomitaDomain ω where
  toFun x := x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Completeness of `TomitaGraphDom ω hclos` derived from the topological closedness of
`closedTomitaCoreGraph ω` in `ω.functional.GNS × ω.functional.GNS`. -/
instance : CompleteSpace (TomitaGraphDom ω hclos) := by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  have hf1 : CauchySeq (fun n => ((f n).val : ω.functional.GNS)) := by
    rw [Metric.cauchySeq_iff] at hf ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hf ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    calc
      dist ((f m).val : ω.functional.GNS) ((f n).val : ω.functional.GNS)
          = ‖((f m - f n).val : ω.functional.GNS)‖ := by
        rw [dist_eq_norm]; rfl
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
    refine (isClosed_closedTomitaCoreGraph ω).mem_of_tendsto (hξ.prodMk_nhds hη) ?_
    exact Filter.Eventually.of_forall fun n => closedTomitaValue_mem_graph ω (f n).val
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
      have heq : ((f n - ⟨⟨ξ, hξ_dom⟩⟩).val : ω.functional.GNS) =
          ((f n).val : ω.functional.GNS) - ξ := rfl
      rw [heq]
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

end TomitaGraphDom

variable (ω : State A) (hclos : IsClosableTomitaCore ω)

/-- Contractive continuous linear inclusion `TomitaGraphDom ω hclos →L[ℂ] ω.functional.GNS`. -/
def graphDomInclCLM : TomitaGraphDom ω hclos →L[ℂ] ω.functional.GNS :=
  LinearMap.mkContinuous
    { toFun := fun x => (x.val : ω.functional.GNS)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1
    (fun x => by
      rw [one_mul]
      exact TomitaGraphDom.norm_val_le ω hclos x)

@[simp]
theorem graphDomInclCLM_apply (x : TomitaGraphDom ω hclos) :
    graphDomInclCLM ω hclos x = (x.val : ω.functional.GNS) := rfl

theorem graphDomInclCLM_norm_le : ‖graphDomInclCLM ω hclos‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Conjugate-linear bounded functional `y ↦ ⟪ξ, y.val⟫_ℂ` on `TomitaGraphDom ω hclos`
associated to `ξ : ω.functional.GNS`. -/
def gnsToGraphDual (ξ : ω.functional.GNS) :
    StrongDual ℂ (TomitaGraphDom ω hclos) :=
  (InnerProductSpace.toDualMap ℂ ω.functional.GNS ξ).comp (graphDomInclCLM ω hclos)

@[simp]
theorem gnsToGraphDual_apply (ξ : ω.functional.GNS) (y : TomitaGraphDom ω hclos) :
    gnsToGraphDual ω hclos ξ y = inner ℂ ξ (y.val : ω.functional.GNS) := rfl

theorem gnsToGraphDual_add (ξ η : ω.functional.GNS) :
    gnsToGraphDual ω hclos (ξ + η) =
      gnsToGraphDual ω hclos ξ + gnsToGraphDual ω hclos η := by
  ext y
  simp [inner_add_left]

theorem gnsToGraphDual_smul (c : ℂ) (ξ : ω.functional.GNS) :
    gnsToGraphDual ω hclos (c • ξ) = star c • gnsToGraphDual ω hclos ξ := by
  ext y
  simp [inner_smul_left]

theorem gnsToGraphDual_norm_le (ξ : ω.functional.GNS) :
    ‖gnsToGraphDual ω hclos ξ‖ ≤ ‖ξ‖ := by
  calc
    ‖(InnerProductSpace.toDualMap ℂ ω.functional.GNS ξ).comp (graphDomInclCLM ω hclos)‖
        ≤ ‖InnerProductSpace.toDualMap ℂ ω.functional.GNS ξ‖ * ‖graphDomInclCLM ω hclos‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖ξ‖ * ‖graphDomInclCLM ω hclos‖ := by
      rw [LinearIsometry.norm_map]
    _ ≤ ‖ξ‖ * 1 := mul_le_mul_of_nonneg_left (graphDomInclCLM_norm_le ω hclos) (norm_nonneg ξ)
    _ = ‖ξ‖ := mul_one _

/-- Riesz-representation domain-valued Friedrichs resolvent
`tomitaFormResolventDomCLM : ω.functional.GNS →L[ℂ] TomitaGraphDom ω hclos`, constructed
explicitly via `(InnerProductSpace.toDual ℂ (TomitaGraphDom ω hclos)).symm`. -/
def tomitaFormResolventDomCLM :
    ω.functional.GNS →L[ℂ] TomitaGraphDom ω hclos :=
  LinearMap.mkContinuous
    { toFun := fun ξ =>
        (InnerProductSpace.toDual ℂ (TomitaGraphDom ω hclos)).symm
          (gnsToGraphDual ω hclos ξ)
      map_add' := fun ξ η => by
        rw [gnsToGraphDual_add, map_add]
      map_smul' := fun c ξ => by
        rw [gnsToGraphDual_smul, map_smulₛₗ]
        simp }
    1
    (fun ξ => by
      change ‖(InnerProductSpace.toDual ℂ (TomitaGraphDom ω hclos)).symm
        (gnsToGraphDual ω hclos ξ)‖ ≤ 1 * ‖ξ‖
      rw [one_mul, LinearIsometryEquiv.norm_map]
      exact gnsToGraphDual_norm_le ω hclos ξ)

@[simp]
theorem tomitaFormResolventDomCLM_apply (ξ : ω.functional.GNS) :
    tomitaFormResolventDomCLM ω hclos ξ =
      (InnerProductSpace.toDual ℂ (TomitaGraphDom ω hclos)).symm
        (gnsToGraphDual ω hclos ξ) := rfl

theorem tomitaFormResolventDomCLM_norm_le :
    ‖tomitaFormResolventDomCLM ω hclos‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem tomitaFormResolventDomCLM_apply_norm_le (ξ : ω.functional.GNS) :
    ‖tomitaFormResolventDomCLM ω hclos ξ‖ ≤ ‖ξ‖ := by
  calc
    ‖tomitaFormResolventDomCLM ω hclos ξ‖
        ≤ ‖tomitaFormResolventDomCLM ω hclos‖ * ‖ξ‖ := ContinuousLinearMap.le_opNorm _ ξ
    _ ≤ 1 * ‖ξ‖ := mul_le_mul_of_nonneg_right (tomitaFormResolventDomCLM_norm_le ω hclos)
      (norm_nonneg ξ)
    _ = ‖ξ‖ := one_mul _

theorem tomitaFormResolventDomCLM_inner_left (ξ : ω.functional.GNS)
    (y : TomitaGraphDom ω hclos) :
    inner ℂ (tomitaFormResolventDomCLM ω hclos ξ) y =
      inner ℂ ξ (y.val : ω.functional.GNS) := by
  rw [tomitaFormResolventDomCLM_apply, InnerProductSpace.toDual_symm_apply]
  rfl

theorem tomitaFormResolventDomCLM_inner_right (y : TomitaGraphDom ω hclos)
    (ξ : ω.functional.GNS) :
    inner ℂ y (tomitaFormResolventDomCLM ω hclos ξ) =
      inner ℂ (y.val : ω.functional.GNS) ξ := by
  rw [← inner_conj_symm, tomitaFormResolventDomCLM_inner_left, inner_conj_symm]

theorem tomitaFormResolventDomCLM_eq_adjoint :
    tomitaFormResolventDomCLM ω hclos = (graphDomInclCLM ω hclos).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro ξ y
  exact tomitaFormResolventDomCLM_inner_left ω hclos ξ y

/-- Bounded positive self-adjoint Friedrichs form resolvent `R = (1 + Δ)⁻¹` on
`ω.functional.GNS`. -/
def tomitaFormResolventCLM : ω.functional.GNS →L[ℂ] ω.functional.GNS :=
  (graphDomInclCLM ω hclos).comp (tomitaFormResolventDomCLM ω hclos)

@[simp]
theorem tomitaFormResolventCLM_apply (ξ : ω.functional.GNS) :
    tomitaFormResolventCLM ω hclos ξ = ((tomitaFormResolventDomCLM ω hclos ξ).val : ω.functional.GNS) :=
  rfl

/-- Variational characterization of the Friedrichs resolvent `R = (1 + Δ)⁻¹`:
`⟪R ξ, y.val⟫ + ⟪S y.val, S (R_dom ξ).val⟫ = ⟪ξ, y.val⟫`. -/
theorem tomitaFormResolvent_variational (ξ : ω.functional.GNS)
    (y : TomitaGraphDom ω hclos) :
    inner ℂ (tomitaFormResolventCLM ω hclos ξ) (y.val : ω.functional.GNS) +
      inner ℂ (closedTomitaOperator ω hclos y.val)
        (closedTomitaOperator ω hclos (tomitaFormResolventDomCLM ω hclos ξ).val) =
      inner ℂ ξ (y.val : ω.functional.GNS) := by
  rw [tomitaFormResolventCLM_apply, ← TomitaGraphDom.inner_apply,
    tomitaFormResolventDomCLM_inner_left]

/-- Exact energy identity: `‖R ξ‖^2 + ‖S (R_dom ξ).val‖^2 = (⟪ξ, R ξ⟫).re`. -/
theorem tomitaFormResolvent_energy (ξ : ω.functional.GNS) :
    ‖tomitaFormResolventCLM ω hclos ξ‖ ^ 2 +
      ‖closedTomitaOperator ω hclos (tomitaFormResolventDomCLM ω hclos ξ).val‖ ^ 2 =
      (inner ℂ ξ (tomitaFormResolventCLM ω hclos ξ)).re := by
  have hv := congrArg Complex.re
    (tomitaFormResolvent_variational ω hclos ξ (tomitaFormResolventDomCLM ω hclos ξ))
  rw [Complex.add_re, ← tomitaFormResolventCLM_apply, ← RCLike.re_to_complex,
    ← RCLike.re_to_complex, ← InnerProductSpace.norm_sq_eq_re_inner,
    ← InnerProductSpace.norm_sq_eq_re_inner] at hv
  exact hv

theorem tomitaFormResolvent_norm_le (ξ : ω.functional.GNS) :
    ‖tomitaFormResolventCLM ω hclos ξ‖ ≤ ‖ξ‖ :=
  le_trans (TomitaGraphDom.norm_val_le ω hclos _)
    (tomitaFormResolventDomCLM_apply_norm_le ω hclos ξ)

theorem tomitaFormResolvent_opNorm_le :
    ‖tomitaFormResolventCLM ω hclos‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by
    rw [one_mul]
    exact tomitaFormResolvent_norm_le ω hclos ξ

theorem tomitaFormResolvent_S_norm_le (ξ : ω.functional.GNS) :
    ‖closedTomitaOperator ω hclos (tomitaFormResolventDomCLM ω hclos ξ).val‖ ≤ ‖ξ‖ :=
  le_trans (TomitaGraphDom.norm_S_le ω hclos _)
    (tomitaFormResolventDomCLM_apply_norm_le ω hclos ξ)

theorem tomitaFormResolvent_inner_symm (ξ η : ω.functional.GNS) :
    inner ℂ (tomitaFormResolventCLM ω hclos ξ) η =
      inner ℂ ξ (tomitaFormResolventCLM ω hclos η) := by
  calc
    inner ℂ (tomitaFormResolventCLM ω hclos ξ) η
        = inner ℂ (tomitaFormResolventDomCLM ω hclos ξ) (tomitaFormResolventDomCLM ω hclos η) :=
      (tomitaFormResolventDomCLM_inner_right ω hclos (tomitaFormResolventDomCLM ω hclos ξ) η).symm
    _ = inner ℂ ξ (tomitaFormResolventCLM ω hclos η) :=
      tomitaFormResolventDomCLM_inner_left ω hclos ξ (tomitaFormResolventDomCLM ω hclos η)

theorem tomitaFormResolvent_isSelfAdjoint :
    IsSelfAdjoint (tomitaFormResolventCLM ω hclos) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro ξ η
  exact tomitaFormResolvent_inner_symm ω hclos ξ η

theorem tomitaFormResolvent_pos_le_one (ξ : ω.functional.GNS) :
    0 ≤ (inner ℂ ξ (tomitaFormResolventCLM ω hclos ξ)).re ∧
      (inner ℂ ξ (tomitaFormResolventCLM ω hclos ξ)).re ≤ ‖ξ‖ ^ 2 := by
  have he := tomitaFormResolvent_energy ω hclos ξ
  have hnorm : ‖tomitaFormResolventDomCLM ω hclos ξ‖ ^ 2 =
      (inner ℂ ξ (tomitaFormResolventCLM ω hclos ξ)).re := by
    rw [← he, TomitaGraphDom.norm_sq_eq]
    rfl
  have hdom : ‖tomitaFormResolventDomCLM ω hclos ξ‖ ≤ ‖ξ‖ :=
    tomitaFormResolventDomCLM_apply_norm_le ω hclos ξ
  constructor
  · rw [← he]
    positivity
  · rw [← hnorm]
    nlinarith [norm_nonneg (tomitaFormResolventDomCLM ω hclos ξ), norm_nonneg ξ]

theorem tomitaFormResolvent_eq_zero (ξ : ω.functional.GNS)
    (hξ : tomitaFormResolventCLM ω hclos ξ = 0) : ξ = 0 := by
  have hdom_sq : ‖tomitaFormResolventDomCLM ω hclos ξ‖ ^ 2 = 0 := by
    have he := tomitaFormResolvent_energy ω hclos ξ
    rw [hξ, inner_zero_right, Complex.zero_re, norm_zero, sq, mul_zero, zero_add] at he
    have hval : ((tomitaFormResolventDomCLM ω hclos ξ).val : ω.functional.GNS) = 0 := by
      simpa [tomitaFormResolventCLM_apply] using hξ
    rw [TomitaGraphDom.norm_sq_eq, hval, norm_zero, sq, mul_zero, zero_add, he]
  have hdom : tomitaFormResolventDomCLM ω hclos ξ = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hdom_sq)
  have horth_core : ∀ a : ω.functional.PreGNS,
      inner ℂ ξ (a : ω.functional.GNS) = 0 := by
    intro a
    let y : TomitaGraphDom ω hclos :=
      ⟨⟨(a : ω.functional.GNS), ⟨(tomitaCore ω a : ω.functional.GNS),
        subset_closure ⟨a, rfl⟩⟩⟩⟩
    have hv := tomitaFormResolvent_variational ω hclos ξ y
    rw [hξ, hdom] at hv
    change inner ℂ (0 : ω.functional.GNS) (a : ω.functional.GNS) +
        inner ℂ (closedTomitaOperator ω hclos y.val)
          (closedTomitaOperator ω hclos (0 : closedTomitaDomain ω)) =
      inner ℂ ξ (a : ω.functional.GNS) at hv
    rw [inner_zero_left, map_zero, inner_zero_right, add_zero] at hv
    exact hv.symm
  have hdense : DenseRange (fun a : ω.functional.PreGNS => (a : ω.functional.GNS)) :=
    UniformSpace.Completion.denseRange_coe
  exact hdense.eq_zero_of_inner_left ℂ horth_core

theorem tomitaFormResolvent_injective :
    Function.Injective (tomitaFormResolventCLM ω hclos) :=
  (injective_iff_map_eq_zero (tomitaFormResolventCLM ω hclos)).mpr
    (tomitaFormResolvent_eq_zero ω hclos)

/-! =========================================================================
    1. Resolvent Range & Density of Closed Tomita Domain
    ========================================================================= -/

theorem tomitaFormResolvent_range_subset_domain :
    Set.range (tomitaFormResolventCLM ω hclos) ⊆
      (closedTomitaDomain ω : Set ω.functional.GNS) := by
  rintro _ ⟨ξ, rfl⟩
  exact (tomitaFormResolventDomCLM ω hclos ξ).val.property

theorem tomitaFormResolvent_denseRange :
    DenseRange (tomitaFormResolventCLM ω hclos) := by
  have hrange : Set.range (tomitaFormResolventCLM ω hclos) =
      ((tomitaFormResolventCLM ω hclos : ω.functional.GNS →ₗ[ℂ] ω.functional.GNS).range :
        Set ω.functional.GNS) := by
    rw [LinearMap.coe_range]
    rfl
  rw [DenseRange, hrange,
    Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff,
    ContinuousLinearMap.orthogonal_range, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
  have hadj : (tomitaFormResolventCLM ω hclos).adjoint = tomitaFormResolventCLM ω hclos := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (tomitaFormResolvent_isSelfAdjoint ω hclos).star_eq
  rw [hadj] at hx
  exact tomitaFormResolvent_eq_zero ω hclos x hx

theorem dense_closedTomitaDomain (hclos : IsClosableTomitaCore ω) :
    Dense (closedTomitaDomain ω : Set ω.functional.GNS) :=
  Dense.mono (tomitaFormResolvent_range_subset_domain ω hclos)
    (tomitaFormResolvent_denseRange ω hclos)

/-! =========================================================================
    2. Antilinear S ∘ R (ℝ-CLM) and Complementary Resolvent 1 - R
    ========================================================================= -/

/-- Bounded `ℝ`-linear (conjugate-`ℂ`-linear) companion `ξ ↦ S ((1 + Δ)⁻¹ ξ)` on
`ω.functional.GNS`, contractive of norm `≤ 1`. -/
def tomitaSCompResolventRLM :
    ω.functional.GNS →L[ℝ] ω.functional.GNS :=
  LinearMap.mkContinuous
    { toFun := fun ξ => closedTomitaOperator ω hclos (tomitaFormResolventDomCLM ω hclos ξ).val
      map_add' := fun ξ η => by
        rw [map_add]
        change closedTomitaOperator ω hclos
          ((tomitaFormResolventDomCLM ω hclos ξ).val +
            (tomitaFormResolventDomCLM ω hclos η).val) = _
        rw [map_add]
      map_smul' := fun r ξ => by
        have hsmul : (r : ℝ) • ξ = (r : ℂ) • ξ := rfl
        rw [hsmul, map_smul]
        change closedTomitaOperator ω hclos
          ((r : ℂ) • (tomitaFormResolventDomCLM ω hclos ξ).val) =
          (r : ℂ) • closedTomitaOperator ω hclos (tomitaFormResolventDomCLM ω hclos ξ).val
        rw [map_smulₛₗ, Complex.conj_ofReal] }
    1
    (fun ξ => by
      rw [one_mul]
      exact tomitaFormResolvent_S_norm_le ω hclos ξ)

@[simp]
theorem tomitaSCompResolventRLM_apply (ξ : ω.functional.GNS) :
    tomitaSCompResolventRLM ω hclos ξ =
      closedTomitaOperator ω hclos (tomitaFormResolventDomCLM ω hclos ξ).val := rfl

theorem tomitaSCompResolventRLM_norm_apply_le (ξ : ω.functional.GNS) :
    ‖tomitaSCompResolventRLM ω hclos ξ‖ ≤ ‖ξ‖ :=
  tomitaFormResolvent_S_norm_le ω hclos ξ

theorem tomitaSCompResolventRLM_norm_le :
    ‖tomitaSCompResolventRLM ω hclos‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Complementary resolvent `1 - R = Δ(1 + Δ)⁻¹` on `ω.functional.GNS`. -/
def tomitaFormComplementaryResolventCLM :
    ω.functional.GNS →L[ℂ] ω.functional.GNS :=
  ContinuousLinearMap.id ℂ ω.functional.GNS - tomitaFormResolventCLM ω hclos

theorem tomitaFormComplementaryResolventCLM_isSelfAdjoint :
    IsSelfAdjoint (tomitaFormComplementaryResolventCLM ω hclos) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', tomitaFormComplementaryResolventCLM,
    map_sub, ContinuousLinearMap.adjoint_id, ← ContinuousLinearMap.star_eq_adjoint,
    (tomitaFormResolvent_isSelfAdjoint ω hclos).star_eq]

theorem tomitaFormComplementaryResolventCLM_inner_bounds (ξ : ω.functional.GNS) :
    0 ≤ (inner ℂ ξ (tomitaFormComplementaryResolventCLM ω hclos ξ)).re ∧
      (inner ℂ ξ (tomitaFormComplementaryResolventCLM ω hclos ξ)).re ≤ ‖ξ‖ ^ 2 := by
  have hsub : inner ℂ ξ (tomitaFormComplementaryResolventCLM ω hclos ξ) =
      inner ℂ ξ ξ - inner ℂ ξ (tomitaFormResolventCLM ω hclos ξ) := by
    simp [tomitaFormComplementaryResolventCLM, inner_sub_right]
  have hre : (inner ℂ ξ (tomitaFormComplementaryResolventCLM ω hclos ξ)).re =
      ‖ξ‖ ^ 2 - (inner ℂ ξ (tomitaFormResolventCLM ω hclos ξ)).re := by
    rw [hsub, Complex.sub_re, ← RCLike.re_to_complex, ← InnerProductSpace.norm_sq_eq_re_inner]
  obtain ⟨h0, h1⟩ := tomitaFormResolvent_pos_le_one ω hclos ξ
  constructor <;> linarith

theorem tomitaFormComplementaryResolventCLM_norm_le (ξ : ω.functional.GNS) :
    ‖tomitaFormComplementaryResolventCLM ω hclos ξ‖ ≤ ‖ξ‖ := by
  have hsq : ‖tomitaFormComplementaryResolventCLM ω hclos ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
    change ‖ξ - tomitaFormResolventCLM ω hclos ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2
    rw [norm_sub_sq (𝕜 := ℂ)]
    simp only [RCLike.re_to_complex]
    have he := tomitaFormResolvent_energy ω hclos ξ
    obtain ⟨h0, _⟩ := tomitaFormResolvent_pos_le_one ω hclos ξ
    nlinarith [sq_nonneg ‖closedTomitaOperator ω hclos (tomitaFormResolventDomCLM ω hclos ξ).val‖]
  nlinarith [norm_nonneg (tomitaFormComplementaryResolventCLM ω hclos ξ), norm_nonneg ξ]

theorem tomitaFormComplementaryResolventCLM_opNorm_le :
    ‖tomitaFormComplementaryResolventCLM ω hclos‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by
    rw [one_mul]
    exact tomitaFormComplementaryResolventCLM_norm_le ω hclos ξ

end SingleStage

/-! =========================================================================
    3 & 5a. Bridge to `closedTomitaModularForm` and Filtered Stage Compatibility
    ========================================================================= -/

section FilteredModularAndTransition

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
variable (hclos : ∀ i, IsClosableTomitaCore (ω.state i))

/-- Identification of the stage graph inner product with the GNS inner product plus
`closedTomitaModularForm`. -/
theorem tomitaGraphInner_eq_inner_add_modularForm (i : I)
    (x y : TomitaGraphDom (ω.state i) (hclos i)) :
    inner ℂ x y =
      inner ℂ (x.val : (ω.state i).functional.GNS) (y.val : (ω.state i).functional.GNS) +
        closedTomitaModularForm Stage sys ω hclos i x.val y.val :=
  rfl

/-- Variational identity for `tomitaFormResolventCLM` expressed via `closedTomitaModularForm`. -/
theorem tomitaFormResolvent_modularForm_variational (i : I)
    (ξ : (ω.state i).functional.GNS) (y : closedTomitaDomain (ω.state i)) :
    inner ℂ (tomitaFormResolventCLM (ω.state i) (hclos i) ξ)
        (y : (ω.state i).functional.GNS) +
      closedTomitaModularForm Stage sys ω hclos i
        (tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ).val y =
      inner ℂ ξ (y : (ω.state i).functional.GNS) := by
  simpa only [closedTomitaModularForm_apply] using
    tomitaFormResolvent_variational (ω.state i) (hclos i) ξ ⟨y⟩

/-- Underlying complex-linear stage transition on `TomitaGraphDom`. -/
def filteredTomitaGraphDomLinearMap {i j : I} (hij : i ≤ j) :
    TomitaGraphDom (ω.state i) (hclos i) →ₗ[ℂ] TomitaGraphDom (ω.state j) (hclos j) where
  toFun x := ⟨filteredClosedTomitaDomainMap Stage sys ω hij x.val⟩
  map_add' x y := by
    apply TomitaGraphDom.ext
    exact (filteredClosedTomitaDomainMap Stage sys ω hij).map_add x.val y.val
  map_smul' c x := by
    apply TomitaGraphDom.ext
    exact (filteredClosedTomitaDomainMap Stage sys ω hij).map_smul c x.val

theorem filteredTomitaGraphDomLinearMap_inner {i j : I} (hij : i ≤ j)
    (x y : TomitaGraphDom (ω.state i) (hclos i)) :
    inner ℂ (filteredTomitaGraphDomLinearMap Stage sys ω hclos hij x)
        (filteredTomitaGraphDomLinearMap Stage sys ω hclos hij y) =
      inner ℂ x y := by
  rw [tomitaGraphInner_eq_inner_add_modularForm Stage sys ω hclos j,
    tomitaGraphInner_eq_inner_add_modularForm Stage sys ω hclos i]
  have h1 :
      inner ℂ
          ((filteredClosedTomitaDomainMap Stage sys ω hij x.val :
            closedTomitaDomain (ω.state j)) : (ω.state j).functional.GNS)
          ((filteredClosedTomitaDomainMap Stage sys ω hij y.val :
            closedTomitaDomain (ω.state j)) : (ω.state j).functional.GNS) =
        inner ℂ (x.val : (ω.state i).functional.GNS)
          (y.val : (ω.state i).functional.GNS) := by
    simpa only [filteredClosedTomitaDomainMap_apply, ← filteredGNSLinearIsometry_apply] using
      (filteredGNSLinearIsometry Stage sys ω hij).inner_map_map
        (x.val : (ω.state i).functional.GNS) (y.val : (ω.state i).functional.GNS)
  have h2 := filteredClosedTomitaDomainMap_preserves_modularForm
    Stage sys ω hclos hij x.val y.val
  exact congrArg₂ (· + ·) h1 h2

/-- Isometric complex-linear stage transition on `TomitaGraphDom` for `i ≤ j`. -/
def filteredTomitaGraphDomMap {i j : I} (hij : i ≤ j) :
    TomitaGraphDom (ω.state i) (hclos i) →ₗᵢ[ℂ] TomitaGraphDom (ω.state j) (hclos j) :=
  (filteredTomitaGraphDomLinearMap Stage sys ω hclos hij).isometryOfInner
    (filteredTomitaGraphDomLinearMap_inner Stage sys ω hclos hij)

@[simp]
theorem filteredTomitaGraphDomMap_val {i j : I} (hij : i ≤ j)
    (x : TomitaGraphDom (ω.state i) (hclos i)) :
    (filteredTomitaGraphDomMap Stage sys ω hclos hij x).val =
      filteredClosedTomitaDomainMap Stage sys ω hij x.val := rfl

@[simp]
theorem graphDomInclCLM_filteredTomitaGraphDomMap {i j : I} (hij : i ≤ j)
    (x : TomitaGraphDom (ω.state i) (hclos i)) :
    graphDomInclCLM (ω.state j) (hclos j)
        (filteredTomitaGraphDomMap Stage sys ω hclos hij x) =
      filteredGNSLinearIsometry Stage sys ω hij
        (graphDomInclCLM (ω.state i) (hclos i) x) := by
  simp [graphDomInclCLM_apply, filteredClosedTomitaDomainMap_apply, filteredGNSLinearIsometry_apply]

theorem filteredTomitaGraphDomMap_id (i : I)
    (x : TomitaGraphDom (ω.state i) (hclos i)) :
    filteredTomitaGraphDomMap Stage sys ω hclos (le_refl i) x = x := by
  apply TomitaGraphDom.ext
  exact LinearMap.congr_fun (filteredClosedTomitaDomainMap_id Stage sys ω i) x.val

theorem filteredTomitaGraphDomMap_comp {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (x : TomitaGraphDom (ω.state i) (hclos i)) :
    filteredTomitaGraphDomMap Stage sys ω hclos (le_trans hij hjk) x =
      filteredTomitaGraphDomMap Stage sys ω hclos hjk
        (filteredTomitaGraphDomMap Stage sys ω hclos hij x) := by
  apply TomitaGraphDom.ext
  exact (LinearMap.congr_fun (filteredClosedTomitaDomainMap_comp Stage sys ω hij hjk) x.val).symm

/-- Variational compatibility across filtered stages `i ≤ j`. -/
theorem filteredTomitaFormResolvent_variational_compat {i j : I} (hij : i ≤ j)
    (ξ : (ω.state i).functional.GNS)
    (y : TomitaGraphDom (ω.state i) (hclos i)) :
    inner ℂ
        (tomitaFormResolventCLM (ω.state j) (hclos j)
          (filteredGNSLinearIsometry Stage sys ω hij ξ))
        ((filteredTomitaGraphDomMap Stage sys ω hclos hij y).val :
          (ω.state j).functional.GNS) +
      closedTomitaModularForm Stage sys ω hclos j
        (tomitaFormResolventDomCLM (ω.state j) (hclos j)
          (filteredGNSLinearIsometry Stage sys ω hij ξ)).val
        (filteredTomitaGraphDomMap Stage sys ω hclos hij y).val =
      inner ℂ (tomitaFormResolventCLM (ω.state i) (hclos i) ξ)
          (y.val : (ω.state i).functional.GNS) +
        closedTomitaModularForm Stage sys ω hclos i
          (tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ).val y.val := by
  rw [tomitaFormResolvent_modularForm_variational Stage sys ω hclos j,
    tomitaFormResolvent_modularForm_variational Stage sys ω hclos i]
  have hy : ((filteredTomitaGraphDomMap Stage sys ω hclos hij y).val :
      (ω.state j).functional.GNS) =
      filteredGNSLinearIsometry Stage sys ω hij (y.val : (ω.state i).functional.GNS) := by
    simp [filteredClosedTomitaDomainMap_apply, filteredGNSLinearIsometry_apply]
  rw [hy]
  exact (filteredGNSLinearIsometry Stage sys ω hij).inner_map_map
    ξ (y.val : (ω.state i).functional.GNS)

/-- Orthogonal projection residual identity in `TomitaGraphDom (ω.state j) (hclos j)`:
`R_dom_j (U ξ) - V (R_dom_i ξ)` is orthogonal to `V (TomitaGraphDom_i)`. -/
theorem filteredTomitaFormResolvent_orth_proj {i j : I} (hij : i ≤ j)
    (ξ : (ω.state i).functional.GNS)
    (y : TomitaGraphDom (ω.state i) (hclos i)) :
    inner ℂ
        (tomitaFormResolventDomCLM (ω.state j) (hclos j)
            (filteredGNSLinearIsometry Stage sys ω hij ξ) -
          filteredTomitaGraphDomMap Stage sys ω hclos hij
            (tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ))
        (filteredTomitaGraphDomMap Stage sys ω hclos hij y) = 0 := by
  rw [inner_sub_left, tomitaFormResolventDomCLM_inner_left,
    (filteredTomitaGraphDomMap Stage sys ω hclos hij).inner_map_map,
    tomitaFormResolventDomCLM_inner_left]
  have hy : ((filteredTomitaGraphDomMap Stage sys ω hclos hij y).val :
      (ω.state j).functional.GNS) =
      filteredGNSLinearIsometry Stage sys ω hij (y.val : (ω.state i).functional.GNS) := by
    simp [filteredClosedTomitaDomainMap_apply, filteredGNSLinearIsometry_apply]
  rw [hy, (filteredGNSLinearIsometry Stage sys ω hij).inner_map_map, sub_self]

/-- Exact Pythagorean defect identity for stagewise Friedrichs resolvents. -/
theorem filteredTomitaFormResolvent_pythagoras {i j : I} (hij : i ≤ j)
    (ξ : (ω.state i).functional.GNS) :
    (inner ℂ ξ (tomitaFormResolventCLM (ω.state i) (hclos i) ξ)).re +
      ‖tomitaFormResolventDomCLM (ω.state j) (hclos j)
          (filteredGNSLinearIsometry Stage sys ω hij ξ) -
        filteredTomitaGraphDomMap Stage sys ω hclos hij
          (tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ)‖ ^ 2 =
      (inner ℂ (filteredGNSLinearIsometry Stage sys ω hij ξ)
        (tomitaFormResolventCLM (ω.state j) (hclos j)
          (filteredGNSLinearIsometry Stage sys ω hij ξ))).re := by
  let a := tomitaFormResolventDomCLM (ω.state j) (hclos j)
    (filteredGNSLinearIsometry Stage sys ω hij ξ)
  let b := filteredTomitaGraphDomMap Stage sys ω hclos hij
    (tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ)
  have horth : inner ℂ (a - b) b = 0 :=
    filteredTomitaFormResolvent_orth_proj Stage sys ω hclos hij ξ
      (tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ)
  have hpyth : ‖a‖ ^ 2 = ‖a - b‖ ^ 2 + ‖b‖ ^ 2 := by
    have hsum : a = (a - b) + b := (sub_add_cancel a b).symm
    conv_lhs => rw [hsum]
    have hre : ‖(a - b) + b‖ ^ 2 = (inner ℂ ((a - b) + b) ((a - b) + b)).re := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), RCLike.re_to_complex]
    rw [inner_add_left, inner_add_right, inner_add_right, horth,
      ← inner_conj_symm b (a - b), horth, map_zero, add_zero, zero_add,
      Complex.add_re, ← RCLike.re_to_complex, ← RCLike.re_to_complex,
      ← InnerProductSpace.norm_sq_eq_re_inner, ← InnerProductSpace.norm_sq_eq_re_inner] at hre
    exact hre
  have ha_norm : ‖a‖ ^ 2 =
      (inner ℂ (filteredGNSLinearIsometry Stage sys ω hij ξ)
        (tomitaFormResolventCLM (ω.state j) (hclos j)
          (filteredGNSLinearIsometry Stage sys ω hij ξ))).re := by
    have h : ‖a‖ ^ 2 = (inner ℂ a a).re := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), RCLike.re_to_complex]
    have hinner : inner ℂ a a =
        inner ℂ (filteredGNSLinearIsometry Stage sys ω hij ξ)
          (tomitaFormResolventCLM (ω.state j) (hclos j)
            (filteredGNSLinearIsometry Stage sys ω hij ξ)) :=
      tomitaFormResolventDomCLM_inner_left (ω.state j) (hclos j) _ a
    rw [h, hinner]
  have hb_norm : ‖b‖ ^ 2 =
      (inner ℂ ξ (tomitaFormResolventCLM (ω.state i) (hclos i) ξ)).re := by
    have h1 : ‖b‖ = ‖tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ‖ :=
      (filteredTomitaGraphDomMap Stage sys ω hclos hij).norm_map _
    have h : ‖tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ‖ ^ 2 =
        (inner ℂ (tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ)
          (tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ)).re := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), RCLike.re_to_complex]
    have hinner : inner ℂ (tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ)
          (tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ) =
        inner ℂ ξ (tomitaFormResolventCLM (ω.state i) (hclos i) ξ) :=
      tomitaFormResolventDomCLM_inner_left (ω.state i) (hclos i) ξ _
    rw [h1, h, hinner]
  linarith

/-- Quadratic-form monotonicity `R_i ≤ U^* R_j U` across filtered stages `i ≤ j`. -/
theorem filteredTomitaFormResolvent_monotone {i j : I} (hij : i ≤ j)
    (ξ : (ω.state i).functional.GNS) :
    (inner ℂ ξ (tomitaFormResolventCLM (ω.state i) (hclos i) ξ)).re ≤
      (inner ℂ (filteredGNSLinearIsometry Stage sys ω hij ξ)
        (tomitaFormResolventCLM (ω.state j) (hclos j)
          (filteredGNSLinearIsometry Stage sys ω hij ξ))).re := by
  have hpyth := filteredTomitaFormResolvent_pythagoras Stage sys ω hclos hij ξ
  linarith [sq_nonneg ‖tomitaFormResolventDomCLM (ω.state j) (hclos j)
    (filteredGNSLinearIsometry Stage sys ω hij ξ) -
    filteredTomitaGraphDomMap Stage sys ω hclos hij
      (tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ)‖]

end FilteredModularAndTransition

/-! =========================================================================
    4 & 5b. Contractions to `ModularHilbertCompletion` and Compatibility
    ========================================================================= -/

section ModularHilbertCompletionBridges

set_option synthInstance.maxHeartbeats 80000

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
variable (hclos : ∀ i, IsClosableTomitaCore (ω.state i))

/-- Complex-linear stage embedding from `closedTomitaDomain (ω.state i)` into
`ClosedDomainDirectLimit Stage sys ω`. -/
def stageDomainToDirectLimitLM (i : I) :
    closedTomitaDomain (ω.state i) →ₗ[ℂ] ClosedDomainDirectLimit Stage sys ω where
  toFun := Module.DirectLimit.of ℝ I
    (fun k => closedTomitaDomain (ω.state k))
    (fun _ _ h => domainTransition Stage sys ω h) i
  map_add' x y :=
    (Module.DirectLimit.of ℝ I
      (fun k => closedTomitaDomain (ω.state k))
      (fun _ _ h => domainTransition Stage sys ω h) i).map_add x y
  map_smul' c x := (complex_smul_of Stage sys ω c i x).symm

/-- Underlying complex-linear map from `TomitaGraphDom (ω.state i) (hclos i)` into
`ModularHilbertCompletion Stage sys ω hclos`. -/
def tomitaGraphDomToCompletionLM (i : I) :
    TomitaGraphDom (ω.state i) (hclos i) →ₗ[ℂ]
      ModularHilbertCompletion Stage sys ω hclos :=
  (modularQuotientToCompletionLinearIsometry Stage sys ω hclos).toLinearMap.comp
    ((modularNullSubmodule Stage sys ω hclos).mkQ.comp
      ((stageDomainToDirectLimitLM Stage sys ω i).comp
        (TomitaGraphDom.valLM (ω.state i) (hclos i))))

theorem tomitaGraphDomToCompletionLM_norm_sq (i : I)
    (x : TomitaGraphDom (ω.state i) (hclos i)) :
    ‖tomitaGraphDomToCompletionLM Stage sys ω hclos i x‖ ^ 2 =
      (closedTomitaModularForm Stage sys ω hclos i x.val x.val).re := by
  let z : ClosedDomainDirectLimit Stage sys ω :=
    Module.DirectLimit.of ℝ I (fun k => closedTomitaDomain (ω.state k))
      (fun _ _ h => domainTransition Stage sys ω h) i x.val
  let qz : ModularFormQuotient Stage sys ω hclos :=
    (modularNullSubmodule Stage sys ω hclos).mkQ z
  have h1 : tomitaGraphDomToCompletionLM Stage sys ω hclos i x =
      modularQuotientToCompletionLinearIsometry Stage sys ω hclos qz := rfl
  rw [h1, (modularQuotientToCompletionLinearIsometry Stage sys ω hclos).norm_map]
  have hre : ‖qz‖ ^ 2 = (inner ℂ qz qz).re := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), RCLike.re_to_complex]
  rw [modularQuotient_inner_eq] at hre
  have hqq : quotientModularForm Stage sys ω hclos qz qz =
      complexDirectLimitModularForm Stage sys ω hclos z z := by
    change quotientModularForm Stage sys ω hclos
      (Submodule.Quotient.mk z) (Submodule.Quotient.mk z) = _
    exact quotientModularForm_mk_mk Stage sys ω hclos z z
  rw [hqq, complexDirectLimitModularForm_apply] at hre
  have hdz : directLimitModularForm Stage sys ω hclos z z =
      commonStageModularPairing Stage sys ω hclos i i x.val x.val :=
    directLimitModularForm_of_of Stage sys ω hclos i i x.val x.val
  rw [hdz, commonStageModularPairing_eq_at Stage sys ω hclos i i i (le_refl i) (le_refl i)] at hre
  have hid : domainTransition Stage sys ω (le_refl i) x.val = x.val :=
    LinearMap.congr_fun (filteredClosedTomitaDomainMap_id Stage sys ω i) x.val
  rw [hid] at hre
  exact hre

theorem tomitaGraphDomToCompletionLM_norm_le (i : I)
    (x : TomitaGraphDom (ω.state i) (hclos i)) :
    ‖tomitaGraphDomToCompletionLM Stage sys ω hclos i x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul]
  have hsq : ‖tomitaGraphDomToCompletionLM Stage sys ω hclos i x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [tomitaGraphDomToCompletionLM_norm_sq, closedTomitaModularForm_apply]
    have hinner : (inner ℂ (closedTomitaOperator (ω.state i) (hclos i) x.val)
        (closedTomitaOperator (ω.state i) (hclos i) x.val)).re =
        ‖closedTomitaOperator (ω.state i) (hclos i) x.val‖ ^ 2 := by
      rw [← RCLike.re_to_complex, ← InnerProductSpace.norm_sq_eq_re_inner]
    rw [hinner]
    have hs := TomitaGraphDom.norm_S_le (ω.state i) (hclos i) x
    nlinarith [norm_nonneg (closedTomitaOperator (ω.state i) (hclos i) x.val), norm_nonneg x]
  nlinarith [norm_nonneg (tomitaGraphDomToCompletionLM Stage sys ω hclos i x), norm_nonneg x]

/-- Contractive continuous complex-linear map from `TomitaGraphDom (ω.state i) (hclos i)` into
`ModularHilbertCompletion Stage sys ω hclos`. -/
def tomitaGraphDom_to_modularHilbertCompletion (i : I) :
    TomitaGraphDom (ω.state i) (hclos i) →L[ℂ] ModularHilbertCompletion Stage sys ω hclos :=
  (tomitaGraphDomToCompletionLM Stage sys ω hclos i).mkContinuous 1
    (tomitaGraphDomToCompletionLM_norm_le Stage sys ω hclos i)

theorem tomitaGraphDom_to_modularHilbertCompletion_norm_le (i : I) :
    ‖tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos i‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem tomitaGraphDom_to_modularHilbertCompletion_apply_norm_sq (i : I)
    (x : TomitaGraphDom (ω.state i) (hclos i)) :
    ‖tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos i x‖ ^ 2 =
      (closedTomitaModularForm Stage sys ω hclos i x.val x.val).re :=
  tomitaGraphDomToCompletionLM_norm_sq Stage sys ω hclos i x

theorem tomitaGraphDom_to_modularHilbertCompletion_apply_norm_le (i : I)
    (x : TomitaGraphDom (ω.state i) (hclos i)) :
    ‖tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos i x‖ ≤ ‖x‖ := by
  have h := tomitaGraphDomToCompletionLM_norm_le Stage sys ω hclos i x
  rw [one_mul] at h
  exact h

/-- Contractive continuous complex-linear map from `(ω.state i).functional.GNS` into
`ModularHilbertCompletion Stage sys ω hclos` factored through the Friedrichs resolvent domain. -/
def gns_to_modularHilbertCompletion_via_resolvent (i : I) :
    (ω.state i).functional.GNS →L[ℂ] ModularHilbertCompletion Stage sys ω hclos :=
  (tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos i).comp
    (tomitaFormResolventDomCLM (ω.state i) (hclos i))

theorem gns_to_modularHilbertCompletion_via_resolvent_norm_le (i : I) :
    ‖gns_to_modularHilbertCompletion_via_resolvent Stage sys ω hclos i‖ ≤ 1 := by
  calc
    ‖(tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos i).comp
        (tomitaFormResolventDomCLM (ω.state i) (hclos i))‖
        ≤ ‖tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos i‖ *
            ‖tomitaFormResolventDomCLM (ω.state i) (hclos i)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by
      apply mul_le_mul
      · exact tomitaGraphDom_to_modularHilbertCompletion_norm_le Stage sys ω hclos i
      · exact tomitaFormResolventDomCLM_norm_le (ω.state i) (hclos i)
      · exact norm_nonneg (tomitaFormResolventDomCLM (ω.state i) (hclos i))
      · exact zero_le_one
    _ = 1 := mul_one 1

theorem gns_to_modularHilbertCompletion_via_resolvent_apply_norm_le (i : I)
    (ξ : (ω.state i).functional.GNS) :
    ‖gns_to_modularHilbertCompletion_via_resolvent Stage sys ω hclos i ξ‖ ≤ ‖ξ‖ := by
  calc
    ‖gns_to_modularHilbertCompletion_via_resolvent Stage sys ω hclos i ξ‖
        ≤ ‖tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ‖ :=
      tomitaGraphDom_to_modularHilbertCompletion_apply_norm_le Stage sys ω hclos i _
    _ ≤ ‖ξ‖ := tomitaFormResolventDomCLM_apply_norm_le (ω.state i) (hclos i) ξ

/-- Stage-transition compatibility of `tomitaGraphDom_to_modularHilbertCompletion` for `i ≤ j`. -/
theorem tomitaGraphDom_to_modularHilbertCompletion_compat {i j : I} (hij : i ≤ j)
    (x : TomitaGraphDom (ω.state i) (hclos i)) :
    tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos j
        (filteredTomitaGraphDomMap Stage sys ω hclos hij x) =
      tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos i x := by
  change modularQuotientToCompletionLinearIsometry Stage sys ω hclos
      ((modularNullSubmodule Stage sys ω hclos).mkQ
        (Module.DirectLimit.of ℝ I (fun k => closedTomitaDomain (ω.state k))
          (fun _ _ h => domainTransition Stage sys ω h) j
          (domainTransition Stage sys ω hij x.val))) =
    modularQuotientToCompletionLinearIsometry Stage sys ω hclos
      ((modularNullSubmodule Stage sys ω hclos).mkQ
        (Module.DirectLimit.of ℝ I (fun k => closedTomitaDomain (ω.state k))
          (fun _ _ h => domainTransition Stage sys ω h) i x.val))
  rw [Module.DirectLimit.of_f]

end ModularHilbertCompletionBridges

end CStarStateColimit.Native.FilteredGNSTomitaFriedrichsResolvent
