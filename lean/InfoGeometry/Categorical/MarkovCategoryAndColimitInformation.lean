/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import InfoGeometry.InformationGeometry.CsiszarAlphaDivergenceAndChentsovMonotonicity
import InfoGeometry.Amari.DuallyFlatThermodynamics
import InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
import InfoGeometry.Canonical.TensorTowerColimit

/-!
# Categorical Foundations of Markov Kernels, Bregman Duality, and Tower Colimit States

This module formalizes the categorical pillars of information geometry and noncommutative
tower states using native Mathlib category theory:

1. **The Category `FinSampleSpace` (`FinStoch`) of Finite Markov Kernels**:
   - Objects are finite decidable sample spaces (`FinSampleSpace`); morphisms are stochastic
     matrices (`VariationalRG.MarkovKernel`), with `idKernel` as identity and Chapman–Kolmogorov
     matrix multiplication (`VariationalRG.compose`) as composition.
   - Establishes the deterministic embedding `detKernel`, unique terminal discard morphism
     `discardKernel` (causality / trace preservation), and tensor product of channels
     `tensorKernel` obeying the functorial interchange law (`tensorKernel_compose`).
2. **State & Tangent Pushforward Functors and Compositional Data Processing**:
   - Constructs the covariant state functor `probDistFunctor : FinSampleSpace ⥤ Type u`,
     tangent pushforward functoriality (`pushforwardTangentVec_idKernel`,
     `pushforwardTangentVec_compose`), and compositional Fisher metric and Csiszár
     `f`-divergence contraction along composable Markov chains.
3. **Legendre–Bregman Primal-Dual Anti-Isomorphism & Exact Cocycle Identity**:
   - Establishes `canonicalDivergence_cocycle_identity` (exact four-point / three-point cocycle
     without spurious triangle hypotheses) and the Legendre duality anti-isomorphism
     `canonicalDivergence_dual_anti_iso` (`D_{Φ*}(∇Φ(x) ∥ ∇Φ(y)) = D_Φ(y ∥ x)`).
4. **Inductive `ClTower` Normalized State & Universal Filtered-Colimit Descent**:
   - Constructs the `ℝ`-linear normalized trace `normalizedTowerTrace` on `ClTower B n`,
     proves exact Bott–`diagEmbed` and `clTowerHom` state compatibility
     (`normalizedTowerTrace_clTowerHom`), unitality (`normalizedTowerTrace_one`), and
     `StarOrderedRing` state positivity (`normalizedTowerTrace_star_mul_self_nonneg`).
   - Lifts `ClTower` into `ModuleCat ℝ` (`clTowerModuleFunctor B : ℕ ⥤ ModuleCat ℝ`) and
     constructs the universal filtered-colimit state `colimitNormalizedTrace B` via
     `CategoryTheory.Limits.colimit.desc`, together with exact finite-stage readback and
     universal uniqueness.
-/

noncomputable section

namespace InfoGeometry.Categorical.MarkovCategoryAndColimitInformation

open Finset CategoryTheory CategoryTheory.Limits
open scoped BigOperators RealInnerProductSpace
open InfoGeometry.Epistemology.VariationalRG
open InfoGeometry.Epistemology.ChentsovMetricInvariance
open InfoGeometry.InformationGeometry.CsiszarAlphaDivergenceAndChentsovMonotonicity
open InfoGeometry.Convex
open InfoGeometry.Amari.DuallyFlatThermodynamics
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy
open InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
open InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge

universe u v

/-! ### 1. The Category `FinSampleSpace` (`FinStoch`) of Finite Markov Kernels -/

/-- Extensionality for `MarkovKernel`. -/
@[ext]
theorem markovKernel_ext {α β : Type*} [Fintype α] [Fintype β]
    {K₁ K₂ : MarkovKernel α β} (h : ∀ a b, K₁.T a b = K₂.T a b) :
    K₁ = K₂ := by
  cases K₁
  cases K₂
  congr
  funext a b
  exact h a b

/-- An object in the category `FinSampleSpace` (`FinStoch`): a finite sample space
equipped with decidable equality. -/
structure FinSampleSpace : Type (u + 1) where
  carrier : Type u
  fintype : Fintype carrier := by infer_instance
  decEq : DecidableEq carrier := by infer_instance

namespace FinSampleSpace

/-- Construct a `FinSampleSpace` from a type with `[Fintype α] [DecidableEq α]`. -/
def of (α : Type u) [Fintype α] [DecidableEq α] : FinSampleSpace.{u} where
  carrier := α
  fintype := inferInstance
  decEq := inferInstance

instance (X : FinSampleSpace.{u}) : Fintype X.carrier := X.fintype
instance (X : FinSampleSpace.{u}) : DecidableEq X.carrier := X.decEq

end FinSampleSpace

/-- Identity Markov kernel on a finite decidable sample space. -/
def idKernel (α : Type*) [Fintype α] [DecidableEq α] : MarkovKernel α α where
  T a b := if a = b then 1 else 0
  nonneg a b := by split_ifs <;> norm_num
  sum_one a := by simp

/-- Deterministic Markov kernel induced by any finite map `f : α → β`. -/
def detKernel {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) :
    MarkovKernel α β where
  T a b := if f a = b then 1 else 0
  nonneg a b := by split_ifs <;> norm_num
  sum_one a := by simp

/-- Canonical terminal finite sample space (`PUnit`). -/
def unitSampleSpace : FinSampleSpace.{u} :=
  FinSampleSpace.of PUnit.{u + 1}

/-- Unique trace-preserving discard Markov kernel to the terminal space `PUnit`. -/
def discardKernel {α : Type*} [Fintype α] : MarkovKernel α PUnit where
  T _ _ := 1
  nonneg _ _ := zero_le_one
  sum_one _ := by simp

/-- Parallel tensor product of two Markov kernels on product sample spaces. -/
def tensorKernel {α₁ β₁ α₂ β₂ : Type*}
    [Fintype α₁] [Fintype β₁] [Fintype α₂] [Fintype β₂]
    (K₁ : MarkovKernel α₁ β₁) (K₂ : MarkovKernel α₂ β₂) :
    MarkovKernel (α₁ × α₂) (β₁ × β₂) where
  T p q := K₁.T p.1 q.1 * K₂.T p.2 q.2
  nonneg p q := mul_nonneg (K₁.nonneg p.1 q.1) (K₂.nonneg p.2 q.2)
  sum_one p := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ b₁, ∑ b₂, K₁.T p.1 b₁ * K₂.T p.2 b₂
          = ∑ b₁, K₁.T p.1 b₁ * ∑ b₂, K₂.T p.2 b₂ := by
              refine Finset.sum_congr rfl ?_
              intro b₁ _
              rw [← Finset.mul_sum]
      _ = ∑ b₁, K₁.T p.1 b₁ * 1 := by
            refine Finset.sum_congr rfl ?_
            intro b₁ _
            rw [K₂.sum_one p.2]
      _ = 1 := by simpa using K₁.sum_one p.1

theorem compose_idKernel {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (K : MarkovKernel α β) :
    InfoGeometry.Epistemology.VariationalRG.compose K (idKernel β) = K := by
  apply markovKernel_ext
  intro a c
  simp [InfoGeometry.Epistemology.VariationalRG.compose, idKernel]

theorem idKernel_compose {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (K : MarkovKernel α β) :
    InfoGeometry.Epistemology.VariationalRG.compose (idKernel α) K = K := by
  apply markovKernel_ext
  intro a c
  simp [InfoGeometry.Epistemology.VariationalRG.compose, idKernel]

theorem compose_assoc {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (K₁ : MarkovKernel α β) (K₂ : MarkovKernel β γ) (K₃ : MarkovKernel γ δ) :
    InfoGeometry.Epistemology.VariationalRG.compose
        (InfoGeometry.Epistemology.VariationalRG.compose K₁ K₂) K₃ =
      InfoGeometry.Epistemology.VariationalRG.compose K₁
        (InfoGeometry.Epistemology.VariationalRG.compose K₂ K₃) := by
  apply markovKernel_ext
  intro a d
  dsimp [InfoGeometry.Epistemology.VariationalRG.compose]
  calc
    ∑ c, (∑ b, K₁.T a b * K₂.T b c) * K₃.T c d
        = ∑ c, ∑ b, (K₁.T a b * K₂.T b c) * K₃.T c d := by
            refine Finset.sum_congr rfl ?_
            intro c _
            rw [Finset.sum_mul]
    _ = ∑ b, ∑ c, K₁.T a b * (K₂.T b c * K₃.T c d) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro b _
          refine Finset.sum_congr rfl ?_
          intro c _
          ring
    _ = ∑ b, K₁.T a b * ∑ c, K₂.T b c * K₃.T c d := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [← Finset.mul_sum]

/-- Native Mathlib `CategoryTheory.Category` instance for `FinSampleSpace` (`FinStoch`). -/
instance instCategoryFinSampleSpace : CategoryTheory.Category.{u, u + 1} FinSampleSpace.{u} where
  Hom X Y := MarkovKernel X.carrier Y.carrier
  id X := idKernel X.carrier
  comp K₁ K₂ := InfoGeometry.Epistemology.VariationalRG.compose K₁ K₂
  id_comp K := idKernel_compose K
  comp_id K := compose_idKernel K
  assoc K₁ K₂ K₃ := compose_assoc K₁ K₂ K₃

@[simp]
theorem finSampleSpace_id_eq {X : FinSampleSpace.{u}} :
    (𝟙 X : X ⟶ X) = idKernel X.carrier := rfl

@[simp]
theorem finSampleSpace_comp_eq {X Y Z : FinSampleSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X ⟶ Z) = InfoGeometry.Epistemology.VariationalRG.compose f g := rfl

theorem detKernel_id (α : Type*) [Fintype α] [DecidableEq α] :
    detKernel (id : α → α) = idKernel α := rfl

theorem detKernel_comp {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (f : α → β) (g : β → γ) :
    InfoGeometry.Epistemology.VariationalRG.compose (detKernel f) (detKernel g) =
      detKernel (g ∘ f) := by
  apply markovKernel_ext
  intro a c
  dsimp [InfoGeometry.Epistemology.VariationalRG.compose, detKernel]
  rw [Finset.sum_eq_single (f a)]
  · simp
  · intro b _ hne
    simp [Ne.symm hne]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

/-- Terminal causality: `discardKernel` is the unique Markov kernel into `PUnit`. -/
theorem discardKernel_unique {α : Type*} [Fintype α] (K : MarkovKernel α PUnit) :
    K = discardKernel := by
  apply markovKernel_ext
  intro a b
  cases b
  simpa [discardKernel] using K.sum_one a

/-- Composition causality: every Markov kernel followed by `discardKernel` equals
`discardKernel`. -/
theorem compose_discardKernel {α β : Type*} [Fintype α] [Fintype β]
    (K : MarkovKernel α β) :
    InfoGeometry.Epistemology.VariationalRG.compose K (discardKernel (α := β)) = discardKernel :=
  discardKernel_unique _

theorem tensorKernel_id (α₁ α₂ : Type*)
    [Fintype α₁] [DecidableEq α₁] [Fintype α₂] [DecidableEq α₂] :
    tensorKernel (idKernel α₁) (idKernel α₂) = idKernel (α₁ × α₂) := by
  apply markovKernel_ext
  intro p q
  rcases p with ⟨a₁, a₂⟩
  rcases q with ⟨b₁, b₂⟩
  dsimp [tensorKernel, idKernel]
  by_cases h1 : a₁ = b₁ <;> by_cases h2 : a₂ = b₂ <;> simp [h1, h2]

/-- Monoidal interchange law for parallel tensor products and sequential composition of
Markov kernels. -/
theorem tensorKernel_compose {α₁ β₁ γ₁ α₂ β₂ γ₂ : Type*}
    [Fintype α₁] [Fintype β₁] [Fintype γ₁] [Fintype α₂] [Fintype β₂] [Fintype γ₂]
    (K₁ : MarkovKernel α₁ β₁) (L₁ : MarkovKernel β₁ γ₁)
    (K₂ : MarkovKernel α₂ β₂) (L₂ : MarkovKernel β₂ γ₂) :
    InfoGeometry.Epistemology.VariationalRG.compose (tensorKernel K₁ K₂) (tensorKernel L₁ L₂) =
      tensorKernel (InfoGeometry.Epistemology.VariationalRG.compose K₁ L₁)
        (InfoGeometry.Epistemology.VariationalRG.compose K₂ L₂) := by
  apply markovKernel_ext
  intro p r
  dsimp [InfoGeometry.Epistemology.VariationalRG.compose, tensorKernel]
  rw [Fintype.sum_prod_type]
  calc
    ∑ b₁, ∑ b₂, (K₁.T p.1 b₁ * K₂.T p.2 b₂) * (L₁.T b₁ r.1 * L₂.T b₂ r.2)
        = ∑ b₁, ∑ b₂, (K₁.T p.1 b₁ * L₁.T b₁ r.1) * (K₂.T p.2 b₂ * L₂.T b₂ r.2) := by
            refine Finset.sum_congr rfl ?_
            intro b₁ _
            refine Finset.sum_congr rfl ?_
            intro b₂ _
            ring
    _ = ∑ b₁, (K₁.T p.1 b₁ * L₁.T b₁ r.1) * ∑ b₂, K₂.T p.2 b₂ * L₂.T b₂ r.2 := by
          refine Finset.sum_congr rfl ?_
          intro b₁ _
          rw [← Finset.mul_sum]
    _ = (∑ b₁, K₁.T p.1 b₁ * L₁.T b₁ r.1) * ∑ b₂, K₂.T p.2 b₂ * L₂.T b₂ r.2 := by
          rw [← Finset.sum_mul]

/-! ### 2. Functoriality of Probability States, Tangent Pushforwards, and Contraction -/

@[ext]
theorem probDist_ext {α : Type*} [Fintype α] {P₁ P₂ : ProbDist α} (h : P₁.p = P₂.p) :
    P₁ = P₂ := by
  cases P₁
  cases P₂
  congr

@[ext]
theorem probInterior_ext {α : Type*} [Fintype α] {P₁ P₂ : ProbInterior α} (h : P₁.p = P₂.p) :
    P₁ = P₂ := by
  cases P₁
  cases P₂
  congr

theorem pushforward_idKernel {α : Type*} [Fintype α] [DecidableEq α] (P : ProbDist α) :
    pushforward (idKernel α) P = P := by
  apply probDist_ext
  funext b
  simp [pushforward, idKernel]

theorem pushforward_compose_eq {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (K₁ : MarkovKernel α β) (K₂ : MarkovKernel β γ) (P : ProbDist α) :
    pushforward (InfoGeometry.Epistemology.VariationalRG.compose K₁ K₂) P =
      pushforward K₂ (pushforward K₁ P) :=
  probDist_ext (InfoGeometry.Epistemology.VariationalRG.pushforward_compose K₁ K₂ P)

/-- Covariant functor `FinSampleSpace ⥤ Type u` sending each finite sample space to its
simplex of finite probability distributions `ProbDist`. -/
def probDistFunctor : FinSampleSpace.{u} ⥤ Type u where
  obj X := ProbDist X.carrier
  map {X Y} K := TypeCat.ofHom (fun P => pushforward K P)
  map_id X := by
    ext P a
    exact congrFun (congrArg ProbDist.p (pushforward_idKernel P)) a
  map_comp {X Y Z} K₁ K₂ := by
    ext P a
    exact congrFun (congrArg ProbDist.p (pushforward_compose_eq K₁ K₂ P)) a

@[simp]
theorem pushforwardTangentVec_idKernel {α : Type*} [Fintype α] [DecidableEq α] (u : α → ℝ) :
    pushforwardTangentVec (idKernel α) u = u := by
  funext b
  simp [pushforwardTangentVec, idKernel]

theorem pushforwardTangentVec_compose {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (K₁ : MarkovKernel α β) (K₂ : MarkovKernel β γ) (u : α → ℝ) :
    pushforwardTangentVec (InfoGeometry.Epistemology.VariationalRG.compose K₁ K₂) u =
      pushforwardTangentVec K₂ (pushforwardTangentVec K₁ u) := by
  funext c
  dsimp [pushforwardTangentVec, InfoGeometry.Epistemology.VariationalRG.compose]
  calc
    ∑ a, u a * ∑ b, K₁.T a b * K₂.T b c
        = ∑ a, ∑ b, (u a * K₁.T a b) * K₂.T b c := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro b _
            ring
    _ = ∑ b, ∑ a, (u a * K₁.T a b) * K₂.T b c := Finset.sum_comm
    _ = ∑ b, (∑ a, u a * K₁.T a b) * K₂.T b c := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [← Finset.sum_mul]

theorem colNondegenerate_idKernel (α : Type*) [Fintype α] [DecidableEq α] :
    ColNondegenerate (idKernel α) := by
  intro b
  exact ⟨b, by simp [idKernel]⟩

theorem colNondegenerate_compose {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {K₁ : MarkovKernel α β} {K₂ : MarkovKernel β γ}
    (h₁ : ColNondegenerate K₁) (h₂ : ColNondegenerate K₂) :
    ColNondegenerate (InfoGeometry.Epistemology.VariationalRG.compose K₁ K₂) := by
  intro c
  rcases h₂ c with ⟨b, hb⟩
  rcases h₁ b with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  dsimp [InfoGeometry.Epistemology.VariationalRG.compose]
  exact Finset.sum_pos'
    (fun b' _ => mul_nonneg (K₁.nonneg a b') (K₂.nonneg b' c))
    ⟨b, Finset.mem_univ b, mul_pos ha hb⟩

theorem pushInterior_compose {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (K₁ : MarkovKernel α β) (K₂ : MarkovKernel β γ)
    (h₁ : ColNondegenerate K₁) (h₂ : ColNondegenerate K₂) (P : ProbInterior α) :
    pushInterior (InfoGeometry.Epistemology.VariationalRG.compose K₁ K₂) P
        (colNondegenerate_compose h₁ h₂) =
      pushInterior K₂ (pushInterior K₁ P h₁) h₂ := by
  apply probInterior_ext
  have hcomp := InfoGeometry.Epistemology.VariationalRG.pushforward_compose K₁ K₂ (toProbDist P)
  simpa [pushInterior, toProbDist] using hcomp

/-- Categorical two-step Fisher metric monotonicity along composable morphisms in
`FinSampleSpace`. -/
theorem categorical_fisher_contraction_comp {X Y Z : FinSampleSpace.{u}}
    (K₁ : X ⟶ Y) (K₂ : Y ⟶ Z)
    (h₁ : ColNondegenerate K₁) (h₂ : ColNondegenerate K₂)
    (P : ProbInterior X.carrier) (u : X.carrier → ℝ) :
    fisherMetric (pushInterior (K₁ ≫ K₂) P (colNondegenerate_compose h₁ h₂))
        (pushforwardTangentVec (K₁ ≫ K₂) u) (pushforwardTangentVec (K₁ ≫ K₂) u) ≤
      fisherMetric (pushInterior K₁ P h₁) (pushforwardTangentVec K₁ u)
        (pushforwardTangentVec K₁ u) ∧
    fisherMetric (pushInterior K₁ P h₁) (pushforwardTangentVec K₁ u)
        (pushforwardTangentVec K₁ u) ≤
      fisherMetric P u u := by
  refine ⟨?_, chentsov_markov_fisher_contraction K₁ P h₁ u⟩
  change fisherMetric
      (pushInterior (InfoGeometry.Epistemology.VariationalRG.compose K₁ K₂) P
        (colNondegenerate_compose h₁ h₂))
      (pushforwardTangentVec (InfoGeometry.Epistemology.VariationalRG.compose K₁ K₂) u)
      (pushforwardTangentVec (InfoGeometry.Epistemology.VariationalRG.compose K₁ K₂) u) ≤
    fisherMetric (pushInterior K₁ P h₁) (pushforwardTangentVec K₁ u)
      (pushforwardTangentVec K₁ u)
  rw [pushInterior_compose K₁ K₂ h₁ h₂ P, pushforwardTangentVec_compose K₁ K₂ u]
  exact chentsov_markov_fisher_contraction K₂ (pushInterior K₁ P h₁) h₂
    (pushforwardTangentVec K₁ u)

/-- Categorical two-step Csiszár `f`-divergence Data Processing Inequality along composable
morphisms in `FinSampleSpace`. -/
theorem categorical_csiszar_dpi_comp {X Y Z : FinSampleSpace.{u}}
    (K₁ : X ⟶ Y) (K₂ : Y ⟶ Z)
    (h₁ : ColNondegenerate K₁) (h₂ : ColNondegenerate K₂)
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici (0 : ℝ)) f)
    (P Q : ProbInterior X.carrier) :
    csiszarFDivergence f
        (pushInterior (K₁ ≫ K₂) P (colNondegenerate_compose h₁ h₂)).p
        (pushInterior (K₁ ≫ K₂) Q (colNondegenerate_compose h₁ h₂)).p ≤
      csiszarFDivergence f (pushInterior K₁ P h₁).p (pushInterior K₁ Q h₁).p ∧
    csiszarFDivergence f (pushInterior K₁ P h₁).p (pushInterior K₁ Q h₁).p ≤
      csiszarFDivergence f P.p Q.p := by
  refine ⟨?_, csiszarFDivergence_markov_contraction K₁ h₁ f hf P Q⟩
  change csiszarFDivergence f
      (pushInterior (InfoGeometry.Epistemology.VariationalRG.compose K₁ K₂) P
        (colNondegenerate_compose h₁ h₂)).p
      (pushInterior (InfoGeometry.Epistemology.VariationalRG.compose K₁ K₂) Q
        (colNondegenerate_compose h₁ h₂)).p ≤
    csiszarFDivergence f (pushInterior K₁ P h₁).p (pushInterior K₁ Q h₁).p
  rw [pushInterior_compose K₁ K₂ h₁ h₂ P, pushInterior_compose K₁ K₂ h₁ h₂ Q]
  exact csiszarFDivergence_markov_contraction K₂ h₂ f hf
    (pushInterior K₁ P h₁) (pushInterior K₁ Q h₁)

/-! ### 3. Legendre–Bregman Primal-Dual Anti-Isomorphism & Exact Cocycle Law -/

section BregmanDuality

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
  [CompleteSpace Space]

/-- Exact Bregman cocycle (three-point defect) identity for `Amari.DuallyFlatThermodynamics.canonicalDivergence`
on arbitrary smooth convex potentials without triangle-inequality assumptions. -/
theorem canonicalDivergence_cocycle_identity
    (Φ : ConvexFunctional Space) (x y z : Space) :
    canonicalDivergence Φ x y + canonicalDivergence Φ y z - canonicalDivergence Φ x z =
      ⟪z - y, Φ.grad x - Φ.grad y⟫ := by
  have h := amari_three_point_identity Φ x y z
  rw [inner_sub_right] at h ⊢
  linarith [h]

/-- Exact Bregman cocycle bound from Cauchy–Schwarz: the defect between
`D_Φ(x ∥ z)` and `D_Φ(x ∥ y) + D_Φ(y ∥ z)` is bounded in magnitude by
`‖z - y‖ * ‖∇Φ(x) - ∇Φ(y)‖`. -/
theorem canonicalDivergence_cocycle_abs_le
    (Φ : ConvexFunctional Space) (x y z : Space) :
    |canonicalDivergence Φ x z - (canonicalDivergence Φ x y + canonicalDivergence Φ y z)| ≤
      ‖z - y‖ * ‖Φ.grad x - Φ.grad y‖ := by
  have h := canonicalDivergence_cocycle_identity Φ x y z
  have habs :
      canonicalDivergence Φ x z - (canonicalDivergence Φ x y + canonicalDivergence Φ y z) =
        -⟪z - y, Φ.grad x - Φ.grad y⟫ := by linarith [h]
  rw [habs, abs_neg]
  exact abs_real_inner_le_norm (z - y) (Φ.grad x - Φ.grad y)

/-- **Legendre–Bregman Primal-Dual Anti-Isomorphism**: whenever `primal` and `dual` form a
Legendre-conjugate pair (`dual.grad (primal.grad x) = x` and
`primal.F x + dual.F (primal.grad x) = ⟪x, primal.grad x⟫`), pushing forward by `primal.grad`
reverses the arguments of the canonical Bregman divergence:
`D_{dual}(∇Φ(x) ∥ ∇Φ(y)) = D_{primal}(y ∥ x)`. -/
theorem canonicalDivergence_dual_anti_iso
    (primal dual : ConvexFunctional Space)
    (hinv : Function.LeftInverse dual.grad primal.grad)
    (hfy : ∀ z : Space, primal.F z + dual.F (primal.grad z) = ⟪z, primal.grad z⟫)
    (x y : Space) :
    canonicalDivergence dual (primal.grad x) (primal.grad y) =
      canonicalDivergence primal y x := by
  rw [canonical_divergence_eq_bregman dual (primal.grad x) (primal.grad y),
    canonical_divergence_eq_bregman primal y x, hinv x]
  have hy := hfy y
  have hx := hfy x
  have hix : ⟪x, primal.grad y - primal.grad x⟫ = ⟪x, primal.grad y⟫ - ⟪x, primal.grad x⟫ :=
    inner_sub_right x (primal.grad y) (primal.grad x)
  have hiy : ⟪primal.grad y, x - y⟫ = ⟪x, primal.grad y⟫ - ⟪y, primal.grad y⟫ := by
    rw [inner_sub_right, real_inner_comm (primal.grad y) x, real_inner_comm (primal.grad y) y]
  linarith [hy, hx, hix, hiy]

end BregmanDuality

/-! ### 4. Inductive `ClTower` Normalized State & Filtered-Colimit Universal Descent -/

section ClTowerNormalizedState

/-- Recursive `R`-module structure on `ClTower B n` matching `instRingClTower`'s additive
group structure. -/
@[reducible]
instance instModuleClTower {R : Type*} {B : Type u} [Semiring R] [Ring B] [Module R B] :
    ∀ n : ℕ, Module R (ClTower B n)
  | 0 => inferInstanceAs (Module R B)
  | n + 1 => by
      letI : Ring (ClTower B n) := instRingClTower n
      letI : Module R (ClTower B n) := instModuleClTower n
      exact inferInstanceAs (Module R (Matrix (Fin 2) (Fin 2) (ClTower B n)))

lemma towerTrace_smul {R : Type*} {B : Type u} [Semiring R] [Ring B] [Module R B] (r : R) :
    ∀ (n : ℕ) (X : ClTower B n),
      towerTrace (n := n) (r • X) = r • towerTrace (n := n) X
  | 0, _ => rfl
  | n + 1, X => by
      have h00 : (r • X) 0 0 = r • X 0 0 := rfl
      have h11 : (r • X) 1 1 = r • X 1 1 := rfl
      change towerTrace (n := n) ((r • X) 0 0) + towerTrace (n := n) ((r • X) 1 1) =
        r • (towerTrace (n := n) (X 0 0) + towerTrace (n := n) (X 1 1))
      rw [h00, h11, towerTrace_smul r n (X 0 0), towerTrace_smul r n (X 1 1), smul_add]

/-- `ℝ`-linear unnormalized tower trace `ClTower B n →ₗ[ℝ] B`. -/
def towerTraceLinear (B : Type u) [Ring B] [Module ℝ B] (n : ℕ) : ClTower B n →ₗ[ℝ] B where
  toFun := towerTrace
  map_add' := towerTrace_add n
  map_smul' r X := towerTrace_smul r n X

/-- `ℝ`-linear normalized tracial state `(1 / 2) ^ n • towerTrace` on `ClTower B n`,
invariant under every scale transition `clTowerHom B h : ClTower B m →+* ClTower B n`. -/
def normalizedTowerTrace (B : Type u) [Ring B] [Module ℝ B] (n : ℕ) : ClTower B n →ₗ[ℝ] B :=
  ((1 / 2 : ℝ) ^ n) • towerTraceLinear B n

lemma diagEmbed_smul {B : Type u} [Ring B] [Module ℝ B] (r : ℝ)
    {n : ℕ} (X : ClTower B n) :
    diagEmbed (r • X) = r • diagEmbed X := by
  apply ext_fin2 <;> simp [diagEmbed, Matrix.smul_apply]

lemma clTowerHom_smul {B : Type u} [Ring B] [Module ℝ B] (r : ℝ) :
    ∀ {m n : ℕ} (h : m ≤ n) (X : ClTower B m),
      clTowerHom B h (r • X) = r • clTowerHom B h X
  | m, 0, h, X => by
      obtain rfl : m = 0 := Nat.le_zero.mp h
      rfl
  | m, n + 1, h, X => by
      by_cases heq : m = n + 1
      · subst heq
        rw [clTowerHom_refl, clTowerHom_refl]
      · have hlt : m ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne h heq)
        rw [clTowerHom_step hlt (r • X), clTowerHom_step hlt X,
          clTowerHom_smul r hlt X, diagEmbed_smul r (clTowerHom B hlt X)]

/-- Promote the unital ring transition `clTowerHom B h` to an `ℝ`-linear map. -/
def clTowerLinearMap (B : Type u) [Ring B] [Module ℝ B]
    {m n : ℕ} (h : m ≤ n) : ClTower B m →ₗ[ℝ] ClTower B n where
  toFun := clTowerHom B h
  map_add' X Y := (clTowerHom B h).map_add X Y
  map_smul' r X := clTowerHom_smul r h X

@[simp]
lemma normalizedTowerTrace_zero (B : Type u) [Ring B] [Module ℝ B] (X : ClTower B 0) :
    normalizedTowerTrace B 0 X = X := by
  change ((1 / 2 : ℝ) ^ 0) • towerTrace (n := 0) X = X
  rw [pow_zero, one_smul]
  rfl

/-- Bott/scale invariance of `normalizedTowerTrace` across a single `diagEmbed` step. -/
theorem normalizedTowerTrace_diagEmbed (B : Type u) [Ring B] [Module ℝ B]
    (n : ℕ) (X : ClTower B n) :
    normalizedTowerTrace B (n + 1) (diagEmbed X) = normalizedTowerTrace B n X := by
  have htr : towerTrace (n := n + 1) (diagEmbed X) = (2 : ℝ) • towerTrace (n := n) X := by
    change towerTrace (n := n) (mat2 X 0 0 X 0 0) + towerTrace (n := n) (mat2 X 0 0 X 1 1) =
      (2 : ℝ) • towerTrace (n := n) X
    rw [mat2_00, mat2_11, ← two_smul ℝ (towerTrace X)]
  change ((1 / 2 : ℝ) ^ (n + 1)) • towerTrace (n := n + 1) (diagEmbed X) =
    ((1 / 2 : ℝ) ^ n) • towerTrace (n := n) X
  rw [htr, smul_smul]
  have hpow : (1 / 2 : ℝ) ^ (n + 1) * (2 : ℝ) = (1 / 2 : ℝ) ^ n := by
    rw [pow_succ']
    ring
  rw [hpow]

/-- Exact scale invariance across arbitrary `m ≤ n`: `normalizedTowerTrace` factors through
every `clTowerHom B h`. -/
theorem normalizedTowerTrace_clTowerHom (B : Type u) [Ring B] [Module ℝ B] :
    ∀ {m n : ℕ} (h : m ≤ n) (X : ClTower B m),
      normalizedTowerTrace B n (clTowerHom B h X) = normalizedTowerTrace B m X
  | m, 0, h, X => by
      obtain rfl : m = 0 := Nat.le_zero.mp h
      rw [clTowerHom_refl]
  | m, n + 1, h, X => by
      by_cases heq : m = n + 1
      · subst heq
        rw [clTowerHom_refl]
      · have hlt : m ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne h heq)
        rw [clTowerHom_step hlt X, normalizedTowerTrace_diagEmbed B n (clTowerHom B hlt X),
          normalizedTowerTrace_clTowerHom B hlt X]

/-- Unital normalization: `normalizedTowerTrace B n 1 = 1` at every stage `n : ℕ`. -/
theorem normalizedTowerTrace_one (B : Type u) [Ring B] [Module ℝ B] :
    ∀ (n : ℕ), normalizedTowerTrace B n 1 = 1
  | 0 => normalizedTowerTrace_zero B 1
  | n + 1 => by
      have h1 : (1 : ClTower B (n + 1)) = diagEmbed (1 : ClTower B n) := by
        apply ext_fin2 <;> simp [diagEmbed]
      rw [h1, normalizedTowerTrace_diagEmbed B n 1, normalizedTowerTrace_one B n]

/-- State positivity: in any `[StarOrderedRing B]` with `[PosSMulMono ℝ B]`,
`0 ≤ normalizedTowerTrace B n (star X * X)` at every finite stage `n : ℕ`. -/
theorem normalizedTowerTrace_star_mul_self_nonneg (B : Type u)
    [Ring B] [PartialOrder B] [IsOrderedAddMonoid B] [StarRing B] [StarOrderedRing B]
    [Module ℝ B] [PosSMulMono ℝ B]
    (n : ℕ) (X : ClTower B n) :
    (0 : B) ≤ normalizedTowerTrace B n (star X * X) := by
  dsimp [normalizedTowerTrace, towerTraceLinear]
  exact smul_nonneg (by positivity) (towerTrace_star_mul_self_nonneg X)

/-- The normalized trace is nonnegative on the additive star-square cone at each
finite tower stage. The stage itself need not carry an order: its positive cone
is explicitly the additive submonoid generated by elements `star X * X`. -/
theorem normalizedTowerTrace_nonneg_of_starSquareClosure (B : Type u)
    [Ring B] [PartialOrder B] [IsOrderedAddMonoid B] [StarRing B] [StarOrderedRing B]
    [Module ℝ B] [PosSMulMono ℝ B]
    (n : ℕ) {X : ClTower B n}
    (hX : X ∈ AddSubmonoid.closure (Set.range fun Y : ClTower B n => star Y * Y)) :
    (0 : B) ≤ normalizedTowerTrace B n X := by
  refine AddSubmonoid.closure_induction
      (s := Set.range fun Y : ClTower B n => star Y * Y)
      (motive := fun x _ => (0 : B) ≤ normalizedTowerTrace B n x)
      ?_ ?_ ?_ hX
  · intro x hx
    obtain ⟨Y, rfl⟩ := hx
    exact normalizedTowerTrace_star_mul_self_nonneg B n Y
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_nonneg hx hy

end ClTowerNormalizedState

section ModuleCatFilteredColimit

/-- Native Mathlib `ModuleCat ℝ` diagram functor `ℕ ⥤ ModuleCat ℝ` of the inductive
`ClTower B` system. -/
def clTowerModuleFunctor (B : Type u) [Ring B] [Module ℝ B] : ℕ ⥤ ModuleCat.{u} ℝ where
  obj n := ModuleCat.of.{u} ℝ (ClTower B n)
  map {m n} f := ModuleCat.ofHom (clTowerLinearMap B (leOfHom f))
  map_id n := by
    ext x
    exact clTowerHom_refl n x
  map_comp {m k n} f g := by
    ext x
    exact clTowerHom_trans (leOfHom f) (leOfHom g) x

/-- Native Mathlib filtered colimit of `clTowerModuleFunctor B` in `ModuleCat ℝ`. -/
abbrev ClTowerModuleColimit (B : Type u) [Ring B] [Module ℝ B] : ModuleCat.{u} ℝ :=
  Limits.colimit (clTowerModuleFunctor B)

/-- Cocone in `ModuleCat ℝ` induced by the coherent normalized tracial state family
`normalizedTowerTrace B n`. -/
def normalizedTowerTraceCocone (B : Type u) [Ring B] [Module ℝ B] :
    Limits.Cocone (clTowerModuleFunctor B) where
  pt := ModuleCat.of.{u} ℝ B
  ι :=
    { app := fun n => ModuleCat.ofHom (normalizedTowerTrace B n)
      naturality := fun {m n} f => by
        ext x
        exact normalizedTowerTrace_clTowerHom B (leOfHom f) x }

/-- Universal filtered-colimit state descending from `ClTowerModuleColimit B` to `B`
via `CategoryTheory.Limits.colimit.desc`. -/
def colimitNormalizedTrace (B : Type u) [Ring B] [Module ℝ B] :
    ClTowerModuleColimit B ⟶ ModuleCat.of.{u} ℝ B :=
  Limits.colimit.desc (clTowerModuleFunctor B) (normalizedTowerTraceCocone B)

/-- Stage readback compatibility: composing the universal colimit state with the canonical
stage injection `colimit.ι` recovers `normalizedTowerTrace B n` identically. -/
theorem colimitNormalizedTrace_ι (B : Type u) [Ring B] [Module ℝ B] (n : ℕ) :
    Limits.colimit.ι (clTowerModuleFunctor B) n ≫ colimitNormalizedTrace B =
      ModuleCat.ofHom (normalizedTowerTrace B n) :=
  Limits.colimit.ι_desc (normalizedTowerTraceCocone B) n

/-- Positivity descends to every represented positive stage element in the
module colimit. This only asserts positivity of the scalar readout: the
`ModuleCat ℝ` colimit has no induced multiplication or star operation. -/
theorem colimitNormalizedTrace_stage_positive (B : Type u)
    [Ring B] [PartialOrder B] [IsOrderedAddMonoid B] [StarRing B] [StarOrderedRing B]
    [Module ℝ B] [PosSMulMono ℝ B]
    (n : ℕ) (X : ClTower B n)
    (hX : X ∈ AddSubmonoid.closure (Set.range fun Y : ClTower B n => star Y * Y)) :
    (0 : B) ≤ (colimitNormalizedTrace B).hom
      ((Limits.colimit.ι (clTowerModuleFunctor B) n).hom X) := by
  have hread :
      (colimitNormalizedTrace B).hom
        ((Limits.colimit.ι (clTowerModuleFunctor B) n).hom X) =
        normalizedTowerTrace B n X :=
    congrArg
      (fun f : ModuleCat.of.{u} ℝ (ClTower B n) ⟶ ModuleCat.of.{u} ℝ B => f.hom X)
      (colimitNormalizedTrace_ι B n)
  rw [hread]
  exact normalizedTowerTrace_nonneg_of_starSquareClosure B n hX

/-- Universal uniqueness of `colimitNormalizedTrace`: it is the unique `ℝ`-linear colimit
morphism restricting to `normalizedTowerTrace B n` on every stage `n : ℕ`. -/
theorem colimitNormalizedTrace_unique (B : Type u) [Ring B] [Module ℝ B]
    (ψ : ClTowerModuleColimit B ⟶ ModuleCat.of.{u} ℝ B)
    (hψ : ∀ n : ℕ, Limits.colimit.ι (clTowerModuleFunctor B) n ≫ ψ =
      ModuleCat.ofHom (normalizedTowerTrace B n)) :
    ψ = colimitNormalizedTrace B :=
  Limits.colimit.hom_ext (fun n => by rw [hψ n, colimitNormalizedTrace_ι])

end ModuleCatFilteredColimit

end InfoGeometry.Categorical.MarkovCategoryAndColimitInformation

end section
