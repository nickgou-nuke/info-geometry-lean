/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.BilinearForm.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebraGeneral
import InfoGeometry.Thermo.OnsagerOperatorClosure
import InfoGeometry.Thermo.SusceptibilityOnsagerStress

/-!
# Onsager–Casimir Pairings on General Operator Differential Forms

This module preserves the degree-1 `Op1Form` compatibility theorems and extends
`OnsagerCasimirSystem` and `ParityOnsagerSystem` to arbitrary-degree alternating
operator differential forms (`V [⋀^Fin n]→ₗ[ℝ] A`), covering
`ActionOperatorForm K n`, `DerivationOperatorForm K n`, and `OpForm ℝ V A n`
definitionally, together with `ThermodynamicOperatorDerivation` adapters into the
unified `NonAssocDerivation.derivations` / `LieActionLane` / `DerivationLieLane` spine.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Thermo.OnsagerFormsBridge

open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem

variable {V W A : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]
  [Ring A] [Algebra ℝ A]

/-- The induced Onsager dissipative bilinear metric on operator 1-forms evaluated on test vectors. -/
def dissipative1Form
    (S : OnsagerCasimirSystem A) (α β : Op1Form ℝ V A) (u v : V) : ℝ :=
  S.dissipative (α u) (β v)

/-- The induced Onsager reversible skew-symplectic form on operator 1-forms. -/
def reversible1Form
    (S : OnsagerCasimirSystem A) (α β : Op1Form ℝ V A) (u v : V) : ℝ :=
  S.reversible (α u) (β v)

/-- The induced total non-equilibrium generator on operator 1-forms. -/
def totalGenerator1Form
    (S : OnsagerCasimirSystem A) (α β : Op1Form ℝ V A) (u v : V) : ℝ :=
  S.totalGenerator (α u) (β v)

/-- THEOREM 1 (1-Form Onsager Reciprocity):
    On matching test state u, the dissipative metric is symmetric in 1-forms:
      L(α u, β u) = L(β u, α u)
-/
theorem dissipative1Form_symm
    (S : OnsagerCasimirSystem A) (α β : Op1Form ℝ V A) (u : V) :
    dissipative1Form S α β u u = dissipative1Form S β α u u := by
  dsimp [dissipative1Form]
  exact S.dissipative_symm (α u) (β u)

/-- THEOREM 2 (1-Form Skew Reversibility):
    The reversible generator is skew-symmetric on 1-forms:
      Ω(α u, β u) = - Ω(β u, α u)
-/
theorem reversible1Form_skew
    (S : OnsagerCasimirSystem A) (α β : Op1Form ℝ V A) (u : V) :
    reversible1Form S α β u u = - reversible1Form S β α u u := by
  dsimp [reversible1Form]
  exact S.reversible_skew (α u) (β u)

/-- THEOREM 3 (Zero Dissipation of Reversible Bracket on 1-Forms):
    Ω(α u, α u) = 0
-/
@[simp]
theorem reversible1Form_diag_zero
    (S : OnsagerCasimirSystem A) (α : Op1Form ℝ V A) (u : V) :
    reversible1Form S α α u u = 0 := by
  dsimp [reversible1Form]
  exact S.reversible_diag_zero (α u)

/-- THEOREM 4 (1-Form Total Entropy Production):
    W(α u, α u) = L(α u, α u) ≥ 0
-/
theorem totalGenerator1Form_diag_eq
    (S : OnsagerCasimirSystem A) (α : Op1Form ℝ V A) (u : V) :
    totalGenerator1Form S α α u u = dissipative1Form S α α u u := by
  dsimp [totalGenerator1Form, dissipative1Form]
  exact S.entropy_production_eq (α u)

/-- THEOREM 5 (Second Law on Operator 1-Forms):
    Total entropy production of any operator 1-form is unconditionally non-negative:
      0 ≤ W(α u, α u)
-/
theorem totalGenerator1Form_nonneg
    (S : OnsagerCasimirSystem A) (α : Op1Form ℝ V A) (u : V) :
    0 ≤ totalGenerator1Form S α α u u := by
  dsimp [totalGenerator1Form]
  exact S.entropy_production_nonneg (α u)

/-- THEOREM 6 (Master Onsager–Casimir Reciprocity on Operator 1-Forms):
    Under time reversal T on the operator algebra, the 1-form generator satisfies:
      W((T ∘ α) u, (T ∘ β) u) = W(β u, α u)
-/
theorem onsager_casimir_1Form_master_reciprocity
    (PS : ParityOnsagerSystem A) (α β : Op1Form ℝ V A) (u : V) :
    PS.totalGenerator (PS.T.op (α u)) (PS.T.op (β u)) =
      totalGenerator1Form PS.toOnsagerCasimirSystem β α u u := by
  dsimp [totalGenerator1Form]
  exact PS.onsager_casimir_master_reciprocity (α u) (β u)

/-- THEOREM 7 (Pullback Invariance of the 1-Form Response):
    Pullback along linear map ϕ : W → V preserves the Onsager metric evaluated on pulled-back vectors:
      L(ϕ* α w, ϕ* β w) = L(α (ϕ w), β (ϕ w))
-/
theorem pullback_dissipative1Form_eq
    (S : OnsagerCasimirSystem A) (ϕ : W →ₗ[ℝ] V) (α β : Op1Form ℝ V A) (w : W) :
    dissipative1Form S (pullback1 ϕ α) (pullback1 ϕ β) w w =
      dissipative1Form S α β (ϕ w) (ϕ w) := by
  rfl

end InfoGeometry.Thermo.OnsagerFormsBridge

namespace InfoGeometry.Thermo.OnsagerFormsBridge

open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem

/-! ## General arbitrary-degree Onsager pairings on `V [⋀^Fin n]→ₗ[ℝ] A` -/

section GeneralFormPairing

variable {V W A : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup A] [Module ℝ A]

/-- Evaluation of an alternating `n`-form at a fixed `n`-frame `v : Fin n → V`
as an `ℝ`-linear map `(V [⋀^Fin n]→ₗ[ℝ] A) →ₗ[ℝ] A`. -/
def evalAlternatingForm (V A : Type*) [AddCommGroup V] [Module ℝ V]
    [AddCommGroup A] [Module ℝ A] (n : ℕ) (v : Fin n → V) :
    (V [⋀^Fin n]→ₗ[ℝ] A) →ₗ[ℝ] A where
  toFun ω := ω v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evalAlternatingForm_apply (n : ℕ) (v : Fin n → V) (ω : V [⋀^Fin n]→ₗ[ℝ] A) :
    evalAlternatingForm V A n v ω = ω v :=
  rfl

/-- Pullback of alternating `n`-forms along a linear map `ϕ : W →ₗ[ℝ] V`,
packaged as an `ℝ`-linear map. -/
def pullbackFormLM {n : ℕ} (ϕ : W →ₗ[ℝ] V) :
    (V [⋀^Fin n]→ₗ[ℝ] A) →ₗ[ℝ] (W [⋀^Fin n]→ₗ[ℝ] A) where
  toFun ω := ω.compLinearMap ϕ
  map_add' _ _ := by ext v; rfl
  map_smul' _ _ := by ext v; rfl

@[simp]
theorem pullbackFormLM_apply {n : ℕ} (ϕ : W →ₗ[ℝ] V)
    (ω : V [⋀^Fin n]→ₗ[ℝ] A) (w : Fin n → W) :
    pullbackFormLM ϕ ω w = ω (fun i => ϕ (w i)) :=
  rfl

/-- Coefficient transport of alternating `n`-forms along an `ℝ`-linear map
`f : B →ₗ[ℝ] A`, packaged as an `ℝ`-linear map. -/
def mapValuesFormLM {B : Type*} [AddCommGroup B] [Module ℝ B] {n : ℕ} (f : B →ₗ[ℝ] A) :
    (V [⋀^Fin n]→ₗ[ℝ] B) →ₗ[ℝ] (V [⋀^Fin n]→ₗ[ℝ] A) where
  toFun ω := f.compAlternatingMap ω
  map_add' _ _ := by ext v; simp
  map_smul' _ _ := by ext v; simp

@[simp]
theorem mapValuesFormLM_apply {B : Type*} [AddCommGroup B] [Module ℝ B] {n : ℕ}
    (f : B →ₗ[ℝ] A) (ω : V [⋀^Fin n]→ₗ[ℝ] B) (v : Fin n → V) :
    mapValuesFormLM f ω v = f (ω v) :=
  rfl

/-- An Onsager–Casimir system directly on arbitrary-degree alternating
`A`-valued `n`-forms `V [⋀^Fin n]→ₗ[ℝ] A`, covering `ActionOperatorForm`,
`DerivationOperatorForm`, and `OpForm` definitionally without requiring
finite dimensionality or a ring structure on `A`. -/
structure OnsagerFormPairing (V A : Type*) (n : ℕ)
    [AddCommGroup V] [Module ℝ V] [AddCommGroup A] [Module ℝ A]
    extends OnsagerCasimirSystem (V [⋀^Fin n]→ₗ[ℝ] A)

namespace OnsagerFormPairing

/-- Pull back an `OnsagerCasimirSystem` on the value space `A` along a single
`n`-frame `v : Fin n → V`. -/
def ofFrame (S : OnsagerCasimirSystem A) {n : ℕ} (v : Fin n → V) :
    OnsagerFormPairing V A n where
  dissipative := S.dissipative.compl₁₂ (evalAlternatingForm V A n v) (evalAlternatingForm V A n v)
  reversible := S.reversible.compl₁₂ (evalAlternatingForm V A n v) (evalAlternatingForm V A n v)
  dissipative_symm ω η := S.dissipative_symm (ω v) (η v)
  reversible_skew ω η := S.reversible_skew (ω v) (η v)
  dissipative_nonneg ω := S.dissipative_nonneg (ω v)

@[simp]
theorem ofFrame_dissipative (S : OnsagerCasimirSystem A) {n : ℕ} (v : Fin n → V)
    (ω η : V [⋀^Fin n]→ₗ[ℝ] A) :
    (ofFrame S v).dissipative ω η = S.dissipative (ω v) (η v) :=
  rfl

@[simp]
theorem ofFrame_reversible (S : OnsagerCasimirSystem A) {n : ℕ} (v : Fin n → V)
    (ω η : V [⋀^Fin n]→ₗ[ℝ] A) :
    (ofFrame S v).reversible ω η = S.reversible (ω v) (η v) :=
  rfl

@[simp]
theorem ofFrame_totalGenerator (S : OnsagerCasimirSystem A) {n : ℕ} (v : Fin n → V)
    (ω η : V [⋀^Fin n]→ₗ[ℝ] A) :
    (ofFrame S v).totalGenerator ω η = S.totalGenerator (ω v) (η v) :=
  rfl

/-- Weighted finite sum of frame-induced Onsager form pairings. -/
def ofWeightedFrames (S : OnsagerCasimirSystem A) {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (frames : ι → Fin n → V) :
    OnsagerFormPairing V A n where
  dissipative := ∑ i : ι,
    w i • S.dissipative.compl₁₂
      (evalAlternatingForm V A n (frames i))
      (evalAlternatingForm V A n (frames i))
  reversible := ∑ i : ι,
    w i • S.reversible.compl₁₂
      (evalAlternatingForm V A n (frames i))
      (evalAlternatingForm V A n (frames i))
  dissipative_symm ω η := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
      evalAlternatingForm_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [S.dissipative_symm]
  reversible_skew ω η := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
      evalAlternatingForm_apply, smul_eq_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [S.reversible_skew, mul_neg]
  dissipative_nonneg ω := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
      evalAlternatingForm_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (S.dissipative_nonneg (ω (frames i)))

/-- Push an `OnsagerFormPairing` on `W`-forms forward along `ϕ : W →ₗ[ℝ] V`
via pullback of forms `ω ↦ ω.compLinearMap ϕ`. -/
def pushforward {n : ℕ} (ϕ : W →ₗ[ℝ] V) (P : OnsagerFormPairing W A n) :
    OnsagerFormPairing V A n where
  dissipative := P.dissipative.compl₁₂ (pullbackFormLM ϕ) (pullbackFormLM ϕ)
  reversible := P.reversible.compl₁₂ (pullbackFormLM ϕ) (pullbackFormLM ϕ)
  dissipative_symm _ω _η := P.dissipative_symm _ _
  reversible_skew _ω _η := P.reversible_skew _ _
  dissipative_nonneg _ω := P.dissipative_nonneg _

@[simp]
theorem pushforward_dissipative {n : ℕ} (ϕ : W →ₗ[ℝ] V) (P : OnsagerFormPairing W A n)
    (ω η : V [⋀^Fin n]→ₗ[ℝ] A) :
    (P.pushforward ϕ).dissipative ω η =
      P.dissipative (ω.compLinearMap ϕ) (η.compLinearMap ϕ) :=
  rfl

@[simp]
theorem pushforward_reversible {n : ℕ} (ϕ : W →ₗ[ℝ] V) (P : OnsagerFormPairing W A n)
    (ω η : V [⋀^Fin n]→ₗ[ℝ] A) :
    (P.pushforward ϕ).reversible ω η =
      P.reversible (ω.compLinearMap ϕ) (η.compLinearMap ϕ) :=
  rfl

theorem pushforward_apply {n : ℕ} (ϕ : W →ₗ[ℝ] V) (P : OnsagerFormPairing W A n)
    (ω η : V [⋀^Fin n]→ₗ[ℝ] A) :
    (P.pushforward ϕ).totalGenerator ω η =
      P.totalGenerator (ω.compLinearMap ϕ) (η.compLinearMap ϕ) :=
  rfl

theorem pushforward_ofFrame {n : ℕ} (S : OnsagerCasimirSystem A) (ϕ : W →ₗ[ℝ] V)
    (w : Fin n → W) :
    (ofFrame S w).pushforward ϕ = ofFrame S (fun i => ϕ (w i)) := by
  cases S
  rfl

/-- Pull an `OnsagerFormPairing` on `A`-valued forms back to `B`-valued forms along
an `ℝ`-linear value map `f : B →ₗ[ℝ] A`. -/
def mapValues {B : Type*} [AddCommGroup B] [Module ℝ B] {n : ℕ}
    (f : B →ₗ[ℝ] A) (P : OnsagerFormPairing V A n) :
    OnsagerFormPairing V B n where
  dissipative := P.dissipative.compl₁₂ (mapValuesFormLM f) (mapValuesFormLM f)
  reversible := P.reversible.compl₁₂ (mapValuesFormLM f) (mapValuesFormLM f)
  dissipative_symm _ω _η := P.dissipative_symm _ _
  reversible_skew _ω _η := P.reversible_skew _ _
  dissipative_nonneg _ω := P.dissipative_nonneg _

@[simp]
theorem mapValues_apply {B : Type*} [AddCommGroup B] [Module ℝ B] {n : ℕ}
    (f : B →ₗ[ℝ] A) (P : OnsagerFormPairing V A n) (ω η : V [⋀^Fin n]→ₗ[ℝ] B) :
    (P.mapValues f).totalGenerator ω η =
      P.totalGenerator (f.compAlternatingMap ω) (f.compAlternatingMap η) :=
  rfl

end OnsagerFormPairing

/-- Post-composition time-reversal involution on `V [⋀^Fin n]→ₗ[ℝ] A` induced
by a `TimeReversal A` on the value space. -/
def formTimeReversal (T : TimeReversal A) (n : ℕ) :
    TimeReversal (V [⋀^Fin n]→ₗ[ℝ] A) where
  op := mapValuesFormLM (V := V) T.op
  involutive ω := by
    ext v
    exact T.involutive (ω v)

@[simp]
theorem formTimeReversal_apply (T : TimeReversal A) (n : ℕ)
    (ω : V [⋀^Fin n]→ₗ[ℝ] A) (v : Fin n → V) :
    (formTimeReversal (V := V) T n).op ω v = T.op (ω v) :=
  rfl

/-- Pre-composition time-reversal involution on `V [⋀^Fin n]→ₗ[ℝ] A` induced
by a `TimeReversal V` on the domain tangent space. -/
def domainFormTimeReversal (T_V : TimeReversal V) (n : ℕ) :
    TimeReversal (V [⋀^Fin n]→ₗ[ℝ] A) where
  op := pullbackFormLM (A := A) T_V.op
  involutive ω := by
    ext v
    change ω (fun i => T_V.op (T_V.op (v i))) = ω v
    congr 1
    funext i
    exact T_V.involutive (v i)

@[simp]
theorem domainFormTimeReversal_apply (T_V : TimeReversal V) (n : ℕ)
    (ω : V [⋀^Fin n]→ₗ[ℝ] A) (v : Fin n → V) :
    (domainFormTimeReversal (A := A) T_V n).op ω v = ω (fun i => T_V.op (v i)) :=
  rfl

/-- Parity-equipped Onsager–Casimir system on arbitrary-degree alternating
`A`-valued `n`-forms. -/
structure ParityOnsagerFormPairing (V A : Type*) (n : ℕ)
    [AddCommGroup V] [Module ℝ V] [AddCommGroup A] [Module ℝ A]
    extends OnsagerFormPairing V A n where
  T : TimeReversal (V [⋀^Fin n]→ₗ[ℝ] A)
  dissipative_T_even : ∀ ω η, dissipative (T.op ω) (T.op η) = dissipative ω η
  reversible_T_odd : ∀ ω η, reversible (T.op ω) (T.op η) = - reversible ω η

namespace ParityOnsagerFormPairing

/-- View a `ParityOnsagerFormPairing V A n` as a canonical `ParityOnsagerSystem`
on the module `V [⋀^Fin n]→ₗ[ℝ] A`. -/
def toParityOnsagerSystem {n : ℕ} (PP : ParityOnsagerFormPairing V A n) :
    ParityOnsagerSystem (V [⋀^Fin n]→ₗ[ℝ] A) where
  toOnsagerCasimirSystem := PP.toOnsagerCasimirSystem
  T := PP.T
  dissipative_T_even := PP.dissipative_T_even
  reversible_T_odd := PP.reversible_T_odd

/-- Lift a `ParityOnsagerSystem A` along a frame `v : Fin n → V`. -/
def ofValueParity (PS : ParityOnsagerSystem A) {n : ℕ} (v : Fin n → V) :
    ParityOnsagerFormPairing V A n where
  toOnsagerFormPairing := OnsagerFormPairing.ofFrame PS.toOnsagerCasimirSystem v
  T := formTimeReversal PS.T n
  dissipative_T_even ω η := PS.dissipative_T_even (ω v) (η v)
  reversible_T_odd ω η := PS.reversible_T_odd (ω v) (η v)

/-- Lift a `ParityOnsagerSystem A` along a nonnegatively weighted finite frame family. -/
def ofWeightedValueParity (PS : ParityOnsagerSystem A) {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (frames : ι → Fin n → V) :
    ParityOnsagerFormPairing V A n where
  toOnsagerFormPairing := OnsagerFormPairing.ofWeightedFrames PS.toOnsagerCasimirSystem w hw frames
  T := formTimeReversal PS.T n
  dissipative_T_even ω η := by
    simp only [OnsagerFormPairing.ofWeightedFrames, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.compl₁₂_apply, evalAlternatingForm_apply,
      formTimeReversal_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PS.dissipative_T_even]
  reversible_T_odd ω η := by
    simp only [OnsagerFormPairing.ofWeightedFrames, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.compl₁₂_apply, evalAlternatingForm_apply,
      formTimeReversal_apply, smul_eq_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PS.reversible_T_odd, mul_neg]

/-- Unconditional domain-orbit construction: given any `S : OnsagerCasimirSystem A`
and domain involution `T_V : TimeReversal V`, symmetrizing `S.dissipative` and
antisymmetrizing `S.reversible` over the `T_V`-orbit of `v` yields a genuine
`ParityOnsagerFormPairing` under `domainFormTimeReversal T_V n`. -/
def ofDomainOrbit (S : OnsagerCasimirSystem A) (T_V : TimeReversal V)
    {n : ℕ} (v : Fin n → V) :
    ParityOnsagerFormPairing V A n where
  dissipative :=
    S.dissipative.compl₁₂ (evalAlternatingForm V A n v) (evalAlternatingForm V A n v) +
      S.dissipative.compl₁₂
        (evalAlternatingForm V A n (fun i => T_V.op (v i)))
        (evalAlternatingForm V A n (fun i => T_V.op (v i)))
  reversible :=
    S.reversible.compl₁₂ (evalAlternatingForm V A n v) (evalAlternatingForm V A n v) -
      S.reversible.compl₁₂
        (evalAlternatingForm V A n (fun i => T_V.op (v i)))
        (evalAlternatingForm V A n (fun i => T_V.op (v i)))
  dissipative_symm ω η := by
    simp only [LinearMap.BilinForm.add_apply, LinearMap.compl₁₂_apply, evalAlternatingForm_apply]
    rw [S.dissipative_symm (ω v) (η v),
      S.dissipative_symm (ω (fun i => T_V.op (v i))) (η (fun i => T_V.op (v i)))]
  reversible_skew ω η := by
    simp only [LinearMap.BilinForm.sub_apply, LinearMap.compl₁₂_apply, evalAlternatingForm_apply]
    rw [S.reversible_skew (ω v) (η v),
      S.reversible_skew (ω (fun i => T_V.op (v i))) (η (fun i => T_V.op (v i)))]
    ring
  dissipative_nonneg ω := by
    simp only [LinearMap.BilinForm.add_apply, LinearMap.compl₁₂_apply, evalAlternatingForm_apply]
    exact add_nonneg (S.dissipative_nonneg _) (S.dissipative_nonneg _)
  T := domainFormTimeReversal T_V n
  dissipative_T_even ω η := by
    simp only [LinearMap.BilinForm.add_apply, LinearMap.compl₁₂_apply, evalAlternatingForm_apply,
      domainFormTimeReversal_apply]
    have hTT : (fun i => T_V.op (T_V.op (v i))) = v := funext fun i => T_V.involutive (v i)
    rw [hTT, add_comm]
  reversible_T_odd ω η := by
    simp only [LinearMap.BilinForm.sub_apply, LinearMap.compl₁₂_apply, evalAlternatingForm_apply,
      domainFormTimeReversal_apply]
    have hTT : (fun i => T_V.op (T_V.op (v i))) = v := funext fun i => T_V.involutive (v i)
    rw [hTT]
    ring

end ParityOnsagerFormPairing

/-- Master Onsager–Casimir reciprocity for arbitrary-degree operator differential
forms: `W(T α, T β) = W(β, α)`. -/
theorem onsager_pairing_general_form_reciprocity
    {n : ℕ} (PP : ParityOnsagerFormPairing V A n) (ω η : V [⋀^Fin n]→ₗ[ℝ] A) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  PP.toParityOnsagerSystem.onsager_casimir_master_reciprocity ω η

theorem onsager_pairing_symm_part
    {n : ℕ} (P : OnsagerFormPairing V A n) (ω η : V [⋀^Fin n]→ₗ[ℝ] A) :
    (1 / 2 : ℝ) * (P.totalGenerator ω η + P.totalGenerator η ω) = P.dissipative ω η :=
  P.toOnsagerCasimirSystem.totalGenerator_symm_part ω η

theorem onsager_pairing_skew_part
    {n : ℕ} (P : OnsagerFormPairing V A n) (ω η : V [⋀^Fin n]→ₗ[ℝ] A) :
    (1 / 2 : ℝ) * (P.totalGenerator ω η - P.totalGenerator η ω) = P.reversible ω η :=
  P.toOnsagerCasimirSystem.totalGenerator_skew_part ω η

theorem onsager_pairing_entropy_production_eq
    {n : ℕ} (P : OnsagerFormPairing V A n) (ω : V [⋀^Fin n]→ₗ[ℝ] A) :
    P.totalGenerator ω ω = P.dissipative ω ω :=
  P.toOnsagerCasimirSystem.entropy_production_eq ω

theorem onsager_pairing_entropy_production_nonneg
    {n : ℕ} (P : OnsagerFormPairing V A n) (ω : V [⋀^Fin n]→ₗ[ℝ] A) :
    0 ≤ P.totalGenerator ω ω :=
  P.toOnsagerCasimirSystem.entropy_production_nonneg ω

theorem onsager_pairing_entropy_T_invariant
    {n : ℕ} (PP : ParityOnsagerFormPairing V A n) (ω : V [⋀^Fin n]→ₗ[ℝ] A) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op ω) = PP.totalGenerator ω ω :=
  PP.toParityOnsagerSystem.entropy_production_T_invariant ω

/-- Two-frame evaluation helpers generalizing `dissipative1Form`/`reversible1Form`/
`totalGenerator1Form` to arbitrary degree `n`. -/
def dissipativeForm (S : OnsagerCasimirSystem A) {n : ℕ}
    (α β : V [⋀^Fin n]→ₗ[ℝ] A) (u v : Fin n → V) : ℝ :=
  S.dissipative (α u) (β v)

def reversibleForm (S : OnsagerCasimirSystem A) {n : ℕ}
    (α β : V [⋀^Fin n]→ₗ[ℝ] A) (u v : Fin n → V) : ℝ :=
  S.reversible (α u) (β v)

def totalGeneratorForm (S : OnsagerCasimirSystem A) {n : ℕ}
    (α β : V [⋀^Fin n]→ₗ[ℝ] A) (u v : Fin n → V) : ℝ :=
  S.totalGenerator (α u) (β v)

theorem totalGeneratorForm_diag_eq (S : OnsagerCasimirSystem A) {n : ℕ}
    (α β : V [⋀^Fin n]→ₗ[ℝ] A) (u : Fin n → V) :
    totalGeneratorForm S α β u u =
      (OnsagerFormPairing.ofFrame S u).totalGenerator α β :=
  rfl

/-- Embed an `OnsagerTwoOperatorForm A` (from `SusceptibilityOnsagerStress`)
into `OnsagerCasimirSystem A` with zero reversible part, without adding orphan instances. -/
def onsagerCasimirSystemOfTwoOperatorForm
    (L : InfoGeometry.Thermo.SusceptibilityOnsagerStress.OnsagerTwoOperatorForm A) :
    OnsagerCasimirSystem A where
  dissipative := L.form
  reversible := 0
  dissipative_symm := L.symmetric
  reversible_skew x y := by simp
  dissipative_nonneg := L.diagonal_nonnegative

@[simp]
theorem onsagerCasimirSystemOfTwoOperatorForm_totalGenerator
    (L : InfoGeometry.Thermo.SusceptibilityOnsagerStress.OnsagerTwoOperatorForm A)
    (a b : A) :
    (onsagerCasimirSystemOfTwoOperatorForm L).totalGenerator a b = L.form a b := by
  simp [onsagerCasimirSystemOfTwoOperatorForm, OnsagerCasimirSystem.totalGenerator]

end GeneralFormPairing

/-! ## Carrier Specializations (`ActionOperatorForm`, `DerivationOperatorForm`, `OpForm`, DGA) -/

section CarrierSpecializations

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.General
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

section ActionLaneSpecialization

variable {A : Type*} [Ring A] [Module ℝ A]

/-- Master Onsager–Casimir reciprocity specialized to `ActionOperatorForm K n`. -/
theorem onsager_pairing_actionForm_reciprocity
    (K : LieActionLane ℝ A) {n : ℕ}
    (PP : ParityOnsagerFormPairing K.L A n)
    (ω η : ActionOperatorForm K n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_general_form_reciprocity PP ω η

/-- Exactness `d_{n+1} (d_n ω) = 0` gives zero total entropy production on
`ActionOperatorForm K (n + 2)` under any `OnsagerFormPairing`. -/
theorem onsager_pairing_actionExteriorDerivative_d_sq_zero
    (K : LieActionLane ℝ A) (n : ℕ)
    (P : OnsagerFormPairing K.L A (n + 2))
    (ω : ActionOperatorForm K n) :
    P.totalGenerator
        (actionExteriorDerivative K (n + 1) (actionExteriorDerivative K n ω))
        (actionExteriorDerivative K (n + 1) (actionExteriorDerivative K n ω)) = 0 := by
  rw [actionExteriorDerivative_succ_comp K n ω, map_zero]

/-- Pullback of `ActionOperatorForm` along a linear map `φ : K₁.L →ₗ[ℝ] K₂.L`
matches `OnsagerFormPairing.pushforward`. -/
theorem onsager_pairing_pullbackActionForm
    {K₁ K₂ : LieActionLane ℝ A} (φ : K₁.L →ₗ[ℝ] K₂.L) (n : ℕ)
    (P : OnsagerFormPairing K₁.L A n)
    (ω η : ActionOperatorForm K₂ n) :
    (P.pushforward φ).totalGenerator ω η =
      P.totalGenerator (pullbackActionForm φ n ω) (pullbackActionForm φ n η) :=
  rfl

end ActionLaneSpecialization

section DerivationLaneSpecialization

variable {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

/-- Master Onsager–Casimir reciprocity specialized to `DerivationOperatorForm K n`. -/
theorem onsager_pairing_derivationForm_reciprocity
    (K : DerivationLieLane ℝ A) {n : ℕ}
    (PP : ParityOnsagerFormPairing K.L A n)
    (ω η : DerivationOperatorForm K n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_general_form_reciprocity PP ω η

/-- Onsager–Casimir reciprocity on CE exterior derivatives `d_n ω`, `d_n η` in degree `n + 1`. -/
theorem onsager_pairing_ceExteriorDerivative_reciprocity
    (K : DerivationLieLane ℝ A) (n : ℕ)
    (PP : ParityOnsagerFormPairing K.L A (n + 1))
    (ω η : DerivationOperatorForm K n) :
    PP.totalGenerator
        (PP.T.op (ceExteriorDerivative K n ω))
        (PP.T.op (ceExteriorDerivative K n η)) =
      PP.totalGenerator (ceExteriorDerivative K n η) (ceExteriorDerivative K n ω) :=
  onsager_pairing_general_form_reciprocity PP
    (ceExteriorDerivative K n ω) (ceExteriorDerivative K n η)

/-- Onsager–Casimir reciprocity on graded wedge products `ω₁ ∧ η₁`, `ω₂ ∧ η₂` in degree `p + q`. -/
theorem onsager_pairing_ceWedge_reciprocity
    (K : DerivationLieLane ℝ A) {p q : ℕ}
    (PP : ParityOnsagerFormPairing K.L A (p + q))
    (ω₁ : DerivationOperatorForm K p) (η₁ : DerivationOperatorForm K q)
    (ω₂ : DerivationOperatorForm K p) (η₂ : DerivationOperatorForm K q) :
    PP.totalGenerator (PP.T.op (ceWedge K ω₁ η₁)) (PP.T.op (ceWedge K ω₂ η₂)) =
      PP.totalGenerator (ceWedge K ω₂ η₂) (ceWedge K ω₁ η₁) :=
  onsager_pairing_general_form_reciprocity PP (ceWedge K ω₁ η₁) (ceWedge K ω₂ η₂)

/-- Onsager–Casimir reciprocity on noncommutative gauge curvatures `F(Γ₁)`, `F(Γ₂)` in degree `2`. -/
theorem onsager_pairing_ceCurvature_reciprocity
    {A' : Type*} [Ring A'] [Algebra ℝ A']
    (K : DerivationLieLane ℝ A')
    (PP : ParityOnsagerFormPairing K.L A' 2)
    (Γ₁ Γ₂ : DerivationOperatorForm K 1) :
    PP.totalGenerator (PP.T.op (ceCurvature K Γ₁)) (PP.T.op (ceCurvature K Γ₂)) =
      PP.totalGenerator (ceCurvature K Γ₂) (ceCurvature K Γ₁) :=
  onsager_pairing_general_form_reciprocity PP (ceCurvature K Γ₁) (ceCurvature K Γ₂)

/-- Pullback along `act.rangeRestrict` from the faithful range lane to a possibly
non-faithful `L →ₗ⁅ℝ⁆ NonAssocDerivation.derivations ℝ A` preserves the Onsager pairing. -/
theorem onsager_pairing_pullbackRangeForm
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (act : L →ₗ⁅ℝ⁆ NonAssocDerivation.derivations ℝ A) (n : ℕ)
    (P : OnsagerFormPairing (toLieActionLaneFromHom act).L A n)
    (ω η : DerivationOperatorForm (rangeDerivationLieLane act) n) :
    (P.pushforward (act.rangeRestrict : L →ₗ[ℝ] act.range)).totalGenerator ω η =
      P.totalGenerator (pullbackRangeForm act n ω) (pullbackRangeForm act n η) :=
  rfl

private theorem ceExteriorDerivative_zero_eval_apply
    (K : DerivationLieLane ℝ A) (a : A) (x : K.L) :
    ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![x] = K.operatorAction x a :=
  actionExteriorDerivative_zero_apply K.toLieActionLane (zeroFormAlternatingEquiv K a) ![x]

/-- Pull an `OnsagerCasimirSystem A` back to the derivation Lie algebra `K.L`
via `x ↦ d₀(a)(x) = K.operatorAction x a`, generalizing finite Gibbs
`CEBKMOnsagerSystem` beyond `FiniteOperatorAlgebra n`. -/
def inducedDerivationLaneOnsagerSystem
    (S : OnsagerCasimirSystem A) (K : DerivationLieLane ℝ A) (a : A) :
    OnsagerCasimirSystem K.L :=
  let evalD : K.L →ₗ[ℝ] A :=
    { toFun := fun x => ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![x]
      map_add' := fun x y => by
        rw [ceExteriorDerivative_zero_eval_apply, ceExteriorDerivative_zero_eval_apply,
          ceExteriorDerivative_zero_eval_apply, map_add, LinearMap.add_apply]
      map_smul' := fun c x => by
        rw [ceExteriorDerivative_zero_eval_apply, ceExteriorDerivative_zero_eval_apply,
          map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  { dissipative := S.dissipative.compl₁₂ evalD evalD
    reversible := S.reversible.compl₁₂ evalD evalD
    dissipative_symm := fun x y => S.dissipative_symm _ _
    reversible_skew := fun x y => S.reversible_skew _ _
    dissipative_nonneg := fun x => S.dissipative_nonneg _ }

@[simp]
theorem inducedDerivationLaneOnsagerSystem_totalGenerator
    (S : OnsagerCasimirSystem A) (K : DerivationLieLane ℝ A) (a : A) (x y : K.L) :
    (inducedDerivationLaneOnsagerSystem S K a).totalGenerator x y =
      S.totalGenerator (K.operatorAction x a) (K.operatorAction y a) := by
  change S.totalGenerator (ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![x])
      (ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K a) ![y]) =
    S.totalGenerator (K.operatorAction x a) (K.operatorAction y a)
  rw [ceExteriorDerivative_zero_eval_apply, ceExteriorDerivative_zero_eval_apply]

end DerivationLaneSpecialization

section OpFormAndExteriorAlgebraCompatibility

variable {V W A : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [Ring A] [Algebra ℝ A]

/-- Master Onsager–Casimir reciprocity specialized to `OpForm ℝ V A n`. -/
theorem onsager_pairing_opForm_reciprocity
    {n : ℕ} (PP : ParityOnsagerFormPairing V A n) (ω η : OpForm ℝ V A n) :
    PP.totalGenerator (PP.T.op ω) (PP.T.op η) = PP.totalGenerator η ω :=
  onsager_pairing_general_form_reciprocity PP ω η

/-- Onsager–Casimir reciprocity on `opWedge` products in degree `p + q`. -/
theorem onsager_pairing_opWedge_reciprocity
    {p q : ℕ} (PP : ParityOnsagerFormPairing V A (p + q))
    (ω₁ : OpForm ℝ V A p) (η₁ : OpForm ℝ V A q)
    (ω₂ : OpForm ℝ V A p) (η₂ : OpForm ℝ V A q) :
    PP.totalGenerator (PP.T.op (opWedge ω₁ η₁)) (PP.T.op (opWedge ω₂ η₂)) =
      PP.totalGenerator (opWedge ω₂ η₂) (opWedge ω₁ η₁) :=
  onsager_pairing_general_form_reciprocity PP (opWedge ω₁ η₁) (opWedge ω₂ η₂)

/-- `OnsagerFormPairing.pushforward` agrees with `OperatorExteriorAlgebraGeneral.pullbackN`. -/
theorem onsager_pairing_pullbackN_eq
    {n : ℕ} (ϕ : W →ₗ[ℝ] V) (P : OnsagerFormPairing W A n)
    (ω η : OpForm ℝ V A n) :
    (P.pushforward ϕ).totalGenerator ω η =
      P.totalGenerator (pullbackN n ϕ ω) (pullbackN n ϕ η) :=
  rfl

/-- Backward compatibility: degree-1 `dissipative1Form` equals
`(OnsagerFormPairing.ofFrame S (fun _ => u)).dissipative` via `op1FormEquivOpForm`. -/
theorem dissipative1Form_eq_onsagerFormPairing
    (S : OnsagerCasimirSystem A) (α β : Op1Form ℝ V A) (u : V) :
    dissipative1Form S α β u u =
      (OnsagerFormPairing.ofFrame S (fun _ : Fin 1 => u)).dissipative
        (op1FormEquivOpForm α) (op1FormEquivOpForm β) :=
  rfl

/-- Backward compatibility: degree-1 `reversible1Form` equals
`(OnsagerFormPairing.ofFrame S (fun _ => u)).reversible` via `op1FormEquivOpForm`. -/
theorem reversible1Form_eq_onsagerFormPairing
    (S : OnsagerCasimirSystem A) (α β : Op1Form ℝ V A) (u : V) :
    reversible1Form S α β u u =
      (OnsagerFormPairing.ofFrame S (fun _ : Fin 1 => u)).reversible
        (op1FormEquivOpForm α) (op1FormEquivOpForm β) :=
  rfl

/-- Backward compatibility: degree-1 `totalGenerator1Form` equals
`(OnsagerFormPairing.ofFrame S (fun _ => u)).totalGenerator` via `op1FormEquivOpForm`. -/
theorem totalGenerator1Form_eq_onsagerFormPairing
    (S : OnsagerCasimirSystem A) (α β : Op1Form ℝ V A) (u : V) :
    totalGenerator1Form S α β u u =
      (OnsagerFormPairing.ofFrame S (fun _ : Fin 1 => u)).totalGenerator
        (op1FormEquivOpForm α) (op1FormEquivOpForm β) :=
  rfl

/-- Degree-2 `ExteriorAlgebra.Op2Form` reciprocity via `op2FormEquivOpForm`. -/
theorem onsager_pairing_op2Form_reciprocity
    (PP : ParityOnsagerFormPairing V A 2) (ω η : Op2Form ℝ V A) :
    PP.totalGenerator
        (PP.T.op (op2FormEquivOpForm ω))
        (PP.T.op (op2FormEquivOpForm η)) =
      PP.totalGenerator (op2FormEquivOpForm η) (op2FormEquivOpForm ω) :=
  onsager_pairing_general_form_reciprocity PP (op2FormEquivOpForm ω) (op2FormEquivOpForm η)

/-- Reciprocity on `ExteriorAlgebra.wedge α β` via `op2FormEquivOpForm_wedge`. -/
theorem onsager_pairing_exteriorWedge_reciprocity
    (PP : ParityOnsagerFormPairing V A 2)
    (α₁ β₁ α₂ β₂ : Op1Form ℝ V A) :
    PP.totalGenerator
        (PP.T.op (opWedge (op1FormEquivOpForm α₁) (op1FormEquivOpForm β₁)))
        (PP.T.op (opWedge (op1FormEquivOpForm α₂) (op1FormEquivOpForm β₂))) =
      PP.totalGenerator
        (op2FormEquivOpForm (wedge α₂ β₂))
        (op2FormEquivOpForm (wedge α₁ β₁)) := by
  rw [op2FormEquivOpForm_wedge, op2FormEquivOpForm_wedge]
  exact onsager_pairing_opWedge_reciprocity PP
    (op1FormEquivOpForm α₁) (op1FormEquivOpForm β₁)
    (op1FormEquivOpForm α₂) (op1FormEquivOpForm β₂)

end OpFormAndExteriorAlgebraCompatibility

end CarrierSpecializations

/-! ## `ThermodynamicOperatorDerivation` Adapters into the Unified M1A Spine (F1.5) -/

section ThermodynamicDerivationSpine

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.General
open InfoGeometry.Thermo.SusceptibilityOnsagerStress

/-- Every `ThermodynamicOperatorDerivation Op` satisfies `NonAssocDerivation.IsLeibniz ℝ Op`. -/
theorem thermodynamicDerivation_isLeibniz
    {Op : Type*} [NonUnitalNonAssocRing Op] [Module ℝ Op]
    (D : ThermodynamicOperatorDerivation Op) :
    NonAssocDerivation.IsLeibniz ℝ Op D.toLinearMap :=
  D.map_mul_eq

section NonAssocRingAdapters

variable {Op : Type*} [NonUnitalNonAssocRing Op] [Module ℝ Op]
  [IsScalarTower ℝ Op Op] [SMulCommClass ℝ Op Op]

/-- Canonical equivalence between `ThermodynamicOperatorDerivation Op` and
`NonAssocDerivation.derivations ℝ Op` (with zero orphan instances on
`ThermodynamicOperatorDerivation`). -/
def thermodynamicDerivationEquivDerivations :
    ThermodynamicOperatorDerivation Op ≃ NonAssocDerivation.derivations ℝ Op where
  toFun D := ⟨D.toLinearMap, D.map_mul_eq⟩
  invFun D := ⟨(D : Module.End ℝ Op), D.property⟩
  left_inv D := by cases D; rfl
  right_inv D := by apply Subtype.ext; ext x; rfl

@[simp]
theorem thermodynamicDerivationEquivDerivations_apply
    (D : ThermodynamicOperatorDerivation Op) (x : Op) :
    ((thermodynamicDerivationEquivDerivations D : NonAssocDerivation.derivations ℝ Op) :
      Module.End ℝ Op) x = D x :=
  rfl

@[simp]
theorem thermodynamicDerivationEquivDerivations_symm_apply
    (D : NonAssocDerivation.derivations ℝ Op) (x : Op) :
    thermodynamicDerivationEquivDerivations.symm D x = (D : Module.End ℝ Op) x :=
  rfl

/-- Commutator on `ThermodynamicOperatorDerivation Op` inherited from
`NonAssocDerivation.derivations ℝ Op`. -/
def thermodynamicDerivationCommutator
    (D E : ThermodynamicOperatorDerivation Op) :
    ThermodynamicOperatorDerivation Op :=
  thermodynamicDerivationEquivDerivations.symm
    ⁅thermodynamicDerivationEquivDerivations D,
      thermodynamicDerivationEquivDerivations E⁆

theorem thermodynamicDerivationEquivDerivations_commutator
    (D E : ThermodynamicOperatorDerivation Op) :
    thermodynamicDerivationEquivDerivations (thermodynamicDerivationCommutator D E) =
      ⁅thermodynamicDerivationEquivDerivations D,
        thermodynamicDerivationEquivDerivations E⁆ := by
  apply Subtype.ext
  ext x
  rfl

/-- Faithful `DerivationLieLane ℝ Op` on the Lie subalgebra generated by a single
`ThermodynamicOperatorDerivation D`. -/
def thermodynamicDerivationSpanLane (D : ThermodynamicOperatorDerivation Op) :
    DerivationLieLane ℝ Op :=
  lieSubalgebraLane (LieSubalgebra.lieSpan ℝ (NonAssocDerivation.derivations ℝ Op)
    {thermodynamicDerivationEquivDerivations D})

/-- One-generator abelian `LieActionLane ℝ Op` attached to a single
`ThermodynamicOperatorDerivation D`. -/
def thermodynamicDerivationActionLane (D : ThermodynamicOperatorDerivation Op) :
    LieActionLane ℝ Op :=
  letI : LieRing ℝ :=
    { bracket := fun _ _ => 0
      add_lie := fun _ _ _ => (add_zero 0).symm
      lie_add := fun _ _ _ => (add_zero 0).symm
      lie_self := fun _ => rfl
      leibniz_lie := fun _ _ _ => (add_zero 0).symm }
  letI : LieAlgebra ℝ ℝ :=
    { lie_smul := fun _ _ _ => (smul_zero _).symm }
  { L := ℝ
    lieRing := ‹_›
    lieAlgebra := ‹_›
    act :=
      { toFun := fun r => r • D.toLinearMap
        map_add' := fun r s => add_smul r s _
        map_smul' := fun r s => smul_eq_mul r s ▸ mul_smul r s _
        map_lie' := fun {r s} => by
          ext a
          change (0 : ℝ) • D a = r • D (s • D a) - s • D (r • D a)
          rw [zero_smul, D.map_smul, D.map_smul, smul_smul, smul_smul, mul_comm r s, sub_self] } }

theorem thermodynamicDerivationActionLane_isLeibniz
    (D : ThermodynamicOperatorDerivation Op) :
    IsLeibnizAction (thermodynamicDerivationActionLane D) := by
  intro r x y
  let r' : ℝ := r
  change r' • D (x * y) = (r' • D x) * y + x * (r' • D y)
  rw [D.map_mul, smul_add, smul_mul_assoc, mul_smul_comm]

section FamilySpine

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Lift a Lie-bracketed family `L → ThermodynamicOperatorDerivation Op` (without
requiring faithfulness) into `L →ₗ⁅ℝ⁆ NonAssocDerivation.derivations ℝ Op`. -/
def thermodynamicFamilyLieHom
    (D : L → ThermodynamicOperatorDerivation Op)
    (hadd : ∀ x y a, D (x + y) a = D x a + D y a)
    (hsmul : ∀ (r : ℝ) x a, D (r • x) a = r • D x a)
    (hlie : ∀ x y a, D ⁅x, y⁆ a = D x (D y a) - D y (D x a)) :
    L →ₗ⁅ℝ⁆ NonAssocDerivation.derivations ℝ Op where
  toFun x := thermodynamicDerivationEquivDerivations (D x)
  map_add' x y := Subtype.ext (LinearMap.ext (hadd x y))
  map_smul' r x := Subtype.ext (LinearMap.ext (hsmul r x))
  map_lie' {x y} := Subtype.ext (LinearMap.ext (hlie x y))

/-- Tier 1 faithfulness-free `LieActionLane ℝ Op` for a `ThermodynamicOperatorDerivation`
family. -/
def thermodynamicFamilyLieActionLane
    (D : L → ThermodynamicOperatorDerivation Op)
    (hadd : ∀ x y a, D (x + y) a = D x a + D y a)
    (hsmul : ∀ (r : ℝ) x a, D (r • x) a = r • D x a)
    (hlie : ∀ x y a, D ⁅x, y⁆ a = D x (D y a) - D y (D x a)) :
    LieActionLane ℝ Op :=
  toLieActionLaneFromHom (thermodynamicFamilyLieHom D hadd hsmul hlie)

theorem thermodynamicFamilyLieActionLane_isLeibniz
    (D : L → ThermodynamicOperatorDerivation Op)
    (hadd : ∀ x y a, D (x + y) a = D x a + D y a)
    (hsmul : ∀ (r : ℝ) x a, D (r • x) a = r • D x a)
    (hlie : ∀ x y a, D ⁅x, y⁆ a = D x (D y a) - D y (D x a)) :
    IsLeibnizAction (thermodynamicFamilyLieActionLane D hadd hsmul hlie) :=
  toLieActionLaneFromHom_isLeibniz (thermodynamicFamilyLieHom D hadd hsmul hlie)

/-- Tier 2 faithful range `DerivationLieLane ℝ Op` for a `ThermodynamicOperatorDerivation`
family. -/
def thermodynamicFamilyRangeLane
    (D : L → ThermodynamicOperatorDerivation Op)
    (hadd : ∀ x y a, D (x + y) a = D x a + D y a)
    (hsmul : ∀ (r : ℝ) x a, D (r • x) a = r • D x a)
    (hlie : ∀ x y a, D ⁅x, y⁆ a = D x (D y a) - D y (D x a)) :
    DerivationLieLane ℝ Op :=
  rangeDerivationLieLane (thermodynamicFamilyLieHom D hadd hsmul hlie)

/-- Tier 2 faithful quotient `DerivationLieLane ℝ Op` for a `ThermodynamicOperatorDerivation`
family. -/
def thermodynamicFamilyQuotientLane
    (D : L → ThermodynamicOperatorDerivation Op)
    (hadd : ∀ x y a, D (x + y) a = D x a + D y a)
    (hsmul : ∀ (r : ℝ) x a, D (r • x) a = r • D x a)
    (hlie : ∀ x y a, D ⁅x, y⁆ a = D x (D y a) - D y (D x a)) :
    DerivationLieLane ℝ Op :=
  quotientDerivationLieLane (thermodynamicFamilyLieHom D hadd hsmul hlie)

/-- Equivariant identification between quotient and range lanes of a
`ThermodynamicOperatorDerivation` family. -/
def thermodynamicFamilyQuotientEquivRange
    (D : L → ThermodynamicOperatorDerivation Op)
    (hadd : ∀ x y a, D (x + y) a = D x a + D y a)
    (hsmul : ∀ (r : ℝ) x a, D (r • x) a = r • D x a)
    (hlie : ∀ x y a, D ⁅x, y⁆ a = D x (D y a) - D y (D x a)) :
    DerivationLaneEquiv
      (thermodynamicFamilyQuotientLane D hadd hsmul hlie)
      (thermodynamicFamilyRangeLane D hadd hsmul hlie) :=
  quotientDerivationLieLaneEquivRange (thermodynamicFamilyLieHom D hadd hsmul hlie)

theorem thermodynamicFamily_pullbackRangeForm_injective
    (D : L → ThermodynamicOperatorDerivation Op)
    (hadd : ∀ x y a, D (x + y) a = D x a + D y a)
    (hsmul : ∀ (r : ℝ) x a, D (r • x) a = r • D x a)
    (hlie : ∀ x y a, D ⁅x, y⁆ a = D x (D y a) - D y (D x a))
    (n : ℕ) :
    Function.Injective (pullbackRangeForm (thermodynamicFamilyLieHom D hadd hsmul hlie) n) :=
  pullbackRangeForm_injective (thermodynamicFamilyLieHom D hadd hsmul hlie) n

theorem thermodynamicFamily_pullbackRangeForm_d
    (D : L → ThermodynamicOperatorDerivation Op)
    (hadd : ∀ x y a, D (x + y) a = D x a + D y a)
    (hsmul : ∀ (r : ℝ) x a, D (r • x) a = r • D x a)
    (hlie : ∀ x y a, D ⁅x, y⁆ a = D x (D y a) - D y (D x a))
    (n : ℕ)
    (ω : ActionOperatorForm (thermodynamicFamilyRangeLane D hadd hsmul hlie).toLieActionLane n) :
    actionExteriorDerivative (thermodynamicFamilyLieActionLane D hadd hsmul hlie) n
        (pullbackRangeForm (thermodynamicFamilyLieHom D hadd hsmul hlie) n ω) =
      pullbackRangeForm (thermodynamicFamilyLieHom D hadd hsmul hlie) (n + 1)
        (actionExteriorDerivative
          (thermodynamicFamilyRangeLane D hadd hsmul hlie).toLieActionLane n ω) :=
  pullbackRangeForm_actionExteriorDerivative (thermodynamicFamilyLieHom D hadd hsmul hlie) n ω

end FamilySpine

/-- Reverse spine adapter: extract a `ThermodynamicOperatorDerivation Op` from any
generator `x : K.L` of a `LieActionLane ℝ Op` satisfying `IsLeibnizAction K`. -/
def thermodynamicDerivationOfLieAction
    (K : LieActionLane ℝ Op) (hK : IsLeibnizAction K) (x : K.L) :
    ThermodynamicOperatorDerivation Op :=
  thermodynamicDerivationEquivDerivations.symm (lieActionToDerivationHom K hK x)

/-- Reverse spine adapter: extract a `ThermodynamicOperatorDerivation Op` from any
generator `x : K.L` of a `DerivationLieLane ℝ Op`. -/
def thermodynamicDerivationOfDerivationLane
    (K : DerivationLieLane ℝ Op) (x : K.L) :
    ThermodynamicOperatorDerivation Op :=
  thermodynamicDerivationEquivDerivations.symm (K.act x)

theorem thermodynamicDerivationEquivDerivations_ofLieAction
    (K : LieActionLane ℝ Op) (hK : IsLeibnizAction K) (x : K.L) :
    thermodynamicDerivationEquivDerivations (thermodynamicDerivationOfLieAction K hK x) =
      lieActionToDerivationHom K hK x :=
  rfl

theorem thermodynamicDerivation_eval_fullDerivationLieLane
    (D : ThermodynamicOperatorDerivation Op) (a : Op) :
    (fullDerivationLieLane ℝ Op).operatorAction
        (thermodynamicDerivationEquivDerivations D) a = D a :=
  rfl

end NonAssocRingAdapters

section FormDerivationCompatibility

variable {Op : Type*} [Ring Op] [Module ℝ Op]

/-- Canonical equivalence between `FormDerivation ℝ Op` and
`ThermodynamicOperatorDerivation Op`. -/
def formDerivationEquivThermodynamic :
    FormDerivation ℝ Op ≃ ThermodynamicOperatorDerivation Op where
  toFun D := ⟨D.toLinearMap, D.leibniz'⟩
  invFun D :=
    { toFun := D.toLinearMap
      map_add' := D.toLinearMap.map_add
      map_smul' := D.toLinearMap.map_smul
      leibniz' := D.map_mul_eq }
  left_inv D := by ext x; rfl
  right_inv D := by cases D; rfl

@[simp]
theorem formDerivationEquivThermodynamic_apply (D : FormDerivation ℝ Op) (x : Op) :
    formDerivationEquivThermodynamic D x = D x :=
  rfl

@[simp]
theorem formDerivationEquivThermodynamic_symm_apply
    (D : ThermodynamicOperatorDerivation Op) (x : Op) :
    formDerivationEquivThermodynamic.symm D x = D x :=
  rfl

theorem derivN_formDerivationEquivThermodynamic_opWedge
    [IsScalarTower ℝ Op Op] [SMulCommClass ℝ Op Op]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : ThermodynamicOperatorDerivation Op) {p q : ℕ}
    (ω : OpForm ℝ V Op p) (η : OpForm ℝ V Op q) :
    derivN (p + q) (formDerivationEquivThermodynamic.symm D) (opWedge ω η) =
      opWedge (derivN p (formDerivationEquivThermodynamic.symm D) ω) η +
        opWedge ω (derivN q (formDerivationEquivThermodynamic.symm D) η) :=
  derivN_opWedge (formDerivationEquivThermodynamic.symm D) p q ω η

theorem derivN_formDerivationEquivThermodynamic_d
    (K : LieActionLane ℝ Op) (D : ThermodynamicOperatorDerivation Op)
    (hDK : ∀ (x : K.L) (a : Op), D (K.operatorAction x a) = K.operatorAction x (D a))
    (n : ℕ) (ω : OpForm ℝ K.L Op n) :
    derivN (n + 1) (formDerivationEquivThermodynamic.symm D) (opExteriorDerivative K n ω) =
      opExteriorDerivative K n (derivN n (formDerivationEquivThermodynamic.symm D) ω) :=
  derivN_opExteriorDerivative K (formDerivationEquivThermodynamic.symm D) hDK n ω

end FormDerivationCompatibility

end ThermodynamicDerivationSpine

end InfoGeometry.Thermo.OnsagerFormsBridge

end noncomputable section
