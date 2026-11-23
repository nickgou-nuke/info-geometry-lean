/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import InfoGeometry.Arithmetic.AlpogeDeligneFrobeniusBoundBridge

/-!
# InfoGeometry.Arithmetic.ElladicDeligneWeightsWeakLefschetzBridge

Unifies three structural layers around Deligne's Frobenius bounds:

1. **Mathlib-Native `ℓ`-adic Cohomology Pullback & Endomorphism Action**:
   Imports `Mathlib.AlgebraicGeometry.Sites.ElladicCohomology` directly (`X.ellAdicSheaf ℓ`,
   `X.EllAdicCohomology ℓ n`), constructs functorial sheaf-endomorphism actions
   `ellAdicSheafMapH` and contravariant `Ext` pullbacks `ellAdicExtPullback` on `X.ProEt`
   for **all** degrees `n : ℕ`, constructs small pro-étale site base change
   `proEtBaseChange f : Y.ProEt ⥤ X.ProEt`, and constructs contravariant scheme-morphism
   pullback `ellAdicH0Pullback f` together with `CharP` affine Frobenius
   `schemeFrobenius` / `ellAdicSchemeFrobeniusH0` on `H⁰(X, ℤ_[ℓ])`.
2. **Scalar Deligne-Weight and Purity Algebra**:
   Formalizes `IsPureOfWeight w q α` (`‖α‖ = q ^ (w / 2)`) and `HasWeightAtMost w q α`,
   proves weight additivity under tensor products (`w₁ + w₂`), dual negation (`-w`),
   determinant / exterior power scaling (`k * w`), Tate-twist shift (`w - 2 * m`),
   Poincaré-duality-shaped scalar purity upgrade (via
   `AlpogeDeligneFrobeniusBoundBridge`) and the alternating-trace /
   rational-zeta partial-sum identity. These scalar statements do not identify
   geometric Frobenius eigenvalues or prove a Weil positivity criterion.
3. **Mathlib sheaf-cohomology consequences of abstract vanishing**:
   Derives injectivity and bijectivity of `Sheaf.H.map S.g k` from the exact sequence
   in Mathlib's `Sheaf.H.longSequence` and explicit subsingleton hypotheses. The abstract
   Artin-vanishing/Weak-Lefschetz equivalence is owned by
   `WeakLefschetzExcisionBridge`; this module does not construct a geometric weak
   Lefschetz map or prove Artin vanishing.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ElladicDeligneWeightsWeakLefschetzBridge

open CategoryTheory Limits AlgebraicGeometry
open scoped BigOperators
open InfoGeometry.Arithmetic.AlpogeDeligneFrobeniusBoundBridge

/-! ## 1. Mathlib-native `ℓ`-adic cohomology pullback & endomorphism action -/

section EllAdicAction

universe u

/-- Functorial action of any `ℓ`-adic sheaf endomorphism `φ : X.ellAdicSheaf ℓ ⟶ X.ellAdicSheaf ℓ`
on `X.EllAdicCohomology ℓ n` for every degree `n : ℕ`. -/
def ellAdicSheafMapH {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
    (φ : X.ellAdicSheaf ℓ ⟶ X.ellAdicSheaf ℓ) (n : ℕ) :
    X.EllAdicCohomology ℓ n →+ X.EllAdicCohomology ℓ n :=
  Sheaf.H.map ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).map φ) n

theorem ellAdicSheafMapH_id {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] (n : ℕ)
    (x : X.EllAdicCohomology ℓ n) :
    ellAdicSheafMapH (𝟙 (X.ellAdicSheaf ℓ)) n x = x := by
  let x' : ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ)).H n := x
  change Sheaf.H.map ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).map
    (𝟙 (X.ellAdicSheaf ℓ))) n x' = x'
  rw [CategoryTheory.Functor.map_id]
  exact Sheaf.H.map_id_apply x'

theorem ellAdicSheafMapH_comp {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
    (φ ψ : X.ellAdicSheaf ℓ ⟶ X.ellAdicSheaf ℓ) (n : ℕ)
    (x : X.EllAdicCohomology ℓ n) :
    ellAdicSheafMapH (φ ≫ ψ) n x = ellAdicSheafMapH ψ n (ellAdicSheafMapH φ n x) := by
  let x' : ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ)).H n := x
  change Sheaf.H.map ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).map (φ ≫ ψ)) n x' =
    Sheaf.H.map ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).map ψ) n
      (Sheaf.H.map ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).map φ) n x')
  rw [CategoryTheory.Functor.map_comp]
  exact Sheaf.H.map_comp_apply
    (f := (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).map φ)
    ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).map ψ) x'

/-- Terminal object `id_X : X ⟶ X` of the pro-étale site `X.ProEt`. -/
abbrev proEtTerminal (X : Scheme.{u}) : X.ProEt :=
  Scheme.ProEt.mk (𝟙 X)

/-- `proEtTerminal X` is terminal in `X.ProEt`. -/
def isTerminal_proEtTerminal (X : Scheme.{u}) : IsTerminal (proEtTerminal X) :=
  IsTerminal.ofUniqueHom
    (fun U => (Scheme.ProEt.forgetFullyFaithful X).preimage
      (Over.homMk U.hom (Category.comp_id _)))
    (fun U m => (Scheme.ProEt.forgetFullyFaithful X).map_injective (by
      rw [(Scheme.ProEt.forgetFullyFaithful X).map_preimage]
      ext
      exact (Category.comp_id _).symm.trans (Over.w ((Scheme.ProEt.forget X).map m))))

/-- Explicit `AddEquiv` identifying `H⁰(X, ℤ_[ℓ])` with `ULift C(X, ℤ_[ℓ])`. -/
def ellAdicH0Equiv (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] :
    X.EllAdicCohomology ℓ 0 ≃+ ULift.{u + 1} C(X, ℤ_[ℓ]) :=
  Sheaf.H.equiv₀ ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ))
    (isTerminal_proEtTerminal X)

/-- Contravariant functorial pullback `f^* : H⁰(Y, ℤ_[ℓ]) →+ H⁰(X, ℤ_[ℓ])`
induced by any scheme morphism `f : X ⟶ Y` via continuous precomposition on `C(·, ℤ_[ℓ])`. -/
def ellAdicH0Pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (ℓ : ℕ) [Fact ℓ.Prime] :
    Y.EllAdicCohomology ℓ 0 →+ X.EllAdicCohomology ℓ 0 :=
  ((ellAdicH0Equiv X ℓ).symm.toAddMonoidHom).comp <|
    ({ toFun := fun g => ULift.up (g.down.comp f.base.hom)
       map_zero' := by ext x; rfl
       map_add' := fun g₁ g₂ => by ext x; rfl } :
      ULift.{u + 1} C(Y, ℤ_[ℓ]) →+ ULift.{u + 1} C(X, ℤ_[ℓ])).comp
      (ellAdicH0Equiv Y ℓ).toAddMonoidHom

theorem ellAdicH0Pullback_id (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (α : X.EllAdicCohomology ℓ 0) :
    ellAdicH0Pullback (𝟙 X) ℓ α = α := by
  dsimp [ellAdicH0Pullback]
  have hcomp :
      ((ellAdicH0Equiv X ℓ α).down.comp (𝟙 X : X ⟶ X).base.hom) =
        (ellAdicH0Equiv X ℓ α).down := by
    ext x
    rfl
  change (ellAdicH0Equiv X ℓ).symm
    (ULift.up ((ellAdicH0Equiv X ℓ α).down.comp (𝟙 X : X ⟶ X).base.hom)) = α
  rw [hcomp]
  exact (ellAdicH0Equiv X ℓ).symm_apply_apply α

theorem ellAdicH0Pullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (ℓ : ℕ) [Fact ℓ.Prime] (α : Z.EllAdicCohomology ℓ 0) :
    ellAdicH0Pullback (f ≫ g) ℓ α = ellAdicH0Pullback f ℓ (ellAdicH0Pullback g ℓ α) := by
  dsimp [ellAdicH0Pullback]
  simp only [AddEquiv.apply_symm_apply]
  congr 1

/-- Frobenius (or any endomorphism `F : X ⟶ X`) pullback action on `H⁰(X, ℤ_[ℓ])`. -/
def ellAdicFrobeniusH0 {X : Scheme.{u}} (F : X ⟶ X) (ℓ : ℕ) [Fact ℓ.Prime] :
    X.EllAdicCohomology ℓ 0 →+ X.EllAdicCohomology ℓ 0 :=
  ellAdicH0Pullback F ℓ

/-- Small pro-étale site base-change functor `Y.ProEt ⥤ X.ProEt` along any
scheme morphism `f : X ⟶ Y` (`MorphismProperty.Over.pullback @WeaklyEtale ⊤ f`). -/
def proEtBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    [MorphismProperty.HasPullbacksAlong @WeaklyEtale f]
    [MorphismProperty.IsStableUnderBaseChangeAlong @WeaklyEtale f] : Y.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.pullback @WeaklyEtale ⊤ f

/-- Contravariant composition isomorphism for pro-étale base change:
`proEtBaseChange (f ≫ g) ≅ proEtBaseChange g ⋙ proEtBaseChange f`. -/
def proEtBaseChangeComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [MorphismProperty.HasPullbacksAlong @WeaklyEtale f]
    [MorphismProperty.HasPullbacksAlong @WeaklyEtale g]
    [MorphismProperty.HasPullbacksAlong @WeaklyEtale (f ≫ g)]
    [MorphismProperty.IsStableUnderBaseChangeAlong @WeaklyEtale f]
    [MorphismProperty.IsStableUnderBaseChangeAlong @WeaklyEtale g]
    [MorphismProperty.IsStableUnderBaseChangeAlong @WeaklyEtale (f ≫ g)] :
    proEtBaseChange (f ≫ g) ≅ proEtBaseChange g ⋙ proEtBaseChange f :=
  MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g (f ≫ g) rfl

/-- Contravariant `Ext` pullback map in degree `n` targeting the pro-étale
`ℓ`-adic sheaf `(sheafCompose _ AddCommGrpCat.uliftFunctor).obj (X.ellAdicSheaf ℓ)`. -/
def ellAdicExtPullback {X : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    {F₁ F₂ : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (α : F₁ ⟶ F₂) :
    Abelian.Ext F₂
      ((sheafCompose (Scheme.ProEt.topology X) AddCommGrpCat.uliftFunctor.{u + 1}).obj
        (X.ellAdicSheaf ℓ)) n →+
    Abelian.Ext F₁
      ((sheafCompose (Scheme.ProEt.topology X) AddCommGrpCat.uliftFunctor.{u + 1}).obj
        (X.ellAdicSheaf ℓ)) n :=
  (Abelian.Ext.mk₀ α).precomp _ (zero_add n)

@[simp] theorem ellAdicExtPullback_id {X : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (x : Abelian.Ext F
      ((sheafCompose (Scheme.ProEt.topology X) AddCommGrpCat.uliftFunctor.{u + 1}).obj
        (X.ellAdicSheaf ℓ)) n) :
    ellAdicExtPullback ℓ n (𝟙 F) x = x := by
  simp [ellAdicExtPullback]

theorem ellAdicExtPullback_comp {X : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    {F₁ F₂ F₃ : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃)
    (x : Abelian.Ext F₃
      ((sheafCompose (Scheme.ProEt.topology X) AddCommGrpCat.uliftFunctor.{u + 1}).obj
        (X.ellAdicSheaf ℓ)) n) :
    ellAdicExtPullback ℓ n (α ≫ β) x =
      ellAdicExtPullback ℓ n α (ellAdicExtPullback ℓ n β x) := by
  dsimp [ellAdicExtPullback]
  change ((Abelian.Ext.mk₀ (α ≫ β)).comp x (zero_add n)) =
    ((Abelian.Ext.mk₀ α).comp ((Abelian.Ext.mk₀ β).comp x (zero_add n)) (zero_add n))
  rw [← Abelian.Ext.mk₀_comp_mk₀]
  exact Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ α) (Abelian.Ext.mk₀ β) x rfl (zero_add n)
    (zero_add n)

/-- Arithmetic Frobenius scheme endomorphism on `Spec R` for any characteristic-`p`
commutative ring `R`. -/
def schemeFrobenius (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    Spec (.of R) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (frobenius R p))

/-- Frobenius pullback action on `H⁰(Spec R, ℤ_[ℓ])` induced by `schemeFrobenius R p`. -/
def ellAdicSchemeFrobeniusH0 (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    (Spec (.of R)).EllAdicCohomology ℓ 0 →+ (Spec (.of R)).EllAdicCohomology ℓ 0 :=
  ellAdicFrobeniusH0 (schemeFrobenius R p) ℓ

/-- Any scheme endomorphism acts trivially on this Mathlib `H⁰` carrier when the
underlying point space is subsingleton. The proof uses the owner equivalence
`H⁰(X, ℤ_[ℓ]) ≃+ C(X, ℤ_[ℓ])`: every self-map of a one-point space is the identity
on continuous functions. This is a concrete low-degree result for the defined
pro-étale coefficient sheaf; it says nothing about positive-degree Frobenius
eigenvalues. -/
theorem ellAdicH0Pullback_eq_id_of_subsingleton
    {X : Scheme.{u}} (hX : Subsingleton X) (F : X ⟶ X) (ℓ : ℕ) [Fact ℓ.Prime] :
    ellAdicH0Pullback F ℓ = AddMonoidHom.id (X.EllAdicCohomology ℓ 0) := by
  ext α
  dsimp [ellAdicH0Pullback]
  have hcomp : ((ellAdicH0Equiv X ℓ α).down.comp F.base.hom) =
      (ellAdicH0Equiv X ℓ α).down := by
    ext x
    have hx : F.base.hom x = x := hX.elim _ _
    simp [hx]
  change (ellAdicH0Equiv X ℓ).symm
    (ULift.up ((ellAdicH0Equiv X ℓ α).down.comp F.base.hom)) = α
  rw [hcomp]
  exact (ellAdicH0Equiv X ℓ).symm_apply_apply α

/-- On a connected scheme, pullback by any endomorphism acts identically on
Mathlib's continuous-function model of pro-étale `H⁰(X, ℤ_[ℓ])`. The key point
is topological: the coefficient space `ℤ_[ℓ]` is totally disconnected, so a
continuous map from connected `X` to it is constant. -/
theorem ellAdicH0Pullback_eq_id_of_connected
    {X : Scheme.{u}} [ConnectedSpace X] (F : X ⟶ X) (ℓ : ℕ) [Fact ℓ.Prime] :
    ellAdicH0Pullback F ℓ = AddMonoidHom.id (X.EllAdicCohomology ℓ 0) := by
  ext α
  dsimp [ellAdicH0Pullback]
  have hcomp : ((ellAdicH0Equiv X ℓ α).down.comp F.base.hom) =
      (ellAdicH0Equiv X ℓ α).down := by
    ext x
    exact TotallyDisconnectedSpace.eq_of_continuous
      ((ellAdicH0Equiv X ℓ α).down) (ellAdicH0Equiv X ℓ α).down.continuous
      (F.base.hom x) x
  change (ellAdicH0Equiv X ℓ).symm
    (ULift.up ((ellAdicH0Equiv X ℓ α).down.comp F.base.hom)) = α
  rw [hcomp]
  exact (ellAdicH0Equiv X ℓ).symm_apply_apply α

/-- Arithmetic Frobenius on the Mathlib pro-étale `H⁰` of a field spectrum is
the identity, since `Spec K` has one point. This result is a useful boundary
check: nontrivial Frobenius weights must come from positive-degree or
compactly-supported cohomology carriers, neither of which is constructed by the
current `EllAdicCohomology` specialization. -/
theorem ellAdicSchemeFrobeniusH0_eq_id_of_field
    (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ellAdicSchemeFrobeniusH0 K p ℓ =
      AddMonoidHom.id ((Spec (.of K)).EllAdicCohomology ℓ 0) := by
  change ellAdicH0Pullback (schemeFrobenius K p) ℓ = _
  have hSpec : Subsingleton (Spec (.of K)) := by
    change Subsingleton (PrimeSpectrum K)
    infer_instance
  exact ellAdicH0Pullback_eq_id_of_subsingleton
    hSpec
    (schemeFrobenius K p) ℓ

end EllAdicAction

/-! ## 2. Deligne weight / purity algebra & Frobenius–Zeta–Krein bridge -/

/-- Deligne purity of weight `w` relative to `q`: `‖α‖ = q ^ (w / 2)`. -/
def IsPureOfWeight (w q : ℝ) (α : ℂ) : Prop :=
  ‖α‖ = q ^ (w / 2)

/-- Deligne weight bound `≤ w` relative to `q`: `‖α‖ ≤ q ^ (w / 2)`. -/
def HasWeightAtMost (w q : ℝ) (α : ℂ) : Prop :=
  ‖α‖ ≤ q ^ (w / 2)

theorem isPureOfWeight_hasWeightAtMost {w q : ℝ} {α : ℂ} (h : IsPureOfWeight w q α) :
    HasWeightAtMost w q α :=
  le_of_eq h

/-- **Tensor-product weight additivity**: if `α` is pure of weight `w₁` and `β` is pure
of weight `w₂`, then `α * β` is pure of weight `w₁ + w₂`. -/
theorem isPureOfWeight_mul {w₁ w₂ q : ℝ} (hq : 0 < q) {α β : ℂ}
    (hα : IsPureOfWeight w₁ q α) (hβ : IsPureOfWeight w₂ q β) :
    IsPureOfWeight (w₁ + w₂) q (α * β) := by
  unfold IsPureOfWeight at *
  rw [norm_mul, hα, hβ, ← Real.rpow_add hq]
  congr 1
  ring

theorem hasWeightAtMost_mul {w₁ w₂ q : ℝ} (hq : 0 < q) {α β : ℂ}
    (hα : HasWeightAtMost w₁ q α) (hβ : HasWeightAtMost w₂ q β) :
    HasWeightAtMost (w₁ + w₂) q (α * β) := by
  unfold HasWeightAtMost at *
  rw [norm_mul]
  calc
    ‖α‖ * ‖β‖ ≤ q ^ (w₁ / 2) * q ^ (w₂ / 2) :=
      mul_le_mul hα hβ (norm_nonneg β) (Real.rpow_nonneg hq.le _)
    _ = q ^ ((w₁ + w₂) / 2) := by
      rw [← Real.rpow_add hq]
      congr 1
      ring

/-- **Dual weight negation**: if `α` is pure of weight `w`, then `α⁻¹` is pure of weight `-w`. -/
theorem isPureOfWeight_inv {w q : ℝ} (hq : 0 < q) {α : ℂ}
    (hα : IsPureOfWeight w q α) :
    IsPureOfWeight (-w) q α⁻¹ := by
  unfold IsPureOfWeight at *
  rw [norm_inv, hα, ← Real.rpow_neg hq.le]
  congr 1
  ring

/-- **Determinant / `k`-th exterior power weight scaling**: the product of `k` eigenvalues
each pure of weight `w` is pure of weight `k * w`. -/
theorem isPureOfWeight_prod {k : ℕ} {w q : ℝ} (hq : 0 < q) {α : Fin k → ℂ}
    (hα : ∀ i : Fin k, IsPureOfWeight w q (α i)) :
    IsPureOfWeight ((k : ℝ) * w) q (∏ i : Fin k, α i) := by
  unfold IsPureOfWeight at *
  rw [norm_prod]
  calc
    ∏ i : Fin k, ‖α i‖ = ∏ _i : Fin k, q ^ (w / 2) := Finset.prod_congr rfl fun i _ => hα i
    _ = (q ^ (w / 2)) ^ k := by simp
    _ = q ^ ((k : ℝ) * w / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
      congr 1
      ring

/-- **Tate twist `(m)`**: multiplying an eigenvalue of weight `w` by `q ^ (-m)` shifts
its weight to `w - 2 * m`. -/
theorem isPureOfWeight_tateTwist {w m q : ℝ} (hq : 0 < q) {α : ℂ}
    (hα : IsPureOfWeight w q α) :
    IsPureOfWeight (w - 2 * m) q (((q ^ (-m) : ℝ) : ℂ) * α) := by
  unfold IsPureOfWeight at *
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq.le _), hα,
    ← Real.rpow_add hq]
  congr 1
  ring

/-- **Poincaré-duality purity upgrade** (welding to `AlpogeDeligneFrobeniusBoundBridge`):
`HasWeightAtMost (w + i) q α` together with the dual bound
`HasWeightAtMost (-w + 2*d - i) q (q^d / α)` forces `IsPureOfWeight (w + i) q α`. -/
theorem isPureOfWeight_of_poincareDuality
    {q w i d : ℝ} (hq : 0 < q) {α : ℂ} (hα : α ≠ 0)
    (hupper : HasWeightAtMost (w + i) q α)
    (hdual : HasWeightAtMost (-w + 2 * d - i) q (((q ^ d : ℝ) : ℂ) / α)) :
    IsPureOfWeight (w + i) q α :=
  poincareDuality_purity_eq hq hα hupper hdual

/-- Alternating Frobenius trace `∑_i (-1)^i Tr(F^n | H^i)` for a finite graded family
of eigenvalues, matching the `n`-th coefficient of `T * d/dT log Z(X, T)`. -/
def alternatingFrobeniusTrace {r : ℕ} (deg : Fin r → ℕ) (eig : Fin r → ℂ) (n : ℕ) : ℂ :=
  ∑ j : Fin r, (-1 : ℂ) ^ (deg j) * (eig j) ^ n

/-- Splitting the alternating Frobenius trace into even-degree (denominator / pole)
and odd-degree (numerator / zero) contributions. -/
theorem alternatingFrobeniusTrace_even_sub_odd
    {r : ℕ} (deg : Fin r → ℕ) (eig : Fin r → ℂ) (n : ℕ) :
    alternatingFrobeniusTrace deg eig n =
      (∑ j ∈ Finset.univ.filter (fun j => Even (deg j)), (eig j) ^ n) -
      (∑ j ∈ Finset.univ.filter (fun j => ¬ Even (deg j)), (eig j) ^ n) := by
  classical
  unfold alternatingFrobeniusTrace
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => Even (deg j)),
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hev : Even (deg j) := (Finset.mem_filter.mp hj).2
    rw [hev.neg_one_pow, one_mul]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hodd : Odd (deg j) := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hj).2
    rw [hodd.neg_one_pow, neg_one_mul]

/-- Partial geometric trace identity `(∑ n < N, z ^ (n + 1)) * (1 - z) = z * (1 - z ^ N)`. -/
theorem geom_trace_partial_sum_mul_one_sub (z : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, z ^ (n + 1)) * (1 - z) = z * (1 - z ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    ring

/-- Closed rational-function formula for the first `N` positive trace powers:
`∑ n < N, z ^ (n + 1) = z * (1 - z ^ N) / (1 - z)` whenever `z ≠ 1`. -/
theorem geom_trace_partial_sum_eq_div {z : ℂ} (hz : z ≠ 1) (N : ℕ) :
    (∑ n ∈ Finset.range N, z ^ (n + 1)) = z * (1 - z ^ N) / (1 - z) := by
  have hnz : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  exact eq_div_of_mul_eq hnz (geom_trace_partial_sum_mul_one_sub z N)

/-- **Finite-Dimensional Alternating Trace ↔ Rational Zeta Partial-Sum Identity**:
the generating polynomial of `alternatingFrobeniusTrace deg eig (n + 1) * T ^ (n + 1)`
over `0 ≤ n < N` equals the alternating signed sum of rational logarithmic-derivative
terms `(-1)^(deg j) * (eig j * T) * (1 - (eig j * T) ^ N) / (1 - eig j * T)`. -/
theorem alternatingFrobeniusTrace_rationalZeta_partialSum
    {r : ℕ} (deg : Fin r → ℕ) (eig : Fin r → ℂ) (T : ℂ)
    (hT : ∀ j : Fin r, eig j * T ≠ 1) (N : ℕ) :
    (∑ n ∈ Finset.range N, alternatingFrobeniusTrace deg eig (n + 1) * T ^ (n + 1)) =
      ∑ j : Fin r, (-1 : ℂ) ^ (deg j) *
        ((eig j * T) * (1 - (eig j * T) ^ N) / (1 - eig j * T)) := by
  simp only [alternatingFrobeniusTrace, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc
    (∑ n ∈ Finset.range N, (-1 : ℂ) ^ (deg j) * (eig j) ^ (n + 1) * T ^ (n + 1))
        = ∑ n ∈ Finset.range N, (-1 : ℂ) ^ (deg j) * ((eig j * T) ^ (n + 1)) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [mul_assoc, ← mul_pow]
    _ = (-1 : ℂ) ^ (deg j) * ∑ n ∈ Finset.range N, (eig j * T) ^ (n + 1) := by
          rw [Finset.mul_sum]
    _ = (-1 : ℂ) ^ (deg j) * ((eig j * T) * (1 - (eig j * T) ^ N) / (1 - eig j * T)) := by
          rw [geom_trace_partial_sum_eq_div (hT j) N]

/-- Scalar purity for `q ^ s` is exactly the real-part equation. This concerns
the complex scalar power only; it does not identify a Frobenius spectrum or a
positivity criterion. -/
theorem isPureOfWeight_cpow_iff_re
    {q : ℝ} (hq : 1 < q) (w : ℝ) (s : ℂ) :
    IsPureOfWeight w q ((q : ℂ) ^ s) ↔ s.re = w / 2 := by
  unfold IsPureOfWeight
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hq) s]
  exact (Real.strictMono_rpow_of_base_gt_one hq).injective.eq_iff

section MathlibSheafCohomologyExcision

universe w' w''

/-- In Mathlib's `Sheaf.H.longSequence`, vanishing of `Sheaf.H S.X₁ k` implies
injectivity of `Sheaf.H.map S.g k : Sheaf.H S.X₂ k →+ Sheaf.H S.X₃ k`. -/
theorem sheafCohomology_map_g_injective_of_X1_subsingleton
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w'}] [HasExt.{w''} (Sheaf J AddCommGrpCat.{w'})]
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w'})} (hS : S.ShortExact) (k : ℕ)
    [Subsingleton (Sheaf.H S.X₁ k)] :
    Function.Injective (Sheaf.H.map S.g k) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x₁, hx₁⟩ := Sheaf.H.longSequence_exact₂ hS x hx
  have hx₁_zero : x₁ = 0 := Subsingleton.elim x₁ 0
  rw [← hx₁, hx₁_zero, map_zero]

/-- In Mathlib's `Sheaf.H.longSequence`, simultaneous vanishing of `Sheaf.H S.X₁ k`
and `Sheaf.H S.X₁ (k + 1)` forces `Sheaf.H.map S.g k` to be bijective. -/
theorem sheafCohomology_map_g_bijective_of_X1_subsingleton
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w'}] [HasExt.{w''} (Sheaf J AddCommGrpCat.{w'})]
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w'})} (hS : S.ShortExact) (k : ℕ)
    [Subsingleton (Sheaf.H S.X₁ k)] [Subsingleton (Sheaf.H S.X₁ (k + 1))] :
    Function.Bijective (Sheaf.H.map S.g k) := by
  refine ⟨sheafCohomology_map_g_injective_of_X1_subsingleton hS k, fun x₃ => ?_⟩
  have hδ : Sheaf.H.δ hS k (k + 1) rfl x₃ = 0 := Subsingleton.elim _ 0
  exact Sheaf.H.longSequence_exact₃ hS x₃ rfl hδ

end MathlibSheafCohomologyExcision

end InfoGeometry.Arithmetic.ElladicDeligneWeightsWeakLefschetzBridge
