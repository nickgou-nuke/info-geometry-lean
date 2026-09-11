/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Category.AlgCat.Limits
import InfoGeometry.Arithmetic.PrimeCyclotomicFieldMaps
import InfoGeometry.Arithmetic.GaloisIdeleTatePrimonSuperalgebraCapstone

/-!
# Profinite cyclotomic unit carrier

The carrier below is the explicit inverse-limit object of the finite unit
groups `(ZMod n)ˣ`.  It is intentionally only a carrier with compatibility;
no identification with an adelic group, topology, or Haar measure is claimed.
-/

namespace InfoGeometry.Arithmetic.ProfiniteCyclotomicUnitLimit

open scoped BigOperators
open Finset
open CategoryTheory Limits

/-! ### The divisibility index category -/

structure DivisibilityIndex where
  value : ℕ+

instance : LE DivisibilityIndex :=
  ⟨fun n m => (n.value : ℕ) ∣ (m.value : ℕ)⟩

instance : PartialOrder DivisibilityIndex where
  le_refl n := dvd_refl _
  le_trans a b c hab hbc := dvd_trans hab hbc
  le_antisymm a b hab hba := by
    cases a with
    | mk a =>
      cases b with
      | mk b =>
        congr 1
        apply Subtype.ext
        exact Nat.dvd_antisymm hab hba

theorem divisibilityIndex_le_iff {n m : DivisibilityIndex} :
    n ≤ m ↔ (n.value : ℕ) ∣ (m.value : ℕ) := Iff.rfl

theorem divisibilityIndex_nonempty : Nonempty DivisibilityIndex :=
  ⟨⟨⟨1, Nat.zero_lt_one⟩⟩⟩

noncomputable def cyclotomicUnitDiagram : DivisibilityIndexᵒᵖ ⥤ Type where
  obj i := (ZMod (i.unop.value : ℕ))ˣ
  map f := ZMod.unitsMap (CategoryTheory.leOfHom f.unop)
  map_id i := by
    funext x
    rw [ZMod.unitsMap_self]
    rfl
  map_comp f g := by
    funext x
    simpa [Function.comp_def] using congrArg (fun h => h x)
      (ZMod.unitsMap_comp (CategoryTheory.leOfHom g.unop)
        (CategoryTheory.leOfHom f.unop)).symm

/-! ### Categorical profinite unit limit

The inverse limit is kept as a categorical object.  No identification with a
topological completion, Haar measure, or an adelic group is asserted here.
-/

noncomputable abbrev cyclotomicUnitLimit : Type :=
  limit cyclotomicUnitDiagram

noncomputable def cyclotomicUnitLimitCone :
    Cone cyclotomicUnitDiagram :=
  limit.cone cyclotomicUnitDiagram

noncomputable def cyclotomicUnitLimitCone_isLimit :
    IsLimit cyclotomicUnitLimitCone :=
  limit.isLimit cyclotomicUnitDiagram

/-! ### Finite cyclotomic field stages -/

abbrev CyclotomicFieldStage (n : ℕ+) := CyclotomicField (n : ℕ) ℚ

noncomputable def fieldTransition {n m : ℕ+} (h : (n : ℕ) ∣ (m : ℕ)) :
    CyclotomicFieldStage n →ₐ[ℚ] CyclotomicFieldStage m :=
  cyclotomicFieldEmbedding n.pos m.pos h

theorem fieldTransition_zeta {n m : ℕ+} (h : (n : ℕ) ∣ (m : ℕ)) :
    fieldTransition h
        (IsCyclotomicExtension.zeta (n : ℕ) ℚ (CyclotomicFieldStage n)) =
      IsCyclotomicExtension.zeta (m : ℕ) ℚ (CyclotomicFieldStage m) ^ ((m : ℕ) / (n : ℕ)) := by
  exact cyclotomicFieldEmbedding_zeta n.pos m.pos h

theorem fieldTransition_self (n : ℕ+) :
    fieldTransition (dvd_refl (n : ℕ)) = AlgHom.id ℚ (CyclotomicFieldStage n) := by
  exact cyclotomicFieldEmbedding_self n.pos

theorem fieldTransition_comp
    {n m k : ℕ+} (hnm : (n : ℕ) ∣ (m : ℕ)) (hmk : (m : ℕ) ∣ (k : ℕ))
    (hnk : (n : ℕ) ∣ (k : ℕ))
    (hq : (k : ℕ) / (n : ℕ) = ((k : ℕ) / (m : ℕ)) * ((m : ℕ) / (n : ℕ))) :
    (fieldTransition hmk).comp (fieldTransition hnm) = fieldTransition hnk := by
  exact cyclotomicFieldEmbedding_comp n.pos m.pos k.pos hnm hmk hnk hq

theorem fieldTransition_comp_of_dvd
    {n m k : ℕ+} (hnm : (n : ℕ) ∣ (m : ℕ)) (hmk : (m : ℕ) ∣ (k : ℕ)) :
    (fieldTransition hmk).comp (fieldTransition hnm) =
      fieldTransition (dvd_trans hnm hmk) := by
  apply fieldTransition_comp hnm hmk (dvd_trans hnm hmk)
  exact (Nat.div_mul_div hmk hnm).symm

noncomputable def cyclotomicFieldDiagram : DivisibilityIndex ⥤ AlgCat ℚ where
  obj i := AlgCat.of ℚ (CyclotomicFieldStage i.value)
  map f := AlgCat.ofHom (fieldTransition (CategoryTheory.leOfHom f))
  map_id i := by
    apply AlgCat.hom_ext
    exact fieldTransition_self i.value
  map_comp f g := by
    apply AlgCat.hom_ext
    simpa [AlgCat.hom_comp] using (fieldTransition_comp_of_dvd
      (CategoryTheory.leOfHom f) (CategoryTheory.leOfHom g)).symm

noncomputable abbrev cyclotomicFieldLimit : AlgCat ℚ :=
  limit cyclotomicFieldDiagram

noncomputable def cyclotomicFieldLimitCone :
    Cone cyclotomicFieldDiagram :=
  limit.cone cyclotomicFieldDiagram

noncomputable def cyclotomicFieldLimitCone_isLimit :
    IsLimit cyclotomicFieldLimitCone :=
  limit.isLimit cyclotomicFieldDiagram

def Compatible (x : ∀ n : ℕ, (ZMod n)ˣ) : Prop :=
  ∀ {n m : ℕ} (h : n ∣ m), ZMod.unitsMap h (x m) = x n

def Carrier := {x : ∀ n : ℕ, (ZMod n)ˣ // Compatible x}

instance : One Carrier := ⟨⟨fun _ => 1, by
  intro n m h
  simp⟩⟩

instance : Mul Carrier := ⟨fun x y => ⟨fun n => x.1 n * y.1 n, by
  intro n m h
  simp [Compatible, x.2 h, y.2 h]⟩⟩

instance : Inv Carrier := ⟨fun x => ⟨fun n => (x.1 n)⁻¹, by
  intro n m h
  simp [Compatible, x.2 h]⟩⟩

instance : Group Carrier where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  one_mul x := by apply Subtype.ext; funext n; exact one_mul _
  mul_one x := by apply Subtype.ext; funext n; exact mul_one _
  mul_assoc x y z := by apply Subtype.ext; funext n; exact mul_assoc _ _ _
  inv_mul_cancel x := by apply Subtype.ext; funext n; exact inv_mul_cancel _

/-! A deliberate topological realization using discrete finite stages. -/

abbrev TopologicalCarrier := Carrier

instance unitStageTopology (n : ℕ) : TopologicalSpace ((ZMod n)ˣ) := ⊥

instance topologicalCarrierTopology : TopologicalSpace TopologicalCarrier :=
  TopologicalSpace.induced Subtype.val inferInstance

def coordinate (x : Carrier) (n : ℕ) : (ZMod n)ˣ := x.1 n

theorem continuous_coordinate (n : ℕ) :
    Continuous (coordinate · n : TopologicalCarrier → (ZMod n)ˣ) := by
  exact (continuous_apply n).comp continuous_induced_dom


theorem coordinate_compatible (x : Carrier) {n m : ℕ} (h : n ∣ m) :
    ZMod.unitsMap h (coordinate x m) = coordinate x n :=
  x.2 h

theorem transition_identity {n : ℕ} (x : (ZMod n)ˣ) :
    ZMod.unitsMap (dvd_refl n) x = x := by
  rw [ZMod.unitsMap_self]
  rfl

theorem transition_composition {n m k : ℕ}
    (hnm : n ∣ m) (hmk : m ∣ k) (x : (ZMod k)ˣ) :
    ZMod.unitsMap hnm (ZMod.unitsMap hmk x) = ZMod.unitsMap (dvd_trans hnm hmk) x := by
  exact congrArg (fun f => f x) (ZMod.unitsMap_comp hnm hmk)

theorem transition_surjective {n m : ℕ} (h : n ∣ m) [NeZero m] :
    Function.Surjective (ZMod.unitsMap h) := by
  exact ZMod.unitsMap_surjective h

theorem transition_fiber_card_eq {n m : ℕ} (h : n ∣ m) [NeZero m]
    (u v : (ZMod m)ˣ) :
    #{x : (ZMod m)ˣ | ZMod.unitsMap h x = ZMod.unitsMap h u} =
      #{x : (ZMod m)ˣ | ZMod.unitsMap h x = ZMod.unitsMap h v} := by
  exact MonoidHom.card_fiber_eq_of_mem_range
    (ZMod.unitsMap h) ⟨u, rfl⟩ ⟨v, rfl⟩

noncomputable def transition_fiber_equiv_kernel {n m : ℕ} (h : n ∣ m) [NeZero m]
    (u : (ZMod m)ˣ) :
    {x : (ZMod m)ˣ | ZMod.unitsMap h x = ZMod.unitsMap h u} ≃
      (ZMod.unitsMap h).ker := by
  exact MonoidHom.fiberEquivKer (ZMod.unitsMap h) u

theorem transition_fiber_card_eq_kernel {n m : ℕ} (h : n ∣ m) [NeZero m]
    (u : (ZMod m)ˣ) :
    Fintype.card {x : (ZMod m)ˣ | ZMod.unitsMap h x = ZMod.unitsMap h u} =
      Fintype.card (ZMod.unitsMap h).ker := by
  exact Fintype.card_congr (transition_fiber_equiv_kernel h u)

theorem carrier_ext {x y : Carrier}
    (h : ∀ n : ℕ, coordinate x n = coordinate y n) : x = y := by
  apply Subtype.ext
  funext n
  exact h n

@[simp] theorem coordinate_one (n : ℕ) :
    coordinate (1 : Carrier) n = 1 := rfl

@[simp] theorem coordinate_mul (x y : Carrier) (n : ℕ) :
    coordinate (x * y) n = coordinate x n * coordinate y n := rfl

@[simp] theorem coordinate_inv (x : Carrier) (n : ℕ) :
    coordinate x⁻¹ n = (coordinate x n)⁻¹ := rfl

theorem compatible_family_readback (x : Carrier) (n m : ℕ) (h : n ∣ m) :
    ZMod.unitsMap h (coordinate x m) = coordinate x n :=
  coordinate_compatible x h

/-! ### Finite Haar analogue: normalized counting average -/

noncomputable def normalizedStageAverage (n : ℕ+) (f : (ZMod (n : ℕ))ˣ → ℝ) : ℝ :=
  (Fintype.card (ZMod n)ˣ : ℝ)⁻¹ * ∑ x, f x

theorem normalizedStageAverage_const (n : ℕ+) (c : ℝ) :
    normalizedStageAverage n (fun _ : (ZMod (n : ℕ))ˣ => c) = c := by
  unfold normalizedStageAverage
  simp

theorem normalizedStageAverage_nonneg (n : ℕ+)
    (f : (ZMod (n : ℕ))ˣ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ normalizedStageAverage n f := by
  unfold normalizedStageAverage
  have hcard : 0 < (Fintype.card (ZMod (n : ℕ))ˣ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply mul_nonneg (inv_nonneg.mpr (le_of_lt hcard))
  exact Finset.sum_nonneg fun x _ => hf x

theorem normalizedStageAverage_add (n : ℕ+)
    (f g : (ZMod (n : ℕ))ˣ → ℝ) :
    normalizedStageAverage n (fun x => f x + g x) =
      normalizedStageAverage n f + normalizedStageAverage n g := by
  unfold normalizedStageAverage
  rw [Finset.sum_add_distrib]
  ring

theorem normalizedStageAverage_smul (n : ℕ+) (c : ℝ)
    (f : (ZMod (n : ℕ))ˣ → ℝ) :
    normalizedStageAverage n (fun x => c * f x) =
      c * normalizedStageAverage n f := by
  unfold normalizedStageAverage
  rw [← Finset.mul_sum]
  ring

structure StageHaarData (n : ℕ+) where
  integral : ((ZMod (n : ℕ))ˣ → ℝ) → ℝ
  integral_const : ∀ c, integral (fun _ => c) = c
  integral_add : ∀ f g, integral (fun x => f x + g x) = integral f + integral g
  integral_smul : ∀ c f, integral (fun x => c * f x) = c * integral f
  integral_nonneg : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ integral f

noncomputable def stageHaarData (n : ℕ+) : StageHaarData n where
  integral := normalizedStageAverage n
  integral_const := normalizedStageAverage_const n
  integral_add := normalizedStageAverage_add n
  integral_smul := normalizedStageAverage_smul n
  integral_nonneg := normalizedStageAverage_nonneg n

theorem stageHaarData_integral (n : ℕ+) (f : (ZMod (n : ℕ))ˣ → ℝ) :
    (stageHaarData n).integral f = normalizedStageAverage n f := rfl

theorem stageHaarData_normalized (n : ℕ+) (c : ℝ) :
    (stageHaarData n).integral (fun _ : (ZMod (n : ℕ))ˣ => c) = c := by
  exact (stageHaarData n).integral_const c

/-! ### Finite local Euler readout -/

noncomputable def finiteLocalEulerFactor (p : ℕ) (s : ℂ) : ℂ :=
  1 - (p : ℂ) ^ (-s)

noncomputable def finiteGlobalEulerDenominator (P : Finset ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ P, finiteLocalEulerFactor p s

noncomputable def finiteGlobalEulerProduct (P : Finset ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ P, (finiteLocalEulerFactor p s)⁻¹

theorem finiteGlobalEulerProduct_eq_inv_denominator
    (P : Finset ℕ) (s : ℂ) :
    finiteGlobalEulerProduct P s = (finiteGlobalEulerDenominator P s)⁻¹ := by
  unfold finiteGlobalEulerProduct finiteGlobalEulerDenominator
  rw [Finset.prod_inv_distrib]

theorem finiteGlobalEulerProduct_mul_denominator
    (P : Finset ℕ) (s : ℂ)
    (hP : ∀ p ∈ P, finiteLocalEulerFactor p s ≠ 0) :
    finiteGlobalEulerProduct P s * finiteGlobalEulerDenominator P s = 1 := by
  rw [finiteGlobalEulerProduct_eq_inv_denominator]
  exact inv_mul_cancel₀ (by
    unfold finiteGlobalEulerDenominator
    intro hzero
    rw [Finset.prod_eq_zero_iff] at hzero
    obtain ⟨p, hp, hfactor⟩ := hzero
    exact hP p hp hfactor)

/-! ### Finite commutative topological KMS model -/

structure FiniteTopologicalKMS (n : ℕ+) where
  beta : ℝ
  beta_gt_one : 1 < beta
  expectation : ((ZMod (n : ℕ))ˣ → ℝ) → ℝ
  expectation_one : expectation (fun _ => 1) = 1
  dynamics : ℝ → ((ZMod (n : ℕ))ˣ → ℝ) → ((ZMod (n : ℕ))ˣ → ℝ)
  dynamics_zero : ∀ f, dynamics 0 f = f
  kms : ∀ (t : ℝ) (f g),
    expectation (fun x => f x * dynamics t g x) =
      expectation (fun x => g x * dynamics t f x)

noncomputable def finiteHaarKMS (n : ℕ+) (beta : ℝ) (hbeta : 1 < beta) :
    FiniteTopologicalKMS n where
  beta := beta
  beta_gt_one := hbeta
  expectation := (stageHaarData n).integral
  expectation_one := by
    simpa using (stageHaarData n).integral_const 1
  dynamics := fun _ f => f
  dynamics_zero := by intro f; rfl
  kms := by
    intro t f g
    apply congrArg (stageHaarData n).integral
    funext x
    exact mul_comm _ _

theorem finiteHaarKMS_expectation_eq_stage_average
    (n : ℕ+) (beta : ℝ) (hbeta : 1 < beta)
    (f : (ZMod (n : ℕ))ˣ → ℝ) :
    (finiteHaarKMS n beta hbeta).expectation f = normalizedStageAverage n f := rfl

theorem finiteHaarKMS_kms_law
    (n : ℕ+) (beta : ℝ) (hbeta : 1 < beta) (t : ℝ)
    (f g : (ZMod (n : ℕ))ˣ → ℝ) :
    (finiteHaarKMS n beta hbeta).expectation
        (fun x => f x * (finiteHaarKMS n beta hbeta).dynamics t g x) =
      (finiteHaarKMS n beta hbeta).expectation
        (fun x => g x * (finiteHaarKMS n beta hbeta).dynamics t f x) := by
  exact (finiteHaarKMS n beta hbeta).kms t f g

noncomputable def normalizedFiniteAverage {α : Type*} [Fintype α]
    (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

theorem normalizedFiniteAverage_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) :
    normalizedFiniteAverage (fun x => f (e x)) =
      normalizedFiniteAverage f := by
  unfold normalizedFiniteAverage
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e (fun x => f (e x)) f (fun _ => rfl)

theorem normalizedFiniteAverage_const {α : Type*} [Fintype α] [Nonempty α]
    (c : ℝ) :
    normalizedFiniteAverage (fun _ : α => c) = c := by
  unfold normalizedFiniteAverage
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  field_simp [Fintype.card_ne_zero]

theorem normalizedFiniteAverage_add {α : Type*} [Fintype α]
    (f g : α → ℝ) :
    normalizedFiniteAverage (fun x => f x + g x) =
      normalizedFiniteAverage f + normalizedFiniteAverage g := by
  unfold normalizedFiniteAverage
  rw [Finset.sum_add_distrib]
  ring

theorem normalizedFiniteAverage_smul {α : Type*} [Fintype α]
    (c : ℝ) (f : α → ℝ) :
    normalizedFiniteAverage (fun x => c * f x) =
      c * normalizedFiniteAverage f := by
  unfold normalizedFiniteAverage
  calc
    (Fintype.card α : ℝ)⁻¹ * ∑ x, c * f x =
        ∑ x, (Fintype.card α : ℝ)⁻¹ * (c * f x) := by
          rw [Finset.mul_sum]
    _ =
        ∑ x, ((Fintype.card α : ℝ)⁻¹ * c) * f x := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = (Fintype.card α : ℝ)⁻¹ * c * ∑ x, f x := by
          rw [Finset.mul_sum]
    _ = c * ((Fintype.card α : ℝ)⁻¹ * ∑ x, f x) := by ring

/-! ### Supplied profinite Haar extension certificate -/

structure ProfiniteHaarExtensionData where
  integral : (Carrier → ℝ) → ℝ
  integral_const : ∀ c, integral (fun _ => c) = c
  integral_add : ∀ f g, integral (fun x => f x + g x) = integral f + integral g
  integral_smul : ∀ c f, integral (fun x => c * f x) = c * integral f
  integral_nonneg : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ integral f
  cylinder_readback : ∀ (n : ℕ+) (f : (ZMod (n : ℕ))ˣ → ℝ),
    integral (fun x => f (coordinate x n)) =
      normalizedStageAverage n f

theorem ProfiniteHaarExtensionData.cylinder_readback_eq
    (Haar : ProfiniteHaarExtensionData) (n : ℕ+)
    (f : (ZMod (n : ℕ))ˣ → ℝ) :
    Haar.integral (fun x => f (coordinate x n)) =
      normalizedStageAverage n f :=
  Haar.cylinder_readback n f

theorem ProfiniteHaarExtensionData.transition_cylinder_readback
    (Haar : ProfiniteHaarExtensionData) {n m : ℕ+} (h : (n : ℕ) ∣ (m : ℕ))
    (f : (ZMod (n : ℕ))ˣ → ℝ) :
    Haar.integral
        (fun x => f (ZMod.unitsMap h (coordinate x (m : ℕ)))) =
      normalizedStageAverage n f := by
  rw [show (fun x : Carrier =>
      f (ZMod.unitsMap h (coordinate x (m : ℕ)))) =
      (fun x : Carrier => f (coordinate x (n : ℕ))) by
    funext x
    rw [coordinate_compatible x h]]
  exact Haar.cylinder_readback n f

/-! ### Profinite cylinder KMS readout -/

noncomputable def profiniteCylinderExpectation
    (Haar : ProfiniteHaarExtensionData) : (Carrier → ℝ) → ℝ :=
  Haar.integral

theorem profiniteCylinderExpectation_normalized
    (Haar : ProfiniteHaarExtensionData) :
    profiniteCylinderExpectation Haar (fun _ : Carrier => 1) = 1 :=
  Haar.integral_const 1

theorem profiniteCylinderExpectation_kms
    (Haar : ProfiniteHaarExtensionData)
    (f g : Carrier → ℝ) :
    profiniteCylinderExpectation Haar (fun x => f x * g x) =
      profiniteCylinderExpectation Haar (fun x => g x * f x) := by
  apply congrArg Haar.integral
  funext x
  exact mul_comm _ _

theorem profiniteCylinderExpectation_add
    (Haar : ProfiniteHaarExtensionData) (f g : Carrier → ℝ) :
    profiniteCylinderExpectation Haar (fun x => f x + g x) =
      profiniteCylinderExpectation Haar f +
        profiniteCylinderExpectation Haar g :=
  Haar.integral_add f g

theorem profiniteCylinderExpectation_smul
    (Haar : ProfiniteHaarExtensionData) (c : ℝ) (f : Carrier → ℝ) :
    profiniteCylinderExpectation Haar (fun x => c * f x) =
      c * profiniteCylinderExpectation Haar f :=
  Haar.integral_smul c f

theorem profiniteCylinderExpectation_nonneg
    (Haar : ProfiniteHaarExtensionData) (f : Carrier → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ profiniteCylinderExpectation Haar f :=
  Haar.integral_nonneg f hf

/-! ### Topological KMS action on the profinite carrier -/

def carrierTranslate (a : TopologicalCarrier) (x : TopologicalCarrier) :
    TopologicalCarrier := a * x

def translateFunction (a : TopologicalCarrier) (f : TopologicalCarrier → ℝ) :
    TopologicalCarrier → ℝ :=
  fun x => f (a⁻¹ * x)

theorem translateFunction_one (f : TopologicalCarrier → ℝ) :
    translateFunction 1 f = f := by
  funext x
  simp [translateFunction]

theorem translateFunction_mul (a b : TopologicalCarrier)
    (f : TopologicalCarrier → ℝ) :
    translateFunction a (translateFunction b f) =
      translateFunction (a * b) f := by
  funext x
  simp [translateFunction, mul_assoc]

theorem translateFunction_inv (a : TopologicalCarrier)
    (f : TopologicalCarrier → ℝ) :
    translateFunction a⁻¹ (translateFunction a f) = f := by
  rw [translateFunction_mul]
  simpa using translateFunction_one f

structure ProfiniteHaarInvariantData extends ProfiniteHaarExtensionData where
  integral_translate : ∀ (a : TopologicalCarrier) (f : TopologicalCarrier → ℝ),
    integral (translateFunction a f) = integral f

def profiniteTopologicalKMS (Haar : ProfiniteHaarInvariantData)
    (a : TopologicalCarrier) (f : TopologicalCarrier → ℝ) : ℝ :=
  Haar.integral (translateFunction a f)

theorem profiniteTopologicalKMS_eq_expectation
    (Haar : ProfiniteHaarInvariantData) (a : TopologicalCarrier)
    (f : TopologicalCarrier → ℝ) :
    profiniteTopologicalKMS Haar a f = Haar.integral f :=
  Haar.integral_translate a f

theorem profiniteTopologicalKMS_normalized
    (Haar : ProfiniteHaarInvariantData) (a : TopologicalCarrier) :
    profiniteTopologicalKMS Haar a (fun _ => 1) = 1 := by
  rw [profiniteTopologicalKMS_eq_expectation]
  exact Haar.integral_const 1

theorem profiniteTopologicalKMS_kms
    (Haar : ProfiniteHaarInvariantData) (a : TopologicalCarrier)
    (f g : TopologicalCarrier → ℝ) :
    profiniteTopologicalKMS Haar a (fun x => f x * g x) =
      profiniteTopologicalKMS Haar a (fun x => g x * f x) := by
  rw [profiniteTopologicalKMS_eq_expectation,
    profiniteTopologicalKMS_eq_expectation]
  apply congrArg Haar.integral
  funext x
  exact mul_comm _ _

/-! ### Finite adelic unit windows

These windows are the finite algebraic shadows of an idelic construction.  We
use normalized counting measure, so every statement below is constructive at
the finite level and makes no claim about an infinite Haar measure.
-/

abbrev FiniteAdelicUnitWindow (P : Finset ℕ+) : Type :=
  ∀ p : P, (ZMod (p : ℕ))ˣ

noncomputable instance finiteAdelicUnitWindowFintype (P : Finset ℕ+) :
    Fintype (FiniteAdelicUnitWindow P) := by
  infer_instance

noncomputable def finiteAdelicAverage {P : Finset ℕ+}
    (f : FiniteAdelicUnitWindow P → ℝ) : ℝ :=
  normalizedFiniteAverage f

def carrierWindowProjection (P : Finset ℕ+) :
    Carrier → FiniteAdelicUnitWindow P :=
  fun x p => coordinate x p

theorem carrierWindowProjection_mul (P : Finset ℕ+) (x y : Carrier) :
    carrierWindowProjection P (x * y) =
      carrierWindowProjection P x * carrierWindowProjection P y := by
  funext p
  exact coordinate_mul x y p

theorem carrierWindowProjection_one (P : Finset ℕ+) :
    carrierWindowProjection P (1 : Carrier) = 1 := by
  funext p
  exact coordinate_one p

theorem carrierWindowProjection_inv (P : Finset ℕ+) (x : Carrier) :
    carrierWindowProjection P (x⁻¹) =
      (carrierWindowProjection P x)⁻¹ := by
  funext p
  exact coordinate_inv x p

theorem finiteAdelicAverage_const {P : Finset ℕ+} (c : ℝ) :
    finiteAdelicAverage (fun _ : FiniteAdelicUnitWindow P => c) = c := by
  simpa [finiteAdelicAverage] using
    (normalizedFiniteAverage_const
      (α := FiniteAdelicUnitWindow P) c)

theorem finiteAdelicAverage_add {P : Finset ℕ+}
    (f g : FiniteAdelicUnitWindow P → ℝ) :
    finiteAdelicAverage (fun x => f x + g x) =
      finiteAdelicAverage f + finiteAdelicAverage g := by
  simpa [finiteAdelicAverage] using normalizedFiniteAverage_add f g

theorem finiteAdelicAverage_smul {P : Finset ℕ+} (c : ℝ)
    (f : FiniteAdelicUnitWindow P → ℝ) :
    finiteAdelicAverage (fun x => c * f x) =
      c * finiteAdelicAverage f := by
  simpa [finiteAdelicAverage] using normalizedFiniteAverage_smul c f

def finiteAdelicTranslate {P : Finset ℕ+}
    (a : FiniteAdelicUnitWindow P)
    (f : FiniteAdelicUnitWindow P → ℝ) :
    FiniteAdelicUnitWindow P → ℝ :=
  fun x => f (a⁻¹ * x)

theorem finiteAdelicTranslate_one {P : Finset ℕ+}
    (f : FiniteAdelicUnitWindow P → ℝ) :
    finiteAdelicTranslate 1 f = f := by
  funext x
  simp [finiteAdelicTranslate]

theorem finiteAdelicTranslate_mul {P : Finset ℕ+}
    (a b : FiniteAdelicUnitWindow P)
    (f : FiniteAdelicUnitWindow P → ℝ) :
    finiteAdelicTranslate a (finiteAdelicTranslate b f) =
      finiteAdelicTranslate (a * b) f := by
  funext x
  simp [finiteAdelicTranslate, mul_assoc]

theorem finiteAdelicTranslate_inv {P : Finset ℕ+}
    (a : FiniteAdelicUnitWindow P)
    (f : FiniteAdelicUnitWindow P → ℝ) :
    finiteAdelicTranslate a⁻¹ (finiteAdelicTranslate a f) = f := by
  rw [finiteAdelicTranslate_mul]
  simpa using finiteAdelicTranslate_one f

theorem finiteAdelicAverage_translate {P : Finset ℕ+}
    (a : FiniteAdelicUnitWindow P)
    (f : FiniteAdelicUnitWindow P → ℝ) :
    finiteAdelicAverage (finiteAdelicTranslate a f) =
      finiteAdelicAverage f := by
  unfold finiteAdelicAverage finiteAdelicTranslate
  exact normalizedFiniteAverage_equiv (Equiv.mulLeft a⁻¹) f

/-! ### Algebraic finite crossed-product precursor -/

abbrev FiniteAdelicCrossedProduct (P : Finset ℕ+) : Type :=
  MonoidAlgebra ℝ (FiniteAdelicUnitWindow P)

noncomputable def finiteAdelicBasis {P : Finset ℕ+}
    (a : FiniteAdelicUnitWindow P) : FiniteAdelicCrossedProduct P :=
  MonoidAlgebra.single a 1

theorem finiteAdelicBasis_mul {P : Finset ℕ+}
    (a b : FiniteAdelicUnitWindow P) :
    finiteAdelicBasis (a * b) =
      finiteAdelicBasis a * finiteAdelicBasis b := by
  unfold finiteAdelicBasis
  rw [MonoidAlgebra.single_mul_single]
  simp

theorem finiteAdelicBasis_inv_mul {P : Finset ℕ+}
    (a : FiniteAdelicUnitWindow P) :
    finiteAdelicBasis (a⁻¹) * finiteAdelicBasis a =
      (1 : FiniteAdelicCrossedProduct P) := by
  rw [← finiteAdelicBasis_mul]
  simp only [inv_mul_cancel]
  unfold finiteAdelicBasis
  change MonoidAlgebra.single 1 1 = MonoidAlgebra.single 1 1
  rfl

theorem finiteAdelicBasis_mul_inv {P : Finset ℕ+}
    (a : FiniteAdelicUnitWindow P) :
    finiteAdelicBasis a * finiteAdelicBasis (a⁻¹) =
      (1 : FiniteAdelicCrossedProduct P) := by
  rw [← finiteAdelicBasis_mul]
  simp only [mul_inv_cancel]
  unfold finiteAdelicBasis
  change MonoidAlgebra.single 1 1 = MonoidAlgebra.single 1 1
  rfl

def finiteAdelicCoefficientAtOne {P : Finset ℕ+} :
    FiniteAdelicCrossedProduct P →+ ℝ :=
  { toFun := fun F => F 1
    map_zero' := by rfl
    map_add' := by intro F G; rfl }

theorem finiteAdelicCoefficientAtOne_basis {P : Finset ℕ+}
    (a : FiniteAdelicUnitWindow P) :
    finiteAdelicCoefficientAtOne (finiteAdelicBasis a) =
      if a = 1 then 1 else 0 := by
  classical
  unfold finiteAdelicCoefficientAtOne finiteAdelicBasis
  simp [Finsupp.single_apply]

theorem finiteAdelicCoefficientAtOne_conjugation_basis {P : Finset ℕ+}
    (a b : FiniteAdelicUnitWindow P) :
    finiteAdelicCoefficientAtOne
        (finiteAdelicBasis a * finiteAdelicBasis b *
          finiteAdelicBasis a⁻¹) =
      finiteAdelicCoefficientAtOne (finiteAdelicBasis b) := by
  rw [← finiteAdelicBasis_mul, ← finiteAdelicBasis_mul]
  simp [mul_assoc]

theorem finiteAdelicCoefficientAtOne_cyclic {P : Finset ℕ+}
    (F G : FiniteAdelicCrossedProduct P) :
    finiteAdelicCoefficientAtOne (F * G) =
      finiteAdelicCoefficientAtOne (G * F) := by
  rw [mul_comm]

end InfoGeometry.Arithmetic.ProfiniteCyclotomicUnitLimit
