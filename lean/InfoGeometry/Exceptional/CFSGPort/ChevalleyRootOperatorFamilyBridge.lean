/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Local port of the operator/pinned-root bridge from
`CFSG.LieType.Chevalley.PinnedBridge`. It connects the checked sparse
`RootOperatorFamily` coefficients to the existing pinned root operators.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootOperatorFamilyData
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyPinnedBridge

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

open Chevalley

variable {τ : Tag}

@[expose] def wordRoot (w : List ℕ) (β : RootCarrier τ) : RootCarrier τ :=
  w.foldl (fun γ i => ⟨reflect τ (τ.idx i) γ.1, IsRoot.reflect (τ.idx i) γ.2⟩) β

theorem wordRoot_pinnedData {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    wordRoot (pinnedData τ α).2.1
      ⟨Pi.single (pinnedData τ α).1 1, IsRoot.basis (pinnedData τ α).1⟩ = ⟨α, hα⟩ := by
  apply Subtype.ext
  have hval (w : List ℕ) (β : RootCarrier τ) :
      (wordRoot w β).1 = w.foldl (fun v i => reflect τ (τ.idx i) v) β.1 := by
    induction w generalizing β with
    | nil => rfl
    | cons i w ih =>
        exact ih ⟨reflect τ (τ.idx i) β.1, IsRoot.reflect (τ.idx i) β.2⟩
  change (wordRoot (pinnedData τ α).2.1
      ⟨Pi.single (pinnedData τ α).1 1, IsRoot.basis (pinnedData τ α).1⟩).1 = α
  rw [hval]
  exact foldl_reflect_pinnedData hα

namespace RootOperatorFamily

variable (F : RootOperatorFamily τ)

@[expose] def wordSign : List ℕ → RootCarrier τ → ℤ
  | [], _ => 1
  | i :: w, β =>
      F.sign (τ.idx i) β * wordSign w ⟨reflect τ (τ.idx i) β.1,
        IsRoot.reflect (τ.idx i) β.2⟩

theorem wordSign_eq (w : List ℕ) (β : RootCarrier τ) :
    F.wordSign w β = 1 ∨ F.wordSign w β = -1 := by
  induction w generalizing β with
  | nil => exact .inl rfl
  | cons i w ih =>
    rcases F.sign_eq (τ.idx i) β with h | h <;>
      rcases ih ⟨reflect τ (τ.idx i) β.1, IsRoot.reflect (τ.idx i) β.2⟩ with h' | h' <;>
        simp [wordSign, h, h']

theorem weylElt_mul_D_mul_inv (R : Type u) [CommRing R]
    (i : Fin τ.rank) (β : RootCarrier τ) (k : ℕ) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * F.D R β k *
        (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
      ((F.sign i β ^ k : ℤ) : R) •
        F.D R ⟨reflect τ i β.1, IsRoot.reflect i β.2⟩ k := by
  rw [F.conj, smul_mul_assoc, Units.mul_inv_cancel_right]

theorem prod_weylElt_mul_D_mul_inv (R : Type u) [CommRing R]
    (w : List ℕ) (β : RootCarrier τ) (k : ℕ) :
    ((((w.map fun i => weylElt τ R (τ.idx i) 1).reverse).prod :
        (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) *
        F.D R β k *
        (((((w.map fun i => weylElt τ R (τ.idx i) 1).reverse).prod)⁻¹ :
          (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) =
      ((F.wordSign w β ^ k : ℤ) : R) • F.D R (wordRoot w β) k := by
  induction w generalizing β with
  | nil => simp [wordSign, wordRoot]
  | cons i w ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton,
      mul_inv_rev, Units.val_mul]
    set W := ((w.map fun i => weylElt τ R (τ.idx i) 1).reverse).prod
    calc
      (W : Module.End R (RootModule τ R)) *
          (weylElt τ R (τ.idx i) 1 : Module.End R (RootModule τ R)) * F.D R β k *
          ((((weylElt τ R (τ.idx i) 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
            Module.End R (RootModule τ R)) *
            ((W⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))) =
        (W : Module.End R (RootModule τ R)) *
          ((weylElt τ R (τ.idx i) 1 : Module.End R (RootModule τ R)) * F.D R β k *
            (((weylElt τ R (τ.idx i) 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
              Module.End R (RootModule τ R))) *
          ((W⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) := by
        simp only [mul_assoc]
      _ = ((F.sign (τ.idx i) β ^ k : ℤ) : R) •
          ((W : Module.End R (RootModule τ R)) *
            F.D R ⟨reflect τ (τ.idx i) β.1, IsRoot.reflect (τ.idx i) β.2⟩ k *
            ((W⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))) := by
        rw [F.weylElt_mul_D_mul_inv, mul_smul_comm, smul_mul_assoc]
      _ = ((F.wordSign (i :: w) β ^ k : ℤ) : R) •
          F.D R (wordRoot (i :: w) β) k := by
        rw [ih, smul_smul, wordSign, mul_pow, Int.cast_mul]
        rfl

@[expose] def pinnedFamilySign (α : Fin τ.rank → ℤ) : ℤ :=
  F.wordSign (pinnedData τ α).2.1
      ⟨Pi.single (pinnedData τ α).1 1, IsRoot.basis (pinnedData τ α).1⟩ *
    (pinnedData τ α).2.2

theorem pinnedFamilySign_eq (α : Fin τ.rank → ℤ) :
    F.pinnedFamilySign α = 1 ∨ F.pinnedFamilySign α = -1 := by
  unfold pinnedFamilySign
  rcases F.wordSign_eq (pinnedData τ α).2.1
      ⟨Pi.single (pinnedData τ α).1 1, IsRoot.basis (pinnedData τ α).1⟩ with h | h <;>
    rcases pinnedSign_eq τ α with h' | h' <;> simp [h, h']

theorem pinnedFamilySign_mul_self (R : Type u) [CommRing R]
    (α : Fin τ.rank → ℤ) :
    (F.pinnedFamilySign α : R) * (F.pinnedFamilySign α : R) = 1 := by
  rcases F.pinnedFamilySign_eq α with h | h <;> rw [h] <;> norm_num

theorem pinnedCoeff_eq_smul_D (R : Type u) [CommRing R]
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (k : ℕ) :
    pinnedCoeff τ R α k =
      ((F.pinnedFamilySign α ^ k : ℤ) : R) • F.D R ⟨α, hα⟩ k := by
  have h := F.prod_weylElt_mul_D_mul_inv R (pinnedData τ α).2.1
    ⟨Pi.single (pinnedData τ α).1 1, IsRoot.basis (pinnedData τ α).1⟩ k
  rw [F.D_simple, wordRoot_pinnedData hα] at h
  simp only [pinnedCoeff, pinnedWeyl]
  rw [h, smul_smul, pinnedFamilySign, mul_pow,
    Int.cast_mul, mul_comm]

@[expose] noncomputable def elt (R : Type u) [CommRing R]
    (α : RootCarrier τ) (c : R) : Module.End R (RootModule τ R) :=
  ∑ k ∈ Finset.range 4, c ^ k • F.D R α k

theorem pinnedX_eq_elt (R : Type u) [CommRing R]
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : R) :
    (pinnedX τ R α c : Module.End R (RootModule τ R)) =
      F.elt R ⟨α, hα⟩ ((F.pinnedFamilySign α : R) * c) := by
  rw [pinnedX_eq_sum, elt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [F.pinnedCoeff_eq_smul_D R hα k, smul_smul, mul_pow, Int.cast_pow, mul_comm (c ^ k)]

end RootOperatorFamily

@[simp] theorem pinnedX_eq_rootOperatorFamilyData (R : Type u) [CommRing R]
    {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : R) :
    (pinnedX τ R α c : Module.End R (RootModule τ R)) =
      (RootOperatorFamily.elt (rootOperatorFamilyData.{u} τ) R ⟨α, hα⟩
        ((RootOperatorFamily.pinnedFamilySign (rootOperatorFamilyData.{u} τ) α : R) * c)) := by
  let F : RootOperatorFamily.{u} τ := rootOperatorFamilyData.{u} τ
  simpa only [F] using F.pinnedX_eq_elt R hα c

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps
