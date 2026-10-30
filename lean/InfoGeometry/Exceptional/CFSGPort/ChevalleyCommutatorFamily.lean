/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Lean 4.34.1 port of the family-evaluation lemmas in
`CFSG.LieType.Chevalley.RootOps.Poly`. It connects the already checked sparse
commutator certificates to products in the local checked root-operator family.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyCommutatorCertificate
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootOperatorFamilyBridge

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

variable {τ : Tag} {R : Type*} [CommRing R]

@[expose] def rootAt (τ : Tag) (a : ℕ)
    (ha : a < τ.rootCertificate.roots.length) : RootCarrier τ :=
  ⟨τ.rootCertificate.root a, isRoot_rootCertificate_root ha⟩

theorem rootPos_rootAt {a : ℕ} (ha : a < τ.rootCertificate.roots.length) :
    rootPos (rootAt τ a ha) = a :=
  rootPos_eq ha rfl

theorem validP_nilpE (h : allValid τ = true) {g : ℕ}
    (hg : g < τ.rootCertificate.roots.length) (C : ℤ) (ea eb : ℕ) :
    ValidP τ (nilpE τ g C ea eb) := by
  intro x hx
  simp only [nilpE, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨k, hk, e, he, rfl⟩ := hx
  exact validEntries_of_validB (validB_of_allValid h hg hk) e he

theorem pOp_map_deg (δ : ℕ × ℕ) (L : List Entry) (s t : R) :
    pOp τ R (L.map fun e => (δ, e)) s t =
      (s ^ δ.1 * t ^ δ.2) • entriesOp τ R L := by
  induction L with
  | nil => simp
  | cons e L ih =>
      rw [List.map_cons, pOp_cons, ih, show e :: L = [e] ++ L from rfl,
        entriesOp_append, smul_add]

theorem one_add_pOp_nilpE (γ : RootCarrier τ) (C : ℤ) (ea eb : ℕ) (s t : R) :
    1 + pOp τ R (nilpE τ (rootPos γ) C ea eb) s t =
      (rootOperatorFamilyData τ).elt R γ ((C : R) * s ^ ea * t ^ eb) := by
  have hmap : ∀ k : ℕ, ((entries τ (rootPos γ) k).map fun e =>
      ((k * ea, k * eb), (e.1, e.2.1, C ^ k * e.2.2))) =
      ((entries τ (rootPos γ) k).map fun e => (e.1, e.2.1, C ^ k * e.2.2)).map
        fun e => ((k * ea, k * eb), e) := by
    intro k
    rw [List.map_map]
    rfl
  simp only [nilpE, pOp_flatMap, hmap, pOp_map_deg, entriesOp_map_smul,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [RootOperatorFamily.elt, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  change _ = (((C : R) * s ^ ea * t ^ eb) ^ 0) •
      (rootOperatorFamilyData τ).D R γ 0 +
    (((C : R) * s ^ ea * t ^ eb) ^ 1) • (rootOperatorFamilyData τ).D R γ 1 +
    (((C : R) * s ^ ea * t ^ eb) ^ 2) • (rootOperatorFamilyData τ).D R γ 2 +
    (((C : R) * s ^ ea * t ^ eb) ^ 3) • (rootOperatorFamilyData τ).D R γ 3
  simp only [rootOperatorFamilyData, DataChecks.family, dataD,
    show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega,
    show (3 : ℕ) ≠ 0 by omega, show (1 : ℕ) ≤ 3 by omega,
    show (2 : ℕ) ≤ 3 by omega, le_refl, ↓reduceIte, pow_zero, one_smul, smul_smul]
  have e1 : (s ^ (1 * ea) * t ^ (1 * eb)) * ((C ^ 1 : ℤ) : R) =
      ((C : R) * s ^ ea * t ^ eb) ^ 1 := by push_cast; ring
  have e2 : (s ^ (2 * ea) * t ^ (2 * eb)) * ((C ^ 2 : ℤ) : R) =
      ((C : R) * s ^ ea * t ^ eb) ^ 2 := by push_cast; ring
  have e3 : (s ^ (3 * ea) * t ^ (3 * eb)) * ((C ^ 3 : ℤ) : R) =
      ((C : R) * s ^ ea * t ^ eb) ^ 3 := by push_cast; ring
  rw [e1, e2, e3]
  abel

@[expose] noncomputable def factorsProd (τ : Tag) (R : Type*) [CommRing R]
    (fs : List Factor) (s t : R) : Module.End R (RootModule τ R) :=
  (fs.map fun f => if h : f.2.2.1 < τ.rootCertificate.roots.length then
    (rootOperatorFamilyData τ).elt R (rootAt τ f.2.2.1 h)
      ((f.2.2.2 : R) * s ^ f.1 * t ^ f.2.1) else 1).prod

theorem factorsProd_cons (f : Factor) (fs : List Factor) (s t : R) :
    factorsProd τ R (f :: fs) s t =
      (if h : f.2.2.1 < τ.rootCertificate.roots.length then
        (rootOperatorFamilyData τ).elt R (rootAt τ f.2.2.1 h)
          ((f.2.2.2 : R) * s ^ f.1 * t ^ f.2.1) else 1) *
        factorsProd τ R fs s t := by
  simp [factorsProd]

theorem one_add_pOp_factorsN (hv : allValid τ = true) (fs : List Factor)
    (hfs : ∀ f ∈ fs, f.2.2.1 < τ.rootCertificate.roots.length) (acc : List PEntry)
    (hacc : ValidP τ acc) (s t : R) :
    1 + pOp τ R (factorsN τ acc fs) s t =
      (1 + pOp τ R acc s t) * factorsProd τ R fs s t := by
  induction fs generalizing acc with
  | nil => simp [factorsN, factorsProd]
  | cons f fs ih =>
    have hf := hfs f (List.mem_cons_self ..)
    have hn := validP_nilpE hv hf f.2.2.2 f.1 f.2.1
    rw [factorsN,
      ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) _ (validP_mul1 hacc hn),
      one_add_pOp_mul1 acc hn, factorsProd_cons, mul_assoc]
    simp only [hf, ↓reduceDIte]
    congr 2
    have h := one_add_pOp_nilpE (R := R)
      (rootAt τ f.2.2.1 hf) f.2.2.2 f.1 f.2.1 s t
    rwa [rootPos_rootAt] at h

theorem validP_factorsN (hv : allValid τ = true) (fs : List Factor)
    (hfs : ∀ f ∈ fs, f.2.2.1 < τ.rootCertificate.roots.length) (acc : List PEntry)
    (hacc : ValidP τ acc) : ValidP τ (factorsN τ acc fs) := by
  induction fs generalizing acc with
  | nil => exact hacc
  | cons f fs ih =>
      exact ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) _
        (validP_mul1 hacc (validP_nilpE hv (hfs f (List.mem_cons_self ..)) _ _ _))

theorem elt_mul_elt_of_repCheck (hv : allValid τ = true) {a b : ℕ} {fs : List Factor}
    (h : repCheck τ a b fs = true) (α β : RootCarrier τ)
    (ha : rootPos α = a) (hb : rootPos β = b) (s t : R) :
    (rootOperatorFamilyData τ).elt R α s * (rootOperatorFamilyData τ).elt R β t =
      factorsProd τ R fs s t * (rootOperatorFamilyData τ).elt R β t *
        (rootOperatorFamilyData τ).elt R α s := by
  simp only [repCheck, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨ha', hb'⟩, hcone⟩, hpeq⟩ := h
  have hfs : ∀ f ∈ fs, f.2.2.1 < τ.rootCertificate.roots.length := fun f hf => by
    have hc := hcone f hf
    simp only [coneOk, Bool.and_eq_true, Nat.blt_eq] at hc
    exact hc.1.1.1
  have hA := validP_nilpE hv ha' 1 1 0
  have hB := validP_nilpE hv hb' 1 0 1
  have hP := validP_factorsN hv fs hfs [] (fun x hx => absurd hx (List.not_mem_nil))
  have heq := congrArg (fun X => 1 + X)
    (pOp_eq_of_pEqCheck (τ := τ) (R := R) hpeq s t)
  rw [one_add_pOp_mul1 _ hB, one_add_pOp_mul1 _ hA, one_add_pOp_mul1 _ hB,
    one_add_pOp_factorsN hv fs hfs [] (fun x hx => absurd hx (List.not_mem_nil))] at heq
  rw [← ha, ← hb] at heq
  simp only [one_add_pOp_nilpE, Int.cast_one, one_mul, pow_one, pow_zero, mul_one,
    pOp_nil, add_zero, one_mul] at heq
  exact heq

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

end
