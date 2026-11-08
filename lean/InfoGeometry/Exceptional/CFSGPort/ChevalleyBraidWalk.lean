/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Port of AxiomMath/CFSG `CFSG.LieType.Chevalley.RootWalk`, using the local
checked root table and the existing Chevalley root-module operators.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootTableAction

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootWalk

open InfoGeometry.Exceptional.CFSGPort.Chevalley
  InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps CoxeterSystem

variable {τ : Tag} {R : Type*} [CommRing R]

theorem rootModule_end_ext {f g : Module.End R (RootModule τ R)}
    (hh : ∀ j, f (hVec τ R j) = g (hVec τ R j))
    (hr : ∀ α, IsRoot τ α → f (rootVec τ R α) = g (rootVec τ R α)) : f = g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rcases b with j | ⟨α, hα⟩
  · exact hh j
  · have h := hr α hα
    rwa [rootVec, dite_eq_left hα] at h

@[expose] def walk (τ : Tag) (ω : List (Fin τ.rank)) (k : ℕ) : ℕ × ℕ :=
  ω.foldr (fun i p => (τ.rootCertificate.image p.1 i,
    (p.2 + RootOps.downAt τ p.1 i) % 2)) (k, 0)

theorem walk_nil (k : ℕ) : walk τ [] k = (k, 0) :=
  rfl

theorem walk_cons (i : Fin τ.rank) (ω : List (Fin τ.rank)) (k : ℕ) :
    walk τ (i :: ω) k = (τ.rootCertificate.image (walk τ ω k).1 i,
      ((walk τ ω k).2 + RootOps.downAt τ (walk τ ω k).1 i) % 2) :=
  rfl

theorem walk_fst_lt (ω : List (Fin τ.rank)) {k : ℕ}
    (hk : k < τ.rootCertificate.roots.length) :
    (walk τ ω k).1 < τ.rootCertificate.roots.length := by
  induction ω with
  | nil => exact hk
  | cons i ω ih => exact RootOps.rootCertificate_image_lt ih i

theorem prod_weylElt_rootVec_root (ω : List (Fin τ.rank)) {k : ℕ}
    (hk : k < τ.rootCertificate.roots.length) :
    (((ω.map fun i => weylElt τ R i 1).prod :
        (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
        (rootVec τ R (τ.rootCertificate.root k)) =
      ((-1 : R) ^ (walk τ ω k).2) •
        rootVec τ R (τ.rootCertificate.root (walk τ ω k).1) := by
  induction ω with
  | nil => simp [walk_nil]
  | cons i ω ih =>
    have hlt := walk_fst_lt ω hk
    rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, ih, map_smul,
      weylElt_rootVec i 1 (isRoot_rootCertificate_root hlt), one_zpow, Units.val_one, mul_one,
      stringDown_rootCertificate_root hlt, ← rootCertificate_root_image hlt, smul_smul,
      ← pow_add, walk_cons,
      neg_one_pow_eq_pow_mod_two (R := R) (n := (walk τ ω k).2 + downAt τ (walk τ ω k).1 i)]

variable (R) in
@[expose] noncomputable def hVecSum (c : Fin τ.rank → ℤ) : RootModule τ R :=
  ∑ j, (c j : R) • hVec τ R j

theorem hVecSum_single (k : Fin τ.rank) :
    hVecSum R (Pi.single k 1) = hVec τ R k := by
  simp [hVecSum, Pi.single_apply]

@[expose] def hStep (τ : Tag) (i : Fin τ.rank) (c : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  c - (∑ j, ((τ.cartan j i).natAbs : ℤ) * c j) • Pi.single i 1

theorem weylElt_hVecSum (i : Fin τ.rank) (t : Rˣ) (c : Fin τ.rank → ℤ) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) (hVecSum R c) =
      hVecSum R (hStep τ i c) := by
  simp only [hVecSum, hStep, map_sum, map_smul, weylElt_hVec, smul_sub,
    Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub,
    sub_smul, Pi.single_apply, mul_ite, mul_one, mul_zero, Int.cast_ite,
    Int.cast_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  rw [Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, Int.cast_mul, Int.cast_natCast, mul_comm]

variable (R) in
theorem prod_weylElt_hVecSum (ω : List (Fin τ.rank)) (c : Fin τ.rank → ℤ) :
    (((ω.map fun i => weylElt τ R i 1).prod :
        (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
        (hVecSum R c) = hVecSum R (ω.foldr (hStep τ) c) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, ih,
      weylElt_hVecSum, List.foldr_cons]

@[expose] def braidLength (c : ℤ) : ℕ :=
  if c = 0 then 2 else if c = 1 then 3 else if c = 2 then 4 else if c = 3 then 6 else
    if c = 4 then 1 else 0

@[expose] def braidCheckPair (τ : Tag) (i j : Fin τ.rank) : Bool :=
  ((List.finRange τ.rank).all fun k =>
      List.ofFn ((CoxeterSystem.alternatingWord i j
        (braidLength (τ.cartan i j * τ.cartan j i))).foldr (hStep τ) (Pi.single k 1)) ==
        List.ofFn ((CoxeterSystem.alternatingWord j i
          (braidLength (τ.cartan i j * τ.cartan j i))).foldr (hStep τ) (Pi.single k 1))) &&
    (List.range τ.rootCertificate.roots.length).all fun k =>
      decide (walk τ (CoxeterSystem.alternatingWord i j
        (braidLength (τ.cartan i j * τ.cartan j i))) k =
        walk τ (CoxeterSystem.alternatingWord j i
          (braidLength (τ.cartan i j * τ.cartan j i))) k)

@[expose] def braidCheck (τ : Tag) : Bool :=
  (List.finRange τ.rank).all fun i => (List.finRange τ.rank).all fun j =>
    !decide (i < j) || braidCheckPair τ i j

theorem g2_braidCheck : braidCheck .G2 = true := by decide +kernel

theorem f4_braidCheck : braidCheck .F4 = true := by decide +kernel

theorem d4_braidCheck : braidCheck .D4 = true := by decide +kernel

theorem e6_braidCheck : braidCheck .E6 = true := by decide +kernel

theorem e7_braidCheck : braidCheck .E7 = true := by decide +kernel

theorem e8_braidCheck : braidCheck .E8 = true := by decide +kernel

theorem braidCheck_eq_true : ∀ τ : Tag, braidCheck τ = true
  | .G2 => g2_braidCheck
  | .F4 => f4_braidCheck
  | .D4 => d4_braidCheck
  | .E6 => e6_braidCheck
  | .E7 => e7_braidCheck
  | .E8 => e8_braidCheck

theorem braidCheckPair_of_lt {i j : Fin τ.rank} (hij : i < j) :
    (∀ k : Fin τ.rank,
      (CoxeterSystem.alternatingWord i j
        (braidLength (τ.cartan i j * τ.cartan j i))).foldr (hStep τ) (Pi.single k 1) =
        (CoxeterSystem.alternatingWord j i
          (braidLength (τ.cartan i j * τ.cartan j i))).foldr (hStep τ) (Pi.single k 1)) ∧
      ∀ k < τ.rootCertificate.roots.length,
        walk τ (CoxeterSystem.alternatingWord i j
          (braidLength (τ.cartan i j * τ.cartan j i))) k =
          walk τ (CoxeterSystem.alternatingWord j i
            (braidLength (τ.cartan i j * τ.cartan j i))) k := by
  have h := braidCheck_eq_true τ
  simp only [braidCheck, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  have hp := (h i j).resolve_left (not_not.2 hij)
  simp only [braidCheckPair, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies, List.mem_range, decide_eq_true_eq] at hp
  exact ⟨fun k => List.ofFn_injective (eq_of_beq (hp.1 k)), hp.2⟩

theorem prod_alternatingWord_weylElt_of_lt {i j : Fin τ.rank} (hij : i < j) :
    ((CoxeterSystem.alternatingWord i j
      (braidLength (τ.cartan i j * τ.cartan j i))).map
        fun k => weylElt τ R k 1).prod =
      ((CoxeterSystem.alternatingWord j i
        (braidLength (τ.cartan i j * τ.cartan j i))).map
          fun k => weylElt τ R k 1).prod := by
  obtain ⟨hh, hr⟩ := braidCheckPair_of_lt hij
  apply Units.ext
  apply rootModule_end_ext
  · intro k
    rw [← hVecSum_single, prod_weylElt_hVecSum, prod_weylElt_hVecSum]
    congr 1
    exact hh k
  · intro α hα
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
    rw [prod_weylElt_rootVec_root (R := R) _ hk,
      prod_weylElt_rootVec_root (R := R) _ hk, hr k hk]

theorem prod_alternatingWord_weylElt (i j : Fin τ.rank) :
    ((CoxeterSystem.alternatingWord i j
      (braidLength (τ.cartan i j * τ.cartan j i))).map
        fun k => weylElt τ R k 1).prod =
      ((CoxeterSystem.alternatingWord j i
        (braidLength (τ.cartan i j * τ.cartan j i))).map
          fun k => weylElt τ R k 1).prod := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact prod_alternatingWord_weylElt_of_lt (R := R) hij
  · rfl
  · have hcomm := prod_alternatingWord_weylElt_of_lt (R := R) hij
    rw [mul_comm] at hcomm
    exact hcomm.symm

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootWalk
