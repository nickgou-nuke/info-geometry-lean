/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from AxiomMath/CFSG RootOps/Poly.lean.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyOperatorPolynomial
public import InfoGeometry.Exceptional.CFSGPort.ChevalleySparseCertificate

/-!
# Sparse bivariate certificates on the root-module endomorphism algebra

The external commutator tables use this sparse polynomial format. Its
multiplication and equality checks are interpreted as full operator identities.
-/

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

abbrev PEntry : Type := (ℕ × ℕ) × Entry

variable {τ : Tag}

section Ring

variable {R : Type*} [CommRing R]

variable (τ R) in
@[expose] noncomputable def pOp (L : List PEntry) (s t : R) : Module.End R (RootModule τ R) :=
  (L.map fun x => (s ^ x.1.1 * t ^ x.1.2) • entriesOp τ R [x.2]).sum

/-- The external sparse format evaluates through the native
operator-coefficient evaluator. -/
theorem pOp_eq_eval (L : List PEntry) (s t : R) :
    pOp τ R L s t = OperatorPolynomial.eval
      (L.map fun x => (x.1, entriesOp τ R [x.2])) s t := by
  simp only [pOp, OperatorPolynomial.eval, OperatorPolynomial.evalTerm, List.map_map,
    Function.comp_def]

@[simp] theorem pOp_nil (s t : R) : pOp τ R [] s t = 0 :=
  rfl

theorem pOp_cons (x : PEntry) (L : List PEntry) (s t : R) :
    pOp τ R (x :: L) s t = (s ^ x.1.1 * t ^ x.1.2) • entriesOp τ R [x.2] + pOp τ R L s t :=
  rfl

theorem pOp_append (L L' : List PEntry) (s t : R) :
    pOp τ R (L ++ L') s t = pOp τ R L s t + pOp τ R L' s t := by
  simp [pOp]

theorem pOp_flatMap {α : Type*} (l : List α) (f : α → List PEntry) (s t : R) :
    pOp τ R (l.flatMap f) s t = (l.map fun a => pOp τ R (f a) s t).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, pOp_append, ih, List.map_cons, List.sum_cons]

@[expose] def ValidP (τ : Tag) (L : List PEntry) : Prop :=
  ∀ x ∈ L, x.2.1 < dim τ ∧ x.2.2.1 < dim τ

theorem ValidP.append {L L' : List PEntry} (h : ValidP τ L) (h' : ValidP τ L') :
    ValidP τ (L ++ L') := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h x hx
  · exact h' x hx

@[expose] def pmul (L L' : List PEntry) : List PEntry :=
  L'.flatMap fun y => (L.filter fun x => Nat.beq x.2.1 y.2.2.1).map fun x =>
    ((x.1.1 + y.1.1, x.1.2 + y.1.2), (y.2.1, x.2.2.1, x.2.2.2 * y.2.2.2))

theorem pOp_mul_single (L : List PEntry) (y : PEntry) (hy : y.2.2.1 < dim τ) (s t : R) :
    pOp τ R L s t * ((s ^ y.1.1 * t ^ y.1.2) • entriesOp τ R [y.2]) =
      pOp τ R ((L.filter fun x => Nat.beq x.2.1 y.2.2.1).map fun x =>
        ((x.1.1 + y.1.1, x.1.2 + y.1.2), (y.2.1, x.2.2.1, x.2.2.2 * y.2.2.2))) s t := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have key : ((s ^ x.1.1 * t ^ x.1.2) • entriesOp τ R [x.2]) *
        ((s ^ y.1.1 * t ^ y.1.2) • entriesOp τ R [y.2]) =
        if x.2.1 = y.2.2.1 then
          (s ^ (x.1.1 + y.1.1) * t ^ (x.1.2 + y.1.2)) •
            entriesOp τ R [(y.2.1, x.2.2.1, x.2.2.2 * y.2.2.2)]
        else 0 := by
      rw [smul_mul_smul_comm, entriesOp_single_mul_single _ _ hy]
      split_ifs
      · congr 1
        ring
      · rw [smul_zero]
    rw [pOp_cons, add_mul, ih, key, List.filter_cons]
    cases hb : Nat.beq x.2.1 y.2.2.1
    · have h : x.2.1 ≠ y.2.2.1 := fun h => by rw [h, Nat.beq_refl] at hb; cases hb
      simp only [h, ↓reduceIte, zero_add, Bool.false_eq_true]
    · have h : x.2.1 = y.2.2.1 := Nat.eq_of_beq_eq_true hb
      simp only [h, ↓reduceIte, List.map_cons, pOp_cons]

theorem pOp_pmul (L : List PEntry) {L' : List PEntry} (hL' : ValidP τ L') (s t : R) :
    pOp τ R (pmul L L') s t = pOp τ R L s t * pOp τ R L' s t := by
  induction L' with
  | nil => simp [pmul]
  | cons y L' ih =>
    have hy := (hL' y (List.mem_cons_self ..)).2
    rw [pmul, List.flatMap_cons, pOp_append, ← pmul, ih fun x hx => hL' x (List.mem_cons_of_mem _ hx),
      pOp_cons, mul_add, pOp_mul_single L y hy]

theorem validP_pmul {L L' : List PEntry} (hL : ValidP τ L) (hL' : ValidP τ L') :
    ValidP τ (pmul L L') := by
  intro z hz
  simp only [pmul, List.mem_flatMap, List.mem_map, List.mem_filter] at hz
  obtain ⟨y, hy, x, ⟨hx, -⟩, rfl⟩ := hz
  exact ⟨(hL' y hy).1, (hL x hx).2⟩

@[expose] def mul1 (A B : List PEntry) : List PEntry :=
  A ++ B ++ pmul A B

theorem one_add_pOp_mul1 (A : List PEntry) {B : List PEntry} (hB : ValidP τ B) (s t : R) :
    1 + pOp τ R (mul1 A B) s t = (1 + pOp τ R A s t) * (1 + pOp τ R B s t) := by
  rw [mul1, pOp_append, pOp_append, pOp_pmul A hB]
  noncomm_ring

theorem validP_mul1 {A B : List PEntry} (hA : ValidP τ A) (hB : ValidP τ B) :
    ValidP τ (mul1 A B) :=
  (hA.append hB).append (validP_pmul hA hB)

@[expose] def coeffAt (L : List PEntry) (δ : ℕ × ℕ) : List Entry :=
  (L.filter fun x => Nat.beq x.1.1 δ.1 && Nat.beq x.1.2 δ.2).map Prod.snd

theorem pOp_eq_sum (L : List PEntry) (S : Finset (ℕ × ℕ)) (hS : ∀ x ∈ L, x.1 ∈ S) (s t : R) :
    pOp τ R L s t = ∑ δ ∈ S, (s ^ δ.1 * t ^ δ.2) • entriesOp τ R (coeffAt L δ) := by
  induction L with
  | nil => simp [coeffAt]
  | cons x L ih =>
    rw [pOp_cons, ih fun y hy => hS y (List.mem_cons_of_mem _ hy)]
    have hx := hS x (List.mem_cons_self ..)
    have hc : ∀ δ : ℕ × ℕ, coeffAt (x :: L) δ =
        if x.1 = δ then x.2 :: coeffAt L δ else coeffAt L δ := by
      intro δ
      simp only [coeffAt, List.filter_cons]
      by_cases h : x.1 = δ
      · subst h
        simp [Nat.beq_refl]
      · have : ¬(Nat.beq x.1.1 δ.1 && Nat.beq x.1.2 δ.2) = true := by
          simp only [Bool.and_eq_true]
          exact fun ⟨h1, h2⟩ => h (Prod.ext (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2))
        simp [h, this]
    have hc' : ∀ δ : ℕ × ℕ, entriesOp τ R (coeffAt (x :: L) δ) =
        (if x.1 = δ then entriesOp τ R [x.2] else 0) + entriesOp τ R (coeffAt L δ) := by
      intro δ
      rw [hc δ]
      split_ifs
      · rw [show x.2 :: coeffAt L δ = [x.2] ++ coeffAt L δ from rfl, entriesOp_append]
      · rw [zero_add]
    simp only [hc', smul_add, Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, hx,
      ↓reduceIte]

@[expose] def pEqCheck (L L' : List PEntry) : Bool :=
  (L ++ L').all fun x => summaryEq (summary (coeffAt L x.1)) (summary (coeffAt L' x.1))

theorem pOp_eq_of_pEqCheck {L L' : List PEntry} (h : pEqCheck L L' = true) (s t : R) :
    pOp τ R L s t = pOp τ R L' s t := by
  classical
  set S : Finset (ℕ × ℕ) := ((L ++ L').map Prod.fst).toFinset
  have hS : ∀ x ∈ L ++ L', x.1 ∈ S := fun x hx =>
    List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
  rw [pOp_eq_sum L S (fun x hx => hS x (List.mem_append_left _ hx)),
    pOp_eq_sum L' S (fun x hx => hS x (List.mem_append_right _ hx))]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hδ)
  simp only [pEqCheck, List.all_eq_true] at h
  rw [entriesOp_eq_of_summaryEq (h x hx)]

end Ring

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps
