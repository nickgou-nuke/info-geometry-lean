/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from AxiomMath/CFSG RootOps/Poly.lean. Coefficients here are native
root-module endomorphisms; external sparse entries can be interpreted into
these coefficients before using the evaluation theorems.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleySparseColumns

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.OperatorPolynomial

variable {τ : Tag} {R : Type*} [CommRing R]

/-- A bivariate monomial with a full, potentially noncommuting operator
coefficient on the exceptional root module. -/
abbrev Term (τ : Tag) (R : Type*) [CommRing R] :=
  (ℕ × ℕ) × Module.End R (RootModule τ R)

@[expose] def evalTerm (x : Term τ R) (s t : R) : Module.End R (RootModule τ R) :=
  (s ^ x.1.1 * t ^ x.1.2) • x.2

@[expose] def eval (L : List (Term τ R)) (s t : R) : Module.End R (RootModule τ R) :=
  (L.map fun x => evalTerm x s t).sum

@[simp] theorem eval_nil (s t : R) : eval ([] : List (Term τ R)) s t = 0 := rfl

theorem eval_cons (x : Term τ R) (L : List (Term τ R)) (s t : R) :
    eval (x :: L) s t = evalTerm x s t + eval L s t := rfl

theorem eval_append (L M : List (Term τ R)) (s t : R) :
    eval (L ++ M) s t = eval L s t + eval M s t := by
  simp [eval]

/-- Coefficient products retain their order under operator composition. -/
@[expose] def mulTerm (x y : Term τ R) : Term τ R :=
  ((x.1.1 + y.1.1, x.1.2 + y.1.2), x.2 * y.2)

theorem evalTerm_mulTerm (x y : Term τ R) (s t : R) :
    evalTerm (mulTerm x y) s t = evalTerm x s t * evalTerm y s t := by
  simp only [evalTerm, mulTerm, smul_mul_smul_comm]
  congr 1
  ring

/-- Distributive multiplication of finite operator-polynomial expressions. -/
@[expose] def mul (L M : List (Term τ R)) : List (Term τ R) :=
  L.flatMap fun x => M.map (mulTerm x)

theorem eval_map_mulTerm (x : Term τ R) (M : List (Term τ R)) (s t : R) :
    eval (M.map (mulTerm x)) s t = evalTerm x s t * eval M s t := by
  induction M with
  | nil => simp
  | cons y M ih =>
    rw [List.map_cons, eval_cons, evalTerm_mulTerm, ih, eval_cons, mul_add]

/-- Soundness of symbolic multiplication in the noncommutative operator
algebra, valid over every commutative coefficient ring. -/
theorem eval_mul (L M : List (Term τ R)) (s t : R) :
    eval (mul L M) s t = eval L s t * eval M s t := by
  induction L with
  | nil => simp [mul]
  | cons x L ih =>
    rw [mul, List.flatMap_cons, eval_append, eval_map_mulTerm, ← mul, ih,
      eval_cons, add_mul]

/-- Product of two identity-plus-polynomial operators, as used in the
root-operator commutator certificates. -/
@[expose] def mulOne (L M : List (Term τ R)) : List (Term τ R) :=
  L ++ M ++ mul L M

theorem one_add_eval_mulOne (L M : List (Term τ R)) (s t : R) :
    1 + eval (mulOne L M) s t = (1 + eval L s t) * (1 + eval M s t) := by
  rw [mulOne, eval_append, eval_append, eval_mul]
  noncomm_ring

/-- Collect the operator coefficient at a bidegree, adding repeated terms. -/
@[expose] def coeff (L : List (Term τ R)) (δ : ℕ × ℕ) :
    Module.End R (RootModule τ R) :=
  ((L.filter fun x => x.1 = δ).map Prod.snd).sum

theorem coeff_cons (x : Term τ R) (L : List (Term τ R)) (δ : ℕ × ℕ) :
    coeff (x :: L) δ = (if x.1 = δ then x.2 else 0) + coeff L δ := by
  by_cases h : x.1 = δ <;> simp [coeff, h]

/-- Evaluation can be regrouped by any finite set containing all bidegrees. -/
theorem eval_eq_sum (L : List (Term τ R)) (S : Finset (ℕ × ℕ))
    (hS : ∀ x ∈ L, x.1 ∈ S) (s t : R) :
    eval L s t = ∑ δ ∈ S, (s ^ δ.1 * t ^ δ.2) • coeff L δ := by
  induction L with
  | nil => simp [coeff]
  | cons x L ih =>
    rw [eval_cons, ih (fun y hy => hS y (List.mem_cons_of_mem _ hy))]
    have hx := hS x (List.mem_cons_self ..)
    simp only [coeff_cons, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero,
      Finset.sum_ite_eq, hx, ↓reduceIte, evalTerm]

/-- Equality of collected operator coefficients certifies equality for all
parameters, without imposing commutativity on the operator coefficients. -/
theorem eval_eq_of_coeff_eq (L M : List (Term τ R))
    (h : ∀ δ, coeff L δ = coeff M δ) (s t : R) :
    eval L s t = eval M s t := by
  let S := ((L ++ M).map Prod.fst).toFinset
  have hS : ∀ x ∈ L ++ M, x.1 ∈ S := fun x hx =>
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)
  rw [eval_eq_sum L S (fun x hx => hS x (List.mem_append_left _ hx)),
    eval_eq_sum M S (fun x hx => hS x (List.mem_append_right _ hx))]
  simp only [h]

end InfoGeometry.Exceptional.CFSGPort.Chevalley.OperatorPolynomial
