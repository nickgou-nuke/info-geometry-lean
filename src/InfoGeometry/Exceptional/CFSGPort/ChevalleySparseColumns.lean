/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from AxiomMath/CFSG RootOps/Sparse.lean.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleySparseOperators

/-! # Sparse-column evaluation on the exceptional root module -/

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

variable {τ : Tag} {R : Type*} [CommRing R]

variable (τ R) in
@[expose] noncomputable def vecOf (v : List (ℕ × ℤ)) : RootModule τ R :=
  (v.map fun x => (x.2 : R) • posVec τ R x.1).sum

@[simp] theorem vecOf_nil : vecOf τ R [] = 0 :=
  rfl

@[simp] theorem vecOf_cons (x : ℕ × ℤ) (v : List (ℕ × ℤ)) :
    vecOf τ R (x :: v) = (x.2 : R) • posVec τ R x.1 + vecOf τ R v :=
  rfl

theorem vecOf_append (v w : List (ℕ × ℤ)) : vecOf τ R (v ++ w) = vecOf τ R v + vecOf τ R w := by
  simp [vecOf]

theorem vecOf_flatMap (v : List (ℕ × ℤ)) (f : ℕ × ℤ → List (ℕ × ℤ)) :
    vecOf τ R (v.flatMap f) = (v.map fun x => vecOf τ R (f x)).sum := by
  induction v with
  | nil => rfl
  | cons x v ih => rw [List.flatMap_cons, vecOf_append, ih, List.map_cons, List.sum_cons]

theorem vecOf_map_mul (z : ℤ) (v : List (ℕ × ℤ)) :
    vecOf τ R (v.map fun y => (y.1, z * y.2)) = (z : R) • vecOf τ R v := by
  induction v with
  | nil => simp
  | cons y v ih =>
    simp only [List.map_cons, vecOf_cons, ih, smul_add, Int.cast_mul, mul_smul]

@[expose] def colOf (L : List Entry) (c : ℕ) : List (ℕ × ℤ) :=
  (L.filter fun e => e.1 == c).map fun e => (e.2.1, e.2.2)

@[expose] def ValidVec (τ : Tag) (v : List (ℕ × ℤ)) : Prop :=
  ∀ x ∈ v, x.1 < dim τ

@[expose] def ValidEntries (τ : Tag) (L : List Entry) : Prop :=
  ∀ e ∈ L, e.1 < dim τ ∧ e.2.1 < dim τ

theorem ValidEntries.colOf {L : List Entry} (hL : ValidEntries τ L) (c : ℕ) :
    ValidVec τ (colOf L c) := by
  intro x hx
  simp only [RootOps.colOf, List.mem_map, List.mem_filter] at hx
  obtain ⟨e, ⟨he, -⟩, rfl⟩ := hx
  exact (hL e he).2

theorem entriesOp_cons (e : Entry) (L : List Entry) :
    entriesOp τ R (e :: L) =
      (e.2.2 : R) • (posCoord τ R e.1).smulRight (posVec τ R e.2.1) + entriesOp τ R L :=
  rfl

theorem entriesOp_posVec (L : List Entry) {c : ℕ} (hc : c < dim τ) :
    entriesOp τ R L (posVec τ R c) = vecOf τ R (colOf L c) := by
  induction L with
  | nil => simp [colOf]
  | cons e L ih =>
    rw [entriesOp_cons, LinearMap.add_apply, ih, LinearMap.smul_apply, LinearMap.smulRight_apply,
      posCoord_posVec hc]
    simp only [colOf, List.filter_cons, beq_iff_eq]
    split_ifs with h
    · simp
    · simp

@[expose] def applyL (L : List Entry) (v : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  v.flatMap fun x => (colOf L x.1).map fun y => (y.1, x.2 * y.2)

theorem entriesOp_vecOf (L : List Entry) {v : List (ℕ × ℤ)} (hv : ValidVec τ v) :
    entriesOp τ R L (vecOf τ R v) = vecOf τ R (applyL L v) := by
  induction v with
  | nil => simp [applyL]
  | cons x v ih =>
    rw [vecOf_cons, map_add, map_smul, entriesOp_posVec L (hv x (List.mem_cons_self ..)),
      ih fun y hy => hv y (List.mem_cons_of_mem _ hy)]
    simp only [applyL, List.flatMap_cons, vecOf_append, vecOf_map_mul]

/-- A sparse table represents a given root-module operator exactly when all
of its valid columns agree with that operator's action on the basis. -/
theorem entriesOp_eq_iff (L : List Entry) (f : Module.End R (RootModule τ R)) :
    entriesOp τ R L = f ↔
      ∀ c, c < dim τ → vecOf τ R (colOf L c) = f (posVec τ R c) := by
  constructor
  · intro h c hc
    rw [← entriesOp_posVec L hc, h]
  · intro h
    apply ext_posVec
    intro c hc
    rw [entriesOp_posVec L hc]
    exact h c hc

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps
