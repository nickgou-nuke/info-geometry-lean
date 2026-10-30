/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from AxiomMath/CFSG RootOps/Sparse.lean.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleySparseColumns
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootTableAction

/-! # Sparse columns of the pinned Weyl operator -/

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

variable {τ : Tag} {R : Type*} [CommRing R]

theorem posVec_cartan (i : Fin τ.rank) : posVec τ R i = hVec τ R i := by
  have hi : (i : ℕ) < dim τ := by unfold dim; omega
  simp [posVec, posLabel, hi, i.2, hVec]

theorem posVec_root {k : ℕ} (hk : k < τ.rootCertificate.roots.length) :
    posVec τ R (τ.rank + k) = rootVec τ R (τ.rootCertificate.root k) := by
  have hi : τ.rank + k < dim τ := by unfold dim; omega
  have hn : ¬ τ.rank + k < τ.rank := by omega
  simp [posVec, posLabel, hi, hn, rootVec, isRoot_rootCertificate_root hk]

@[expose] def nPos (τ : Tag) (i : Fin τ.rank) (p : ℕ) : List (ℕ × ℤ) :=
  if h : p < τ.rank then [(p, 1), (i, -((τ.cartan ⟨p, h⟩ i).natAbs : ℤ))]
  else [(τ.rank + τ.rootCertificate.image (p - τ.rank) i, (-1) ^ downAt τ (p - τ.rank) i)]

theorem weylElt_posVec (i : Fin τ.rank) {p : ℕ} (hp : p < dim τ) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) (posVec τ R p) =
      vecOf τ R (nPos τ i p) := by
  unfold nPos
  split_ifs with h
  · have hi : posVec τ R (i : ℕ) = hVec τ R i := posVec_cartan i
    simp only [vecOf_cons, vecOf_nil, add_zero, Int.cast_one, one_smul, hi]
    rw [show posVec τ R p = hVec τ R ⟨p, h⟩ from posVec_cartan ⟨p, h⟩, weylElt_hVec]
    rw [Int.cast_neg, Int.cast_natCast, neg_smul, sub_eq_add_neg]
  · have hm : p - τ.rank < τ.rootCertificate.roots.length := by simp only [dim] at hp; omega
    have hpv : posVec τ R p = rootVec τ R (τ.rootCertificate.root (p - τ.rank)) := by
      have he : τ.rank + (p - τ.rank) = p := by omega
      simpa only [he] using (posVec_root (R := R) hm)
    have hq : posVec τ R (τ.rank + τ.rootCertificate.image (p - τ.rank) i) =
        rootVec τ R (τ.rootCertificate.root (τ.rootCertificate.image (p - τ.rank) i)) := by
      exact posVec_root (rootCertificate_image_lt hm i)
    rw [hpv, weylElt_rootVec i 1 (isRoot_rootCertificate_root hm), vecOf_cons, vecOf_nil,
      add_zero, hq, rootCertificate_root_image hm, stringDown_rootCertificate_root hm]
    simp

theorem validVec_nPos (i : Fin τ.rank) {p : ℕ} (hp : p < dim τ) : ValidVec τ (nPos τ i p) := by
  intro x hx
  unfold nPos at hx
  split_ifs at hx with h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simpa using h.trans_le (Nat.le_add_right _ _)
    · simpa using i.2.trans_le (Nat.le_add_right _ _)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    simp only [dim] at hp ⊢
    have := rootCertificate_image_lt (τ := τ) (k := p - τ.rank) (by omega) i
    omega

@[expose] def nVecL (τ : Tag) (i : Fin τ.rank) (v : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  v.flatMap fun x => (nPos τ i x.1).map fun y => (y.1, x.2 * y.2)

theorem weylElt_vecOf (i : Fin τ.rank) {v : List (ℕ × ℤ)} (hv : ValidVec τ v) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) (vecOf τ R v) =
      vecOf τ R (nVecL τ i v) := by
  induction v with
  | nil => simp [nVecL]
  | cons x v ih =>
    rw [vecOf_cons, map_add, map_smul, weylElt_posVec i (hv x (List.mem_cons_self ..)),
      ih fun y hy => hv y (List.mem_cons_of_mem _ hy)]
    simp only [nVecL, List.flatMap_cons, vecOf_append, vecOf_map_mul]

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps
