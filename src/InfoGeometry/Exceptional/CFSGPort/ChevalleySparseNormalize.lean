/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from AxiomMath/CFSG RootOps/Sparse.lean.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleySparseColumns

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

variable {τ : Tag} {R : Type*} [CommRing R]

@[expose] def insertCoeff (x : ℕ × ℤ) : List (ℕ × ℤ) → List (ℕ × ℤ)
  | [] => [x]
  | y :: ys =>
    if x.1 < y.1 then x :: y :: ys
    else if x.1 = y.1 then (x.1, x.2 + y.2) :: ys
    else y :: insertCoeff x ys

@[expose] def normalize (v : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  (v.foldr insertCoeff []).filter fun x => x.2 != 0

theorem vecOf_insertCoeff (x : ℕ × ℤ) (v : List (ℕ × ℤ)) :
    vecOf τ R (insertCoeff x v) = (x.2 : R) • posVec τ R x.1 + vecOf τ R v := by
  induction v with
  | nil => simp [insertCoeff]
  | cons y v ih =>
    unfold insertCoeff
    split_ifs with h₁ h₂
    · rfl
    · simp only [vecOf_cons, h₂, Int.cast_add, add_smul]
      abel
    · rw [vecOf_cons, ih, vecOf_cons]
      abel

theorem vecOf_filter_ne_zero (v : List (ℕ × ℤ)) :
    vecOf τ R (v.filter fun x => x.2 != 0) = vecOf τ R v := by
  induction v with
  | nil => rfl
  | cons y v ih =>
    rw [List.filter_cons]
    split_ifs with h
    · rw [vecOf_cons, ih, vecOf_cons]
    · simp only [bne_iff_ne, ne_eq, not_not] at h
      rw [ih, vecOf_cons, h, Int.cast_zero, zero_smul, zero_add]

theorem vecOf_normalize (v : List (ℕ × ℤ)) : vecOf τ R (normalize v) = vecOf τ R v := by
  rw [normalize, vecOf_filter_ne_zero]
  induction v with
  | nil => rfl
  | cons x v ih => rw [List.foldr_cons, vecOf_insertCoeff, ih, vecOf_cons]

theorem vecOf_eq_of_normalize_eq {v w : List (ℕ × ℤ)} (h : normalize v = normalize w) :
    vecOf τ R v = vecOf τ R w := by
  rw [← vecOf_normalize v, h, vecOf_normalize]

@[expose] def decodeEntries : ℕ → ℕ → List Entry
  | 0, _ => []
  | fuel + 1, code =>
    if code = 0 then []
    else
      (code % 2 ^ 20 / 4096, code % 2 ^ 20 / 16 % 256, ((code % 16 : ℕ) : ℤ) - 8) ::
        decodeEntries fuel (code / 2 ^ 20)


end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps
