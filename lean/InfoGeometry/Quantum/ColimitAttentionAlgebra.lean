import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Tactic

/-!
Finite-stage zero-padding on full complex matrix algebras. The map is
non-unital when `n < m`; this file does not assert injectivity or star
preservation. It is not the bonding map of the repository's Cuntz tensor-stage
colimit, which is owned by `InfoGeometry.Canonical.CuntzMatrixTraceTower` and
uses `A ↦ A ⊗ₖ 1`.
-/

noncomputable section

namespace InfoGeometry.Quantum.ColimitAttentionAlgebra

open Matrix

variable {n m : ℕ}

/-- The entrywise zero-padded finite matrix map. -/
def blockEmbedFn (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ := fun i j =>
  if hi : i.1 < n then
    if hj : j.1 < n then A ⟨i.1, hi⟩ ⟨j.1, hj⟩ else 0
  else 0

/-- Finite matrix zero-padding map. It is non-unital if `n < m`. -/
def blockEmbed (hnm : n ≤ m) :
    Matrix (Fin n) (Fin n) ℂ →ₙₐ[ℂ] Matrix (Fin m) (Fin m) ℂ where
  toFun := blockEmbedFn n m
  map_zero' := by
    ext i j
    by_cases hi : i.1 < n <;> by_cases hj : j.1 < n <;>
      simp [blockEmbedFn, hi, hj]
  map_add' := by
    intro A B
    ext i j
    by_cases hi : i.1 < n <;> by_cases hj : j.1 < n <;>
      simp [blockEmbedFn, hi, hj]
  map_smul' := by
    intro c A
    ext i j
    by_cases hi : i.1 < n <;> by_cases hj : j.1 < n <;>
      simp [blockEmbedFn, hi, hj, Matrix.smul_apply]
  map_mul' := by
    intro A B
    ext i j
    by_cases hi : i.1 < n
    · by_cases hj : j.1 < n
      · change blockEmbedFn n m (A * B) i j =
          ∑ k : Fin m, blockEmbedFn n m A i k * blockEmbedFn n m B k j
        simp [blockEmbedFn, hi, hj]
        rw [Matrix.mul_apply]
        let p : Fin m → Prop := fun k => k.1 < n
        let f : Fin m → ℂ := fun k =>
          (if hk : p k then A ⟨i.1, hi⟩ ⟨k.1, hk⟩ else 0) *
            (if hk : p k then B ⟨k.1, hk⟩ ⟨j.1, hj⟩ else 0)
        have hsum : (∑ k : Fin m, f k) =
            ∑ k : Fin n, A ⟨i.1, hi⟩ k * B k ⟨j.1, hj⟩ := by
          have hp : ∀ k ∈ (Finset.univ : Finset (Fin m)), f k ≠ 0 → p k := by
            intro k _ hne
            by_contra hk
            exact hne (by simp [f, p, hk])
          rw [← Finset.sum_filter_of_ne (s := Finset.univ) (p := p) hp]
          rw [← Finset.sum_subtype_eq_sum_filter]
          let e : Fin n ≃ {k : Fin m // p k} :=
            { toFun := fun k => ⟨Fin.castLEEmb hnm k, by simp [p, k.2]⟩
              invFun := fun k => ⟨k.1.1, k.2⟩
              left_inv := by intro k; apply Fin.ext; rfl
              right_inv := by intro k; apply Subtype.ext; apply Fin.ext; rfl }
          calc
            (∑ x ∈ Finset.subtype p Finset.univ, f x.1) =
                ∑ x : {k : Fin m // p k}, f x.1 := by simp
            _ = ∑ k : Fin n, f (e k).1 := by
              simpa using
                (Equiv.sum_comp e (fun x : {k : Fin m // p k} => f x.1)).symm
            _ = ∑ k : Fin n, A ⟨i.1, hi⟩ k * B k ⟨j.1, hj⟩ := by
              apply Finset.sum_congr rfl
              intro k hk
              simp [f, p, e]
        simpa [f, p, blockEmbedFn, hi, hj, Matrix.mul_apply] using hsum.symm
      · simp [blockEmbedFn, hj, Matrix.mul_apply]
    · simp [blockEmbedFn, hi, Matrix.mul_apply]

/-- The zero-padding map is not unital when the target dimension is strictly larger. -/
theorem blockEmbed_not_map_one (hnm : n < m) :
    blockEmbed (Nat.le_of_lt hnm) (1 : Matrix (Fin n) (Fin n) ℂ) ≠
      (1 : Matrix (Fin m) (Fin m) ℂ) := by
  intro h
  let i : Fin m := ⟨n, hnm⟩
  have hentry := congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M i i) h
  have hzero : blockEmbed (Nat.le_of_lt hnm) (1 : Matrix (Fin n) (Fin n) ℂ) i i = 0 := by
    simp [blockEmbed, blockEmbedFn, i]
  rw [hzero] at hentry
  simp at hentry

end InfoGeometry.Quantum.ColimitAttentionAlgebra

end
