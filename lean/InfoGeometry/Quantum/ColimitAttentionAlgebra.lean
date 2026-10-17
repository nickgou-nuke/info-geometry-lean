import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Algebra.NonUnitalHom

noncomputable section

namespace InfoGeometry.Quantum.ColimitAttentionAlgebra

variable {n m : ℕ} (hnm : n ≤ m)

open Matrix

/-- Block embedding: embed M_n(ℂ) into M_m(ℂ) as top-left block with zeros elsewhere. -/
def blockEmbed (hnm : n ≤ m) : Matrix (Fin n) (Fin n) ℂ →ₙₐ[ℂ] Matrix (Fin m) (Fin m) ℂ where
  toFun A i j :=
    if hi : i.1 < n then
      if hj : j.1 < n then
        A ⟨i.1, hi⟩ ⟨j.1, hj⟩
      else 0
    else 0
  map_mul' := by
    intros A B
    ext i j
    by_cases hi : i.1 < n
    · by_cases hj : j.1 < n
      · have h_left : blockEmbed hnm (A * B) i j = (A * B) ⟨i.1, hi⟩ ⟨j.1, hj⟩ := by
          simp [blockEmbed, hi, hj]
      have h_right : (blockEmbed hnm A * blockEmbed hnm B) i j =
                     ∑ k : Fin m, blockEmbed hnm A i k * blockEmbed hnm B k j := by
          rw [Matrix.mul_apply]
      rw [h_left, h_right, Matrix.mul_apply]
      rw [← Finset.sum_filter]
      have h_bij : (∑ k ∈ Finset.filter (fun k : Fin m => k.1 < n) Finset.univ,
                     blockEmbed hnm A i k * blockEmbed hnm B k j) =
                   (∑ k : Fin n, A ⟨i.1, hi⟩ k * B k ⟨j.1, hj⟩) := by
        apply Finset.sum_bij
        · intro k hk; exact ⟨k.1, hk.2⟩
        · intro k hk; simp [blockEmbed, hi, hk.2, hj]
        · intro k hk; simp
        · intro k _; ext; simp [Fin.castLEEmb_apply]
        · intro k hk; simp
      rw [h_bij]
      rw [add_eq_left]
      · apply Finset.sum_eq_zero
        intro k hk
        simp at hk
        simp [blockEmbed, hi, hk, hj]
    · simp [blockEmbed, hi, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      simp [blockEmbed, hi]
  map_zero' := by
    ext i j
    simp
  map_add' := by
    intros A B
    ext i j
    simp
    split_ifs <;> simp
  map_smul' := by
    intros r A
    ext i j
    simp [Pi.smul_apply]
    by_cases hi : i.1 < n <;> by_cases hj : j.1 < n <;> simp [blockEmbed, smul_apply]

end InfoGeometry.Quantum.ColimitAttentionAlgebra

end
