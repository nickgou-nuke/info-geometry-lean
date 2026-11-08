import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Wire 1: Fock Space 3-mode to 5-mode Hodge Intertwiner Bridge

This module proves the exact intertwining between the 3-mode exterior/Hodge
space $\bigwedge^\bullet \mathbb{R}^3$ (dim 8) and the 5-mode master spinor Fock
space $\bigwedge^\bullet \mathbb{R}^5$ (dim 32).

Under the standard tensor factorization $\bigwedge^\bullet \mathbb{R}^5 \cong \bigwedge^\bullet \mathbb{R}^3 \otimes \bigwedge^\bullet \mathbb{R}^2$,
the 3-mode Hodge operator $D_H^{(3)}$ on $\bigwedge^\bullet \mathbb{R}^3$ embeds as
$D_H^{(3)} \otimes I_4$ on $\bigwedge^\bullet \mathbb{R}^5$.
-/

noncomputable section

namespace InfoGeometry.Canonical.HodgeFockEmbeddingBridge

open Matrix

abbrev Spinor8 := InfoGeometry.Algebra.FiniteSpin.Vec8R
abbrev Spinor32 := InfoGeometry.Algebra.FiniteSpin.Vec32R

/-- Canonical tensor factor equivalence Fin 32 ≃ Fin 8 × Fin 4 -/
def fin32Equiv : Fin 32 ≃ Fin 8 × Fin 4 where
  toFun i := (⟨i.val / 4, by omega⟩, ⟨i.val % 4, by omega⟩)
  invFun p := ⟨p.1.val * 4 + p.2.val, by
    rcases p with ⟨⟨m, hm⟩, ⟨b, hb⟩⟩
    dsimp
    have : m * 4 + b < 8 * 4 := by omega
    simpa using this⟩
  left_inv i := by
    ext
    dsimp
    omega
  right_inv p := by
    ext
    · dsimp; omega
    · dsimp; omega

/-- Canonical isometric embedding of 8D Fock space into 32D Fock space via vacuum tensor product |v⟩ ↦ |v⟩ ⊗ |0⟩ -/
def fockEmbedding (v : Spinor8) : Spinor32 :=
  fun i =>
    let p := fin32Equiv i
    if p.2.val = 0 then v p.1 else 0

/-- Standard 8D Hodge-Dirac operator -/
def dirac8 (D : Matrix (Fin 8) (Fin 8) ℝ) (v : Spinor8) : Spinor8 :=
  D *ᵥ v

/-- Extended 32D Hodge-Dirac operator D_8 ⊗ I_4 -/
def dirac32 (D : Matrix (Fin 8) (Fin 8) ℝ) : Matrix (Fin 32) (Fin 32) ℝ :=
  fun i j =>
    let pi := fin32Equiv i
    let pj := fin32Equiv j
    if pi.2 = pj.2 then D pi.1 pj.1 else 0

/-- 🏆 THEOREM 1: Exact Intertwining: fockEmbedding (D_8 v) = (D_8 ⊗ I_4) (fockEmbedding v) -/
theorem fockEmbedding_dirac_intertwine
    (D : Matrix (Fin 8) (Fin 8) ℝ) (v : Spinor8) :
    fockEmbedding (dirac8 D v) = (dirac32 D) *ᵥ (fockEmbedding v) := by
  ext i
  dsimp [fockEmbedding, dirac8, dirac32, Matrix.mulVec, dotProduct]
  have hequiv : ∑ j : Fin 32, (if (fin32Equiv i).2 = (fin32Equiv j).2 then D (fin32Equiv i).1 (fin32Equiv j).1 else 0) * (if (fin32Equiv j).2.val = 0 then v (fin32Equiv j).1 else 0) =
                ∑ p : Fin 8 × Fin 4, (if (fin32Equiv i).2 = (fin32Equiv (fin32Equiv.symm p)).2 then D (fin32Equiv i).1 (fin32Equiv (fin32Equiv.symm p)).1 else 0) * (if (fin32Equiv (fin32Equiv.symm p)).2.val = 0 then v (fin32Equiv (fin32Equiv.symm p)).1 else 0) := by
    exact ((fin32Equiv).symm.sum_comp _).symm
  rw [hequiv]
  simp_rw [fin32Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  have hinner (m : Fin 8) :
      ∑ b : Fin 4, (if (fin32Equiv i).2 = b then D (fin32Equiv i).1 m else 0) * (if b.val = 0 then v m else 0) =
        (if (fin32Equiv i).2.val = 0 then D (fin32Equiv i).1 m * v m else 0) := by
    have hb0 : (if (fin32Equiv i).2 = (0 : Fin 4) then D (fin32Equiv i).1 m else 0) * (if (0 : Fin 4).val = 0 then v m else 0) =
        if (fin32Equiv i).2.val = 0 then D (fin32Equiv i).1 m * v m else 0 := by
      dsimp
      by_cases h : (fin32Equiv i).2 = 0
      · simp [h]
      · have hval : (fin32Equiv i).2.val ≠ 0 := by
          intro hc
          apply h
          ext
          exact hc
        simp [h, hval]
    have hb1 : (if (fin32Equiv i).2 = (1 : Fin 4) then D (fin32Equiv i).1 m else 0) * (if (1 : Fin 4).val = 0 then v m else 0) = 0 := by
      have : (1 : Fin 4).val = 1 := rfl
      rw [this]
      simp
    have hb2 : (if (fin32Equiv i).2 = (2 : Fin 4) then D (fin32Equiv i).1 m else 0) * (if (2 : Fin 4).val = 0 then v m else 0) = 0 := by
      have : (2 : Fin 4).val = 2 := rfl
      rw [this]
      simp
    have hb3 : (if (fin32Equiv i).2 = (3 : Fin 4) then D (fin32Equiv i).1 m else 0) * (if (3 : Fin 4).val = 0 then v m else 0) = 0 := by
      have : (3 : Fin 4).val = 3 := rfl
      rw [this]
      simp
    rw [Fin.sum_univ_four]
    rw [hb0, hb1, hb2, hb3]
    ring
  simp_rw [hinner]
  split_ifs with h
  · rfl
  · simp

/-- 🏆 THEOREM 2: Exact Laplacian Intertwining Δ₃₂ (fockEmbedding v) = fockEmbedding (Δ₈ v) -/
theorem fockEmbedding_laplacian_intertwine
    (D : Matrix (Fin 8) (Fin 8) ℝ) (v : Spinor8) :
    (dirac32 D * dirac32 D) *ᵥ (fockEmbedding v) =
      fockEmbedding ((D * D) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec]
  rw [← fockEmbedding_dirac_intertwine]
  rw [← fockEmbedding_dirac_intertwine]
  dsimp [dirac8]
  rw [Matrix.mulVec_mulVec]

end InfoGeometry.Canonical.HodgeFockEmbeddingBridge
