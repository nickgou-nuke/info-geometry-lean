/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.GradedNullconeAlgebra
import InfoGeometry.Clifford.SplitCl11GradedTensorTower
import InfoGeometry.Clifford.DaviauRealDirac8x8
import InfoGeometry.Clifford.DaviauChiralPeirceSU2
import InfoGeometry.Clifford.LochakRodichevFierzKrein
import InfoGeometry.Clifford.SplitCliffordMatrixEquiv

/-!
# Daviau Real `M₈(ℝ)` Dirac Algebra Inside the `k = 3` Parity-Soldered `Cl(1,1)` Tower

Establishes without any change of basis (`towerIdx3EquivFin8`) that Daviau's real `8 × 8` Dirac
matrices `Γ^μ` (`gammaR μ`), quaternionic commutant `{P₁, P₂, P₃}` (`quatPR j`), pseudoscalar
`Γ^{0123}` (`gamma0123R`), chirality `γ₅ = Γ^{0123} P₃` (`gamma5Real 2`), and chiral Peirce
projectors `(p_j, p'_j)` sit verbatim inside:

1. **Rung `k = 3` of the Axiom 5 parity-soldered tower** (`Matrix (TowerIdx 3) (TowerIdx 3) ℝ`
   from `InfoGeometry.Algebra.GradedNullconeAlgebra`) as explicit 1-to-4-factor monomials in the
   split `(3, 3)` Jordan–Wigner Clifford generators `m_i^+ = e_i^+ + e_i^-` and
   `m_i^- = e_i^+ - e_i^-` (`i = 0, 1, 2`).
2. **The abstract `3`-fold graded tensor power `SplitClPower 3 ≅ ⊗ᵍ^3 Cl(1,1)`** (via
   `SplitCl11GradedTensorTower.splitClPowerEquivMat 3`).
-/

noncomputable section

open scoped Kronecker Matrix
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Algebra.GradedNullconeAlgebra
open InfoGeometry.Clifford.SplitCl11GradedTensorTower
open InfoGeometry.Clifford.DaviauRealDirac8x8
open InfoGeometry.Clifford.DaviauChiralPeirceSU2
open InfoGeometry.Clifford.LochakRodichevFierzKrein

namespace InfoGeometry.Clifford.DaviauCl11TowerRung3Bridge

/-! ### 1. Closed Noncommutativity Witnesses (Trap T16) -/

theorem mat8R_mul_noncomm_witness :
    ∃ A B : Mat8R, A * B ≠ B * A :=
  ⟨gammaR 0, gammaR 1, daviau_mat8_noncomm.1⟩

theorem tower3_mul_noncomm_witness :
    ∃ A B : Matrix (TowerIdx 3) (TowerIdx 3) ℝ, A * B ≠ B * A :=
  towerMatrix_mul_noncommutative 3 (by decide)

theorem splitCl3_mul_noncomm_witness :
    ∃ A B : SplitClPower 3, A * B ≠ B * A := by
  refine ⟨(splitClPowerEquivMat 3).symm (gammaR 0),
    (splitClPowerEquivMat 3).symm (gammaR 1), ?_⟩
  intro h
  apply daviau_mat8_noncomm.1
  have h' := congrArg (splitClPowerEquivMat 3) h
  simpa only [map_mul, AlgEquiv.apply_symm_apply] using h'

/-! ### 2. Index Equivalence `TowerIdx 3 ≃ Fin 8` & Algebra Isomorphisms -/

/-- Canonical binary index equivalence mapping `((((), b₀), b₁), b₂) : TowerIdx 3` to
`4 * b₀ + 2 * b₁ + b₂ : Fin 8`. -/
def towerIdx3EquivFin8 : TowerIdx 3 ≃ Fin 8 where
  toFun x := ⟨4 * x.1.1.2.val + 2 * x.1.2.val + x.2.val, by omega⟩
  invFun i := ((((), ⟨i.val / 4, by omega⟩), ⟨(i.val / 2) % 2, by omega⟩), ⟨i.val % 2, by omega⟩)
  left_inv x := by
    rcases x with ⟨⟨⟨u, b0⟩, b1⟩, b2⟩
    cases u
    fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> rfl
  right_inv i := by
    fin_cases i <;> rfl

/-- Real algebra isomorphism reindexing rung `k = 3` of the `Cl(1,1)` tower onto `M₈(ℝ)`. -/
def tower3AlgEquivMat8 : Matrix (TowerIdx 3) (TowerIdx 3) ℝ ≃ₐ[ℝ] Mat8R :=
  Matrix.reindexAlgEquiv ℝ ℝ towerIdx3EquivFin8

/-- Real algebra isomorphism between `SplitClPower 3` and `Matrix (TowerIdx 3) (TowerIdx 3) ℝ`. -/
def splitCl3EquivTower3 :
    SplitClPower 3 ≃ₐ[ℝ] Matrix (TowerIdx 3) (TowerIdx 3) ℝ :=
  (splitClPowerEquivMat 3).trans tower3AlgEquivMat8.symm

/-! ### 3. Split `(3, 3)` Jordan–Wigner Generators in `M₈(ℝ)` and Sparse `ℤ`-Models -/

/-- Rung-3 positive split Clifford generators `m_i^+ = e_i^+ + e_i^-` transported to `M₈(ℝ)`. -/
def mPos3 (i : Fin 3) : Mat8R :=
  tower3AlgEquivMat8 (jwPos 3 i + jwNeg 3 i)

/-- Rung-3 negative split Clifford generators `m_i^- = e_i^+ - e_i^-` transported to `M₈(ℝ)`. -/
def mNeg3 (i : Fin 3) : Mat8R :=
  tower3AlgEquivMat8 (jwPos 3 i - jwNeg 3 i)

/-- Rung-3 total parity operator `Γ^(3)` transported to `M₈(ℝ)`. -/
def towerGamma3Mat8 : Mat8R :=
  tower3AlgEquivMat8 (towerGamma 3)

/-- The transported generators `(mPos3, mNeg3)` satisfy the exact `(3, 3)` split Clifford and
grading relations of `axiom5_parity_soldered_clifford_tower 3`. -/
theorem mPos3_mNeg3_split_clifford (i j : Fin 3) :
    (mPos3 i * mPos3 i = 1) ∧
    (mNeg3 i * mNeg3 i = -1) ∧
    (i ≠ j → mPos3 i * mPos3 j + mPos3 j * mPos3 i = 0) ∧
    (i ≠ j → mNeg3 i * mNeg3 j + mNeg3 j * mNeg3 i = 0) ∧
    (mPos3 i * mNeg3 j + mNeg3 j * mPos3 i = 0) ∧
    (towerGamma3Mat8 * towerGamma3Mat8 = 1) := by
  have h5 := axiom5_parity_soldered_clifford_tower 3
  have hpos_anticomm (hij : i ≠ j) :
      (jwPos 3 i + jwNeg 3 i) * (jwPos 3 j + jwNeg 3 j) +
        (jwPos 3 j + jwNeg 3 j) * (jwPos 3 i + jwNeg 3 i) = 0 := by
    have hpp := h5.2.2.2.2.1 i j
    have hnn := h5.2.2.2.2.2.1 i j
    have hpn := h5.2.2.2.2.2.2.1 i j
    have hnp := h5.2.2.2.2.2.2.1 j i
    have hij' : j ≠ i := fun h => hij h.symm
    simp only [hij, hij', ite_false] at hpn hnp
    calc
      (jwPos 3 i + jwNeg 3 i) * (jwPos 3 j + jwNeg 3 j) +
          (jwPos 3 j + jwNeg 3 j) * (jwPos 3 i + jwNeg 3 i)
          = (jwPos 3 i * jwPos 3 j + jwPos 3 j * jwPos 3 i) +
            (jwNeg 3 i * jwNeg 3 j + jwNeg 3 j * jwNeg 3 i) +
            (jwPos 3 i * jwNeg 3 j + jwNeg 3 j * jwPos 3 i) +
            (jwPos 3 j * jwNeg 3 i + jwNeg 3 i * jwPos 3 j) := by noncomm_ring
      _ = 0 := by rw [hpp, hnn, hpn, hnp, add_zero, add_zero, add_zero]
  have hneg_anticomm (hij : i ≠ j) :
      (jwPos 3 i - jwNeg 3 i) * (jwPos 3 j - jwNeg 3 j) +
        (jwPos 3 j - jwNeg 3 j) * (jwPos 3 i - jwNeg 3 i) = 0 := by
    have hpp := h5.2.2.2.2.1 i j
    have hnn := h5.2.2.2.2.2.1 i j
    have hpn := h5.2.2.2.2.2.2.1 i j
    have hnp := h5.2.2.2.2.2.2.1 j i
    have hij' : j ≠ i := fun h => hij h.symm
    simp only [hij, hij', ite_false] at hpn hnp
    calc
      (jwPos 3 i - jwNeg 3 i) * (jwPos 3 j - jwNeg 3 j) +
          (jwPos 3 j - jwNeg 3 j) * (jwPos 3 i - jwNeg 3 i)
          = (jwPos 3 i * jwPos 3 j + jwPos 3 j * jwPos 3 i) +
            (jwNeg 3 i * jwNeg 3 j + jwNeg 3 j * jwNeg 3 i) -
            (jwPos 3 i * jwNeg 3 j + jwNeg 3 j * jwPos 3 i) -
            (jwPos 3 j * jwNeg 3 i + jwNeg 3 i * jwPos 3 j) := by noncomm_ring
      _ = 0 := by rw [hpp, hnn, hpn, hnp]; simp
  have hcross_anticomm :
      (jwPos 3 i + jwNeg 3 i) * (jwPos 3 j - jwNeg 3 j) +
        (jwPos 3 j - jwNeg 3 j) * (jwPos 3 i + jwNeg 3 i) = 0 := by
    have hpp := h5.2.2.2.2.1 i j
    have hnn := h5.2.2.2.2.2.1 i j
    have hpn := h5.2.2.2.2.2.2.1 i j
    have hnp := h5.2.2.2.2.2.2.1 j i
    calc
      (jwPos 3 i + jwNeg 3 i) * (jwPos 3 j - jwNeg 3 j) +
          (jwPos 3 j - jwNeg 3 j) * (jwPos 3 i + jwNeg 3 i)
          = (jwPos 3 i * jwPos 3 j + jwPos 3 j * jwPos 3 i) -
            (jwNeg 3 i * jwNeg 3 j + jwNeg 3 j * jwNeg 3 i) -
            (jwPos 3 i * jwNeg 3 j + jwNeg 3 j * jwPos 3 i) +
            (jwPos 3 j * jwNeg 3 i + jwNeg 3 i * jwPos 3 j) := by noncomm_ring
      _ = 0 := by
          rw [hpp, hnn, hpn, hnp]
          by_cases hij : i = j <;> simp [hij, eq_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [mPos3]
    rw [← map_mul, (h5.2.2.2.2.2.2.2 i).1, map_one]
  · dsimp [mNeg3]
    rw [← map_mul, (h5.2.2.2.2.2.2.2 i).2, map_neg, map_one]
  · intro hij
    dsimp [mPos3]
    rw [← map_mul, ← map_mul, ← map_add, hpos_anticomm hij, map_zero]
  · intro hij
    dsimp [mNeg3]
    rw [← map_mul, ← map_mul, ← map_add, hneg_anticomm hij, map_zero]
  · dsimp [mPos3, mNeg3]
    rw [← map_mul, ← map_mul, ← map_add, hcross_anticomm, map_zero]
  · dsimp [towerGamma3Mat8]
    rw [← map_mul, h5.2.1, map_one]

private def gamma0Sp : SpMat8Z := ⟨![0, 1, 2, 3, 4, 5, 6, 7], ![1, 1, 1, 1, -1, -1, -1, -1]⟩
private def gamma1Sp : SpMat8Z := ⟨![5, 4, 7, 6, 1, 0, 3, 2], ![1, -1, -1, 1, 1, -1, -1, 1]⟩
private def gamma2Sp : SpMat8Z := ⟨![6, 7, 4, 5, 2, 3, 0, 1], ![1, -1, 1, -1, -1, 1, -1, 1]⟩
private def gamma3Sp : SpMat8Z := ⟨![7, 6, 5, 4, 3, 2, 1, 0], ![1, 1, 1, 1, -1, -1, -1, -1]⟩
private def p1Sp : SpMat8Z := ⟨![1, 0, 3, 2, 5, 4, 7, 6], ![1, -1, -1, 1, 1, -1, -1, 1]⟩
private def p2Sp : SpMat8Z := ⟨![2, 3, 0, 1, 6, 7, 4, 5], ![-1, -1, 1, 1, 1, 1, -1, -1]⟩
private def p3Sp : SpMat8Z := ⟨![3, 2, 1, 0, 7, 6, 5, 4], ![-1, 1, -1, 1, 1, -1, 1, -1]⟩
private def g0123Sp : SpMat8Z := ⟨![4, 5, 6, 7, 0, 1, 2, 3], ![1, 1, -1, -1, -1, -1, 1, 1]⟩

private def mPos3Sp : Fin 3 → SpMat8Z
  | ⟨0, _⟩ => ⟨![4, 5, 6, 7, 0, 1, 2, 3], ![1, 1, 1, 1, 1, 1, 1, 1]⟩
  | ⟨1, _⟩ => ⟨![2, 3, 0, 1, 6, 7, 4, 5], ![1, 1, 1, 1, -1, -1, -1, -1]⟩
  | ⟨2, _⟩ => ⟨![1, 0, 3, 2, 5, 4, 7, 6], ![1, 1, -1, -1, -1, -1, 1, 1]⟩

private def mNeg3Sp : Fin 3 → SpMat8Z
  | ⟨0, _⟩ => ⟨![4, 5, 6, 7, 0, 1, 2, 3], ![-1, -1, -1, -1, 1, 1, 1, 1]⟩
  | ⟨1, _⟩ => ⟨![2, 3, 0, 1, 6, 7, 4, 5], ![-1, -1, 1, 1, 1, 1, -1, -1]⟩
  | ⟨2, _⟩ => ⟨![1, 0, 3, 2, 5, 4, 7, 6], ![-1, 1, 1, -1, 1, -1, -1, 1]⟩

private def towerGamma3Sp : SpMat8Z :=
  ⟨![0, 1, 2, 3, 4, 5, 6, 7], ![1, -1, -1, 1, -1, 1, 1, -1]⟩

private theorem gammaSp_toMat (μ : Fin 4) :
    (match μ with | 0 => gamma0Sp | 1 => gamma1Sp | 2 => gamma2Sp | 3 => gamma3Sp).toMat =
      gammaZ μ := by
  fin_cases μ <;> decide

private theorem p1Sp_toMat : p1Sp.toMat = p1Z := by decide
private theorem p2Sp_toMat : p2Sp.toMat = p2Z := by decide
private theorem p3Sp_toMat : p3Sp.toMat = p3Z := by decide
private theorem g0123Sp_toMat : g0123Sp.toMat = gamma0123Z := by decide

private lemma jwSumLast_eq (k : ℕ) :
    jwPos (k + 1) (Fin.last k) + jwNeg (k + 1) (Fin.last k) =
      towerGamma k ⊗ₖ !![(0 : ℝ), 1; 1, 0] := by
  dsimp [jwPos, jwNeg]
  simp only [Fin.lastCases_last]
  rw [← Matrix.kronecker_add]
  congr 1
  ext r c
  fin_cases r <;> fin_cases c
  · change (0 : ℝ) + 0 = 0; norm_num
  · change (0 : ℝ) + 1 = 1; norm_num
  · change (1 : ℝ) + 0 = 1; norm_num
  · change (0 : ℝ) + 0 = 0; norm_num

private lemma jwDiffLast_eq (k : ℕ) :
    jwPos (k + 1) (Fin.last k) - jwNeg (k + 1) (Fin.last k) =
      towerGamma k ⊗ₖ !![(0 : ℝ), -1; 1, 0] := by
  dsimp [jwPos, jwNeg]
  simp only [Fin.lastCases_last]
  ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, ← mul_sub]
  congr 1
  fin_cases a₂ <;> fin_cases b₂
  · change (0 : ℝ) - 0 = 0; norm_num
  · change (0 : ℝ) - 1 = -1; norm_num
  · change (1 : ℝ) - 0 = 1; norm_num
  · change (0 : ℝ) - 0 = 0; norm_num

private lemma jwSumCastSucc_eq (k : ℕ) (i : Fin k) :
    jwPos (k + 1) i.castSucc + jwNeg (k + 1) i.castSucc =
      (jwPos k i + jwNeg k i) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  dsimp [jwPos, jwNeg]
  simp only [Fin.lastCases_castSucc, ← Matrix.add_kronecker]

private lemma jwDiffCastSucc_eq (k : ℕ) (i : Fin k) :
    jwPos (k + 1) i.castSucc - jwNeg (k + 1) i.castSucc =
      (jwPos k i - jwNeg k i) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  dsimp [jwPos, jwNeg]
  simp only [Fin.lastCases_castSucc]
  ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, ← sub_mul]

private def castZ2 (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Int.castRingHom ℝ).mapMatrix A

private def zMatX2 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
private def zMatY2 : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]
private def zMatZ2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

private lemma gammaCut2_eq_castZ2 : gammaCut2 = castZ2 zMatZ2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gammaCut2, castZ2, zMatZ2]

private lemma matX2_eq_castZ2 : !![(0 : ℝ), 1; 1, 0] = castZ2 zMatX2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [castZ2, zMatX2]

private lemma matY2_eq_castZ2 : !![(0 : ℝ), -1; 1, 0] = castZ2 zMatY2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [castZ2, zMatY2]

private def kron3Z (A B C : Matrix (Fin 2) (Fin 2) ℤ) : Mat8Z :=
  Matrix.reindex towerIdx3EquivFin8 towerIdx3EquivFin8
    ((((1 : Matrix (TowerIdx 0) (TowerIdx 0) ℤ) ⊗ₖ A) ⊗ₖ B) ⊗ₖ C)

private lemma reindex_kron3_cast (A B C : Matrix (Fin 2) (Fin 2) ℤ) :
    tower3AlgEquivMat8
        ((((1 : Matrix (TowerIdx 0) (TowerIdx 0) ℝ) ⊗ₖ castZ2 A) ⊗ₖ castZ2 B) ⊗ₖ castZ2 C) =
      castZ8 (kron3Z A B C) := by
  ext r c
  dsimp [tower3AlgEquivMat8, kron3Z, castZ8, castZ2]
  simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, RingHom.mapMatrix_apply]

private lemma mPos3_eq_sp (i : Fin 3) : mPos3 i = castZ8 (mPos3Sp i).toMat := by
  fin_cases i
  · dsimp [mPos3]
    rw [show (0 : Fin 3) = Fin.castSucc (Fin.castSucc (Fin.last 0)) from rfl,
      jwSumCastSucc_eq, jwSumCastSucc_eq, jwSumLast_eq]
    have ht0 : towerGamma 0 = (1 : Matrix (TowerIdx 0) (TowerIdx 0) ℝ) := rfl
    rw [ht0, matX2_eq_castZ2,
      show (1 : Matrix (Fin 2) (Fin 2) ℝ) = castZ2 1 by ext a b; fin_cases a <;> fin_cases b <;> simp [castZ2],
      reindex_kron3_cast]
    congr 1; decide
  · dsimp [mPos3]
    rw [show (1 : Fin 3) = Fin.castSucc (Fin.last 1) from rfl,
      jwSumCastSucc_eq, jwSumLast_eq]
    have ht1 : towerGamma 1 = (1 : Matrix (TowerIdx 0) (TowerIdx 0) ℝ) ⊗ₖ gammaCut2 := rfl
    rw [ht1, gammaCut2_eq_castZ2, matX2_eq_castZ2,
      show (1 : Matrix (Fin 2) (Fin 2) ℝ) = castZ2 1 by ext a b; fin_cases a <;> fin_cases b <;> simp [castZ2],
      reindex_kron3_cast]
    congr 1; decide
  · dsimp [mPos3]
    rw [show (2 : Fin 3) = Fin.last 2 from rfl, jwSumLast_eq]
    have ht2 : towerGamma 2 = ((1 : Matrix (TowerIdx 0) (TowerIdx 0) ℝ) ⊗ₖ gammaCut2) ⊗ₖ gammaCut2 := rfl
    rw [ht2, gammaCut2_eq_castZ2, matX2_eq_castZ2, reindex_kron3_cast]
    congr 1; decide

private lemma mNeg3_eq_sp (i : Fin 3) : mNeg3 i = castZ8 (mNeg3Sp i).toMat := by
  fin_cases i
  · dsimp [mNeg3]
    rw [show (0 : Fin 3) = Fin.castSucc (Fin.castSucc (Fin.last 0)) from rfl,
      jwDiffCastSucc_eq, jwDiffCastSucc_eq, jwDiffLast_eq]
    have ht0 : towerGamma 0 = (1 : Matrix (TowerIdx 0) (TowerIdx 0) ℝ) := rfl
    rw [ht0, matY2_eq_castZ2,
      show (1 : Matrix (Fin 2) (Fin 2) ℝ) = castZ2 1 by ext a b; fin_cases a <;> fin_cases b <;> simp [castZ2],
      reindex_kron3_cast]
    congr 1; decide
  · dsimp [mNeg3]
    rw [show (1 : Fin 3) = Fin.castSucc (Fin.last 1) from rfl,
      jwDiffCastSucc_eq, jwDiffLast_eq]
    have ht1 : towerGamma 1 = (1 : Matrix (TowerIdx 0) (TowerIdx 0) ℝ) ⊗ₖ gammaCut2 := rfl
    rw [ht1, gammaCut2_eq_castZ2, matY2_eq_castZ2,
      show (1 : Matrix (Fin 2) (Fin 2) ℝ) = castZ2 1 by ext a b; fin_cases a <;> fin_cases b <;> simp [castZ2],
      reindex_kron3_cast]
    congr 1; decide
  · dsimp [mNeg3]
    rw [show (2 : Fin 3) = Fin.last 2 from rfl, jwDiffLast_eq]
    have ht2 : towerGamma 2 = ((1 : Matrix (TowerIdx 0) (TowerIdx 0) ℝ) ⊗ₖ gammaCut2) ⊗ₖ gammaCut2 := rfl
    rw [ht2, gammaCut2_eq_castZ2, matY2_eq_castZ2, reindex_kron3_cast]
    congr 1; decide

private lemma towerGamma3Mat8_eq_sp : towerGamma3Mat8 = castZ8 towerGamma3Sp.toMat := by
  dsimp [towerGamma3Mat8]
  have ht3 :
      towerGamma 3 =
        (((1 : Matrix (TowerIdx 0) (TowerIdx 0) ℝ) ⊗ₖ gammaCut2) ⊗ₖ gammaCut2) ⊗ₖ gammaCut2 := rfl
  rw [ht3, gammaCut2_eq_castZ2, reindex_kron3_cast]
  congr 1; decide

/-! ### 4. Verbatim Daviau Monomial Identities in Rung `k = 3` -/

/-- Every Daviau generator (`Γ⁰..Γ³`, `Γ^{0123}`, `P₁..P₃`, `γ₅`, `Γ^(3)`) equals a short
product monomial in the `k = 3` Jordan–Wigner generators `mPos3, mNeg3` verbatim in `M₈(ℝ)`. -/
theorem daviau_generators_as_jw_monomials :
    (gammaR 0 = mPos3 0 * mNeg3 0) ∧
    (InfoGeometry.Canonical.KreinMajoranaBlockInvariance.kreinMetric8 = mPos3 0 * mNeg3 0) ∧
    (gammaR 1 = -(mNeg3 0 * mNeg3 2)) ∧
    (gammaR 2 = -(mPos3 0 * mPos3 1 * mPos3 2 * mNeg3 2)) ∧
    (gammaR 3 = -(mNeg3 0 * mNeg3 1 * mPos3 2)) ∧
    (gamma0123R = -(mNeg3 0 * mPos3 1 * mNeg3 1)) ∧
    (quatPR 0 = -(mPos3 0 * mNeg3 0 * mNeg3 2)) ∧
    (quatPR 1 = mNeg3 1) ∧
    (quatPR 2 = mPos3 0 * mNeg3 0 * mNeg3 1 * mNeg3 2) ∧
    (gamma5Real 2 = mPos3 0 * mPos3 1 * mNeg3 2) ∧
    (towerGamma3Mat8 =
      mPos3 0 * mNeg3 0 * mPos3 1 * mNeg3 1 * mPos3 2 * mNeg3 2) := by
  have hg0 : gammaR 0 = mPos3 0 * mNeg3 0 := by
    dsimp [gammaR]
    rw [mPos3_eq_sp 0, mNeg3_eq_sp 0, ← castZ8_mul, ← SpMat8Z.toMat_mul, ← gammaSp_toMat 0]
    congr 1; decide
  refine ⟨hg0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gamma0R_eq_kreinMetric8.symm.trans hg0
  · dsimp [gammaR]
    rw [mNeg3_eq_sp 0, mNeg3_eq_sp 2, ← castZ8_mul, ← castZ8_neg, ← SpMat8Z.toMat_mul,
      ← gammaSp_toMat 1]
    congr 1; decide
  · dsimp [gammaR]
    rw [mPos3_eq_sp 0, mPos3_eq_sp 1, mPos3_eq_sp 2, mNeg3_eq_sp 2,
      ← castZ8_mul, ← castZ8_mul, ← castZ8_mul, ← castZ8_neg,
      ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul, ← gammaSp_toMat 2]
    congr 1; decide
  · dsimp [gammaR]
    rw [mNeg3_eq_sp 0, mNeg3_eq_sp 1, mPos3_eq_sp 2,
      ← castZ8_mul, ← castZ8_mul, ← castZ8_neg,
      ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul, ← gammaSp_toMat 3]
    congr 1; decide
  · dsimp [gamma0123R]
    rw [mNeg3_eq_sp 0, mPos3_eq_sp 1, mNeg3_eq_sp 1,
      ← castZ8_mul, ← castZ8_mul, ← castZ8_neg,
      ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul, ← g0123Sp_toMat]
    congr 1; decide
  · dsimp [quatPR, quatPZ]
    rw [mPos3_eq_sp 0, mNeg3_eq_sp 0, mNeg3_eq_sp 2,
      ← castZ8_mul, ← castZ8_mul, ← castZ8_neg,
      ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul, ← p1Sp_toMat]
    congr 1; decide
  · dsimp [quatPR, quatPZ]
    rw [mNeg3_eq_sp 1, ← p2Sp_toMat]
    rfl
  · dsimp [quatPR, quatPZ]
    rw [mPos3_eq_sp 0, mNeg3_eq_sp 0, mNeg3_eq_sp 1, mNeg3_eq_sp 2,
      ← castZ8_mul, ← castZ8_mul, ← castZ8_mul,
      ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul, ← p3Sp_toMat]
    congr 1; decide
  · dsimp [gamma5Real, gamma0123R, quatPR, quatPZ]
    rw [mPos3_eq_sp 0, mPos3_eq_sp 1, mNeg3_eq_sp 2,
      ← g0123Sp_toMat, ← p3Sp_toMat, ← castZ8_mul, ← castZ8_mul, ← castZ8_mul,
      ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul]
    congr 1; decide
  · rw [towerGamma3Mat8_eq_sp, mPos3_eq_sp 0, mNeg3_eq_sp 0, mPos3_eq_sp 1, mNeg3_eq_sp 1,
      mPos3_eq_sp 2, mNeg3_eq_sp 2,
      ← castZ8_mul, ← castZ8_mul, ← castZ8_mul, ← castZ8_mul, ← castZ8_mul,
      ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul,
      ← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_mul]
    congr 1; decide

/-! ### 5. Abstract Realization Inside `SplitClPower 3 ≅ ⊗ᵍ^3 Cl(1,1)` -/

/-- Daviau Dirac generators `Γ^μ` inside the abstract `3`-fold graded tensor power `SplitClPower 3`. -/
def daviauGammaInSplitCl3 (μ : Fin 4) : SplitClPower 3 :=
  (splitClPowerEquivMat 3).symm (gammaR μ)

/-- Daviau quaternionic commutant `{P₁, P₂, P₃}` inside `SplitClPower 3`. -/
def daviauQuatInSplitCl3 (j : Fin 3) : SplitClPower 3 :=
  (splitClPowerEquivMat 3).symm (quatPR j)

/-- Daviau left chiral Peirce projectors `p_j` inside `SplitClPower 3`. -/
def daviauPeirceLeftInSplitCl3 (j : Fin 3) : SplitClPower 3 :=
  (splitClPowerEquivMat 3).symm (peirceLeft j)

/-- Daviau right chiral Peirce projectors `p'_j` inside `SplitClPower 3`. -/
def daviauPeirceRightInSplitCl3 (j : Fin 3) : SplitClPower 3 :=
  (splitClPowerEquivMat 3).symm (peirceRight j)

/-- Complete structural transfer theorem: the abstract `3`-fold graded Clifford power
`SplitClPower 3 ≅ ⊗ᵍ^3 Cl(1,1)` simultaneously carries Daviau's Clifford algebra `{Γ^μ, Γ^ν}`,
quaternionic commutant `{P₁, P₂, P₃}`, and orthogonal chiral Peirce decompositions `(p_j, p'_j)`. -/
theorem daviau_realDirac_in_cl11_tower_rung3 (μ ν : Fin 4) (j : Fin 3) :
    (daviauGammaInSplitCl3 μ * daviauGammaInSplitCl3 ν +
        daviauGammaInSplitCl3 ν * daviauGammaInSplitCl3 μ =
      (if μ = ν then 2 * minkowskiMetricR μ else 0) • (1 : SplitClPower 3)) ∧
    (daviauGammaInSplitCl3 μ * daviauQuatInSplitCl3 j =
      daviauQuatInSplitCl3 j * daviauGammaInSplitCl3 μ) ∧
    (daviauQuatInSplitCl3 j * daviauQuatInSplitCl3 j = -(1 : SplitClPower 3)) ∧
    (daviauQuatInSplitCl3 0 * daviauQuatInSplitCl3 1 = daviauQuatInSplitCl3 2) ∧
    (daviauPeirceLeftInSplitCl3 j * daviauPeirceLeftInSplitCl3 j =
      daviauPeirceLeftInSplitCl3 j) ∧
    (daviauPeirceRightInSplitCl3 j * daviauPeirceRightInSplitCl3 j =
      daviauPeirceRightInSplitCl3 j) ∧
    (daviauPeirceLeftInSplitCl3 j * daviauPeirceRightInSplitCl3 j = 0) ∧
    (daviauPeirceLeftInSplitCl3 j + daviauPeirceRightInSplitCl3 j = (1 : SplitClPower 3)) := by
  dsimp [daviauGammaInSplitCl3, daviauQuatInSplitCl3, daviauPeirceLeftInSplitCl3,
    daviauPeirceRightInSplitCl3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, ← map_add, gammaR_anticomm μ ν, map_smul, map_one]
  · rw [← map_mul, ← map_mul, gammaR_comm_quatPR μ j]
  · rw [← map_mul, quatPR_sq j, map_neg, map_one]
  · rw [← map_mul, quatPR_01]
  · rw [← map_mul, peirceLeft_idem j]
  · rw [← map_mul, peirceRight_idem j]
  · rw [← map_mul, peirceLeft_mul_peirceRight j, map_zero]
  · rw [← map_add, peirceLeft_add_peirceRight j, map_one]

/-! ### 6. R2-Gap1 Contract Reconciliation -/

/-- **`R2-Gap1` Reconciliation**: Canonical split Clifford algebra isomorphism identifying
the recursive generator algebra `Cl_split 3 = CliffordAlgebra (SplitQuad 3)` with `M₈(ℝ)`. -/
noncomputable def clSplit3AlgEquivMat8 :
    InfoGeometry.Clifford.SpinorRep.Cl_split 3 ≃ₐ[ℝ] Mat8R :=
  InfoGeometry.Clifford.SplitCliffordMatrixEquiv.splitSpinorAlgEquiv 3

/-- Identification of `Cl_split 3` with rung `k = 3` of the `Cl(1,1)` matrix tower. -/
noncomputable def clSplit3EquivTower3 :
    InfoGeometry.Clifford.SpinorRep.Cl_split 3 ≃ₐ[ℝ] Matrix (TowerIdx 3) (TowerIdx 3) ℝ :=
  clSplit3AlgEquivMat8.trans tower3AlgEquivMat8.symm

/-- Transitive algebra equivalence identifying `Cl_split 3` with the abstract graded tensor
power `SplitClPower 3 ≅ ⊗ᵍ^3 Cl(1,1)`. -/
noncomputable def clSplit3EquivSplitClPower3 :
    InfoGeometry.Clifford.SpinorRep.Cl_split 3 ≃ₐ[ℝ] SplitClPower 3 :=
  clSplit3EquivTower3.trans splitCl3EquivTower3.symm

theorem clSplit3_reconciliation_packet :
    (clSplit3AlgEquivMat8.trans tower3AlgEquivMat8.symm = clSplit3EquivTower3) ∧
    (clSplit3EquivTower3.trans splitCl3EquivTower3.symm = clSplit3EquivSplitClPower3) :=
  ⟨rfl, rfl⟩

/-! ### 7. Curved `ℤ/2`-Graded DG Differential `∂_F` on Rung `k = 3` (`M₈(ℝ)`) -/

/-- Chiral parity conjugation `α(A) = γ₅ A γ₅` on `M₈(ℝ)` using `γ₅ = gamma5Real 2`. -/
def rung3ParityConj (A : Mat8R) : Mat8R :=
  parityConj (gamma5Real 2) A

/-- Curved `ℤ/2`-graded differential `∂_F(A) = F A - (γ₅ A γ₅) F` on `M₈(ℝ)`. -/
def rung3CurvedDiff (F A : Mat8R) : Mat8R :=
  gradedInnerDiff (gamma5Real 2) F A

/-- Rung-3 curved DG package: graded Leibniz rule, `∂_F²(A) = [F², A]`, Bianchi identity
`∂_F(F²) = 0`, and centrality characterization for any `γ₅`-odd operator `F ∈ M₈(ℝ)`. -/
theorem rung3CurvedDiff_leibniz_sq_and_bianchi {F : Mat8R}
    (hF : rung3ParityConj F = -F) (A B : Mat8R) :
    (rung3CurvedDiff F (A * B) =
      rung3CurvedDiff F A * B + rung3ParityConj A * rung3CurvedDiff F B) ∧
    (rung3CurvedDiff F (rung3CurvedDiff F A) = (F * F) * A - A * (F * F)) ∧
    (rung3CurvedDiff F (F * F) = 0) ∧
    ((∀ X : Mat8R, rung3CurvedDiff F (rung3CurvedDiff F X) = 0) ↔
      (∀ X : Mat8R, (F * F) * X = X * (F * F))) :=
  ⟨gradedInnerDiff_mul (gamma5Real_sq 2) F A B,
    gradedInnerDiff_sq (gamma5Real_sq 2) hF A,
    gradedInnerDiff_curvature_closed (gamma5Real_sq 2) hF,
    gradedInnerDiff_sq_eq_zero_iff_central (gamma5Real_sq 2) hF⟩

/-- Every Daviau Dirac matrix `Γ^μ` (`gammaR μ`) is `γ₅`-odd (`γ₅ Γ^μ γ₅ = -Γ^μ`) with central
square `(Γ^μ)² = g^{μμ} I₈`, so its graded differential satisfies `∂_{Γ^μ}² = 0` on all of `M₈(ℝ)`. -/
theorem rung3_gammaR_is_chiral_odd_and_curvedDiff_sq_zero (μ : Fin 4) :
    rung3ParityConj (gammaR μ) = -gammaR μ ∧
    (∀ A : Mat8R, rung3CurvedDiff (gammaR μ) (rung3CurvedDiff (gammaR μ) A) = 0) := by
  have hodd : rung3ParityConj (gammaR μ) = -gammaR μ := by
    dsimp [rung3ParityConj, parityConj]
    have hanti : gamma5Real 2 * gammaR μ = -(gammaR μ * gamma5Real 2) :=
      eq_neg_of_add_eq_zero_left (gamma5Real_anticomm 2 μ)
    rw [hanti, neg_mul, Matrix.mul_assoc, gamma5Real_sq 2, Matrix.mul_one]
  have h2sq : gammaR μ * gammaR μ + gammaR μ * gammaR μ =
      (2 * minkowskiMetricR μ) • (1 : Mat8R) := by
    simpa using gammaR_anticomm μ μ
  have hsq : gammaR μ * gammaR μ = minkowskiMetricR μ • (1 : Mat8R) := by
    have hhalf := congrArg (fun M : Mat8R => (1 / 2 : ℝ) • M) h2sq
    rw [← two_smul ℝ (gammaR μ * gammaR μ), smul_smul, smul_smul,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul,
      show (1 / 2 : ℝ) * (2 * minkowskiMetricR μ) = minkowskiMetricR μ by ring] at hhalf
    exact hhalf
  refine ⟨hodd, ?_⟩
  intro A
  rw [(rung3CurvedDiff_leibniz_sq_and_bianchi hodd A 1).2.1, hsq,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Matrix.one_mul, Matrix.mul_one, sub_self]

end InfoGeometry.Clifford.DaviauCl11TowerRung3Bridge
