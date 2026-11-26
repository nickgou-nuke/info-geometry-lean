/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.H3ZornTKKLieAlgebra
import InfoGeometry.Algebra.H3ZornE6RootSystem
import Mathlib.Algebra.Lie.Weights.Cartan

/-!
# 7D Split Cartan Subalgebra and 126-Root System for `𝔈₇(7)` (`H3ZornTKKLie`)

On the 133-dimensional split real exceptional Lie algebra `H3ZornTKKLie` (`𝔈₇(7)`), this module
constructs:
1. The trace-dual basis involution `traceDualIdx` on `Fin 27` and weight injectivity of
   `h3zornWeight`.
2. The 7 simple Chevalley triples `(e7SimpleE i, e7SimpleF i, e7SimpleH i)` (`i : Fin 7`),
   extending `e6SimpleE/F/H` (`i < 6`) by `e7SimpleE 6 := negInj (h3ZornBasis 10)` and
   `e7SimpleF 6 := (2 : ℝ) • posInj (h3ZornBasis 3)`.
3. The 7D split Cartan subalgebra `h3zornE7Cartan` (`IsLieAbelian`, `finrank = 7`, equal to
   `h3zornCartan ⊕ ℝ·h3zornTKKGradeOp`).
4. All 126 root vectors `e7RootVec : Fin 126 → H3ZornTKKLie` (`72` grade-`0`, `27` grade-`-1`,
   `27` grade-`+1`), root coordinates `e7RootCoord` matching `CFSGPort.Chevalley.IsRoot .E7`,
   weights `h3zornE7RootWeight`, exact eigenvalues `e7RootEigenvalue`, and the 133D basis
   `e7ChevalleyBasis : Module.Basis (Fin 7 ⊕ Fin 126) ℝ H3ZornTKKLie`.
5. `IsCartanSubalgebra` and `LieModule.IsTriangularizable ℝ h3zornE7Cartan H3ZornTKKLie`, plus
   Vandermonde weight-killing, opposite-root Cartan brackets, and `E₇` Serre/Cartan relations
   supporting `H3ZornE7Simplicity`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit
open InfoGeometry.Canonical.H3ZornTKKLieAlgebra
open InfoGeometry.Exceptional.CFSGPort.Chevalley

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private instance : Module.Finite ℝ (H3Zorn ℝ) :=
  Module.Finite.of_basis h3ZornBasis

private instance : Module.Finite ℝ h3zornCubicStabilizer :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_h3zornCubicStabilizer]; decide)

private instance : Module.Finite ℝ H3ZornTKKLie :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_H3ZornTKKLie]; decide)

section TraceDualAndWeights

/-- Trace-pairing involution on `zorn_basis` (`zornBilinInt i j ≠ 0 ↔ j = zornDualIdx i`). -/
def zornDualIdx (i : Fin 8) : Fin 8 :=
  match i.val with
  | 0 => 7 | 1 => 4 | 2 => 5 | 3 => 6
  | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 0
  | _ => 0

theorem zornDualIdx_involutive (i : Fin 8) : zornDualIdx (zornDualIdx i) = i := by
  fin_cases i <;> rfl

theorem zornBilinInt_zornDualIdx_eq_zero {i j : Fin 8} (hij : j ≠ i) :
    zornBilinInt (zornDualIdx i) j = 0 := by
  have hchk : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      if j = i then true else zornBilinInt (zornDualIdx i) j == 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have h := hchk i j
  simp only [hij, ↓reduceIte, beq_iff_eq] at h
  exact h

/-- Trace-pairing involution on the 27 basis indices `h3ZornBasis`. -/
def traceDualIdx (k : Fin 27) : Fin 27 :=
  match sectorOfFin k with
  | .diag d => finOfSector (.diag d)
  | .j12 i => finOfSector (.j12 (zornDualIdx i))
  | .j23 i => finOfSector (.j23 (zornDualIdx i))
  | .j31 i => finOfSector (.j31 (zornDualIdx i))

@[simp] theorem traceDualIdx_involutive (k : Fin 27) : traceDualIdx (traceDualIdx k) = k := by
  have hchk : (List.finRange 27).all (fun k => traceDualIdx (traceDualIdx k) == k) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
  exact hchk k

theorem traceDualIdx_bijective : Function.Bijective traceDualIdx :=
  Function.Involutive.bijective traceDualIdx_involutive

private theorem zornBilin_zero_left' (x : ZornVectorMatrix ℝ) :
    zornBilin (0 : ZornVectorMatrix ℝ) x = 0 := by
  change ZornVectorMatrix.trace (ZornVectorMatrix.mul 0 (ZornVectorMatrix.conj x)) = 0
  simp [ZornVectorMatrix.zero_mul]

private theorem zornBilin_zero_right' (x : ZornVectorMatrix ℝ) :
    zornBilin x (0 : ZornVectorMatrix ℝ) = 0 := by
  change ZornVectorMatrix.trace (ZornVectorMatrix.mul x (ZornVectorMatrix.conj 0)) = 0
  simp [ZornVectorMatrix.conj_zero, ZornVectorMatrix.mul_zero]

private theorem zornBilin_zero_zero :
    ZornVectorMatrix.trace (ZornVectorMatrix.mul (0 : ZornVectorMatrix ℝ)
      (ZornVectorMatrix.conj 0)) = 0 := by
  change zornBilin (0 : ZornVectorMatrix ℝ) 0 = 0
  exact zornBilin_zero_left' 0

private theorem traceBilin_sector (s₁ s₂ : H3Sector) :
    traceBilin (h3ZornBasis (finOfSector s₁)) (h3ZornBasis (finOfSector s₂)) =
      match s₁, s₂ with
      | .diag d₁, .diag d₂ => if d₁ = d₂ then 1 else 0
      | .j12 i, .j12 j => (zornBilinInt i j : ℝ)
      | .j23 i, .j23 j => (zornBilinInt i j : ℝ)
      | .j31 i, .j31 j => (zornBilinInt i j : ℝ)
      | _, _ => 0 := by
  cases s₁ with
  | diag d₁ =>
    cases s₂ with
    | diag d₂ =>
      fin_cases d₁ <;> fin_cases d₂ <;>
        simp [h3ZornBasis_sector, traceBilin, h3_diag₁, h3_diag₂, h3_diag₃]
    | j12 j =>
      fin_cases d₁ <;>
        simp [h3ZornBasis_sector, traceBilin, h3_diag₁, h3_diag₂, h3_diag₃, embedJ12]
    | j23 j =>
      fin_cases d₁ <;>
        simp [h3ZornBasis_sector, traceBilin, h3_diag₁, h3_diag₂, h3_diag₃, embedJ23]
    | j31 j =>
      fin_cases d₁ <;>
        simp [h3ZornBasis_sector, traceBilin, h3_diag₁, h3_diag₂, h3_diag₃, embedJ31]
  | j12 i =>
    cases s₂ with
    | diag d₂ =>
      fin_cases d₂ <;>
        simp [h3ZornBasis_sector, traceBilin, h3_diag₁, h3_diag₂, h3_diag₃, embedJ12]
    | j12 j =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector]
      dsimp only [traceBilin, embedJ12]
      rw [zornBilin_zero_zero]
      simp only [zero_mul, add_zero, zero_add]
      exact zornBilin_zorn_basis i j
    | j23 j =>
      simp [h3ZornBasis_sector, traceBilin, embedJ12, embedJ23]
    | j31 j =>
      simp [h3ZornBasis_sector, traceBilin, embedJ12, embedJ31]
  | j23 i =>
    cases s₂ with
    | diag d₂ =>
      fin_cases d₂ <;>
        simp [h3ZornBasis_sector, traceBilin, h3_diag₁, h3_diag₂, h3_diag₃, embedJ23]
    | j12 j =>
      simp [h3ZornBasis_sector, traceBilin, embedJ23, embedJ12]
    | j23 j =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector]
      dsimp only [traceBilin, embedJ23]
      rw [zornBilin_zero_zero]
      simp only [zero_mul, zero_add, add_zero]
      exact zornBilin_zorn_basis i j
    | j31 j =>
      simp [h3ZornBasis_sector, traceBilin, embedJ23, embedJ31]
  | j31 i =>
    cases s₂ with
    | diag d₂ =>
      fin_cases d₂ <;>
        simp [h3ZornBasis_sector, traceBilin, h3_diag₁, h3_diag₂, h3_diag₃, embedJ31]
    | j12 j =>
      simp [h3ZornBasis_sector, traceBilin, embedJ31, embedJ12]
    | j23 j =>
      simp [h3ZornBasis_sector, traceBilin, embedJ31, embedJ23]
    | j31 j =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector]
      dsimp only [traceBilin, embedJ31]
      rw [zornBilin_zero_zero]
      simp only [zero_mul, zero_add]
      exact zornBilin_zorn_basis i j

private theorem traceDualIdx_finOfSector (s : H3Sector) :
    traceDualIdx (finOfSector s) = finOfSector (match s with
      | .diag d => .diag d
      | .j12 i => .j12 (zornDualIdx i)
      | .j23 i => .j23 (zornDualIdx i)
      | .j31 i => .j31 (zornDualIdx i)) := by
  cases s with
  | diag d => fin_cases d <;> rfl
  | j12 i => fin_cases i <;> rfl
  | j23 i => fin_cases i <;> rfl
  | j31 i => fin_cases i <;> rfl

theorem traceBilin_h3ZornBasis_ne_dual (k m : Fin 27) (hm : m ≠ k) :
    traceBilin (h3ZornBasis (traceDualIdx k)) (h3ZornBasis m) = 0 := by
  have hne : sectorOfFin m ≠ sectorOfFin k := by
    intro heq
    apply hm
    rw [← finOfSector_sectorOfFin m, ← finOfSector_sectorOfFin k, heq]
  conv_lhs =>
    rw [← finOfSector_sectorOfFin k, ← finOfSector_sectorOfFin m, traceDualIdx_finOfSector]
  rw [traceBilin_sector]
  cases hk : sectorOfFin k with
  | diag d₁ =>
    cases hm' : sectorOfFin m with
    | diag d₂ =>
      have hd : d₁ ≠ d₂ := fun h => hne (by rw [hk, hm', h])
      simp [hd]
    | j12 _ => rfl
    | j23 _ => rfl
    | j31 _ => rfl
  | j12 i =>
    cases hm' : sectorOfFin m with
    | diag _ => rfl
    | j12 j =>
      have hj : j ≠ i := fun h => hne (by rw [hk, hm', h])
      simp [zornBilinInt_zornDualIdx_eq_zero hj]
    | j23 _ => rfl
    | j31 _ => rfl
  | j23 i =>
    cases hm' : sectorOfFin m with
    | diag _ => rfl
    | j12 _ => rfl
    | j23 j =>
      have hj : j ≠ i := fun h => hne (by rw [hk, hm', h])
      simp [zornBilinInt_zornDualIdx_eq_zero hj]
    | j31 _ => rfl
  | j31 i =>
    cases hm' : sectorOfFin m with
    | diag _ => rfl
    | j12 _ => rfl
    | j23 _ => rfl
    | j31 j =>
      have hj : j ≠ i := fun h => hne (by rw [hk, hm', h])
      simp [zornBilinInt_zornDualIdx_eq_zero hj]

theorem h3zornWeight_injective : Function.Injective h3zornWeight := by
  have hchk : (List.finRange 27).all (fun k₁ => (List.finRange 27).all (fun k₂ =>
      if k₁ = k₂ then true else
        (List.finRange 6).any (fun i => h3zornWeight k₁ i != h3zornWeight k₂ i))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  intro k₁ k₂ heq
  by_contra hne
  have h12 := hchk k₁ k₂
  simp only [hne, ↓reduceIte, List.any_eq_true, List.mem_finRange, true_and, bne_iff_ne,
    ne_eq] at h12
  obtain ⟨i, hi⟩ := h12
  exact hi (congrFun heq i)

end TraceDualAndWeights

section SimpleTriplesAndNode6

/-- The 7 simple Chevalley `E` generators in `H3ZornTKKLie`. -/
def e7SimpleE (i : Fin 7) : H3ZornTKKLie :=
  if hi : i.val < 6 then h3zornCubicStabilizerToTKK (e6SimpleE ⟨i.val, hi⟩)
  else negInj (h3ZornBasis 10)

/-- The 7 simple Chevalley `F` generators in `H3ZornTKKLie`. -/
def e7SimpleF (i : Fin 7) : H3ZornTKKLie :=
  if hi : i.val < 6 then h3zornCubicStabilizerToTKK (e6SimpleF ⟨i.val, hi⟩)
  else (2 : ℝ) • posInj (h3ZornBasis 3)

/-- The 7 simple Chevalley Cartan generators `Hᵢ = ⁅Eᵢ, Fᵢ⁆` in `H3ZornTKKLie`. -/
def e7SimpleH (i : Fin 7) : H3ZornTKKLie :=
  ⁅e7SimpleE i, e7SimpleF i⁆

theorem e7SimpleE_castSucc (i : Fin 6) :
    e7SimpleE i.castSucc = h3zornCubicStabilizerToTKK (e6SimpleE i) := by
  simp [e7SimpleE, i.isLt]

theorem e7SimpleF_castSucc (i : Fin 6) :
    e7SimpleF i.castSucc = h3zornCubicStabilizerToTKK (e6SimpleF i) := by
  simp [e7SimpleF, i.isLt]

theorem e7SimpleH_castSucc (i : Fin 6) :
    e7SimpleH i.castSucc = h3zornCubicStabilizerToTKK (e6SimpleH i) := by
  rw [e7SimpleH, e7SimpleE_castSucc, e7SimpleF_castSucc, ← LieHom.map_lie,
    e6Simple_bracket_EF_same]

theorem e7SimpleE_six : e7SimpleE 6 = negInj (h3ZornBasis 10) := rfl
theorem e7SimpleF_six : e7SimpleF 6 = (2 : ℝ) • posInj (h3ZornBasis 3) := rfl

theorem e7SimpleH_six :
    e7SimpleH 6 =
      zeroInj ⟨(2 : ℝ) • JordanTKK.tripleD ℝ (h3ZornBasis 10) (h3ZornBasis 3),
        h3zornTKKDatum.str.smul_mem 2 (h3zornTKKDatum.tripleD_mem_str _ _)⟩ := by
  rw [e7SimpleH, e7SimpleE_six, e7SimpleF_six, lie_smul, negInj_bracket_posInj, ← map_smul]
  rfl

/-- Diagonal eigenvalues of `2 • tripleD ℝ (h3ZornBasis 10) (h3ZornBasis 3)` on `h3ZornBasis`. -/
def e7H6Weight (k : Fin 27) : ℤ :=
  match k.val with
  | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1
  | 9 => 1 | 10 => 2 | 11 => 1 | 12 => 1 | 13 => 1 | 14 => 1 | 15 => 0 | 16 => 0 | 17 => 0
  | 18 => 0 | 19 => 1 | 20 => 0 | 21 => 0 | 22 => 0 | 23 => 1 | 24 => 1 | 25 => 1 | 26 => 0
  | _ => 0

def e7H6Sparse : SparseMat27 :=
  [(0, 0, 1), (1, 1, 1), (4, 4, 1), (5, 5, 1), (6, 6, 1), (7, 7, 1), (8, 8, 1), (9, 9, 1),
   (10, 10, 2), (11, 11, 1), (12, 12, 1), (13, 13, 1), (14, 14, 1), (19, 19, 1), (23, 23, 1),
   (24, 24, 1), (25, 25, 1)]

private theorem h3ZornBasis_10_mul_3 :
    h3ZornBasis 10 * h3ZornBasis 3 = (1 / 2 : ℝ) • (h3ZornBasis 0 + h3ZornBasis 1) := by
  have h10 : h3ZornBasis 10 = embedJ12 (zorn_basis 7) := h3ZornBasis_12 7
  have h3 : h3ZornBasis 3 = embedJ12 (zorn_basis 0) := h3ZornBasis_12 0
  have h0 : h3ZornBasis 0 = h3_diag₁ := h3ZornBasis_zero
  have h1 : h3ZornBasis 1 = h3_diag₂ := h3ZornBasis_one
  rw [h10, h3, h0, h1, embedJ12_mul_embedJ12, zornBilin_zorn_basis 7 0]
  have hz : zornBilinInt 7 0 = 1 := rfl
  rw [hz, Int.cast_one, mul_one]

private theorem h3zornToMatrix_four_inner_basis (p q : Fin 27) :
    h3zornToMatrix ((4 : ℝ) • jordanInnerDerivation (R := ℝ) (h3ZornBasis p) (h3ZornBasis q)) =
      (sparseToMat (sparseComm (twoLData p) (twoLData q))).map Int.cast := by
  have hinner : jordanInnerDerivation (R := ℝ) (h3ZornBasis p) (h3ZornBasis q) =
      jordanLmul (R := ℝ) (h3ZornBasis p) * jordanLmul (R := ℝ) (h3ZornBasis q) -
        jordanLmul (R := ℝ) (h3ZornBasis q) * jordanLmul (R := ℝ) (h3ZornBasis p) := by
    apply LinearMap.ext; intro x
    change h3ZornBasis p * (h3ZornBasis q * x) - h3ZornBasis q * (h3ZornBasis p * x) =
      (h3ZornBasis p * (h3ZornBasis q * x) - h3ZornBasis q * (h3ZornBasis p * x))
    rfl
  have h4 : (4 : ℝ) • (jordanLmul (R := ℝ) (h3ZornBasis p) * jordanLmul (R := ℝ) (h3ZornBasis q) -
        jordanLmul (R := ℝ) (h3ZornBasis q) * jordanLmul (R := ℝ) (h3ZornBasis p)) =
      ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis p)) *
        ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis q)) -
      ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis q)) *
        ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis p)) := by
    simp only [smul_sub, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    norm_num
  rw [hinner, h4, map_sub, map_mul, map_mul, h3zornToMatrix_two_jordanLmul_basis p,
    h3zornToMatrix_two_jordanLmul_basis q, sparseToMat_comm]
  ext i j
  simp [Matrix.mul_apply]

private def e7H6RowCheck (r : Fin 27) : Bool :=
  (List.finRange 27).all fun c =>
    2 * sparseVal e7H6Sparse r c ==
      sparseVal (twoLData 0) r c + sparseVal (twoLData 1) r c +
        (∑ k : Fin 27, sparseVal (twoLData 10) r k * sparseVal (twoLData 3) k c -
          ∑ k : Fin 27, sparseVal (twoLData 3) r k * sparseVal (twoLData 10) k c)

private theorem e7H6RowCheck_lt9 :
    ((List.finRange 9).all fun n => e7H6RowCheck ⟨n.val, by omega⟩) = true := by decide
private theorem e7H6RowCheck_9_18 :
    ((List.finRange 9).all fun n => e7H6RowCheck ⟨n.val + 9, by omega⟩) = true := by decide
private theorem e7H6RowCheck_18_27 :
    ((List.finRange 9).all fun n => e7H6RowCheck ⟨n.val + 18, by omega⟩) = true := by decide

private theorem e7H6Sparse_mat_eq :
    sparseToMat (sparseSmul 2 e7H6Sparse) =
      sparseToMat (sparseAdd (sparseAdd (twoLData 0) (twoLData 1))
        (sparseComm (twoLData 10) (twoLData 3))) := by
  ext r c
  change sparseVal (sparseSmul 2 e7H6Sparse) r c =
    sparseVal (sparseAdd (sparseAdd (twoLData 0) (twoLData 1))
      (sparseComm (twoLData 10) (twoLData 3))) r c
  rw [sparseVal_smul, sparseVal_add, sparseVal_add, sparseComm, sparseVal_sub,
    sparseVal_mul, sparseVal_mul]
  have hrow : e7H6RowCheck r = true := by
    by_cases hr9 : r.val < 9
    · have h1 := e7H6RowCheck_lt9
      simp only [List.all_eq_true, List.mem_finRange, true_implies] at h1
      simpa using h1 ⟨r.val, hr9⟩
    · by_cases hr18 : r.val < 18
      · have h2 := e7H6RowCheck_9_18
        simp only [List.all_eq_true, List.mem_finRange, true_implies] at h2
        have hr' : r.val - 9 < 9 := by omega
        have heq : (⟨(⟨r.val - 9, hr'⟩ : Fin 9).val + 9, by omega⟩ : Fin 27) = r :=
          Fin.ext (by dsimp; omega)
        simpa [heq] using h2 ⟨r.val - 9, hr'⟩
      · have h3 := e7H6RowCheck_18_27
        simp only [List.all_eq_true, List.mem_finRange, true_implies] at h3
        have hr' : r.val - 18 < 9 := by omega
        have heq : (⟨(⟨r.val - 18, hr'⟩ : Fin 9).val + 18, by omega⟩ : Fin 27) = r :=
          Fin.ext (by dsimp; omega)
        simpa [heq] using h3 ⟨r.val - 18, hr'⟩
  dsimp [e7H6RowCheck] at hrow
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hrow
  exact hrow c

theorem h3zornToMatrix_two_tripleD_10_3 :
    h3zornToMatrix ((2 : ℝ) • JordanTKK.tripleD ℝ (h3ZornBasis 10) (h3ZornBasis 3)) =
      (sparseToMat e7H6Sparse).map Int.cast := by
  have h4 : (4 : ℝ) • JordanTKK.tripleD ℝ (h3ZornBasis 10) (h3ZornBasis 3) =
      ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis 0) +
        (2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis 1)) +
      (4 : ℝ) • jordanInnerDerivation (R := ℝ) (h3ZornBasis 10) (h3ZornBasis 3) := by
    rw [JordanTKK.tripleD_eq_jordanLmul_add_innerDerivation, smul_add, h3ZornBasis_10_mul_3]
    congr 1
    apply LinearMap.ext; intro x
    simp only [LinearMap.smul_apply, LinearMap.add_apply, jordanLmul_apply, smul_add,
      smul_mul_assoc, add_mul, smul_smul]
    norm_num
  have hm4 : h3zornToMatrix ((4 : ℝ) • JordanTKK.tripleD ℝ (h3ZornBasis 10) (h3ZornBasis 3)) =
      (sparseToMat (sparseSmul 2 e7H6Sparse)).map Int.cast := by
    have hsum_mat : (sparseToMat (twoLData 0)).map (Int.cast : ℤ → ℝ) +
          (sparseToMat (twoLData 1)).map Int.cast +
          (sparseToMat (sparseComm (twoLData 10) (twoLData 3))).map Int.cast =
        (sparseToMat (sparseAdd (sparseAdd (twoLData 0) (twoLData 1))
          (sparseComm (twoLData 10) (twoLData 3)))).map Int.cast := by
      rw [sparseToMat_add, sparseToMat_add]
      ext r c; simp only [Matrix.add_apply, Matrix.map_apply, Int.cast_add]
    rw [h4, map_add, map_add, h3zornToMatrix_two_jordanLmul_basis 0,
      h3zornToMatrix_two_jordanLmul_basis 1, h3zornToMatrix_four_inner_basis 10 3,
      hsum_mat, ← e7H6Sparse_mat_eq]
  have h2' : (2 : ℝ) • h3zornToMatrix ((2 : ℝ) • JordanTKK.tripleD ℝ (h3ZornBasis 10)
        (h3ZornBasis 3)) =
      (2 : ℝ) • (sparseToMat e7H6Sparse).map Int.cast := by
    rw [← map_smul, show (2 : ℝ) • ((2 : ℝ) • JordanTKK.tripleD ℝ (h3ZornBasis 10)
        (h3ZornBasis 3)) = (4 : ℝ) • JordanTKK.tripleD ℝ (h3ZornBasis 10) (h3ZornBasis 3) by
      rw [smul_smul]; norm_num, hm4, sparseToMat_smul]
    ext r c
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_ofNat]
  exact smul_right_injective _ (two_ne_zero : (2 : ℝ) ≠ 0) h2'

theorem e7H6Sparse_diag (r c : Fin 27) :
    sparseToMat e7H6Sparse r c = if r = c then e7H6Weight r else 0 := by
  have h : (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseToMat e7H6Sparse r c == if r = c then e7H6Weight r else 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h r c

theorem two_tripleD_10_3_apply_basis (k : Fin 27) :
    ((2 : ℝ) • JordanTKK.tripleD ℝ (h3ZornBasis 10) (h3ZornBasis 3)) (h3ZornBasis k) =
      (e7H6Weight k : ℝ) • h3ZornBasis k := by
  apply h3ZornBasis.ext_elem
  intro r
  have h1 : h3ZornBasis.repr (((2 : ℝ) • JordanTKK.tripleD ℝ (h3ZornBasis 10) (h3ZornBasis 3))
      (h3ZornBasis k)) r =
      h3zornToMatrix ((2 : ℝ) • JordanTKK.tripleD ℝ (h3ZornBasis 10) (h3ZornBasis 3)) r k := by
    rw [h3zornToMatrix_apply]; rfl
  rw [h1, h3zornToMatrix_two_tripleD_10_3, Matrix.map_apply, e7H6Sparse_diag, map_smul,
    Finsupp.smul_apply, h3ZornBasis.repr_self, Finsupp.single_apply, smul_eq_mul]
  by_cases hrk : r = k
  · subst hrk; simp
  · have hkr : k ≠ r := fun h => hrk h.symm
    simp [hrk, hkr]

private theorem e7GradeOp_weight_identity (k : Fin 27) :
    2 * h3zornWeight k 0 + 3 * h3zornWeight k 1 + 4 * h3zornWeight k 2 +
      6 * h3zornWeight k 3 + 5 * h3zornWeight k 4 + 4 * h3zornWeight k 5 +
      3 * e7H6Weight k = 2 := by
  have h : (List.finRange 27).all (fun k =>
      2 * h3zornWeight k 0 + 3 * h3zornWeight k 1 + 4 * h3zornWeight k 2 +
        6 * h3zornWeight k 3 + 5 * h3zornWeight k 4 + 4 * h3zornWeight k 5 +
        3 * e7H6Weight k == 2) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h k

theorem h3zornTKKGradeOp_eq_linear_comb :
    h3zornTKKGradeOp =
      e7SimpleH 0 + (3 / 2 : ℝ) • e7SimpleH 1 + (2 : ℝ) • e7SimpleH 2 +
        (3 : ℝ) • e7SimpleH 3 + (5 / 2 : ℝ) • e7SimpleH 4 + (2 : ℝ) • e7SimpleH 5 +
        (3 / 2 : ℝ) • e7SimpleH 6 := by
  have h_e6 : ∀ i : Fin 6, e7SimpleH i.castSucc =
      zeroInj ⟨(e6SimpleH i : Module.End ℝ (H3Zorn ℝ)),
        h3zornCubicStabilizer_le_structureOperatorLieSubalgebra (e6SimpleH i).2⟩ := by
    intro i; rw [e7SimpleH_castSucc]; rfl
  have h0 : (0 : Fin 7) = (0 : Fin 6).castSucc := rfl
  have h1 : (1 : Fin 7) = (1 : Fin 6).castSucc := rfl
  have h2 : (2 : Fin 7) = (2 : Fin 6).castSucc := rfl
  have h3 : (3 : Fin 7) = (3 : Fin 6).castSucc := rfl
  have h4 : (4 : Fin 7) = (4 : Fin 6).castSucc := rfl
  have h5 : (5 : Fin 7) = (5 : Fin 6).castSucc := rfl
  rw [h3zornTKKGradeOp, h0, h1, h2, h3, h4, h5,
    h_e6 0, h_e6 1, h_e6 2, h_e6 3, h_e6 4, h_e6 5, e7SimpleH_six]
  simp only [← map_smul, ← map_add]
  congr 1
  apply Subtype.ext
  apply h3ZornBasis.ext
  intro k
  change h3zornStrOne.1 (h3ZornBasis k) =
    (e6SimpleH 0).1 (h3ZornBasis k) + (3 / 2 : ℝ) • (e6SimpleH 1).1 (h3ZornBasis k) +
      (2 : ℝ) • (e6SimpleH 2).1 (h3ZornBasis k) + (3 : ℝ) • (e6SimpleH 3).1 (h3ZornBasis k) +
      (5 / 2 : ℝ) • (e6SimpleH 4).1 (h3ZornBasis k) + (2 : ℝ) • (e6SimpleH 5).1 (h3ZornBasis k) +
      (3 / 2 : ℝ) • ((2 : ℝ) • JordanTKK.tripleD ℝ (h3ZornBasis 10) (h3ZornBasis 3))
        (h3ZornBasis k)
  rw [h3zornStrOne_apply, e6SimpleH_apply_basis 0 k, e6SimpleH_apply_basis 1 k,
    e6SimpleH_apply_basis 2 k, e6SimpleH_apply_basis 3 k, e6SimpleH_apply_basis 4 k,
    e6SimpleH_apply_basis 5 k, two_tripleD_10_3_apply_basis k]
  simp only [smul_smul, ← add_smul]
  have hw := congrArg (Int.cast : ℤ → ℝ) (e7GradeOp_weight_identity k)
  push_cast at hw
  have hcoeff : (1 : ℝ) =
      (h3zornWeight k 0 : ℝ) + (3 / 2 : ℝ) * (h3zornWeight k 1 : ℝ) +
        (2 : ℝ) * (h3zornWeight k 2 : ℝ) + (3 : ℝ) * (h3zornWeight k 3 : ℝ) +
        (5 / 2 : ℝ) * (h3zornWeight k 4 : ℝ) + (2 : ℝ) * (h3zornWeight k 5 : ℝ) +
        (3 / 2 : ℝ) * (e7H6Weight k : ℝ) := by
    linarith
  rw [← hcoeff, one_smul]

theorem e7SimpleH_six_eq_linear_comb :
    e7SimpleH 6 =
      (2 / 3 : ℝ) • h3zornTKKGradeOp -
        ((2 / 3 : ℝ) • e7SimpleH 0 + e7SimpleH 1 + (4 / 3 : ℝ) • e7SimpleH 2 +
          (2 : ℝ) • e7SimpleH 3 + (5 / 3 : ℝ) • e7SimpleH 4 + (4 / 3 : ℝ) • e7SimpleH 5) := by
  have hg := h3zornTKKGradeOp_eq_linear_comb
  have h32 : (3 / 2 : ℝ) • e7SimpleH 6 = h3zornTKKGradeOp -
      (e7SimpleH 0 + (3 / 2 : ℝ) • e7SimpleH 1 + (2 : ℝ) • e7SimpleH 2 +
        (3 : ℝ) • e7SimpleH 3 + (5 / 2 : ℝ) • e7SimpleH 4 + (2 : ℝ) • e7SimpleH 5) := by
    rw [hg]; abel
  have hmul := congrArg (fun X : H3ZornTKKLie => (2 / 3 : ℝ) • X) h32
  rw [smul_smul, show (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 by norm_num, one_smul] at hmul
  rw [hmul, smul_sub]
  simp only [smul_add, smul_smul]
  norm_num

end SimpleTriplesAndNode6

section CartanSubalgebra

theorem e7SimpleH_comm (i j : Fin 7) : ⁅e7SimpleH i, e7SimpleH j⁆ = 0 := by
  have h_e6 : ∀ a b : Fin 6, ⁅e7SimpleH a.castSucc, e7SimpleH b.castSucc⁆ = 0 := by
    intro a b
    rw [e7SimpleH_castSucc, e7SimpleH_castSucc, ← LieHom.map_lie, e6SimpleH_comm, map_zero]
  have h_grade : ∀ a : Fin 6, ⁅h3zornTKKGradeOp, e7SimpleH a.castSucc⁆ = 0 := by
    intro a
    rw [e7SimpleH_castSucc]
    exact h3zornTKKGradeOp_bracket_zero _
  have h_6_left : ∀ b : Fin 6, ⁅e7SimpleH 6, e7SimpleH b.castSucc⁆ = 0 := by
    intro b
    rw [e7SimpleH_six_eq_linear_comb, sub_lie, smul_lie, h_grade b, smul_zero, zero_sub]
    simp only [add_lie, smul_lie, show (0 : Fin 7) = (0 : Fin 6).castSucc from rfl,
      show (1 : Fin 7) = (1 : Fin 6).castSucc from rfl,
      show (2 : Fin 7) = (2 : Fin 6).castSucc from rfl,
      show (3 : Fin 7) = (3 : Fin 6).castSucc from rfl,
      show (4 : Fin 7) = (4 : Fin 6).castSucc from rfl,
      show (5 : Fin 7) = (5 : Fin 6).castSucc from rfl,
      h_e6, smul_zero, add_zero, neg_zero]
  by_cases hi : i.val < 6 <;> by_cases hj : j.val < 6
  · have hi' : i = (⟨i.val, hi⟩ : Fin 6).castSucc := Fin.ext rfl
    have hj' : j = (⟨j.val, hj⟩ : Fin 6).castSucc := Fin.ext rfl
    rw [hi', hj']; exact h_e6 _ _
  · have hj6 : j = 6 := Fin.ext (by omega)
    have hi' : i = (⟨i.val, hi⟩ : Fin 6).castSucc := Fin.ext rfl
    rw [hj6, hi', ← lie_skew, h_6_left, neg_zero]
  · have hi6 : i = 6 := Fin.ext (by omega)
    have hj' : j = (⟨j.val, hj⟩ : Fin 6).castSucc := Fin.ext rfl
    rw [hi6, hj']; exact h_6_left _
  · have hi6 : i = 6 := Fin.ext (by omega)
    have hj6 : j = 6 := Fin.ext (by omega)
    rw [hi6, hj6, lie_self]

/-- The 7-dimensional split Cartan subalgebra `h3zornCartan ⊕ ℝ·1` of `H3ZornTKKLie`. -/
def h3zornE7Cartan : LieSubalgebra ℝ H3ZornTKKLie where
  toSubmodule := Submodule.span ℝ (Set.range e7SimpleH)
  lie_mem' := by
    intro x y hx hy
    change x ∈ Submodule.span ℝ (Set.range e7SimpleH) at hx
    change y ∈ Submodule.span ℝ (Set.range e7SimpleH) at hy
    induction hx using Submodule.span_induction with
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => rw [add_lie]; exact Submodule.add_mem _ ih₁ ih₂
    | smul c _ _ ih => rw [smul_lie]; exact Submodule.smul_mem _ c ih
    | mem _ hx =>
      rcases hx with ⟨i, rfl⟩
      induction hy using Submodule.span_induction with
      | zero => simp
      | add _ _ _ _ ih₁ ih₂ => rw [lie_add]; exact Submodule.add_mem _ ih₁ ih₂
      | smul c _ _ ih => rw [lie_smul]; exact Submodule.smul_mem _ c ih
      | mem _ hy =>
        rcases hy with ⟨j, rfl⟩
        rw [e7SimpleH_comm]
        exact Submodule.zero_mem _

@[simp] theorem e7SimpleH_mem_h3zornE7Cartan (i : Fin 7) :
    e7SimpleH i ∈ h3zornE7Cartan :=
  Submodule.subset_span ⟨i, rfl⟩

theorem span_e7SimpleH_eq_h3zornE7Cartan :
    Submodule.span ℝ (Set.range e7SimpleH) = h3zornE7Cartan.toSubmodule :=
  rfl

@[simp] theorem e6SimpleH_mem_h3zornE7Cartan (i : Fin 6) :
    h3zornCubicStabilizerToTKK (e6SimpleH i) ∈ h3zornE7Cartan := by
  rw [← e7SimpleH_castSucc]
  exact e7SimpleH_mem_h3zornE7Cartan i.castSucc

theorem h3zornTKKGradeOp_mem_h3zornE7Cartan :
    h3zornTKKGradeOp ∈ h3zornE7Cartan := by
  rw [h3zornTKKGradeOp_eq_linear_comb]
  refine h3zornE7Cartan.add_mem (h3zornE7Cartan.add_mem (h3zornE7Cartan.add_mem
    (h3zornE7Cartan.add_mem (h3zornE7Cartan.add_mem (h3zornE7Cartan.add_mem
      (e7SimpleH_mem_h3zornE7Cartan 0)
      (h3zornE7Cartan.smul_mem _ (e7SimpleH_mem_h3zornE7Cartan 1)))
      (h3zornE7Cartan.smul_mem _ (e7SimpleH_mem_h3zornE7Cartan 2)))
      (h3zornE7Cartan.smul_mem _ (e7SimpleH_mem_h3zornE7Cartan 3)))
      (h3zornE7Cartan.smul_mem _ (e7SimpleH_mem_h3zornE7Cartan 4)))
      (h3zornE7Cartan.smul_mem _ (e7SimpleH_mem_h3zornE7Cartan 5)))
    (h3zornE7Cartan.smul_mem _ (e7SimpleH_mem_h3zornE7Cartan 6))

theorem h3zornE7Cartan_eq_sup :
    h3zornE7Cartan.toSubmodule =
      h3zornCartan.toSubmodule.map h3zornCubicStabilizerToTKK.toLinearMap ⊔
        Submodule.span ℝ {h3zornTKKGradeOp} := by
  apply le_antisymm
  · rw [← span_e7SimpleH_eq_h3zornE7Cartan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i.val < 6
    · have hi' : i = (⟨i.val, hi⟩ : Fin 6).castSucc := Fin.ext rfl
      rw [hi', e7SimpleH_castSucc]
      exact Submodule.mem_sup_left
        (Submodule.mem_map_of_mem (e6SimpleH_mem_h3zornCartan ⟨i.val, hi⟩))
    · have hi6 : i = 6 := Fin.ext (by omega)
      rw [hi6, e7SimpleH_six_eq_linear_comb]
      refine Submodule.sub_mem _
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span rfl))) ?_
      have mem_left : ∀ j : Fin 6, e7SimpleH j.castSucc ∈
          h3zornCartan.toSubmodule.map h3zornCubicStabilizerToTKK.toLinearMap ⊔
            Submodule.span ℝ {h3zornTKKGradeOp} := by
        intro j
        rw [e7SimpleH_castSucc]
        exact Submodule.mem_sup_left (Submodule.mem_map_of_mem (e6SimpleH_mem_h3zornCartan j))
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.smul_mem _ _ (mem_left 0))
          (mem_left 1))
          (Submodule.smul_mem _ _ (mem_left 2)))
          (Submodule.smul_mem _ _ (mem_left 3)))
          (Submodule.smul_mem _ _ (mem_left 4)))
          (Submodule.smul_mem _ _ (mem_left 5))
  · refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      change x ∈ Submodule.span ℝ (Set.range e6SimpleH) at hx
      induction hx using Submodule.span_induction with
      | zero => simp
      | add _ _ _ _ ih₁ ih₂ =>
        change h3zornCubicStabilizerToTKK _ ∈ h3zornE7Cartan
        rw [map_add]
        exact h3zornE7Cartan.add_mem ih₁ ih₂
      | smul c _ _ ih =>
        change h3zornCubicStabilizerToTKK _ ∈ h3zornE7Cartan
        rw [map_smul]
        exact h3zornE7Cartan.smul_mem c ih
      | mem _ h =>
        rcases h with ⟨i, rfl⟩
        exact e6SimpleH_mem_h3zornE7Cartan i
    · rw [Submodule.span_singleton_le_iff_mem]
      exact h3zornTKKGradeOp_mem_h3zornE7Cartan

instance : IsLieAbelian h3zornE7Cartan where
  trivial x y := by
    apply Subtype.ext
    rcases x with ⟨xv, hx⟩
    rcases y with ⟨yv, hy⟩
    change ⁅xv, yv⁆ = 0
    change xv ∈ Submodule.span ℝ (Set.range e7SimpleH) at hx
    change yv ∈ Submodule.span ℝ (Set.range e7SimpleH) at hy
    induction hx using Submodule.span_induction with
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => rw [add_lie, ih₁, ih₂, add_zero]
    | smul c _ _ ih => rw [smul_lie, ih, smul_zero]
    | mem _ hx =>
      rcases hx with ⟨i, rfl⟩
      induction hy using Submodule.span_induction with
      | zero => simp
      | add _ _ _ _ ih₁ ih₂ => rw [lie_add, ih₁, ih₂, add_zero]
      | smul c _ _ ih => rw [lie_smul, ih, smul_zero]
      | mem _ hy =>
        rcases hy with ⟨j, rfl⟩
        exact e7SimpleH_comm i j

theorem e7SimpleH_linearIndependent : LinearIndependent ℝ e7SimpleH := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let d : Fin 6 → ℝ := ![2 / 3, 1, 4 / 3, 2, 5 / 3, 4 / 3]
  have hd_sum : (2 / 3 : ℝ) • e7SimpleH 0 + e7SimpleH 1 + (4 / 3 : ℝ) • e7SimpleH 2 +
      (2 : ℝ) • e7SimpleH 3 + (5 / 3 : ℝ) • e7SimpleH 4 + (4 / 3 : ℝ) • e7SimpleH 5 =
      ∑ i : Fin 6, d i • e7SimpleH i.castSucc := by
    rw [Fin.sum_univ_six]
    simp only [d, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul]
    rfl
  have hsum : (c 6 * (2 / 3 : ℝ)) • h3zornTKKGradeOp +
      h3zornCubicStabilizerToTKK
        (∑ i : Fin 6, (c i.castSucc - c 6 * d i) • e6SimpleH i) = 0 := by
    have h6 := e7SimpleH_six_eq_linear_comb
    rw [hd_sum] at h6
    have h0' : ∑ i : Fin 7, c i • e7SimpleH i =
        (∑ i : Fin 6, c i.castSucc • e7SimpleH i.castSucc) + c 6 • e7SimpleH 6 := by
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [h0', h6, smul_sub, smul_smul, Finset.smul_sum] at hc
    have hsm : ∑ x : Fin 6, c 6 • (d x • e7SimpleH x.castSucc) =
        ∑ x : Fin 6, (c 6 * d x) • e7SimpleH x.castSucc :=
      Finset.sum_congr rfl fun x _ => smul_smul (c 6) (d x) (e7SimpleH x.castSucc)
    rw [hsm] at hc
    have hcomb : h3zornCubicStabilizerToTKK
          (∑ i : Fin 6, (c i.castSucc - c 6 * d i) • e6SimpleH i) =
        ∑ i : Fin 6, c i.castSucc • e7SimpleH i.castSucc -
          ∑ i : Fin 6, (c 6 * d i) • e7SimpleH i.castSucc := by
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← e7SimpleH_castSucc, sub_smul]
    rw [hcomb, ← hc]
    abel
  have h6zero : c 6 = 0 := by
    by_contra hc6
    have hne : c 6 * (2 / 3 : ℝ) ≠ 0 := mul_ne_zero hc6 (by norm_num)
    have hmem : (c 6 * (2 / 3 : ℝ)) • h3zornStrOne.1 ∈ h3zornCubicStabilizer := by
      let T0 : h3zornCubicStabilizer := ∑ i : Fin 6, (c i.castSucc - c 6 * d i) • e6SimpleH i
      have hsum' : (c 6 * (2 / 3 : ℝ)) • h3zornTKKGradeOp + h3zornCubicStabilizerToTKK T0 = 0 :=
        hsum
      have hz := congrArg (fun X : H3ZornTKKLie => X.zero.1) hsum'
      have hadd : ∀ X Y : H3ZornTKKLie, (X + Y).zero.1 = X.zero.1 + Y.zero.1 := fun _ _ => rfl
      have hsm : ∀ (r : ℝ) (X : H3ZornTKKLie), (r • X).zero.1 = r • X.zero.1 := fun _ _ => rfl
      have hg1 : h3zornTKKGradeOp.zero.1 = h3zornStrOne.1 := rfl
      have ht1 : (h3zornCubicStabilizerToTKK T0).zero.1 = T0.1 := rfl
      have hz0 : (0 : H3ZornTKKLie).zero.1 = 0 := rfl
      rw [hadd, hsm, hg1, ht1, hz0] at hz
      rw [eq_neg_of_add_eq_zero_left hz]
      exact h3zornCubicStabilizer.neg_mem T0.2
    have h1 := h3zornCubicStabilizer.smul_mem (c 6 * (2 / 3 : ℝ))⁻¹ hmem
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at h1
    exact h3zornStrOne_not_mem_cubicStabilizer h1
  have hsum' : h3zornCubicStabilizerToTKK (∑ i : Fin 6, c i.castSucc • e6SimpleH i) = 0 := by
    simpa [h6zero] using hsum
  have hc6' : ∀ i : Fin 6, c i.castSucc = 0 :=
    Fintype.linearIndependent_iff.mp e6SimpleH_linearIndependent (fun i => c i.castSucc)
      (h3zornCubicStabilizerToTKK_injective (hsum'.trans (map_zero _).symm))
  intro i
  by_cases hi : i.val < 6
  · exact hc6' ⟨i.val, hi⟩
  · have hi6 : i = 6 := Fin.ext (by omega)
    rw [hi6]; exact h6zero

/-- Canonical 7-element basis of `h3zornE7Cartan`. -/
def e7CartanBasis : Module.Basis (Fin 7) ℝ h3zornE7Cartan :=
  Module.Basis.span (by
    have hli : LinearIndependent ℝ (fun i : Fin 7 =>
        (⟨e7SimpleH i, e7SimpleH_mem_h3zornE7Cartan i⟩ : h3zornE7Cartan)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      exact Fintype.linearIndependent_iff.mp e7SimpleH_linearIndependent c
        (congrArg Subtype.val hc)
    exact e7SimpleH_linearIndependent)

@[simp] theorem e7CartanBasis_apply (i : Fin 7) :
    (e7CartanBasis i : H3ZornTKKLie) = e7SimpleH i := by
  change ((Module.Basis.span e7SimpleH_linearIndependent i :
    Submodule.span ℝ (Set.range e7SimpleH)) : H3ZornTKKLie) = e7SimpleH i
  rw [Module.Basis.span_apply]

theorem finrank_h3zornE7Cartan : Module.finrank ℝ h3zornE7Cartan = 7 := by
  have hli : LinearIndependent ℝ (fun i : Fin 7 =>
      (⟨e7SimpleH i, e7SimpleH_mem_h3zornE7Cartan i⟩ : h3zornE7Cartan)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    exact Fintype.linearIndependent_iff.mp e7SimpleH_linearIndependent c (congrArg Subtype.val hc)
  have hsp : Submodule.span ℝ (Set.range (fun i : Fin 7 =>
      (⟨e7SimpleH i, e7SimpleH_mem_h3zornE7Cartan i⟩ : h3zornE7Cartan))) = ⊤ := by
    rw [Submodule.eq_top_iff']
    rintro ⟨x, hx⟩
    change x ∈ Submodule.span ℝ (Set.range e7SimpleH) at hx
    induction hx using Submodule.span_induction with
    | zero => exact Submodule.zero_mem _
    | add _ _ _ _ ih₁ ih₂ => exact Submodule.add_mem _ ih₁ ih₂
    | smul r _ _ ih => exact Submodule.smul_mem _ r ih
    | mem _ h =>
      rcases h with ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
  have hfin := finrank_span_eq_card hli
  rw [hsp, finrank_top] at hfin
  simpa using hfin

end CartanSubalgebra

section RootDecompositionAndBasis

/-- The 126 root vectors of `𝔈₇(7)`: `0..71` in grade `0`, `72..98` in grade `-1`,
and `99..125` in grade `+1` (via `traceDualIdx`). -/
def e7RootVec (r : Fin 126) : H3ZornTKKLie :=
  if h0 : r.val < 72 then
    h3zornCubicStabilizerToTKK (e6RootVec ⟨r.val, h0⟩)
  else if h1 : r.val < 99 then
    negInj (h3ZornBasis ⟨r.val - 72, by omega⟩)
  else
    posInj (h3ZornBasis (traceDualIdx ⟨r.val - 99, by omega⟩))

/-- Bourbaki `E₇` root coordinates for the 27 grade-`-1` root vectors `negInj (h3ZornBasis k)`. -/
def e7NegRootCoord (k : Fin 27) : Fin 7 → ℤ :=
  match k.val with
  | 0 => ![1, 1, 1, 2, 2, 1, 1]
  | 1 => ![1, 1, 2, 2, 1, 1, 1]
  | 2 => ![0, 1, 1, 2, 2, 2, 1]
  | 3 => ![2, 2, 3, 4, 3, 2, 1]
  | 4 => ![1, 0, 1, 1, 1, 1, 1]
  | 5 => ![1, 1, 1, 1, 1, 1, 1]
  | 6 => ![1, 1, 1, 2, 1, 1, 1]
  | 7 => ![1, 2, 2, 3, 2, 1, 1]
  | 8 => ![1, 1, 2, 3, 2, 1, 1]
  | 9 => ![1, 1, 2, 2, 2, 1, 1]
  | 10 => ![0, 0, 0, 0, 0, 0, 1]
  | 11 => ![0, 0, 0, 0, 0, 1, 1]
  | 12 => ![0, 0, 1, 1, 1, 1, 1]
  | 13 => ![0, 1, 1, 1, 1, 1, 1]
  | 14 => ![0, 1, 1, 2, 1, 1, 1]
  | 15 => ![1, 2, 2, 3, 2, 2, 1]
  | 16 => ![1, 1, 2, 3, 2, 2, 1]
  | 17 => ![1, 1, 2, 2, 2, 2, 1]
  | 18 => ![1, 2, 3, 4, 3, 2, 1]
  | 19 => ![0, 1, 1, 2, 2, 1, 1]
  | 20 => ![1, 1, 2, 3, 3, 2, 1]
  | 21 => ![1, 2, 2, 3, 3, 2, 1]
  | 22 => ![1, 2, 2, 4, 3, 2, 1]
  | 23 => ![0, 1, 0, 1, 1, 1, 1]
  | 24 => ![0, 0, 0, 1, 1, 1, 1]
  | 25 => ![0, 0, 0, 0, 1, 1, 1]
  | 26 => ![1, 1, 1, 2, 2, 2, 1]
  | _ => ![0, 0, 0, 0, 0, 0, 0]

/-- Bourbaki `E₇` root coordinates for all 126 root vectors. -/
def e7RootCoord (r : Fin 126) : Fin 7 → ℤ :=
  if h0 : r.val < 72 then
    fun i => if hi : i.val < 6 then e6RootCoord ⟨r.val, h0⟩ ⟨i.val, hi⟩ else 0
  else if h1 : r.val < 99 then
    e7NegRootCoord ⟨r.val - 72, by omega⟩
  else
    -e7NegRootCoord ⟨r.val - 99, by omega⟩

private def e7RootCertIdx (r : Fin 126) : Fin 126 :=
  match r.val with
  | 0 => 47 | 1 => 59 | 2 => 71 | 3 => 104 | 4 => 97 | 5 => 89 | 6 => 61 | 7 => 48
  | 8 => 9 | 9 => 22 | 10 => 107 | 11 => 39 | 12 => 1 | 13 => 13 | 14 => 101 | 15 => 10
  | 16 => 3 | 17 => 94 | 18 => 50 | 19 => 37 | 20 => 57 | 21 => 26 | 22 => 68 | 23 => 78
  | 24 => 81 | 25 => 80 | 26 => 35 | 27 => 36 | 28 => 25 | 29 => 27 | 30 => 11 | 31 => 15
  | 32 => 24 | 33 => 23 | 34 => 14 | 35 => 12 | 36 => 4 | 37 => 2 | 38 => 86 | 39 => 87
  | 40 => 83 | 41 => 77 | 42 => 49 | 43 => 44 | 44 => 41 | 45 => 32 | 46 => 29 | 47 => 20
  | 48 => 33 | 49 => 38 | 50 => 21 | 51 => 28 | 52 => 8 | 53 => 16 | 54 => 70 | 55 => 75
  | 56 => 7 | 57 => 17 | 58 => 40 | 59 => 34 | 60 => 51 | 61 => 46 | 62 => 64 | 63 => 58
  | 64 => 45 | 65 => 53 | 66 => 56 | 67 => 62 | 68 => 67 | 69 => 73 | 70 => 5 | 71 => 0
  | 72 => 91 | 73 => 90 | 74 => 93 | 75 => 124 | 76 => 60 | 77 => 72 | 78 => 82 | 79 => 110
  | 80 => 105 | 81 => 98 | 82 => 6 | 83 => 18 | 84 => 54 | 85 => 65 | 86 => 76 | 87 => 114
  | 88 => 111 | 89 => 106 | 90 => 122 | 91 => 85 | 92 => 115 | 93 => 118 | 94 => 120 | 95 => 52
  | 96 => 42 | 97 => 30 | 98 => 99 | 99 => 96 | 100 => 95 | 101 => 100 | 102 => 125 | 103 => 69
  | 104 => 79 | 105 => 88 | 106 => 112 | 107 => 108 | 108 => 102 | 109 => 19 | 110 => 31
  | 111 => 66 | 112 => 74 | 113 => 84 | 114 => 116 | 115 => 113 | 116 => 109 | 117 => 123
  | 118 => 92 | 119 => 117 | 120 => 119 | 121 => 121 | 122 => 63 | 123 => 55 | 124 => 43
  | 125 => 103
  | _ => 0

private def e7CertBlockCheck (offset : ℕ) (h : offset + 21 ≤ 126) : Bool :=
  (List.finRange 21).all fun k =>
    let r : Fin 126 := ⟨offset + k.val, by omega⟩
    List.ofFn (e7RootCoord r) == List.ofFn (e7Certificate.root (e7RootCertIdx r).val)

private theorem e7CertBlock_0 : e7CertBlockCheck 0 (by decide) = true := by decide
private theorem e7CertBlock_1 : e7CertBlockCheck 21 (by decide) = true := by decide
private theorem e7CertBlock_2 : e7CertBlockCheck 42 (by decide) = true := by decide
private theorem e7CertBlock_3 : e7CertBlockCheck 63 (by decide) = true := by decide
private theorem e7CertBlock_4 : e7CertBlockCheck 84 (by decide) = true := by decide
private theorem e7CertBlock_5 : e7CertBlockCheck 105 (by decide) = true := by decide

theorem e7RootCoord_eq_cert (r : Fin 126) :
    e7RootCoord r = e7Certificate.root (e7RootCertIdx r).val := by
  apply List.ofFn_injective
  have hb : ∀ (off : ℕ) (h : off + 21 ≤ 126), e7CertBlockCheck off h = true →
      ∀ k : Fin 21,
        List.ofFn (e7RootCoord ⟨off + k.val, by omega⟩) =
          List.ofFn (e7Certificate.root (e7RootCertIdx ⟨off + k.val, by omega⟩).val) := by
    intro off h hchk k
    dsimp [e7CertBlockCheck] at hchk
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
    exact hchk k
  by_cases h0 : r.val < 21
  · have heq : (⟨0 + (⟨r.val, h0⟩ : Fin 21).val, by omega⟩ : Fin 126) = r :=
      Fin.ext (by dsimp; omega)
    have hres := hb 0 (by decide) e7CertBlock_0 ⟨r.val, h0⟩
    rwa [heq] at hres
  · by_cases h1 : r.val < 42
    · have hk : r.val - 21 < 21 := by omega
      have heq : (⟨21 + (⟨r.val - 21, hk⟩ : Fin 21).val, by omega⟩ : Fin 126) = r :=
        Fin.ext (by dsimp; omega)
      have hres := hb 21 (by decide) e7CertBlock_1 ⟨r.val - 21, hk⟩
      rwa [heq] at hres
    · by_cases h2 : r.val < 63
      · have hk : r.val - 42 < 21 := by omega
        have heq : (⟨42 + (⟨r.val - 42, hk⟩ : Fin 21).val, by omega⟩ : Fin 126) = r :=
          Fin.ext (by dsimp; omega)
        have hres := hb 42 (by decide) e7CertBlock_2 ⟨r.val - 42, hk⟩
        rwa [heq] at hres
      · by_cases h3 : r.val < 84
        · have hk : r.val - 63 < 21 := by omega
          have heq : (⟨63 + (⟨r.val - 63, hk⟩ : Fin 21).val, by omega⟩ : Fin 126) = r :=
            Fin.ext (by dsimp; omega)
          have hres := hb 63 (by decide) e7CertBlock_3 ⟨r.val - 63, hk⟩
          rwa [heq] at hres
        · by_cases h4 : r.val < 105
          · have hk : r.val - 84 < 21 := by omega
            have heq : (⟨84 + (⟨r.val - 84, hk⟩ : Fin 21).val, by omega⟩ : Fin 126) = r :=
              Fin.ext (by dsimp; omega)
            have hres := hb 84 (by decide) e7CertBlock_4 ⟨r.val - 84, hk⟩
            rwa [heq] at hres
          · have hk : r.val - 105 < 21 := by omega
            have heq : (⟨105 + (⟨r.val - 105, hk⟩ : Fin 21).val, by omega⟩ : Fin 126) = r :=
              Fin.ext (by dsimp; omega)
            have hres := hb 105 (by decide) e7CertBlock_5 ⟨r.val - 105, hk⟩
            rwa [heq] at hres

private theorem e7Certificate_roots_length : e7Certificate.roots.length = 126 :=
  Tag.rootCertificate_length .E7

theorem e7RootCoord_isRoot (r : Fin 126) : IsRoot .E7 (e7RootCoord r) := by
  rw [e7RootCoord_eq_cert r]
  exact RootCertificate.isRoot_root e7Certificate_check (e7RootCertIdx r).val
    (Nat.lt_of_lt_of_eq (e7RootCertIdx r).isLt e7Certificate_roots_length.symm)

private theorem e7NegRootCoord_six (k : Fin 27) : e7NegRootCoord k 6 = 1 := by
  have h : (List.finRange 27).all (fun k => e7NegRootCoord k 6 == 1) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h k

private theorem e7NegRootCoord_injective : Function.Injective e7NegRootCoord := by
  have h : (List.finRange 27).all (fun k₁ => (List.finRange 27).all (fun k₂ =>
      if k₁ = k₂ then true else
        !(List.ofFn (e7NegRootCoord k₁) == List.ofFn (e7NegRootCoord k₂)))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  intro k₁ k₂ heq
  by_contra hne
  have h12 := h k₁ k₂
  simp [hne, heq] at h12

theorem e7RootCoord_injective : Function.Injective e7RootCoord := by
  intro r₁ r₂ heq
  have h6 : e7RootCoord r₁ 6 = e7RootCoord r₂ 6 := congrFun heq 6
  by_cases h10 : r₁.val < 72 <;> by_cases h20 : r₂.val < 72
  · have h6' : e6RootCoord ⟨r₁.val, h10⟩ = e6RootCoord ⟨r₂.val, h20⟩ := by
      ext i
      have hi := congrFun heq i.castSucc
      simpa [e7RootCoord, h10, h20, i.isLt] using hi
    have hval := congrArg Fin.val (e6RootCoord_injective h6')
    exact Fin.ext hval
  · exfalso
    by_cases h21 : r₂.val < 99
    · simp [e7RootCoord, h10, h20, h21, e7NegRootCoord_six] at h6
    · simp [e7RootCoord, h10, h20, h21, e7NegRootCoord_six] at h6
  · exfalso
    by_cases h11 : r₁.val < 99
    · simp [e7RootCoord, h10, h20, h11, e7NegRootCoord_six] at h6
    · simp [e7RootCoord, h10, h20, h11, e7NegRootCoord_six] at h6
  · by_cases h11 : r₁.val < 99 <;> by_cases h21 : r₂.val < 99
    · have hne : e7NegRootCoord ⟨r₁.val - 72, by omega⟩ =
          e7NegRootCoord ⟨r₂.val - 72, by omega⟩ := by
        simpa [e7RootCoord, h10, h20, h11, h21] using heq
      have hk := congrArg Fin.val (e7NegRootCoord_injective hne)
      dsimp at hk
      exact Fin.ext (by omega)
    · exfalso
      simp [e7RootCoord, h10, h20, h11, h21, e7NegRootCoord_six] at h6
    · exfalso
      simp [e7RootCoord, h10, h20, h11, h21, e7NegRootCoord_six] at h6
    · have hne : -e7NegRootCoord ⟨r₁.val - 99, by omega⟩ =
          -e7NegRootCoord ⟨r₂.val - 99, by omega⟩ := by
        simpa [e7RootCoord, h10, h20, h11, h21] using heq
      have hk := congrArg Fin.val (e7NegRootCoord_injective (neg_inj.mp hne))
      dsimp at hk
      exact Fin.ext (by omega)

/-- Canonical bijection between the 126 `H3ZornTKKLie` root operators and `CFSGPort` `E₇` roots. -/
def e7RootEquiv : Fin 126 ≃ {v : Fin 7 → ℤ // IsRoot .E7 v} :=
  letI : Fintype {v : Fin 7 → ℤ // IsRoot .E7 v} :=
    (inferInstance : Fintype {v : Fin (Tag.rank .E7) → ℤ // IsRoot .E7 v})
  Equiv.ofBijective (fun r => ⟨e7RootCoord r, e7RootCoord_isRoot r⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun _ _ h => e7RootCoord_injective (congrArg Subtype.val h),
       by rw [Fintype.card_fin]; exact (card_isRoot .E7).symm⟩)

/-- Integer eigenvalue of `ad (e7SimpleH i)` on `e7RootVec r`. -/
def e7RootEigenvalue (i : Fin 7) (r : Fin 126) : ℤ :=
  ∑ j : Fin 7, Tag.cartan .E7 i j * e7RootCoord r j

/-- The 126 root weights in `(h3zornE7Cartan)⋆`. -/
def h3zornE7RootWeight (r : Fin 126) : Module.Dual ℝ h3zornE7Cartan :=
  e7CartanBasis.constr ℝ (fun i => (e7RootEigenvalue i r : ℝ))

private theorem e7CartanBasis_eq (i : Fin 7) :
    e7CartanBasis i = ⟨e7SimpleH i, e7SimpleH_mem_h3zornE7Cartan i⟩ :=
  Subtype.ext (e7CartanBasis_apply i)

@[simp] theorem h3zornE7RootWeight_simpleH (r : Fin 126) (i : Fin 7) :
    h3zornE7RootWeight r ⟨e7SimpleH i, e7SimpleH_mem_h3zornE7Cartan i⟩ =
      (e7RootEigenvalue i r : ℝ) := by
  rw [← e7CartanBasis_eq i]
  exact Module.Basis.constr_basis e7CartanBasis ℝ (fun j => (e7RootEigenvalue j r : ℝ)) i

private theorem e7RootEigenvalue_grade0_castSucc (i : Fin 6) (r : Fin 72) :
    e7RootEigenvalue i.castSucc ⟨r.val, by omega⟩ = rootEigenvalue i r := by
  have h : (List.finRange 6).all (fun i => (List.finRange 72).all (fun r =>
      e7RootEigenvalue i.castSucc ⟨r.val, by omega⟩ == rootEigenvalue i r)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h i r

private theorem e7RootEigenvalue_grade0_six (r : Fin 72) :
    3 * e7RootEigenvalue 6 ⟨r.val, by omega⟩ =
      -(2 * rootEigenvalue 0 r + 3 * rootEigenvalue 1 r + 4 * rootEigenvalue 2 r +
        6 * rootEigenvalue 3 r + 5 * rootEigenvalue 4 r + 4 * rootEigenvalue 5 r) := by
  have h : (List.finRange 72).all (fun r =>
      3 * e7RootEigenvalue 6 ⟨r.val, by omega⟩ ==
        -(2 * rootEigenvalue 0 r + 3 * rootEigenvalue 1 r + 4 * rootEigenvalue 2 r +
          6 * rootEigenvalue 3 r + 5 * rootEigenvalue 4 r + 4 * rootEigenvalue 5 r)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h r

private theorem e7RootEigenvalue_neg_castSucc (i : Fin 6) (k : Fin 27) :
    e7RootEigenvalue i.castSucc ⟨72 + k.val, by omega⟩ = h3zornWeight k i := by
  have h : (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      e7RootEigenvalue i.castSucc ⟨72 + k.val, by omega⟩ == h3zornWeight k i)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h i k

private theorem e7RootEigenvalue_neg_six (k : Fin 27) :
    e7RootEigenvalue 6 ⟨72 + k.val, by omega⟩ = e7H6Weight k := by
  have h : (List.finRange 27).all (fun k =>
      e7RootEigenvalue 6 ⟨72 + k.val, by omega⟩ == e7H6Weight k) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h k

private theorem e7RootEigenvalue_pos_castSucc (i : Fin 6) (k : Fin 27) :
    e7RootEigenvalue i.castSucc ⟨99 + k.val, by omega⟩ = -h3zornWeight k i := by
  have h : (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      e7RootEigenvalue i.castSucc ⟨99 + k.val, by omega⟩ == -h3zornWeight k i)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h i k

private theorem e7RootEigenvalue_pos_six (k : Fin 27) :
    e7RootEigenvalue 6 ⟨99 + k.val, by omega⟩ = -e7H6Weight k := by
  have h : (List.finRange 27).all (fun k =>
      e7RootEigenvalue 6 ⟨99 + k.val, by omega⟩ == -e7H6Weight k) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h k

theorem e7RootVec_bracket_H (i : Fin 7) (r : Fin 126) :
    ⁅e7SimpleH i, e7RootVec r⁆ = (e7RootEigenvalue i r : ℝ) • e7RootVec r := by
  by_cases hr0 : r.val < 72
  · have hr_eq : r = ⟨r.val, by omega⟩ := Fin.ext rfl
    have hrv : e7RootVec r = h3zornCubicStabilizerToTKK (e6RootVec ⟨r.val, hr0⟩) := by
      simp [e7RootVec, hr0]
    rw [hrv]
    by_cases hi : i.val < 6
    · have hi' : i = (⟨i.val, hi⟩ : Fin 6).castSucc := Fin.ext rfl
      rw [hi', e7SimpleH_castSucc, ← LieHom.map_lie, e6RootVec_bracket_H, map_smul]
      congr 1
      exact_mod_cast (e7RootEigenvalue_grade0_castSucc ⟨i.val, hi⟩ ⟨r.val, hr0⟩).symm
    · have hi6 : i = 6 := Fin.ext (by omega)
      rw [hi6, e7SimpleH_six_eq_linear_comb]
      have h_grade : ⁅h3zornTKKGradeOp, h3zornCubicStabilizerToTKK (e6RootVec ⟨r.val, hr0⟩)⁆ = 0 :=
        h3zornTKKGradeOp_bracket_zero _
      have h_e6 : ∀ j : Fin 6, ⁅e7SimpleH j.castSucc,
            h3zornCubicStabilizerToTKK (e6RootVec ⟨r.val, hr0⟩)⁆ =
          (rootEigenvalue j ⟨r.val, hr0⟩ : ℝ) •
            h3zornCubicStabilizerToTKK (e6RootVec ⟨r.val, hr0⟩) := by
        intro j
        rw [e7SimpleH_castSucc, ← LieHom.map_lie, e6RootVec_bracket_H, map_smul]
      rw [sub_lie, smul_lie, h_grade, smul_zero, zero_sub]
      simp only [add_lie, smul_lie, show (0 : Fin 7) = (0 : Fin 6).castSucc from rfl,
        show (1 : Fin 7) = (1 : Fin 6).castSucc from rfl,
        show (2 : Fin 7) = (2 : Fin 6).castSucc from rfl,
        show (3 : Fin 7) = (3 : Fin 6).castSucc from rfl,
        show (4 : Fin 7) = (4 : Fin 6).castSucc from rfl,
        show (5 : Fin 7) = (5 : Fin 6).castSucc from rfl, h_e6, smul_smul, ← add_smul, ← neg_smul]
      congr 1
      have hw := congrArg (Int.cast : ℤ → ℝ) (e7RootEigenvalue_grade0_six ⟨r.val, hr0⟩)
      push_cast at hw
      have hre : e7RootEigenvalue 6 r = e7RootEigenvalue 6 ⟨r.val, by omega⟩ :=
        congrArg (e7RootEigenvalue 6) hr_eq
      rw [hre]
      linarith
  · by_cases hr1 : r.val < 99
    · let k : Fin 27 := ⟨r.val - 72, by omega⟩
      have hk_idx : (⟨72 + k.val, by omega⟩ : Fin 126) = r := Fin.ext (by dsimp [k]; omega)
      have hrv : e7RootVec r = negInj (h3ZornBasis k) := by
        simp [e7RootVec, hr0, hr1, k]
      rw [hrv]
      by_cases hi : i.val < 6
      · have hi' : i = (⟨i.val, hi⟩ : Fin 6).castSucc := Fin.ext rfl
        rw [hi', e7SimpleH_castSucc]
        change ⁅zeroInj _, negInj (h3ZornBasis k)⁆ = _
        rw [zeroInj_bracket_negInj]
        change negInj ((e6SimpleH ⟨i.val, hi⟩).1 (h3ZornBasis k)) = _
        rw [e6SimpleH_apply_basis, map_smul, ← hk_idx, e7RootEigenvalue_neg_castSucc]
      · have hi6 : i = 6 := Fin.ext (by omega)
        rw [hi6, e7SimpleH_six, zeroInj_bracket_negInj, two_tripleD_10_3_apply_basis, map_smul,
          ← hk_idx, e7RootEigenvalue_neg_six]
    · let k : Fin 27 := ⟨r.val - 99, by omega⟩
      have hk_idx : (⟨99 + k.val, by omega⟩ : Fin 126) = r := Fin.ext (by dsimp [k]; omega)
      have hrv : e7RootVec r = posInj (h3ZornBasis (traceDualIdx k)) := by
        simp [e7RootVec, hr0, hr1, k]
      rw [hrv]
      by_cases hi : i.val < 6
      · have hi' : i = (⟨i.val, hi⟩ : Fin 6).castSucc := Fin.ext rfl
        rw [hi', e7SimpleH_castSucc]
        change ⁅zeroInj _, posInj (h3ZornBasis (traceDualIdx k))⁆ = _
        rw [zeroInj_bracket_posInj]
        have hadj := h3zornTraceAdjoint_eigenvector (e6SimpleH ⟨i.val, hi⟩).1 h3ZornBasis
          (fun m => (h3zornWeight m ⟨i.val, hi⟩ : ℝ))
          (fun m => e6SimpleH_apply_basis ⟨i.val, hi⟩ m)
          (h3ZornBasis (traceDualIdx k)) k (traceBilin_h3ZornBasis_ne_dual k)
        change posInj (-h3zornTraceAdjoint (e6SimpleH ⟨i.val, hi⟩).1
            (h3ZornBasis (traceDualIdx k))) = _
        rw [hadj, ← neg_smul, map_smul, ← hk_idx, e7RootEigenvalue_pos_castSucc, Int.cast_neg]
      · have hi6 : i = 6 := Fin.ext (by omega)
        rw [hi6, e7SimpleH_six, zeroInj_bracket_posInj]
        have hadj := h3zornTraceAdjoint_eigenvector
          ((2 : ℝ) • JordanTKK.tripleD ℝ (h3ZornBasis 10) (h3ZornBasis 3)) h3ZornBasis
          (fun m => (e7H6Weight m : ℝ))
          two_tripleD_10_3_apply_basis
          (h3ZornBasis (traceDualIdx k)) k (traceBilin_h3ZornBasis_ne_dual k)
        change posInj (-h3zornTraceAdjoint
            ((2 : ℝ) • JordanTKK.tripleD ℝ (h3ZornBasis 10) (h3ZornBasis 3))
            (h3ZornBasis (traceDualIdx k))) = _
        rw [hadj, ← neg_smul, map_smul, ← hk_idx, e7RootEigenvalue_pos_six, Int.cast_neg]

theorem e7RootVec_bracket_cartan (H : h3zornE7Cartan) (r : Fin 126) :
    ⁅(H : H3ZornTKKLie), e7RootVec r⁆ = h3zornE7RootWeight r H • e7RootVec r := by
  have hrep := e7CartanBasis.sum_repr H
  conv_lhs => rw [← hrep]
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, e7CartanBasis_apply, sum_lie,
    smul_lie, e7RootVec_bracket_H, smul_smul, ← Finset.sum_smul]
  congr 1
  have hlin : h3zornE7RootWeight r H =
      ∑ i : Fin 7, (e7CartanBasis.repr H i) * (e7RootEigenvalue i r : ℝ) := by
    conv_lhs => rw [← hrep]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    congr 1
    have h := Module.Basis.constr_basis e7CartanBasis ℝ (fun j => (e7RootEigenvalue j r : ℝ)) i
    simpa only [h3zornE7RootWeight] using h
  rw [hlin]

theorem e7RootEigenvalue_ne_zero (r : Fin 126) : ∃ i : Fin 7, e7RootEigenvalue i r ≠ 0 := by
  have h : (List.finRange 126).all (fun r =>
      (List.finRange 7).any (fun i => e7RootEigenvalue i r != 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, List.any_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨i, _, hi⟩ := h r
  exact ⟨i, hi⟩

theorem h3zornE7RootWeight_ne_zero (r : Fin 126) : h3zornE7RootWeight r ≠ 0 := by
  intro h0
  obtain ⟨i, hi⟩ := e7RootEigenvalue_ne_zero r
  have hval := congrArg (fun f : Module.Dual ℝ h3zornE7Cartan =>
    f ⟨e7SimpleH i, e7SimpleH_mem_h3zornE7Cartan i⟩) h0
  rw [h3zornE7RootWeight_simpleH, LinearMap.zero_apply] at hval
  exact hi (Int.cast_eq_zero.mp hval)

private def cE7 (i j : Fin 7) : ℤ := Tag.cartan .E7 i j

private theorem cE7_eq (i j : Fin 7) : cE7 i j =
    match i.val, j.val with
    | 0, 0 => 2 | 0, 2 => -1
    | 1, 1 => 2 | 1, 3 => -1
    | 2, 0 => -1 | 2, 2 => 2 | 2, 3 => -1
    | 3, 1 => -1 | 3, 2 => -1 | 3, 3 => 2 | 3, 4 => -1
    | 4, 3 => -1 | 4, 4 => 2 | 4, 5 => -1
    | 5, 4 => -1 | 5, 5 => 2 | 5, 6 => -1
    | 6, 5 => -1 | 6, 6 => 2
    | _, _ => 0 := by
  fin_cases i <;> fin_cases j <;> decide

private theorem cartan_E7_mulVec_inj : Function.Injective (Tag.cartan .E7).mulVec := by
  intro v₁ v₂ hv
  let d : Fin 7 → ℤ := v₁ - v₂
  have hd : (Tag.cartan .E7).mulVec d = 0 := by
    rw [Matrix.mulVec_sub, hv, sub_self]
  have hrow : ∀ i : Fin 7, ∑ j : Fin 7, cE7 i j * d j = 0 :=
    fun i => congrFun hd i
  have hc0 : cE7 0 0 = 2 ∧ cE7 0 1 = 0 ∧ cE7 0 2 = -1 ∧ cE7 0 3 = 0 ∧
      cE7 0 4 = 0 ∧ cE7 0 5 = 0 ∧ cE7 0 6 = 0 := by decide
  have hc1 : cE7 1 0 = 0 ∧ cE7 1 1 = 2 ∧ cE7 1 2 = 0 ∧ cE7 1 3 = -1 ∧
      cE7 1 4 = 0 ∧ cE7 1 5 = 0 ∧ cE7 1 6 = 0 := by decide
  have hc2 : cE7 2 0 = -1 ∧ cE7 2 1 = 0 ∧ cE7 2 2 = 2 ∧ cE7 2 3 = -1 ∧
      cE7 2 4 = 0 ∧ cE7 2 5 = 0 ∧ cE7 2 6 = 0 := by decide
  have hc3 : cE7 3 0 = 0 ∧ cE7 3 1 = -1 ∧ cE7 3 2 = -1 ∧ cE7 3 3 = 2 ∧
      cE7 3 4 = -1 ∧ cE7 3 5 = 0 ∧ cE7 3 6 = 0 := by decide
  have hc4 : cE7 4 0 = 0 ∧ cE7 4 1 = 0 ∧ cE7 4 2 = 0 ∧ cE7 4 3 = -1 ∧
      cE7 4 4 = 2 ∧ cE7 4 5 = -1 ∧ cE7 4 6 = 0 := by decide
  have hc5 : cE7 5 0 = 0 ∧ cE7 5 1 = 0 ∧ cE7 5 2 = 0 ∧ cE7 5 3 = 0 ∧
      cE7 5 4 = -1 ∧ cE7 5 5 = 2 ∧ cE7 5 6 = -1 := by decide
  have hc6 : cE7 6 0 = 0 ∧ cE7 6 1 = 0 ∧ cE7 6 2 = 0 ∧ cE7 6 3 = 0 ∧
      cE7 6 4 = 0 ∧ cE7 6 5 = -1 ∧ cE7 6 6 = 2 := by decide
  have h0 : 2 * d 0 - d 2 = 0 := by
    have := hrow 0; rw [Fin.sum_univ_seven] at this; simp only [hc0] at this; linarith
  have h1 : 2 * d 1 - d 3 = 0 := by
    have := hrow 1; rw [Fin.sum_univ_seven] at this; simp only [hc1] at this; linarith
  have h2 : -d 0 + 2 * d 2 - d 3 = 0 := by
    have := hrow 2; rw [Fin.sum_univ_seven] at this; simp only [hc2] at this; linarith
  have h3 : -d 1 - d 2 + 2 * d 3 - d 4 = 0 := by
    have := hrow 3; rw [Fin.sum_univ_seven] at this; simp only [hc3] at this; linarith
  have h4 : -d 3 + 2 * d 4 - d 5 = 0 := by
    have := hrow 4; rw [Fin.sum_univ_seven] at this; simp only [hc4] at this; linarith
  have h5 : -d 4 + 2 * d 5 - d 6 = 0 := by
    have := hrow 5; rw [Fin.sum_univ_seven] at this; simp only [hc5] at this; linarith
  have h6 : -d 5 + 2 * d 6 = 0 := by
    have := hrow 6; rw [Fin.sum_univ_seven] at this; simp only [hc6] at this; linarith
  have hd0 : ∀ i : Fin 7, d i = 0 := by
    intro i; fin_cases i <;> dsimp <;> omega
  ext i
  exact sub_eq_zero.mp (hd0 i)

theorem e7RootEigenvalue_eq_imp {r₁ r₂ : Fin 126}
    (h : ∀ i : Fin 7, e7RootEigenvalue i r₁ = e7RootEigenvalue i r₂) : r₁ = r₂ := by
  apply e7RootCoord_injective
  apply cartan_E7_mulVec_inj
  ext i
  exact h i

theorem h3zornE7RootWeight_injective : Function.Injective h3zornE7RootWeight := by
  intro r₁ r₂ heq
  apply e7RootEigenvalue_eq_imp
  intro i
  have hval := congrArg (fun f : Module.Dual ℝ h3zornE7Cartan =>
    f ⟨e7SimpleH i, e7SimpleH_mem_h3zornE7Cartan i⟩) heq
  rw [h3zornE7RootWeight_simpleH, h3zornE7RootWeight_simpleH] at hval
  exact Int.cast_injective hval

theorem e7RootVec_ne_zero (r : Fin 126) : e7RootVec r ≠ 0 := by
  by_cases hr0 : r.val < 72
  · simp only [e7RootVec, hr0, ↓reduceDIte]
    intro h0
    exact e6RootVec_ne_zero ⟨r.val, hr0⟩
      (h3zornCubicStabilizerToTKK_injective (h0.trans (map_zero _).symm))
  · by_cases hr1 : r.val < 99
    · simp only [e7RootVec, hr0, hr1, ↓reduceDIte]
      intro h0
      exact h3ZornBasis.ne_zero ⟨r.val - 72, by omega⟩
        (negInj_injective (h0.trans (map_zero _).symm))
    · simp only [e7RootVec, hr0, hr1, ↓reduceDIte]
      intro h0
      exact h3ZornBasis.ne_zero (traceDualIdx ⟨r.val - 99, by omega⟩)
        (posInj_injective (h0.trans (map_zero _).symm))

theorem e7RootVec_mem_rootSpace (r : Fin 126) :
    e7RootVec r ∈ LieAlgebra.rootSpace h3zornE7Cartan (h3zornE7RootWeight r) := by
  rw [LieAlgebra.rootSpace, LieModule.mem_genWeightSpace]
  intro H
  refine ⟨1, ?_⟩
  simp only [pow_one]
  change ⁅(H : H3ZornTKKLie), e7RootVec r⁆ - h3zornE7RootWeight r H • e7RootVec r = 0
  rw [e7RootVec_bracket_cartan H r, sub_self]

theorem e7RootSpace_ne_bot (r : Fin 126) :
    LieAlgebra.rootSpace h3zornE7Cartan (h3zornE7RootWeight r) ≠ ⊥ := by
  intro hbot
  have hmem := e7RootVec_mem_rootSpace r
  rw [hbot, LieSubmodule.mem_bot] at hmem
  exact e7RootVec_ne_zero r hmem

private theorem sum_fin126_split {M : Type*} [AddCommMonoid M] (f : Fin 126 → M) :
    ∑ r : Fin 126, f r =
      (∑ r : Fin 72, f ⟨r.val, by omega⟩) +
        (∑ k : Fin 27, f ⟨72 + k.val, by omega⟩) +
        (∑ k : Fin 27, f ⟨99 + k.val, by omega⟩) := by
  have h1 := Fin.sum_univ_add (a := 72) (b := 54) (fun r : Fin (72 + 54) => f r)
  have h2 := Fin.sum_univ_add (a := 27) (b := 27)
    (fun j : Fin (27 + 27) => f (Fin.natAdd 72 j))
  change ∑ r : Fin 126, f r =
    ∑ r : Fin 72, f ⟨r.val, by omega⟩ + ∑ j : Fin 54, f (Fin.natAdd 72 j) at h1
  change ∑ j : Fin 54, f (Fin.natAdd 72 j) =
    ∑ k : Fin 27, f ⟨72 + k.val, by omega⟩ +
      ∑ k : Fin 27, f ⟨99 + k.val, by omega⟩ at h2
  rw [h1, h2, add_assoc]

/-- The 133-element Chevalley basis `(e7SimpleH ⊕ e7RootVec)` of `H3ZornTKKLie` is linearly
independent. -/
theorem e7Chevalley_linearIndependent :
    LinearIndependent ℝ (Sum.elim e7SimpleH e7RootVec) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  have hneg : ∑ k : Fin 27, g (Sum.inr ⟨72 + k.val, by omega⟩) • h3ZornBasis k = 0 := by
    have hp := congrArg projNeg hg
    rw [map_zero, map_add, map_sum, map_sum] at hp
    have hH0 : ∀ i : Fin 7, projNeg (g (Sum.inl i) • e7SimpleH i) = 0 := by
      intro i
      rw [map_smul]
      by_cases hi : i.val < 6
      · have hi' : i = (⟨i.val, hi⟩ : Fin 6).castSucc := Fin.ext rfl
        rw [hi', e7SimpleH_castSucc]
        change _ • (0 : H3Zorn ℝ) = 0
        rw [smul_zero]
      · have hi6 : i = 6 := Fin.ext (by omega)
        rw [hi6, e7SimpleH_six]
        change _ • (0 : H3Zorn ℝ) = 0
        rw [smul_zero]
    have hR : ∑ r : Fin 126, projNeg (g (Sum.inr r) • e7RootVec r) =
        ∑ k : Fin 27, g (Sum.inr ⟨72 + k.val, by omega⟩) • h3ZornBasis k := by
      rw [sum_fin126_split]
      have hz1 : ∑ r : Fin 72,
          projNeg (g (Sum.inr ⟨r.val, by omega⟩) • e7RootVec ⟨r.val, by omega⟩) = 0 := by
        refine Finset.sum_eq_zero fun r _ => ?_
        simp only [e7RootVec, r.isLt, ↓reduceDIte, map_smul]
        change _ • (0 : H3Zorn ℝ) = 0
        rw [smul_zero]
      have hz2 : ∑ k : Fin 27, projNeg (g (Sum.inr ⟨99 + k.val, by omega⟩) •
          e7RootVec ⟨99 + k.val, by omega⟩) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        have hge72 : ¬((⟨99 + k.val, by omega⟩ : Fin 126).val < 72) := by dsimp; omega
        have hge99 : ¬((⟨99 + k.val, by omega⟩ : Fin 126).val < 99) := by dsimp; omega
        simp only [e7RootVec, hge72, hge99, ↓reduceDIte, map_smul]
        change _ • (0 : H3Zorn ℝ) = 0
        rw [smul_zero]
      rw [hz1, zero_add, hz2, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hge72 : ¬((⟨72 + k.val, by omega⟩ : Fin 126).val < 72) := by dsimp; omega
      have hlt99 : (⟨72 + k.val, by omega⟩ : Fin 126).val < 99 := by dsimp; omega
      have hk : (⟨(⟨72 + k.val, by omega⟩ : Fin 126).val - 72, by omega⟩ : Fin 27) = k :=
        Fin.ext (by dsimp; omega)
      simp only [e7RootVec, hge72, hlt99, ↓reduceDIte, hk, map_smul]
      rfl
    rw [Finset.sum_eq_zero (fun i _ => hH0 i), zero_add, hR] at hp
    exact hp
  have hb_neg : ∀ k : Fin 27, g (Sum.inr ⟨72 + k.val, by omega⟩) = 0 :=
    Fintype.linearIndependent_iff.mp h3ZornBasis.linearIndependent _ hneg
  have hpos : ∑ k : Fin 27, g (Sum.inr ⟨99 + k.val, by omega⟩) •
      h3ZornBasis (traceDualIdx k) = 0 := by
    have hp := congrArg projPos hg
    rw [map_zero, map_add, map_sum, map_sum] at hp
    have hH0 : ∀ i : Fin 7, projPos (g (Sum.inl i) • e7SimpleH i) = 0 := by
      intro i
      rw [map_smul]
      by_cases hi : i.val < 6
      · have hi' : i = (⟨i.val, hi⟩ : Fin 6).castSucc := Fin.ext rfl
        rw [hi', e7SimpleH_castSucc]
        change _ • (0 : H3Zorn ℝ) = 0
        rw [smul_zero]
      · have hi6 : i = 6 := Fin.ext (by omega)
        rw [hi6, e7SimpleH_six]
        change _ • (0 : H3Zorn ℝ) = 0
        rw [smul_zero]
    have hR : ∑ r : Fin 126, projPos (g (Sum.inr r) • e7RootVec r) =
        ∑ k : Fin 27, g (Sum.inr ⟨99 + k.val, by omega⟩) • h3ZornBasis (traceDualIdx k) := by
      rw [sum_fin126_split]
      have hz1 : ∑ r : Fin 72,
          projPos (g (Sum.inr ⟨r.val, by omega⟩) • e7RootVec ⟨r.val, by omega⟩) = 0 := by
        refine Finset.sum_eq_zero fun r _ => ?_
        simp only [e7RootVec, r.isLt, ↓reduceDIte, map_smul]
        change _ • (0 : H3Zorn ℝ) = 0
        rw [smul_zero]
      have hz2 : ∑ k : Fin 27, projPos (g (Sum.inr ⟨72 + k.val, by omega⟩) •
          e7RootVec ⟨72 + k.val, by omega⟩) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        have hge72 : ¬((⟨72 + k.val, by omega⟩ : Fin 126).val < 72) := by dsimp; omega
        have hlt99 : (⟨72 + k.val, by omega⟩ : Fin 126).val < 99 := by dsimp; omega
        simp only [e7RootVec, hge72, hlt99, ↓reduceDIte, map_smul]
        change _ • (0 : H3Zorn ℝ) = 0
        rw [smul_zero]
      rw [hz1, zero_add, hz2, zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hge72 : ¬((⟨99 + k.val, by omega⟩ : Fin 126).val < 72) := by dsimp; omega
      have hge99 : ¬((⟨99 + k.val, by omega⟩ : Fin 126).val < 99) := by dsimp; omega
      have hk : (⟨(⟨99 + k.val, by omega⟩ : Fin 126).val - 99, by omega⟩ : Fin 27) = k :=
        Fin.ext (by dsimp; omega)
      simp only [e7RootVec, hge72, hge99, ↓reduceDIte, hk, map_smul]
      rfl
    rw [Finset.sum_eq_zero (fun i _ => hH0 i), zero_add, hR] at hp
    exact hp
  have hb_pos : ∀ k : Fin 27, g (Sum.inr ⟨99 + k.val, by omega⟩) = 0 := by
    have hli : LinearIndependent ℝ (fun k : Fin 27 => h3ZornBasis (traceDualIdx k)) :=
      h3ZornBasis.linearIndependent.comp traceDualIdx traceDualIdx_bijective.injective
    exact Fintype.linearIndependent_iff.mp hli _ hpos
  have hzero_part : (∑ i : Fin 7, g (Sum.inl i) • e7SimpleH i) +
      (∑ r : Fin 72, g (Sum.inr ⟨r.val, by omega⟩) •
        h3zornCubicStabilizerToTKK (e6RootVec r)) = 0 := by
    have hg' := hg
    rw [sum_fin126_split] at hg'
    have h1 : ∀ k : Fin 27, g (Sum.inr ⟨72 + k.val, by omega⟩) •
        e7RootVec ⟨72 + k.val, by omega⟩ = 0 := fun k => by rw [hb_neg k, zero_smul]
    have h2 : ∀ k : Fin 27, g (Sum.inr ⟨99 + k.val, by omega⟩) •
        e7RootVec ⟨99 + k.val, by omega⟩ = 0 := fun k => by rw [hb_pos k, zero_smul]
    have h0 : ∀ r : Fin 72, g (Sum.inr ⟨r.val, by omega⟩) •
        e7RootVec ⟨r.val, by omega⟩ =
        g (Sum.inr ⟨r.val, by omega⟩) •
          h3zornCubicStabilizerToTKK (e6RootVec r) := fun r => by
      simp only [e7RootVec, r.isLt, ↓reduceDIte]
    simp only [h1, h2, h0, Finset.sum_const_zero, add_zero] at hg'
    exact hg'
  let d : Fin 6 → ℝ := ![2 / 3, 1, 4 / 3, 2, 5 / 3, 4 / 3]
  have hd_sum : (2 / 3 : ℝ) • e7SimpleH 0 + e7SimpleH 1 + (4 / 3 : ℝ) • e7SimpleH 2 +
      (2 : ℝ) • e7SimpleH 3 + (5 / 3 : ℝ) • e7SimpleH 4 + (4 / 3 : ℝ) • e7SimpleH 5 =
      ∑ i : Fin 6, d i • e7SimpleH i.castSucc := by
    rw [Fin.sum_univ_six]
    simp only [d, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul]
    rfl
  have hcomb : (g (Sum.inl 6) * (2 / 3 : ℝ)) • h3zornTKKGradeOp +
      h3zornCubicStabilizerToTKK
        (∑ i : Fin 6, (g (Sum.inl i.castSucc) - g (Sum.inl 6) * d i) • e6SimpleH i +
          ∑ r : Fin 72, g (Sum.inr ⟨r.val, by omega⟩) • e6RootVec r) = 0 := by
    have h6 := e7SimpleH_six_eq_linear_comb
    rw [hd_sum] at h6
    have hsplit : ∑ i : Fin 7, g (Sum.inl i) • e7SimpleH i =
        (∑ i : Fin 6, g (Sum.inl i.castSucc) • e7SimpleH i.castSucc) +
          g (Sum.inl 6) • e7SimpleH 6 := by
      rw [Fin.sum_univ_castSucc]; rfl
    rw [hsplit, h6, smul_sub, smul_smul, Finset.smul_sum] at hzero_part
    have hsm : ∑ x : Fin 6, g (Sum.inl 6) • (d x • e7SimpleH x.castSucc) =
        ∑ x : Fin 6, (g (Sum.inl 6) * d x) • e7SimpleH x.castSucc :=
      Finset.sum_congr rfl fun x _ => smul_smul _ _ _
    rw [hsm] at hzero_part
    have h_e6_part : h3zornCubicStabilizerToTKK
          (∑ i : Fin 6, (g (Sum.inl i.castSucc) - g (Sum.inl 6) * d i) • e6SimpleH i) =
        ∑ i : Fin 6, g (Sum.inl i.castSucc) • e7SimpleH i.castSucc -
          ∑ i : Fin 6, (g (Sum.inl 6) * d i) • e7SimpleH i.castSucc := by
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← e7SimpleH_castSucc, sub_smul]
    have h_r_part : h3zornCubicStabilizerToTKK
          (∑ r : Fin 72, g (Sum.inr ⟨r.val, by omega⟩) • e6RootVec r) =
        ∑ r : Fin 72, g (Sum.inr ⟨r.val, by omega⟩) •
          h3zornCubicStabilizerToTKK (e6RootVec r) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun r _ => map_smul _ _ _
    rw [map_add, h_e6_part, h_r_part, ← hzero_part]
    abel
  have hg6 : g (Sum.inl 6) = 0 := by
    by_contra hne6
    have hne : g (Sum.inl 6) * (2 / 3 : ℝ) ≠ 0 := mul_ne_zero hne6 (by norm_num)
    have hmem : (g (Sum.inl 6) * (2 / 3 : ℝ)) • h3zornStrOne.1 ∈ h3zornCubicStabilizer := by
      let T0 : h3zornCubicStabilizer :=
        ∑ i : Fin 6, (g (Sum.inl i.castSucc) - g (Sum.inl 6) * d i) • e6SimpleH i +
          ∑ r : Fin 72, g (Sum.inr ⟨r.val, by omega⟩) • e6RootVec r
      have hcomb' : (g (Sum.inl 6) * (2 / 3 : ℝ)) • h3zornTKKGradeOp +
          h3zornCubicStabilizerToTKK T0 = 0 := hcomb
      have hz := congrArg (fun X : H3ZornTKKLie => X.zero.1) hcomb'
      have hadd : ∀ X Y : H3ZornTKKLie, (X + Y).zero.1 = X.zero.1 + Y.zero.1 := fun _ _ => rfl
      have hsm : ∀ (r : ℝ) (X : H3ZornTKKLie), (r • X).zero.1 = r • X.zero.1 := fun _ _ => rfl
      have hg1 : h3zornTKKGradeOp.zero.1 = h3zornStrOne.1 := rfl
      have ht1 : (h3zornCubicStabilizerToTKK T0).zero.1 = T0.1 := rfl
      have hz0 : (0 : H3ZornTKKLie).zero.1 = 0 := rfl
      rw [hadd, hsm, hg1, ht1, hz0] at hz
      rw [eq_neg_of_add_eq_zero_left hz]
      exact h3zornCubicStabilizer.neg_mem T0.2
    have h1 := h3zornCubicStabilizer.smul_mem (g (Sum.inl 6) * (2 / 3 : ℝ))⁻¹ hmem
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at h1
    exact h3zornStrOne_not_mem_cubicStabilizer h1
  have he6_0 : ∑ i : Fin 6, g (Sum.inl i.castSucc) • e6SimpleH i +
      ∑ r : Fin 72, g (Sum.inr ⟨r.val, by omega⟩) • e6RootVec r = 0 := by
    apply h3zornCubicStabilizerToTKK_injective
    simpa only [hg6, zero_mul, zero_smul, zero_add, sub_zero, map_zero] using hcomb
  have he6_li := Fintype.linearIndependent_iff.mp e6Chevalley_linearIndependent
    (Sum.elim (fun i : Fin 6 => g (Sum.inl i.castSucc))
      (fun r : Fin 72 => g (Sum.inr ⟨r.val, by omega⟩)))
    (by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      apply Subtype.ext
      have he6_val := congrArg Subtype.val he6_0
      simp only [ZeroMemClass.coe_zero, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul,
        AddMemClass.coe_add] at he6_val ⊢
      exact he6_val)
  rintro (i | r)
  · by_cases hi : i.val < 6
    · have hi' : i = (⟨i.val, hi⟩ : Fin 6).castSucc := Fin.ext rfl
      rw [hi']; exact he6_li (Sum.inl ⟨i.val, hi⟩)
    · have hi6 : i = 6 := Fin.ext (by omega)
      rw [hi6]; exact hg6
  · by_cases hr0 : r.val < 72
    · have hr' : r = ⟨(⟨r.val, hr0⟩ : Fin 72).val, by omega⟩ := Fin.ext rfl
      rw [hr']; exact he6_li (Sum.inr ⟨r.val, hr0⟩)
    · by_cases hr1 : r.val < 99
      · have hr' : r = ⟨72 + (⟨r.val - 72, by omega⟩ : Fin 27).val, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hr']; exact hb_neg ⟨r.val - 72, by omega⟩
      · have hr' : r = ⟨99 + (⟨r.val - 99, by omega⟩ : Fin 27).val, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hr']; exact hb_pos ⟨r.val - 99, by omega⟩

/-- The 133-element Chevalley basis `(e7SimpleH ⊕ e7RootVec)` of `H3ZornTKKLie`. -/
def e7ChevalleyBasis : Module.Basis (Fin 7 ⊕ Fin 126) ℝ H3ZornTKKLie :=
  basisOfLinearIndependentOfCardEqFinrank e7Chevalley_linearIndependent
    (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, finrank_H3ZornTKKLie])

@[simp] theorem e7ChevalleyBasis_inl (i : Fin 7) :
    e7ChevalleyBasis (Sum.inl i) = e7SimpleH i := by
  simp [e7ChevalleyBasis]

@[simp] theorem e7ChevalleyBasis_inr (r : Fin 126) :
    e7ChevalleyBasis (Sum.inr r) = e7RootVec r := by
  simp [e7ChevalleyBasis]

end RootDecompositionAndBasis

section CartanAndTriangularizable

/-- Vandermonde weight-killing lemma for `H3ZornTKKLie` submodules invariant under `h3zornE7Cartan`:
if `h + ∑ r ∈ A, b r • e7RootVec r ∈ S` with `h ∈ h3zornE7Cartan`, then `h ∈ S` and each
`b r • e7RootVec r ∈ S`. -/
theorem e7_cartan_weight_kill_mem
    (S : Submodule ℝ H3ZornTKKLie)
    (hS : ∀ (i : Fin 7) (x : H3ZornTKKLie), x ∈ S → ⁅e7SimpleH i, x⁆ ∈ S)
    (A : Finset (Fin 126)) (h : H3ZornTKKLie) (hh : h ∈ h3zornE7Cartan)
    (b : Fin 126 → ℝ) (hx : h + ∑ r ∈ A, b r • e7RootVec r ∈ S) :
    h ∈ S ∧ ∀ r ∈ A, b r • e7RootVec r ∈ S := by
  have hKillH : ∀ (u : H3ZornTKKLie), u ∈ h3zornE7Cartan →
      ∀ (i : Fin 7), ⁅e7SimpleH i, u⁆ = 0 := by
    intro u hu i
    have hi : e7SimpleH i ∈ h3zornE7Cartan := e7SimpleH_mem_h3zornE7Cartan i
    have hc := (inferInstance : IsLieAbelian h3zornE7Cartan).trivial ⟨e7SimpleH i, hi⟩ ⟨u, hu⟩
    exact congrArg Subtype.val hc
  suffices hMain : ∀ n : ℕ, ∀ (B : Finset (Fin 126)) (h0 : H3ZornTKKLie),
      h0 ∈ h3zornE7Cartan → B.card = n →
      ∀ (c : Fin 126 → ℝ), h0 + ∑ r ∈ B, c r • e7RootVec r ∈ S →
        h0 ∈ S ∧ ∀ r ∈ B, c r • e7RootVec r ∈ S from
    hMain A.card A h hh rfl b hx
  intro n
  induction n with
  | zero =>
    intro B h0 hh0 hcard c hc
    rw [Finset.card_eq_zero.mp hcard] at hc ⊢
    simp only [Finset.sum_empty, add_zero] at hc
    exact ⟨hc, fun _ hr => absurd hr (Finset.notMem_empty _)⟩
  | succ n ih =>
    intro B h0 hh0 hcard c hc
    by_cases hn : n = 0
    · subst hn
      rw [Finset.card_eq_one] at hcard
      rcases hcard with ⟨r₀, rfl⟩
      simp only [Finset.sum_singleton] at hc
      obtain ⟨i₀, hi₀⟩ := e7RootEigenvalue_ne_zero r₀
      have hbr := hS i₀ _ hc
      rw [lie_add, hKillH h0 hh0 i₀, zero_add, lie_smul, e7RootVec_bracket_H, smul_smul] at hbr
      have hk₀ : (e7RootEigenvalue i₀ r₀ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hi₀
      have hroot : c r₀ • e7RootVec r₀ ∈ S := by
        have hs := S.smul_mem (e7RootEigenvalue i₀ r₀ : ℝ)⁻¹ hbr
        rw [smul_smul, mul_comm (c r₀), ← mul_assoc, inv_mul_cancel₀ hk₀, one_mul] at hs
        exact hs
      have hh0_mem : h0 ∈ S := by
        have hsub := S.sub_mem hc hroot
        simpa [add_sub_cancel_right] using hsub
      exact ⟨hh0_mem, fun r hr => by
        rw [Finset.mem_singleton] at hr
        subst hr
        exact hroot⟩
    · have hpos : 1 < B.card := by omega
      obtain ⟨r₀, hr₀, r₁, hr₁, hne⟩ := Finset.one_lt_card.mp hpos
      have hdiff : ∃ i₁ : Fin 7, e7RootEigenvalue i₁ r₀ ≠ e7RootEigenvalue i₁ r₁ := by
        by_contra hcon
        push Not at hcon
        exact hne (e7RootEigenvalue_eq_imp hcon)
      obtain ⟨i₁, hi₁⟩ := hdiff
      let lam0 : ℝ := e7RootEigenvalue i₁ r₀
      have hy : ⁅e7SimpleH i₁, h0 + ∑ r ∈ B, c r • e7RootVec r⁆ -
          lam0 • (h0 + ∑ r ∈ B, c r • e7RootVec r) ∈ S :=
        S.sub_mem (hS i₁ _ hc) (S.smul_mem lam0 hc)
      let c' : Fin 126 → ℝ := fun r => c r * ((e7RootEigenvalue i₁ r : ℝ) - lam0)
      have hy_eq : ⁅e7SimpleH i₁, h0 + ∑ r ∈ B, c r • e7RootVec r⁆ -
          lam0 • (h0 + ∑ r ∈ B, c r • e7RootVec r) =
          (-lam0) • h0 + ∑ r ∈ B.erase r₀, c' r • e7RootVec r := by
        rw [lie_add, hKillH h0 hh0 i₁, zero_add, lie_sum, smul_add, Finset.smul_sum]
        have h1 : ∑ r ∈ B, ⁅e7SimpleH i₁, c r • e7RootVec r⁆ =
            ∑ r ∈ B, (c r * (e7RootEigenvalue i₁ r : ℝ)) • e7RootVec r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [lie_smul, e7RootVec_bracket_H, smul_smul]
        rw [h1]
        have h2 : ∑ r ∈ B, (c r * (e7RootEigenvalue i₁ r : ℝ)) • e7RootVec r -
            (lam0 • h0 + ∑ r ∈ B, lam0 • (c r • e7RootVec r)) =
            (-lam0) • h0 + ∑ r ∈ B, c' r • e7RootVec r := by
          rw [sub_eq_add_neg, neg_add, ← neg_smul lam0 h0,
            add_comm (-lam0 • h0) (-(∑ r ∈ B, lam0 • (c r • e7RootVec r))), ← add_assoc,
            add_comm (∑ r ∈ B, (c r * (e7RootEigenvalue i₁ r : ℝ)) • e7RootVec r +
              -(∑ r ∈ B, lam0 • (c r • e7RootVec r))) ((-lam0) • h0)]
          congr 1
          rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          dsimp [c']
          rw [smul_smul, ← sub_smul]
          congr 1; ring
        rw [h2, ← Finset.add_sum_erase B (fun r => c' r • e7RootVec r) hr₀]
        have hc'0 : c' r₀ = 0 := by simp [c', lam0]
        rw [hc'0, zero_smul, zero_add]
      rw [hy_eq] at hy
      have hcard0 : (B.erase r₀).card = n := by rw [Finset.card_erase_of_mem hr₀, hcard]; simp
      have ih0 := ih (B.erase r₀) ((-lam0) • h0) (h3zornE7Cartan.smul_mem (-lam0) hh0) hcard0 c' hy
      have hr₁_erase : r₁ ∈ B.erase r₀ := Finset.mem_erase.mpr ⟨hne.symm, hr₁⟩
      have hc'r₁ := ih0.2 r₁ hr₁_erase
      have hlam_ne : ((e7RootEigenvalue i₁ r₁ : ℝ) - lam0) ≠ 0 := by
        intro heq
        apply hi₁
        exact (Int.cast_injective (sub_eq_zero.mp heq)).symm
      have hr₁_mem : c r₁ • e7RootVec r₁ ∈ S := by
        have hs := S.smul_mem ((e7RootEigenvalue i₁ r₁ : ℝ) - lam0)⁻¹ hc'r₁
        dsimp [c'] at hs
        rw [smul_smul, mul_comm (c r₁), ← mul_assoc, inv_mul_cancel₀ hlam_ne, one_mul] at hs
        exact hs
      have hx_erase : h0 + ∑ r ∈ B.erase r₁, c r • e7RootVec r ∈ S := by
        have hsub := S.sub_mem hc hr₁_mem
        have hs_eq : (h0 + ∑ r ∈ B, c r • e7RootVec r) - c r₁ • e7RootVec r₁ =
            h0 + ∑ r ∈ B.erase r₁, c r • e7RootVec r := by
          rw [← Finset.add_sum_erase B _ hr₁]
          abel
        rwa [hs_eq] at hsub
      have hcard1 : (B.erase r₁).card = n := by rw [Finset.card_erase_of_mem hr₁, hcard]; simp
      have ih1 := ih (B.erase r₁) h0 hh0 hcard1 c hx_erase
      refine ⟨ih1.1, fun r hr => ?_⟩
      by_cases heq : r = r₁
      · subst heq; exact hr₁_mem
      · exact ih1.2 r (Finset.mem_erase.mpr ⟨heq, hr⟩)

/-- `h3zornE7Cartan` is a genuine 7D split Cartan subalgebra of `H3ZornTKKLie`. -/
instance h3zornE7Cartan_isCartanSubalgebra : h3zornE7Cartan.IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := by
    apply le_antisymm _ h3zornE7Cartan.le_normalizer
    intro x hx
    have hrep := e7ChevalleyBasis.sum_repr x
    rw [Fintype.sum_sum_type] at hrep
    simp only [e7ChevalleyBasis_inl, e7ChevalleyBasis_inr] at hrep
    have hhpart : (∑ i : Fin 7, (e7ChevalleyBasis.repr x) (Sum.inl i) • e7SimpleH i) ∈
        h3zornE7Cartan :=
      Submodule.sum_mem _ fun i _ => h3zornE7Cartan.smul_mem _ (e7SimpleH_mem_h3zornE7Cartan i)
    have hb0 : ∀ r : Fin 126, (e7ChevalleyBasis.repr x) (Sum.inr r) = 0 := by
      intro r
      obtain ⟨i, hi⟩ := e7RootEigenvalue_ne_zero r
      have hnorm : ⁅e7SimpleH i, x⁆ ∈ h3zornE7Cartan := by
        have hxmem := (LieSubalgebra.mem_normalizer_iff h3zornE7Cartan x).mp hx (e7SimpleH i)
          (e7SimpleH_mem_h3zornE7Cartan i)
        have hneg := h3zornE7Cartan.neg_mem hxmem
        rw [← lie_skew, neg_neg] at hneg
        exact hneg
      have hKillH :
          ⁅e7SimpleH i, ∑ j : Fin 7, (e7ChevalleyBasis.repr x) (Sum.inl j) • e7SimpleH j⁆ = 0 := by
        have hc := (inferInstance : IsLieAbelian h3zornE7Cartan).trivial
          ⟨e7SimpleH i, e7SimpleH_mem_h3zornE7Cartan i⟩ ⟨_, hhpart⟩
        exact congrArg Subtype.val hc
      have hbr : ⁅e7SimpleH i, x⁆ =
          ∑ q : Fin 126, ((e7ChevalleyBasis.repr x) (Sum.inr q) *
            (e7RootEigenvalue i q : ℝ)) • e7RootVec q := by
        conv_lhs => rw [← hrep]
        rw [lie_add, hKillH, zero_add, lie_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [lie_smul, e7RootVec_bracket_H, smul_smul]
      have hmem : (-⁅e7SimpleH i, x⁆) +
          ∑ q : Fin 126, ((e7ChevalleyBasis.repr x) (Sum.inr q) *
            (e7RootEigenvalue i q : ℝ)) • e7RootVec q ∈
            (⊥ : Submodule ℝ H3ZornTKKLie) := by
        rw [← hbr, neg_add_cancel]
        exact Submodule.zero_mem _
      have hkill := e7_cartan_weight_kill_mem ⊥ (fun _ y hy => by
        rw [Submodule.mem_bot] at hy; subst hy; simp)
        Finset.univ (-⁅e7SimpleH i, x⁆) (h3zornE7Cartan.neg_mem hnorm)
        (fun q => (e7ChevalleyBasis.repr x) (Sum.inr q) * (e7RootEigenvalue i q : ℝ)) hmem
      have hr0 : ((e7ChevalleyBasis.repr x) (Sum.inr r) *
          (e7RootEigenvalue i r : ℝ)) • e7RootVec r = 0 :=
        (Submodule.mem_bot ℝ).mp (hkill.2 r (Finset.mem_univ r))
      have hmul0 := (smul_eq_zero.mp hr0).resolve_right (e7RootVec_ne_zero r)
      exact (mul_eq_zero.mp hmul0).resolve_right (Int.cast_ne_zero.mpr hi)
    have hs0 : (∑ r : Fin 126, (e7ChevalleyBasis.repr x) (Sum.inr r) • e7RootVec r) = 0 :=
      Finset.sum_eq_zero fun r _ => by rw [hb0 r, zero_smul]
    rw [← hrep, hs0, add_zero]
    exact hhpart

instance h3zornE7Cartan_isTriangularizable :
    LieModule.IsTriangularizable ℝ h3zornE7Cartan H3ZornTKKLie := by
  refine ⟨fun H => ?_⟩
  apply (Submodule.eq_top_iff_forall_basis_mem e7ChevalleyBasis).mpr
  rintro (i | r)
  · apply Submodule.mem_iSup_of_mem (0 : ℝ)
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff, e7ChevalleyBasis_inl, zero_smul]
    have hc := (inferInstance : IsLieAbelian h3zornE7Cartan).trivial H
      ⟨e7SimpleH i, e7SimpleH_mem_h3zornE7Cartan i⟩
    exact congrArg Subtype.val hc
  · apply Submodule.mem_iSup_of_mem (h3zornE7RootWeight r H)
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff, e7ChevalleyBasis_inr]
    exact e7RootVec_bracket_cartan H r

end CartanAndTriangularizable

section SimplicityHelpersAndSerre

/-- Any bracket of opposite root vectors lies in `h3zornE7Cartan`. -/
theorem e7RootVec_opposite_bracket_mem_cartan {r₁ r₂ : Fin 126}
    (hopp : e7RootCoord r₁ + e7RootCoord r₂ = 0) :
    ⁅e7RootVec r₁, e7RootVec r₂⁆ ∈ h3zornE7Cartan := by
  rw [← h3zornE7Cartan_isCartanSubalgebra.self_normalizing, LieSubalgebra.mem_normalizer_iff]
  intro H hH
  change H ∈ Submodule.span ℝ (Set.range e7SimpleH) at hH
  have hcomm : ∀ i : Fin 7, ⁅e7SimpleH i, ⁅e7RootVec r₁, e7RootVec r₂⁆⁆ = 0 := by
    intro i
    rw [leibniz_lie, e7RootVec_bracket_H, e7RootVec_bracket_H, smul_lie, lie_smul, ← add_smul]
    have hsum : e7RootEigenvalue i r₁ + e7RootEigenvalue i r₂ = 0 := by
      simp only [e7RootEigenvalue, ← Finset.sum_add_distrib, ← mul_add]
      have h0 : ∀ j : Fin 7, e7RootCoord r₁ j + e7RootCoord r₂ j = 0 :=
        fun j => congrFun hopp j
      simp [h0]
    have hsumR : (e7RootEigenvalue i r₁ : ℝ) + (e7RootEigenvalue i r₂ : ℝ) = 0 := by
      exact_mod_cast hsum
    rw [hsumR, zero_smul]
  induction hH using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ih₁ ih₂ => rw [lie_add]; exact h3zornE7Cartan.add_mem ih₁ ih₂
  | smul c _ _ ih => rw [lie_smul]; exact h3zornE7Cartan.smul_mem c ih
  | mem _ h =>
    rcases h with ⟨i, rfl⟩
    rw [← lie_skew, hcomm i, neg_zero]
    exact h3zornE7Cartan.zero_mem

theorem negInj_bracket_posInj_traceDual_mem_cartan (k : Fin 27) :
    ⁅negInj (h3ZornBasis k), posInj (h3ZornBasis (traceDualIdx k))⁆ ∈ h3zornE7Cartan := by
  let r₁ : Fin 126 := ⟨72 + k.val, by omega⟩
  let r₂ : Fin 126 := ⟨99 + k.val, by omega⟩
  have h1 : e7RootVec r₁ = negInj (h3ZornBasis k) := by
    have hge : ¬(r₁.val < 72) := by dsimp [r₁]; omega
    have hlt : r₁.val < 99 := by dsimp [r₁]; omega
    have hk : (⟨r₁.val - 72, by omega⟩ : Fin 27) = k := Fin.ext (by dsimp [r₁]; omega)
    simp [e7RootVec, hge, hlt, hk]
  have h2 : e7RootVec r₂ = posInj (h3ZornBasis (traceDualIdx k)) := by
    have hge1 : ¬(r₂.val < 72) := by dsimp [r₂]; omega
    have hge2 : ¬(r₂.val < 99) := by dsimp [r₂]; omega
    have hk : (⟨r₂.val - 99, by omega⟩ : Fin 27) = k := Fin.ext (by dsimp [r₂]; omega)
    simp [e7RootVec, hge1, hge2, hk]
  rw [← h1, ← h2]
  apply e7RootVec_opposite_bracket_mem_cartan
  have hge1 : ¬(r₁.val < 72) := by dsimp [r₁]; omega
  have hlt1 : r₁.val < 99 := by dsimp [r₁]; omega
  have hge2 : ¬(r₂.val < 72) := by dsimp [r₂]; omega
  have hge3 : ¬(r₂.val < 99) := by dsimp [r₂]; omega
  have hk1 : (⟨r₁.val - 72, by omega⟩ : Fin 27) = k := Fin.ext (by dsimp [r₁]; omega)
  have hk2 : (⟨r₂.val - 99, by omega⟩ : Fin 27) = k := Fin.ext (by dsimp [r₂]; omega)
  simp [e7RootCoord, hge1, hlt1, hge2, hge3, hk1, hk2]

private theorem twoLData_dual_trace_ne_zero (k : Fin 27) :
    sparseVal (twoLData k) 0 (traceDualIdx k) +
      sparseVal (twoLData k) 1 (traceDualIdx k) +
      sparseVal (twoLData k) 2 (traceDualIdx k) ≠ 0 := by
  have h : (List.finRange 27).all (fun k =>
      sparseVal (twoLData k) 0 (traceDualIdx k) +
        sparseVal (twoLData k) 1 (traceDualIdx k) +
        sparseVal (twoLData k) 2 (traceDualIdx k) != 0) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, bne_iff_ne, ne_eq] at h
  exact h k

theorem negInj_bracket_posInj_traceDual_ne_zero (k : Fin 27) :
    ⁅negInj (h3ZornBasis k), posInj (h3ZornBasis (traceDualIdx k))⁆ ≠ 0 := by
  intro h0
  have h1 := congrArg (fun X : H3ZornTKKLie => linearTrace (X.zero.1 (1 : H3Zorn ℝ))) h0
  rw [negInj_bracket_posInj] at h1
  have h0_tr : linearTrace ((0 : H3ZornTKKLie).zero.1 (1 : H3Zorn ℝ)) = 0 := by
    change linearTrace ((0 : Module.End ℝ (H3Zorn ℝ)) 1) = 0
    rw [LinearMap.zero_apply]
    change (0 : ℝ) + 0 + 0 = 0
    norm_num
  rw [h0_tr] at h1
  change linearTrace (JordanTKK.triple (h3ZornBasis k) (h3ZornBasis (traceDualIdx k)) 1) = 0 at h1
  have htr_id : JordanTKK.triple (h3ZornBasis k) (h3ZornBasis (traceDualIdx k)) 1 =
      h3ZornBasis k * h3ZornBasis (traceDualIdx k) := by
    have hm1 : ∀ x : H3Zorn ℝ, x * (1 : H3Zorn ℝ) = x := fun x => by
      change candidateJordanMul x 1 = x; exact candidateJordanMul_one_right x
    have h1m : ∀ x : H3Zorn ℝ, (1 : H3Zorn ℝ) * x = x := fun x => by
      change candidateJordanMul 1 x = x; exact candidateJordanMul_one_left x
    change (h3ZornBasis k * h3ZornBasis (traceDualIdx k)) * 1 +
      (1 * h3ZornBasis (traceDualIdx k)) * h3ZornBasis k -
      (h3ZornBasis k * 1) * h3ZornBasis (traceDualIdx k) =
      h3ZornBasis k * h3ZornBasis (traceDualIdx k)
    rw [hm1, h1m, hm1, mul_comm (h3ZornBasis (traceDualIdx k)) (h3ZornBasis k),
      add_sub_cancel_right]
  rw [htr_id] at h1
  have h2tr : linearTrace ((2 : ℝ) • (h3ZornBasis k * h3ZornBasis (traceDualIdx k))) = 0 := by
    rw [linearTrace_smul, h1, mul_zero]
  have hentry : ∀ r : Fin 27,
      h3ZornCoordinate ((2 : ℝ) • (h3ZornBasis k * h3ZornBasis (traceDualIdx k))) r =
        (sparseVal (twoLData k) r (traceDualIdx k) : ℝ) := by
    intro r
    have hc := congrArg (fun M : Matrix (Fin 27) (Fin 27) ℝ => M r (traceDualIdx k))
      (h3zornToMatrix_two_jordanLmul_basis k)
    rw [h3zornToMatrix_apply, Matrix.map_apply] at hc
    exact hc
  have hsum : linearTrace ((2 : ℝ) • (h3ZornBasis k * h3ZornBasis (traceDualIdx k))) =
      ((sparseVal (twoLData k) 0 (traceDualIdx k) +
        sparseVal (twoLData k) 1 (traceDualIdx k) +
        sparseVal (twoLData k) 2 (traceDualIdx k) : ℤ) : ℝ) := by
    have h0' := hentry 0
    have h1' := hentry 1
    have h2' := hentry 2
    change ((2 : ℝ) • (h3ZornBasis k * h3ZornBasis (traceDualIdx k))).α₁ = _ at h0'
    change ((2 : ℝ) • (h3ZornBasis k * h3ZornBasis (traceDualIdx k))).α₂ = _ at h1'
    change ((2 : ℝ) • (h3ZornBasis k * h3ZornBasis (traceDualIdx k))).α₃ = _ at h2'
    change ((2 : ℝ) • (h3ZornBasis k * h3ZornBasis (traceDualIdx k))).α₁ +
        ((2 : ℝ) • (h3ZornBasis k * h3ZornBasis (traceDualIdx k))).α₂ +
        ((2 : ℝ) • (h3ZornBasis k * h3ZornBasis (traceDualIdx k))).α₃ = _
    push_cast
    linarith
  rw [hsum] at h2tr
  exact twoLData_dual_trace_ne_zero k (Int.cast_eq_zero.mp h2tr)

/-- Opposite root index involution on `Fin 72` (`e6RootCoord (e6RootOpp r) = -e6RootCoord r`). -/
def e6RootOpp (r : Fin 72) : Fin 72 :=
  match r.val with
  | 0 => 20 | 1 => 22 | 2 => 23 | 3 => 10 | 4 => 14 | 5 => 17 | 6 => 18 | 7 => 19
  | 8 => 12 | 9 => 15 | 10 => 3 | 11 => 21 | 12 => 8 | 13 => 16 | 14 => 4 | 15 => 9
  | 16 => 13 | 17 => 5 | 18 => 6 | 19 => 7 | 20 => 0 | 21 => 11 | 22 => 1 | 23 => 2
  | 24 => 39 | 25 => 38 | 26 => 33 | 27 => 32 | 28 => 35 | 29 => 34 | 30 => 37 | 31 => 36
  | 32 => 27 | 33 => 26 | 34 => 29 | 35 => 28 | 36 => 31 | 37 => 30 | 38 => 25 | 39 => 24
  | 40 => 55 | 41 => 54 | 42 => 49 | 43 => 48 | 44 => 51 | 45 => 50 | 46 => 53 | 47 => 52
  | 48 => 43 | 49 => 42 | 50 => 45 | 51 => 44 | 52 => 47 | 53 => 46 | 54 => 41 | 55 => 40
  | 56 => 71 | 57 => 70 | 58 => 65 | 59 => 64 | 60 => 67 | 61 => 66 | 62 => 69 | 63 => 68
  | 64 => 59 | 65 => 58 | 66 => 61 | 67 => 60 | 68 => 63 | 69 => 62 | 70 => 57 | 71 => 56
  | _ => 0

theorem e6RootCoord_opp (r : Fin 72) : e6RootCoord (e6RootOpp r) = -e6RootCoord r := by
  have h : (List.finRange 72).all (fun r =>
      List.ofFn (e6RootCoord (e6RootOpp r)) == List.ofFn (-e6RootCoord r)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact List.ofFn_injective (h r)

theorem e6RootVec_opposite_bracket_mem_cartan (r : Fin 72) :
    ⁅e6RootVec r, e6RootVec (e6RootOpp r)⁆ ∈ h3zornCartan := by
  rw [← h3zornCartan_isCartanSubalgebra.self_normalizing, LieSubalgebra.mem_normalizer_iff]
  intro H hH
  change H ∈ Submodule.span ℝ (Set.range e6SimpleH) at hH
  have hcomm : ∀ i : Fin 6, ⁅e6SimpleH i, ⁅e6RootVec r, e6RootVec (e6RootOpp r)⁆⁆ = 0 := by
    intro i
    rw [leibniz_lie, e6RootVec_bracket_H, e6RootVec_bracket_H, smul_lie, lie_smul, ← add_smul]
    have hsum : rootEigenvalue i r + rootEigenvalue i (e6RootOpp r) = 0 := by
      simp only [rootEigenvalue, ← Finset.sum_add_distrib, ← mul_add, e6RootCoord_opp,
        Pi.neg_apply, add_neg_cancel, mul_zero, Finset.sum_const_zero]
    have hsumR : (rootEigenvalue i r : ℝ) + (rootEigenvalue i (e6RootOpp r) : ℝ) = 0 := by
      exact_mod_cast hsum
    rw [hsumR, zero_smul]
  induction hH using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ih₁ ih₂ => rw [lie_add]; exact h3zornCartan.add_mem ih₁ ih₂
  | smul c _ _ ih => rw [lie_smul]; exact h3zornCartan.smul_mem c ih
  | mem _ h =>
    rcases h with ⟨i, rfl⟩
    rw [← lie_skew, hcomm i, neg_zero]
    exact h3zornCartan.zero_mem

theorem e6RootVec_opposite_bracket_ne_zero (r : Fin 72) :
    ⁅e6RootVec r, e6RootVec (e6RootOpp r)⁆ ≠ 0 := by
  have hchk : (List.finRange 72).all (fun r =>
      !sparseZeroCheck (sparseComm (e6RootSparse r) (e6RootSparse (e6RootOpp r)))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_true'] at hchk
  intro h0
  have hm := congrArg (fun x : h3zornCubicStabilizer =>
    h3zornToMatrix (x.1 : Module.End ℝ (H3Zorn ℝ))) h0
  change h3zornToMatrix (⁅e6RootVec r, e6RootVec (e6RootOpp r)⁆ :
      Module.End ℝ (H3Zorn ℝ)) = h3zornToMatrix (0 : Module.End ℝ (H3Zorn ℝ)) at hm
  rw [h3zornToMatrix_lie, h3zornToMatrix_e6RootVec, h3zornToMatrix_e6RootVec, map_zero] at hm
  have hcomm : (sparseToMat (e6RootSparse r)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (e6RootSparse (e6RootOpp r))).map Int.cast -
      (sparseToMat (e6RootSparse (e6RootOpp r))).map Int.cast *
        (sparseToMat (e6RootSparse r)).map Int.cast =
      (sparseToMat (sparseComm (e6RootSparse r) (e6RootSparse (e6RootOpp r)))).map
        Int.cast := by
    rw [sparseToMat_comm]
    ext a b; simp [Matrix.mul_apply]
  rw [hcomm] at hm
  have hzm : sparseToMat (sparseComm (e6RootSparse r) (e6RootSparse (e6RootOpp r))) = 0 := by
    ext a b
    have := congrFun (congrFun hm a) b
    simpa [Matrix.map_apply] using this
  have hzc : sparseZeroCheck (sparseComm (e6RootSparse r) (e6RootSparse (e6RootOpp r))) = true := by
    simp only [sparseZeroCheck, List.all_eq_true, beq_iff_eq]
    intro p _
    exact congrFun (congrFun hzm p.1) p.2.1
  rw [hchk r] at hzc
  cases hzc

/-- Root indices in `Fin 126` of the 7 simple `E₇` Chevalley `E` generators. -/
def e7ESimpleIdx (i : Fin 7) : Fin 126 :=
  if hi : i.val < 6 then ⟨(eSimpleIdx ⟨i.val, hi⟩).val, by omega⟩
  else ⟨82, by decide⟩

/-- Root indices in `Fin 126` of the 7 simple `E₇` Chevalley `F` generators. -/
def e7FSimpleIdx (i : Fin 7) : Fin 126 :=
  if hi : i.val < 6 then ⟨(fSimpleIdx ⟨i.val, hi⟩).val, by omega⟩
  else ⟨109, by decide⟩

/-- Scalar signs/factors of the 7 simple `E₇` Chevalley `F` generators. -/
def e7FSimpleSign (i : Fin 7) : ℤ :=
  if hi : i.val < 6 then fSimpleSign ⟨i.val, hi⟩
  else 2

/-- Highest root index in `Fin 126`: `negInj (h3ZornBasis 3)`, root `![2, 2, 3, 4, 3, 2, 1]`. -/
def e7HighestRootIdx : Fin 126 := ⟨75, by decide⟩

theorem e7SimpleE_eq_rootVec (i : Fin 7) : e7SimpleE i = e7RootVec (e7ESimpleIdx i) := by
  by_cases hi : i.val < 6
  · have hlt : (eSimpleIdx ⟨i.val, hi⟩).val < 72 := (eSimpleIdx ⟨i.val, hi⟩).isLt
    simp only [e7SimpleE, e7ESimpleIdx, e7RootVec, hi, hlt, ↓reduceDIte]
    rfl
  · have hi6 : i = 6 := Fin.ext (by omega)
    subst hi6
    rfl

theorem e7SimpleF_eq_rootVec (i : Fin 7) :
    e7SimpleF i = (e7FSimpleSign i : ℝ) • e7RootVec (e7FSimpleIdx i) := by
  by_cases hi : i.val < 6
  · simp [e7SimpleF, e7FSimpleSign, e7FSimpleIdx, e7RootVec, hi, e6SimpleF]
  · have hi6 : i = 6 := Fin.ext (by omega)
    subst hi6
    have h10 : traceDualIdx 10 = 3 := rfl
    simp [e7SimpleF, e7FSimpleSign, e7FSimpleIdx, e7RootVec, h10]

theorem e7Simple_bracket_EF_same (i : Fin 7) : ⁅e7SimpleE i, e7SimpleF i⁆ = e7SimpleH i := rfl

private theorem e6SimpleF_col10_zero (j : Fin 6) (r : Fin 27) :
    sparseVal (e6SimpleFSparse j) r 10 = 0 := by
  have h : (List.finRange 6).all (fun j => (List.finRange 27).all (fun r =>
      sparseVal (e6SimpleFSparse j) r 10 == 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h j r

private theorem e6SimpleE_row10_zero (i : Fin 6) (c : Fin 27) :
    sparseVal (e6SimpleESparse i) 10 c = 0 := by
  have h : (List.finRange 6).all (fun i => (List.finRange 27).all (fun c =>
      sparseVal (e6SimpleESparse i) 10 c == 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h i c

private theorem e6SimpleF_apply_basis10_eq_zero (j : Fin 6) :
    (e6SimpleF j : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis 10) = 0 := by
  apply h3ZornBasis.ext_elem
  intro r
  have h1 : h3ZornBasis.repr ((e6SimpleF j : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis 10)) r =
      h3zornToMatrix (e6SimpleF j : Module.End ℝ (H3Zorn ℝ)) r 10 := by
    rw [h3zornToMatrix_apply]; rfl
  rw [h1, h3zornToMatrix_e6SimpleF, Matrix.map_apply, map_zero, Finsupp.zero_apply]
  change (sparseVal (e6SimpleFSparse j) r 10 : ℝ) = 0
  rw [e6SimpleF_col10_zero, Int.cast_zero]

private theorem h3zornTraceAdjoint_e6SimpleE_basis3_eq_zero (i : Fin 6) :
    h3zornTraceAdjoint (e6SimpleE i : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis 3) = 0 := by
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro z
  rw [traceBilin_zero_left, ← h3ZornBasis.sum_repr z]
  change h3zornTraceBilin (h3zornTraceAdjoint (e6SimpleE i : Module.End ℝ (H3Zorn ℝ))
      (h3ZornBasis 3)) (∑ m, (h3ZornBasis.repr z) m • h3ZornBasis m) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [LinearMap.map_smul, smul_eq_zero]
  right
  change traceBilin (h3zornTraceAdjoint (e6SimpleE i : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis 3))
      (h3ZornBasis m) = 0
  rw [h3zornTraceAdjoint_pair, ← h3ZornBasis.sum_repr ((e6SimpleE i : Module.End ℝ (H3Zorn ℝ))
      (h3ZornBasis m))]
  change h3zornTraceBilin (h3ZornBasis 3) (∑ r, _ • h3ZornBasis r) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [LinearMap.map_smul, smul_eq_zero]
  by_cases hr10 : r = 10
  · left
    subst hr10
    have h1 : h3ZornBasis.repr ((e6SimpleE i : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis m)) 10 =
        h3zornToMatrix (e6SimpleE i : Module.End ℝ (H3Zorn ℝ)) 10 m := by
      rw [h3zornToMatrix_apply]; rfl
    rw [h1, h3zornToMatrix_e6SimpleE, Matrix.map_apply]
    change (sparseVal (e6SimpleESparse i) 10 m : ℝ) = 0
    rw [e6SimpleE_row10_zero, Int.cast_zero]
  · right
    change traceBilin (h3ZornBasis 3) (h3ZornBasis r) = 0
    have h3 : (3 : Fin 27) = traceDualIdx 10 := rfl
    rw [h3]
    exact traceBilin_h3ZornBasis_ne_dual 10 r hr10

theorem e7Simple_bracket_EF_ne {i j : Fin 7} (hij : i ≠ j) :
    ⁅e7SimpleE i, e7SimpleF j⁆ = 0 := by
  by_cases hi : i.val < 6 <;> by_cases hj : j.val < 6
  · have hi' : i = (⟨i.val, hi⟩ : Fin 6).castSucc := Fin.ext rfl
    have hj' : j = (⟨j.val, hj⟩ : Fin 6).castSucc := Fin.ext rfl
    have hne : (⟨i.val, hi⟩ : Fin 6) ≠ ⟨j.val, hj⟩ := fun h => hij (by rw [hi', hj', h])
    rw [hi', hj', e7SimpleE_castSucc, e7SimpleF_castSucc, ← LieHom.map_lie,
      e6Simple_bracket_EF_ne hne, map_zero]
  · have hj6 : j = 6 := Fin.ext (by omega)
    have hi' : i = (⟨i.val, hi⟩ : Fin 6).castSucc := Fin.ext rfl
    rw [hj6, hi', e7SimpleE_castSucc, e7SimpleF_six, lie_smul]
    change (2 : ℝ) • ⁅zeroInj _, posInj (h3ZornBasis 3)⁆ = 0
    rw [zeroInj_bracket_posInj]
    change (2 : ℝ) • posInj (-h3zornTraceAdjoint (e6SimpleE ⟨i.val, hi⟩).1 (h3ZornBasis 3)) = 0
    rw [h3zornTraceAdjoint_e6SimpleE_basis3_eq_zero, neg_zero, map_zero, smul_zero]
  · have hi6 : i = 6 := Fin.ext (by omega)
    have hj' : j = (⟨j.val, hj⟩ : Fin 6).castSucc := Fin.ext rfl
    rw [hi6, hj', e7SimpleE_six, e7SimpleF_castSucc]
    change ⁅negInj (h3ZornBasis 10), zeroInj _⁆ = 0
    rw [negInj_bracket_zeroInj]
    change negInj (-((e6SimpleF ⟨j.val, hj⟩).1 (h3ZornBasis 10))) = 0
    rw [e6SimpleF_apply_basis10_eq_zero, neg_zero, map_zero]
  · exfalso
    apply hij
    apply Fin.ext
    omega

theorem e7Simple_bracket_HE (i j : Fin 7) :
    ⁅e7SimpleH i, e7SimpleE j⁆ = ((Tag.cartan .E7 i j : ℤ) : ℝ) • e7SimpleE j := by
  have hwt : e7RootEigenvalue i (e7ESimpleIdx j) = Tag.cartan .E7 i j := by
    have hchk : (List.finRange 7).all (fun i => (List.finRange 7).all (fun j =>
        e7RootEigenvalue i (e7ESimpleIdx j) == Tag.cartan .E7 i j)) = true := by
      decide
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
    exact hchk i j
  rw [e7SimpleE_eq_rootVec, e7RootVec_bracket_H, hwt]

theorem e7Simple_bracket_HF (i j : Fin 7) :
    ⁅e7SimpleH i, e7SimpleF j⁆ = (-(Tag.cartan .E7 i j : ℤ) : ℝ) • e7SimpleF j := by
  have hwt : e7RootEigenvalue i (e7FSimpleIdx j) = -Tag.cartan .E7 i j := by
    have hchk : (List.finRange 7).all (fun i => (List.finRange 7).all (fun j =>
        e7RootEigenvalue i (e7FSimpleIdx j) == -Tag.cartan .E7 i j)) = true := by
      decide
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
    exact hchk i j
  rw [e7SimpleF_eq_rootVec, lie_smul, e7RootVec_bracket_H, hwt]
  simp only [Int.cast_neg, smul_smul, mul_comm]

private theorem e6SimpleE_lt5_col10_zero_aux :
    (List.finRange 5).all (fun j => (List.finRange 27).all (fun r =>
      sparseVal (e6SimpleESparse ⟨j.val, by omega⟩) r 10 == 0)) = true := by
  decide

private theorem e6SimpleE_lt5_col10_zero (j : Fin 6) (hj : j.val < 5) (r : Fin 27) :
    sparseVal (e6SimpleESparse j) r 10 = 0 := by
  have h := e6SimpleE_lt5_col10_zero_aux
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h ⟨j.val, hj⟩ r

private theorem e6SimpleF_lt5_row10_zero_aux :
    (List.finRange 5).all (fun j => (List.finRange 27).all (fun c =>
      sparseVal (e6SimpleFSparse ⟨j.val, by omega⟩) 10 c == 0)) = true := by
  decide

private theorem e6SimpleF_lt5_row10_zero (j : Fin 6) (hj : j.val < 5) (c : Fin 27) :
    sparseVal (e6SimpleFSparse j) 10 c = 0 := by
  have h := e6SimpleF_lt5_row10_zero_aux
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h ⟨j.val, hj⟩ c

private theorem e6SimpleE5_sq_col10_zero (r : Fin 27) :
    sparseVal (sparseMul (e6SimpleESparse 5) (e6SimpleESparse 5)) r 10 = 0 := by
  have h : (List.finRange 27).all (fun r =>
      sparseVal (sparseMul (e6SimpleESparse 5) (e6SimpleESparse 5)) r 10 == 0) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h r

private theorem e6SimpleF5_sq_row10_zero (c : Fin 27) :
    sparseVal (sparseMul (e6SimpleFSparse 5) (e6SimpleFSparse 5)) 10 c = 0 := by
  have h : (List.finRange 27).all (fun c =>
      sparseVal (sparseMul (e6SimpleFSparse 5) (e6SimpleFSparse 5)) 10 c == 0) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h c

private theorem e6SimpleE_lt5_apply_basis10 (j : Fin 6) (hj : j.val < 5) :
    (e6SimpleE j : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis 10) = 0 := by
  apply h3ZornBasis.ext_elem
  intro r
  have h1 : h3ZornBasis.repr ((e6SimpleE j : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis 10)) r =
      h3zornToMatrix (e6SimpleE j : Module.End ℝ (H3Zorn ℝ)) r 10 := by
    rw [h3zornToMatrix_apply]; rfl
  rw [h1, h3zornToMatrix_e6SimpleE, Matrix.map_apply, map_zero, Finsupp.zero_apply]
  change (sparseVal (e6SimpleESparse j) r 10 : ℝ) = 0
  rw [e6SimpleE_lt5_col10_zero j hj, Int.cast_zero]

private theorem h3zornTraceAdjoint_e6SimpleF_lt5_basis3 (j : Fin 6) (hj : j.val < 5) :
    h3zornTraceAdjoint (e6SimpleF j : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis 3) = 0 := by
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro z
  rw [traceBilin_zero_left, ← h3ZornBasis.sum_repr z]
  change h3zornTraceBilin (h3zornTraceAdjoint (e6SimpleF j : Module.End ℝ (H3Zorn ℝ))
      (h3ZornBasis 3)) (∑ m, (h3ZornBasis.repr z) m • h3ZornBasis m) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [LinearMap.map_smul, smul_eq_zero]
  right
  change traceBilin (h3zornTraceAdjoint (e6SimpleF j : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis 3))
      (h3ZornBasis m) = 0
  rw [h3zornTraceAdjoint_pair, ← h3ZornBasis.sum_repr ((e6SimpleF j : Module.End ℝ (H3Zorn ℝ))
      (h3ZornBasis m))]
  change h3zornTraceBilin (h3ZornBasis 3) (∑ r, _ • h3ZornBasis r) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [LinearMap.map_smul, smul_eq_zero]
  by_cases hr10 : r = 10
  · left
    subst hr10
    have h1 : h3ZornBasis.repr ((e6SimpleF j : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis m)) 10 =
        h3zornToMatrix (e6SimpleF j : Module.End ℝ (H3Zorn ℝ)) 10 m := by
      rw [h3zornToMatrix_apply]; rfl
    rw [h1, h3zornToMatrix_e6SimpleF, Matrix.map_apply]
    change (sparseVal (e6SimpleFSparse j) 10 m : ℝ) = 0
    rw [e6SimpleF_lt5_row10_zero j hj, Int.cast_zero]
  · right
    change traceBilin (h3ZornBasis 3) (h3ZornBasis r) = 0
    have h3 : (3 : Fin 27) = traceDualIdx 10 := rfl
    rw [h3]
    exact traceBilin_h3ZornBasis_ne_dual 10 r hr10

private theorem end_sq_apply_basis10_eq_zero (T : Module.End ℝ (H3Zorn ℝ))
    (S : SparseMat27) (hT : h3zornToMatrix T = (sparseToMat S).map Int.cast)
    (hS : ∀ r : Fin 27, sparseVal (sparseMul S S) r 10 = 0) :
    T (T (h3ZornBasis 10)) = 0 := by
  have hmat : h3zornToMatrix (T * T) = (sparseToMat (sparseMul S S)).map Int.cast := by
    rw [map_mul, hT, sparseToMat_mul]
    ext a b; simp [Matrix.mul_apply]
  apply h3ZornBasis.ext_elem
  intro r
  have h1 : h3ZornBasis.repr ((T * T) (h3ZornBasis 10)) r = h3zornToMatrix (T * T) r 10 := by
    rw [h3zornToMatrix_apply]; rfl
  change h3ZornBasis.repr ((T * T) (h3ZornBasis 10)) r = _
  rw [h1, hmat, Matrix.map_apply, map_zero, Finsupp.zero_apply]
  change (sparseVal (sparseMul S S) r 10 : ℝ) = 0
  rw [hS r, Int.cast_zero]

private theorem e6SimpleE5_sq_apply_basis10 :
    (e6SimpleE 5 : Module.End ℝ (H3Zorn ℝ))
      ((e6SimpleE 5 : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis 10)) = 0 :=
  end_sq_apply_basis10_eq_zero (e6SimpleE 5).1 (e6SimpleESparse 5)
    (h3zornToMatrix_e6SimpleE 5) e6SimpleE5_sq_col10_zero

private theorem traceAdjoint_sq_apply_basis3 (T : Module.End ℝ (H3Zorn ℝ))
    (S : SparseMat27) (hT : h3zornToMatrix T = (sparseToMat S).map Int.cast)
    (hS : ∀ c : Fin 27, sparseVal (sparseMul S S) 10 c = 0) :
    h3zornTraceAdjoint T (h3zornTraceAdjoint T (h3ZornBasis 3)) = 0 := by
  have hcomp : h3zornTraceAdjoint T (h3zornTraceAdjoint T (h3ZornBasis 3)) =
      h3zornTraceAdjoint (T * T) (h3ZornBasis 3) := by
    change h3zornTraceAdjoint T (h3zornTraceAdjoint T (h3ZornBasis 3)) =
      h3zornTraceAdjoint (T ∘ₗ T) (h3ZornBasis 3)
    rw [h3zornTraceAdjoint_comp, LinearMap.comp_apply]
  have hmat : h3zornToMatrix (T * T) = (sparseToMat (sparseMul S S)).map Int.cast := by
    rw [map_mul, hT, sparseToMat_mul]
    ext a b; simp [Matrix.mul_apply]
  rw [hcomp]
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro z
  rw [traceBilin_zero_left, ← h3ZornBasis.sum_repr z]
  change h3zornTraceBilin (h3zornTraceAdjoint (T * T) (h3ZornBasis 3))
    (∑ m, (h3ZornBasis.repr z) m • h3ZornBasis m) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [LinearMap.map_smul, smul_eq_zero]
  right
  change traceBilin (h3zornTraceAdjoint (T * T) (h3ZornBasis 3)) (h3ZornBasis m) = 0
  rw [h3zornTraceAdjoint_pair, ← h3ZornBasis.sum_repr ((T * T) (h3ZornBasis m))]
  change h3zornTraceBilin (h3ZornBasis 3) (∑ r, _ • h3ZornBasis r) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [LinearMap.map_smul, smul_eq_zero]
  by_cases hr10 : r = 10
  · left
    subst hr10
    have h1 : h3ZornBasis.repr ((T * T) (h3ZornBasis m)) 10 = h3zornToMatrix (T * T) 10 m := by
      rw [h3zornToMatrix_apply]; rfl
    rw [h1, hmat, Matrix.map_apply]
    change (sparseVal (sparseMul S S) 10 m : ℝ) = 0
    rw [hS m, Int.cast_zero]
  · right
    change traceBilin (h3ZornBasis 3) (h3ZornBasis r) = 0
    have h3 : (3 : Fin 27) = traceDualIdx 10 := rfl
    rw [h3]
    exact traceBilin_h3ZornBasis_ne_dual 10 r hr10

private theorem h3zornTraceAdjoint_e6SimpleF5_sq_basis3 :
    h3zornTraceAdjoint (e6SimpleF 5 : Module.End ℝ (H3Zorn ℝ))
      (h3zornTraceAdjoint (e6SimpleF 5 : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis 3)) = 0 :=
  traceAdjoint_sq_apply_basis3 (e6SimpleF 5).1 (e6SimpleFSparse 5)
    (h3zornToMatrix_e6SimpleF 5) e6SimpleF5_sq_row10_zero

private theorem cartan_E7_castSucc (a b : Fin 6) :
    Tag.cartan .E7 a.castSucc b.castSucc = Tag.cartan .E6 a b := by
  fin_cases a <;> fin_cases b <;> decide

private theorem cartan_E7_5_6 :
    (1 - Tag.cartan .E7 ((5 : Fin 6).castSucc) ⟨6, by decide⟩).toNat = 2 := by
  decide

private theorem cartan_E7_6_5 :
    (1 - Tag.cartan .E7 ⟨6, by decide⟩ ((5 : Fin 6).castSucc)).toNat = 2 := by
  decide

private theorem cartan_E7_lt5_6_aux :
    (List.finRange 5).all (fun a =>
      (1 - Tag.cartan .E7 ⟨a.val, Nat.lt_trans a.isLt (by decide : 5 < Tag.E7.rank)⟩
        ⟨6, by decide⟩).toNat == 1) = true := by
  decide

private theorem cartan_E7_lt5_6 (a : Fin 6) (ha : a.val < 5) :
    (1 - Tag.cartan .E7 a.castSucc ⟨6, by decide⟩).toNat = 1 := by
  have h := cartan_E7_lt5_6_aux
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h ⟨a.val, ha⟩

private theorem cartan_E7_6_lt5_aux :
    (List.finRange 5).all (fun b =>
      (1 - Tag.cartan .E7 ⟨6, by decide⟩
        ⟨b.val, Nat.lt_trans b.isLt (by decide : 5 < Tag.E7.rank)⟩).toNat == 1) = true := by
  decide

private theorem cartan_E7_6_lt5 (b : Fin 6) (hb : b.val < 5) :
    (1 - Tag.cartan .E7 ⟨6, by decide⟩ b.castSucc).toNat = 1 := by
  have h := cartan_E7_6_lt5_aux
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h ⟨b.val, hb⟩

theorem e7Simple_serre_E {i j : Fin 7} (hij : i ≠ j) :
    (Nat.iterate (fun x => ⁅e7SimpleE i, x⁆)
      (1 - Tag.cartan .E7 i j).toNat) (e7SimpleE j) = 0 := by
  by_cases hi : i.val < 6 <;> by_cases hj : j.val < 6
  · obtain ⟨a, rfl⟩ : ∃ a : Fin 6, i = a.castSucc := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    obtain ⟨b, rfl⟩ : ∃ b : Fin 6, j = b.castSucc := ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
    have hne : a ≠ b := fun h => hij (congrArg Fin.castSucc h)
    rw [cartan_E7_castSucc a b]
    have hmap : ∀ n : ℕ, (Nat.iterate (fun x => ⁅e7SimpleE a.castSucc, x⁆) n)
          (e7SimpleE b.castSucc) =
        h3zornCubicStabilizerToTKK
          ((Nat.iterate (fun x => ⁅e6SimpleE a, x⁆) n) (e6SimpleE b)) := by
      intro n
      induction n with
      | zero => rw [e7SimpleE_castSucc, e7SimpleE_castSucc]; rfl
      | succ n ih =>
        simp only [Function.iterate_succ_apply']
        rw [ih, e7SimpleE_castSucc, ← LieHom.map_lie]
    rw [hmap, e6Simple_serre_E hne, map_zero]
  · obtain rfl : j = 6 := Fin.ext (by omega)
    obtain ⟨a, rfl⟩ : ∃ a : Fin 6, i = a.castSucc := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    by_cases ha5 : a.val = 5
    · obtain rfl : a = 5 := Fin.ext ha5
      have hc : (1 - Tag.cartan .E7 (5 : Fin 6).castSucc ⟨6, by decide⟩).toNat = 2 :=
        cartan_E7_5_6
      change (Nat.iterate (fun x => ⁅e7SimpleE (5 : Fin 6).castSucc, x⁆)
        (1 - Tag.cartan .E7 (5 : Fin 6).castSucc ⟨6, by decide⟩).toNat) (e7SimpleE 6) = 0
      rw [hc]
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [e7SimpleE_castSucc, e7SimpleE_six]
      change ⁅zeroInj _, ⁅zeroInj _, negInj (h3ZornBasis 10)⁆⁆ = 0
      rw [zeroInj_bracket_negInj, zeroInj_bracket_negInj]
      change negInj ((e6SimpleE 5).1 ((e6SimpleE 5).1 (h3ZornBasis 10))) = 0
      rw [e6SimpleE5_sq_apply_basis10, map_zero]
    · have ha_lt5 : a.val < 5 := by omega
      change (Nat.iterate (fun x => ⁅e7SimpleE a.castSucc, x⁆)
        (1 - Tag.cartan .E7 a.castSucc ⟨6, by decide⟩).toNat) (e7SimpleE 6) = 0
      rw [cartan_E7_lt5_6 a ha_lt5]
      simp only [Function.iterate_one]
      rw [e7SimpleE_castSucc, e7SimpleE_six]
      change ⁅zeroInj _, negInj (h3ZornBasis 10)⁆ = 0
      rw [zeroInj_bracket_negInj]
      change negInj ((e6SimpleE a).1 (h3ZornBasis 10)) = 0
      rw [e6SimpleE_lt5_apply_basis10 a ha_lt5, map_zero]
  · obtain rfl : i = 6 := Fin.ext (by omega)
    obtain ⟨b, rfl⟩ : ∃ b : Fin 6, j = b.castSucc := ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
    by_cases hb5 : b.val = 5
    · obtain rfl : b = 5 := Fin.ext hb5
      have hc : (1 - Tag.cartan .E7 ⟨6, by decide⟩ (5 : Fin 6).castSucc).toNat = 2 :=
        cartan_E7_6_5
      change (Nat.iterate (fun x => ⁅e7SimpleE 6, x⁆)
        (1 - Tag.cartan .E7 ⟨6, by decide⟩ (5 : Fin 6).castSucc).toNat)
          (e7SimpleE (5 : Fin 6).castSucc) = 0
      rw [hc]
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [e7SimpleE_six, e7SimpleE_castSucc]
      change ⁅negInj (h3ZornBasis 10), ⁅negInj (h3ZornBasis 10), zeroInj _⁆⁆ = 0
      rw [negInj_bracket_zeroInj, negInj_bracket_negInj]
    · have hb_lt5 : b.val < 5 := by omega
      change (Nat.iterate (fun x => ⁅e7SimpleE 6, x⁆)
        (1 - Tag.cartan .E7 ⟨6, by decide⟩ b.castSucc).toNat) (e7SimpleE b.castSucc) = 0
      rw [cartan_E7_6_lt5 b hb_lt5]
      simp only [Function.iterate_one]
      rw [e7SimpleE_six, e7SimpleE_castSucc]
      change ⁅negInj (h3ZornBasis 10), zeroInj _⁆ = 0
      rw [negInj_bracket_zeroInj]
      change negInj (-((e6SimpleE b).1 (h3ZornBasis 10))) = 0
      rw [e6SimpleE_lt5_apply_basis10 b hb_lt5, neg_zero, map_zero]
  · exfalso
    apply hij
    apply Fin.ext
    omega

theorem e7Simple_serre_F {i j : Fin 7} (hij : i ≠ j) :
    (Nat.iterate (fun x => ⁅e7SimpleF i, x⁆)
      (1 - Tag.cartan .E7 i j).toNat) (e7SimpleF j) = 0 := by
  by_cases hi : i.val < 6 <;> by_cases hj : j.val < 6
  · obtain ⟨a, rfl⟩ : ∃ a : Fin 6, i = a.castSucc := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    obtain ⟨b, rfl⟩ : ∃ b : Fin 6, j = b.castSucc := ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
    have hne : a ≠ b := fun h => hij (congrArg Fin.castSucc h)
    rw [cartan_E7_castSucc a b]
    have hmap : ∀ n : ℕ, (Nat.iterate (fun x => ⁅e7SimpleF a.castSucc, x⁆) n)
          (e7SimpleF b.castSucc) =
        h3zornCubicStabilizerToTKK
          ((Nat.iterate (fun x => ⁅e6SimpleF a, x⁆) n) (e6SimpleF b)) := by
      intro n
      induction n with
      | zero => rw [e7SimpleF_castSucc, e7SimpleF_castSucc]; rfl
      | succ n ih =>
        simp only [Function.iterate_succ_apply']
        rw [ih, e7SimpleF_castSucc, ← LieHom.map_lie]
    rw [hmap, e6Simple_serre_F hne, map_zero]
  · obtain rfl : j = 6 := Fin.ext (by omega)
    obtain ⟨a, rfl⟩ : ∃ a : Fin 6, i = a.castSucc := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    by_cases ha5 : a.val = 5
    · obtain rfl : a = 5 := Fin.ext ha5
      have hc : (1 - Tag.cartan .E7 (5 : Fin 6).castSucc ⟨6, by decide⟩).toNat = 2 :=
        cartan_E7_5_6
      change (Nat.iterate (fun x => ⁅e7SimpleF (5 : Fin 6).castSucc, x⁆)
        (1 - Tag.cartan .E7 (5 : Fin 6).castSucc ⟨6, by decide⟩).toNat) (e7SimpleF 6) = 0
      rw [hc]
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [e7SimpleF_castSucc, e7SimpleF_six, lie_smul, lie_smul]
      change (2 : ℝ) • ⁅zeroInj _, ⁅zeroInj _, posInj (h3ZornBasis 3)⁆⁆ = 0
      rw [zeroInj_bracket_posInj, zeroInj_bracket_posInj]
      change (2 : ℝ) • posInj (-h3zornTraceAdjoint (e6SimpleF 5).1
        (-h3zornTraceAdjoint (e6SimpleF 5).1 (h3ZornBasis 3))) = 0
      rw [LinearMap.map_neg (h3zornTraceAdjoint (e6SimpleF 5).1), neg_neg,
        h3zornTraceAdjoint_e6SimpleF5_sq_basis3, map_zero, smul_zero]
    · have ha_lt5 : a.val < 5 := by omega
      change (Nat.iterate (fun x => ⁅e7SimpleF a.castSucc, x⁆)
        (1 - Tag.cartan .E7 a.castSucc ⟨6, by decide⟩).toNat) (e7SimpleF 6) = 0
      rw [cartan_E7_lt5_6 a ha_lt5]
      simp only [Function.iterate_one]
      rw [e7SimpleF_castSucc, e7SimpleF_six, lie_smul]
      change (2 : ℝ) • ⁅zeroInj _, posInj (h3ZornBasis 3)⁆ = 0
      rw [zeroInj_bracket_posInj]
      change (2 : ℝ) • posInj (-h3zornTraceAdjoint (e6SimpleF a).1 (h3ZornBasis 3)) = 0
      rw [h3zornTraceAdjoint_e6SimpleF_lt5_basis3 a ha_lt5, neg_zero, map_zero, smul_zero]
  · obtain rfl : i = 6 := Fin.ext (by omega)
    obtain ⟨b, rfl⟩ : ∃ b : Fin 6, j = b.castSucc := ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
    by_cases hb5 : b.val = 5
    · obtain rfl : b = 5 := Fin.ext hb5
      have hc : (1 - Tag.cartan .E7 ⟨6, by decide⟩ (5 : Fin 6).castSucc).toNat = 2 :=
        cartan_E7_6_5
      change (Nat.iterate (fun x => ⁅e7SimpleF 6, x⁆)
        (1 - Tag.cartan .E7 ⟨6, by decide⟩ (5 : Fin 6).castSucc).toNat)
          (e7SimpleF (5 : Fin 6).castSucc) = 0
      rw [hc]
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [e7SimpleF_six, e7SimpleF_castSucc]
      change ⁅(2 : ℝ) • posInj (h3ZornBasis 3),
        ⁅(2 : ℝ) • posInj (h3ZornBasis 3), zeroInj _⁆⁆ = 0
      rw [smul_lie, smul_lie, lie_smul, posInj_bracket_zeroInj, posInj_bracket_posInj]
      simp
    · have hb_lt5 : b.val < 5 := by omega
      change (Nat.iterate (fun x => ⁅e7SimpleF 6, x⁆)
        (1 - Tag.cartan .E7 ⟨6, by decide⟩ b.castSucc).toNat) (e7SimpleF b.castSucc) = 0
      rw [cartan_E7_6_lt5 b hb_lt5]
      simp only [Function.iterate_one]
      rw [e7SimpleF_six, e7SimpleF_castSucc, smul_lie]
      change (2 : ℝ) • ⁅posInj (h3ZornBasis 3), zeroInj _⁆ = 0
      rw [posInj_bracket_zeroInj]
      change (2 : ℝ) • posInj (h3zornTraceAdjoint (e6SimpleF b).1 (h3ZornBasis 3)) = 0
      rw [h3zornTraceAdjoint_e6SimpleF_lt5_basis3 b hb_lt5, map_zero, smul_zero]
  · exfalso
    apply hij
    apply Fin.ext
    omega

theorem e7SimpleF_six_bracket_negInj (k : Fin 27) :
    ⁅e7SimpleF 6, negInj (h3ZornBasis k)⁆ =
      (-2 : ℝ) • zeroInj ⟨JordanTKK.tripleD ℝ (h3ZornBasis k) (h3ZornBasis 3),
        h3zornTKKDatum.tripleD_mem_str _ _⟩ := by
  rw [e7SimpleF_six, smul_lie, posInj_bracket_negInj, ← map_smul, ← map_smul]
  congr 1
  apply Subtype.ext
  apply LinearMap.ext; intro z
  simp only [SetLike.val_smul, LinearMap.smul_apply, LinearMap.neg_apply, smul_neg, neg_smul]

theorem e7SimpleE_six_bracket_posInj (k : Fin 27) :
    ⁅e7SimpleE 6, posInj (h3ZornBasis k)⁆ =
      zeroInj ⟨JordanTKK.tripleD ℝ (h3ZornBasis 10) (h3ZornBasis k),
        h3zornTKKDatum.tripleD_mem_str _ _⟩ := by
  rw [e7SimpleE_six, negInj_bracket_posInj]

theorem h3zornE7_noncomm_witness : ⁅e7SimpleH 0, e7SimpleE 0⁆ ≠ 0 := by
  rw [e7Simple_bracket_HE]
  have hc : Tag.cartan .E7 (0 : Fin 7) (0 : Fin 7) = 2 := by decide
  rw [hc, e7SimpleE_eq_rootVec]
  intro h0
  have hsm := smul_eq_zero.mp h0
  norm_num at hsm
  exact e7RootVec_ne_zero (e7ESimpleIdx 0) hsm

theorem e7_matrix27_noncomm_witness :
    ∃ A B : Matrix (Fin 27) (Fin 27) ℝ, A * B ≠ B * A :=
  matrix27_real_noncomm_witness

end SimplicityHelpersAndSerre

end InfoGeometry.Algebra
