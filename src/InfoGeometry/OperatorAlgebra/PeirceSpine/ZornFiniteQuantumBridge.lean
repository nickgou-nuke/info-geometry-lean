/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornPeirceShearD63
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
import Mathlib.Data.Matrix.Composition
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Operator-valued Zorn slices on a finite tensor carrier

The carrier map is the standard matrix composition equivalence. The Zorn
slice is not asserted to preserve the nonassociative Zorn multiplication.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ZornFiniteQuantumBridge

open Matrix InfoGeometry.Physics.NCG InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornPeirceShearD63
open scoped Matrix ComplexOrder Kronecker

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Block" => Matrix (Fin 2) (Fin 2) (Matrix n n ℂ)
local notation "Flat" => Matrix (Fin 2 × n) (Fin 2 × n) ℂ

/-- The existing sheet projection acting on the full tensor carrier. -/
def zornFlatSheet : Flat :=
  Matrix.compRingEquiv (Fin 2) n ℂ (peirceSheetProj (A := Matrix n n ℂ))

/-- An operator-valued Zorn slice acting on the full tensor carrier. -/
def zornFlatSlice (i : Fin 3) (X : OperatorZornMatrix (Matrix n n ℂ)) : Flat :=
  Matrix.compRingEquiv (Fin 2) n ℂ (zornChiralPlaneMatrix i X)

omit [DecidableEq n] in
theorem compRingEquiv_star (M : Block) :
    Matrix.compRingEquiv (Fin 2) n ℂ (star M) =
      star (Matrix.compRingEquiv (Fin 2) n ℂ M) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rfl

theorem zornFlatSheet_idem : (zornFlatSheet : Flat) * zornFlatSheet = zornFlatSheet := by
  unfold zornFlatSheet
  rw [← map_mul, peirceSheetProj_idem]

theorem zornFlatSheet_star : star (zornFlatSheet : Flat) = zornFlatSheet := by
  unfold zornFlatSheet
  rw [← compRingEquiv_star]
  congr 1
  ext i j a b
  fin_cases i <;> fin_cases j <;>
    simp [peirceSheetProj, Matrix.star_apply, Matrix.one_apply, eq_comm]

/-- The full upper sheet has the dimension of the internal operator space. -/
theorem zornFlatSheet_trace : Matrix.trace (zornFlatSheet : Flat) = Fintype.card n := by
  simp [zornFlatSheet, Matrix.trace, Matrix.diag, Matrix.comp_apply,
    peirceSheetProj, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Normalize the Peirce state by the internal dimension. -/
def zornNormalizedState (i : Fin 3)
    (X : OperatorZornMatrix (Matrix n n ℂ)) : Flat :=
  ((Fintype.card n : ℝ)⁻¹) •
    pageDensityOp zornFlatSheet (zornFlatSlice i X) (star (zornFlatSlice i X))

theorem zornNormalizedState_positive (i : Fin 3)
    (X : OperatorZornMatrix (Matrix n n ℂ))
    (hBound : (1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X))).PosSemidef) :
    (zornNormalizedState i X).PosSemidef := by
  unfold zornNormalizedState
  apply Matrix.PosSemidef.smul
    (page_density_posSemidef _ _ zornFlatSheet_idem zornFlatSheet_star
      (upper_corner_posSemidef_of_metric_bound _ _ zornFlatSheet_idem zornFlatSheet_star hBound))
  positivity

theorem zornNormalizedState_trace [Nonempty n] (i : Fin 3)
    (X : OperatorZornMatrix (Matrix n n ℂ)) :
    Matrix.trace (zornNormalizedState i X) = 1 := by
  unfold zornNormalizedState
  rw [Matrix.trace_smul, page_density_trace _ _ _ zornFlatSheet_idem, zornFlatSheet_trace]
  simp [Fintype.card_ne_zero]

/-- The upper Peirce corner of a Zorn slice retains its full noncommutative
matrix coefficient. -/
theorem zornFlatSlice_conePlus (i : Fin 3)
    (X : OperatorZornMatrix (Matrix n n ℂ)) :
    conePlus zornFlatSheet (zornFlatSlice i X) =
      Matrix.compRingEquiv (Fin 2) n ℂ !![0, X.sigma_plus i; 0, 0] := by
  unfold conePlus zornFlatSheet zornFlatSlice
  rw [← map_one (Matrix.compRingEquiv (Fin 2) n ℂ), ← map_sub, ← map_mul, ← map_mul]
  change Matrix.compRingEquiv (Fin 2) n ℂ
    (conePlus peirceSheetProj (zornChiralPlaneMatrix i X)) = _
  rw [zornChiralPlane_conePlus]

/-- The Peirce Gramian of a flattened Zorn slice retains both ordered Gram
products of the matrix-valued upper coefficient. -/
theorem zornFlatSlice_metric_blocks (i : Fin 3)
    (X : OperatorZornMatrix (Matrix n n ℂ)) :
    genV zornFlatSheet (zornFlatSlice i X) (star (zornFlatSlice i X)) =
      Matrix.compRingEquiv (Fin 2) n ℂ
        !![X.sigma_plus i * star (X.sigma_plus i), 0;
           0, star (X.sigma_plus i) * X.sigma_plus i] := by
  unfold genV anticomm
  rw [← star_conePlus zornFlatSheet_star, zornFlatSlice_conePlus]
  simp only [← compRingEquiv_star, ← map_mul, ← map_add]
  congr 1
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.star_apply]

/-- The global contractivity condition implies both operator inequalities
for the noncommuting upper Zorn coefficient. -/
theorem zornFlatSlice_bound_compressions (i : Fin 3)
    (X : OperatorZornMatrix (Matrix n n ℂ))
    (hBound : (1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X))).PosSemidef) :
    (1 - X.sigma_plus i * star (X.sigma_plus i)).PosSemidef ∧
    (1 - star (X.sigma_plus i) * X.sigma_plus i).PosSemidef := by
  have hUpper := hBound.submatrix (fun a : n => ((0 : Fin 2), a))
  have hLower := hBound.submatrix (fun a : n => ((1 : Fin 2), a))
  have hUpperEq : (1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X))).submatrix (fun a : n => ((0 : Fin 2), a))
        (fun a : n => ((0 : Fin 2), a)) = 1 - X.sigma_plus i * star (X.sigma_plus i) := by
    ext a b
    simp [zornFlatSlice_metric_blocks, Matrix.submatrix_apply, Matrix.comp_apply,
      Matrix.one_apply, Prod.mk.injEq]
  have hLowerEq : (1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X))).submatrix (fun a : n => ((1 : Fin 2), a))
        (fun a : n => ((1 : Fin 2), a)) = 1 - star (X.sigma_plus i) * X.sigma_plus i := by
    ext a b
    simp [zornFlatSlice_metric_blocks, Matrix.submatrix_apply, Matrix.comp_apply,
      Matrix.one_apply, Prod.mk.injEq]
  exact ⟨hUpperEq ▸ hUpper, hLowerEq ▸ hLower⟩

/-- Conversely, the two operator bounds imply positivity on the full
sheet-indexed carrier. The coefficient matrices need not commute. -/
theorem zornFlatSlice_bound_of_compressions (i : Fin 3)
    (X : OperatorZornMatrix (Matrix n n ℂ))
    (hUpper : (1 - X.sigma_plus i * star (X.sigma_plus i)).PosSemidef)
    (hLower : (1 - star (X.sigma_plus i) * X.sigma_plus i).PosSemidef) :
    (1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X))).PosSemidef := by
  let e₀ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]
  let e₁ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, 1]
  have he₀ : e₀.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro j
    fin_cases j <;> simp
  have he₁ : e₁.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro j
    fin_cases j <;> simp
  have hSum := (he₀.kronecker hUpper).add (he₁.kronecker hLower)
  have hEq : 1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X)) =
      e₀ ⊗ₖ (1 - X.sigma_plus i * star (X.sigma_plus i)) +
        e₁ ⊗ₖ (1 - star (X.sigma_plus i) * X.sigma_plus i) := by
    ext ⟨r, a⟩ ⟨s, b⟩
    fin_cases r <;> fin_cases s <;>
      simp [zornFlatSlice_metric_blocks, Matrix.comp_apply,
        Matrix.one_apply, e₀, e₁, Prod.mk.injEq]
  rw [hEq]
  exact hSum

theorem zornFlatSlice_bound_iff_compressions (i : Fin 3)
    (X : OperatorZornMatrix (Matrix n n ℂ)) :
    (1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X))).PosSemidef ↔
    (1 - X.sigma_plus i * star (X.sigma_plus i)).PosSemidef ∧
    (1 - star (X.sigma_plus i) * X.sigma_plus i).PosSemidef := by
  constructor
  · exact zornFlatSlice_bound_compressions i X
  · rintro ⟨hUpper, hLower⟩
    exact zornFlatSlice_bound_of_compressions i X hUpper hLower

section OperatorNorm

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- For a square matrix, the two ordered contraction bounds are equivalent
by the C-star norm identity. -/
theorem matrix_ordered_gram_bounds_iff (B : Matrix n n ℂ) :
    (1 - B * star B).PosSemidef ↔ (1 - star B * B).PosSemidef := by
  have hUpper : (1 - B * star B).PosSemidef ↔ ‖B * star B‖ ≤ 1 := by
    rw [← Matrix.nonneg_iff_posSemidef, sub_nonneg]
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (mul_star_self_nonneg B)).symm
  have hLower : (1 - star B * B).PosSemidef ↔ ‖star B * B‖ ≤ 1 := by
    rw [← Matrix.nonneg_iff_posSemidef, sub_nonneg]
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg B)).symm
  rw [hUpper, hLower, CStarRing.norm_self_mul_star, CStarRing.norm_star_mul_self]

end OperatorNorm

/-- The upper corner retains the entire operator-valued Zorn coefficient:
two such corners are equal exactly when their coefficient matrices agree. -/
theorem zornFlatSlice_conePlus_eq_iff (i : Fin 3)
    (X Y : OperatorZornMatrix (Matrix n n ℂ)) :
    conePlus zornFlatSheet (zornFlatSlice i X) =
      conePlus zornFlatSheet (zornFlatSlice i Y) ↔ X.sigma_plus i = Y.sigma_plus i := by
  rw [zornFlatSlice_conePlus, zornFlatSlice_conePlus]
  constructor
  · intro h
    have hBlocks : (!![0, X.sigma_plus i; 0, 0] : Block) =
        !![0, Y.sigma_plus i; 0, 0] :=
      (Matrix.compRingEquiv (Fin 2) n ℂ).injective h
    have hEntry := congrArg (fun M : Block => M 0 1) hBlocks
    simpa using hEntry
  · intro h
    rw [h]

/-- The upper block of the product defect is the negative transverse Zorn
cross product, entry by entry on the full internal matrix carrier. -/
theorem zornFlatSlice_zero_product_defect_upper
    (X Y : OperatorZornMatrix (Matrix n n ℂ)) (a b : n) :
    (zornFlatSlice 0 (X * Y) - zornFlatSlice 0 X * zornFlatSlice 0 Y)
      (0, a) (1, b) = -NCZornElement.zornCross X.sigma_minus Y.sigma_minus 0 a b := by
  have h := congrArg
    (fun M : Block => Matrix.compRingEquiv (Fin 2) n ℂ M (0, a) (1, b))
    (zornChiralPlane_zero_mul_defect X Y)
  simpa [zornFlatSlice, map_sub, map_mul, Matrix.comp_apply] using h

/-- A nonzero transverse cross term obstructs multiplicativity of the
flattened Zorn slice. -/
theorem zornFlatSlice_zero_not_mul_of_cross_ne_zero
    (X Y : OperatorZornMatrix (Matrix n n ℂ))
    (hCross : NCZornElement.zornCross X.sigma_minus Y.sigma_minus 0 ≠ 0) :
    zornFlatSlice 0 (X * Y) ≠ zornFlatSlice 0 X * zornFlatSlice 0 Y := by
  intro hMul
  apply hCross
  apply neg_eq_zero.mp
  ext a b
  have hEntry := zornFlatSlice_zero_product_defect_upper X Y a b
  rw [hMul, sub_self] at hEntry
  simpa using hEntry.symm

/-- The upper block of the square defect is the negative commutator of the
two internal operators. -/
theorem zornTransverseOperators_square_defect (B C : Matrix n n ℂ) (a b : n) :
    (zornFlatSlice 0 (zornTransverseOperators B C * zornTransverseOperators B C) -
      zornFlatSlice 0 (zornTransverseOperators B C) *
        zornFlatSlice 0 (zornTransverseOperators B C)) (0, a) (1, b) =
      -(B * C - C * B) a b := by
  simpa [zornTransverseOperators, NCZornElement.zornCross] using
    zornFlatSlice_zero_product_defect_upper (zornTransverseOperators B C)
      (zornTransverseOperators B C) a b

/-- Noncommuting internal matrices give an explicit Zorn element whose
flattened slice does not preserve its square. -/
theorem zornTransverseOperators_square_not_preserved (B C : Matrix n n ℂ)
    (hNoncomm : B * C ≠ C * B) :
    zornFlatSlice 0 (zornTransverseOperators B C * zornTransverseOperators B C) ≠
      zornFlatSlice 0 (zornTransverseOperators B C) *
        zornFlatSlice 0 (zornTransverseOperators B C) := by
  apply zornFlatSlice_zero_not_mul_of_cross_ne_zero
  simpa [zornTransverseOperators, NCZornElement.zornCross, sub_ne_zero] using hNoncomm

/-- The completed Kraus family depends on the full upper coefficient matrix
and is insensitive to the other coordinates of the chosen Zorn slice. -/
theorem zornCornerKraus_eq_of_upper_eq (i : Fin 3)
    (X Y : OperatorZornMatrix (Matrix n n ℂ)) (W : Flat)
    (h : X.sigma_plus i = Y.sigma_plus i) :
    cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W =
      cornerKrausWithResidual zornFlatSheet (zornFlatSlice i Y) W := by
  have hp := (zornFlatSlice_conePlus_eq_iff i X Y).2 h
  have hm : coneMinus zornFlatSheet (star (zornFlatSlice i X)) =
      coneMinus zornFlatSheet (star (zornFlatSlice i Y)) := by
    rw [← star_conePlus zornFlatSheet_star, ← star_conePlus zornFlatSheet_star, hp]
  unfold cornerKrausWithResidual
  rw [hp, hm]

/-- Every contractive flattened Zorn slice determines a trace-preserving
completely positive corner channel after adding its residual Kraus factor. -/
theorem zornFlatSlice_channel_exists (i : Fin 3)
    (X : OperatorZornMatrix (Matrix n n ℂ))
    (hBound : (1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X))).PosSemidef) :
    ∃ W : Flat,
      (∀ Z : Flat, Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W) Z) = Matrix.trace Z) ∧
      (∀ Z : Flat, Z.PosSemidef →
        (InfoGeometry.Quantum.Choi.krausMap
          (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W) Z).PosSemidef) ∧
      (∀ (r : Type*) [Fintype r] [DecidableEq r]
        (Z : Matrix (r × (Fin 2 × n)) (r × (Fin 2 × n)) ℂ), Z.PosSemidef →
          (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
            (InfoGeometry.Modular.Choi.krausChannel
              (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W)) Z).PosSemidef) := by
  obtain ⟨W, hW⟩ := exists_residual_kraus zornFlatSheet (zornFlatSlice i X) hBound
  refine ⟨W, ?_, ?_, ?_⟩
  · intro Z
    exact cornerKrausWithResidual_trace _ _ W Z zornFlatSheet_star hW
  · intro Z hZ
    exact cornerKrausWithResidual_positive _ _ W Z hZ
  · intro r _ _ Z hZ
    exact cornerKrausWithResidual_completely_positive _ _ W Z hZ

/-- Iterating the completed corner channel from the normalized Zorn state. -/
def zornStateEvolution (i : Fin 3)
    (X : OperatorZornMatrix (Matrix n n ℂ)) (W : Flat) : ℕ → Flat
  | 0 => zornNormalizedState i X
  | k + 1 => InfoGeometry.Quantum.Choi.krausMap
      (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W)
      (zornStateEvolution i X W k)

theorem zornStateEvolution_is_density [Nonempty n] (i : Fin 3)
    (X : OperatorZornMatrix (Matrix n n ℂ)) (W : Flat)
    (hBound : (1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X))).PosSemidef)
    (hW : star W * W = 1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X))) (k : ℕ) :
    (zornStateEvolution i X W k).PosSemidef ∧
      Matrix.trace (zornStateEvolution i X W k) = 1 := by
  induction k with
  | zero => exact ⟨zornNormalizedState_positive i X hBound, zornNormalizedState_trace i X⟩
  | succ k ih =>
      change (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W)
        (zornStateEvolution i X W k)).PosSemidef ∧
        Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
          (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W)
          (zornStateEvolution i X W k)) = 1
      exact ⟨cornerKrausWithResidual_positive _ _ W _ ih.1,
        (cornerKrausWithResidual_trace _ _ W _ zornFlatSheet_star hW).trans ih.2⟩

/-- Contractive operator-valued Zorn slices produce a completely positive,
trace-preserving channel and a normalized discrete state evolution. -/
theorem zorn_channel_and_state_evolution [Nonempty n] (i : Fin 3)
    (X : OperatorZornMatrix (Matrix n n ℂ))
    (hBound : (1 - genV zornFlatSheet (zornFlatSlice i X)
      (star (zornFlatSlice i X))).PosSemidef) :
    ∃ W : Flat,
      (∀ Z : Flat, Matrix.trace (InfoGeometry.Quantum.Choi.krausMap
        (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W) Z) = Matrix.trace Z) ∧
      (∀ (r : Type*) [Fintype r] [DecidableEq r]
        (Z : Matrix (r × (Fin 2 × n)) (r × (Fin 2 × n)) ℂ), Z.PosSemidef →
          (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
            (InfoGeometry.Modular.Choi.krausChannel
              (cornerKrausWithResidual zornFlatSheet (zornFlatSlice i X) W)) Z).PosSemidef) ∧
      (∀ k, (zornStateEvolution i X W k).PosSemidef ∧
        Matrix.trace (zornStateEvolution i X W k) = 1) := by
  obtain ⟨W, hW⟩ := exists_residual_kraus zornFlatSheet (zornFlatSlice i X) hBound
  refine ⟨W, ?_, ?_, ?_⟩
  · intro Z
    exact cornerKrausWithResidual_trace _ _ W Z zornFlatSheet_star hW
  · intro r _ _ Z hZ
    exact cornerKrausWithResidual_completely_positive _ _ W Z hZ
  · intro k
    exact zornStateEvolution_is_density i X W hBound hW k

end InfoGeometry.OperatorAlgebra.PeirceSpine.ZornFiniteQuantumBridge

end
