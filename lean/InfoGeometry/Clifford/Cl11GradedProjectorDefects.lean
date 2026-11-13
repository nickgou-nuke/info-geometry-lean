/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Ordered Clifford projector defects

Products of the local idempotents `(1 + eᵢ) / 2` are ordered products in a
noncommutative Clifford algebra. They need not be idempotent. Even the
unnormalized identity `q² = 2 q` for two anticommuting involutions stops being
valid for three factors.

The universal word identities below use only ring relations. Their native
specialization uses the positive basis generators of the existing weighted
`Cl(3,3)` quotient. Nonzero defects are detected by one entry of the existing
Jordan--Wigner algebra representation, without an injectivity assumption.
The entry functional is not asserted to preserve multiplication.
-/

namespace InfoGeometry.Clifford.Cl11GradedProjectorDefects

section OrderedWords

variable {A : Type*} [Ring A]

private theorem square_word {x : A} (hx : x * x = 1) (a : A) :
    x * (x * a) = a := by
  rw [← mul_assoc, hx, one_mul]

private theorem reorder_word {x y : A} (hxy : y * x = -(x * y)) (a : A) :
    y * (x * a) = -(x * (y * a)) := by
  rw [← mul_assoc, hxy, neg_mul, mul_assoc]

/-- The exact two-factor word identity, without commuting its two generators. -/
theorem two_factor_square (x y : A)
    (hx : x * x = 1) (hy : y * y = 1) (hxy : y * x = -(x * y)) :
    ((1 + x) * (1 + y)) * ((1 + x) * (1 + y)) =
      2 * ((1 + x) * (1 + y)) := by
  noncomm_ring [hx, hy, hxy, square_word hx, square_word hy, reorder_word hxy]

/-- The third factor changes the square to a different ordered Clifford word. -/
theorem three_factor_square (x y z : A)
    (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1)
    (hxy : y * x = -(x * y)) (hxz : z * x = -(x * z))
    (hyz : z * y = -(y * z)) :
    ((1 + x) * (1 + y) * (1 + z)) * ((1 + x) * (1 + y) * (1 + z)) =
      4 * ((1 + x) * y * (1 + z)) := by
  noncomm_ring [hx, hy, hz, hxy, hxz, hyz,
    square_word hx, square_word hy, square_word hz,
    reorder_word hxy, reorder_word hxz, reorder_word hyz]

end OrderedWords

noncomputable section

open InfoGeometry.Clifford.Cl11JordanWignerCARBridge
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix

/-- The native quadratic form already used by the three-site JW representation. -/
abbrev Q33 : QuadraticForm ℝ ((Fin 3 ⊕ Fin 3) → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (jwCliffordWeight (n := 3))

abbrev Cl33 := CliffordAlgebra Q33

/-- A positive canonical basis generator in the actual Clifford quotient. -/
def positive (i : Fin 3) : Cl33 :=
  CliffordAlgebra.ι Q33 (Pi.single (Sum.inl i) 1)

private theorem positive_quadratic (i : Fin 3) :
    Q33 (Pi.single (Sum.inl i) 1) = 1 := by
  fin_cases i <;>
    norm_num [Q33, QuadraticMap.weightedSumSquares_apply,
      Fintype.sum_sum_type, Fin.sum_univ_succ, Pi.single_apply, jwCliffordWeight]

private theorem positive_polar (i j : Fin 3) (hij : i ≠ j) :
    QuadraticMap.polar Q33 (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inl j) 1) = 0 := by
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact (hij rfl).elim
    | norm_num [Q33, QuadraticMap.polar, QuadraticMap.weightedSumSquares_apply,
        Fintype.sum_sum_type, Fin.sum_univ_succ, Pi.single_apply, jwCliffordWeight]

theorem positive_square (i : Fin 3) : positive i * positive i = 1 := by
  rw [positive, CliffordAlgebra.ι_sq_scalar, positive_quadratic, map_one]

theorem positive_anticommutes (i j : Fin 3) (hij : i ≠ j) :
    positive i * positive j = -(positive j * positive i) := by
  unfold positive
  rw [CliffordAlgebra.ι_mul_ι_comm, positive_polar i j hij, map_zero, zero_sub]

@[simp] theorem represented_positive (i : Fin 3) :
    jwCliffordRepresentation 3 (positive i) = jwMajoranaPlus 3 i := by
  simpa only [positive, jwCliffordGenerator] using
    jwCliffordRepresentation_basis 3 (Sum.inl i)

/-- Each separate site still supplies a genuine idempotent. -/
def siteProjection (i : Fin 3) : Cl33 := (1 / 2 : ℝ) • (1 + positive i)

theorem siteProjection_idempotent (i : Fin 3) : IsIdempotentElem (siteProjection i) := by
  change siteProjection i * siteProjection i = siteProjection i
  have hsq : (1 + positive i) * (1 + positive i) =
      (1 + positive i) + (1 + positive i) := by
    noncomm_ring [positive_square i]
  dsimp only [siteProjection]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hsq]
  module

def pairWord : Cl33 := (1 + positive 0) * (1 + positive 1)
def tripleWord : Cl33 := (1 + positive 0) * (1 + positive 1) * (1 + positive 2)
def tripleMiddleWord : Cl33 := (1 + positive 0) * positive 1 * (1 + positive 2)

theorem pairWord_square : pairWord * pairWord = (2 : ℝ) • pairWord := by
  have h := two_factor_square (positive 0) (positive 1)
    (positive_square 0) (positive_square 1) (positive_anticommutes 1 0 (by decide))
  simpa only [pairWord, Algebra.smul_def, map_ofNat] using h

theorem tripleWord_square : tripleWord * tripleWord = (4 : ℝ) • tripleMiddleWord := by
  have h := three_factor_square (positive 0) (positive 1) (positive 2)
    (positive_square 0) (positive_square 1) (positive_square 2)
    (positive_anticommutes 1 0 (by decide))
    (positive_anticommutes 2 0 (by decide))
    (positive_anticommutes 2 1 (by decide))
  simpa only [tripleWord, tripleMiddleWord, Algebra.smul_def, map_ofNat] using h

def pairProjection : Cl33 := (1 / 4 : ℝ) • pairWord
def tripleProjection : Cl33 := (1 / 8 : ℝ) • tripleWord

theorem pairProjection_eq_ordered_product :
    pairProjection = siteProjection 0 * siteProjection 1 := by
  simp only [pairProjection, pairWord, siteProjection, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  norm_num

theorem tripleProjection_eq_ordered_product :
    tripleProjection = siteProjection 0 * siteProjection 1 * siteProjection 2 := by
  simp only [tripleProjection, tripleWord, siteProjection, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  norm_num

/-- The two-site product is a half-scaled idempotent, with its scale explicit. -/
theorem pairProjection_square :
    pairProjection * pairProjection = (1 / 2 : ℝ) • pairProjection := by
  dsimp only [pairProjection]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, pairWord_square, smul_smul]
  norm_num [smul_smul]

/-- The defect is an explicit noncommutative word, before any representation. -/
theorem pairProjection_defect :
    pairProjection * pairProjection - pairProjection = (-1 / 8 : ℝ) • pairWord := by
  dsimp only [pairProjection]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, pairWord_square, smul_smul]
  module

/-- Three-site defect with its full ordered Clifford content retained. -/
theorem tripleProjection_defect :
    tripleProjection * tripleProjection - tripleProjection =
      (1 / 16 : ℝ) • tripleMiddleWord - (1 / 8 : ℝ) • tripleWord := by
  dsimp only [tripleProjection]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, tripleWord_square, smul_smul]
  norm_num

/-- The proposed three-site quarter-scaling also has an explicit ordered defect. -/
theorem tripleProjection_scaling_defect :
    tripleProjection * tripleProjection - (1 / 4 : ℝ) • tripleProjection =
      (1 / 16 : ℝ) • tripleMiddleWord - (1 / 32 : ℝ) • tripleWord := by
  dsimp only [tripleProjection]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, tripleWord_square, smul_smul]
  norm_num [smul_smul]

/-- The all-zero coordinate of the existing tensor-stage spinor module. -/
def vacuumIndex : Idx 3 := ((((0 : Fin 1), 0), 0), 0)

theorem represented_pairWord_vacuum :
    jwCliffordRepresentation 3 pairWord vacuumIndex vacuumIndex = 1 := by
  simp only [pairWord, map_mul, map_add, map_one, represented_positive]
  let e : Fin 3 → Matrix (((Fin 1 × Fin 2) × Fin 2) × Fin 2)
      (((Fin 1 × Fin 2) × Fin 2) × Fin 2) ℝ := jwMajoranaPlus 3
  change
    ((1 + e 0) * (1 + e 1) :
      Matrix (((Fin 1 × Fin 2) × Fin 2) × Fin 2)
        (((Fin 1 × Fin 2) × Fin 2) × Fin 2) ℝ)
      ((((0 : Fin 1), 0), 0), 0) ((((0 : Fin 1), 0), 0), 0) = 1
  simp only [Matrix.mul_apply, Matrix.add_apply]
  norm_num [e, vacuumIndex, jwMajoranaPlus, jwCreation, jwAnnihilation, jwStringWithBase,
    globalChirality, kronPow, Idx, gamma_chiral_base, gamma_0_base, gamma_1_base,
    wittCreationBase, wittAnnihilationBase, Cl11Matrix.J1, Cl11Matrix.Eminus,
    Matrix.mul_apply, Matrix.kronecker_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem represented_tripleWord_vacuum :
    jwCliffordRepresentation 3 tripleWord vacuumIndex vacuumIndex = 1 := by
  simp only [tripleWord, map_mul, map_add, map_one, represented_positive]
  let e : Fin 3 → Matrix (((Fin 1 × Fin 2) × Fin 2) × Fin 2)
      (((Fin 1 × Fin 2) × Fin 2) × Fin 2) ℝ := jwMajoranaPlus 3
  change
    ((1 + e 0) * (1 + e 1) *
        (1 + e 2) :
      Matrix (((Fin 1 × Fin 2) × Fin 2) × Fin 2)
        (((Fin 1 × Fin 2) × Fin 2) × Fin 2) ℝ)
      ((((0 : Fin 1), 0), 0), 0) ((((0 : Fin 1), 0), 0), 0) = 1
  simp only [Matrix.mul_apply, Matrix.add_apply]
  norm_num [e, vacuumIndex, jwMajoranaPlus, jwCreation, jwAnnihilation, jwStringWithBase,
    globalChirality, kronPow, Idx, gamma_chiral_base, gamma_0_base, gamma_1_base,
    wittCreationBase, wittAnnihilationBase, Cl11Matrix.J1, Cl11Matrix.Eminus,
    Matrix.mul_apply, Matrix.kronecker_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem represented_tripleMiddleWord_vacuum :
    jwCliffordRepresentation 3 tripleMiddleWord vacuumIndex vacuumIndex = 0 := by
  simp only [tripleMiddleWord, map_mul, map_add, map_one, represented_positive]
  let e : Fin 3 → Matrix (((Fin 1 × Fin 2) × Fin 2) × Fin 2)
      (((Fin 1 × Fin 2) × Fin 2) × Fin 2) ℝ := jwMajoranaPlus 3
  change
    ((1 + e 0) * e 1 *
        (1 + e 2) :
      Matrix (((Fin 1 × Fin 2) × Fin 2) × Fin 2)
        (((Fin 1 × Fin 2) × Fin 2) × Fin 2) ℝ)
      ((((0 : Fin 1), 0), 0), 0) ((((0 : Fin 1), 0), 0), 0) = 0
  simp only [Matrix.mul_apply, Matrix.add_apply]
  norm_num [e, vacuumIndex, jwMajoranaPlus, jwCreation, jwAnnihilation, jwStringWithBase,
    globalChirality, kronPow, Idx, gamma_chiral_base, gamma_0_base, gamma_1_base,
    wittCreationBase, wittAnnihilationBase, Cl11Matrix.J1, Cl11Matrix.Eminus,
    Matrix.mul_apply, Matrix.kronecker_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- The failed extension of `q² = 2q` has an exact nonzero matrix-entry defect. -/
theorem represented_tripleWord_scaling_defect :
    jwCliffordRepresentation 3 (tripleWord * tripleWord - (2 : ℝ) • tripleWord)
      vacuumIndex vacuumIndex = -2 := by
  rw [tripleWord_square]
  simp only [map_sub, map_smul, Matrix.sub_apply, Matrix.smul_apply,
    represented_tripleWord_vacuum, represented_tripleMiddleWord_vacuum, smul_eq_mul]
  norm_num

theorem tripleWord_scaling_defect_ne_zero :
    tripleWord * tripleWord - (2 : ℝ) • tripleWord ≠ 0 := by
  intro h
  have hv := congrArg (fun a : Cl33 => jwCliffordRepresentation 3 a vacuumIndex vacuumIndex) h
  rw [represented_tripleWord_scaling_defect] at hv
  norm_num at hv

theorem represented_pairProjection_defect :
    jwCliffordRepresentation 3 (pairProjection * pairProjection - pairProjection)
      vacuumIndex vacuumIndex = -1 / 8 := by
  rw [pairProjection_defect]
  simp only [map_smul, Matrix.smul_apply, represented_pairWord_vacuum, smul_eq_mul, mul_one]

theorem represented_tripleProjection_defect :
    jwCliffordRepresentation 3 (tripleProjection * tripleProjection - tripleProjection)
      vacuumIndex vacuumIndex = -1 / 8 := by
  rw [tripleProjection_defect]
  simp only [map_sub, map_smul, Matrix.sub_apply, Matrix.smul_apply,
    represented_tripleWord_vacuum, represented_tripleMiddleWord_vacuum, smul_eq_mul]
  norm_num

theorem represented_tripleProjection_scaling_defect :
    jwCliffordRepresentation 3
      (tripleProjection * tripleProjection - (1 / 4 : ℝ) • tripleProjection)
      vacuumIndex vacuumIndex = -1 / 32 := by
  rw [tripleProjection_scaling_defect]
  simp only [map_sub, map_smul, Matrix.sub_apply, Matrix.smul_apply,
    represented_tripleWord_vacuum, represented_tripleMiddleWord_vacuum, smul_eq_mul]
  norm_num

theorem tripleProjection_scaling_defect_ne_zero :
    tripleProjection * tripleProjection - (1 / 4 : ℝ) • tripleProjection ≠ 0 := by
  intro h
  have hv := congrArg (fun a : Cl33 =>
    jwCliffordRepresentation 3 a vacuumIndex vacuumIndex) h
  rw [represented_tripleProjection_scaling_defect] at hv
  norm_num at hv

theorem pairProjection_defect_ne_zero :
    pairProjection * pairProjection - pairProjection ≠ 0 := by
  intro h
  have hv := congrArg (fun a : Cl33 => jwCliffordRepresentation 3 a vacuumIndex vacuumIndex) h
  rw [represented_pairProjection_defect] at hv
  norm_num at hv

theorem tripleProjection_defect_ne_zero :
    tripleProjection * tripleProjection - tripleProjection ≠ 0 := by
  intro h
  have hv := congrArg (fun a : Cl33 => jwCliffordRepresentation 3 a vacuumIndex vacuumIndex) h
  rw [represented_tripleProjection_defect] at hv
  norm_num at hv

theorem pairProjection_not_idempotent : ¬IsIdempotentElem pairProjection :=
  fun h => pairProjection_defect_ne_zero (sub_eq_zero.mpr h.eq)

theorem tripleProjection_not_idempotent : ¬IsIdempotentElem tripleProjection :=
  fun h => tripleProjection_defect_ne_zero (sub_eq_zero.mpr h.eq)

/-- The two individual idempotents retain a concrete noncommuting action. -/
theorem siteProjections_noncommuting : ¬Commute (siteProjection 0) (siteProjection 1) := by
  intro h
  apply pairProjection_not_idempotent
  rw [pairProjection_eq_ordered_product]
  exact IsIdempotentElem.mul_of_commute h
    (siteProjection_idempotent 0) (siteProjection_idempotent 1)

end

end InfoGeometry.Clifford.Cl11GradedProjectorDefects
