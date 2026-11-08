/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Clifford.TowerMatrix
import InfoGeometry.Clifford.CliffordBitWordEquivalence

/-!
# Three-mode Jordan--Wigner Majoranas as real 8 by 8 matrices

This candidate reindexes the repository's three-mode finite Jordan--Wigner
matrix stage to `Matrix (Fin 8) (Fin 8) ℝ`. The six operators are the sums and
differences of the existing creation and annihilation generators. The claims
are finite matrix CAR identities only. Separately,
`InfoGeometry.Canonical.MajoranaEightByEightJW` contains literal `Fin 8`
Jordan--Wigner tables; this module neither imports those tables nor claims an
identification with them. No Clifford algebra isomorphism, split-octonion
identification, or completion claim is made.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl33FiniteJWMajoranaMatrix

open scoped Kronecker Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11JordanWignerCARBridge
open InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.FiniteCantorCuntzBranches
open InfoGeometry.Canonical.CuntzMatrixTraceTower

abbrev Stage3 := MatStage 3
abbrev Matrix8 := Matrix (Fin 8) (Fin 8) ℝ

/-- Explicit recursive binary occupation index, using the repository's
`Idx → BitWord → Fin (2^n)` equivalences rather than a cardinality choice. -/
noncomputable def occupationFinPowTwoEquiv (n : ℕ) :
    TowerMatrix.Idx n ≃ Fin (2 ^ n) :=
  (idxBitWordEquiv n).trans (bitWordFinPowTwoEquiv n)

/-- The binary value of a bit, as a natural number. -/
def bitValue (b : Bool) : ℕ := if b then 1 else 0

private theorem stageIndexEquiv_val (n : ℕ) (i : Fin (2 ^ n)) (b : Fin 2) :
    ((stageIndexEquiv n (i, b) : Fin (2 ^ (n + 1))) : ℕ) =
      2 * (i : ℕ) + (b : ℕ) := by
  simp [stageIndexEquiv, finProdFinEquiv, Nat.mul_comm]
  <;> omega

private theorem bitWordFinPowTwoEquiv_succ_val (n : ℕ)
    (w : BitWord (n + 1)) :
    ((bitWordFinPowTwoEquiv (n + 1) w : Fin (2 ^ (n + 1))) : ℕ) =
      2 * ((bitWordFinPowTwoEquiv n (prefixSucc n w) : Fin (2 ^ n)) : ℕ) +
        bitValue (lastBit n w) := by
  change ((stageIndexEquiv n
      (bitWordFinPowTwoEquiv n (prefixSucc n w),
        (finTwoEquivBool).symm (lastBit n w)) : Fin (2 ^ (n + 1))) : ℕ) = _
  rw [stageIndexEquiv_val]
  cases hb : lastBit n w <;> simp [finTwoEquivBool, bitValue, hb]

/-- At three modes, the repository's explicit recursive occupation index is
`4 b₀ + 2 b₁ + b₂`, with the newly appended bit least significant. -/
theorem bitWordFinPowTwoEquiv_three_formula (w : BitWord 3) :
    ((bitWordFinPowTwoEquiv 3 w : Fin 8) : ℕ) =
      4 * bitValue (w 0) + 2 * bitValue (w 1) + bitValue (w 2) := by
  rw [bitWordFinPowTwoEquiv_succ_val,
    bitWordFinPowTwoEquiv_succ_val,
    bitWordFinPowTwoEquiv_succ_val]
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;>
    simp [prefixSucc, lastBit, bitWordFinPowTwoEquiv,
      bitWordZeroFinOneEquiv, stageIndexEquiv, finProdFinEquiv,
      finTwoEquivBool, bitValue, h0, h1, h2]

/-- The explicit source-index agreement for the three-mode matrix reindexing. -/
theorem occupationFinPowTwoEquiv_three_formula (i : TowerMatrix.Idx 3) :
    ((occupationFinPowTwoEquiv 3 i : Fin 8) : ℕ) =
      4 * bitValue ((idxBitWordEquiv 3 i) 0) +
        2 * bitValue ((idxBitWordEquiv 3 i) 1) +
        bitValue ((idxBitWordEquiv 3 i) 2) := by
  exact bitWordFinPowTwoEquiv_three_formula (idxBitWordEquiv 3 i)

/-- The existing occupation matrix stage reindexed to an explicit `Fin 8`
matrix carrier with the repository's recursive bit-word ordering. -/
noncomputable def stage3ToMatrix8 : Stage3 ≃ₐ[ℝ] Matrix8 :=
  Matrix.reindexAlgEquiv ℝ ℝ (occupationFinPowTwoEquiv 3)

@[simp] theorem stage3ToMatrix8_apply (A : Stage3) (r c : Fin 8) :
    stage3ToMatrix8 A r c =
      A ((occupationFinPowTwoEquiv 3).symm r)
        ((occupationFinPowTwoEquiv 3).symm c) := rfl

private theorem jwCreation_sq_all (n : ℕ) : ∀ i : Fin n,
    jwCreation n i * jwCreation n i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      cases i using Fin.lastCases with
      | cast j =>
          rw [← matStageEmbed_jwCreation]
          change stageEmbed n (jwCreation n j) * stageEmbed n (jwCreation n j) = 0
          calc
            stageEmbed n (jwCreation n j) * stageEmbed n (jwCreation n j) =
                stageEmbed n (jwCreation n j * jwCreation n j) :=
              (map_mul (stageEmbed n) (jwCreation n j) (jwCreation n j)).symm
            _ = stageEmbed n 0 := by rw [ih j]
            _ = 0 := map_zero (stageEmbed n)
      | last =>
          simpa [Fin.last] using
            InfoGeometry.Clifford.Cl11JordanWignerCARBridge.jwCreation_last_sq n

private theorem jwAnnihilation_sq_all (n : ℕ) : ∀ i : Fin n,
    jwAnnihilation n i * jwAnnihilation n i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      cases i using Fin.lastCases with
      | cast j =>
          rw [← matStageEmbed_jwAnnihilation]
          change stageEmbed n (jwAnnihilation n j) * stageEmbed n (jwAnnihilation n j) = 0
          calc
            stageEmbed n (jwAnnihilation n j) * stageEmbed n (jwAnnihilation n j) =
                stageEmbed n (jwAnnihilation n j * jwAnnihilation n j) :=
              (map_mul (stageEmbed n) (jwAnnihilation n j) (jwAnnihilation n j)).symm
            _ = stageEmbed n 0 := by rw [ih j]
            _ = 0 := map_zero (stageEmbed n)
      | last =>
          simpa [Fin.last] using
            InfoGeometry.Clifford.Cl11JordanWignerCARBridge.jwAnnihilation_last_sq n

private theorem jwCreation_anticommute_all (n : ℕ) (i j : Fin n) :
    jwCreation n i * jwCreation n j + jwCreation n j * jwCreation n i = 0 := by
  by_cases h : i = j
  · subst j
    rw [jwCreation_sq_all n i]
    simp
  · exact creation_cross_site_anticommute n i j h

private theorem jwAnnihilation_anticommute_all (n : ℕ) (i j : Fin n) :
    jwAnnihilation n i * jwAnnihilation n j +
      jwAnnihilation n j * jwAnnihilation n i = 0 := by
  by_cases h : i = j
  · subst j
    rw [jwAnnihilation_sq_all n i]
    simp
  · exact annihilation_cross_site_anticommute n i j h

private theorem jwCreationAnnihilation_anticommute (n : ℕ) (i j : Fin n) :
    jwCreation n i * jwAnnihilation n j +
      jwAnnihilation n j * jwCreation n i = if i = j then 1 else 0 := by
  simpa [add_comm, eq_comm] using
    (jwAnnihilation_creation_anticommutator n j i)

/-- The tower's second site has an extra minus sign in its chiral prefix
`gamma_chiral_base = -Z`. The user-facing bit convention uses `Z` there, so
both local operators at site 1 are corrected by the same sign. -/
def bitConventionSign (i : Fin 3) : ℝ := if i.val = 1 then -1 else 1

private theorem bitConventionSign_sq (i : Fin 3) : bitConventionSign i ^ 2 = 1 := by
  fin_cases i <;> norm_num [bitConventionSign]

/-- The user-facing column-vector creation matrices are the tower's
`jwAnnihilation` matrices (the tower names its upper-right atom creation). -/
noncomputable def create8 (i : Fin 3) : Matrix8 :=
  bitConventionSign i • stage3ToMatrix8 (jwAnnihilation 3 i)

/-- The user-facing column-vector annihilation matrices are the tower's
`jwCreation` matrices, with the same second-site convention correction. -/
noncomputable def annihilate8 (i : Fin 3) : Matrix8 :=
  bitConventionSign i • stage3ToMatrix8 (jwCreation 3 i)

theorem create8_sq_zero (i : Fin 3) : create8 i * create8 i = 0 := by
  simp only [create8, map_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hs : bitConventionSign i * bitConventionSign i = 1 := by
    simpa [pow_two] using bitConventionSign_sq i
  rw [hs, one_smul, ← map_mul, jwAnnihilation_sq_all, map_zero]

theorem annihilate8_sq_zero (i : Fin 3) : annihilate8 i * annihilate8 i = 0 := by
  simp only [annihilate8, map_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hs : bitConventionSign i * bitConventionSign i = 1 := by
    simpa [pow_two] using bitConventionSign_sq i
  rw [hs, one_smul, ← map_mul, jwCreation_sq_all, map_zero]

theorem create8_anticommute (i j : Fin 3) :
    create8 i * create8 j + create8 j * create8 i = 0 := by
  have hmap := congrArg stage3ToMatrix8 (jwAnnihilation_anticommute_all 3 i j)
  simp only [map_add, map_mul] at hmap
  simp only [create8, map_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (bitConventionSign j) (bitConventionSign i), ← smul_add, hmap,
    map_zero, smul_zero]

theorem annihilate8_anticommute (i j : Fin 3) :
    annihilate8 i * annihilate8 j + annihilate8 j * annihilate8 i = 0 := by
  have hmap := congrArg stage3ToMatrix8 (jwCreation_anticommute_all 3 i j)
  simp only [map_add, map_mul] at hmap
  simp only [annihilate8, map_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (bitConventionSign j) (bitConventionSign i), ← smul_add, hmap,
    map_zero, smul_zero]

theorem annihilate8_create8_car (i j : Fin 3) :
    annihilate8 i * create8 j + create8 j * annihilate8 i =
      if i = j then 1 else 0 := by
  have hmap := congrArg stage3ToMatrix8 (jwCreationAnnihilation_anticommute 3 i j)
  have hs : bitConventionSign i * bitConventionSign i = 1 := by
    simpa [pow_two] using bitConventionSign_sq i
  simp only [map_add, map_mul] at hmap
  simp only [annihilate8, create8, map_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [mul_comm (bitConventionSign j) (bitConventionSign i), ← smul_add, hmap]
  by_cases h : i = j
  · subst j
    rw [hs]
    simp [map_one]
  · simp [h, map_zero]

/-- The finite Jordan--Wigner operator algebra is genuinely noncommutative:
creation and annihilation at one site do not commute. This witness is derived
from this file's CAR and nilpotence laws on the actual `Fin 8` matrix carrier. -/
theorem create8_annihilate8_noncommute (i : Fin 3) :
    create8 i * annihilate8 i ≠ annihilate8 i * create8 i := by
  intro hcomm
  have hcar := annihilate8_create8_car i i
  have hsum : create8 i * annihilate8 i + create8 i * annihilate8 i = 1 := by
    simpa [hcomm] using hcar
  have hnil :
      (create8 i * annihilate8 i) * (create8 i * annihilate8 i) = 0 := by
    calc
      (create8 i * annihilate8 i) * (create8 i * annihilate8 i) =
          create8 i * (annihilate8 i * create8 i) * annihilate8 i := by noncomm_ring
      _ = create8 i * (create8 i * annihilate8 i) * annihilate8 i := by rw [hcomm]
      _ = (create8 i * create8 i) * (annihilate8 i * annihilate8 i) := by noncomm_ring
      _ = 0 := by rw [create8_sq_zero, annihilate8_sq_zero]; simp
  have hone : (1 : Matrix8) = 0 := by
    calc
      1 = (create8 i * annihilate8 i + create8 i * annihilate8 i) *
          (create8 i * annihilate8 i + create8 i * annihilate8 i) := by rw [hsum]; simp
      _ = 0 := by rw [add_mul, mul_add, hnil]; simp
  exact one_ne_zero hone

/-- Concrete creation operator for mode zero, exposed for the carrier-level
noncommutativity witness below. -/
noncomputable def mode0Create : Matrix8 := create8 0

/-- Concrete annihilation operator for mode zero, exposed for the carrier-level
noncommutativity witness below. -/
noncomputable def mode0Annihilate : Matrix8 := annihilate8 0

/-- A closed noncommutativity witness in the actual `Matrix (Fin 8) (Fin 8) ℝ`
carrier. -/
theorem mode0_car_noncommute :
    mode0Create * mode0Annihilate ≠ mode0Annihilate * mode0Create := by
  simpa [mode0Create, mode0Annihilate] using create8_annihilate8_noncommute 0

/-- Positive-square Majorana family `c† + c`. -/
noncomputable def majoranaPlus (i : Fin 3) : Matrix8 := create8 i + annihilate8 i

/-- Negative-square Majorana family `c† - c`. -/
noncomputable def majoranaMinus (i : Fin 3) : Matrix8 := create8 i - annihilate8 i

private theorem anticommutator_add_add {R : Type*} [Ring R] (a b c d : R) :
    (a + b) * (c + d) + (c + d) * (a + b) =
      (a * c + c * a) + (a * d + d * a) +
        (b * c + c * b) + (b * d + d * b) := by
  noncomm_ring

private theorem anticommutator_sub_sub {R : Type*} [Ring R] (a b c d : R) :
    (a - b) * (c - d) + (c - d) * (a - b) =
      (a * c + c * a) - (a * d + d * a) -
        (b * c + c * b) + (b * d + d * b) := by
  noncomm_ring

private theorem anticommutator_add_sub {R : Type*} [Ring R] (a b c d : R) :
    (a + b) * (c - d) + (c - d) * (a + b) =
      (a * c + c * a) - (a * d + d * a) +
        (b * c + c * b) - (b * d + d * b) := by
  noncomm_ring

theorem majoranaPlus_odd_anticommutator (i j : Fin 3) :
    majoranaPlus i * majoranaPlus j + majoranaPlus j * majoranaPlus i =
      if i = j then (2 : ℝ) • (1 : Matrix8) else 0 := by
  by_cases hij : i = j
  · subst j
    have hcc := create8_anticommute i i
    have haa := annihilate8_anticommute i i
    have hmix := annihilate8_create8_car i i
    have hmix0 : annihilate8 i * create8 i + create8 i * annihilate8 i = 1 := by
      simpa using hmix
    have hmix' : create8 i * annihilate8 i + annihilate8 i * create8 i = 1 := by
      simpa [add_comm] using hmix0
    rw [if_pos rfl]
    change (create8 i + annihilate8 i) * (create8 i + annihilate8 i) +
      (create8 i + annihilate8 i) * (create8 i + annihilate8 i) = _
    rw [anticommutator_add_add, hcc, hmix', hmix, haa]
    simp [two_smul]
  · have hcc := create8_anticommute i j
    have haa := annihilate8_anticommute i j
    have hmix₁ := annihilate8_create8_car i j
    have hmix₂ := annihilate8_create8_car j i
    have hji : j ≠ i := fun h => hij h.symm
    have hmix₂0 : annihilate8 j * create8 i + create8 i * annihilate8 j = 0 := by
      simpa [hji] using hmix₂
    have hmix₁0 : annihilate8 i * create8 j + create8 j * annihilate8 i = 0 := by
      simpa [hij] using hmix₁
    have hmix₁' : create8 i * annihilate8 j + annihilate8 j * create8 i = 0 := by
      simpa [add_comm] using hmix₂0
    have hmix₂' : annihilate8 i * create8 j + create8 j * annihilate8 i = 0 := hmix₁0
    rw [if_neg hij]
    change (create8 i + annihilate8 i) * (create8 j + annihilate8 j) +
      (create8 j + annihilate8 j) * (create8 i + annihilate8 i) = _
    rw [anticommutator_add_add, hcc, hmix₁', hmix₂', haa]
    module

theorem majoranaMinus_odd_anticommutator (i j : Fin 3) :
    majoranaMinus i * majoranaMinus j + majoranaMinus j * majoranaMinus i =
      if i = j then -(2 : ℝ) • (1 : Matrix8) else 0 := by
  by_cases hij : i = j
  · subst j
    have hcc := create8_anticommute i i
    have haa := annihilate8_anticommute i i
    have hmix := annihilate8_create8_car i i
    have hmix0 : annihilate8 i * create8 i + create8 i * annihilate8 i = 1 := by
      simpa using hmix
    have hmix' : create8 i * annihilate8 i + annihilate8 i * create8 i = 1 := by
      simpa [add_comm] using hmix0
    rw [if_pos rfl]
    change (create8 i - annihilate8 i) * (create8 i - annihilate8 i) +
      (create8 i - annihilate8 i) * (create8 i - annihilate8 i) = _
    rw [anticommutator_sub_sub, hcc, hmix', hmix0, haa]
    norm_num [two_smul]
  · have hcc := create8_anticommute i j
    have haa := annihilate8_anticommute i j
    have hmix₁ := annihilate8_create8_car i j
    have hmix₂ := annihilate8_create8_car j i
    have hji : j ≠ i := fun h => hij h.symm
    have hmix₂0 : annihilate8 j * create8 i + create8 i * annihilate8 j = 0 := by
      simpa [hji] using hmix₂
    have hmix₁0 : annihilate8 i * create8 j + create8 j * annihilate8 i = 0 := by
      simpa [hij] using hmix₁
    have hmix₁' : create8 i * annihilate8 j + annihilate8 j * create8 i = 0 := by
      simpa [add_comm] using hmix₂0
    have hmix₂' : annihilate8 i * create8 j + create8 j * annihilate8 i = 0 := hmix₁0
    rw [if_neg hij]
    change (create8 i - annihilate8 i) * (create8 j - annihilate8 j) +
      (create8 j - annihilate8 j) * (create8 i - annihilate8 i) = _
    rw [anticommutator_sub_sub, hcc, hmix₁', hmix₂', haa]
    module

theorem majoranaPlusMinus_odd_anticommutator (i j : Fin 3) :
    majoranaPlus i * majoranaMinus j + majoranaMinus j * majoranaPlus i = 0 := by
  have hcc := create8_anticommute i j
  have haa := annihilate8_anticommute i j
  have hmix₁ := annihilate8_create8_car i j
  have hmix₂ := annihilate8_create8_car j i
  by_cases hij : i = j
  · subst j
    have hmix0 : annihilate8 i * create8 i + create8 i * annihilate8 i = 1 := by
      simpa using hmix₁
    have hmix₁' : create8 i * annihilate8 i + annihilate8 i * create8 i = 1 := by
      simpa [add_comm] using hmix0
    have hmix₂' : annihilate8 i * create8 i + create8 i * annihilate8 i = 1 := hmix0
    change (create8 i + annihilate8 i) * (create8 i - annihilate8 i) +
      (create8 i - annihilate8 i) * (create8 i + annihilate8 i) = _
    rw [anticommutator_add_sub, hcc, hmix₁', hmix₂', haa]
    module
  · simp [hij] at hmix₁ hmix₂
    have hmix₁' : create8 i * annihilate8 j + annihilate8 j * create8 i = 0 := by
      have hz : annihilate8 j * create8 i + create8 i * annihilate8 j = 0 := by
        have hji : j ≠ i := fun h => hij h.symm
        simpa [hji] using hmix₂
      simpa [add_comm] using hz
    have hmix₂' : annihilate8 i * create8 j + create8 j * annihilate8 i = 0 := hmix₁
    change (create8 i + annihilate8 i) * (create8 j - annihilate8 j) +
      (create8 j - annihilate8 j) * (create8 i + annihilate8 i) = _
    rw [anticommutator_add_sub, hcc, hmix₁', hmix₂', haa]
    simp

/-- The three creation operators are recovered exactly from the signed
Majorana pairs; this is an operator identity in the noncommutative matrix
algebra. -/
theorem create8_recovered_from_majoranas (i : Fin 3) :
    (1 / 2 : ℝ) • (majoranaPlus i + majoranaMinus i) = create8 i := by
  unfold majoranaPlus majoranaMinus
  simp only [smul_add, smul_sub]
  module

/-- The three annihilation operators are recovered exactly from the signed
Majorana pairs. -/
theorem annihilate8_recovered_from_majoranas (i : Fin 3) :
    (1 / 2 : ℝ) • (majoranaPlus i - majoranaMinus i) = annihilate8 i := by
  unfold majoranaPlus majoranaMinus
  simp only [smul_add, smul_sub]
  module

theorem recovered_operators_satisfy_car (i j : Fin 3) :
    ((1 / 2 : ℝ) • (majoranaPlus i - majoranaMinus i)) *
        ((1 / 2 : ℝ) • (majoranaPlus j + majoranaMinus j)) +
      ((1 / 2 : ℝ) • (majoranaPlus j + majoranaMinus j)) *
        ((1 / 2 : ℝ) • (majoranaPlus i - majoranaMinus i)) =
      if i = j then 1 else 0 := by
  rw [annihilate8_recovered_from_majoranas, create8_recovered_from_majoranas,
    annihilate8_create8_car]

end InfoGeometry.Clifford.Cl33FiniteJWMajoranaMatrix
