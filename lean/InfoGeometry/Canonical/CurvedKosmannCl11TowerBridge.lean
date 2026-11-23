/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.CurvedLorentzianKosmannFrame
import InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.PontryaginSpace
import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Curved real Kosmann coefficients on the native Cl(1,1) tensor tower

For each point and tangent direction in the curved real chart, the established
Kosmann matrix is inserted into the first factor of the existing Cl(1,1)
matrix tower. Left multiplication is compatible with the tower's actual
`A ↦ A ⊗ I₂` bonding maps, so it induces an endomorphism of the existing
categorical colimit. The primitive left-ideal carrier is transported
stagewise as well, yielding a colimit action on the actual two-sheet spinor
sector rather than only on the regular module. No analytic completion or
global spin-bundle holonomy is claimed.
-/

noncomputable section

namespace InfoGeometry.Canonical.CurvedKosmannCl11TowerBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge
open InfoGeometry.Geometry.CurvedLorentzianKosmannFrame
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open scoped Kronecker

local instance : LieRing
    (InfoGeometry.Krein.DoubledSpace ℝ →L[ℝ] InfoGeometry.Krein.DoubledSpace ℝ) :=
  LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ
    (InfoGeometry.Krein.DoubledSpace ℝ →L[ℝ] InfoGeometry.Krein.DoubledSpace ℝ) :=
  LieAlgebra.ofAssociativeAlgebra

/-- The one-factor tower index `Idx 1 = Fin 1 × Fin 2` is identified with the
fixed two-component real spinor index by forgetting its unique first entry. -/
def idxOneEquivFinTwo : Idx 1 ≃ Fin 2 where
  toFun i := i.2
  invFun j := (⟨0, by decide⟩, j)
  left_inv i := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  right_inv _ := rfl

@[simp] theorem idxOneEquivFinTwo_symm_apply (j : Fin 2) :
    idxOneEquivFinTwo.symm j = (⟨0, by decide⟩, j) := by
  apply idxOneEquivFinTwo.injective
  change j = idxOneEquivFinTwo (⟨0, by decide⟩, j)
  rfl

/-- Reindexing the initial tower stage into the real `Mat2` carrier used by
the curved Riesz spinor owner. -/
noncomputable def stageZeroMatrixEquiv : Stage 0 ≃ₐ[ℝ] Mat2 :=
  Matrix.reindexAlgEquiv ℝ ℝ idxOneEquivFinTwo

@[simp] theorem stageZeroMatrixEquiv_apply (A : Stage 0) (i j : Fin 2) :
    stageZeroMatrixEquiv A i j =
      A (idxOneEquivFinTwo.symm i) (idxOneEquivFinTwo.symm j) := rfl

/-- Curved Kosmann coefficient placed in the first real `Cl(1,1)` matrix
factor of the maintained tower. -/
def kosmannBaseElem (x : ℝ) (v : Tangent) : Stage 0 :=
  (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ spinConnection x v

/-- Reindexing the initial tensor stage cancels its singleton matrix factor. -/
theorem stageZero_oneKronecker (A : Mat2) :
    stageZeroMatrixEquiv
      (show Stage 0 from
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ A)) = A := by
  ext i j
  rw [stageZeroMatrixEquiv_apply]
  simp only [idxOneEquivFinTwo_symm_apply]
  change (1 : ℝ) * A i j = A i j
  simp

/-- The singleton factor in the first tensor slot evaluates to the identity,
so the reindexed initial-stage coefficient is exactly the curved spin
connection matrix, with the same real spinor convention. -/
theorem stageZero_kosmannBaseElem_eq_spinConnection (x : ℝ) (v : Tangent) :
    stageZeroMatrixEquiv (kosmannBaseElem x v) = spinConnection x v := by
  exact stageZero_oneKronecker (spinConnection x v)

/-- The reindexed initial-stage action agrees with ordinary left matrix
multiplication by the curved real Kosmann coefficient. -/
theorem stageZero_kosmann_left_action (x : ℝ) (v : Tangent) (z : Stage 0) :
    stageZeroMatrixEquiv (kosmannBaseElem x v * z) =
      spinConnection x v * stageZeroMatrixEquiv z := by
  rw [map_mul, stageZero_kosmannBaseElem_eq_spinConnection]

/-- In the fixed real Pauli representation the stage-zero chirality is the
diagonal involution `diag(-1,1)`. -/
theorem stageZero_globalChirality_eq :
    stageZeroMatrixEquiv (globalChirality 1) =
      !![(-1 : ℝ), 0; 0, 1] := by
  rw [show globalChirality 1 =
      (show Stage 0 from
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ gamma_chiral_base)) by rfl]
  rw [stageZero_oneKronecker]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma_chiral_base, gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eminus, Fin.sum_univ_two]

/-- The negative-chirality tower projector at its initial stage is the same
primitive real spinor idempotent used by the curved Riesz left ideal. -/
theorem stageZero_fMinus_eq_spinorIdempotent_matrix :
    stageZeroMatrixEquiv fMinusBase =
      InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat spinorIdempotent := by
  rw [spinorIdempotent_matrix]
  rw [show fMinusBase = (1 / 2 : ℝ) • (1 - globalChirality 1) by rfl]
  rw [map_smul, map_sub, map_one, stageZero_globalChirality_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.smul_apply, Matrix.sub_apply]

/-- The stage-zero real tower matrix algebra is identified with the same
real `Cl(1,1)` carrier used to define the curved Riesz spinor ideal. -/
noncomputable def stageZeroCliffordEquiv :
    Stage 0 ≃ₐ[ℝ] CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 :=
  stageZeroMatrixEquiv.trans InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm

/-- The real tower reindexing preserves genuine noncommutativity: the
transported bivector generator and negative Clifford generator do not commute. -/
def stageZeroJ1 : Stage 0 :=
  stageZeroCliffordEquiv.symm InfoGeometry.Clifford.Cl11Matrix.J1_cl

def stageZeroEminus : Stage 0 := stageZeroCliffordEquiv.symm
  (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (0, 1))

theorem stageZeroClifford_noncommuting_generators :
    stageZeroJ1 * stageZeroEminus ≠ stageZeroEminus * stageZeroJ1 := by
  intro h
  have hm := congrArg (fun z =>
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat (stageZeroCliffordEquiv z)) h
  apply InfoGeometry.Clifford.Cl11Matrix.J1_mul_Eminus_ne
  simpa [stageZeroJ1, stageZeroEminus, stageZeroCliffordEquiv,
    AlgEquiv.trans_apply,
    InfoGeometry.Clifford.Cl11Matrix.J1_cl,
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat_iota_pos,
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat_iota_neg,
    InfoGeometry.Clifford.Cl11Matrix.Eplus_mul_Eminus] using hm

/-- This algebra equivalence sends the tower's negative-chirality primitive
to the Riesz idempotent, not merely to an isomorphic matrix idempotent. -/
theorem stageZeroCliffordEquiv_fMinusBase :
    stageZeroCliffordEquiv fMinusBase = spinorIdempotent := by
  apply InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.injective
  simp only [stageZeroCliffordEquiv, AlgEquiv.trans_apply,
    AlgEquiv.apply_symm_apply]
  exact stageZero_fMinus_eq_spinorIdempotent_matrix

/-- The curved connection coefficient transported through the stage-zero
Clifford equivalence is precisely the existing real `Cl(1,1)` spin lift. -/
theorem stageZeroCliffordEquiv_kosmannBaseElem (x : ℝ) (v : Tangent) :
    stageZeroCliffordEquiv (kosmannBaseElem x v) =
      InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm (spinConnection x v) := by
  simp [stageZeroCliffordEquiv, AlgEquiv.trans_apply,
    stageZero_kosmannBaseElem_eq_spinConnection]

/-! ## Primitive spinor ideal in every tower stage -/

/-- The stage-`n` spinor sector is the left ideal cut out by the coherent
negative-chirality primitive idempotent already transported by the Hestenes
tower owner. -/
def spinorStageSubmodule (n : ℕ) : Submodule ℝ (Stage n) where
  carrier := {a | a * fMinusElem n = a}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change a * fMinusElem n = a at ha
    change b * fMinusElem n = b at hb
    change (a + b) * fMinusElem n = a + b
    rw [add_mul, ha, hb]
  smul_mem' := by
    intro c a ha
    change a * fMinusElem n = a at ha
    change (c • a) * fMinusElem n = c • a
    rw [smul_mul_assoc, ha]

abbrev SpinorStage (n : ℕ) := spinorStageSubmodule n

/-- The coherent negative-sheet sector of the first Hestenes tower stage is
linearly equivalent to the curved owner's actual Riesz spinor left ideal. -/
noncomputable def stageZeroSpinorRieszEquiv :
    SpinorStage 0 ≃ₗ[ℝ]
      InfoGeometry.Clifford.LipschitzWittRieszPrimary.RieszLeftIdeal
        (CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) spinorIdempotent where
  toFun a := by
    refine ⟨stageZeroCliffordEquiv a.1, ?_⟩
    apply (InfoGeometry.Clifford.LipschitzWittRieszPrimary.mem_rieszLeftIdeal_iff_mul_eq
      spinorIdempotent_idempotent _).2
    calc
      stageZeroCliffordEquiv a.1 * spinorIdempotent =
          stageZeroCliffordEquiv a.1 * stageZeroCliffordEquiv fMinusBase := by
            rw [stageZeroCliffordEquiv_fMinusBase]
      _ = stageZeroCliffordEquiv (a.1 * fMinusBase) :=
            (stageZeroCliffordEquiv.map_mul _ _).symm
      _ = stageZeroCliffordEquiv a.1 := congrArg stageZeroCliffordEquiv a.2
  invFun z := by
    refine ⟨stageZeroCliffordEquiv.symm z.1, ?_⟩
    change stageZeroCliffordEquiv.symm z.1 * fMinusBase =
      stageZeroCliffordEquiv.symm z.1
    apply stageZeroCliffordEquiv.injective
    calc
      stageZeroCliffordEquiv (stageZeroCliffordEquiv.symm z.1 * fMinusBase) =
          stageZeroCliffordEquiv (stageZeroCliffordEquiv.symm z.1) *
            stageZeroCliffordEquiv fMinusBase := stageZeroCliffordEquiv.map_mul _ _
      _ = z.1 * spinorIdempotent := by rw [AlgEquiv.apply_symm_apply,
        stageZeroCliffordEquiv_fMinusBase]
      _ = z.1 :=
        (InfoGeometry.Clifford.LipschitzWittRieszPrimary.mem_rieszLeftIdeal_iff_mul_eq
          spinorIdempotent_idempotent z.1).mp z.2
      _ = stageZeroCliffordEquiv (stageZeroCliffordEquiv.symm z.1) :=
        (stageZeroCliffordEquiv.apply_symm_apply z.1).symm
  left_inv a := by
    apply Subtype.ext
    exact stageZeroCliffordEquiv.symm_apply_apply a.1
  right_inv z := by
    apply Subtype.ext
    exact stageZeroCliffordEquiv.apply_symm_apply z.1
  map_add' a b := by
    apply Subtype.ext
    exact stageZeroCliffordEquiv.map_add a.1 b.1
  map_smul' c a := by
    apply Subtype.ext
    simp

/-- The coefficient transported to stage `n` by the existing tower maps. -/
def kosmannStageElem (x : ℝ) (v : Tangent) (n : ℕ) : Stage n :=
  stageMapAlg 0 n (Nat.zero_le n) (kosmannBaseElem x v)

/-- The generator transported from the existing real Clifford bivector into
the initial matrix stage. -/
theorem stageZeroMatrixEquiv_stageZeroJ1 :
    stageZeroMatrixEquiv stageZeroJ1 = InfoGeometry.Clifford.Cl11Matrix.J1 := by
  calc
    stageZeroMatrixEquiv stageZeroJ1 =
        InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
          (InfoGeometry.Clifford.Cl11Matrix.J1_cl) := by
      simp [stageZeroJ1, stageZeroCliffordEquiv]
    _ = InfoGeometry.Clifford.Cl11Matrix.J1 := by
      have h := congrArg InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat
        cl11EquivMat_symm_J1
      simpa using h.symm

/-- On the time direction, the curved Rindler spin coefficient is the scalar
multiple `-x` of the fixed real bivector generator. -/
theorem kosmannBaseElem_time_eq_neg_smul (x : ℝ) :
    kosmannBaseElem x (1, 0) = (-x) • stageZeroJ1 := by
  apply stageZeroMatrixEquiv.injective
  rw [stageZero_kosmannBaseElem_eq_spinConnection, map_smul,
    spinConnection_eq_lapseDerivative, deriv_lapse,
    stageZeroMatrixEquiv_stageZeroJ1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, InfoGeometry.Clifford.Cl11Matrix.J1]

/-- The time-direction Kosmann coefficient has the same affine spatial
dependence at each actual tensor-tower stage. -/
theorem kosmannStageElem_time_eq_neg_smul (x : ℝ) (n : ℕ) :
    kosmannStageElem x (1, 0) n =
      (-x) • stageMapAlg 0 n (Nat.zero_le n) stageZeroJ1 := by
  rw [kosmannStageElem, kosmannBaseElem_time_eq_neg_smul]
  exact (stageMapAlg 0 n (Nat.zero_le n)).toLinearMap.map_smul
    (-x) stageZeroJ1

/-- The transported matrix generator is the already-owned first-sheet
exchange element of the Hestenes--Krein tower. -/
theorem stageZeroJ1_eq_etaBase : stageZeroJ1 = etaBase := by
  apply stageZeroMatrixEquiv.injective
  have hη : stageZeroMatrixEquiv etaBase =
      InfoGeometry.Clifford.Cl11Matrix.J1 := by
    change stageZeroMatrixEquiv
        (show Stage 0 from
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ gamma_0_base)) = _
    rw [stageZero_oneKronecker]
    rfl
  exact stageZeroMatrixEquiv_stageZeroJ1.trans hη.symm

/-- The curved time-Kosmann coefficient is a scalar multiple of the
coherent sheet exchange at every finite tower stage. -/
theorem kosmannStageElem_time_eq_etaElem (x : ℝ) (n : ℕ) :
    kosmannStageElem x (1, 0) n = (-x) • etaElem n := by
  rw [kosmannStageElem_time_eq_neg_smul, stageZeroJ1_eq_etaBase]
  rfl

/-- The existing first-factor sheet exchange intertwines the two coherent
Peirce projectors, using their proved tower compatibility. -/
theorem etaElem_mul_fPlusElem_eq_fMinusElem_mul_etaElem (n : ℕ) :
    etaElem n * fPlusElem n = fMinusElem n * etaElem n := by
  have hη := etaElem_sq n
  have hconj := etaElem_fPlusElem_etaElem n
  calc
    etaElem n * fPlusElem n =
        etaElem n * fPlusElem n * (etaElem n * etaElem n) := by rw [hη, mul_one]
    _ = (etaElem n * fPlusElem n * etaElem n) * etaElem n := by
          noncomm_ring
    _ = fMinusElem n * etaElem n := by rw [hconj]

/-- The curved time-Kosmann action exchanges the two coherent Hestenes--Krein
sheet projectors at every stage, not only the full tensor-product chirality. -/
theorem kosmannStageElem_time_mul_fPlusElem (x : ℝ) (n : ℕ) :
    kosmannStageElem x (1, 0) n * fPlusElem n =
      fMinusElem n * kosmannStageElem x (1, 0) n := by
  rw [kosmannStageElem_time_eq_etaElem, Matrix.smul_mul,
    Matrix.mul_smul, etaElem_mul_fPlusElem_eq_fMinusElem_mul_etaElem]

/-- Reverse exchange of the two coherent Hestenes--Krein sheet projectors by
the curved time-Kosmann action. -/
theorem kosmannStageElem_time_mul_fMinusElem (x : ℝ) (n : ℕ) :
    kosmannStageElem x (1, 0) n * fMinusElem n =
      fPlusElem n * kosmannStageElem x (1, 0) n := by
  rw [kosmannStageElem_time_eq_etaElem, Matrix.smul_mul, Matrix.mul_smul]
  have hη := etaElem_sq n
  have hconj := etaElem_fMinusElem_etaElem n
  have hrev : etaElem n * fMinusElem n = fPlusElem n * etaElem n := by
    calc
      etaElem n * fMinusElem n =
          etaElem n * fMinusElem n * (etaElem n * etaElem n) := by
            rw [hη, mul_one]
      _ = (etaElem n * fMinusElem n * etaElem n) * etaElem n := by
            noncomm_ring
      _ = fPlusElem n * etaElem n := by rw [hconj]
  rw [hrev]

/-- The transported initial bivector generator exchanges the two global
chiral sectors at every finite stage of the existing real tensor tower. -/
theorem stageZeroJ1_anticomm_globalChirality :
    ∀ n : ℕ,
      stageMapAlg 0 n (Nat.zero_le n) stageZeroJ1 * globalChirality (n + 1) +
        globalChirality (n + 1) *
          stageMapAlg 0 n (Nat.zero_le n) stageZeroJ1 = 0 := by
  intro n
  induction n with
  | zero =>
      have hbase : stageZeroJ1 * globalChirality 1 +
          globalChirality 1 * stageZeroJ1 = 0 := by
        apply stageZeroMatrixEquiv.injective
        rw [map_add, map_mul, map_mul, stageZeroMatrixEquiv_stageZeroJ1,
          stageZero_globalChirality_eq]
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [InfoGeometry.Clifford.Cl11Matrix.J1, Matrix.mul_apply,
            Matrix.add_apply, Fin.sum_univ_two]
      simpa [stageMapAlg_refl] using hbase
  | succ n ih =>
      rw [stageMapAlg_succ]
      change (stageMapAlg 0 n (Nat.zero_le n) stageZeroJ1 ⊗ₖ
          (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
          (kronPow gamma_chiral_base (n + 1) ⊗ₖ gamma_chiral_base) +
        (kronPow gamma_chiral_base (n + 1) ⊗ₖ gamma_chiral_base) *
          (stageMapAlg 0 n (Nat.zero_le n) stageZeroJ1 ⊗ₖ
            (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp only [one_mul, mul_one]
      rw [← Matrix.add_kronecker]
      have hprev := congrArg
        (fun z : MatStage (n + 1) => z ⊗ₖ gamma_chiral_base) ih
      simpa [globalChirality] using hprev

/-- The curved time-direction Kosmann generator is odd for the global
chirality on every finite stage: it maps each chiral sector into the other. -/
theorem kosmannStageElem_time_anticomm_globalChirality (x : ℝ) (n : ℕ) :
    kosmannStageElem x (1, 0) n * globalChirality (n + 1) +
      globalChirality (n + 1) * kosmannStageElem x (1, 0) n = 0 := by
  rw [kosmannStageElem_time_eq_neg_smul]
  rw [Matrix.smul_mul, Matrix.mul_smul]
  have h := stageZeroJ1_anticomm_globalChirality n
  rw [← smul_add, h]
  simp

/-- The curved time-Kosmann operator exchanges the maintained finite-stage
chiral projectors. This follows from its oddness for the global volume element. -/
theorem kosmannStageElem_time_mul_chiralProjPlus (x : ℝ) (n : ℕ) :
    kosmannStageElem x (1, 0) n * chiralProjPlus (n + 1) =
      chiralProjMinus (n + 1) * kosmannStageElem x (1, 0) n := by
  have h := kosmannStageElem_time_anticomm_globalChirality x n
  dsimp [chiralProjPlus, chiralProjMinus]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [mul_add, sub_mul, mul_one, one_mul]
  rw [eq_neg_of_add_eq_zero_left h]
  noncomm_ring

/-- The reverse chiral projector is exchanged by the same curved
time-Kosmann operator. -/
theorem kosmannStageElem_time_mul_chiralProjMinus (x : ℝ) (n : ℕ) :
    kosmannStageElem x (1, 0) n * chiralProjMinus (n + 1) =
      chiralProjPlus (n + 1) * kosmannStageElem x (1, 0) n := by
  have h := kosmannStageElem_time_anticomm_globalChirality x n
  dsimp [chiralProjPlus, chiralProjMinus]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [mul_sub, add_mul, mul_one, one_mul]
  rw [eq_neg_of_add_eq_zero_left h]
  noncomm_ring

/-- The curved spin-curvature generator, transported through the existing
bonding maps, is the time-Kosmann coefficient at the chart point `x = -1`.
The chart's spin curvature is constant, so this identifies one and the same
real bivector coefficient at every finite tensor depth. -/
theorem kosmannStageElem_curvatureLift (x : ℝ) (n : ℕ) :
    kosmannStageElem (-1) (1, 0) n =
      stageMapAlg 0 n (Nat.zero_le n)
        (stageZeroMatrixEquiv.symm
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x)) := by
  have hbase : kosmannBaseElem (-1) (1, 0) =
      stageZeroMatrixEquiv.symm
        (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x) := by
    apply stageZeroMatrixEquiv.injective
    rw [stageZero_kosmannBaseElem_eq_spinConnection]
    rw [InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinConnection_eq_lapseDerivative,
      InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature_eq,
      InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.deriv_lapse]
    simp [InfoGeometry.Clifford.Cl11Matrix.J1]
  calc
    kosmannStageElem (-1) (1, 0) n =
        stageMapAlg 0 n (Nat.zero_le n) (kosmannBaseElem (-1) (1, 0)) := rfl
    _ = stageMapAlg 0 n (Nat.zero_le n)
        (stageZeroMatrixEquiv.symm
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x)) :=
      congrArg (stageMapAlg 0 n (Nat.zero_le n)) hbase

/-- Differentiating each matrix coefficient of the initial-stage time
Kosmann operator recovers the curved spin curvature, with the sign fixed by
`R(∂t,∂x) = -∂x A_t`. -/
theorem stageZero_kosmannCoefficient_curvature_entries (x : ℝ) :
    ∀ i j : Fin 2,
      -(deriv (fun y =>
        stageZeroMatrixEquiv (kosmannStageElem y (1, 0) 0) i j) x) =
          spinCurvature x i j := by
  intro i j
  have hfun : (fun y =>
      stageZeroMatrixEquiv (kosmannStageElem y (1, 0) 0) i j) =
      fun y => spinConnection y (1, 0) i j := by
    funext y
    rw [show kosmannStageElem y (1, 0) 0 = kosmannBaseElem y (1, 0) by
      simp [kosmannStageElem, stageMapAlg_refl]]
    exact congrArg (fun A : Mat2 => A i j)
      (stageZero_kosmannBaseElem_eq_spinConnection y (1, 0))
  rw [hfun, spinCurvature_eq]
  fin_cases i <;> fin_cases j <;>
    simp [spinConnection_eq_lapseDerivative, deriv_lapse,
      Matrix.smul_apply, InfoGeometry.Clifford.Cl11Matrix.J1]

/-- At every finite stage of the real tensor tower, differentiating the
time-Kosmann coefficient in the spatial chart direction recovers the
transported spin curvature. The derivative is taken coefficientwise on the
finite matrix stage; the right side is the image of the existing curvature
coefficient under the tower bonding map. -/
theorem kosmannStageElem_curvature_entries (x : ℝ) (n : ℕ) :
    ∀ i j : Idx (n + 1),
      -(deriv (fun y => kosmannStageElem y (1, 0) n i j) x) =
        (stageMapAlg 0 n (Nat.zero_le n)
          (stageZeroMatrixEquiv.symm
            (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x))) i j := by
  intro i j
  have hfun : (fun y => kosmannStageElem y (1, 0) n i j) =
      fun y => (-y) * etaElem n i j := by
    funext y
    rw [kosmannStageElem_time_eq_etaElem]
    simp [Matrix.smul_apply]
  have hd : HasDerivAt
      (fun y : ℝ => (-y) * etaElem n i j) (-(etaElem n i j)) x := by
    convert ((hasDerivAt_id x).neg).mul_const (etaElem n i j) using 1 <;> simp
  have hcurv : stageMapAlg 0 n (Nat.zero_le n)
      (stageZeroMatrixEquiv.symm
        (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x)) =
      etaElem n := by
    have h := kosmannStageElem_curvatureLift x n
    rw [kosmannStageElem_time_eq_etaElem] at h
    norm_num at h
    exact h.symm
  rw [hcurv, hfun, hd.deriv]
  simp

/-- Left multiplication by the curved Kosmann coefficient is a natural
endomorphism of the existing real matrix-stage diagram. -/
def kosmannNat (x : ℝ) (v : Tangent) : moduleDiagram ⟶ moduleDiagram where
  app n := ModuleCat.ofHom (leftMul (kosmannStageElem x v n))
  naturality := by
    intro m n f
    ext z
    change Stage m at z
    dsimp [moduleDiagram, leftMul] at z ⊢
    change kosmannStageElem x v n *
        stageMapAlg m n (leOfHom f) z =
      stageMapAlg m n (leOfHom f) (kosmannStageElem x v m * z)
    rw [show kosmannStageElem x v n =
        stageMapAlg m n (leOfHom f) (kosmannStageElem x v m) by
          change stageMapAlg 0 n (Nat.zero_le n) (kosmannBaseElem x v) =
            stageMapAlg m n (leOfHom f)
              (stageMapAlg 0 m (Nat.zero_le m) (kosmannBaseElem x v))
          exact (stageMapAlg_apply_trans 0 m n (Nat.zero_le m)
            (leOfHom f) (kosmannBaseElem x v))]
    exact (stageMapAlg m n (leOfHom f)).map_mul _ _ |>.symm

/-- The induced operator on the native Hestenes--Krein filtered colimit. -/
def kosmannColimitEnd (x : ℝ) (v : Tangent) : Module.End ℝ ColimitCarrier :=
  (colim.map (kosmannNat x v)).hom

/-- On every finite-stage representative, the induced colimit operator reads
back as left multiplication by the transported curved Kosmann coefficient. -/
theorem kosmannColimitEnd_on_stage (x : ℝ) (v : Tangent)
    (n : ℕ) (z : Stage n) :
    kosmannColimitEnd x v ((colimit.ι moduleDiagram n).hom z) =
      (colimit.ι moduleDiagram n).hom (kosmannStageElem x v n * z) := by
  have h := colimit.ι_map (kosmannNat x v) n
  exact congrArg (fun f => f z) h

/-- The existing algebra transition restricted to the primitive spinor
sectors. -/
def spinorStageMap (m n : ℕ) (h : m ≤ n) :
    SpinorStage m →ₗ[ℝ] SpinorStage n where
  toFun a := by
    refine ⟨stageMapAlg m n h a.1, ?_⟩
    change stageMapAlg m n h a.1 * fMinusElem n = stageMapAlg m n h a.1
    calc
      stageMapAlg m n h a.1 * fMinusElem n =
          stageMapAlg m n h a.1 * stageMapAlg m n h (fMinusElem m) := by
            rw [stageMap_fMinusElem h]
      _ = stageMapAlg m n h (a.1 * fMinusElem m) :=
            ((stageMapAlg m n h).map_mul _ _).symm
      _ = stageMapAlg m n h a.1 := by rw [a.2]
  map_add' a b := by
    apply Subtype.ext
    exact (stageMapAlg m n h).map_add a.1 b.1
  map_smul' c a := by
    apply Subtype.ext
    calc
      stageMapAlg m n h (c • a.1) =
          stageMapAlg m n h ((algebraMap ℝ (Stage m) c) * a.1) := by
            rw [Algebra.smul_def]
      _ = stageMapAlg m n h (algebraMap ℝ (Stage m) c) *
          stageMapAlg m n h a.1 := (stageMapAlg m n h).map_mul _ _
      _ = (algebraMap ℝ (Stage n) c) * stageMapAlg m n h a.1 := by
            rw [(stageMapAlg m n h).commutes]
      _ = c • stageMapAlg m n h a.1 := (Algebra.smul_def c _).symm

/- Every transition in the shifted matrix tower is injective.  This follows
from the already-owned one-step matrix embedding, iterated along the order
proof defining `stageMapAlg`. -/
theorem stageMapAlg_injective (m n : ℕ) (h : m ≤ n) :
    Function.Injective (stageMapAlg m n h) := by
  refine Nat.le_induction (m := m)
    (P := fun k hk => Function.Injective (stageMapAlg m k hk)) ?_ ?_ n h
  · intro a b hab
    simpa [stageMapAlg_refl] using hab
  · intro k hmk ih
    rw [stageMapAlg_succ m k hmk]
    intro a b hab
    apply ih
    apply (stageEmbed (k + 1)).injective
    exact hab

/- The actual transition on the primitive spinor ideal is injective; the
subtype condition does not lose information because its underlying map is an
injective transition of the owned matrix tower. -/
theorem spinorStageMap_injective (m n : ℕ) (h : m ≤ n) :
    Function.Injective (spinorStageMap m n h) := by
  intro a b hab
  apply Subtype.ext
  exact stageMapAlg_injective m n h (congrArg Subtype.val hab)

/-- The coherent primitive spinor ideals form a real module diagram under the
actual Cl(1,1) tensor embeddings. -/
def spinorModuleDiagram : ℕ ⥤ ModuleCat ℝ where
  obj n := ModuleCat.of ℝ (SpinorStage n)
  map {m n} f := ModuleCat.ofHom (spinorStageMap m n (leOfHom f))
  map_id n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change stageMapAlg n n le_rfl a.1 = a.1
    rw [stageMapAlg_refl]
    rfl
  map_comp {m n k} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact stageMapAlg_apply_trans m n k (leOfHom f) (leOfHom g) a.1

/- The canonical map from any finite spinor stage into the actual filtered
colimit is injective. The proof uses the existing injective tensor-stage
bonding maps and exactness of filtered colimits in `ModuleCat ℝ`; hence a
nonzero finite-stage spinor cannot disappear in the colimit. -/
set_option linter.style.haveILetI false in
theorem spinorColimit_inclusion_injective (n : ℕ) :
    Function.Injective ((colimit.ι spinorModuleDiagram n).hom) := by
  have hmaps : ∀ (i j : ℕ) (f : i ⟶ j), Mono (spinorModuleDiagram.map f) := by
    intro i j f
    rw [ModuleCat.mono_iff_injective]
    exact spinorStageMap_injective i j (leOfHom f)
  letI : ∀ (i j : ℕ) (f : i ⟶ j), Mono (spinorModuleDiagram.map f) := hmaps
  have hmono : Mono (colimit.ι spinorModuleDiagram n) :=
    (colimit.isColimit spinorModuleDiagram).mono_ι_app_of_isFiltered n
  exact (ModuleCat.mono_iff_injective _).mp hmono

/-- The nonzero curvature action on the constant real spinor `(1, 0)` remains
nonzero after passing into the actual categorical spinor colimit. This uses
the local curved-bundle curvature theorem, the stage-zero Riesz spinor
equivalence, and injectivity of the colimit inclusion; it is not just a
finite-stage coefficient statement. -/
theorem curvedSpinorCurvature_survives_colimit (p :
    InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.Base) :
    (colimit.ι spinorModuleDiagram 0).hom
      (stageZeroSpinorRieszEquiv.symm
        (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
              (fun q => InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
                (fun _ : InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.Base => (![1, 0] : Vec))
                q (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spaceTranslationTangent q))
              p (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.timeTranslationTangent p) -
            InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
              (fun q => InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
                (fun _ : InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.Base => (![1, 0] : Vec))
                q (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.timeTranslationTangent q))
              p (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spaceTranslationTangent p)))) ≠ 0 := by
  let curvatureValue :=
    InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
        (fun q => InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
          (fun _ : InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.Base => (![1, 0] : Vec))
          q (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spaceTranslationTangent q))
        p (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.timeTranslationTangent p) -
      InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
        (fun q => InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
          (fun _ : InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.Base => (![1, 0] : Vec))
          q (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.timeTranslationTangent q))
        p (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spaceTranslationTangent p)
  have hcurvature : curvatureValue ≠ 0 :=
    InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection_curvature_nonzero p
  have hcolumnZero :
      InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement (0 : Vec) = 0 := by
    apply Subtype.ext
    dsimp [InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement]
    apply InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.injective
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hcolumn :
      InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement curvatureValue ≠ 0 := by
    intro h
    have heq := h.trans hcolumnZero.symm
    exact hcurvature
      (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement_injective heq)
  have hstage :
      stageZeroSpinorRieszEquiv.symm
        (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement curvatureValue) ≠ 0 := by
    intro h
    apply hcolumn
    have h' :
        stageZeroSpinorRieszEquiv.symm
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement curvatureValue) =
          stageZeroSpinorRieszEquiv.symm 0 := by
      simpa using h
    exact stageZeroSpinorRieszEquiv.symm.injective h'
  intro hzero
  apply hstage
  apply spinorColimit_inclusion_injective 0
  calc
    ((colimit.ι spinorModuleDiagram 0).hom)
        (stageZeroSpinorRieszEquiv.symm
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement curvatureValue)) = 0 := hzero
    _ = ((colimit.ι spinorModuleDiagram 0).hom) 0 := by rw [map_zero]

/-- Left multiplication by a transported Kosmann coefficient, restricted to
the coherent primitive spinor ideal at stage `n`. -/
def kosmannSpinorAction (x : ℝ) (v : Tangent) (n : ℕ) :
    Module.End ℝ (SpinorStage n) where
  toFun a := by
    refine ⟨kosmannStageElem x v n * a.1, ?_⟩
    change (kosmannStageElem x v n * a.1) * fMinusElem n =
      kosmannStageElem x v n * a.1
    rw [mul_assoc, a.2]
  map_add' a b := by
    apply Subtype.ext
    exact mul_add _ _ _
  map_smul' c a := by
    apply Subtype.ext
    calc
      kosmannStageElem x v n * (c • a.1) =
          kosmannStageElem x v n * ((algebraMap ℝ (Stage n) c) * a.1) := by
            rw [Algebra.smul_def]
      _ = algebraMap ℝ (Stage n) c *
          (kosmannStageElem x v n * a.1) := by
            calc
              _ = (kosmannStageElem x v n * algebraMap ℝ (Stage n) c) * a.1 := by
                    rw [mul_assoc]
              _ = (algebraMap ℝ (Stage n) c * kosmannStageElem x v n) * a.1 := by
                    rw [Algebra.commutes]
              _ = _ := by rw [mul_assoc]
      _ = c • (kosmannStageElem x v n * a.1) := (Algebra.smul_def c _).symm

/-- On the initial spinor sector, the tower action is transported to the
curved real Kosmann action on the same Riesz left ideal. -/
theorem kosmannSpinorAction_stageZero_intertwinesRiesz
    (x : ℝ) (v : Tangent) (a : SpinorStage 0) :
    stageZeroSpinorRieszEquiv (kosmannSpinorAction x v 0 a) =
      ⟨InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm (spinConnection x v) *
          (stageZeroSpinorRieszEquiv a).1,
        (InfoGeometry.Clifford.LipschitzWittRieszPrimary.mem_rieszLeftIdeal_iff_mul_eq
          spinorIdempotent_idempotent _).2 (by
            have ha :=
              (InfoGeometry.Clifford.LipschitzWittRieszPrimary.mem_rieszLeftIdeal_iff_mul_eq
                spinorIdempotent_idempotent (stageZeroSpinorRieszEquiv a).1).mp
                (stageZeroSpinorRieszEquiv a).2
            rw [mul_assoc, ha])⟩ := by
  apply Subtype.ext
  change stageZeroCliffordEquiv
      (kosmannStageElem x v 0 * a.1) =
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm (spinConnection x v) *
      stageZeroCliffordEquiv a.1
  rw [show kosmannStageElem x v 0 = kosmannBaseElem x v by
    simp [kosmannStageElem, stageMapAlg_refl]]
  rw [map_mul, stageZeroCliffordEquiv_kosmannBaseElem]

/-- The actual curved bundle-curvature action on a `C²` real spinor section
agrees with the tower action after transporting its value through the existing
Riesz ideal and stage-zero equivalences. The section's derivatives enter the
curvature computation; the resulting operator is the local spin-curvature
coefficient, not an assertion that the whole covariant derivative is induced
from a colimit. -/
theorem curvedBundleCurvature_matches_stageZeroTower_action
    (σ : InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.Base → Vec)
    (p : InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.Base)
    (hσ : ContDiffAt ℝ 2 σ p) :
    stageZeroSpinorRieszEquiv
        (kosmannSpinorAction (-1) (1, 0) 0
          (stageZeroSpinorRieszEquiv.symm
            (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement (σ p)))) =
      InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement
        (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
            (fun q => InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
              σ q (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spaceTranslationTangent q)) p
            (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.timeTranslationTangent p) -
          InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
            (fun q => InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
              σ q (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.timeTranslationTangent q)) p
            (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spaceTranslationTangent p)) := by
  rw [InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection_curvature
    σ p hσ]
  rw [kosmannSpinorAction_stageZero_intertwinesRiesz]
  apply Subtype.ext
  change InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm
      (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinConnection (-1) (1, 0)) *
        (stageZeroSpinorRieszEquiv
            (stageZeroSpinorRieszEquiv.symm
            (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement (σ p)))).1 =
      (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement
        ((InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature (p 1)).mulVec (σ p))).1
  rw [stageZeroSpinorRieszEquiv.apply_symm_apply]
  rw [← InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.cl11_spinConnection_leftIdeal_action]
  congr 1
  simp [InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature_eq,
    InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinConnection_eq_lapseDerivative,
    InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.deriv_lapse,
    InfoGeometry.Clifford.Cl11Matrix.J1]

/-- The curved Kosmann operators are natural on the primitive spinor-ideal
diagram, not merely on the ambient matrix regular modules. -/
def kosmannSpinorNat (x : ℝ) (v : Tangent) :
    spinorModuleDiagram ⟶ spinorModuleDiagram where
  app n := ModuleCat.ofHom (kosmannSpinorAction x v n)
  naturality := by
    intro m n f
    ext a
    apply Subtype.ext
    change kosmannStageElem x v n *
        stageMapAlg m n (leOfHom f) a.1 =
      stageMapAlg m n (leOfHom f) (kosmannStageElem x v m * a.1)
    rw [show kosmannStageElem x v n =
        stageMapAlg m n (leOfHom f) (kosmannStageElem x v m) by
          change stageMapAlg 0 n (Nat.zero_le n) (kosmannBaseElem x v) =
            stageMapAlg m n (leOfHom f)
              (stageMapAlg 0 m (Nat.zero_le m) (kosmannBaseElem x v))
          exact stageMapAlg_apply_trans 0 m n (Nat.zero_le m)
            (leOfHom f) (kosmannBaseElem x v)]
    exact (stageMapAlg m n (leOfHom f)).map_mul _ _ |>.symm

/-- Colimit carrier of the actual two-sheet spinor sectors. -/
abbrev SpinorColimit := colimit spinorModuleDiagram

/-- The existing real spinor column, transported through its Riesz left
ideal and the maintained stage-zero equivalence, then into the actual
spinor-sector colimit. -/
noncomputable def spinorColumnStageZeroEquiv :
    Vec ≃ₗ[ℝ] SpinorStage 0 :=
  (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnLinearEquiv).trans
    stageZeroSpinorRieszEquiv.symm

/-- Canonical representation of a real two-spinor column in the actual
filtered spinor colimit. -/
noncomputable def spinorColumnColimitMap : Vec →ₗ[ℝ] SpinorColimit :=
  (colimit.ι spinorModuleDiagram 0).hom.comp
    spinorColumnStageZeroEquiv.toLinearMap

/-- The stage-zero equivalence reads back to the owner's Riesz column map. -/
@[simp] theorem spinorColumnStageZeroEquiv_apply (ψ : Vec) :
    stageZeroSpinorRieszEquiv (spinorColumnStageZeroEquiv ψ) =
      InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement ψ := by
  simp [spinorColumnStageZeroEquiv]

/-- Curved Kosmann endomorphism on the colimit of the primitive spinor
sectors. -/
def kosmannSpinorColimitEnd (x : ℝ) (v : Tangent) :
    Module.End ℝ SpinorColimit :=
  (colim.map (kosmannSpinorNat x v)).hom

/-- Exact stage readback for the Kosmann action on the spinor-ideal colimit. -/
theorem kosmannSpinorColimitEnd_on_stage (x : ℝ) (v : Tangent)
    (n : ℕ) (a : SpinorStage n) :
    kosmannSpinorColimitEnd x v ((colimit.ι spinorModuleDiagram n).hom a) =
      (colimit.ι spinorModuleDiagram n).hom (kosmannSpinorAction x v n a) := by
  have h := colimit.ι_map (kosmannSpinorNat x v) n
  exact congrArg (fun f => f a) h

/-- The connection coefficient on the actual spinor colimit acts on the
canonical real column exactly as the curved chart's real Kosmann matrix.
This uses the established tower/Riesz intertwiner and the general matrix
left-action theorem, so the statement is an operator readback on the colimit
carrier rather than only a coefficient equality. -/
theorem kosmannSpinorColimitEnd_spinorColumn (x : ℝ) (v : Tangent)
    (ψ : Vec) :
    kosmannSpinorColimitEnd x v (spinorColumnColimitMap ψ) =
      spinorColumnColimitMap
        ((InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinConnection x v).mulVec ψ) := by
  change kosmannSpinorColimitEnd x v
      ((colimit.ι spinorModuleDiagram 0).hom (spinorColumnStageZeroEquiv ψ)) =
    (colimit.ι spinorModuleDiagram 0).hom
      (spinorColumnStageZeroEquiv
        ((InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinConnection x v).mulVec ψ))
  rw [kosmannSpinorColimitEnd_on_stage]
  congr 1
  apply stageZeroSpinorRieszEquiv.injective
  rw [kosmannSpinorAction_stageZero_intertwinesRiesz]
  apply Subtype.ext
  rw [spinorColumnStageZeroEquiv_apply, spinorColumnStageZeroEquiv_apply]
  exact (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement_matrix_left_action
    (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinConnection x v) ψ).symm

/-- At every finite stage, the induced spinor-colimit operator acts by the
transport of the curved chart's spin-curvature coefficient. This identifies
the same curvature action across the full algebraic tower. -/
theorem curvedSpinorCurvature_colimit_on_stage
    (x : ℝ) (n : ℕ) (a : SpinorStage n) :
    kosmannSpinorColimitEnd (-1) (1, 0)
        ((colimit.ι spinorModuleDiagram n).hom a) =
      (colimit.ι spinorModuleDiagram n).hom
        (⟨stageMapAlg 0 n (Nat.zero_le n)
            (stageZeroMatrixEquiv.symm
              (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x)) * a.1,
          by
            change (stageMapAlg 0 n (Nat.zero_le n)
                (stageZeroMatrixEquiv.symm
                  (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x)) * a.1) *
                fMinusElem n = _
            rw [mul_assoc, a.2]⟩ : SpinorStage n) := by
  have hact : kosmannSpinorAction (-1) (1, 0) n a =
      (⟨stageMapAlg 0 n (Nat.zero_le n)
          (stageZeroMatrixEquiv.symm
            (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x)) * a.1,
        by
          change (stageMapAlg 0 n (Nat.zero_le n)
              (stageZeroMatrixEquiv.symm
                (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x)) * a.1) *
              fMinusElem n = _
          rw [mul_assoc, a.2]⟩ : SpinorStage n) := by
    apply Subtype.ext
    change kosmannStageElem (-1) (1, 0) n * a.1 = _
    rw [kosmannStageElem_curvatureLift]
  rw [kosmannSpinorColimitEnd_on_stage]
  exact congrArg (fun z : SpinorStage n => (colimit.ι spinorModuleDiagram n).hom z) hact

/-- The nonzero curvature seen by the initial real spinor remains nonzero
after transporting that spinor through any finite tensor stage and then into
the spinor colimit.  The proof uses the actual bonding maps twice: first to
transport the spin-curvature action, then injectivity of the colimit
inclusions to prevent the resulting vector from collapsing. -/
theorem curvedSpinorCurvature_survives_every_stage
    (p : InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.Base) (n : ℕ) :
    kosmannSpinorColimitEnd (-1) (1, 0)
        ((colimit.ι spinorModuleDiagram n).hom
          (spinorStageMap 0 n (Nat.zero_le n)
            (stageZeroSpinorRieszEquiv.symm
              (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement
                (![1, 0] : Vec))))) ≠ 0 := by
  let seed : SpinorStage 0 := stageZeroSpinorRieszEquiv.symm
    (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement
      (![1, 0] : Vec))
  let seedN : SpinorStage n := spinorStageMap 0 n (Nat.zero_le n) seed
  let curvatureValue :=
    InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
        (fun q => InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
          (fun _ : InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.Base => (![1, 0] : Vec))
          q (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spaceTranslationTangent q))
        p (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.timeTranslationTangent p) -
      InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
        (fun q => InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
          (fun _ : InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.Base => (![1, 0] : Vec))
          q (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.timeTranslationTangent q))
        p (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spaceTranslationTangent p)
  have hcurvature : curvatureValue ≠ 0 := by
    simpa [curvatureValue] using
      InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection_curvature_nonzero p
  have hcolumn :
      InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement
        curvatureValue ≠ 0 := by
    intro hz
    apply hcurvature
    have hzero :
        InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement (0 : Vec) = 0 := by
      apply Subtype.ext
      dsimp [InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement]
      apply InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.injective
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    apply InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement_injective
    exact hz.trans hzero.symm
  have hseedAction : kosmannSpinorAction (-1) (1, 0) 0 seed ≠ 0 := by
    intro hz
    have hmap := congrArg stageZeroSpinorRieszEquiv hz
    rw [map_zero] at hmap
    have hbridge := curvedBundleCurvature_matches_stageZeroTower_action
      (fun _ : InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.Base => (![1, 0] : Vec))
      p (by fun_prop)
    have hcolumnZero :
        InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement
          curvatureValue = 0 := by
      simpa [seed, curvatureValue] using hbridge.symm.trans hmap
    exact hcolumn hcolumnZero
  have htransport :
      spinorStageMap 0 n (Nat.zero_le n)
          (kosmannSpinorAction (-1) (1, 0) 0 seed) =
        kosmannSpinorAction (-1) (1, 0) n seedN := by
    apply Subtype.ext
    change stageMapAlg 0 n (Nat.zero_le n)
        (kosmannBaseElem (-1) (1, 0) * seed.1) =
      stageMapAlg 0 n (Nat.zero_le n) (kosmannBaseElem (-1) (1, 0)) *
        stageMapAlg 0 n (Nat.zero_le n) seed.1
    exact (stageMapAlg 0 n (Nat.zero_le n)).map_mul _ _
  have hstageAction : kosmannSpinorAction (-1) (1, 0) n seedN ≠ 0 := by
    intro hz
    apply hseedAction
    apply spinorStageMap_injective 0 n (Nat.zero_le n)
    rw [htransport, hz]
    exact (map_zero _).symm
  have hcolimitAction :
      (colimit.ι spinorModuleDiagram n).hom
        (kosmannSpinorAction (-1) (1, 0) n seedN) ≠ 0 := by
    intro hz
    apply hstageAction
    apply spinorColimit_inclusion_injective n
    exact hz.trans (map_zero _).symm
  rw [kosmannSpinorColimitEnd_on_stage]
  simpa [seed, seedN] using hcolimitAction

/-- The curved bundle-curvature action is represented in the actual spinor
colimit by the transported stage-zero Kosmann action. The right-hand
representative is the column realization of the bundle curvature, carried
back to the tower's negative-chirality ideal. -/
theorem curvedBundleCurvature_matches_spinorColimit
    (σ : InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.Base → Vec)
    (p : InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.Base)
    (hσ : ContDiffAt ℝ 2 σ p) :
    (colimit.ι spinorModuleDiagram 0).hom
        (kosmannSpinorAction (-1) (1, 0) 0
          (stageZeroSpinorRieszEquiv.symm
            (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement (σ p)))) =
      (colimit.ι spinorModuleDiagram 0).hom
        (stageZeroSpinorRieszEquiv.symm
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement
            (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
                (fun q => InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
                  σ q (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spaceTranslationTangent q)) p
                (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.timeTranslationTangent p) -
              InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
                (fun q => InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
                  σ q (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.timeTranslationTangent q)) p
                (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spaceTranslationTangent p)))) := by
  have h := congrArg stageZeroSpinorRieszEquiv.symm
    (curvedBundleCurvature_matches_stageZeroTower_action σ p hσ)
  have h' : kosmannSpinorAction (-1) (1, 0) 0
      (stageZeroSpinorRieszEquiv.symm
        (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement (σ p))) =
      stageZeroSpinorRieszEquiv.symm
        (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
              (fun q => InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
                σ q (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spaceTranslationTangent q)) p
              (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.timeTranslationTangent p) -
            InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
              (fun q => InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.curvedSpinorBundleConnection
                σ q (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.timeTranslationTangent q)) p
              (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spaceTranslationTangent p))) := by
    simpa using h
  exact congrArg (fun a => (colimit.ι spinorModuleDiagram 0).hom a) h'

/-! ### Two-sheet exchange on the actual curved spinor colimit

The algebra tower already has a colimit-level Peirce exchange.  Restricting
that exchange to the coherent primitive spinor ideals is a separate statement:
it verifies that both sheet projections and their exchange preserve this
curved spinor carrier and its bonding maps. -/

/-- Restriction of the tower's sheet exchange to the primitive spinor ideal. -/
def spinorEtaNat : spinorModuleDiagram ⟶ spinorModuleDiagram where
  app n := ModuleCat.ofHom {
    toFun a := by
      refine ⟨etaElem n * a.1, ?_⟩
      change (etaElem n * a.1) * fMinusElem n = etaElem n * a.1
      rw [mul_assoc, a.2]
    map_add' a b := by
      apply Subtype.ext
      exact mul_add _ _ _
    map_smul' r a := by
      apply Subtype.ext
      change etaElem n * (r • a.1) = r • (etaElem n * a.1)
      simp only [Algebra.smul_def]
      calc
        etaElem n * (algebraMap ℝ (Stage n) r * a.1) =
            (etaElem n * algebraMap ℝ (Stage n) r) * a.1 := by rw [mul_assoc]
        _ = (algebraMap ℝ (Stage n) r * etaElem n) * a.1 := by
          rw [Algebra.commutes]
        _ = algebraMap ℝ (Stage n) r * (etaElem n * a.1) := by rw [mul_assoc]
  }
  naturality := by
    intro m n f
    ext a
    apply Subtype.ext
    change etaElem n * stageMapAlg m n (leOfHom f) a.1 =
      stageMapAlg m n (leOfHom f) (etaElem m * a.1)
    rw [show etaElem n = stageMapAlg m n (leOfHom f) (etaElem m) by
      exact (stageMap_etaElem (leOfHom f)).symm]
    exact (stageMapAlg m n (leOfHom f)).map_mul _ _ |>.symm

/-- The positive Peirce projector acts on each curved spinor ideal. -/
def spinorFPlusNat : spinorModuleDiagram ⟶ spinorModuleDiagram where
  app n := ModuleCat.ofHom {
    toFun a := by
      refine ⟨fPlusElem n * a.1, ?_⟩
      change (fPlusElem n * a.1) * fMinusElem n = fPlusElem n * a.1
      rw [mul_assoc, a.2]
    map_add' a b := by
      apply Subtype.ext
      exact mul_add _ _ _
    map_smul' r a := by
      apply Subtype.ext
      change fPlusElem n * (r • a.1) = r • (fPlusElem n * a.1)
      simp only [Algebra.smul_def]
      calc
        fPlusElem n * (algebraMap ℝ (Stage n) r * a.1) =
            (fPlusElem n * algebraMap ℝ (Stage n) r) * a.1 := by rw [mul_assoc]
        _ = (algebraMap ℝ (Stage n) r * fPlusElem n) * a.1 := by
          rw [Algebra.commutes]
        _ = algebraMap ℝ (Stage n) r * (fPlusElem n * a.1) := by rw [mul_assoc]
  }
  naturality := by
    intro m n f
    ext a
    apply Subtype.ext
    change fPlusElem n * stageMapAlg m n (leOfHom f) a.1 =
      stageMapAlg m n (leOfHom f) (fPlusElem m * a.1)
    rw [show fPlusElem n = stageMapAlg m n (leOfHom f) (fPlusElem m) by
      exact (stageMap_fPlusElem (leOfHom f)).symm]
    exact (stageMapAlg m n (leOfHom f)).map_mul _ _ |>.symm

/-- The negative Peirce projector acts on each curved spinor ideal. -/
def spinorFMinusNat : spinorModuleDiagram ⟶ spinorModuleDiagram where
  app n := ModuleCat.ofHom {
    toFun a := by
      refine ⟨fMinusElem n * a.1, ?_⟩
      change (fMinusElem n * a.1) * fMinusElem n = fMinusElem n * a.1
      rw [mul_assoc, a.2]
    map_add' a b := by
      apply Subtype.ext
      exact mul_add _ _ _
    map_smul' r a := by
      apply Subtype.ext
      change fMinusElem n * (r • a.1) = r • (fMinusElem n * a.1)
      simp only [Algebra.smul_def]
      calc
        fMinusElem n * (algebraMap ℝ (Stage n) r * a.1) =
            (fMinusElem n * algebraMap ℝ (Stage n) r) * a.1 := by rw [mul_assoc]
        _ = (algebraMap ℝ (Stage n) r * fMinusElem n) * a.1 := by
          rw [Algebra.commutes]
        _ = algebraMap ℝ (Stage n) r * (fMinusElem n * a.1) := by rw [mul_assoc]
  }
  naturality := by
    intro m n f
    ext a
    apply Subtype.ext
    change fMinusElem n * stageMapAlg m n (leOfHom f) a.1 =
      stageMapAlg m n (leOfHom f) (fMinusElem m * a.1)
    rw [show fMinusElem n = stageMapAlg m n (leOfHom f) (fMinusElem m) by
      exact (stageMap_fMinusElem (leOfHom f)).symm]
    exact (stageMapAlg m n (leOfHom f)).map_mul _ _ |>.symm

/-- Curved sheet exchange on the colimit of the primitive spinor ideals. -/
def spinorColimitEta : Module.End ℝ SpinorColimit :=
  (colim.map spinorEtaNat).hom

/-- At the chart normalization where the local spin curvature equals the
time-Kosmann generator, that generator on the primitive spinor ideal is
exactly the existing Peirce sheet exchange.  This identifies the curved
geometric operator with the tower's maintained two-sheet operator before
passing to the colimit. -/
theorem kosmannSpinorNat_curvature_eq_sheetExchange :
    kosmannSpinorNat (-1) (1, 0) = spinorEtaNat := by
  apply NatTrans.ext
  funext n
  apply ModuleCat.hom_ext
  ext a
  apply Subtype.ext
  change kosmannStageElem (-1) (1, 0) n * a.1 = etaElem n * a.1
  rw [kosmannStageElem_time_eq_etaElem]
  norm_num

/-- Positive Peirce projection on the primitive spinor-ideal colimit. -/
def spinorColimitFPlus : Module.End ℝ SpinorColimit :=
  (colim.map spinorFPlusNat).hom

/-- Negative Peirce projection on the primitive spinor-ideal colimit. -/
def spinorColimitFMinus : Module.End ℝ SpinorColimit :=
  (colim.map spinorFMinusNat).hom

/-- The local curved spin-curvature operator, induced on the actual
categorical spinor colimit, is the tower's involutive forward/backward sheet
exchange. The equality transports the finite-frame curvature normalization
through the already-owned natural transformation and colimit maps. -/
theorem kosmannSpinorColimitEnd_curvature_eq_sheetExchange :
    kosmannSpinorColimitEnd (-1) (1, 0) = spinorColimitEta := by
  change (colim.map (kosmannSpinorNat (-1) (1, 0))).hom =
    (colim.map spinorEtaNat).hom
  rw [kosmannSpinorNat_curvature_eq_sheetExchange]

/-- On the embedded initial real spinor fiber, the curved spin-curvature
operator in the categorical colimit acts by exchanging the two real
components.  This is the same action as `modular_j` on
`DoubledSpace ℝ`, transported through the actual stage-zero Riesz ideal and
the colimit inclusion. -/
theorem kosmannSpinorColimitEnd_curvature_modularFlip (a b : ℝ) :
    kosmannSpinorColimitEnd (-1) (1, 0)
        ((colimit.ι spinorModuleDiagram 0).hom
          (stageZeroSpinorRieszEquiv.symm
            (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement
              (![a, b] : Vec)))) =
      (colimit.ι spinorModuleDiagram 0).hom
        (stageZeroSpinorRieszEquiv.symm
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement
            (![b, a] : Vec))) := by
  rw [kosmannSpinorColimitEnd_on_stage]
  apply congrArg (fun z : SpinorStage 0 =>
    (colimit.ι spinorModuleDiagram 0).hom z)
  apply stageZeroSpinorRieszEquiv.injective
  rw [kosmannSpinorAction_stageZero_intertwinesRiesz]
  apply Subtype.ext
  simp only [stageZeroSpinorRieszEquiv.apply_symm_apply]
  rw [← InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.cl11_spinConnection_leftIdeal_action]
  apply InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.injective
  simp [InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinorColumnElement,
    InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinConnection_eq_lapseDerivative,
    InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.deriv_lapse,
    InfoGeometry.Clifford.Cl11Matrix.J1, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

/-- The restricted exchange is still an involution on the spinor colimit. -/
theorem spinorColimitEta_sq :
    spinorColimitEta * spinorColimitEta =
      (LinearMap.id : Module.End ℝ SpinorColimit) := by
  have hη : spinorEtaNat ≫ spinorEtaNat = 𝟙 spinorModuleDiagram := by
    ext n a
    apply Subtype.ext
    change etaElem n * (etaElem n * a.1) = a.1
    rw [← mul_assoc, etaElem_sq, one_mul]
  have hmap : colim.map spinorEtaNat ≫ colim.map spinorEtaNat =
      𝟙 (colimit spinorModuleDiagram) := by
    rw [← colim.map_comp, hη, colim.map_id]
    rfl
  simpa [spinorColimitEta, Module.End.mul_eq_comp] using
    congrArg ModuleCat.Hom.hom hmap

/-- Stagewise exchange of the two coherent Peirce projectors on the
primitive spinor ideals. -/
theorem spinorEtaNat_fPlusNat_spinorEtaNat_eq_fMinusNat :
    spinorEtaNat ≫ spinorFPlusNat ≫ spinorEtaNat = spinorFMinusNat := by
  ext n a
  apply Subtype.ext
  change etaElem n * (fPlusElem n * (etaElem n * a.1)) =
    fMinusElem n * a.1
  rw [← mul_assoc, ← mul_assoc, etaElem_fPlusElem_etaElem]

/-- The curved tower's sheet exchange conjugates the two Peirce operators on
the colimit of its actual spinor ideal. -/
theorem spinorColimitEta_fPlus_spinorColimitEta_eq_fMinus :
    spinorColimitEta * spinorColimitFPlus * spinorColimitEta =
      spinorColimitFMinus := by
  have hmap : colim.map spinorEtaNat ≫ colim.map spinorFPlusNat ≫
      colim.map spinorEtaNat = colim.map spinorFMinusNat := by
    rw [← colim.map_comp, ← colim.map_comp]
    exact congrArg colim.map spinorEtaNat_fPlusNat_spinorEtaNat_eq_fMinusNat
  simpa [spinorColimitEta, spinorColimitFPlus, spinorColimitFMinus,
    Module.End.mul_eq_comp] using
    congrArg ModuleCat.Hom.hom hmap

/-- At every finite stage, the time-direction Kosmann coefficient acts as
the real multiple `-x` of the coherent Hestenes sheet exchange. -/
theorem kosmannSpinorStage_time_conjugates_fPlus (x : ℝ) (n : ℕ) :
    kosmannStageElem x (1, 0) n * fPlusElem n *
        kosmannStageElem x (1, 0) n =
      x ^ 2 • fMinusElem n := by
  rw [kosmannStageElem_time_eq_etaElem]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [smul_smul]
  calc
    ((-x) * (-x)) • (etaElem n * fPlusElem n * etaElem n) =
        x ^ 2 • (etaElem n * fPlusElem n * etaElem n) := by
          rw [show (-x) * (-x) = x ^ 2 by
            calc
              (-x) * (-x) = x * x := neg_mul_neg x x
              _ = x ^ 2 := by rw [pow_two]]
    _ = x ^ 2 • fMinusElem n := by
      rw [etaElem_fPlusElem_etaElem]

/-- The curved time-Kosmann natural transformation exchanges the positive
Peirce action with the negative Peirce action, with the expected square of
its real coefficient. This is proved on the spinor-ideal carrier itself. -/
theorem kosmannSpinorNat_time_conjugates_fPlus (x : ℝ) :
    kosmannSpinorNat x (1, 0) ≫ spinorFPlusNat ≫ kosmannSpinorNat x (1, 0) =
      (x ^ 2) • spinorFMinusNat := by
  apply NatTrans.ext
  funext n
  apply ModuleCat.hom_ext
  ext a
  apply Subtype.ext
  change kosmannStageElem x (1, 0) n *
      (fPlusElem n * (kosmannStageElem x (1, 0) n * a.1)) =
    x ^ 2 • (fMinusElem n * a.1)
  calc
    kosmannStageElem x (1, 0) n *
        (fPlusElem n * (kosmannStageElem x (1, 0) n * a.1)) =
      (kosmannStageElem x (1, 0) n * fPlusElem n *
        kosmannStageElem x (1, 0) n) * a.1 := by noncomm_ring
    _ = (x ^ 2 • fMinusElem n) * a.1 := by
      rw [kosmannSpinorStage_time_conjugates_fPlus]
    _ = x ^ 2 • (fMinusElem n * a.1) := by rw [Matrix.smul_mul]

/-- The curved Kosmann action and its Peirce exchange law descend together
through the actual categorical spinor-ideal colimit. The right side is kept
as the image of the scaled stage transformation; this avoids assuming the
colimit functor is linear on natural transformations. -/
theorem kosmannSpinorColimit_time_conjugates_fPlus (x : ℝ) :
    kosmannSpinorColimitEnd x (1, 0) * spinorColimitFPlus *
        kosmannSpinorColimitEnd x (1, 0) =
      (colim.map ((x ^ 2) • spinorFMinusNat)).hom := by
  have hmap : colim.map (kosmannSpinorNat x (1, 0)) ≫
      colim.map spinorFPlusNat ≫ colim.map (kosmannSpinorNat x (1, 0)) =
      colim.map ((x ^ 2) • spinorFMinusNat) := by
    rw [← colim.map_comp, ← colim.map_comp]
    exact congrArg colim.map (kosmannSpinorNat_time_conjugates_fPlus x)
  simpa [kosmannSpinorColimitEnd, spinorColimitFPlus,
    Module.End.mul_eq_comp] using congrArg ModuleCat.Hom.hom hmap

/-! ## Curved spin transport on the native real Krein double -/

/-- In the real doubled carrier, the curved `Cl(1,1)` spin connection acts by
the established modular sheet swap, scaled by its geometric connection
coefficient. The coordinates are the two real spinor components; the scalar
is the actual lapse-derivative coefficient from the curved-frame owner. -/
theorem spinConnection_doubled_action (x : ℝ) (v : Tangent) (a b : ℝ) :
    InfoGeometry.Krein.to_doubled
        ((spinConnection x v).mulVec (![a, b] : Vec) 0)
        ((spinConnection x v).mulVec (![a, b] : Vec) 1) =
      (-((deriv lapse x * v.1) / 2)) •
        InfoGeometry.Krein.modular_j
          (InfoGeometry.Krein.to_doubled a b : InfoGeometry.Krein.DoubledSpace ℝ) := by
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    simp [spinConnection_eq_lapseDerivative, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, InfoGeometry.Clifford.Cl11Matrix.J1]

/-- The curved spin connection is infinitesimally skew for the native
Dirac-conjugated Krein pairing on `DoubledSpace ℝ`. Thus its forward/backward
spinor transport preserves the indefinite two-sheet pairing. -/
theorem spinConnection_krein_pairing_skew (x : ℝ) (v : Tangent)
    (a b c d : ℝ) :
    InfoGeometry.Krein.KreinSpace.kreinInner
        (InfoGeometry.Krein.to_doubled
          ((spinConnection x v).mulVec (![a, b] : Vec) 0)
          ((spinConnection x v).mulVec (![a, b] : Vec) 1))
        (InfoGeometry.Krein.to_doubled c d) +
      InfoGeometry.Krein.KreinSpace.kreinInner
        (InfoGeometry.Krein.to_doubled a b)
        (InfoGeometry.Krein.to_doubled
          ((spinConnection x v).mulVec (![c, d] : Vec) 0)
          ((spinConnection x v).mulVec (![c, d] : Vec) 1)) = 0 := by
  let α : ℝ := -((deriv lapse x * v.1) / 2)
  rw [spinConnection_doubled_action, spinConnection_doubled_action]
  change InfoGeometry.Krein.KreinSpace.kreinInner
        (α • InfoGeometry.Krein.modular_j
          (InfoGeometry.Krein.to_doubled a b : InfoGeometry.Krein.DoubledSpace ℝ))
        (InfoGeometry.Krein.to_doubled c d) +
      InfoGeometry.Krein.KreinSpace.kreinInner
        (InfoGeometry.Krein.to_doubled a b)
        (α • InfoGeometry.Krein.modular_j
          (InfoGeometry.Krein.to_doubled c d : InfoGeometry.Krein.DoubledSpace ℝ)) = 0
  rw [InfoGeometry.Krein.KreinSpace.kreinInner_smul_left,
    InfoGeometry.Krein.KreinSpace.kreinInner_smul_right, ← mul_add]
  have hswap := (InfoGeometry.Krein.KreinSpace.isKreinSkewAdjoint_iff
      (InfoGeometry.Krein.modular_j (E := ℝ))).mp
    (InfoGeometry.Krein.isKreinSkewAdjoint_modular_j (E := ℝ))
      (InfoGeometry.Krein.to_doubled a b) (InfoGeometry.Krein.to_doubled c d)
  rw [hswap, mul_zero]

/-- On a pure positive-sheet input, the curved spin generator lands in the
negative sheet. This records the polarization exchange caused by the real
Clifford boost generator; it does not identify the connection with a
positive-sheet-preserving flow. -/
theorem spinConnection_maps_positive_axis_to_negative
    (x : ℝ) (v : Tangent) (a : ℝ) :
    InfoGeometry.Krein.to_doubled
        ((spinConnection x v).mulVec (![a, 0] : Vec) 0)
        ((spinConnection x v).mulVec (![a, 0] : Vec) 1) ∈
      InfoGeometry.Krein.KreinSpace.negSubspace
        (InfoGeometry.Krein.DoubledSpace ℝ) := by
  rw [InfoGeometry.Krein.KreinSpace.mem_negSubspace_iff]
  change InfoGeometry.Krein.KreinSpace.jCLM
      (InfoGeometry.Krein.to_doubled
        ((spinConnection x v).mulVec (![a, 0] : Vec) 0)
        ((spinConnection x v).mulVec (![a, 0] : Vec) 1)) = _
  rw [InfoGeometry.Krein.jCLM_eq_spectral_epsilon]
  rw [spinConnection_doubled_action]
  rw [map_smul, InfoGeometry.Krein.modular_j_to_doubled,
    InfoGeometry.Krein.spectral_epsilon_to_doubled]
  simp [InfoGeometry.Krein.to_doubled]
  rw [show ((0 : ℝ), -a) = -((0 : ℝ), a) by simp,
    WithLp.toLp_neg]
  simp

/-- The curved chart's spin-curvature coefficient is the time-Kosmann
generator at the base point `x = -1`; this normalization makes its action the
same Krein-skew sheet swap as the connection. -/
theorem spinCurvature_eq_baseSpinConnection (x : ℝ) :
    spinCurvature x = spinConnection (-1) (1, 0) := by
  rw [spinCurvature_eq, spinConnection_eq_lapseDerivative, deriv_lapse]
  norm_num

/-- Consequently the curved spin-curvature action itself is Krein-skew on
the real doubled spinor carrier. -/
theorem spinCurvature_krein_pairing_skew (x : ℝ) (a b c d : ℝ) :
    InfoGeometry.Krein.KreinSpace.kreinInner
        (InfoGeometry.Krein.to_doubled
          ((spinCurvature x).mulVec (![a, b] : Vec) 0)
          ((spinCurvature x).mulVec (![a, b] : Vec) 1))
        (InfoGeometry.Krein.to_doubled c d) +
      InfoGeometry.Krein.KreinSpace.kreinInner
        (InfoGeometry.Krein.to_doubled a b)
        (InfoGeometry.Krein.to_doubled
          ((spinCurvature x).mulVec (![c, d] : Vec) 0)
          ((spinCurvature x).mulVec (![c, d] : Vec) 1)) = 0 := by
  rw [spinCurvature_eq_baseSpinConnection]
  exact spinConnection_krein_pairing_skew (-1) (1, 0) a b c d

/-- In the real doubled representation already owned by
`DoubledSpaceMatrixClockBridge`, the curved spin-curvature matrix is exactly
the modular sheet-swap generator. This identifies the actual curvature
operator on the two-sheet carrier, rather than comparing two unnamed matrix
patterns. -/
theorem spinCurvature_doubledEnd (x : ℝ) :
    InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := ℝ)
        (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x) =
      InfoGeometry.Krein.modular_j (E := ℝ) := by
  rw [InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature_eq]
  have hJ : InfoGeometry.Clifford.Cl11Matrix.J1 =
      InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.matrixJ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.Clifford.Cl11Matrix.J1,
        InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.matrixJ]
  rw [map_smul, hJ, one_smul]
  exact InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock_matrixJ

/-- The curved spin-curvature endomorphism is a generator of the native real
doubled symplectic form. This follows from its proved matrix action and the
existing Souriau modular-swap generator theorem. -/
theorem spinCurvature_isSymplecticGenerator (x : ℝ) :
    InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.IsSymplecticGenerator
      (InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := ℝ)
        (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x)) := by
  rw [spinCurvature_doubledEnd]
  exact InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.modularSwap_isSymplecticGenerator

/-- The Souriau quadratic moment Hessian of the curved spin-curvature action
is the negative of the real Krein pairing on the doubled spinor carrier.
Consequently this curvature Hessian is indefinite on the full carrier, as
required by the existing negative/positive sheet decomposition. -/
theorem spinCurvature_souriauHessian_eq_neg_kreinPairing
    (x : ℝ) (z u v : InfoGeometry.Krein.DoubledSpace ℝ) :
    (fderiv ℝ (fderiv ℝ
      (InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.quadraticMoment
        (InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := ℝ)
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x)))) z) u v =
      -InfoGeometry.Krein.hessian_indefinite_form u v := by
  rw [spinCurvature_doubledEnd]
  exact InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.hessian_quadraticMoment_modularSwap_eq_neg_kreinPairing
    z u v

/-- The Hessian of this curved spin-curvature Hamiltonian is not positive on
the full doubled carrier. This rules out identifying it with a positive BKM
metric on all doubled directions; any statistical comparison must first name
and prove a positive polarization/tangent restriction. -/
theorem spinCurvature_souriauHessian_not_positiveSemidefinite (x : ℝ) :
    ¬ ∀ z u : InfoGeometry.Krein.DoubledSpace ℝ,
      0 ≤ (fderiv ℝ (fderiv ℝ
        (InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.quadraticMoment
          (InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := ℝ)
            (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x)))) z) u u := by
  rw [spinCurvature_doubledEnd]
  exact InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.modularSwap_quadraticMoment_hessian_not_positiveSemidefinite

/-- The curved spin-curvature Souriau Hessian, restricted to the positive
second polarization of the real doubled spinor carrier, is the ordinary real
Hilbert inner product. This is the precise positive-sector statement available
from the existing Krein polarization; it does not identify the full Hessian
with a positive BKM metric. -/
theorem spinCurvature_souriauHessian_secondSheet_bilinear
    (x : ℝ) (z : InfoGeometry.Krein.DoubledSpace ℝ) (xi eta : ℝ) :
    (fderiv ℝ (fderiv ℝ
      (InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.quadraticMoment
        (InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := ℝ)
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x)))) z)
        (WithLp.toLp (2 : ENNReal) (0, xi))
        (WithLp.toLp (2 : ENNReal) (0, eta)) = inner ℝ xi eta := by
  rw [spinCurvature_doubledEnd]
  exact InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.hessian_quadraticMoment_modularSwap_secondSheet_bilinear
    (E := ℝ) z xi eta

/-- Pairing the curved spin-curvature direction with any real doubled
symplectic generator in Souriau's reversible form is exactly the algebraic
KKS form of the same state-evaluation functional. -/
theorem spinCurvature_reversibleForm_eq_kks
    (x : ℝ) (z : InfoGeometry.Krein.DoubledSpace ℝ)
    (A : InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.SymplecticGenerators
      (E := ℝ)) :
    InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.souriauReversibleForm
        z ⟨InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := ℝ)
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x),
          spinCurvature_isSymplecticGenerator x⟩ A =
      SouriauKKS.kksForm
        (InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.quadraticMomentFunctional z)
        (InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := ℝ)
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x))
        (A : InfoGeometry.Krein.DoubledSpace ℝ →L[ℝ]
          InfoGeometry.Krein.DoubledSpace ℝ) := by
  change InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.quadraticMomentBracket
      (InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := ℝ)
        (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x))
      (A : InfoGeometry.Krein.DoubledSpace ℝ →L[ℝ]
        InfoGeometry.Krein.DoubledSpace ℝ) z = _
  exact InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.quadraticMomentBracket_eq_kksForm
      _ _ (spinCurvature_isSymplecticGenerator x) A.property z

/-- The Souriau Hamiltonian component generated by the curved spin-curvature
operator has the owner's actual symplectic gradient on the real doubled
carrier. This is a local curved-frame statement: it supplies no global
spacetime action or thermal state. -/
theorem hasFDerivAt_spinCurvature_souriauMoment_component
    (x : ℝ) (z : InfoGeometry.Krein.DoubledSpace ℝ) :
    HasFDerivAt
      (fun w => InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.souriauMomentMap
        w ⟨InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := ℝ)
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x),
          spinCurvature_isSymplecticGenerator x⟩)
      (InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.symplecticForm
        ((InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := ℝ)
          (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x)) z)) z := by
  exact InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.hasFDerivAt_souriauMoment_component
    ⟨_, spinCurvature_isSymplecticGenerator x⟩ z

/-- With the curved spin-curvature generator among its entries, the Souriau
reversible 2-form remains Chevalley--Eilenberg closed. This specializes the
existing Jacobi-based closure theorem on the actual real symplectic-generator
Lie algebra. -/
theorem spinCurvature_reversibleForm_cyclic_closed
    (x : ℝ) (z : InfoGeometry.Krein.DoubledSpace ℝ)
    (A B : InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.SymplecticGenerators
      (E := ℝ)) :
    let C : InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.SymplecticGenerators
      (E := ℝ) :=
      ⟨InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := ℝ)
        (InfoGeometry.Geometry.CurvedLorentzianKosmannFrame.spinCurvature x),
        spinCurvature_isSymplecticGenerator x⟩
    InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.souriauReversibleForm z C
        ⁅A, B⁆ +
      InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.souriauReversibleForm z A ⁅B, C⁆ +
      InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.souriauReversibleForm z B ⁅C, A⁆ = 0 := by
  exact InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.souriauReversibleForm_cyclic_closed z
    (⟨_, spinCurvature_isSymplecticGenerator x⟩ :
      InfoGeometry.Canonical.SouriauDoubledQuadraticMomentMap.SymplecticGenerators
        (E := ℝ)) A B

end InfoGeometry.Canonical.CurvedKosmannCl11TowerBridge

end
