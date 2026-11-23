/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.GradedNullconeAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Canonical.Cl11JordanWignerDirectLimit
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Parity-Soldered `Cl(1,1)` Tower to Direct-Limit CAR Bridge

Connects the irreducible five-axiom Kronecker tower `GradedNullconeAlgebra` (`TowerIdx k`,
`towerStepAlgHom k`, `towerGamma k`, `jwPos k`, `jwNeg k`, `normalizedTowerTrace k`) directly to
the repository's `Cl11TensorTower` / `Cl11TensorTowerLimit.Limit` colimit spine and `τ_∞`
tracial state:

1. Explicit index equivalences `TowerIdx k ≃ TowerMatrix.Idx k` and `ℝ`-algebra isomorphisms
   `towerStageAlgEquiv k : Matrix (TowerIdx k) (TowerIdx k) ℝ ≃ₐ[ℝ] MatStage k`.
2. Commutation with Kronecker products, rung-to-rung step embeddings `towerStepAlgHom k ↦ stageEmbed k`,
   and trace normalization `normalizedTrace_towerStageAlgEquiv`.
3. Atom-by-atom identification of the Axiom 5 generators with `Cl11TensorTower` (`gammaCut2`,
   `gammaMir2`, `gammaSkew2`, `atomPos2`, `atomNeg2`, and `towerStageAlgEquiv_towerGamma`).
4. Stage-independent direct-limit homomorphisms `towerToDirectLimit k : M_{2^k}(ℝ) →+* Limit`,
   stabilized CAR operators `towerDirectLimitPos` / `towerDirectLimitNeg`, and exact trace
   consistency `τ_∞(cliffordBitWordColimitEquiv(towerToDirectLimit k A)) = normalizedTowerTrace k A`.
-/

noncomputable section

open scoped Kronecker
open Matrix

namespace InfoGeometry.Clifford.GradedNullconeTowerDirectLimitBridge

open InfoGeometry.Algebra.GradedNullconeAlgebra
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.Cl11JordanWignerDirectLimit
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Algebra.PrimonColimitAlgebra

/-- Recursive index equivalence identifying `GradedNullconeAlgebra.TowerIdx k` with the
canonical binary spinor index `TowerMatrix.Idx k`. -/
def towerIdxEquivIdx : ∀ k : ℕ, TowerIdx k ≃ TowerMatrix.Idx k
  | 0 =>
    { toFun := fun _ => (0 : Fin 1)
      invFun := fun _ => ()
      left_inv := fun _ => rfl
      right_inv := fun i => Subsingleton.elim _ i }
  | k + 1 => Equiv.prodCongr (towerIdxEquivIdx k) (Equiv.refl (Fin 2))

/-- Canonical `ℝ`-algebra isomorphism between rung `k` of `GradedNullconeAlgebra` and
`Cl11TensorTower.MatStage k`. -/
def towerStageAlgEquiv (k : ℕ) :
    Matrix (TowerIdx k) (TowerIdx k) ℝ ≃ₐ[ℝ] MatStage k :=
  Matrix.reindexAlgEquiv ℝ ℝ (towerIdxEquivIdx k)

/-- `towerStageAlgEquiv` intertwines Kronecker tensor products with `Fin 2 × Fin 2` atoms. -/
theorem towerStageAlgEquiv_kronecker (k : ℕ)
    (A : Matrix (TowerIdx k) (TowerIdx k) ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    towerStageAlgEquiv (k + 1) (A ⊗ₖ B) = (towerStageAlgEquiv k A) ⊗ₖ B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rfl

/-- `towerStageAlgEquiv` intertwines the rung-to-rung step embedding `towerStepAlgHom`
with `Cl11TensorTower.stageEmbed`. -/
@[simp] theorem towerStageAlgEquiv_towerStepAlgHom (k : ℕ)
    (A : Matrix (TowerIdx k) (TowerIdx k) ℝ) :
    towerStageAlgEquiv (k + 1) (towerStepAlgHom k A) =
      stageEmbed k (towerStageAlgEquiv k A) := by
  rw [towerStepAlgHom_apply, stageEmbed_apply, matStageEmbed, towerStageAlgEquiv_kronecker]

/-- `towerStageAlgEquiv` preserves the unnormalized matrix trace. -/
@[simp] theorem trace_towerStageAlgEquiv (k : ℕ)
    (A : Matrix (TowerIdx k) (TowerIdx k) ℝ) :
    Matrix.trace (towerStageAlgEquiv k A) = Matrix.trace A := by
  rw [Matrix.trace, Matrix.trace]
  simp only [towerStageAlgEquiv, Matrix.reindexAlgEquiv]
  exact Equiv.sum_comp (towerIdxEquivIdx k).symm (fun i => A i i)

/-- `towerStageAlgEquiv` preserves the `2^k`-normalized matrix trace. -/
@[simp] theorem normalizedTrace_towerStageAlgEquiv (k : ℕ)
    (A : Matrix (TowerIdx k) (TowerIdx k) ℝ) :
    InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace k (towerStageAlgEquiv k A) =
      normalizedTowerTrace k A := by
  unfold InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace normalizedTowerTrace
  rw [trace_towerStageAlgEquiv]

/-- Atom cut `Γ` agrees with `-gamma_chiral_base` in `Cl11TensorTower`. -/
theorem gammaCut2_eq_neg_gamma_chiral_base :
    gammaCut2 = -gamma_chiral_base := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gammaCut2, gamma_chiral_base, gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1, InfoGeometry.Clifford.Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Atom mirror `J` agrees with `gamma_0_base` (`Pauli X`) in `Cl11TensorTower`. -/
theorem gammaMir2_eq_gamma_0_base :
    gammaMir2 = gamma_0_base := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gammaMir2, gamma_0_base, InfoGeometry.Clifford.Cl11Matrix.J1]

/-- Atom chiral product `Γ * J` agrees with `gamma_1_base` (`Pauli iY`) in `Cl11TensorTower`. -/
theorem gammaSkew2_eq_gamma_1_base :
    gammaSkew2 = gamma_1_base := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gammaSkew2, gamma_1_base, InfoGeometry.Clifford.Cl11Matrix.Eminus]

/-- `atomPos2` agrees with `wittAnnihilationBase` in `Cl11TensorTower`. -/
theorem atomPos2_eq_wittAnnihilationBase :
    atomPos2 = wittAnnihilationBase := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [atomPos2, wittAnnihilationBase]

/-- `atomNeg2` agrees with `wittCreationBase` in `Cl11TensorTower`. -/
theorem atomNeg2_eq_wittCreationBase :
    atomNeg2 = wittCreationBase := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [atomNeg2, wittCreationBase]

private theorem globalChirality_succ (k : ℕ) :
    globalChirality (k + 1) = globalChirality k ⊗ₖ gamma_chiral_base := rfl

private theorem scalar_neg_one_pow_succ (k : ℕ) :
    (-1 : ℝ) ^ k * (-1 : ℝ) = (-1 : ℝ) ^ (k + 1) := by
  rw [pow_succ]

/-- The Axiom 5 grading operator `towerGamma k` maps to `(-1)^k • globalChirality k`
under `towerStageAlgEquiv k`. -/
theorem towerStageAlgEquiv_towerGamma (k : ℕ) :
    towerStageAlgEquiv k (towerGamma k) =
      (-1 : ℝ) ^ k • globalChirality k := by
  induction k with
  | zero =>
    simp [towerGamma, globalChirality, kronPow]
  | succ k ih =>
    have hneg : -gamma_chiral_base = (-1 : ℝ) • gamma_chiral_base :=
      (neg_one_smul ℝ gamma_chiral_base).symm
    rw [towerGamma_succ, towerStageAlgEquiv_kronecker, ih, gammaCut2_eq_neg_gamma_chiral_base,
      hneg, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
      scalar_neg_one_pow_succ, globalChirality_succ]
    ext ⟨i, a⟩ ⟨j, b⟩
    rfl

/-- Ring homomorphism embedding rung `k` of `GradedNullconeAlgebra` into the
repository direct limit `Cl11TensorTowerLimit.Limit`. -/
def towerToDirectLimit (k : ℕ) :
    Matrix (TowerIdx k) (TowerIdx k) ℝ →+* Cl11TensorTowerLimit.Limit :=
  (ofStage k).comp (towerStageAlgEquiv k).toRingHom

@[simp] theorem towerToDirectLimit_apply (k : ℕ)
    (A : Matrix (TowerIdx k) (TowerIdx k) ℝ) :
    towerToDirectLimit k A = ofStage k (towerStageAlgEquiv k A) := rfl

/-- The colimit embedding is strictly compatible with the rung-to-rung step map `towerStepAlgHom`. -/
@[simp] theorem towerToDirectLimit_step (k : ℕ)
    (A : Matrix (TowerIdx k) (TowerIdx k) ℝ) :
    towerToDirectLimit (k + 1) (towerStepAlgHom k A) = towerToDirectLimit k A := by
  rw [towerToDirectLimit_apply, towerStageAlgEquiv_towerStepAlgHom, ofStage_apply_bond,
    ← towerToDirectLimit_apply]

/-- Stabilized raising generator `e_i^+` in the algebraic direct limit `Limit`. -/
def towerDirectLimitPos (k : ℕ) (i : Fin k) : Cl11TensorTowerLimit.Limit :=
  towerToDirectLimit k (jwPos k i)

/-- Stabilized lowering generator `e_i^-` in the algebraic direct limit `Limit`. -/
def towerDirectLimitNeg (k : ℕ) (i : Fin k) : Cl11TensorTowerLimit.Limit :=
  towerToDirectLimit k (jwNeg k i)

/-- Site-index stability of `towerDirectLimitPos` under tower extension. -/
@[simp] theorem towerDirectLimitPos_castSucc (k : ℕ) (i : Fin k) :
    towerDirectLimitPos (k + 1) i.castSucc = towerDirectLimitPos k i := by
  unfold towerDirectLimitPos
  rw [← towerStepAlgHom_jwPos, towerToDirectLimit_step]

/-- Site-index stability of `towerDirectLimitNeg` under tower extension. -/
@[simp] theorem towerDirectLimitNeg_castSucc (k : ℕ) (i : Fin k) :
    towerDirectLimitNeg (k + 1) i.castSucc = towerDirectLimitNeg k i := by
  unfold towerDirectLimitNeg
  rw [← towerStepAlgHom_jwNeg, towerToDirectLimit_step]

/-- The canonical CAR anticommutation relations hold inside `Cl11TensorTowerLimit.Limit`
for all `towerDirectLimitPos` and `towerDirectLimitNeg` generators. -/
theorem towerDirectLimit_car_relations (k : ℕ) (i j : Fin k) :
    (towerDirectLimitPos k i * towerDirectLimitPos k j +
      towerDirectLimitPos k j * towerDirectLimitPos k i = 0) ∧
    (towerDirectLimitNeg k i * towerDirectLimitNeg k j +
      towerDirectLimitNeg k j * towerDirectLimitNeg k i = 0) ∧
    (towerDirectLimitPos k i * towerDirectLimitNeg k j +
      towerDirectLimitNeg k j * towerDirectLimitPos k i = if i = j then 1 else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold towerDirectLimitPos
    rw [← map_mul, ← map_mul, ← map_add, jwPos_anticomm k i j, map_zero]
  · unfold towerDirectLimitNeg
    rw [← map_mul, ← map_mul, ← map_add, jwNeg_anticomm k i j, map_zero]
  · unfold towerDirectLimitPos towerDirectLimitNeg
    rw [← map_mul, ← map_mul, ← map_add, jwPos_jwNeg_car k i j]
    split_ifs <;> simp

/-- The canonical BitWord colimit trace `τ_∞` pulls back along `towerToDirectLimit k` to
`normalizedTowerTrace k`. -/
theorem tauInfinity_towerToDirectLimit (k : ℕ)
    (A : Matrix (TowerIdx k) (TowerIdx k) ℝ) :
    tauInfinity (cliffordBitWordColimitEquiv (towerToDirectLimit k A)) =
      normalizedTowerTrace k A := by
  rw [towerToDirectLimit_apply, tauInfinity_cliffordBitWordColimitEquiv_stage,
    normalizedTrace_towerStageAlgEquiv]

/-- Both families of CAR generators in `Limit` have vanishing `τ_∞` expectation. -/
@[simp] theorem tauInfinity_towerDirectLimitPos (k : ℕ) (i : Fin k) :
    tauInfinity (cliffordBitWordColimitEquiv (towerDirectLimitPos k i)) = 0 := by
  rw [towerDirectLimitPos, tauInfinity_towerToDirectLimit, normalizedTowerTrace_jwPos]

/-- Both families of CAR generators in `Limit` have vanishing `τ_∞` expectation. -/
@[simp] theorem tauInfinity_towerDirectLimitNeg (k : ℕ) (i : Fin k) :
    tauInfinity (cliffordBitWordColimitEquiv (towerDirectLimitNeg k i)) = 0 := by
  rw [towerDirectLimitNeg, tauInfinity_towerToDirectLimit, normalizedTowerTrace_jwNeg]

end InfoGeometry.Clifford.GradedNullconeTowerDirectLimitBridge
