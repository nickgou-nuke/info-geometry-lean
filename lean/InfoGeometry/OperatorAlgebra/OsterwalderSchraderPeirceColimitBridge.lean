/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OsterwalderSchraderTransferSemigroupAndMassGap
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
import InfoGeometry.Canonical.TwoSheetedYangMillsInductiveColimit
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# Osterwalder–Schrader Transfer Semigroup ↔ Peirce/Krein `Cl(1,1)^{⊗n}` Colimit & LogCFT Jordan Obstruction

Bridges the Euclidean lattice gauge transfer-matrix semigroup
(`OsterwalderSchraderTransferSemigroupAndMassGap`) into the two-sheeted operator-algebraic
Peirce/Krein spine (`PeirceDefectBridge`, `TwoSheetedYangMillsInductiveColimit`) and the
`Cl(1,1)^{⊗n}` inductive colimit `Limit` (`Cl11TensorTowerLimit`), establishes multi-site
(`N`-site) tensor-product OS reflection positivity and mass-gap clustering, and separates
Hermitian OS semigroups from non-Hermitian logarithmic CFT Jordan monodromy cells
(`LogCftMonodromy.virasoroL0Cell`).
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OsterwalderSchraderPeirceColimitBridge

open scoped BigOperators Matrix
open Matrix Filter
open InfoGeometry.OperatorAlgebra.OsterwalderSchraderTransferSemigroupAndMassGap
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open CanonicalTwoSheetedInductiveColimit

/-! ## 1. OS Spectral Projectors as a Peirce Cut & Maurer–Cartan Bianchi -/

/-- The excited spectral projection `projExcited` equals the complementary Peirce projection `1 - projGround`. -/
theorem projExcited_eq_one_sub_projGround :
    projExcited = 1 - projGround := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> dsimp [projGround, projExcited] <;> norm_num

/-- The Peirce grading involution `invS projGround = 2 * projGround - 1` equals Pauli `matSigmaX`. -/
theorem invS_projGround_eq_matSigmaX :
    invS projGround = matSigmaX := by
  ext i j
  unfold invS
  simp only [Matrix.sub_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> dsimp [projGround, matSigmaX] <;> norm_num

/-- `projGround` is self-adjoint (`star projGround = projGround`). -/
theorem projGround_star_self :
    star projGround = projGround := by
  ext i j
  rw [Matrix.star_apply]
  fin_cases i <;> fin_cases j <;> dsimp [projGround] <;> norm_num

/-- `matSigmaZ` is self-adjoint (`star matSigmaZ = matSigmaZ`). -/
theorem matSigmaZ_star_self :
    star matSigmaZ = matSigmaZ := by
  ext i j
  rw [Matrix.star_apply]
  fin_cases i <;> fin_cases j <;> dsimp [matSigmaZ] <;> norm_num

/-- Helper: `normTransferMat J` commutes with `projGround`. -/
theorem normTransferMat_comm_projGround (J : ℝ) :
    projGround * normTransferMat J = normTransferMat J * projGround := by
  have hL : projGround * normTransferMat J = projGround := by
    rw [normTransferMat, mul_add, projGround_isIdempotent, mul_smul_comm, proj_orthogonal.1,
      smul_zero, add_zero]
  have hR : normTransferMat J * projGround = projGround := by
    rw [normTransferMat, add_mul, projGround_isIdempotent, smul_mul_assoc, proj_orthogonal.2,
      smul_zero, add_zero]
  rw [hL, hR]

private lemma one_sub_projGround_mul_normTransferMat (J : ℝ) :
    (1 - projGround) * normTransferMat J = Real.tanh J • projExcited := by
  rw [← projExcited_eq_one_sub_projGround, normTransferMat, mul_add, proj_orthogonal.2, zero_add,
    mul_smul_comm, projExcited_isIdempotent]

/-- The normalized transfer matrix `normTransferMat J` lies entirely in the even Peirce grade
of `projGround`. -/
theorem evenGrade_normTransferMat (J : ℝ) :
    evenGrade projGround (normTransferMat J) = normTransferMat J := by
  unfold evenGrade
  have hL : projGround * normTransferMat J * projGround = projGround := by
    rw [normTransferMat, mul_add, projGround_isIdempotent, mul_smul_comm, proj_orthogonal.1,
      smul_zero, add_zero, projGround_isIdempotent]
  have hR : (1 - projGround) * normTransferMat J * (1 - projGround) = Real.tanh J • projExcited := by
    rw [one_sub_projGround_mul_normTransferMat, ← projExcited_eq_one_sub_projGround, smul_mul_assoc,
      projExcited_isIdempotent]
  rw [hL, hR, ← normTransferMat]

/-- The odd Peirce component of `normTransferMat J` vanishes identically. -/
theorem oddGrade_normTransferMat_eq_zero (J : ℝ) :
    oddGrade projGround (normTransferMat J) = 0 := by
  unfold oddGrade
  have h1 : projGround * normTransferMat J * (1 - projGround) = 0 := by
    rw [normTransferMat_comm_projGround, mul_assoc, ← projExcited_eq_one_sub_projGround,
      proj_orthogonal.1, mul_zero]
  have h2 : (1 - projGround) * normTransferMat J * projGround = 0 := by
    rw [one_sub_projGround_mul_normTransferMat, smul_mul_assoc, proj_orthogonal.2, smul_zero]
  rw [h1, h2, add_zero]

/-- Pauli `matSigmaZ` has zero even Peirce component relative to `projGround`. -/
theorem evenGrade_matSigmaZ_eq_zero :
    evenGrade projGround matSigmaZ = 0 := by
  ext i j
  unfold evenGrade
  simp only [Matrix.zero_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> dsimp [projGround, matSigmaZ] <;> norm_num

/-- Pauli `matSigmaZ` is purely odd under the Peirce cut `projGround`. -/
theorem oddGrade_matSigmaZ :
    oddGrade projGround matSigmaZ = matSigmaZ := by
  ext i j
  unfold oddGrade
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> dsimp [projGround, matSigmaZ] <;> norm_num

/-- Explicitly, the forward and backward nilpotent cones `conePlus projGround matSigmaZ`
and `coneMinus projGround matSigmaZ` produce `genV projGround matSigmaZ matSigmaZ = 1`. -/
theorem genV_projGround_matSigmaZ :
    genV projGround matSigmaZ matSigmaZ = 1 := by
  ext i j
  unfold genV anticomm conePlus coneMinus
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> dsimp [projGround, matSigmaZ] <;> norm_num

/-- The OS ground projection and `matSigmaZ` horizon connection satisfy the Peirce Maurer–Cartan
self-dual Yang–Mills / Bianchi suite (`peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills`). -/
theorem os_peirce_maurer_cartan_bianchi (X Y : Matrix (Fin 2) (Fin 2) ℝ) :
    peirceMaurerCartanCurvature projGround matSigmaZ matSigmaZ =
      genJ projGround matSigmaZ matSigmaZ + 1 ∧
    peirceCovariantDeriv projGround matSigmaZ matSigmaZ 1 = 0 ∧
    peirceGradingDeriv projGround (evenGrade projGround X) = 0 ∧
    peirceGradingDeriv projGround (X * Y) =
      peirceGradingDeriv projGround X * Y + X * peirceGradingDeriv projGround Y := by
  have hspec :=
    peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills
      projGround_isIdempotent matSigmaZ matSigmaZ X Y
  refine ⟨?_, ?_, hspec.2.1, hspec.1⟩
  · simpa [genV_projGround_matSigmaZ] using hspec.2.2.1
  · simpa [genV_projGround_matSigmaZ] using hspec.2.2.2.2.2.2.2.2.2.1

/-- **Peirce–OS Mass-Gap Horizon Contraction**: transporting the forward nilpotent horizon wave
`conePlus projGround matSigmaZ` through `L` Euclidean steps of `normTransferMat J` on the
excited side decays exponentially at rate `spectralMassGap J` for `J > 0`. -/
theorem conePlus_matSigmaZ_mul_normTransferMat_pow {J : ℝ} (hJ : 0 < J) (L : ℕ) :
    conePlus projGround (matSigmaZ * (normTransferMat J) ^ L) =
      Real.exp (-(L : ℝ) * spectralMassGap J) • conePlus projGround matSigmaZ := by
  rw [normTransferMat_pow, ← normTransferMat_pow_eq_exp_gap J hJ L]
  unfold conePlus
  rw [← projExcited_eq_one_sub_projGround]
  calc
    projGround * (matSigmaZ * (projGround + (Real.tanh J) ^ L • projExcited)) * projExcited
        = projGround * matSigmaZ * (projGround * projExcited) +
            (Real.tanh J) ^ L • (projGround * matSigmaZ * (projExcited * projExcited)) := by
            simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = 0 + (Real.tanh J) ^ L • (projGround * matSigmaZ * projExcited) := by
            rw [proj_orthogonal.1, projExcited_isIdempotent, mul_zero]
    _ = (Real.tanh J) ^ L • (projGround * matSigmaZ * projExcited) := zero_add _

private lemma projGround_mul_matSigmaZ_mul_projExcited_mul_matSigmaZ_mul_projGround :
    projGround * matSigmaZ * projExcited * matSigmaZ * projGround = projGround := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> dsimp [projGround, projExcited, matSigmaZ] <;> norm_num

private lemma projGround_mul_matSigmaZ_mul_projGround :
    projGround * matSigmaZ * projGround = 0 := by
  ext i j
  simp only [Matrix.zero_apply, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> dsimp [projGround, matSigmaZ] <;> norm_num

/-- Two-sided Peirce–OS correlation matrix identity matching `expect_wilson_from_transferMat`. -/
theorem normTransferMat_pow_sandwich_matSigmaZ (J : ℝ) (L : ℕ) :
    projGround * matSigmaZ * (normTransferMat J) ^ L * matSigmaZ * projGround =
      ((Real.tanh J) ^ L) • projGround := by
  rw [normTransferMat_pow]
  calc
    projGround * matSigmaZ * (projGround + (Real.tanh J) ^ L • projExcited) * matSigmaZ * projGround
        = ((projGround * matSigmaZ * projGround) * matSigmaZ * projGround) +
            (Real.tanh J) ^ L • (projGround * matSigmaZ * projExcited * matSigmaZ * projGround) := by
            simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = ((0 : Matrix (Fin 2) (Fin 2) ℝ) * matSigmaZ * projGround) + (Real.tanh J) ^ L • projGround := by
            rw [projGround_mul_matSigmaZ_mul_projGround,
              projGround_mul_matSigmaZ_mul_projExcited_mul_matSigmaZ_mul_projGround]
    _ = ((Real.tanh J) ^ L) • projGround := by simp

/-! ## 2. Transport of OS Transfer Semigroup & Mass Gap into `Cl(1,1)^{⊗n}` Stages and `Limit` -/

/-- Canonical index equivalence between `TowerMatrix.Idx 1 = Fin 1 × Fin 2` and `Fin 2`. -/
def idx1EquivFin2 : InfoGeometry.Clifford.TowerMatrix.Idx 1 ≃ Fin 2 where
  toFun p := p.2
  invFun i := ((0 : Fin 1), i)
  left_inv := fun ⟨a, _⟩ => by fin_cases a; rfl
  right_inv _ := rfl

/-- Star-preserving `ℝ`-algebra homomorphism embedding `M₂(ℝ)` into `Stage 1` of the `Cl(1,1)` tower. -/
def mat2ToStage1 : Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ] Stage 1 where
  toFun M a b := M a.2 b.2
  map_one' := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    have h1 : i1 = j1 := Subsingleton.elim _ _
    subst h1
    change (1 : Matrix (Fin 2) (Fin 2) ℝ) i2 j2 =
      (1 : Matrix (InfoGeometry.Clifford.TowerMatrix.Idx 0 × Fin 2)
        (InfoGeometry.Clifford.TowerMatrix.Idx 0 × Fin 2) ℝ) (i1, i2) (i1, j2)
    simp [Matrix.one_apply]
  map_mul' A B := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    let X : Stage 1 := fun a b => A a.2 b.2
    let Y : Stage 1 := fun a b => B a.2 b.2
    have hlhs : (A * B) i2 j2 = ∑ k : Fin 2, A i2 k * B k j2 := Matrix.mul_apply
    have hrhs : (X * Y) (i1, i2) (j1, j2) =
        ∑ k : InfoGeometry.Clifford.TowerMatrix.Idx 1, A i2 k.2 * B k.2 j2 :=
      Matrix.mul_apply
    have hgoal : ∑ k : Fin 2, A i2 k * B k j2 =
        ∑ k : InfoGeometry.Clifford.TowerMatrix.Idx 1, A i2 k.2 * B k.2 j2 :=
      (Fintype.sum_equiv idx1EquivFin2 (fun k => A i2 k.2 * B k.2 j2)
        (fun j => A i2 j * B j j2) (fun _ => rfl)).symm
    exact hlhs.trans (hgoal.trans hrhs.symm)
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    have h1 : i1 = j1 := Subsingleton.elim _ _
    subst h1
    change (algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) r) i2 j2 =
      (algebraMap ℝ
        (Matrix (InfoGeometry.Clifford.TowerMatrix.Idx 0 × Fin 2)
          (InfoGeometry.Clifford.TowerMatrix.Idx 0 × Fin 2) ℝ) r) (i1, i2) (i1, j2)
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply]

theorem mat2ToStage1_star (M : Matrix (Fin 2) (Fin 2) ℝ) :
    mat2ToStage1 (star M) = star (mat2ToStage1 M) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  rfl

theorem mat2ToStage1_injective : Function.Injective mat2ToStage1 := by
  intro A B h
  ext i j
  exact congrArg (fun M : Stage 1 => M ((0 : Fin 1), i) ((0 : Fin 1), j)) h

theorem normalizedTrace_mat2ToStage1 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    normalizedTrace 1 (mat2ToStage1 M) = Matrix.trace M / 2 := by
  unfold normalizedTrace Matrix.trace Matrix.diag
  rw [pow_one]
  exact congrArg (· / 2)
    (Fintype.sum_equiv idx1EquivFin2
      (fun i : InfoGeometry.Clifford.TowerMatrix.Idx 1 => mat2ToStage1 M i i)
      (fun j : Fin 2 => M j j)
      (fun _ => rfl))

/-- Embeds `M₂(ℝ)` into any positive tower stage `Stage n` (`1 ≤ n`) via iterated `bondMap stageBond`. -/
def mat2ToStage (n : ℕ) (hn : 1 ≤ n) (M : Matrix (Fin 2) (Fin 2) ℝ) : Stage n :=
  bondMap stageBond 1 n hn (mat2ToStage1 M)

/-- Canonical `RingHom` embedding `M₂(ℝ)` into the inductive colimit `Limit`. -/
def mat2ToLimit : Matrix (Fin 2) (Fin 2) ℝ →+* Limit :=
  (ofStage 1).comp mat2ToStage1.toRingHom

theorem mat2ToStage_ofStage (n : ℕ) (hn : 1 ≤ n) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ofStage n (mat2ToStage n hn M) = mat2ToLimit M := by
  unfold mat2ToStage mat2ToLimit
  change directLimitOf stageBond n (bondMap stageBond 1 n hn (mat2ToStage1 M)) =
    directLimitOf stageBond 1 (mat2ToStage1 M)
  exact directLimitOf_bondMap stageBond 1 n hn (mat2ToStage1 M)

theorem mat2ToLimit_star (M : Matrix (Fin 2) (Fin 2) ℝ) :
    mat2ToLimit (star M) = star (mat2ToLimit M) := by
  unfold mat2ToLimit
  change ofStage 1 (mat2ToStage1 (star M)) = star (ofStage 1 (mat2ToStage1 M))
  rw [mat2ToStage1_star, ofStage_star]

theorem mat2ToStage_star (n : ℕ) (hn : 1 ≤ n) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    mat2ToStage n hn (star M) = star (mat2ToStage n hn M) := by
  unfold mat2ToStage
  rw [mat2ToStage1_star, bondMap_star 1 n hn]

theorem normalizedTrace_bondMap {m n : ℕ} (hmn : m ≤ n) (A : Stage m) :
    normalizedTrace n (bondMap stageBond m n hmn A) = normalizedTrace m A := by
  refine Nat.le_induction
    (P := fun t ht => normalizedTrace t (bondMap stageBond m t ht A) = normalizedTrace m A)
    (by simp [bondMap_refl])
    (fun t hmt ih => by
      rw [bondMap_succ stageBond m t hmt, RingHom.comp_apply]
      change normalizedTrace (t + 1) (matStageEmbed t (bondMap stageBond m t hmt A)) = normalizedTrace m A
      rw [normalizedTrace_matStageEmbed, ih])
    n hmn

theorem normalizedTrace_mat2ToStage (n : ℕ) (hn : 1 ≤ n) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    normalizedTrace n (mat2ToStage n hn M) = Matrix.trace M / 2 := by
  unfold mat2ToStage
  rw [normalizedTrace_bondMap hn, normalizedTrace_mat2ToStage1]

theorem mat2ToLimit_smul (c : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    mat2ToLimit (c • M) = realAlgebraMap c * mat2ToLimit M := by
  unfold mat2ToLimit realAlgebraMap
  have hm : mat2ToStage1 (c • M) = algebraMap ℝ (Stage 1) c * mat2ToStage1 M := by
    rw [map_smul, Algebra.smul_def]
  have halg : (ofStage 1) (algebraMap ℝ (Stage 1) c) = (ofStage 0) (algebraMap ℝ (Stage 0) c) := by
    have h01 : (0 : ℕ) ≤ 1 := by norm_num
    have hb : algebraMap ℝ (Stage 1) c = bondMap stageBond 0 1 h01 (algebraMap ℝ (Stage 0) c) := by
      rw [bondMap_succ stageBond 0 0 le_rfl, bondMap_refl]
      simp only [RingHom.id_apply, RingHom.comp_apply, stageBond, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AlgHom.commutes]
    rw [hb]
    exact directLimitOf_bondMap stageBond 0 1 h01 (algebraMap ℝ (Stage 0) c)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hm, map_mul, halg]

/-- Colimit ground projector `limitProjGround` inside `Limit`. -/
def limitProjGround : Limit := mat2ToLimit projGround

/-- Colimit excited projector `limitProjExcited` inside `Limit`. -/
def limitProjExcited : Limit := mat2ToLimit projExcited

/-- Colimit normalized transfer operator `limitNormTransfer J` inside `Limit`. -/
def limitNormTransfer (J : ℝ) : Limit := mat2ToLimit (normTransferMat J)

/-- Colimit Peirce `matSigmaZ` horizon connection inside `Limit`. -/
def limitSigmaZ : Limit := mat2ToLimit matSigmaZ

/-- Complete colimit transport of the OS spectral semigroup, exponential mass gap, self-adjointness,
Peirce Maurer–Cartan Bianchi identity, and `normalizedTrace` clustering across all stages `n ≥ 1`
and into `Limit`. -/
theorem limit_os_semigroup_peirce_and_trace_clustering
    {J : ℝ} (hJ : 0 < J) (L : ℕ) (n : ℕ) (hn : 1 ≤ n) :
    limitProjGround * limitProjGround = limitProjGround ∧
    star limitProjGround = limitProjGround ∧
    limitProjGround + limitProjExcited = 1 ∧
    limitNormTransfer J ^ L =
      limitProjGround + realAlgebraMap (Real.exp (-(L : ℝ) * spectralMassGap J)) * limitProjExcited ∧
    peirceCovariantDeriv limitProjGround limitSigmaZ limitSigmaZ
      (genV limitProjGround limitSigmaZ limitSigmaZ) = 0 ∧
    normalizedTrace n
      (mat2ToStage n hn (projGround * matSigmaZ * (normTransferMat J) ^ L * matSigmaZ * projGround)) =
        Real.exp (-(L : ℝ) * spectralMassGap J) / 2 := by
  have hP2 : limitProjGround * limitProjGround = limitProjGround := by
    unfold limitProjGround
    rw [← map_mul, projGround_isIdempotent]
  have hPs : star limitProjGround = limitProjGround := by
    unfold limitProjGround
    rw [← mat2ToLimit_star, projGround_star_self]
  have hSum : limitProjGround + limitProjExcited = 1 := by
    unfold limitProjGround limitProjExcited
    rw [← map_add, proj_sum, map_one]
  have hPow :
      limitNormTransfer J ^ L =
        limitProjGround + realAlgebraMap (Real.exp (-(L : ℝ) * spectralMassGap J)) * limitProjExcited := by
    unfold limitNormTransfer limitProjGround limitProjExcited
    rw [← map_pow, normTransferMat_pow, map_add, normTransferMat_pow_eq_exp_gap J hJ L,
      mat2ToLimit_smul]
  have hBianchi :
      peirceCovariantDeriv limitProjGround limitSigmaZ limitSigmaZ
        (genV limitProjGround limitSigmaZ limitSigmaZ) = 0 :=
    (peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills hP2
      limitSigmaZ limitSigmaZ limitProjGround limitSigmaZ).2.2.2.2.2.2.2.2.2.1
  have hTr :
      normalizedTrace n
        (mat2ToStage n hn (projGround * matSigmaZ * (normTransferMat J) ^ L * matSigmaZ * projGround)) =
          Real.exp (-(L : ℝ) * spectralMassGap J) / 2 := by
    rw [normTransferMat_pow_sandwich_matSigmaZ, normalizedTrace_mat2ToStage,
      Matrix.trace_smul, smul_eq_mul, normTransferMat_pow_eq_exp_gap J hJ L]
    have hTrP0 : Matrix.trace projGround = 1 := by
      simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, projGround, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
    rw [hTrP0, mul_one]
  exact ⟨hP2, hPs, hSum, hPow, hBianchi, hTr⟩

/-! ## 3. Multi-Site (`N`-Site) Tensor-Product OS Reflection Positivity & Mass Gap -/

/-- Orthogonal single-site mode functions `b = false ↦ (1, 1)` (ground), `b = true ↦ (1, -1)` (excited). -/
def siteModeVec (b : Bool) (s : Fin 2) : ℝ :=
  if b then (if s = 0 then 1 else -1) else 1

/-- Single-site mode eigenvalues `cosh J` (ground) and `sinh J` (excited). -/
def siteModeEig (J : ℝ) (b : Bool) : ℝ :=
  if b then Real.sinh J else Real.cosh J

private lemma scalar_exp_eq_cosh_add_sinh (J : ℝ) :
    Real.exp J = Real.cosh J + Real.sinh J := by
  linarith [Real.cosh_add_sinh J]

private lemma transferMat_eq_sum_modes (J : ℝ) (a b : Fin 2) :
    transferMat J a b = ∑ m : Bool, siteModeEig J m * siteModeVec m a * siteModeVec m b := by
  rw [Fintype.sum_bool]
  fin_cases a <;> fin_cases b <;>
    dsimp [transferMat, siteModeEig, siteModeVec] <;>
    simp only [scalar_exp_eq_cosh_add_sinh, Real.cosh_neg, Real.sinh_neg] <;>
    ring

/-- Multi-site two-slice Euclidean Boltzmann kernel `∏_{s : Fin N} T(J s)_{sNeg s, sPos s}`. -/
def multiSiteKernel {N : ℕ} (J : Fin N → ℝ) (sNeg sPos : Fin N → Fin 2) : ℝ :=
  ∏ s : Fin N, transferMat (J s) (sNeg s) (sPos s)

/-- Multi-site two-slice partition function `∏_{s : Fin N} Z(J s)`. -/
def multiSitePartitionFn {N : ℕ} (J : Fin N → ℝ) : ℝ :=
  ∏ s : Fin N, osPartitionFn (J s)

theorem multiSitePartitionFn_pos {N : ℕ} (J : Fin N → ℝ) :
    0 < multiSitePartitionFn J := by
  unfold multiSitePartitionFn
  refine Finset.prod_pos fun s _ => ?_
  have hcos : 0 < Real.cosh (J s) := Real.cosh_pos (J s)
  have h4 : osPartitionFn (J s) = 4 * Real.cosh (J s) := by
    simp only [osPartitionFn, transferMat, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Real.cosh_eq]
    ring
  rw [h4]
  positivity

/-- Multi-site Osterwalder–Schrader bilinear form on observables `f, g : (Fin N → Fin 2) → ℝ`. -/
def multiSiteOSBilinForm {N : ℕ} (J : Fin N → ℝ) (f g : (Fin N → Fin 2) → ℝ) : ℝ :=
  (∑ sNeg : Fin N → Fin 2, ∑ sPos : Fin N → Fin 2, multiSiteKernel J sNeg sPos * f sNeg * g sPos) /
    multiSitePartitionFn J

/-- **Multi-Site (`N`-Site) Osterwalder–Schrader Reflection Positivity**: for any `N : ℕ`
and strictly ferromagnetic site couplings `J : Fin N → ℝ` (`0 < J s`), the tensor-product
OS bilinear form is positive semidefinite: `0 ≤ ⟨f, f⟩_{OS, J}`. -/
theorem multiSite_os_reflection_positivity {N : ℕ} (J : Fin N → ℝ) (hJ : ∀ s, 0 < J s)
    (f : (Fin N → Fin 2) → ℝ) :
    0 ≤ multiSiteOSBilinForm J f f := by
  unfold multiSiteOSBilinForm
  refine div_nonneg ?_ (multiSitePartitionFn_pos J).le
  have hker : ∀ sNeg sPos : Fin N → Fin 2,
      multiSiteKernel J sNeg sPos =
        ∑ c : Fin N → Bool,
          (∏ s : Fin N, siteModeEig (J s) (c s)) *
            ((∏ s : Fin N, siteModeVec (c s) (sNeg s)) *
              (∏ s : Fin N, siteModeVec (c s) (sPos s))) := by
    intro sNeg sPos
    unfold multiSiteKernel
    calc
      ∏ s : Fin N, transferMat (J s) (sNeg s) (sPos s)
          = ∏ s : Fin N, ∑ m : Bool, siteModeEig (J s) m * siteModeVec m (sNeg s) * siteModeVec m (sPos s) := by
              refine Finset.prod_congr rfl fun s _ => transferMat_eq_sum_modes (J s) (sNeg s) (sPos s)
      _ = ∑ c : Fin N → Bool, ∏ s : Fin N,
              (siteModeEig (J s) (c s) * siteModeVec (c s) (sNeg s) * siteModeVec (c s) (sPos s)) := by
              rw [Fintype.prod_sum]
      _ = ∑ c : Fin N → Bool,
            (∏ s : Fin N, siteModeEig (J s) (c s)) *
              ((∏ s : Fin N, siteModeVec (c s) (sNeg s)) *
                (∏ s : Fin N, siteModeVec (c s) (sPos s))) := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
              ring
  have hrewrite :
      (∑ sNeg : Fin N → Fin 2, ∑ sPos : Fin N → Fin 2, multiSiteKernel J sNeg sPos * f sNeg * f sPos) =
        ∑ c : Fin N → Bool,
          (∏ s : Fin N, siteModeEig (J s) (c s)) *
            (∑ σ : Fin N → Fin 2, (∏ s : Fin N, siteModeVec (c s) (σ s)) * f σ) ^ 2 := by
    calc
      (∑ sNeg : Fin N → Fin 2, ∑ sPos : Fin N → Fin 2, multiSiteKernel J sNeg sPos * f sNeg * f sPos)
          = ∑ sNeg : Fin N → Fin 2, ∑ sPos : Fin N → Fin 2, ∑ c : Fin N → Bool,
              (∏ s : Fin N, siteModeEig (J s) (c s)) *
                (((∏ s : Fin N, siteModeVec (c s) (sNeg s)) * f sNeg) *
                  ((∏ s : Fin N, siteModeVec (c s) (sPos s)) * f sPos)) := by
              refine Finset.sum_congr rfl fun sNeg _ => Finset.sum_congr rfl fun sPos _ => ?_
              rw [hker sNeg sPos, Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_congr rfl fun c _ => ?_
              ring
      _ = ∑ c : Fin N → Bool, ∑ sNeg : Fin N → Fin 2, ∑ sPos : Fin N → Fin 2,
              (∏ s : Fin N, siteModeEig (J s) (c s)) *
                (((∏ s : Fin N, siteModeVec (c s) (sNeg s)) * f sNeg) *
                  ((∏ s : Fin N, siteModeVec (c s) (sPos s)) * f sPos)) := by
              have hswap1 :
                  ∀ sNeg : Fin N → Fin 2,
                    (∑ sPos : Fin N → Fin 2, ∑ c : Fin N → Bool,
                      (∏ s : Fin N, siteModeEig (J s) (c s)) *
                        (((∏ s : Fin N, siteModeVec (c s) (sNeg s)) * f sNeg) *
                          ((∏ s : Fin N, siteModeVec (c s) (sPos s)) * f sPos))) =
                    (∑ c : Fin N → Bool, ∑ sPos : Fin N → Fin 2,
                      (∏ s : Fin N, siteModeEig (J s) (c s)) *
                        (((∏ s : Fin N, siteModeVec (c s) (sNeg s)) * f sNeg) *
                          ((∏ s : Fin N, siteModeVec (c s) (sPos s)) * f sPos))) :=
                fun _ => Finset.sum_comm
              simp_rw [hswap1]
              exact Finset.sum_comm
      _ = ∑ c : Fin N → Bool,
            (∏ s : Fin N, siteModeEig (J s) (c s)) *
              (∑ σ : Fin N → Fin 2, (∏ s : Fin N, siteModeVec (c s) (σ s)) * f σ) ^ 2 := by
              refine Finset.sum_congr rfl fun c _ => ?_
              have hinner :
                  (∑ sNeg : Fin N → Fin 2, ∑ sPos : Fin N → Fin 2,
                    (∏ s : Fin N, siteModeEig (J s) (c s)) *
                      (((∏ s : Fin N, siteModeVec (c s) (sNeg s)) * f sNeg) *
                        ((∏ s : Fin N, siteModeVec (c s) (sPos s)) * f sPos))) =
                  (∑ sNeg : Fin N → Fin 2,
                    ((∏ s : Fin N, siteModeEig (J s) (c s)) *
                      ((∏ s : Fin N, siteModeVec (c s) (sNeg s)) * f sNeg)) *
                      ∑ sPos : Fin N → Fin 2, (∏ s : Fin N, siteModeVec (c s) (sPos s)) * f sPos) := by
                refine Finset.sum_congr rfl fun sNeg _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun sPos _ => ?_
                ring
              rw [hinner, ← Finset.sum_mul, ← Finset.mul_sum, mul_assoc, ← sq]
  rw [hrewrite]
  refine Finset.sum_nonneg fun c _ => ?_
  refine mul_nonneg ?_ (sq_nonneg _)
  refine Finset.prod_nonneg fun s _ => ?_
  by_cases hc : c s
  · simp [siteModeEig, hc, (Real.sinh_pos_iff.mpr (hJ s)).le]
  · simp [siteModeEig, hc, (Real.cosh_pos (J s)).le]

/-- Multi-site spectral mass gap `inf_{s : Fin N} Δ(J s)` for nonempty `N ≥ 1`. -/
def multiSiteSpectralMassGap {N : ℕ} [NeZero N] (J : Fin N → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun s => spectralMassGap (J s)

/-- Strict positivity of the multi-site spectral mass gap whenever `∀ s, 0 < J s`. -/
theorem multiSiteSpectralMassGap_pos {N : ℕ} [NeZero N] (J : Fin N → ℝ) (hJ : ∀ s, 0 < J s) :
    0 < multiSiteSpectralMassGap J := by
  unfold multiSiteSpectralMassGap
  rw [Finset.lt_inf'_iff]
  intro s _
  exact spectralMassGap_pos (hJ s)

private lemma finset_prod_le_prod_of_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine mul_le_mul (hfg a (Finset.mem_insert_self a t))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi))
      ((hf a (Finset.mem_insert_self a t)).trans (hfg a (Finset.mem_insert_self a t)))

/-- Multi-site sitewise `L`-step Wilson string expectation decays exponentially at least at rate
`multiSiteSpectralMassGap J`: `∏_{s : Fin N} (tanh (J s))^L ≤ exp (-L * Δ_multi(J))`. -/
theorem multiSite_wilson_clustering_le_exp_gap {N : ℕ} [NeZero N] (J : Fin N → ℝ)
    (hJ : ∀ s, 0 < J s) (L : ℕ) :
    (∏ s : Fin N, (Real.tanh (J s)) ^ L) ≤
      Real.exp (-(L : ℝ) * multiSiteSpectralMassGap J) := by
  have htanh_nn : ∀ s : Fin N, 0 ≤ Real.tanh (J s) := fun s => by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact (div_pos (Real.sinh_pos_iff.mpr (hJ s)) (Real.cosh_pos (J s))).le
  have hsingle : ∀ s : Fin N, (Real.tanh (J s)) ^ L ≤ Real.exp (-(L : ℝ) * multiSiteSpectralMassGap J) := by
    intro s
    rw [normTransferMat_pow_eq_exp_gap (J s) (hJ s) L]
    apply Real.exp_le_exp.mpr
    have hinf : multiSiteSpectralMassGap J ≤ spectralMassGap (J s) :=
      Finset.inf'_le (fun u => spectralMassGap (J u)) (Finset.mem_univ s)
    nlinarith [hinf]
  have hpow :
      (∏ s : Fin N, (Real.tanh (J s)) ^ L) ≤
        (∏ _s : Fin N, Real.exp (-(L : ℝ) * multiSiteSpectralMassGap J)) :=
    finset_prod_le_prod_of_nonneg Finset.univ _ _ (fun s _ => pow_nonneg (htanh_nn s) L)
      (fun s _ => hsingle s)
  calc
    (∏ s : Fin N, (Real.tanh (J s)) ^ L)
        ≤ ∏ _s : Fin N, Real.exp (-(L : ℝ) * multiSiteSpectralMassGap J) := hpow
    _ = (Real.exp (-(L : ℝ) * multiSiteSpectralMassGap J)) ^ N := by
        simp [Finset.prod_const, Finset.card_univ]
    _ ≤ Real.exp (-(L : ℝ) * multiSiteSpectralMassGap J) := by
        have hexp_le : Real.exp (-(L : ℝ) * multiSiteSpectralMassGap J) ≤ 1 := by
          rw [← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          have hpos := multiSiteSpectralMassGap_pos J hJ
          nlinarith [hpos]
        exact pow_le_of_le_one (Real.exp_pos _).le hexp_le (NeZero.ne N)

/-! ## 4. LogCFT Jordan Monodromy vs. OS Reflection-Positive Semigroup Obstruction -/

private lemma scalar_jordan_00 (h : ℂ) (n : ℕ) :
    h ^ n * h + ((n : ℂ) * h ^ (n - 1)) * 0 = h ^ (n + 1) := by
  ring

private lemma scalar_jordan_01 (h : ℂ) (n : ℕ) :
    h ^ n * 1 + ((n : ℂ) * h ^ (n - 1)) * h = ((n + 1 : ℕ) : ℂ) * h ^ ((n + 1) - 1) := by
  cases n with
  | zero => simp
  | succ m =>
    simp only [Nat.add_sub_cancel, pow_succ, Nat.cast_add, Nat.cast_one]
    ring

private lemma scalar_jordan_10 (h : ℂ) (n : ℕ) : (0 : ℂ) * h + h ^ n * 0 = 0 := by
  ring

private lemma scalar_jordan_11 (h : ℂ) (n : ℕ) : (0 : ℂ) * 1 + h ^ n * h = h ^ (n + 1) := by
  ring

/-- Exact power formula for the logarithmic CFT Virasoro `L₀` cell `[[h, 1], [0, h]]`. -/
theorem virasoroL0Cell_pow (h : ℂ) (L : ℕ) :
    (virasoroL0Cell h) ^ L = !![h ^ L, (L : ℂ) * h ^ (L - 1); 0, h ^ L] := by
  induction L with
  | zero =>
    rw [pow_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> dsimp [virasoroL0Cell, upperJordan]
    · exact scalar_jordan_00 h n
    · exact scalar_jordan_01 h n
    · exact scalar_jordan_10 h n
    · exact scalar_jordan_11 h n

/-- For every `L ≥ 1`, the `(0, 1)` off-diagonal entry of `(virasoroL0Cell h)^L` exhibits
logarithmic secular growth `L * h^(L - 1)`, preventing pure orthogonal diagonal decay. -/
theorem virasoroL0Cell_pow_apply_01 (h : ℂ) (L : ℕ) :
    ((virasoroL0Cell h) ^ L) 0 1 = (L : ℂ) * h ^ (L - 1) := by
  rw [virasoroL0Cell_pow]
  rfl

/-- A defective logarithmic CFT Jordan transfer cell is NEVER Hermitian for any `h : ℂ`,
obstructing self-adjoint / OS reflection-positive transfer-semigroup realization. -/
theorem virasoroL0Cell_not_hermitian (h : ℂ) :
    (virasoroL0Cell h)ᴴ ≠ virasoroL0Cell h := by
  intro heq
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) heq
  simp [virasoroL0Cell, upperJordan, Matrix.conjTranspose_apply] at h01

end InfoGeometry.OperatorAlgebra.OsterwalderSchraderPeirceColimitBridge
