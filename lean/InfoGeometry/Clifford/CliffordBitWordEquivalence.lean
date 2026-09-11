import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.PrimonColimitAlgebra
import InfoGeometry.Canonical.FiniteCantorCuntzBranches
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Algebra.FiniteTensorDeterminantStabilization
import InfoGeometry.TraceFormula.DeterminantBondNative
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic

/-!
# Coherent Clifford tensor-tower / BitWord UHF equivalence

This is the finite-to-colimit carrier identification.  The recursive index
equivalence is chosen so that the matrix reindexing commutes with the
one-step tensor-with-identity embeddings.  The universal Cuntz quotient is
not identified with this carrier here; finite matrix units are transported.
-/

noncomputable section

namespace InfoGeometry.Algebra.CliffordBitWordEquivalence

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.FiniteCantorCuntzBranches
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Algebra.FiniteTensorDeterminantStabilization
open scoped Kronecker
open Matrix

abbrev ClStage (n : ℕ) := Cl11TensorTowerLimit.Stage n
abbrev UHFStage (n : ℕ) := PrimonColimitAlgebra.MatrixStage n
abbrev ClCarrier := Cl11TensorTowerLimit.Limit
abbrev UHFCarrier := PrimonColimitAlgebra.PrimonUHFAlgebra

def finTwoEquivBool : Fin 2 ≃ Bool where
  toFun i := i = 1
  invFun b := if b then 1 else 0
  left_inv i := by fin_cases i <;> rfl
  right_inv b := by cases b <;> rfl

def bitWordSuccEquiv (n : ℕ) : BitWord n × Bool ≃ BitWord (n + 1) where
  toFun p := extendSucc n p.1 p.2
  invFun w :=
    (prefixSucc n w,
      InfoGeometry.Canonical.FiniteCantorCuntzBranches.lastBit n w)
  left_inv p := by
    rcases p with ⟨w, b⟩
    apply Prod.ext
    · exact prefixSucc_extendSucc n w b
    · exact
        InfoGeometry.Canonical.FiniteCantorCuntzBranches.lastBit_extendSucc n w b
  right_inv w := by
    simpa using extendSucc_prefixSucc_lastBit n w

def idxBitWordEquiv : (n : ℕ) → TowerMatrix.Idx n ≃ BitWord n
  | 0 =>
      { toFun := fun _ j => Fin.elim0 j
        invFun := fun _ => ⟨0, Nat.zero_lt_succ 0⟩
        left_inv := by
          intro i
          exact Subsingleton.elim _ _
        right_inv := by intro w; funext j; exact Fin.elim0 j }
  | n + 1 =>
      (Equiv.prodCongr (idxBitWordEquiv n) finTwoEquivBool).trans
        (bitWordSuccEquiv n)

@[simp] theorem idxBitWordEquiv_zero_apply (i : TowerMatrix.Idx 0)
    (j : Fin 0) : idxBitWordEquiv 0 i j = Fin.elim0 j := rfl

@[simp] theorem idxBitWordEquiv_succ_apply (n : ℕ)
    (i : TowerMatrix.Idx n) (k : Fin 2) :
    idxBitWordEquiv (n + 1) (i, k) =
      extendSucc n (idxBitWordEquiv n i) (finTwoEquivBool k) := rfl

@[simp] theorem idxBitWordEquiv_succ_symm_apply (n : ℕ)
    (w : BitWord (n + 1)) :
    (idxBitWordEquiv (n + 1)).symm w =
      ((idxBitWordEquiv n).symm (prefixSucc n w),
        (finTwoEquivBool).symm
          (InfoGeometry.Canonical.FiniteCantorCuntzBranches.lastBit n w)) := rfl

noncomputable def clStageEquiv (n : ℕ) : ClStage n ≃ₐ[ℝ] UHFStage n :=
  Matrix.reindexAlgEquiv ℝ ℝ (idxBitWordEquiv n)

@[simp] theorem clStageEquiv_apply (n : ℕ) (A : ClStage n) :
    clStageEquiv n A = Matrix.reindex (idxBitWordEquiv n) (idxBitWordEquiv n) A := rfl

theorem clStageEquiv_trace (n : ℕ) (A : ClStage n) :
    Matrix.trace (clStageEquiv n A) = Matrix.trace A := by
  change
    (∑ v : BitWord n,
      A ((idxBitWordEquiv n).symm v) ((idxBitWordEquiv n).symm v)) =
      ∑ i : TowerMatrix.Idx n, A i i
  exact Equiv.sum_comp (idxBitWordEquiv n).symm (fun i : TowerMatrix.Idx n => A i i)

theorem clStageEquiv_det (n : ℕ) (A : ClStage n) :
    Matrix.det (clStageEquiv n A) = Matrix.det A := by
  change Matrix.det
      (Matrix.reindex (idxBitWordEquiv n) (idxBitWordEquiv n) A) = Matrix.det A
  exact Matrix.det_reindex_self (idxBitWordEquiv n) A

/-! ## The real BitWord/Fin transport

The older finite transport owners use arbitrary `Fintype.equivFin` choices.
The following equivalence is recursive and uses the same successor indexing as
the native tensor-with-identity matrix bond.  This is the finite carrier
equation needed before transporting determinant data to the BitWord tower. -/

def bitWordZeroFinOneEquiv : BitWord 0 ≃ Fin 1 where
  toFun _ := 0
  invFun _ := fun i => Fin.elim0 i
  left_inv := by
    intro w
    funext i
    exact Fin.elim0 i
  right_inv := by
    intro i
    exact Subsingleton.elim _ _

noncomputable def bitWordFinPowTwoEquiv :
    (n : ℕ) → BitWord n ≃ Fin (2 ^ n)
  | 0 => bitWordZeroFinOneEquiv
  | n + 1 =>
      (bitWordSuccEquiv n).symm.trans
        (((bitWordFinPowTwoEquiv n).prodCongr finTwoEquivBool.symm).trans
          (stageIndexEquiv n))

noncomputable def bitWordStageEquivFin (n : ℕ) :
    UHFStage n ≃ₐ[ℝ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ (bitWordFinPowTwoEquiv n)

noncomputable def realFinBondFun (n : ℕ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ →
      Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℝ :=
  fun A => Matrix.reindexAlgEquiv ℝ ℝ (stageIndexEquiv n)
    (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ))

theorem bitWordStageEquivFin_det (n : ℕ) (A : UHFStage n) :
    Matrix.det (bitWordStageEquivFin n A) = Matrix.det A := by
  change Matrix.det
      (Matrix.reindex (bitWordFinPowTwoEquiv n)
        (bitWordFinPowTwoEquiv n) A) = Matrix.det A
  exact Matrix.det_reindex_self (bitWordFinPowTwoEquiv n) A

theorem bitWordStageEquivFin_trace (n : ℕ) (A : UHFStage n) :
    Matrix.trace (bitWordStageEquivFin n A) = Matrix.trace A := by
  change Matrix.trace
      ((Matrix.reindexAlgEquiv ℝ ℝ (bitWordFinPowTwoEquiv n)) A) =
    Matrix.trace A
  exact trace_reindex (bitWordFinPowTwoEquiv n) A

theorem tauInfinity_bitWordStageEquivFin_symm (n : ℕ)
    (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) :
    PrimonColimitAlgebra.tauInfinity
        (PrimonColimitAlgebra.toColimit n
          ((bitWordStageEquivFin n).symm A)) =
      (1 / (2 ^ n : ℝ)) * Matrix.trace A := by
  rw [PrimonColimitAlgebra.tauInfinity_stage]
  unfold PrimonColimitAlgebra.normalizedTrace
    PrimonColimitAlgebra.rawTrace
  have htrace := bitWordStageEquivFin_trace n
    ((bitWordStageEquivFin n).symm A)
  simpa using congrArg (fun x : ℝ => (1 / (2 ^ n : ℝ)) * x) htrace.symm

theorem realFinBondFun_det (n : ℕ)
      (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) :
      Matrix.det (realFinBondFun n A) = (Matrix.det A) ^ 2 := by
    unfold realFinBondFun
    change Matrix.det
        (Matrix.reindex (stageIndexEquiv n) (stageIndexEquiv n)
          (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ))) = (Matrix.det A) ^ 2
    rw [Matrix.det_reindex]
    rw [Matrix.det_kronecker]
    simp

theorem bitWordStageEquivFin_coherent (n : ℕ) (A : UHFStage n) :
    bitWordStageEquivFin (n + 1) (matrixBond n A) =
      realFinBondFun n (bitWordStageEquivFin n A) := by
  ext i j
  cases hi : (stageIndexEquiv n).symm i with
  | mk i₁ i₂ =>
      cases hj : (stageIndexEquiv n).symm j with
      | mk j₁ j₂ =>
          dsimp [bitWordStageEquivFin, realFinBondFun, matrixBond,
            Matrix.reindexAlgEquiv, Matrix.reindex]
          rw [hi, hj]
          change
            (matrixBondFun n A
              ((bitWordFinPowTwoEquiv (n + 1)).symm i)
              ((bitWordFinPowTwoEquiv (n + 1)).symm j)) =
              (bitWordStageEquivFin n A
                i₁ j₁) *
                (1 : Matrix (Fin 2) (Fin 2) ℝ) i₂ j₂
          simp [bitWordStageEquivFin, bitWordFinPowTwoEquiv,
            bitWordSuccEquiv, matrixBondFun, finTwoEquivBool,
            Matrix.kronecker_apply, hi, hj]
          fin_cases i₂ <;> fin_cases j₂ <;>
            simp [extendSucc, prefixSucc, prefixSucc_extendSucc,
              finTwoEquivBool]

theorem clStageEquiv_bond (n : ℕ) (A : ClStage n) :
    clStageEquiv (n + 1) (stageBond n A) =
      PrimonColimitAlgebra.matrixBond n (clStageEquiv n A) := by
  ext v w
  change (stageBond n A)
      ((idxBitWordEquiv (n + 1)).symm v)
      ((idxBitWordEquiv (n + 1)).symm w) = _
  rw [idxBitWordEquiv_succ_symm_apply, idxBitWordEquiv_succ_symm_apply]
  simp only [stageBond, Cl11TensorTower.stageEmbed_apply,
    Cl11TensorTower.matStageEmbed, Matrix.kronecker_apply,
    Matrix.one_apply, clStageEquiv_apply, Matrix.reindex]
  change
    (A ((idxBitWordEquiv n).symm (prefixSucc n v))
        ((idxBitWordEquiv n).symm (prefixSucc n w))) *
      (1 : Matrix (Fin 2) (Fin 2) ℝ)
        ((finTwoEquivBool).symm (v ⟨n, Nat.lt_succ_self n⟩))
        ((finTwoEquivBool).symm (w ⟨n, Nat.lt_succ_self n⟩)) = _
  cases hv : v ⟨n, Nat.lt_succ_self n⟩ <;>
    cases hw : w ⟨n, Nat.lt_succ_self n⟩ <;>
    simp [PrimonColimitAlgebra.matrixBond,
      PrimonColimitAlgebra.matrixBondFun,
      InfoGeometry.Canonical.FiniteCantorCuntzBranches.lastBit,
      hv, hw, finTwoEquivBool, Cl11TensorTower.matStageEmbed,
      Matrix.kronecker_apply]

/-- The coherent Clifford bond is block diagonal in the Cantor branch
    coordinates after the finite-stage reindexing. -/
theorem clStageEquiv_bond_extendSucc (n : ℕ) (A : ClStage n)
    (u v : BitWord n) (b c : Bool) :
    clStageEquiv (n + 1) (stageBond n A)
        (extendSucc n u b) (extendSucc n v c) =
      if b = c then clStageEquiv n A u v else 0 := by
  calc
    clStageEquiv (n + 1) (stageBond n A)
          (extendSucc n u b) (extendSucc n v c) =
        (PrimonColimitAlgebra.matrixBond n (clStageEquiv n A))
          (extendSucc n u b) (extendSucc n v c) := by
            rw [clStageEquiv_bond]
    _ = if b = c then clStageEquiv n A u v else 0 := by
      exact PrimonColimitAlgebra.matrixBondFun_extendSucc n
        (clStageEquiv n A) u v b c

theorem clStageEquiv_bond_det (n : ℕ) (A : ClStage n) :
    Matrix.det (clStageEquiv (n + 1) (stageBond n A)) =
      (Matrix.det (clStageEquiv n A)) ^ 2 := by
  rw [clStageEquiv_bond,
    InfoGeometry.TraceFormula.DeterminantBondNative.matrixBond_det_native]

theorem clStageEquiv_bond_logAbsDet_double (n : ℕ) (A : ClStage n) :
    Real.log |Matrix.det (clStageEquiv (n + 1) (stageBond n A))| =
      2 * Real.log |Matrix.det (clStageEquiv n A)| := by
  rw [clStageEquiv_bond_det, abs_pow, Real.log_pow]
  ring

theorem clStageEquiv_normalizedLogAbsDet_stable (n : ℕ) (A : ClStage n) :
    InfoGeometry.Algebra.FiniteTensorDeterminantStabilization.normalizedLogDet (n + 1)
        (Real.log |Matrix.det (clStageEquiv (n + 1) (stageBond n A))|) =
      InfoGeometry.Algebra.FiniteTensorDeterminantStabilization.normalizedLogDet n
        (Real.log |Matrix.det (clStageEquiv n A)|) := by
  exact InfoGeometry.Algebra.FiniteTensorDeterminantStabilization.normalizedLogDet_tensor_embedding_stable n
    (clStageEquiv_bond_logAbsDet_double n A)

/-- The coherent reindexing does not change the native Clifford
    normalized log-absolute-determinant readout. -/
theorem clStageEquiv_normalizedLogAbsDet_eq_native (n : ℕ) (A : ClStage n) :
    InfoGeometry.Algebra.FiniteTensorDeterminantStabilization.normalizedLogDet n
        (Real.log |Matrix.det (clStageEquiv n A)|) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet n A := by
  unfold InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet
  rw [clStageEquiv_det]

theorem normalizedTrace_clStageEquiv (n : ℕ) (A : ClStage n) :
    PrimonColimitAlgebra.normalizedTrace n (clStageEquiv n A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n A := by
  unfold PrimonColimitAlgebra.normalizedTrace
    PrimonColimitAlgebra.rawTrace
    InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace
  simp only [Matrix.trace, Matrix.diag, clStageEquiv_apply, Matrix.reindex]
  dsimp [Matrix.reindexAlgEquiv]
  have hsum :
      (∑ v : BitWord n,
        A ((idxBitWordEquiv n).symm v) ((idxBitWordEquiv n).symm v)) =
        ∑ i, A i i := by
    exact Equiv.sum_comp (idxBitWordEquiv n).symm (fun i => A i i)
  rw [hsum]
  change (1 / (2 ^ n : ℝ)) *
      (∑ i : TowerMatrix.Idx n, A i i) =
    (∑ i : TowerMatrix.Idx n, A i i) / (2 : ℝ) ^ n
  ring

def clToUHFStageHom (n : ℕ) : ClStage n →+* UHFCarrier :=
  (PrimonColimitAlgebra.toColimit n).comp (clStageEquiv n).toRingHom

theorem clToUHFStageHom_compatible :
    CompatibleCone Cl11TensorTowerLimit.stageBond clToUHFStageHom := by
  intro n A
  change PrimonColimitAlgebra.toColimit (n + 1)
      (clStageEquiv (n + 1) (stageBond n A)) =
    PrimonColimitAlgebra.toColimit n (clStageEquiv n A)
  rw [clStageEquiv_bond, PrimonColimitAlgebra.toColimit_bond]

noncomputable def clToUHF : ClCarrier →+* UHFCarrier :=
  directLimitLift Cl11TensorTowerLimit.stageBond clToUHFStageHom
    clToUHFStageHom_compatible

@[simp] theorem clToUHF_ofStage (n : ℕ) (A : ClStage n) :
    clToUHF (Cl11TensorTowerLimit.ofStage n A) =
      PrimonColimitAlgebra.toColimit n (clStageEquiv n A) := by
  exact directLimitLift_of _ _ _ n A

def uhfToClStageHom (n : ℕ) : UHFStage n →+* ClCarrier :=
  (Cl11TensorTowerLimit.ofStage n).comp (clStageEquiv n).symm.toRingHom

theorem uhfToClStageHom_compatible :
    CompatibleCone PrimonColimitAlgebra.matrixBond uhfToClStageHom := by
  intro n A
  change Cl11TensorTowerLimit.ofStage (n + 1)
      ((clStageEquiv (n + 1)).symm (PrimonColimitAlgebra.matrixBond n A)) =
    Cl11TensorTowerLimit.ofStage n ((clStageEquiv n).symm A)
  have hstage :
      (clStageEquiv (n + 1)).symm (PrimonColimitAlgebra.matrixBond n A) =
        Cl11TensorTowerLimit.stageBond n ((clStageEquiv n).symm A) := by
    apply (clStageEquiv (n + 1)).injective
    rw [clStageEquiv_bond]
    simp
  calc
    _ = Cl11TensorTowerLimit.ofStage (n + 1)
        (Cl11TensorTowerLimit.stageBond n ((clStageEquiv n).symm A)) :=
      congrArg (Cl11TensorTowerLimit.ofStage (n + 1)) hstage
    _ = Cl11TensorTowerLimit.ofStage n ((clStageEquiv n).symm A) :=
      Cl11TensorTowerLimit.ofStage_apply_bond n ((clStageEquiv n).symm A)

noncomputable def uhfToCl : UHFCarrier →+* ClCarrier :=
  directLimitLift PrimonColimitAlgebra.matrixBond uhfToClStageHom
    uhfToClStageHom_compatible

@[simp] theorem uhfToCl_toColimit (n : ℕ) (A : UHFStage n) :
    uhfToCl (PrimonColimitAlgebra.toColimit n A) =
      Cl11TensorTowerLimit.ofStage n ((clStageEquiv n).symm A) := by
  exact directLimitLift_of _ _ _ n A

noncomputable def cliffordBitWordColimitEquiv : ClCarrier ≃+* UHFCarrier where
  toFun := clToUHF
  invFun := uhfToCl
  left_inv := by
    intro x
    induction x using DirectLimit.induction with
    | _ n A =>
        change uhfToCl (clToUHF (Cl11TensorTowerLimit.ofStage n A)) = _
        rw [clToUHF_ofStage, uhfToCl_toColimit]
        exact congrArg (Cl11TensorTowerLimit.ofStage n)
          ((clStageEquiv n).symm_apply_apply A)
  right_inv := by
    intro x
    induction x using DirectLimit.induction with
    | _ n A =>
        change clToUHF (uhfToCl (PrimonColimitAlgebra.toColimit n A)) = _
        rw [uhfToCl_toColimit, clToUHF_ofStage]
        exact congrArg (PrimonColimitAlgebra.toColimit n)
          ((clStageEquiv n).apply_symm_apply A)
  map_add' := map_add clToUHF
  map_mul' := map_mul clToUHF

@[simp] theorem cliffordBitWordColimitEquiv_ofStage (n : ℕ) (A : ClStage n) :
    cliffordBitWordColimitEquiv (Cl11TensorTowerLimit.ofStage n A) =
      PrimonColimitAlgebra.toColimit n (clStageEquiv n A) := by
  exact clToUHF_ofStage n A

@[simp] theorem cliffordBitWordColimitEquiv_ofStage_symm (n : ℕ)
    (A : UHFStage n) :
    cliffordBitWordColimitEquiv
        (Cl11TensorTowerLimit.ofStage n ((clStageEquiv n).symm A)) =
      PrimonColimitAlgebra.toColimit n A := by
  rw [cliffordBitWordColimitEquiv_ofStage]
  simp

def cuntzCoreUnit (n : ℕ) (u v : BitWord n) : UHFStage n :=
  Matrix.single u v (1 : ℝ)

def bitWordKet (n : ℕ) (u : BitWord n) : BitWord n → ℝ :=
  Pi.single u 1

theorem cuntzCoreUnit_mulVec_bitWordKet (n : ℕ)
    (u v x : BitWord n) :
    (cuntzCoreUnit n u v) *ᵥ bitWordKet n x =
      if v = x then bitWordKet n u else 0 := by
  change (Matrix.single u v (1 : ℝ)) *ᵥ (Pi.single x 1) =
    if v = x then Pi.single u 1 else 0
  rw [Matrix.mulVec_single_one]
  funext z
  by_cases hvx : v = x
  · by_cases hzu : z = u
    · simp [Matrix.single_apply, Pi.single_apply, hvx, hzu]
    · have hzu' : ¬u = z := by
        intro h
        exact hzu h.symm
      simp [Matrix.single_apply, Pi.single_apply, hvx, hzu, hzu']
  · by_cases hzu : z = u
    · simp [Matrix.single_apply, Pi.single_apply, hvx, hzu]
    · have hzu' : ¬u = z := by
        intro h
        exact hzu h.symm
      simp [Matrix.single_apply, Pi.single_apply, hvx, hzu, hzu']

def cl11CuntzCoreUnit (n : ℕ) (u v : BitWord n) : ClStage n :=
  (clStageEquiv n).symm (cuntzCoreUnit n u v)

theorem cl11CuntzCoreUnit_mul (n : ℕ)
    (u v x y : BitWord n) :
    cl11CuntzCoreUnit n u v * cl11CuntzCoreUnit n x y =
      if v = x then cl11CuntzCoreUnit n u y else 0 := by
  apply (clStageEquiv n).injective
  calc
    (clStageEquiv n)
        (cl11CuntzCoreUnit n u v * cl11CuntzCoreUnit n x y) =
      (clStageEquiv n) (cl11CuntzCoreUnit n u v) *
        (clStageEquiv n) (cl11CuntzCoreUnit n x y) :=
      (clStageEquiv n).map_mul _ _
    _ = cuntzCoreUnit n u v * cuntzCoreUnit n x y := by
      simp [cl11CuntzCoreUnit, cuntzCoreUnit]
    _ = (clStageEquiv n)
        (if v = x then cl11CuntzCoreUnit n u y else 0) := by
      by_cases h : v = x
      · subst x
        simp only [if_pos rfl, cl11CuntzCoreUnit,
          AlgEquiv.apply_symm_apply, cuntzCoreUnit]
        simpa using
          (Matrix.single_mul_mul_single u v v y (1 : ℝ)
            (1 : Matrix (BitWord n) (BitWord n) ℝ) (1 : ℝ))
      · simp only [if_neg h, cl11CuntzCoreUnit, cuntzCoreUnit, map_zero]
        exact Matrix.single_mul_single_of_ne (c := (1 : ℝ)) u v x h (1 : ℝ)

theorem tauInfinity_cuntzCoreUnit (n : ℕ) (u v : BitWord n) :
    tauInfinity (PrimonColimitAlgebra.toColimit n (cuntzCoreUnit n u v)) =
      if u = v then (1 / (2 ^ n : ℝ)) else 0 := by
  rw [PrimonColimitAlgebra.tauInfinity_stage]
  unfold PrimonColimitAlgebra.normalizedTrace
    PrimonColimitAlgebra.rawTrace cuntzCoreUnit
  by_cases h : u = v
  · subst v
    simp [Matrix.trace_single_eq_same]
  · simp [h, Matrix.trace_single_eq_of_ne]

theorem tauInfinity_cliffordCuntzCoreUnit (n : ℕ) (u v : BitWord n) :
    tauInfinity
        (cliffordBitWordColimitEquiv
          (Cl11TensorTowerLimit.ofStage n (cl11CuntzCoreUnit n u v))) =
      if u = v then (1 / (2 ^ n : ℝ)) else 0 := by
  rw [cliffordBitWordColimitEquiv_ofStage]
  simp only [cl11CuntzCoreUnit, AlgEquiv.apply_symm_apply]
  exact tauInfinity_cuntzCoreUnit n u v

/-! The one-step commuting square iterates along the entire directed system. -/

theorem clStageEquiv_bondMap
    (m n : ℕ) (h : m ≤ n) (A : ClStage m) :
    clStageEquiv n (bondMap stageBond m n h A) =
      bondMap PrimonColimitAlgebra.matrixBond m n h
        (clStageEquiv m A) := by
  refine Nat.le_induction
    (m := m)
    (P := fun k hk =>
      clStageEquiv k (bondMap stageBond m k hk A) =
        bondMap PrimonColimitAlgebra.matrixBond m k hk
          (clStageEquiv m A))
    ?base ?succ n h
  · simp [bondMap_refl]
  · intro k hmk ih
    rw [bondMap_succ stageBond m k hmk,
      bondMap_succ PrimonColimitAlgebra.matrixBond m k hmk]
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [clStageEquiv_bond]
    exact congrArg (PrimonColimitAlgebra.matrixBond k) ih

/-! Normalized trace transport follows the coherent matrix-stage equivalence. -/

theorem normalizedTrace_clStageEquiv_bondMap
    (m n : ℕ) (h : m ≤ n) (A : ClStage m) :
    PrimonColimitAlgebra.normalizedTrace n
        (clStageEquiv n (bondMap stageBond m n h A)) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace m A := by
  rw [clStageEquiv_bondMap m n h A]
  rw [PrimonColimitAlgebra.normalizedTrace_compatible_bondMap m n h]
  exact normalizedTrace_clStageEquiv m A

end InfoGeometry.Algebra.CliffordBitWordEquivalence
