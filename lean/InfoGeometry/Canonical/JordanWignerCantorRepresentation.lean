import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Canonical.JordanWignerCelikKocakBridgeNDepth
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Clifford.MatToCantorOperator
import InfoGeometry.Canonical.GeometricMonodromy

/-!
This file contains two theorem-backed finite-stage representations.

* `realMatToCantor` is the existing real matrix/operator algebra equivalence
  `MatStage n ≃ₐ[ℝ] Module.End ℝ (Idx n → ℝ)`.
* `complexMatToCantor` is a concrete algebra homomorphism
  `MatStage n →ₐ[ℝ] CantorOp n`, obtained by entrywise complexification,
  reindexing from tower indices to finite Cantor addresses, and
  `Matrix.toLinAlgEquiv` over the endpoint-function basis.
* `globalRealCantorAlgEquiv` and `globalCantorInverseEquiv` are the
  direct-limit algebra equivalences induced by the finite real bridge.
* `hestenesBivectorInf` and `realCantorBivectorInf` are the global real
  Hestenes--Krein phase and its Cantor-side image.
* `hestenesBivectorTransport_two_pi`,
  `realCantorBivectorTransport_two_pi`,
  `hestenesBivectorTransport_four_pi`, and
  `realCantorBivectorTransport_four_pi` specialize the generic spinorial
  monodromy theorem to those two global phases.

The pointwise theorem identifying `complexMatToCantor n (jwCreation n k)` with
`cantorCreation n k`, and similarly for annihilation, is not asserted here; this
file proves the finite algebra maps and the real direct-limit equivalences.
-/

noncomputable section

namespace JordanWignerCantorRepresentation

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.CelikKocakCantorOperators
open InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace
open InfoGeometry.Canonical.JordanWignerCelikKocakBridgeNDepth

/-- Real finite Cantor operator algebra at depth `n`, using the tower's native indices. -/
abbrev RealCantorOp (n : ℕ) := InfoGeometry.Clifford.MatToCantorOperator.RealCantorOp n

/-- The already-closed real finite matrix/operator algebra equivalence. -/
noncomputable def realMatToCantor (n : ℕ) : MatStage n ≃ₐ[ℝ] RealCantorOp n :=
  InfoGeometry.Clifford.MatToCantorOperator.matToCantor n

@[simp] theorem realMatToCantor_apply (n : ℕ) (A : MatStage n) :
    realMatToCantor n A = Matrix.toLin' A :=
  rfl

@[simp] theorem realMatToCantor_map_one (n : ℕ) :
    realMatToCantor n (1 : MatStage n) = (1 : RealCantorOp n) :=
  InfoGeometry.Clifford.MatToCantorOperator.matToCantor_map_one n

@[simp] theorem realMatToCantor_map_mul (n : ℕ) (A B : MatStage n) :
    realMatToCantor n (A * B) = realMatToCantor n A * realMatToCantor n B :=
  InfoGeometry.Clifford.MatToCantorOperator.matToCantor_map_mul n A B

@[simp] theorem realMatToCantor_map_add (n : ℕ) (A B : MatStage n) :
    realMatToCantor n (A + B) = realMatToCantor n A + realMatToCantor n B :=
  InfoGeometry.Clifford.MatToCantorOperator.matToCantor_map_add n A B

@[simp] theorem realMatToCantor_map_smul (n : ℕ) (c : ℝ) (A : MatStage n) :
    realMatToCantor n (c • A) = c • realMatToCantor n A :=
  InfoGeometry.Clifford.MatToCantorOperator.matToCantor_map_smul n c A

/-- The finite real matrix/operator map is injective. -/
theorem realMatToCantor_injective (n : ℕ) : Function.Injective (realMatToCantor n) :=
  (realMatToCantor n).injective

/-- The real operator-side transition transported from the matrix tower. -/
noncomputable def realCantorOpEmbed (n : ℕ) : RealCantorOp n →ₐ[ℝ] RealCantorOp (n + 1) :=
  InfoGeometry.Clifford.MatToCantorOperator.cantorOpEmbed n

/-- The real finite matrix/operator equivalences commute with one-step embeddings. -/
theorem realCantorOpEmbed_realMatToCantor (n : ℕ) (A : MatStage n) :
    realCantorOpEmbed n (realMatToCantor n A) =
      realMatToCantor (n + 1) (matStageEmbed n A) :=
  InfoGeometry.Clifford.MatToCantorOperator.cantorOpEmbed_matToCantor n A

/-- The inverse finite operator/matrix equivalences commute with one-step embeddings. -/
theorem realMatToCantor_symm_realCantorOpEmbed (n : ℕ) (X : RealCantorOp n) :
    matStageEmbed n ((realMatToCantor n).symm X) =
      (realMatToCantor (n + 1)).symm (realCantorOpEmbed n X) := by
  apply (realMatToCantor (n + 1)).injective
  rw [← realCantorOpEmbed_realMatToCantor n ((realMatToCantor n).symm X)]
  simp

/-- The binary tower index set and the finite Cantor-address set have the same cardinality. -/
theorem idx_card_eq_cantorAddress_card (n : ℕ) :
    Fintype.card (Idx n) = Fintype.card (CantorAddress n) := by
  induction n with
  | zero => simp [Idx, CantorAddress]
  | succ n ih =>
      simp [Idx, CantorAddress, ih, pow_succ, Nat.mul_comm]

/-- Canonical Boolean encoding of `Fin 2`. -/
def fin2EquivBool : Fin 2 ≃ Bool where
  toFun i := i = 1
  invFun b := if b then 1 else 0
  left_inv := by
    intro i
    fin_cases i <;> simp
  right_inv := by
    intro b
    cases b <;> simp

/-- Canonical orientation equivalence from tower indices to finite Cantor addresses. -/
def idxEquivCantorAddress : (n : ℕ) → Idx n ≃ CantorAddress n
  | 0 =>
      { toFun := fun _ i => Fin.elim0 i
        invFun := fun _ => default
        left_inv := by
          intro i
          fin_cases i
          rfl
        right_inv := by
          intro x
          funext i
          exact Fin.elim0 i }
  | n + 1 =>
      { toFun := fun p k =>
          if hk : (k : ℕ) < n then
            idxEquivCantorAddress n p.1 ⟨k, hk⟩
          else
            fin2EquivBool p.2
        invFun := fun x =>
          ( (idxEquivCantorAddress n).symm (fun k => x k.castSucc)
          , fin2EquivBool.symm (x (Fin.last n)) )
        left_inv := by
          intro p
          rcases p with ⟨i, b⟩
          apply Prod.ext
          · apply (idxEquivCantorAddress n).injective
            ext k
            have hk : ((Fin.castSucc k : Fin (n + 1)) : ℕ) < n := k.isLt
            simp
          · have hlast : ¬ ((Fin.last n : Fin (n + 1)) : ℕ) < n := by
              simp
            simp
        right_inv := by
          intro x
          funext k
          by_cases hk : (k : ℕ) < n
          · have hk_cast : (Fin.castSucc ⟨(k : ℕ), hk⟩ : Fin (n + 1)) = k := by
              apply Fin.ext
              rfl
            simp [hk, hk_cast]
          · have hk_last : k = Fin.last n := by
              apply Fin.ext
              exact le_antisymm (Nat.lt_succ_iff.mp k.isLt) (Nat.ge_of_not_lt hk)
            simp [hk_last] }

@[simp] theorem idxEquivCantorAddress_castSucc (n : ℕ) (p : Idx n) (b : Fin 2) (k : Fin n) :
    idxEquivCantorAddress (n + 1) (p, b) k.castSucc = idxEquivCantorAddress n p k := by
  have hk : ((k.castSucc : Fin (n + 1)) : ℕ) < n := k.isLt
  simp [idxEquivCantorAddress]

@[simp] theorem idxEquivCantorAddress_last (n : ℕ) (p : Idx n) (b : Fin 2) :
    idxEquivCantorAddress (n + 1) (p, b) (Fin.last n) = fin2EquivBool b := by
  have hlast : ¬ ((Fin.last n : Fin (n + 1)) : ℕ) < n := by
    simp
  simp [idxEquivCantorAddress]

/-- Entrywise complexification as an `ℝ`-algebra homomorphism. -/
noncomputable def complexifyMatrixAlgHom (n : ℕ) :
    MatStage n →ₐ[ℝ] Matrix (Idx n) (Idx n) ℂ where
  toFun A := (algebraMap ℝ ℂ).mapMatrix A
  map_one' := by
    ext i j
    by_cases h : i = j <;> simp [RingHom.mapMatrix_apply, Matrix.one_apply, h]
  map_mul' A B := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.mul_apply, map_mul]
  map_zero' := by
    ext i j
    simp [RingHom.mapMatrix_apply]
  map_add' A B := by
    ext i j
    simp [RingHom.mapMatrix_apply]
  commutes' r := by
    ext i j
    by_cases h : i = j <;> simp [RingHom.mapMatrix_apply, Matrix.algebraMap_eq_diagonal, h]

/-- Complexified and reindexed matrix representation over finite Cantor addresses. -/
noncomputable def complexMatToMatrix (n : ℕ) :
    MatStage n →ₐ[ℝ] Matrix (CantorAddress n) (CantorAddress n) ℂ :=
  (Matrix.reindexAlgEquiv ℝ ℂ (idxEquivCantorAddress n)).toAlgHom.comp
    (complexifyMatrixAlgHom n)

/-- Concrete finite-stage algebra homomorphism into complex Cantor endpoint operators. -/
noncomputable def complexMatToCantor (n : ℕ) : MatStage n →ₐ[ℝ] CantorOp n :=
  ((Matrix.toLinAlgEquiv (Pi.basisFun ℂ (CantorAddress n))).toAlgHom.restrictScalars ℝ).comp
    (complexMatToMatrix n)

@[simp] theorem complexMatToCantor_map_one (n : ℕ) :
    complexMatToCantor n (1 : MatStage n) = (1 : CantorOp n) := by
  simp [complexMatToCantor]

@[simp] theorem complexMatToCantor_map_mul (n : ℕ) (A B : MatStage n) :
    complexMatToCantor n (A * B) = complexMatToCantor n A * complexMatToCantor n B := by
  simp [complexMatToCantor]

@[simp] theorem complexMatToCantor_map_zero (n : ℕ) :
    complexMatToCantor n (0 : MatStage n) = (0 : CantorOp n) := by
  simp [complexMatToCantor]

@[simp] theorem complexMatToCantor_map_add (n : ℕ) (A B : MatStage n) :
    complexMatToCantor n (A + B) = complexMatToCantor n A + complexMatToCantor n B := by
  simp [complexMatToCantor]

/-- The complex finite matrix/Cantor-operator map is injective. -/
theorem complexMatToCantor_injective (n : ℕ) : Function.Injective (complexMatToCantor n) := by
  intro A B h
  have hmat : complexMatToMatrix n A = complexMatToMatrix n B := by
    exact ((Matrix.toLinAlgEquiv (Pi.basisFun ℂ (CantorAddress n))).toAlgHom.restrictScalars ℝ).injective h
  have hidx : complexifyMatrixAlgHom n A = complexifyMatrixAlgHom n B := by
    exact (Matrix.reindexAlgEquiv ℝ ℂ (idxEquivCantorAddress n)).injective hmat
  ext i j
  have hij := congrFun (congrFun hidx i) j
  simpa [complexifyMatrixAlgHom, RingHom.mapMatrix_apply] using
    (Complex.ofReal_injective hij)

/-- The real-encoded Hestenes-Witt creation string has the same finite real
operator image as the native creation string. -/
theorem realMatToCantor_jwRealEncodedCreation_eq (n : ℕ) (k : Fin n) :
    realMatToCantor n (jwRealEncodedCreation n k) = realMatToCantor n (jwCreation n k) := by
  rw [jwRealEncodedCreation_eq]

/-- The real-encoded Hestenes-Witt annihilation string has the same finite real
operator image as the native annihilation string. -/
theorem realMatToCantor_jwRealEncodedAnnihilation_eq (n : ℕ) (k : Fin n) :
    realMatToCantor n (jwRealEncodedAnnihilation n k) = realMatToCantor n (jwAnnihilation n k) := by
  rw [jwRealEncodedAnnihilation_eq]

/-- The real Cantor operator transition preserves real-encoded creation strings. -/
theorem realCantorOpEmbed_jwRealEncodedCreation {n : ℕ} (k : Fin n) :
    realCantorOpEmbed n (realMatToCantor n (jwRealEncodedCreation n k)) =
      realMatToCantor (n + 1) (jwRealEncodedCreation (n + 1) k.castSucc) := by
  rw [realCantorOpEmbed_realMatToCantor]
  exact congrArg (realMatToCantor (n + 1)) (matStageEmbed_jwRealEncodedCreation k)

/-- The real Cantor operator transition preserves real-encoded annihilation strings. -/
theorem realCantorOpEmbed_jwRealEncodedAnnihilation {n : ℕ} (k : Fin n) :
    realCantorOpEmbed n (realMatToCantor n (jwRealEncodedAnnihilation n k)) =
      realMatToCantor (n + 1) (jwRealEncodedAnnihilation (n + 1) k.castSucc) := by
  rw [realCantorOpEmbed_realMatToCantor]
  exact congrArg (realMatToCantor (n + 1)) (matStageEmbed_jwRealEncodedAnnihilation k)


/-! ## Global direct-limit equivalence for the real finite bridge -/

/-- The one-step bond for the real Cantor operator tower. -/
abbrev realCantorBond : ∀ n : ℕ, RealCantorOp n →+* RealCantorOp (n + 1) :=
  fun n => (realCantorOpEmbed n).toRingHom

/-- The real Cantor operator direct limit. -/
abbrev RealCantorOpInf : Type :=
  DirectLimitSuperClosure (Stage := RealCantorOp) realCantorBond

/-- Canonical insertion into the real Cantor operator direct limit. -/
def realCantorOfStage (n : ℕ) : RealCantorOp n →+* RealCantorOpInf :=
  directLimitOf (Stage := RealCantorOp) realCantorBond n

/-- The base-ring action on the real Cantor operator direct limit, induced from stage zero. -/
noncomputable def realCantorAlgebraMap : ℝ →+* RealCantorOpInf :=
  (realCantorOfStage 0).comp (algebraMap ℝ (RealCantorOp 0))

/-- The scalar embedding into the real Cantor direct limit is independent of stage. -/
@[simp] theorem realCantorAlgebraMap_stage (n : ℕ) (r : ℝ) :
    realCantorAlgebraMap r = realCantorOfStage n (algebraMap ℝ (RealCantorOp n) r) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        realCantorAlgebraMap r = realCantorOfStage n (algebraMap ℝ (RealCantorOp n) r) := ih
        _ = realCantorOfStage (n + 1)
              (realCantorOpEmbed n (algebraMap ℝ (RealCantorOp n) r)) := by
              symm
              exact directLimitOf_bond (Stage := RealCantorOp) realCantorBond n
                (algebraMap ℝ (RealCantorOp n) r)
        _ = realCantorOfStage (n + 1) (algebraMap ℝ (RealCantorOp (n + 1)) r) := by
              rw [← AlgHom.commutes (realCantorOpEmbed n) r]

noncomputable instance : Algebra ℝ RealCantorOpInf :=
  RingHom.toAlgebra' realCantorAlgebraMap (by
    intro r x
    induction x using DirectLimit.induction with
    | _ n x =>
        rw [realCantorAlgebraMap_stage]
        simpa using congrArg (realCantorOfStage n) (Algebra.commutes r x))

/-- The inverse finite maps commute with the one-step bonds. -/
theorem realMatToCantor_symm_compat (n : ℕ) (X : RealCantorOp n) :
    matStageEmbed n ((realMatToCantor n).symm X) =
      (realMatToCantor (n + 1)).symm (realCantorOpEmbed n X) := by
  have h := realCantorOpEmbed_realMatToCantor n ((realMatToCantor n).symm X)
  rw [(realMatToCantor n).apply_symm_apply] at h
  calc
    matStageEmbed n ((realMatToCantor n).symm X)
        = (realMatToCantor (n + 1)).symm
            (realMatToCantor (n + 1) (matStageEmbed n ((realMatToCantor n).symm X))) := by
              exact ((realMatToCantor (n + 1)).symm_apply_apply _).symm
    _ = (realMatToCantor (n + 1)).symm (realCantorOpEmbed n X) := by
              rw [← h]

/-- Matrix-to-real-Cantor finite cone. -/
noncomputable def matToRealCantorCone (n : ℕ) : Stage n →+* RealCantorOpInf :=
  (realCantorOfStage n).comp (realMatToCantor n).toRingHom

/-- The matrix-to-real-Cantor finite cone is compatible with matrix bonds. -/
theorem matToRealCantorCone_compat (n : ℕ) (A : Stage n) :
    matToRealCantorCone (n + 1) (stageBond n A) = matToRealCantorCone n A := by
  calc
    matToRealCantorCone (n + 1) (stageBond n A)
        = realCantorOfStage (n + 1) (realMatToCantor (n + 1) (matStageEmbed n A)) := by
            rfl
    _ = realCantorOfStage (n + 1) (realCantorOpEmbed n (realMatToCantor n A)) := by
            rw [realCantorOpEmbed_realMatToCantor]
    _ = realCantorOfStage n (realMatToCantor n A) := by
            exact directLimitOf_bond (Stage := RealCantorOp) realCantorBond n (realMatToCantor n A)
    _ = matToRealCantorCone n A := by
            rfl

/-- Global direct-limit map from the matrix tower to the real Cantor operator tower. -/
noncomputable def matToRealCantorLimit : Limit →+* RealCantorOpInf :=
  directLimitLift (Stage := Stage) stageBond matToRealCantorCone
    (by intro n A; exact matToRealCantorCone_compat n A)

/-- Real-Cantor-to-matrix finite cone. -/
noncomputable def realCantorToMatCone (n : ℕ) : RealCantorOp n →+* Limit :=
  (ofStage n).comp (realMatToCantor n).symm.toRingHom

/-- The real-Cantor-to-matrix finite cone is compatible with real Cantor bonds. -/
theorem realCantorToMatCone_compat (n : ℕ) (X : RealCantorOp n) :
    realCantorToMatCone (n + 1) (realCantorBond n X) = realCantorToMatCone n X := by
  calc
    realCantorToMatCone (n + 1) (realCantorBond n X)
        = ofStage (n + 1) ((realMatToCantor (n + 1)).symm (realCantorOpEmbed n X)) := by
            rfl
    _ = ofStage (n + 1) (matStageEmbed n ((realMatToCantor n).symm X)) := by
            rw [← realMatToCantor_symm_compat]
    _ = ofStage n ((realMatToCantor n).symm X) := by
            exact ofStage_apply_bond n ((realMatToCantor n).symm X)
    _ = realCantorToMatCone n X := by
            rfl

/-- Global inverse map from the real Cantor operator direct limit back to the
matrix-tower direct limit. -/
noncomputable def realCantorToMatLimit : RealCantorOpInf →+* Limit :=
  directLimitLift (Stage := RealCantorOp) realCantorBond realCantorToMatCone
    (by intro n X; exact realCantorToMatCone_compat n X)

@[simp] theorem matToRealCantorLimit_ofStage (n : ℕ) (A : Stage n) :
    matToRealCantorLimit (ofStage n A) = realCantorOfStage n (realMatToCantor n A) := by
  rfl

@[simp] theorem realCantorToMatLimit_ofStage (n : ℕ) (X : RealCantorOp n) :
    realCantorToMatLimit (realCantorOfStage n X) = ofStage n ((realMatToCantor n).symm X) := by
  rfl

set_option synthInstance.maxHeartbeats 80000 in
/-- The two global direct-limit maps are inverse ring homomorphisms.  This is the
kernel-checked algebraic global equivalence underlying the finite
`realMatToCantor` bridge. -/
noncomputable def globalRealCantorRingEquiv : Limit ≃+* RealCantorOpInf where
  toFun := matToRealCantorLimit
  invFun := realCantorToMatLimit
  left_inv := by
    intro x
    induction x using DirectLimit.induction with
    | _ n A =>
        change realCantorToMatLimit (matToRealCantorLimit (ofStage n A)) = ofStage n A
        rw [matToRealCantorLimit_ofStage, realCantorToMatLimit_ofStage]
        have hsymm : (realMatToCantor n).symm (Matrix.toLin' A) = A := by
          rw [← realMatToCantor_apply n A]
          exact (realMatToCantor n).symm_apply_apply A
        exact congrArg (ofStage n) hsymm
  right_inv := by
    intro x
    induction x using DirectLimit.induction with
    | _ n X =>
        change matToRealCantorLimit (realCantorToMatLimit (realCantorOfStage n X)) =
          realCantorOfStage n X
        rw [realCantorToMatLimit_ofStage, matToRealCantorLimit_ofStage]
        rw [(realMatToCantor n).apply_symm_apply]
  map_mul' := map_mul matToRealCantorLimit
  map_add' := map_add matToRealCantorLimit

/-- The global matrix-to-real-Cantor map preserves real scalars. -/
theorem matToRealCantorLimit_commutes (r : ℝ) :
    globalRealCantorRingEquiv (algebraMap ℝ Limit r) = algebraMap ℝ RealCantorOpInf r := by
  change matToRealCantorLimit (InfoGeometry.Clifford.Cl11TensorTowerLimit.realAlgebraMap r) =
    realCantorAlgebraMap r
  rw [InfoGeometry.Clifford.Cl11TensorTowerLimit.realAlgebraMap_stage 0 r]
  rw [realCantorAlgebraMap_stage 0 r]
  rw [matToRealCantorLimit_ofStage]
  rw [(realMatToCantor 0).commutes r]

/-- Global algebra isomorphism induced by the coherent finite real matrix/Cantor equivalences. -/
noncomputable def globalRealCantorAlgEquiv : Limit ≃ₐ[ℝ] RealCantorOpInf :=
  AlgEquiv.ofRingEquiv (f := globalRealCantorRingEquiv) matToRealCantorLimit_commutes

/-- The global inverse algebra isomorphism lifting real Cantor operators back to the matrix tower. -/
noncomputable def globalCantorInverseEquiv : RealCantorOpInf ≃ₐ[ℝ] Limit :=
  globalRealCantorAlgEquiv.symm

@[simp] theorem globalRealCantorAlgEquiv_ofStage (n : ℕ) (A : Stage n) :
    globalRealCantorAlgEquiv (ofStage n A) = realCantorOfStage n (realMatToCantor n A) := by
  rfl

@[simp] theorem globalCantorInverseEquiv_ofStage (n : ℕ) (X : RealCantorOp n) :
    globalCantorInverseEquiv (realCantorOfStage n X) = ofStage n ((realMatToCantor n).symm X) := by
  rfl

/-! ## Global Hestenes--Krein bivector phase in the real colimit -/

/-- The first-stage real Hestenes phase generator used as the finite
representative of the global bivector. -/
noncomputable def hestenesBivectorStage : Stage 1 :=
  hestenesPhaseHead 0

/-- The first-stage Hestenes bivector squares to `-1`. -/
theorem hestenesBivectorStage_sq :
    hestenesBivectorStage * hestenesBivectorStage = -(1 : Stage 1) := by
  change hestenesPhaseHead 0 * hestenesPhaseHead 0 = -(1 : Stage 1)
  change (InfoGeometry.Clifford.TowerMatrix.kronPow hestenesPhaseBase 1) *
      (InfoGeometry.Clifford.TowerMatrix.kronPow hestenesPhaseBase 1) =
        -(1 : Stage 1)
  dsimp [InfoGeometry.Clifford.TowerMatrix.kronPow]
  rw [← Matrix.mul_kronecker_mul]
  rw [hestenesPhaseBase_sq]
  ext i j
  cases i with
  | mk i0 i1 =>
      cases j with
      | mk j0 j1 =>
          have h0 : i0 = j0 := Subsingleton.elim _ _
          subst h0
          fin_cases i0
          fin_cases i1 <;> fin_cases j1 <;> simp

/-- The global real Hestenes--Krein bivector phase in the matrix-tower colimit. -/
noncomputable def hestenesBivectorInf : Limit :=
  ofStage 1 hestenesBivectorStage

/-- The global Hestenes--Krein phase squares to `-1` in the real matrix colimit. -/
theorem hestenesBivectorInf_sq :
    hestenesBivectorInf * hestenesBivectorInf = -(1 : Limit) := by
  unfold hestenesBivectorInf
  rw [← map_mul]
  rw [hestenesBivectorStage_sq]
  rw [map_neg, map_one]

/-- The corresponding global real Cantor-operator phase, obtained by the proven
colimit bridge. -/
noncomputable def realCantorBivectorInf : RealCantorOpInf :=
  globalRealCantorAlgEquiv hestenesBivectorInf

/-- The real Cantor-operator phase also squares to `-1`. -/
theorem realCantorBivectorInf_sq :
    realCantorBivectorInf * realCantorBivectorInf = -(1 : RealCantorOpInf) := by
  unfold realCantorBivectorInf
  rw [← map_mul]
  rw [hestenesBivectorInf_sq]
  rw [map_neg, map_one]

/-- Pulling the Cantor-side global phase back through the global inverse algebra
equivalence recovers the matrix-colimit bivector representative. -/
theorem globalCantorInverseEquiv_realCantorBivectorInf :
    globalCantorInverseEquiv realCantorBivectorInf = hestenesBivectorInf := by
  simp [globalCantorInverseEquiv, realCantorBivectorInf]

/-! ## Spinorial monodromy readout for the global Hestenes phase -/

/-- Matrix-colimit half-angle transport generated by the global Hestenes phase. -/
noncomputable def hestenesBivectorTransport (θ : ℝ) : Limit :=
  InfoGeometry.Canonical.GeometricMonodromy.spinorTransport hestenesBivectorInf θ

/-- Cantor-operator half-angle transport generated by the transported global phase. -/
noncomputable def realCantorBivectorTransport (θ : ℝ) : RealCantorOpInf :=
  InfoGeometry.Canonical.GeometricMonodromy.spinorTransport realCantorBivectorInf θ

/-- A full `2π` loop gives the spinorial parity flip in the matrix colimit. -/
theorem hestenesBivectorTransport_two_pi :
    hestenesBivectorTransport (2 * Real.pi) = -(1 : Limit) := by
  exact InfoGeometry.Canonical.GeometricMonodromy.spinorial_monodromy_around_pole
    hestenesBivectorInf

set_option synthInstance.maxHeartbeats 80000 in
/-- A full `2π` loop gives the spinorial parity flip in the real Cantor colimit. -/
theorem realCantorBivectorTransport_two_pi :
    realCantorBivectorTransport (2 * Real.pi) = -(1 : RealCantorOpInf) := by
  exact InfoGeometry.Canonical.GeometricMonodromy.spinorial_monodromy_around_pole
    realCantorBivectorInf

/-- Two full loops, i.e. `4π`, return the matrix-colimit spinor phase to `+1`. -/
theorem hestenesBivectorTransport_four_pi :
    hestenesBivectorTransport (4 * Real.pi) = (1 : Limit) := by
  exact InfoGeometry.Canonical.GeometricMonodromy.spinorial_double_loop_identity
    hestenesBivectorInf

set_option synthInstance.maxHeartbeats 80000 in
/-- Two full loops, i.e. `4π`, return the Cantor-colimit spinor phase to `+1`. -/
theorem realCantorBivectorTransport_four_pi :
    realCantorBivectorTransport (4 * Real.pi) = (1 : RealCantorOpInf) := by
  exact InfoGeometry.Canonical.GeometricMonodromy.spinorial_double_loop_identity
    realCantorBivectorInf

/- 
/-- The finite real matrix/Cantor equivalences form a natural transformation between the matrix tower and the Cantor operator tower. -/
theorem realMatToCantor_natural (n : ℕ) :
    (realCantorOpEmbed n : RealCantorOp n →ₐ[ℝ] RealCantorOp (n + 1)) ∘ (realMatToCantor n : MatStage n →ₐ[ℝ] RealCantorOp n)
    = (realMatToCantor (n + 1) : MatStage (n + 1) →ₐ[ℝ] RealCantorOp (n + 1)) ∘ (matStageEmbed n : MatStage n →ₐ[ℝ] MatStage (n + 1)) := by
  ext A
  rw [show (realCantorOpEmbed n ∘ realMatToCantor n) A = realCantorOpEmbed n (realMatToCantor n A) by rfl]
  rw [show (realMatToCantor (n + 1) ∘ matStageEmbed n) A = realMatToCantor (n + 1) (matStageEmbed n A) by rfl]
  rw [realCantorOpEmbed_realMatToCantor]
  <;> simp [AlgHom.comp_apply]

/-- The inverse finite real/Cantor-matrix equivalences also form a natural transformation. -/
theorem realMatToCantor_symm_natural (n : ℕ) :
    (matStageEmbed n : MatStage n →ₐ[ℝ] MatStage (n + 1)) ∘ ((realMatToCantor n).symm : RealCantorOp n →ₐ[ℝ] MatStage n)
    = ((realMatToCantor (n + 1)).symm : RealCantorOp (n + 1) →ₐ[ℝ] MatStage (n + 1)) ∘ (realCantorOpEmbed n : RealCantorOp n →ₐ[ℝ] RealCantorOp (n + 1)) := by
  ext X
  have h₁ : ((matStageEmbed n : MatStage n →ₐ[ℝ] MatStage (n + 1)) ∘ ((realMatToCantor n).symm : RealCantorOp n →ₐ[ℝ] MatStage n)) X =
      matStageEmbed n ((realMatToCantor n).symm X) := by
    simp [AlgHom.comp_apply]
  have h₂ : (((realMatToCantor (n + 1)).symm : RealCantorOp (n + 1) →ₐ[ℝ] MatStage (n + 1)) ∘ (realCantorOpEmbed n : RealCantorOp n →ₐ[ℝ] RealCantorOp (n + 1))) X =
      (realMatToCantor (n + 1)).symm (realCantorOpEmbed n X) := by
    simp [AlgHom.comp_apply]
  rw [h₁, h₂]
  exact realMatToCantor_symm_realCantorOpEmbed n X
-/

end JordanWignerCantorRepresentation
