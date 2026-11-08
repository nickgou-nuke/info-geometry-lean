/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FiniteRealFockMetric
import InfoGeometry.Clifford.FiniteFockCLMReflexivePair
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
import InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence
import InfoGeometry.Clifford.CliffordBitWordEquivalence

/-!
# Finite exterior-Fock and occupation-vector carriers

The exterior-algebra Fock stage and the binary occupation-vector stage are
identified through the actual exterior basis. Reversing the finite mode labels
makes the zero-head exterior inclusion agree with the recursively appended
vacuum bit in the existing binary occupation tower.
-/

noncomputable section

namespace InfoGeometry.Clifford.FockOccupationCarrierEquiv

open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence
open InfoGeometry.Algebra.CliffordBitWordEquivalence
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

/-- Reindex a function module along an equivalence of its finite index types. -/
def piReindex {α β R : Type*} [Semiring R]
    (e : α ≃ β) : (α → R) ≃ₗ[R] (β → R) where
  toFun f b := f (e.symm b)
  invFun g a := g (e a)
  left_inv f := by
    funext a
    simp
  right_inv g := by
    funext b
    simp
  map_add' f g := by
    rfl
  map_smul' r f := by
    rfl

/-- Convert a finite subset of modes to its reversed Boolean occupation word.
The reversal is forced by the existing tower convention: the exterior map
inserts a new head mode, while `Idx (n+1)` appends its new bit. -/
def finsetOccupationWord (n : ℕ) (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i.rev ∈ S)

/-- The finite-subset/Boolean-word bijection associated to the occupation
function. -/
def finsetOccupationEquiv (n : ℕ) : Finset (Fin n) ≃ (Fin n → Bool) where
  toFun := finsetOccupationWord n
  invFun w := Finset.univ.filter (fun i => w i.rev)
  left_inv S := by
    ext i
    simp [finsetOccupationWord]
  right_inv w := by
    funext i
    simp [finsetOccupationWord]

/-- The occupation word of the actual exterior tail is the old word followed
by an unoccupied final mode. -/
theorem finsetOccupationWord_tail (n : ℕ) (S : Finset (Fin n)) :
    finsetOccupationWord (n + 1) (S.map (Fin.succEmb n)) =
      InfoGeometry.Canonical.UHFInductiveColimitBoundary.extendSucc n
        (finsetOccupationWord n S) false := by
  classical
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [finsetOccupationWord, InfoGeometry.Canonical.UHFInductiveColimitBoundary.extendSucc]
  · dsimp only [finsetOccupationWord]
    have hrev : (j.rev).succ = (j.castSucc).rev := by
      rw [Fin.rev_castSucc]
    have hmem : (j.castSucc).rev ∈ S.map (Fin.succEmb n) ↔ j.rev ∈ S := by
      rw [Finset.mem_map]
      constructor
      · rintro ⟨a, ha, h⟩
        have haeq : a = j.rev := Fin.succ_inj.mp (h.trans hrev.symm)
        simpa [haeq] using ha
      · intro h
        exact ⟨j.rev, h, hrev⟩
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [hmem]
    simp [finsetOccupationWord,
      InfoGeometry.Canonical.UHFInductiveColimitBoundary.extendSucc,
      Fin.val_castSucc, j.isLt]

/-- Coherent finite reindexing from exterior basis labels to the existing
recursive occupation indices. -/
def exteriorOccupationIndexEquiv (n : ℕ) : Finset (Fin n) ≃ Idx n :=
  (finsetOccupationEquiv n).trans (idxBitWordEquiv n).symm

/-- The coherent index equivalence sends the exterior tail embedding to the
recursive operator index with the new mode unoccupied. -/
theorem exteriorOccupationIndexEquiv_tail (n : ℕ) (S : Finset (Fin n)) :
    exteriorOccupationIndexEquiv (n + 1) (S.map (Fin.succEmb n)) =
      (exteriorOccupationIndexEquiv n S, (finTwoEquivBool).symm false) := by
  apply (idxBitWordEquiv (n + 1)).injective
  rw [idxBitWordEquiv_succ_apply]
  have hleft :
      idxBitWordEquiv (n + 1)
        (exteriorOccupationIndexEquiv (n + 1) (S.map (Fin.succEmb n))) =
      finsetOccupationWord (n + 1) (S.map (Fin.succEmb n)) := by
    change idxBitWordEquiv (n + 1)
      ((finsetOccupationEquiv (n + 1)).trans (idxBitWordEquiv (n + 1)).symm
        (S.map (Fin.succEmb n))) = _
    rw [Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl
  have hright :
      idxBitWordEquiv n (exteriorOccupationIndexEquiv n S) =
      finsetOccupationWord n S := by
    change idxBitWordEquiv n
      ((finsetOccupationEquiv n).trans (idxBitWordEquiv n).symm S) = _
    rw [Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl
  rw [hleft, hright, finsetOccupationWord_tail]
  simp [finTwoEquivBool]

/-- Coordinates of the finite exterior-Fock module in the matrix tower's
occupation-vector carrier, using the actual exterior basis and coherent
recursive index reindexing above. -/
noncomputable def fockOccupationEquiv (n : ℕ) :
    InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.FockStage n ≃ₗ[ℝ]
      (Idx n → ℝ) :=
  (fockCoordinates n).trans
    ((EuclideanSpace.equiv (Finset (Fin n)) ℝ).toLinearEquiv.trans
      (piReindex (exteriorOccupationIndexEquiv n)))

/-- The endomorphism algebra of the exterior-Fock stage, expressed on the
existing recursive occupation carrier. -/
noncomputable def fockOperatorCarrierEquiv (n : ℕ) :
    Module.End ℝ
        (InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.FockStage n) ≃ₐ[ℝ]
      InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.FockOpStage n :=
  (fockOccupationEquiv n).conjAlgEquiv ℝ

/-- The finite exterior-Fock endomorphism algebra, recursive occupation
operator algebra, and existing Clifford matrix stage form one connected
carrier through the repository's owned finite-stage equivalences. -/
noncomputable def exteriorFockCliffordOperatorEquiv (n : ℕ) :
    Module.End ℝ
        (InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.FockStage n) ≃ₐ[ℝ]
      InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.ClStage n :=
  (fockOperatorCarrierEquiv n).trans
    (InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.clToFockOp n).symm

/-- The finite operator-carrier identification intertwines the actual actions
on vectors. -/
theorem fockOperatorCarrierEquiv_apply (n : ℕ)
    (T : Module.End ℝ
      (InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.FockStage n))
    (ψ : InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.FockStage n) :
    fockOperatorCarrierEquiv n T (fockOccupationEquiv n ψ) =
      fockOccupationEquiv n (T ψ) := by
  simp [fockOperatorCarrierEquiv, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply]

/-- The native exterior-Fock creation and contraction operators, transported
to the repository's recursive occupation-vector endomorphism algebra. -/
def occupationCreation (n : ℕ) (i : Fin n) :
    InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.FockOpStage n :=
  fockOperatorCarrierEquiv n
    (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockExtActionCLM n i).toLinearMap

def occupationContraction (n : ℕ) (i : Fin n) :
    InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.FockOpStage n :=
  fockOperatorCarrierEquiv n
    (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockIntActionCLM n i).toLinearMap

/-- The finite exterior-Fock CAR relation is preserved by the algebra
equivalence to recursive occupation operators. -/
theorem occupationCreation_contraction_CAR (n : ℕ) (i : Fin n) :
    occupationContraction n i * occupationCreation n i +
      occupationCreation n i * occupationContraction n i = 1 := by
  have hCAR :
      (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockIntActionCLM n i).toLinearMap *
          (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockExtActionCLM n i).toLinearMap +
        (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockExtActionCLM n i).toLinearMap *
          (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockIntActionCLM n i).toLinearMap = 1 := by
    simpa using congrArg (fun T => T.toLinearMap)
      (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fock_coordinate_CLM_CAR n i)
  rw [occupationContraction, occupationCreation, ← map_mul, ← map_mul, ← map_add]
  rw [hCAR]
  exact map_one (fockOperatorCarrierEquiv n)

/-- The same finite CAR pair remains the unit relation after transport all the
way into the repository's Clifford matrix stage. -/
theorem exteriorFockClifford_CAR (n : ℕ) (i : Fin n) :
    exteriorFockCliffordOperatorEquiv n
        ((InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockIntActionCLM n i).toLinearMap) *
      exteriorFockCliffordOperatorEquiv n
        ((InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockExtActionCLM n i).toLinearMap) +
    exteriorFockCliffordOperatorEquiv n
        ((InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockExtActionCLM n i).toLinearMap) *
      exteriorFockCliffordOperatorEquiv n
        ((InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockIntActionCLM n i).toLinearMap) = 1 := by
  change (InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.clToFockOp n).symm
        (occupationContraction n i) *
      (InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.clToFockOp n).symm
        (occupationCreation n i) +
    (InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.clToFockOp n).symm
        (occupationCreation n i) *
      (InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.clToFockOp n).symm
        (occupationContraction n i) = 1
  rw [← map_mul, ← map_mul, ← map_add, occupationCreation_contraction_CAR]
  exact map_one
    (InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.clToFockOp n).symm

/-- The exterior-Fock operator algebra's image in the established Clifford
operator colimit agrees with the image obtained through the recursive
occupation-operator stage. This is the stage compatibility needed to transport
finite CAR calculations into the existing operator direct limit. -/
theorem exteriorFockCliffordOperatorEquiv_colimit (n : ℕ)
    (T : Module.End ℝ
      (InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.FockStage n)) :
    InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.clLimitFockOpAlgEquiv
        (InfoGeometry.Canonical.JordanWignerCantorColimit.MatOfStage n
          (exteriorFockCliffordOperatorEquiv n T)) =
      InfoGeometry.Canonical.JordanWignerCantorRepresentation.realCantorOfStage n
        (fockOperatorCarrierEquiv n T) := by
  change InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.clLimitFockOpEquiv
      (InfoGeometry.Canonical.JordanWignerCantorColimit.MatOfStage n
        (exteriorFockCliffordOperatorEquiv n T)) = _
  rw [InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.clLimitFockOpEquiv_ofStage]
  change InfoGeometry.Canonical.JordanWignerCantorRepresentation.realCantorOfStage n
      (InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.clToFockOp n
        (exteriorFockCliffordOperatorEquiv n T)) = _
  simp [exteriorFockCliffordOperatorEquiv]

/-- Each ordered exterior basis vector becomes the corresponding occupation
basis vector, fixing the carrier identification on generators of the module. -/
@[simp] theorem fockOccupationEquiv_exteriorBasis (n : ℕ)
    (S : Finset (Fin n)) :
  fockOccupationEquiv n
      ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra S) =
        (Pi.single (exteriorOccupationIndexEquiv n S) (1 : ℝ) : Idx n → ℝ) := by
  classical
  apply funext
  intro i
  simp [fockOccupationEquiv, fockCoordinates_apply, piReindex,
    exteriorOccupationIndexEquiv, Module.Basis.equivFun_self,
    Equiv.eq_symm_apply, Pi.single_apply, eq_comm]

end InfoGeometry.Clifford.FockOccupationCarrierEquiv

end
