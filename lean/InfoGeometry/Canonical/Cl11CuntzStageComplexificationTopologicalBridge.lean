import InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit
import InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
import InfoGeometry.Canonical.CuntzMatrixTraceTopologicalGNSBridge
import InfoGeometry.Canonical.JordanWignerCantorRepresentation
import InfoGeometry.Canonical.SouriauOnsagerBKMBridge

/-!
# Stage-level real-to-complex bridge for the two matrix towers

The `Cl(1,1)` tower is real and indexed by the recursive tensor index, while
the Cuntz/UHF trace tower uses `Fin (2^n)` and complex matrices.  This owner
only constructs the canonical finite-stage complexification and proves the
normalized trace readout compatibility.  It deliberately does not assert
that the two bonding systems form a natural transformation; that requires a
separate proof of transition compatibility.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11CuntzStageComplexificationTopologicalBridge

open CategoryTheory
open scoped Kronecker
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalGNSBridge
open InfoGeometry.Canonical.JordanWignerCantorRepresentation
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

abbrev ClStage (n : ℕ) : Type := MatStage n
abbrev ComplexStage (n : ℕ) : Type := MatrixStage n
abbrev TensorComplexStage (n : ℕ) : Type :=
  Matrix (Idx n) (Idx n) ℂ

/-- Compatibility required to compare the tensor-index and `Fin (2^n)` towers.
The existing finite equivalences are deliberately not assumed to satisfy this
coherence definitionally. -/
def FinReindexCoherence (n : ℕ) : Prop :=
  ∀ p : Idx n × Fin 2,
    idxEquivFinPowTwo (Nat.succ n) p =
      stageIndexEquiv n (idxEquivFinPowTwo n p.1, p.2)

/-! Before choosing the auxiliary `Fin (2^n)` reindexing, the two towers have
the same recursive tensor index.  This is the canonical place where the
complexification and the tensor successor commute. -/

noncomputable def complexifyClTensorStage (n : ℕ) :
    ClStage n →ₐ[ℝ] TensorComplexStage n :=
  complexifyMatrixAlgHom n

def complexifyClTensorStageTopCatHom (n : ℕ) :
    TopCat.of (ClStage n) ⟶ TopCat.of (TensorComplexStage n) :=
  TopCat.ofHom
    { toFun := complexifyClTensorStage n
      continuous_toFun :=
        (complexifyClTensorStage n).toLinearMap.continuous_of_finiteDimensional }

noncomputable def complexTensorStepLinear (n : ℕ) :
    TensorComplexStage n →ₗ[ℂ] TensorComplexStage (Nat.succ n) where
  toFun A := A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  map_add' A B := by
    simpa using Matrix.add_kronecker A B
      (1 : Matrix (Fin 2) (Fin 2) ℂ)
  map_smul' c A := by
    simp [Matrix.smul_kronecker]

def complexTensorStepTopCatHom (n : ℕ) :
    TopCat.of (TensorComplexStage n) ⟶
      TopCat.of (TensorComplexStage (Nat.succ n)) :=
  TopCat.ofHom
    { toFun := complexTensorStepLinear n
      continuous_toFun :=
        (complexTensorStepLinear n).continuous_of_finiteDimensional }

@[simp] theorem complexifyClTensorStageTopCatHom_apply (n : ℕ) (A : ClStage n) :
    complexifyClTensorStageTopCatHom n A = complexifyClTensorStage n A :=
  rfl

theorem complexifyClTensorStage_transition (n : ℕ) (A : ClStage n) :
    complexifyClTensorStage (Nat.succ n) (matStageEmbed n A) =
      (complexifyClTensorStage n A) ⊗ₖ
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  cases hi : i with
  | mk i₁ i₂ =>
      cases hj : j with
      | mk j₁ j₂ =>
          fin_cases i₂ <;> fin_cases j₂ <;>
            simp [complexifyClTensorStage, complexifyMatrixAlgHom,
              matStageEmbed]

theorem complexifyClTensorStageTopCatHom_naturality (n : ℕ) (A : ClStage n) :
    complexifyClTensorStageTopCatHom (Nat.succ n) (stageEmbed n A) =
      complexTensorStepTopCatHom n (complexifyClTensorStageTopCatHom n A) := by
  change complexifyClTensorStage (Nat.succ n) (stageEmbed n A) =
    complexTensorStepLinear n (complexifyClTensorStage n A)
  simpa [stageEmbed_apply] using complexifyClTensorStage_transition n A

/-- Complexify a real Cl(1,1) stage and reindex it to `Fin (2^n)`. -/
noncomputable def complexifyClStage (n : ℕ) :
    ClStage n →ₐ[ℝ] ComplexStage n :=
  (Matrix.reindexAlgEquiv ℝ ℂ (idxEquivFinPowTwo n)).toAlgHom.comp
    (complexifyMatrixAlgHom n)

def complexifyClStageTopCatHom (n : ℕ) :
    TopCat.of (ClStage n) ⟶ TopCat.of (ComplexStage n) :=
  TopCat.ofHom
    { toFun := complexifyClStage n
      continuous_toFun :=
        (complexifyClStage n).toLinearMap.continuous_of_finiteDimensional }

@[simp] theorem complexifyClStageTopCatHom_apply (n : ℕ) (A : ClStage n) :
    complexifyClStageTopCatHom n A = complexifyClStage n A :=
  rfl

theorem complexifyClStage_concreteStep_of_indexCoherence
    (n : ℕ) (A : ClStage n) (hcoh : FinReindexCoherence n) :
    complexifyClStage (Nat.succ n) (stageEmbed n A) =
      concreteStep n (complexifyClStage n A) := by
  ext i j
  let p := (idxEquivFinPowTwo (Nat.succ n)).symm i
  let q := (idxEquivFinPowTwo (Nat.succ n)).symm j
  have hp := hcoh p
  have hq := hcoh q
  have hpi :
      (idxEquivFinPowTwo n p.1, p.2) = (stageIndexEquiv n).symm i := by
    apply (stageIndexEquiv n).injective
    rw [← hp]
    simp [p]
  have hqi :
      (idxEquivFinPowTwo n q.1, q.2) = (stageIndexEquiv n).symm j := by
    apply (stageIndexEquiv n).injective
    rw [← hq]
    simp [q]
  have hpi₁ := congrArg Prod.fst hpi
  have hpi₂ := congrArg Prod.snd hpi
  have hqi₁ := congrArg Prod.fst hqi
  have hqi₂ := congrArg Prod.snd hqi
  have hp₁ :
      ((idxEquivFinPowTwo (n + 1)).symm i).1 =
        (idxEquivFinPowTwo n).symm ((stageIndexEquiv n).symm i).1 := by
    apply (idxEquivFinPowTwo n).eq_symm_apply.mpr
    simpa [p, Nat.succ_eq_add_one] using hpi₁
  have hp₂ :
      ((idxEquivFinPowTwo (n + 1)).symm i).2 =
        ((stageIndexEquiv n).symm i).2 := by
    simpa [p, Nat.succ_eq_add_one] using hpi₂
  have hq₁ :
      ((idxEquivFinPowTwo (n + 1)).symm j).1 =
        (idxEquivFinPowTwo n).symm ((stageIndexEquiv n).symm j).1 := by
    apply (idxEquivFinPowTwo n).eq_symm_apply.mpr
    simpa [q, Nat.succ_eq_add_one] using hqi₁
  have hq₂ :
      ((idxEquivFinPowTwo (n + 1)).symm j).2 =
        ((stageIndexEquiv n).symm j).2 := by
    simpa [q, Nat.succ_eq_add_one] using hqi₂
  simp only [complexifyClStage, concreteStep, Matrix.reindexAlgEquiv,
    complexifyMatrixAlgHom]
  change Complex.ofReal
      ((A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ))
        ((idxEquivFinPowTwo (n + 1)).symm i)
        ((idxEquivFinPowTwo (n + 1)).symm j)) =
    Complex.ofReal
        (A ((idxEquivFinPowTwo n).symm ((stageIndexEquiv n).symm i).1)
          ((idxEquivFinPowTwo n).symm ((stageIndexEquiv n).symm j).1)) *
      (1 : Matrix (Fin 2) (Fin 2) ℂ)
        ((stageIndexEquiv n).symm i).2 ((stageIndexEquiv n).symm j).2
  rw [Matrix.kroneckerMap_apply, hp₂, hq₂]
  rw [hp₁, hq₁]
  by_cases h : ((stageIndexEquiv n).symm i).2 =
      ((stageIndexEquiv n).symm j).2
  · norm_num [Matrix.one_apply, h]
  · norm_num [Matrix.one_apply, h]

theorem complexifyClStage_trace (n : ℕ) (A : ClStage n) :
    Matrix.trace (complexifyClStage n A) =
      Complex.ofReal (Matrix.trace A) := by
  unfold complexifyClStage
  change Matrix.trace
      ((Matrix.reindexAlgEquiv ℝ ℂ (idxEquivFinPowTwo n))
        (complexifyMatrixAlgHom n A)) = _
  simp only [Matrix.reindexAlgEquiv, Matrix.trace]
  dsimp [complexifyMatrixAlgHom]
  rw [Complex.ofReal_sum]
  exact Equiv.sum_comp (idxEquivFinPowTwo n).symm
    (fun i => Complex.ofReal (A i i))

/-! The same finite readout through the genuine bounded-operator trace used by
the Kubo--Mori owner.  This is a finite complexification theorem, not a
noncommutative log-determinant identification. -/

theorem complexifyClStage_finiteOperatorTrace (n : ℕ) (A : ClStage n) :
    SouriauOnsagerBKM.finiteOperatorTrace
        (matrixOp (complexifyClStage n A)) =
      Complex.ofReal (Matrix.trace A) := by
  unfold SouriauOnsagerBKM.finiteOperatorTrace
  rw [matrixOfOp_matrixOp]
  exact complexifyClStage_trace n A

theorem complexifyClStage_finiteOperatorNormalizedTrace (n : ℕ) (A : ClStage n) :
    (1 / (2 ^ n : ℂ)) *
        SouriauOnsagerBKM.finiteOperatorTrace
          (matrixOp (complexifyClStage n A)) =
      Complex.ofReal (normalizedTrace n A) := by
  rw [complexifyClStage_finiteOperatorTrace]
  unfold normalizedTrace
  rw [Complex.ofReal_div]
  simp [div_eq_mul_inv, mul_comm]

theorem complexifyClStage_normalizedTrace (n : ℕ) (A : ClStage n) :
    matrixTraceFunctional n (complexifyClStage n A) =
      Complex.ofReal (normalizedTrace n A) := by
  rw [matrixTraceFunctional_apply, complexifyClStage_trace]
  unfold normalizedTrace
  rw [Complex.ofReal_div]
  simp [div_eq_mul_inv, mul_comm]

theorem complexifyClStage_normalizedTraceTopCat_readout
    (n : ℕ) (A : ClStage n) :
    (TopCat.ofHom (continuousRealTrace n))
        (complexifyClStageTopCatHom n A) =
      normalizedTrace n A := by
  change (matrixTraceFunctional n (complexifyClStage n A)).re = _
  rw [complexifyClStage_normalizedTrace]
  exact Complex.ofReal_re _

end InfoGeometry.Canonical.Cl11CuntzStageComplexificationTopologicalBridge
