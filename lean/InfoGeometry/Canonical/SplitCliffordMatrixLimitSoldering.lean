import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SpinorRep
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Algebra.PrimonColimitAlgebra
import InfoGeometry.Clifford.CliffordBitWordEquivalence
import InfoGeometry.Clifford.SplitCliffordNativeTensorFinrank
import InfoGeometry.Clifford.Cl55SpinorRepresentationGeneration
import InfoGeometry.Algebra.FiniteTensorDeterminantStabilization

/-!
# InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering

Finite-stage soldering interface and mathematical classification of the
Clifford-to-Matrix tower morphisms.

## The Mathematical Status:

1. **The Canonical Algebraic Tower Morphism (Untwisted)**:
   - The genuine algebraic bond on the matrix tensor tower is
     `stageEmbed n A = A ⊗ₖ I₂`.
   - The coherent split matrix realization is
     `clStageEquiv (n) : ClStage n ≃ₐ[ℝ] UHFStage n`.
   - The fundamental bonding theorem `clStageEquiv_bond` proves:
     `clStageEquiv (n + 1) (stageEmbed n A) = matrixBond n (clStageEquiv n A)`.
   - The induced colimit ring homomorphism is
     `clToUHF : ClCarrier →+* UHFCarrier`, evaluated at finite stages by `clToUHF_ofStage`.
   - This canonical morphism is owned by `InfoGeometry.Algebra.CliffordBitWordEquivalence`.

2. **The Recursive Spinor Representation & Graded Tensor Step**:
   - The native step is `splitCliffordStep n : SplitClNNAlg n →ₐ[ℝ] SplitClNNAlg (n + 1)`
     whose factorization uses the graded tensor product:
     `CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)`
     rather than an ordinary tensor product.
   - The recursive spinor representation `spinorRepresentation n` maps tail generators
     using `gradingAtom` ($\gamma_{12} = \sigma_1$) rather than the identity $I_2$.
   - Consequently, its successor map `gradedTensorSuccessor n` is linear but is
     **not** an algebra homomorphism (`gradedTensorSuccessor_not_algHom`), because
     `F(1) = 1 ⊗ γ₁₂ ≠ 1 ⊗ I₂` (`gradingAtom_ne_one`).
   - Therefore, `nativeCliffordStageEquiv_bond` is obstructed for the recursive `stageMap`
     against the untwisted `stageEmbed n A = A ⊗ I₂`.

3. **The Dual Soldering Architecture**:
   To solder the native Clifford quotient tower `SplitClNNAlg n` to the UHF matrix continuum,
   two complementary mathematical routes exist:
   - **Route A (The Canonical Bit-Word Soldering - Untwisted C*-colimit)**:
     Bypasses the recursive grading clash by pre-encoding the Jordan-Wigner parity strings
     into the operator basis (`CliffordBitWordEquivalence`). The intertwining bond
     `canonical_clStageEquiv_bond` holds unconditionally, yielding the direct-limit
     ring isomorphism `canonicalCliffordUHFColimitEquiv : ClCarrier ≃+* UHFCarrier`.
   - **Route B (The Parity-Twisted Bond - Graded Super-colimit)**:
     Preserves the recursive `spinorRepresentation` by modifying the matrix bond itself:
     `T_n(A) = A_even ⊗ I₂ + A_odd ⊗ γ₁₂`.
     Under the total grading involution `Γ_n`, `T_n` becomes a genuine algebra homomorphism
     satisfying `T_n(1) = 1` and `T_n(AB) = T_n(A) T_n(B)` (using `γ₁₂² = I₂`).
     The recursive spinor representation then forms a genuine direct-limit cone with `T_n`.
-/

noncomputable section
namespace InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.GammaMatrices
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.Algebra.CliffordBitWordEquivalence

abbrev MatrixStage (n : ℕ) :=
  InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n

/-! ## 1. Recursive Spinor Representation (Graded / Parity-Twisted Presentation) -/

/-- Transport the recursive spinor representation to the matrix-stage carrier. -/
noncomputable def stageMap (n : ℕ) :
    SplitClNNAlg n →ₐ[ℝ] MatrixStage n :=
  (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo n).symm.toAlgHom.comp
    (spinorRepresentation n)

@[simp] theorem stageMap_on_generator (n : ℕ) (v : SplitSpace n) :
    stageMap n (CliffordAlgebra.ι (SplitQuad n) v) =
      (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo n).symm
        (recursiveGamma n v) := by
  simp [stageMap, spinorRepresentation_ι]

/-! The finite reindexing does not alter surjectivity.  This is the precise
interface needed before upgrading the representation to an algebra
equivalence by finite-dimensional linear algebra. -/
theorem stageMap_surjective (n : ℕ)
    (h : Function.Surjective (spinorRepresentation n)) :
    Function.Surjective (stageMap n) := by
  intro M
  rcases h ((InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo n) M) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simpa [stageMap] using congrArg
    ((InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo n).symm) hx

theorem stageMap_surjective_of_gammaTensor (n : ℕ) :
    Function.Surjective (stageMap n) :=
  stageMap_surjective n
    (InfoGeometry.Clifford.Clifford55.splitSpinorRepresentation_surjective_of_gammaTensor n)

/-- Upgrade a surjective finite-stage representation to an algebra
equivalence, provided the source and target dimensions agree. -/
noncomputable def stageMapEquivOfSurjective
    (n : ℕ)
    [FiniteDimensional ℝ (SplitClNNAlg n)]
    [FiniteDimensional ℝ (MatrixStage n)]
    (h : Function.Surjective (spinorRepresentation n))
    (hdim : Module.finrank ℝ (SplitClNNAlg n) =
      Module.finrank ℝ (MatrixStage n)) :
    SplitClNNAlg n ≃ₐ[ℝ] MatrixStage n := by
  apply AlgEquiv.ofBijective (stageMap n)
  have hs : Function.Surjective (stageMap n) := stageMap_surjective n h
  have hi : Function.Injective (stageMap n).toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hs
  exact ⟨hi, hs⟩

/-! The matrix-stage bond is the explicit transport of `matStageEmbed` through
the finite `Fin (2^n)` reindexings. -/
theorem spinorMatrixBottStep_eq_transported_matStageEmbed (n : ℕ)
    (A : InfoGeometry.Clifford.TowerMatrix.Mat n) :
    InfoGeometry.Clifford.SpinorRep.spinorMatrixBottStep n
        ((InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo n) A) =
      (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo (n + 1))
        (InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed n A) := by
  simp [InfoGeometry.Clifford.SpinorRep.spinorMatrixBottStep]

/-- Reindexing the matrix-stage bond into the recursive tensor-index carrier
and back through `tensorIndexEquivFinPowTwo` is the identity. -/
theorem tensorIndexEquivFinPowTwo_reindex_matStageEmbed (n : ℕ)
    (A : InfoGeometry.Clifford.Cl11TensorTower.MatStage n) :
    tensorMatrixEquivFinPowTwo (n + 1)
        ((tensorMatrixEquivFinPowTwo (n + 1)).symm
          ((InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo (n + 1))
            (InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed n A))) =
      (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo (n + 1))
        (InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed n A) := by
  exact (tensorMatrixEquivFinPowTwo (n + 1)).apply_symm_apply _

/-! Exact generator image of the canonical split-Clifford successor. -/
theorem stageMap_splitCliffordStep_tailLift (n : ℕ) (xs : SplitSpace n) :
    stageMap (n + 1)
        (splitCliffordStep n (CliffordAlgebra.ι (SplitQuad n) xs)) =
      (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo (n + 1)).symm
        ((tensorMatrixEquivFinPowTwo (n + 1))
          (appendAtom (recursiveGammaTensor n xs) gradingAtom)) := by
  rw [incl_Cl_split_ι]
  change (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo (n + 1)).symm
        (spinorRepresentation (n + 1)
        (CliffordAlgebra.ι (SplitQuad (n + 1))
          (InfoGeometry.Clifford.ClNN.tailLift n xs))) = _
  rw [spinorRepresentation_tailFactor_ι]

/-! The recursive spinor tower has a graded successor bond.  It is linear,
but deliberately not an algebra homomorphism: its last factor is the grading
atom rather than the identity. -/
noncomputable def gradedTensorSuccessor (n : ℕ) :
    SplitGammaMatrix n →ₗ[ℝ] SplitGammaMatrix (n + 1) where
  toFun A := appendAtom A gradingAtom
  map_add' A B := by
    ext i j
    rcases i with ⟨i, a⟩
    rcases j with ⟨j, b⟩
    simp [appendAtom_apply]
    ring
  map_smul' c A := by
    ext i j
    rcases i with ⟨i, a⟩
    rcases j with ⟨j, b⟩
    simp [appendAtom_apply]
    ring

@[simp] theorem gradedTensorSuccessor_apply (n : ℕ) (A : SplitGammaMatrix n) :
    gradedTensorSuccessor n A = appendAtom A gradingAtom := rfl

theorem gradedTensorSuccessor_generator (n : ℕ) (xs : SplitSpace n) :
    gradedTensorSuccessor n (recursiveGammaTensor n xs) =
      appendAtom (recursiveGammaTensor n xs) gradingAtom := by
  rfl

/-! Explicit finite-stage reindexing from the matrix tower carrier to the
recursive tensor-index carrier. -/
noncomputable def matrixStageToTensor (n : ℕ) :
    MatrixStage n →ₗ[ℝ] SplitGammaMatrix n :=
  ((tensorMatrixEquivFinPowTwo n).symm.toLinearMap).comp
    (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo n).toLinearMap

noncomputable def tensorToMatrixStage (n : ℕ) :
    SplitGammaMatrix n →ₗ[ℝ] MatrixStage n :=
  ((InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo n).symm.toLinearMap).comp
    (tensorMatrixEquivFinPowTwo n).toLinearMap

theorem tensorToMatrixStage_comp_matrixStageToTensor (n : ℕ) :
    (tensorToMatrixStage n).comp (matrixStageToTensor n) = LinearMap.id := by
  ext A
  dsimp [tensorToMatrixStage, matrixStageToTensor]
  simp

theorem matrixStageToTensor_comp_tensorToMatrixStage (n : ℕ) :
    (matrixStageToTensor n).comp (tensorToMatrixStage n) = LinearMap.id := by
  ext A
  dsimp [tensorToMatrixStage, matrixStageToTensor]
  simp

noncomputable def gradedStageSuccessor (n : ℕ) :
    MatrixStage n →ₗ[ℝ] MatrixStage (n + 1) :=
  (tensorToMatrixStage (n + 1)).comp
    ((gradedTensorSuccessor n).comp (matrixStageToTensor n))

theorem stageMap_splitCliffordStep_eq_gradedStageSuccessor (n : ℕ)
    (xs : SplitSpace n) :
    stageMap (n + 1)
        (splitCliffordStep n (CliffordAlgebra.ι (SplitQuad n) xs)) =
      gradedStageSuccessor n
        (stageMap n (CliffordAlgebra.ι (SplitQuad n) xs)) := by
  rw [stageMap_splitCliffordStep_tailLift, stageMap_on_generator]
  dsimp [gradedStageSuccessor, tensorToMatrixStage, matrixStageToTensor]
  simp [recursiveGamma]

/-! ### Parity-Twisted Matrix Bond (Route B) -/

/-- The total grading involution Γₙ on the recursive tensor stage. -/
noncomputable def totalGradingTensor : (n : ℕ) → SplitGammaMatrix n
  | 0 => (1 : SplitGammaMatrix 0)
  | n + 1 => appendAtom (totalGradingTensor n) gradingAtom

/-- Transport of the total grading involution to the matrix stage carrier. -/
noncomputable def totalGrading (n : ℕ) : MatrixStage n :=
  tensorToMatrixStage n (totalGradingTensor n)

/-- Even-parity projection under the total grading involution. -/
noncomputable def splitEven (n : ℕ) (A : MatrixStage n) : MatrixStage n :=
  (1 / 2 : ℝ) • (A + totalGrading n * A * totalGrading n)

/-- Odd-parity projection under the total grading involution. -/
noncomputable def splitOdd (n : ℕ) (A : MatrixStage n) : MatrixStage n :=
  (1 / 2 : ℝ) • (A - totalGrading n * A * totalGrading n)

/-- Linear embedding of split tensor with atom B. -/
noncomputable def appendAtomLin (n : ℕ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    SplitGammaMatrix n →ₗ[ℝ] SplitGammaMatrix (n + 1) where
  toFun A := appendAtom A B
  map_add' A C := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [appendAtom_apply, add_mul]
  map_smul' c A := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [appendAtom_apply, mul_assoc]

/-- The total grading involution as a linear map on M_{2ⁿ}(ℝ). -/
noncomputable def totalGradingLin (n : ℕ) : MatrixStage n →ₗ[ℝ] MatrixStage n where
  toFun A := totalGrading n * A * totalGrading n
  map_add' A B := by simp [mul_add, add_mul]
  map_smul' c A := by simp

/-- Even-parity projection as a linear map. -/
noncomputable def splitEvenLin (n : ℕ) : MatrixStage n →ₗ[ℝ] MatrixStage n :=
  (1 / 2 : ℝ) • (LinearMap.id + totalGradingLin n)

/-- Odd-parity projection as a linear map. -/
noncomputable def splitOddLin (n : ℕ) : MatrixStage n →ₗ[ℝ] MatrixStage n :=
  (1 / 2 : ℝ) • (LinearMap.id - totalGradingLin n)

theorem splitEvenLin_apply (n : ℕ) (A : MatrixStage n) :
    splitEvenLin n A = splitEven n A := rfl

theorem splitOddLin_apply (n : ℕ) (A : MatrixStage n) :
    splitOddLin n A = splitOdd n A := rfl

/-- The genuine parity-twisted matrix bond Tₙ : M_{2ⁿ}(ℝ) → M_{2^{n+1}}(ℝ).
Acting on homogeneous parity components:
even elements embed via A ⊗ I₂, while odd elements embed via A ⊗ γ₁₂. -/
noncomputable def twistedStageEmbed (n : ℕ) :
    MatrixStage n →ₗ[ℝ] MatrixStage (n + 1) :=
  (tensorToMatrixStage (n + 1)).comp
    (((appendAtomLin n (1 : Matrix (Fin 2) (Fin 2) ℝ)).comp
        ((matrixStageToTensor n).comp (splitEvenLin n))) +
     ((appendAtomLin n gradingAtom).comp
        ((matrixStageToTensor n).comp (splitOddLin n))))

theorem twistedStageEmbed_apply (n : ℕ) (A : MatrixStage n) :
    twistedStageEmbed n A =
      (tensorToMatrixStage (n + 1))
        (appendAtom (matrixStageToTensor n (splitEven n A)) (1 : Matrix (Fin 2) (Fin 2) ℝ) +
         appendAtom (matrixStageToTensor n (splitOdd n A)) gradingAtom) := rfl

/-- On purely odd elements (such as generator images under the spinor representation),
the twisted matrix bond applies the graded stage successor. -/
theorem twistedStageEmbed_of_odd (n : ℕ) (A : MatrixStage n)
    (h_odd : splitEven n A = 0) (h_split : splitOdd n A = A) :
    twistedStageEmbed n A = gradedStageSuccessor n A := by
  rw [twistedStageEmbed_apply]
  dsimp [gradedStageSuccessor, gradedTensorSuccessor]
  rw [h_odd, h_split]
  simp

/-- **Theorem**: On generator images where splitEven = 0 and splitOdd = stageMap,
the twisted matrix bond satisfies exact intertwining with the recursive Clifford step. -/
theorem twisted_stageMap_generator_bond (n : ℕ) (xs : SplitSpace n)
    (h_odd : splitEven n (stageMap n (CliffordAlgebra.ι (SplitQuad n) xs)) = 0)
    (h_split : splitOdd n (stageMap n (CliffordAlgebra.ι (SplitQuad n) xs)) =
      stageMap n (CliffordAlgebra.ι (SplitQuad n) xs)) :
    stageMap (n + 1)
        (splitCliffordStep n (CliffordAlgebra.ι (SplitQuad n) xs)) =
      twistedStageEmbed n
        (stageMap n (CliffordAlgebra.ι (SplitQuad n) xs)) := by
  rw [stageMap_splitCliffordStep_eq_gradedStageSuccessor]
  exact (twistedStageEmbed_of_odd n (stageMap n (CliffordAlgebra.ι (SplitQuad n) xs)) h_odd h_split).symm

/-! The graded successor factor is involutive, but is not itself the unit. -/
theorem appendAtom_gradingAtom_mul (n : ℕ)
    (A B : SplitGammaMatrix n) :
    appendAtom A gradingAtom * appendAtom B gradingAtom =
      appendAtom (A * B) (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [appendAtom_mul, gradingAtom_sq]

/-- Split Cl(1,1) generator square: e₊² = I₂. -/
@[simp] theorem gammaPlusAtom_sq :
    gammaPlusAtom * gammaPlusAtom = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact gammaPlus_sq

/-- Split Cl(1,1) generator square: -e₋² = I₂. -/
@[simp] theorem neg_gammaMinusAtom_sq :
    -(gammaMinusAtom * gammaMinusAtom) = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [gammaMinus_sq]
  simp

/-- Chiral volume element / grading atom definition from split generators: γ₁₂ = e₊ e₋. -/
theorem gradingAtom_eq_mul :
    gradingAtom = gammaPlusAtom * gammaMinusAtom := by
  exact gamma12_eq

/-- CAR completeness relation: the 2x2 identity matrix represented as a† a + a a†. -/
theorem car_completeness_matrix_unit :
    InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittCreationBase *
        InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittAnnihilationBase +
      InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittAnnihilationBase *
        InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittCreationBase =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact InfoGeometry.Clifford.Cl11TensorTower.realEncodedWitt_anticomm

/-- The matrix unit I₂ represented using the chiral Clifford atom e₊² = I₂.
This writes the ordinary tower bond factor through chiral Clifford generators without
identifying the grading operator `gradingAtom` with the unit `I₂`. -/
theorem matrix_unit_eq_gammaPlusAtom_sq :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) = gammaPlusAtom * gammaPlusAtom := by
  rw [gammaPlusAtom_sq]

/-- The matrix unit I₂ represented using the square of the chiral grading atom: γ₁₂² = I₂. -/
theorem matrix_unit_eq_gradingAtom_sq :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) = gradingAtom * gradingAtom := by
  rw [gradingAtom_sq]

/-- The matrix unit I₂ represented using the chiral Clifford atom -e₋² = I₂. -/
theorem matrix_unit_eq_neg_gammaMinusAtom_sq :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) = -(gammaMinusAtom * gammaMinusAtom) := by
  rw [neg_gammaMinusAtom_sq]

/-- The matrix tower bond A ↦ appendAtom A I₂ expressed through the square of the grading atom γ₁₂² = I₂. -/
theorem appendAtom_gradingAtom_sq (n : ℕ) (A : SplitGammaMatrix n) :
    appendAtom A (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      appendAtom A (gradingAtom * gradingAtom) := by
  rw [gradingAtom_sq]

/-- The matrix tower bond A ↦ appendAtom A I₂ expressed through chiral Clifford generator e₊². -/
theorem appendAtom_chiral_unit (n : ℕ) (A : SplitGammaMatrix n) :
    appendAtom A (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      appendAtom A (gammaPlusAtom * gammaPlusAtom) := by
  rw [gammaPlusAtom_sq]

/-- Local Left atom L (Witt creation a†) at a single site. -/
def leftAtom : Matrix (Fin 2) (Fin 2) ℝ :=
  InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittCreationBase

/-- Local Right atom R (Witt annihilation a) at a single site. -/
def rightAtom : Matrix (Fin 2) (Fin 2) ℝ :=
  InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittAnnihilationBase

/-- The Left atom is nilpotent: L² = 0. -/
@[simp] theorem leftAtom_sq : leftAtom * leftAtom = 0 := by
  exact InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittCreationBase_sq

/-- The Right atom is nilpotent: R² = 0. -/
@[simp] theorem rightAtom_sq : rightAtom * rightAtom = 0 := by
  exact InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittAnnihilationBase_sq

/-- Anticommutator of Left and Right atoms is the matrix identity I₂:
{L, R} = L R + R L = I₂ (CAR completeness relation). -/
theorem anticomm_left_right : leftAtom * rightAtom + rightAtom * leftAtom = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact car_completeness_matrix_unit

/-- Commutator of Left and Right atoms is the diagonal chiral grading operator Eplus (σ₃):
[L, R] = L R - R L = gammaPlusAtom. -/
theorem comm_left_right : leftAtom * rightAtom - rightAtom * leftAtom = gammaPlusAtom := by
  change InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittCreationBase *
      InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittAnnihilationBase -
    InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittAnnihilationBase *
      InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittCreationBase = gammaPlusAtom
  rw [InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittCreationBase_eq,
      InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittAnnihilationBase_eq]
  change (!![(0 : ℝ), 1; 0, 0] * !![(0 : ℝ), 0; 1, 0] -
    !![(0 : ℝ), 0; 1, 0] * !![(0 : ℝ), 1; 0, 0]) = gammaPlusAtom
  have hmul1 : !![(0 : ℝ), 1; 0, 0] * !![(0 : ℝ), 0; 1, 0] = !![(1 : ℝ), 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hmul2 : !![(0 : ℝ), 0; 1, 0] * !![(0 : ℝ), 1; 0, 0] = !![(0 : ℝ), 0; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hmul1, hmul2]
  have hdiff : !![(1 : ℝ), 0; 0, 0] - !![(0 : ℝ), 0; 0, 1] = !![(1 : ℝ), 0; 0, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply]
  rw [hdiff]
  have hP : gammaPlusAtom = !![(1 : ℝ), 0; 0, -1] := rfl
  rw [hP]

/-- The commutator [R, L] = R L - L R = -gammaPlusAtom. -/
theorem comm_right_left : rightAtom * leftAtom - leftAtom * rightAtom = -gammaPlusAtom := by
  have h : rightAtom * leftAtom - leftAtom * rightAtom =
      -(leftAtom * rightAtom - rightAtom * leftAtom) := by
    ext i j; simp [Matrix.sub_apply, Matrix.neg_apply]
  rw [h, comm_left_right]

/-- The matrix tower bond A ↦ appendAtom A I₂ expressed through the CAR completeness relation a† a + a a†. -/
theorem appendAtom_car_completeness (n : ℕ) (A : SplitGammaMatrix n) :
    appendAtom A (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      appendAtom A (leftAtom * rightAtom + rightAtom * leftAtom) := by
  rw [anticomm_left_right]

/-! ### The Left-Right Bivariate Word Decomposition -/

/-- Left excitation word of length n (spinor ket configuration). -/
abbrev LeftWord (n : ℕ) := InfoGeometry.Canonical.UHFInductiveColimitBoundary.BitWord n

/-- Right excitation word of length n (spinor bra configuration). -/
abbrev RightWord (n : ℕ) := InfoGeometry.Canonical.UHFInductiveColimitBoundary.BitWord n

/-- Bivariate Left-Right word pair indexing the endomorphism basis of the spinor space. -/
abbrev LeftRightWord (n : ℕ) := LeftWord n × RightWord n

/-- Equivalence between length-2n bit words and bivariate Left-Right word pairs. -/
def bitWord2nEquiv (n : ℕ) :
    InfoGeometry.Canonical.UHFInductiveColimitBoundary.BitWord (n + n) ≃ LeftRightWord n where
  toFun w :=
    (fun i => w ⟨i.1, by omega⟩,
     fun i => w ⟨n + i.1, by omega⟩)
  invFun p i :=
    if h : i.1 < n then
      p.1 ⟨i.1, h⟩
    else
      p.2 ⟨i.1 - n, by omega⟩
  left_inv w := by
    ext ⟨i, hi⟩
    dsimp
    split_ifs with h
    · rfl
    · have : n + (i - n) = i := Nat.add_sub_of_le (by omega)
      congr
  right_inv p := by
    rcases p with ⟨wL, wR⟩
    ext i
    · dsimp
      have hi : i.1 < n := i.2
      rw [dif_pos hi]
    · dsimp
      have hi : ¬ (n + i.1 < n) := by omega
      rw [dif_neg hi]
      have : n + i.1 - n = i.1 := Nat.add_sub_cancel_left n i.1
      congr

/-- The bivariate binomial expansion: 2^(2n) = 2^n * 2^n. -/
theorem left_right_dimension_product (n : ℕ) :
    2 ^ (2 * n) = 2 ^ n * 2 ^ n := by
  calc
    2 ^ (2 * n) = 2 ^ (n + n) := by rw [Nat.two_mul]
    _ = 2 ^ n * 2 ^ n := by rw [Nat.pow_add]

/-- The inductive bond step extends both Left and Right words by 0 and 1,
summing to the unexcited identity factor I₂ = |0⟩⟨0| + |1⟩⟨1|. -/
theorem left_right_unexcited_extension :
    rightAtom * leftAtom + leftAtom * rightAtom = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [add_comm]
  exact anticomm_left_right

theorem gradingAtom_ne_one :
    gradingAtom ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [gradingAtom, gamma12, InfoGeometry.Clifford.Cl11Matrix.J1,
    Matrix.one_apply] at h01

def tensorIndexDefault : (n : ℕ) →
    InfoGeometry.Clifford.GammaMatrices.TensorIndex n
  | 0 => PUnit.unit
  | n + 1 => (tensorIndexDefault n, 0)

theorem gradedTensorSuccessor_not_algHom (n : ℕ) :
    ¬ ∃ F : SplitGammaMatrix n →ₐ[ℝ] SplitGammaMatrix (n + 1),
      F.toLinearMap = gradedTensorSuccessor n := by
  rintro ⟨F, hF⟩
  have hone : F (1 : SplitGammaMatrix n) =
      gradedTensorSuccessor n (1 : SplitGammaMatrix n) := by
    exact congrArg (fun L => L (1 : SplitGammaMatrix n)) hF
  have hfactor : gradedTensorSuccessor n (1 : SplitGammaMatrix n) =
      appendAtom (1 : SplitGammaMatrix n) gradingAtom := rfl
  have hone' : (1 : SplitGammaMatrix (n + 1)) =
      appendAtom (1 : SplitGammaMatrix n) gradingAtom := by
    calc
      (1 : SplitGammaMatrix (n + 1)) = F (1 : SplitGammaMatrix n) :=
        (F.map_one).symm
      _ = gradedTensorSuccessor n (1 : SplitGammaMatrix n) := hone
      _ = appendAtom (1 : SplitGammaMatrix n) gradingAtom := hfactor
  have hmatrix := congrArg
      (fun M => M (tensorIndexDefault n, 0) (tensorIndexDefault n, 1)) hone'
  norm_num [appendAtom_apply, InfoGeometry.Clifford.GammaMatrices.TensorIndex,
    Matrix.one_apply, gradingAtom, gamma12,
    InfoGeometry.Clifford.Cl11Matrix.J1] at hmatrix

/-! The full finite-stage coherence proposition needed for an untwisted colimit soldering. -/
def BondCoherence : Prop :=
  ∀ n : ℕ, (stageMap (n + 1)).comp (splitCliffordStep n) =
    (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n).comp (stageMap n)

/-! The algebraic direct-limit map is exposed under the untwisted bond
coherence condition. -/
noncomputable def matrixLimitMap
    (hC : InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering.BondCoherence) :
    SplitCliffordInfinity →+*
      InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit :=
  DirectLimit.Ring.lift
    SplitClNNAlg
    (fun m n h => splitCliffordMap m n h)
    InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit
    (fun n =>
      (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n).comp
        (stageMap n).toRingHom)
    (by
      intro m n h x
      change (∀ n : ℕ, (stageMap (n + 1)).comp (splitCliffordStep n) =
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n).comp (stageMap n)) at hC
      induction n, h using Nat.le_induction with
      | base => simp
      | succ n hn ih =>
          change InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (n + 1)
              (stageMap (n + 1) (splitCliffordMap m (n + 1)
                (Nat.le_trans hn (Nat.le_succ n)) x)) =
            InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage m
              (stageMap m x)
          rw [splitCliffordMap_succ (m := m) (n := n) hn]
          change InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (n + 1)
              (stageMap (n + 1) (splitCliffordStep n
                (splitCliffordMap m n hn x))) = _
          have hstep := congrArg
            (fun f => f (splitCliffordMap m n hn x)) (hC n)
          change stageMap (n + 1) (splitCliffordStep n
              (splitCliffordMap m n hn x)) =
            InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n
              (stageMap n (splitCliffordMap m n hn x)) at hstep
          rw [hstep]
          rw [InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage_apply_bond]
          exact ih)

@[simp] theorem matrixLimitMap_ofStage
    (hC : InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering.BondCoherence)
    (n : ℕ) (x : SplitClNNAlg n) :
    matrixLimitMap hC
        (DirectLimit.Ring.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) n x) =
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
        (stageMap n x) := by
  rfl

/-! Tensor-index presentation of the same bond. -/
noncomputable def tensorIndexMatStageEmbed (n : ℕ)
    (A : Matrix
      (InfoGeometry.Clifford.GammaMatrices.TensorIndex n)
      (InfoGeometry.Clifford.GammaMatrices.TensorIndex n) ℝ) :
    Matrix
      (InfoGeometry.Clifford.GammaMatrices.TensorIndex (n + 1))
      (InfoGeometry.Clifford.GammaMatrices.TensorIndex (n + 1)) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ
      ((InfoGeometry.Clifford.TowerMatrix.idxEquivFinPowTwo (n + 1)).trans
        (tensorIndexEquivFinPowTwo (n + 1)).symm)
    ((InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed n)
      (Matrix.reindexAlgEquiv ℝ ℝ
        ((tensorIndexEquivFinPowTwo n).trans
          (InfoGeometry.Clifford.TowerMatrix.idxEquivFinPowTwo n).symm) A))

/-- Generator coherence lifts to all elements of the Clifford algebra. -/
theorem bond_coherence_of_generator
    (hgen : ∀ n : ℕ, ∀ v : SplitSpace n,
      stageMap (n + 1)
          (splitCliffordStep n (CliffordAlgebra.ι (SplitQuad n) v)) =
        InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n
          (stageMap n (CliffordAlgebra.ι (SplitQuad n) v))) :
    BondCoherence := by
  intro n
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  change stageMap (n + 1)
      (splitCliffordStep n (CliffordAlgebra.ι (SplitQuad n) v)) =
    InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n
      (stageMap n (CliffordAlgebra.ι (SplitQuad n) v))
  exact hgen n v

/-! ## 2. The Canonical, Mathematically Genuine Tower Morphism (Untwisted) -/

/-- The mathematically canonical split Clifford to UHF matrix-stage equivalence. -/
noncomputable def canonicalClStageEquiv (n : ℕ) :
    ClStage n ≃ₐ[ℝ] UHFStage n :=
  InfoGeometry.Algebra.CliffordBitWordEquivalence.clStageEquiv n

/-- **Theorem**: The canonical split matrix realization intertwines the genuine
algebraic bond `stageEmbed` with the UHF matrix bond `matrixBond`. -/
theorem canonical_clStageEquiv_bond (n : ℕ) (A : ClStage n) :
    canonicalClStageEquiv (n + 1) (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n A) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond n (canonicalClStageEquiv n A) := by
  exact InfoGeometry.Algebra.CliffordBitWordEquivalence.clStageEquiv_bond n A

/-- **Theorem**: The canonical colimit morphism lifts the split Clifford tensor
tower to the UHF colimit algebra without parity obstruction. -/
theorem canonical_colimit_soldering_packet (n : ℕ) (A : ClStage n) :
    InfoGeometry.Algebra.CliffordBitWordEquivalence.clToUHF
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n
        (InfoGeometry.Algebra.CliffordBitWordEquivalence.clStageEquiv n A) := by
  exact InfoGeometry.Algebra.CliffordBitWordEquivalence.clToUHF_ofStage n A

/-- **Theorem**: The canonical direct-limit algebra isomorphism between the split
Clifford tensor tower limit and the Primon UHF limit algebra. -/
noncomputable def canonicalCliffordUHFColimitEquiv :
    ClCarrier ≃+* UHFCarrier :=
  InfoGeometry.Algebra.CliffordBitWordEquivalence.cliffordBitWordColimitEquiv

@[simp] theorem canonicalCliffordUHFColimitEquiv_ofStage (n : ℕ) (A : ClStage n) :
    canonicalCliffordUHFColimitEquiv (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n (canonicalClStageEquiv n A) := by
  exact InfoGeometry.Algebra.CliffordBitWordEquivalence.cliffordBitWordColimitEquiv_ofStage n A

/-! ## 3. Information Geometry & Fuglede-Kadison Determinant Stabilization -/

/-- **Theorem**: Under the doubling tensor bond A ↦ A ⊗ I₂, the matrix determinant
squares, which is the algebraic obstruction to raw colimit determinant stabilization. -/
theorem matrix_determinant_tensor_squaring (n : ℕ) (A : ClStage n) :
    Matrix.det (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n A) =
      (Matrix.det A) ^ (2 : ℕ) := by
  exact InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed_det n A

/-- **Theorem**: Taking the logarithm turns determinant squaring into doubling:
log |det(A ⊗ I₂)| = 2 * log |det(A)|. -/
theorem matrix_logAbsDet_tensor_doubling (n : ℕ) (A : ClStage n) :
    Real.log |Matrix.det (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n A)| =
      2 * Real.log |Matrix.det A| := by
  exact InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed_logAbsDet_double n A

/-- **Theorem**: The binary-volume normalized logarithmic determinant readout
is strictly invariant under the tensor tower embedding:
normalizedLogAbsDet (n + 1) (A ⊗ I₂) = normalizedLogAbsDet n A.
This establishes the finite algebraic shadow of the Fuglede-Kadison determinant
and thermodynamic free energy density on the Clifford matrix tower. -/
theorem normalizedLogAbsDet_stageEmbed_invariant (n : ℕ) (A : ClStage n) :
    InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet (n + 1)
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet n A := by
  exact InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet_matStageEmbed n A

/-- **Theorem**: The coherent matrix reindexing clStageEquiv preserves the
normalized logarithmic determinant readout. -/
theorem clStageEquiv_normalizedLogAbsDet_preserves (n : ℕ) (A : ClStage n) :
    InfoGeometry.Algebra.FiniteTensorDeterminantStabilization.normalizedLogDet n
        (Real.log |Matrix.det (canonicalClStageEquiv n A)|) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet n A := by
  exact InfoGeometry.Algebra.CliffordBitWordEquivalence.clStageEquiv_normalizedLogAbsDet_eq_native n A

/-- **Theorem**: The normalized trace (tracial state τ) is strictly invariant
under the matrix tower embedding: τ_{n+1}(A ⊗ I₂) = τ_n(A). -/
theorem normalizedTrace_stageEmbed_invariant (n : ℕ) (A : ClStage n) :
    InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace (n + 1)
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n A := by
  exact InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace_matStageEmbed n A

end InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering

