import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealSplitKreinHilbertizationBridge
import InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
import InfoGeometry.Canonical.Cl55MasterHestenesPhaseBridge

/-!
# Native finite `Module.End` readout for the Cl(5,5) master packet

This is the finite algebraic bridge from the repository's matrix carrier to
Mathlib's native endomorphism carrier.  It uses `Matrix.toLin'` and proves the
transport of the matrix unit, addition, scalar, and multiplication laws.
It does not add a norm completion, unbounded-operator regularity, or a
Kasparov class.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge

open Matrix
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
open InfoGeometry.Canonical.RealSplitKreinHilbertizationBridge
open InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
open InfoGeometry.Canonical.Cl55MasterHestenesPhaseBridge

abbrev SpinorCarrier := InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ
abbrev SpinorEnd := Module.End ℝ SpinorCarrier
abbrev Mat32 := Cl55MasterWittSpinorEnvelopeBridge.Mat32

abbrev NativeSpinorCarrier := EuclideanSpace ℝ (Fin 32)
abbrev NativeSpinorCLM := NativeSpinorCarrier →L[ℝ] NativeSpinorCarrier

local instance nativeSpinorT2Space : T2Space NativeSpinorCarrier :=
  TopologicalSpace.t2Space_of_metrizableSpace

noncomputable def matrixEnd (A : Mat32) : SpinorEnd := Matrix.toLin' A

@[simp] theorem matrixEnd_apply (A : Mat32) (v : SpinorCarrier) :
    matrixEnd A v = A *ᵥ v := by
  rfl

theorem matrixEnd_one : matrixEnd (1 : Mat32) = (1 : SpinorEnd) := by
  ext v i
  simp [matrixEnd]

theorem matrixEnd_add (A B : Mat32) :
    matrixEnd (A + B) = matrixEnd A + matrixEnd B := by
  ext v i
  simp [matrixEnd]

theorem matrixEnd_smul (c : ℝ) (A : Mat32) :
    matrixEnd (c • A) = c • matrixEnd A := by
  ext v i
  simp [matrixEnd]

theorem matrixEnd_mul (A B : Mat32) :
    matrixEnd (A * B) = matrixEnd A * matrixEnd B := by
  ext v i
  simp [matrixEnd]

theorem matrixEnd_zero : matrixEnd (0 : Mat32) = (0 : SpinorEnd) := by
  ext v i
  simp [matrixEnd]

noncomputable def nativeMatrix (A : Mat32) :
    Matrix (Fin 32) (Fin 32) ℝ :=
  InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5 A

theorem nativeMatrix_mul (A B : Mat32) :
    nativeMatrix (A * B) = nativeMatrix A * nativeMatrix B := by
  exact (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).map_mul A B

theorem nativeMatrix_add (A B : Mat32) :
    nativeMatrix (A + B) = nativeMatrix A + nativeMatrix B := by
  exact (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).map_add A B

theorem nativeMatrix_smul (c : ℝ) (A : Mat32) :
    nativeMatrix (c • A) = c • nativeMatrix A := by
  exact (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).toLinearMap.map_smul c A

theorem nativeMatrix_zero : nativeMatrix (0 : Mat32) = 0 := by
  exact (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).map_zero

theorem nativeMatrix_transpose_of_transpose (A : Mat32) (hA : Aᵀ = A) :
    (nativeMatrix A)ᵀ = nativeMatrix A := by
  let e := InfoGeometry.Clifford.TowerMatrix.idxEquivFinPowTwo 5
  change (Matrix.reindex e e A)ᵀ = Matrix.reindex e e A
  rw [Matrix.transpose_reindex, hA]

theorem nativeMatrix_one : nativeMatrix (1 : Mat32) = 1 := by
  exact (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).map_one

noncomputable def nativeContinuous (A : Mat32) : NativeSpinorCLM :=
  LinearMap.toContinuousLinearMap
    (𝕜 := ℝ) (E := NativeSpinorCarrier) (F' := NativeSpinorCarrier)
    (Matrix.toEuclideanLin (nativeMatrix A))

@[simp] theorem nativeContinuous_apply (A : Mat32) (v : NativeSpinorCarrier) :
    nativeContinuous A v = Matrix.toEuclideanLin (nativeMatrix A) v := by
  change Matrix.toEuclideanLin (nativeMatrix A) v = _
  rfl

theorem nativeContinuous_mul (A B : Mat32) :
    nativeContinuous (A * B) =
      (nativeContinuous A).comp (nativeContinuous B) := by
  apply ContinuousLinearMap.ext
  intro v
  ext x
  simp [nativeContinuous_apply, nativeMatrix_mul, Matrix.mulVec_mulVec]

theorem nativeContinuous_one :
    nativeContinuous (1 : Mat32) = ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  apply ContinuousLinearMap.ext
  intro v
  ext x
  simp [nativeContinuous_apply, nativeMatrix_one]

theorem nativeContinuous_add (A B : Mat32) :
    nativeContinuous (A + B) = nativeContinuous A + nativeContinuous B := by
  apply ContinuousLinearMap.ext
  intro v
  ext x
  simp [nativeContinuous_apply, nativeMatrix_add]

theorem nativeContinuous_smul (c : ℝ) (A : Mat32) :
    nativeContinuous (c • A) = c • nativeContinuous A := by
  apply ContinuousLinearMap.ext
  intro v
  ext x
  simp [nativeContinuous_apply, nativeMatrix_smul]

theorem nativeContinuous_zero :
    nativeContinuous (0 : Mat32) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  ext x
  simp [nativeContinuous_apply, nativeMatrix_zero]

theorem nativeMatrix_neg (A : Mat32) :
    nativeMatrix (-A) = -nativeMatrix A := by
  exact (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).toLinearMap.map_neg A

theorem nativeContinuous_neg (A : Mat32) :
    nativeContinuous (-A) = -nativeContinuous A := by
  apply ContinuousLinearMap.ext
  intro v
  ext x
  simp [nativeContinuous_apply, nativeMatrix_neg]

theorem nativeContinuous_sub (A B : Mat32) :
    nativeContinuous (A - B) = nativeContinuous A - nativeContinuous B := by
  rw [sub_eq_add_neg, nativeContinuous_add, nativeContinuous_neg,
    sub_eq_add_neg]

theorem nativeContinuous_self_adjoint_of_transpose (A : Mat32) (hA : Aᵀ = A) :
    ContinuousLinearMap.adjoint (nativeContinuous A) = nativeContinuous A := by
  have hM : (nativeMatrix A)ᵀ = nativeMatrix A :=
    nativeMatrix_transpose_of_transpose A hA
  have hC : (nativeMatrix A).conjTranspose = nativeMatrix A := by
    ext i j
    simpa [Matrix.conjTranspose] using congrArg (fun M => M i j) hM
  have hlin : (Matrix.toEuclideanLin (nativeMatrix A)).adjoint =
      Matrix.toEuclideanLin (nativeMatrix A) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    exact congrArg Matrix.toEuclideanLin hC
  change ContinuousLinearMap.adjoint
      (LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin (nativeMatrix A))) = _
  rw [← LinearMap.adjoint_toContinuousLinearMap]
  exact congrArg LinearMap.toContinuousLinearMap hlin

theorem nativeMatrix_transpose (A : Mat32) :
    (nativeMatrix A)ᵀ = nativeMatrix Aᵀ := by
  let e := InfoGeometry.Clifford.TowerMatrix.idxEquivFinPowTwo 5
  change (Matrix.reindex e e A)ᵀ = Matrix.reindex e e Aᵀ
  rw [Matrix.transpose_reindex]

theorem nativeContinuous_adjoint_eq_transpose (A : Mat32) :
    ContinuousLinearMap.adjoint (nativeContinuous A) =
      nativeContinuous Aᵀ := by
  have hM : (nativeMatrix A)ᵀ = nativeMatrix Aᵀ := nativeMatrix_transpose A
  have hC : (nativeMatrix A).conjTranspose = nativeMatrix Aᵀ := by
    ext i j
    simpa [Matrix.conjTranspose] using congrArg (fun M => M i j) hM
  have hlin : (Matrix.toEuclideanLin (nativeMatrix A)).adjoint =
      Matrix.toEuclideanLin (nativeMatrix Aᵀ) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    exact congrArg Matrix.toEuclideanLin hC
  change ContinuousLinearMap.adjoint
      (LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin (nativeMatrix A))) = _
  rw [← LinearMap.adjoint_toContinuousLinearMap]
  exact congrArg LinearMap.toContinuousLinearMap hlin

def hodgeDiracEnd : SpinorEnd := matrixEnd embeddedSplitOctonionHodgeDirac
def chiralityEnd : SpinorEnd := matrixEnd MasterChirality
def normalizedDiracEnd : SpinorEnd := matrixEnd masterBoundedTransform

theorem hodgeDiracEnd_ker_eq_bot : LinearMap.ker hodgeDiracEnd = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro v w hvw
  have hzero : hodgeDiracEnd (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hzero' : v - w = 0 := by
    apply master_hodge_kernel_trivial
    simpa [hodgeDiracEnd, matrixEnd_apply] using hzero
  exact sub_eq_zero.mp hzero'

theorem hodgeDiracEnd_injective : Function.Injective hodgeDiracEnd := by
  rw [← LinearMap.ker_eq_bot]
  exact hodgeDiracEnd_ker_eq_bot

theorem hodgeDiracEnd_surjective : Function.Surjective hodgeDiracEnd :=
  LinearMap.surjective_of_injective hodgeDiracEnd_injective

theorem hodgeDiracEnd_range_eq_top : LinearMap.range hodgeDiracEnd = ⊤ :=
  LinearMap.range_eq_top.mpr hodgeDiracEnd_surjective

theorem normalizedDiracEnd_ker_eq_bot : LinearMap.ker normalizedDiracEnd = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro v w hvw
  have hzero : normalizedDiracEnd (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hzero' : v - w = 0 := by
    apply masterBoundedTransform_kernel_trivial
    simpa [normalizedDiracEnd, matrixEnd_apply] using hzero
  exact sub_eq_zero.mp hzero'

theorem normalizedDiracEnd_injective : Function.Injective normalizedDiracEnd := by
  rw [← LinearMap.ker_eq_bot]
  exact normalizedDiracEnd_ker_eq_bot

theorem normalizedDiracEnd_surjective : Function.Surjective normalizedDiracEnd :=
  LinearMap.surjective_of_injective normalizedDiracEnd_injective

theorem normalizedDiracEnd_range_eq_top : LinearMap.range normalizedDiracEnd = ⊤ :=
  LinearMap.range_eq_top.mpr normalizedDiracEnd_surjective

theorem hodgeDiracEnd_sq :
    hodgeDiracEnd * hodgeDiracEnd = (3 : ℝ) • (1 : SpinorEnd) := by
  unfold hodgeDiracEnd
  rw [← matrixEnd_mul, embeddedSplitOctonionHodgeDirac_sq]
  calc
    matrixEnd ((3 : ℝ) • (1 : Mat32)) =
        (3 : ℝ) • matrixEnd (1 : Mat32) := matrixEnd_smul 3 1
    _ = (3 : ℝ) • (1 : SpinorEnd) := by rw [matrixEnd_one]

theorem chiralityEnd_sq :
    chiralityEnd * chiralityEnd = (1 : SpinorEnd) := by
  unfold chiralityEnd
  rw [← matrixEnd_mul, masterChirality_sq, matrixEnd_one]

theorem hodgeDiracEnd_anticomm_chirality :
    chiralityEnd * hodgeDiracEnd + hodgeDiracEnd * chiralityEnd = 0 := by
  unfold chiralityEnd hodgeDiracEnd
  rw [← matrixEnd_mul, ← matrixEnd_mul, ← matrixEnd_add]
  rw [masterChirality_anticomm_hodge, matrixEnd_zero]

theorem normalizedDiracEnd_sq :
    normalizedDiracEnd * normalizedDiracEnd =
      (3 / 4 : ℝ) • (1 : SpinorEnd) := by
  unfold normalizedDiracEnd
  rw [← matrixEnd_mul, masterBoundedTransform_sq]
  calc
    matrixEnd ((3 / 4 : ℝ) • (1 : Mat32)) =
        (3 / 4 : ℝ) • matrixEnd (1 : Mat32) := matrixEnd_smul (3 / 4) 1
    _ = (3 / 4 : ℝ) • (1 : SpinorEnd) := by rw [matrixEnd_one]

/-! The normalized finite Dirac operator is invertible as well: its square is
`(3 / 4) • I`, so `(4 / 3) • F` is a two-sided inverse.  This is a finite
matrix statement only; it is not an unbounded-operator or Kasparov claim. -/

def normalizedDiracEndInverse : SpinorEnd :=
  matrixEnd ((4 / 3 : ℝ) • masterBoundedTransform)

theorem normalizedDiracEnd_inverse_comp :
    normalizedDiracEndInverse * normalizedDiracEnd = (1 : SpinorEnd) := by
  unfold normalizedDiracEndInverse normalizedDiracEnd
  rw [← matrixEnd_mul, explicitInverse_mul_masterBoundedTransform,
    matrixEnd_one]

theorem normalizedDiracEnd_comp_inverse :
    normalizedDiracEnd * normalizedDiracEndInverse = (1 : SpinorEnd) := by
  unfold normalizedDiracEndInverse normalizedDiracEnd
  rw [← matrixEnd_mul, masterBoundedTransform_mul_explicitInverse,
    matrixEnd_one]

theorem normalizedDiracEnd_bijective : Function.Bijective normalizedDiracEnd := by
  constructor
  · intro v w hvw
    calc
      v = normalizedDiracEndInverse (normalizedDiracEnd v) := by
        simpa [normalizedDiracEndInverse, normalizedDiracEnd, matrixEnd_apply]
          using congrArg (fun T : SpinorEnd => T v)
            normalizedDiracEnd_inverse_comp.symm
      _ = normalizedDiracEndInverse (normalizedDiracEnd w) := by rw [hvw]
      _ = w := by
        simpa [normalizedDiracEndInverse, normalizedDiracEnd, matrixEnd_apply]
          using congrArg (fun T : SpinorEnd => T w)
            normalizedDiracEnd_inverse_comp
  · intro y
    refine ⟨normalizedDiracEndInverse y, ?_⟩
    simpa [normalizedDiracEndInverse, normalizedDiracEnd, matrixEnd_apply]
      using congrArg (fun T : SpinorEnd => T y) normalizedDiracEnd_comp_inverse

def nativeHodgeDirac : NativeSpinorCLM :=
  nativeContinuous embeddedSplitOctonionHodgeDirac

def nativeChirality : NativeSpinorCLM := nativeContinuous MasterChirality

def nativeNormalizedDirac : NativeSpinorCLM := nativeContinuous masterBoundedTransform

def nativeChiralProjectorPlus : NativeSpinorCLM :=
  nativeContinuous masterChiralProjectorPlus

def nativeChiralProjectorMinus : NativeSpinorCLM :=
  nativeContinuous masterChiralProjectorMinus

def nativeChiralDiracPlus : NativeSpinorCLM :=
  nativeContinuous masterChiralDiracPlus

def nativeChiralDiracMinus : NativeSpinorCLM :=
  nativeContinuous masterChiralDiracMinus

def nativeG2Action (g : G2SpinorRepresentation) : NativeSpinorCLM :=
  nativeContinuous g.rho

def nativeCreation (i : Fin 5) : NativeSpinorCLM :=
  nativeContinuous (masterCreation i)

def nativeAnnihilation (i : Fin 5) : NativeSpinorCLM :=
  nativeContinuous (masterAnnihilation i)

theorem nativeCreation_hilbert_adjoint (i : Fin 5) :
    ContinuousLinearMap.adjoint (nativeCreation i) = nativeAnnihilation i := by
  unfold nativeCreation nativeAnnihilation
  rw [nativeContinuous_adjoint_eq_transpose]
  change nativeContinuous ((masterCreation i)ᵀ) = nativeContinuous (masterAnnihilation i)
  exact congrArg nativeContinuous <|
    by simpa [masterCreation, masterAnnihilation] using
      (InfoGeometry.Canonical.Cl55WittCAR.creation_transpose i)

theorem nativeAnnihilation_hilbert_adjoint (i : Fin 5) :
    ContinuousLinearMap.adjoint (nativeAnnihilation i) = nativeCreation i := by
  unfold nativeCreation nativeAnnihilation
  rw [nativeContinuous_adjoint_eq_transpose]
  change nativeContinuous ((masterAnnihilation i)ᵀ) = nativeContinuous (masterCreation i)
  have hbase : (masterCreation i)ᵀ = masterAnnihilation i := by
    simpa [masterCreation, masterAnnihilation] using
      InfoGeometry.Canonical.Cl55WittCAR.creation_transpose i
  have htrans := congrArg Matrix.transpose hbase
  have hrev : (masterAnnihilation i)ᵀ = masterCreation i := by
    simpa only [Matrix.transpose_transpose] using htrans.symm
  exact congrArg nativeContinuous hrev

def nativeMasterHestenesPhase : NativeSpinorCLM :=
  nativeContinuous masterHestenesPhase

def nativeSuperchargeQ : NativeSpinorCLM :=
  nativeContinuous chiralSuperchargeQ

def nativeSuperchargeQBar : NativeSpinorCLM :=
  nativeContinuous chiralSuperchargeQBar

def nativeInducedEvenMomentum : NativeSpinorCLM :=
  nativeContinuous inducedEvenMomentum

def nativeHodgeModeZero : NativeSpinorCLM :=
  nativeContinuous (masterCreation 0 + masterAnnihilation 0)

theorem nativeSuperchargeQ_sq_zero :
    nativeSuperchargeQ.comp nativeSuperchargeQ = 0 := by
  unfold nativeSuperchargeQ
  rw [← nativeContinuous_mul, chiralSupercharge_sq.1, nativeContinuous_zero]

theorem nativeSuperchargeQBar_sq_zero :
    nativeSuperchargeQBar.comp nativeSuperchargeQBar = 0 := by
  unfold nativeSuperchargeQBar
  rw [← nativeContinuous_mul, chiralSupercharge_sq.2, nativeContinuous_zero]

theorem nativeSupercharge_anticommutator_eq_two_momentum :
    nativeSuperchargeQ.comp nativeSuperchargeQBar +
        nativeSuperchargeQBar.comp nativeSuperchargeQ =
      (2 : ℝ) • nativeInducedEvenMomentum := by
  unfold nativeSuperchargeQ nativeSuperchargeQBar nativeInducedEvenMomentum
  rw [← nativeContinuous_mul, ← nativeContinuous_mul, ← nativeContinuous_add,
    ← nativeContinuous_smul]
  exact congrArg nativeContinuous susy_anticommutator_eq_two_momentum

theorem chiralSuperchargeQ_transpose :
    chiralSuperchargeQᵀ = chiralSuperchargeQBar := by
  dsimp [chiralSuperchargeQ, chiralSuperchargeQBar, masterCreation,
    masterAnnihilation]
  rw [Matrix.transpose_add,
    InfoGeometry.Canonical.Cl55WittCAR.creation_transpose 3,
    InfoGeometry.Canonical.Cl55WittCAR.creation_transpose 4]

theorem chiralSuperchargeQBar_transpose :
    chiralSuperchargeQBarᵀ = chiralSuperchargeQ := by
  rw [← chiralSuperchargeQ_transpose]
  exact Matrix.transpose_transpose chiralSuperchargeQ

theorem inducedEvenMomentum_transpose :
    inducedEvenMomentumᵀ = inducedEvenMomentum := by
  unfold inducedEvenMomentum
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_mul, chiralSuperchargeQ_transpose,
    chiralSuperchargeQBar_transpose]

theorem nativeSuperchargeQBar_is_hilbert_adjoint :
    ContinuousLinearMap.adjoint nativeSuperchargeQ = nativeSuperchargeQBar := by
  unfold nativeSuperchargeQ nativeSuperchargeQBar
  rw [nativeContinuous_adjoint_eq_transpose, chiralSuperchargeQ_transpose]

theorem nativeSuperchargeQ_is_hilbert_adjoint :
    ContinuousLinearMap.adjoint nativeSuperchargeQBar = nativeSuperchargeQ := by
  unfold nativeSuperchargeQ nativeSuperchargeQBar
  rw [nativeContinuous_adjoint_eq_transpose, chiralSuperchargeQBar_transpose]

theorem nativeInducedEvenMomentum_is_hilbert_self_adjoint :
    ContinuousLinearMap.adjoint nativeInducedEvenMomentum =
      nativeInducedEvenMomentum := by
  unfold nativeInducedEvenMomentum
  rw [nativeContinuous_adjoint_eq_transpose, inducedEvenMomentum_transpose]

theorem nativeMasterChirality_anticomm_supercharge :
    nativeChirality.comp nativeSuperchargeQ +
        nativeSuperchargeQ.comp nativeChirality = 0 ∧
    nativeChirality.comp nativeSuperchargeQBar +
        nativeSuperchargeQBar.comp nativeChirality = 0 := by
  unfold nativeChirality nativeSuperchargeQ nativeSuperchargeQBar
  rw [← nativeContinuous_mul, ← nativeContinuous_mul, ← nativeContinuous_add,
    ← nativeContinuous_mul, ← nativeContinuous_mul, ← nativeContinuous_add]
  constructor
  · have h := congrArg nativeContinuous masterChirality_anticomm_supercharge.1
    rw [nativeContinuous_zero] at h
    exact h
  · have h := congrArg nativeContinuous masterChirality_anticomm_supercharge.2
    rw [nativeContinuous_zero] at h
    exact h

theorem nativeMasterChirality_commutes_inducedEvenMomentum :
    nativeChirality.comp nativeInducedEvenMomentum =
      nativeInducedEvenMomentum.comp nativeChirality := by
  unfold nativeChirality nativeInducedEvenMomentum
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous masterChirality_commutes_inducedEvenMomentum

theorem masterInducedEvenMomentum_comp_projectorPlus :
    inducedEvenMomentum * masterChiralProjectorPlus =
      masterChiralProjectorPlus * inducedEvenMomentum := by
  unfold masterChiralProjectorPlus
  rw [mul_smul_comm, smul_mul_assoc]
  simp only [mul_add, add_mul, mul_one, one_mul]
  rw [masterChirality_commutes_inducedEvenMomentum]

theorem masterInducedEvenMomentum_comp_projectorMinus :
    inducedEvenMomentum * masterChiralProjectorMinus =
      masterChiralProjectorMinus * inducedEvenMomentum := by
  unfold masterChiralProjectorMinus
  rw [mul_smul_comm, smul_mul_assoc]
  simp only [mul_sub, sub_mul, mul_one, one_mul]
  rw [masterChirality_commutes_inducedEvenMomentum]

theorem nativeInducedEvenMomentum_comp_projectorPlus :
    nativeInducedEvenMomentum.comp nativeChiralProjectorPlus =
      nativeChiralProjectorPlus.comp nativeInducedEvenMomentum := by
  unfold nativeInducedEvenMomentum nativeChiralProjectorPlus
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous masterInducedEvenMomentum_comp_projectorPlus

theorem nativeInducedEvenMomentum_comp_projectorMinus :
    nativeInducedEvenMomentum.comp nativeChiralProjectorMinus =
      nativeChiralProjectorMinus.comp nativeInducedEvenMomentum := by
  unfold nativeInducedEvenMomentum nativeChiralProjectorMinus
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous masterInducedEvenMomentum_comp_projectorMinus

theorem masterSuperchargeQ_comp_projectorPlus :
    chiralSuperchargeQ * masterChiralProjectorPlus =
      masterChiralProjectorMinus * chiralSuperchargeQ := by
  rw [masterChiralProjectorPlus, masterChiralProjectorMinus,
    mul_smul_comm, smul_mul_assoc]
  simp only [mul_add, mul_one, one_mul, sub_mul]
  have hodd := masterChirality_anticomm_supercharge.1
  have hodd' : chiralSuperchargeQ * MasterChirality +
      MasterChirality * chiralSuperchargeQ = 0 := by
    simpa [add_comm] using hodd
  rw [show chiralSuperchargeQ * MasterChirality =
      -(MasterChirality * chiralSuperchargeQ) by
        exact eq_neg_of_add_eq_zero_left hodd']
  module

theorem masterSuperchargeQ_comp_projectorMinus :
    chiralSuperchargeQ * masterChiralProjectorMinus =
      masterChiralProjectorPlus * chiralSuperchargeQ := by
  rw [masterChiralProjectorMinus, masterChiralProjectorPlus,
    mul_smul_comm, smul_mul_assoc]
  simp only [mul_sub, add_mul, mul_one, one_mul]
  have hodd := masterChirality_anticomm_supercharge.1
  have hodd' : chiralSuperchargeQ * MasterChirality +
      MasterChirality * chiralSuperchargeQ = 0 := by
    simpa [add_comm] using hodd
  rw [show chiralSuperchargeQ * MasterChirality =
      -(MasterChirality * chiralSuperchargeQ) by
        exact eq_neg_of_add_eq_zero_left hodd']
  module

theorem masterSuperchargeQBar_comp_projectorPlus :
    chiralSuperchargeQBar * masterChiralProjectorPlus =
      masterChiralProjectorMinus * chiralSuperchargeQBar := by
  rw [masterChiralProjectorPlus, masterChiralProjectorMinus,
    mul_smul_comm, smul_mul_assoc]
  simp only [mul_add, mul_one, one_mul, sub_mul]
  have hodd := masterChirality_anticomm_supercharge.2
  have hodd' : chiralSuperchargeQBar * MasterChirality +
      MasterChirality * chiralSuperchargeQBar = 0 := by
    simpa [add_comm] using hodd
  rw [show chiralSuperchargeQBar * MasterChirality =
      -(MasterChirality * chiralSuperchargeQBar) by
        exact eq_neg_of_add_eq_zero_left hodd']
  module

theorem masterSuperchargeQBar_comp_projectorMinus :
    chiralSuperchargeQBar * masterChiralProjectorMinus =
      masterChiralProjectorPlus * chiralSuperchargeQBar := by
  rw [masterChiralProjectorMinus, masterChiralProjectorPlus,
    mul_smul_comm, smul_mul_assoc]
  simp only [mul_sub, add_mul, mul_one, one_mul]
  have hodd := masterChirality_anticomm_supercharge.2
  have hodd' : chiralSuperchargeQBar * MasterChirality +
      MasterChirality * chiralSuperchargeQBar = 0 := by
    simpa [add_comm] using hodd
  rw [show chiralSuperchargeQBar * MasterChirality =
      -(MasterChirality * chiralSuperchargeQBar) by
        exact eq_neg_of_add_eq_zero_left hodd']
  module

theorem nativeSuperchargeQ_comp_projectorPlus :
    nativeSuperchargeQ.comp nativeChiralProjectorPlus =
      nativeChiralProjectorMinus.comp nativeSuperchargeQ := by
  unfold nativeSuperchargeQ nativeChiralProjectorPlus nativeChiralProjectorMinus
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous masterSuperchargeQ_comp_projectorPlus

theorem nativeSuperchargeQ_comp_projectorMinus :
    nativeSuperchargeQ.comp nativeChiralProjectorMinus =
      nativeChiralProjectorPlus.comp nativeSuperchargeQ := by
  unfold nativeSuperchargeQ nativeChiralProjectorMinus nativeChiralProjectorPlus
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous masterSuperchargeQ_comp_projectorMinus

theorem nativeSuperchargeQBar_comp_projectorPlus :
    nativeSuperchargeQBar.comp nativeChiralProjectorPlus =
      nativeChiralProjectorMinus.comp nativeSuperchargeQBar := by
  unfold nativeSuperchargeQBar nativeChiralProjectorPlus nativeChiralProjectorMinus
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous masterSuperchargeQBar_comp_projectorPlus

theorem nativeSuperchargeQBar_comp_projectorMinus :
    nativeSuperchargeQBar.comp nativeChiralProjectorMinus =
      nativeChiralProjectorPlus.comp nativeSuperchargeQBar := by
  unfold nativeSuperchargeQBar nativeChiralProjectorMinus nativeChiralProjectorPlus
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous masterSuperchargeQBar_comp_projectorMinus

theorem nativeHodgeModeZero_anticomm_supercharge :
    nativeHodgeModeZero.comp nativeSuperchargeQ +
        nativeSuperchargeQ.comp nativeHodgeModeZero = 0 := by
  unfold nativeHodgeModeZero nativeSuperchargeQ
  rw [← nativeContinuous_mul, ← nativeContinuous_mul, ← nativeContinuous_add]
  have h := congrArg nativeContinuous hodge_susy_anticommutator_zero
  rw [nativeContinuous_zero] at h
  exact h

theorem masterHodgeDirac_anticomm_supercharge :
    embeddedSplitOctonionHodgeDirac * chiralSuperchargeQ +
        chiralSuperchargeQ * embeddedSplitOctonionHodgeDirac = 0 := by
  have h03 := masterCAR_cross_site (i := (0 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have h04 := masterCAR_cross_site (i := (0 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have h13 := masterCAR_cross_site (i := (1 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have h14 := masterCAR_cross_site (i := (1 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have h23 := masterCAR_cross_site (i := (2 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have h24 := masterCAR_cross_site (i := (2 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have h30 := masterCAR_cross_site (i := (3 : Fin 5)) (j := (0 : Fin 5)) (by decide)
  have h40 := masterCAR_cross_site (i := (4 : Fin 5)) (j := (0 : Fin 5)) (by decide)
  have h31 := masterCAR_cross_site (i := (3 : Fin 5)) (j := (1 : Fin 5)) (by decide)
  have h41 := masterCAR_cross_site (i := (4 : Fin 5)) (j := (1 : Fin 5)) (by decide)
  have h32 := masterCAR_cross_site (i := (3 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have h42 := masterCAR_cross_site (i := (4 : Fin 5)) (j := (2 : Fin 5)) (by decide)
  have h30' : masterAnnihilation 0 * masterCreation 3 +
      masterCreation 3 * masterAnnihilation 0 = 0 := by
    simpa [add_comm] using h30.2.2
  have h40' : masterAnnihilation 0 * masterCreation 4 +
      masterCreation 4 * masterAnnihilation 0 = 0 := by
    simpa [add_comm] using h40.2.2
  have h31' : masterAnnihilation 1 * masterCreation 3 +
      masterCreation 3 * masterAnnihilation 1 = 0 := by
    simpa [add_comm] using h31.2.2
  have h41' : masterAnnihilation 1 * masterCreation 4 +
      masterCreation 4 * masterAnnihilation 1 = 0 := by
    simpa [add_comm] using h41.2.2
  have h32' : masterAnnihilation 2 * masterCreation 3 +
      masterCreation 3 * masterAnnihilation 2 = 0 := by
    simpa [add_comm] using h32.2.2
  have h42' : masterAnnihilation 2 * masterCreation 4 +
      masterCreation 4 * masterAnnihilation 2 = 0 := by
    simpa [add_comm] using h42.2.2
  calc
    embeddedSplitOctonionHodgeDirac * chiralSuperchargeQ +
          chiralSuperchargeQ * embeddedSplitOctonionHodgeDirac =
        (masterCreation 0 * masterCreation 3 +
            masterCreation 3 * masterCreation 0) +
        (masterCreation 0 * masterCreation 4 +
            masterCreation 4 * masterCreation 0) +
        (masterAnnihilation 0 * masterCreation 3 +
            masterCreation 3 * masterAnnihilation 0) +
        (masterAnnihilation 0 * masterCreation 4 +
            masterCreation 4 * masterAnnihilation 0) +
        (masterCreation 1 * masterCreation 3 +
            masterCreation 3 * masterCreation 1) +
        (masterCreation 1 * masterCreation 4 +
            masterCreation 4 * masterCreation 1) +
        (masterAnnihilation 1 * masterCreation 3 +
            masterCreation 3 * masterAnnihilation 1) +
        (masterAnnihilation 1 * masterCreation 4 +
            masterCreation 4 * masterAnnihilation 1) +
        (masterCreation 2 * masterCreation 3 +
            masterCreation 3 * masterCreation 2) +
        (masterCreation 2 * masterCreation 4 +
            masterCreation 4 * masterCreation 2) +
        (masterAnnihilation 2 * masterCreation 3 +
            masterCreation 3 * masterAnnihilation 2) +
        (masterAnnihilation 2 * masterCreation 4 +
            masterCreation 4 * masterAnnihilation 2) := by
          dsimp [embeddedSplitOctonionHodgeDirac, chiralSuperchargeQ]
          noncomm_ring
    _ = 0 := by
          rw [h03.1, h04.1, h30', h40',
            h13.1, h14.1, h31', h41',
            h23.1, h24.1, h32', h42']
          simp

theorem masterHodgeDirac_anticomm_superchargeBar :
    embeddedSplitOctonionHodgeDirac * chiralSuperchargeQBar +
        chiralSuperchargeQBar * embeddedSplitOctonionHodgeDirac = 0 := by
  have h03 := masterCAR_cross_site (i := (0 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have h04 := masterCAR_cross_site (i := (0 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have h13 := masterCAR_cross_site (i := (1 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have h14 := masterCAR_cross_site (i := (1 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  have h23 := masterCAR_cross_site (i := (2 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have h24 := masterCAR_cross_site (i := (2 : Fin 5)) (j := (4 : Fin 5)) (by decide)
  calc
    embeddedSplitOctonionHodgeDirac * chiralSuperchargeQBar +
          chiralSuperchargeQBar * embeddedSplitOctonionHodgeDirac =
        (masterCreation 0 * masterAnnihilation 3 +
            masterAnnihilation 3 * masterCreation 0) +
        (masterCreation 0 * masterAnnihilation 4 +
            masterAnnihilation 4 * masterCreation 0) +
        (masterAnnihilation 0 * masterAnnihilation 3 +
            masterAnnihilation 3 * masterAnnihilation 0) +
        (masterAnnihilation 0 * masterAnnihilation 4 +
            masterAnnihilation 4 * masterAnnihilation 0) +
        (masterCreation 1 * masterAnnihilation 3 +
            masterAnnihilation 3 * masterCreation 1) +
        (masterCreation 1 * masterAnnihilation 4 +
            masterAnnihilation 4 * masterCreation 1) +
        (masterAnnihilation 1 * masterAnnihilation 3 +
            masterAnnihilation 3 * masterAnnihilation 1) +
        (masterAnnihilation 1 * masterAnnihilation 4 +
            masterAnnihilation 4 * masterAnnihilation 1) +
        (masterCreation 2 * masterAnnihilation 3 +
            masterAnnihilation 3 * masterCreation 2) +
        (masterCreation 2 * masterAnnihilation 4 +
            masterAnnihilation 4 * masterCreation 2) +
        (masterAnnihilation 2 * masterAnnihilation 3 +
            masterAnnihilation 3 * masterAnnihilation 2) +
        (masterAnnihilation 2 * masterAnnihilation 4 +
            masterAnnihilation 4 * masterAnnihilation 2) := by
          dsimp [embeddedSplitOctonionHodgeDirac, chiralSuperchargeQBar]
          noncomm_ring
    _ = 0 := by
          rw [h03.2.2, h04.2.2, h03.2.1, h04.2.1,
            h13.2.2, h14.2.2, h13.2.1, h14.2.1,
            h23.2.2, h24.2.2, h23.2.1, h24.2.1]
          simp

theorem nativeHodgeDirac_anticomm_supercharge :
    nativeHodgeDirac.comp nativeSuperchargeQ +
        nativeSuperchargeQ.comp nativeHodgeDirac = 0 := by
  unfold nativeHodgeDirac nativeSuperchargeQ
  rw [← nativeContinuous_mul, ← nativeContinuous_mul, ← nativeContinuous_add]
  have h := congrArg nativeContinuous masterHodgeDirac_anticomm_supercharge
  rw [nativeContinuous_zero] at h
  exact h

theorem nativeHodgeDirac_anticomm_superchargeBar :
    nativeHodgeDirac.comp nativeSuperchargeQBar +
        nativeSuperchargeQBar.comp nativeHodgeDirac = 0 := by
  unfold nativeHodgeDirac nativeSuperchargeQBar
  rw [← nativeContinuous_mul, ← nativeContinuous_mul, ← nativeContinuous_add]
  have h := congrArg nativeContinuous masterHodgeDirac_anticomm_superchargeBar
  rw [nativeContinuous_zero] at h
  exact h

theorem masterHodgeDirac_commutes_inducedEvenMomentum :
    embeddedSplitOctonionHodgeDirac * inducedEvenMomentum =
      inducedEvenMomentum * embeddedSplitOctonionHodgeDirac := by
  have hQ : embeddedSplitOctonionHodgeDirac * chiralSuperchargeQ =
      -(chiralSuperchargeQ * embeddedSplitOctonionHodgeDirac) :=
    eq_neg_of_add_eq_zero_left masterHodgeDirac_anticomm_supercharge
  have hQBar : embeddedSplitOctonionHodgeDirac * chiralSuperchargeQBar =
      -(chiralSuperchargeQBar * embeddedSplitOctonionHodgeDirac) :=
    eq_neg_of_add_eq_zero_left masterHodgeDirac_anticomm_superchargeBar
  unfold inducedEvenMomentum
  rw [Matrix.mul_smul, Matrix.smul_mul]
  apply congrArg (fun A : Mat32 => (1 / 2 : ℝ) • A)
  calc
    embeddedSplitOctonionHodgeDirac *
          (chiralSuperchargeQ * chiralSuperchargeQBar +
            chiralSuperchargeQBar * chiralSuperchargeQ) =
        (embeddedSplitOctonionHodgeDirac * chiralSuperchargeQ) *
            chiralSuperchargeQBar +
          (embeddedSplitOctonionHodgeDirac * chiralSuperchargeQBar) *
            chiralSuperchargeQ := by
              noncomm_ring
    _ = (-(chiralSuperchargeQ * embeddedSplitOctonionHodgeDirac)) *
            chiralSuperchargeQBar +
          (-(chiralSuperchargeQBar * embeddedSplitOctonionHodgeDirac)) *
            chiralSuperchargeQ := by
              rw [hQ, hQBar]
    _ = (chiralSuperchargeQ * chiralSuperchargeQBar +
          chiralSuperchargeQBar * chiralSuperchargeQ) *
            embeddedSplitOctonionHodgeDirac := by
              have h1 :
                  -(chiralSuperchargeQ * embeddedSplitOctonionHodgeDirac) *
                      chiralSuperchargeQBar =
                    chiralSuperchargeQ * chiralSuperchargeQBar *
                      embeddedSplitOctonionHodgeDirac := by
                calc
                  -(chiralSuperchargeQ * embeddedSplitOctonionHodgeDirac) *
                        chiralSuperchargeQBar =
                      -(chiralSuperchargeQ *
                        (embeddedSplitOctonionHodgeDirac *
                          chiralSuperchargeQBar)) := by
                            noncomm_ring
                  _ = -(chiralSuperchargeQ *
                        (-(chiralSuperchargeQBar *
                          embeddedSplitOctonionHodgeDirac))) := by
                            rw [hQBar]
                  _ = chiralSuperchargeQ * chiralSuperchargeQBar *
                        embeddedSplitOctonionHodgeDirac := by
                            noncomm_ring
              have h2 :
                  -(chiralSuperchargeQBar * embeddedSplitOctonionHodgeDirac) *
                      chiralSuperchargeQ =
                    chiralSuperchargeQBar * chiralSuperchargeQ *
                      embeddedSplitOctonionHodgeDirac := by
                calc
                  -(chiralSuperchargeQBar * embeddedSplitOctonionHodgeDirac) *
                        chiralSuperchargeQ =
                      -(chiralSuperchargeQBar *
                        (embeddedSplitOctonionHodgeDirac *
                          chiralSuperchargeQ)) := by
                            noncomm_ring
                  _ = -(chiralSuperchargeQBar *
                        (-(chiralSuperchargeQ *
                          embeddedSplitOctonionHodgeDirac))) := by
                            rw [hQ]
                  _ = chiralSuperchargeQBar * chiralSuperchargeQ *
                        embeddedSplitOctonionHodgeDirac := by
                            noncomm_ring
              rw [h1, h2]
              noncomm_ring

theorem nativeHodgeDirac_commutes_inducedEvenMomentum :
    nativeHodgeDirac.comp nativeInducedEvenMomentum =
      nativeInducedEvenMomentum.comp nativeHodgeDirac := by
  unfold nativeHodgeDirac nativeInducedEvenMomentum
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  have h := congrArg nativeContinuous masterHodgeDirac_commutes_inducedEvenMomentum
  exact h

theorem nativeHodgeDirac_sq :
    (nativeHodgeDirac).comp nativeHodgeDirac =
      (3 : ℝ) • ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  unfold nativeHodgeDirac
  rw [← nativeContinuous_mul, embeddedSplitOctonionHodgeDirac_sq]
  rw [nativeContinuous_smul, nativeContinuous_one]

theorem nativeChirality_sq :
    (nativeChirality).comp nativeChirality =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  unfold nativeChirality
  rw [← nativeContinuous_mul, masterChirality_sq, nativeContinuous_one]

theorem nativeHodgeDirac_anticomm_chirality :
    (nativeChirality).comp nativeHodgeDirac +
        (nativeHodgeDirac).comp nativeChirality = 0 := by
  unfold nativeChirality nativeHodgeDirac
  rw [← nativeContinuous_mul, ← nativeContinuous_mul, ← nativeContinuous_add]
  rw [masterChirality_anticomm_hodge, nativeContinuous_zero]

theorem nativeNormalizedDirac_sq :
    (nativeNormalizedDirac).comp nativeNormalizedDirac =
      (3 / 4 : ℝ) • ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  unfold nativeNormalizedDirac
  rw [← nativeContinuous_mul, masterBoundedTransform_sq]
  rw [nativeContinuous_smul, nativeContinuous_one]

theorem nativeHodgeDirac_hilbert_self_adjoint :
    ContinuousLinearMap.adjoint nativeHodgeDirac = nativeHodgeDirac := by
  exact nativeContinuous_self_adjoint_of_transpose
    embeddedSplitOctonionHodgeDirac embeddedSplitOctonionHodgeDirac_transpose

theorem nativeChirality_hilbert_self_adjoint :
    ContinuousLinearMap.adjoint nativeChirality = nativeChirality := by
  exact nativeContinuous_self_adjoint_of_transpose
    MasterChirality masterChirality_transpose

theorem nativeNormalizedDirac_hilbert_self_adjoint :
    ContinuousLinearMap.adjoint nativeNormalizedDirac = nativeNormalizedDirac := by
  exact nativeContinuous_self_adjoint_of_transpose
    masterBoundedTransform masterBoundedTransform_transpose

/-! Native Hilbertization of the finite Krein adjoint.  The fundamental
symmetry is the concrete chirality operator; this is the native counterpart
of `kreinAdjoint K T = K.eta * Tᵀ * K.eta`. -/

noncomputable def nativeKreinAdjoint (T : NativeSpinorCLM) : NativeSpinorCLM :=
  nativeChirality.comp ((ContinuousLinearMap.adjoint T).comp nativeChirality)

@[simp] theorem nativeKreinAdjoint_one :
    nativeKreinAdjoint (ContinuousLinearMap.id ℝ NativeSpinorCarrier) =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  simp [nativeKreinAdjoint, nativeChirality_sq]

theorem nativeKreinAdjoint_mul (S T : NativeSpinorCLM) :
    nativeKreinAdjoint (S.comp T) =
      (nativeKreinAdjoint T).comp (nativeKreinAdjoint S) := by
  have hC_apply (z : NativeSpinorCarrier) :
      nativeChirality (nativeChirality z) = z := by
    have h := congrArg (fun L : NativeSpinorCLM => L z) nativeChirality_sq
    simpa [ContinuousLinearMap.comp_apply] using h
  apply ContinuousLinearMap.ext
  intro x
  simp only [nativeKreinAdjoint, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_comp]
  rw [hC_apply]

@[simp] theorem nativeKreinAdjoint_involutive (T : NativeSpinorCLM) :
    nativeKreinAdjoint (nativeKreinAdjoint T) = T := by
  have hC_apply (z : NativeSpinorCarrier) :
      nativeChirality (nativeChirality z) = z := by
    have h := congrArg (fun L : NativeSpinorCLM => L z) nativeChirality_sq
    simpa [ContinuousLinearMap.comp_apply] using h
  apply ContinuousLinearMap.ext
  intro x
  simp only [nativeKreinAdjoint, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hCadj : ContinuousLinearMap.adjoint nativeChirality = nativeChirality :=
    nativeChirality_hilbert_self_adjoint
  rw [hCadj]
  rw [hC_apply]
  rw [hC_apply]

theorem nativeKreinAdjoint_eq_neg_of_self_adjoint_of_anticomm
    (T : NativeSpinorCLM)
    (hself : ContinuousLinearMap.adjoint T = T)
    (hodd : nativeChirality.comp T + T.comp nativeChirality = 0) :
    nativeKreinAdjoint T = -T := by
  unfold nativeKreinAdjoint
  rw [hself]
  have hodd' : nativeChirality.comp T = -(T.comp nativeChirality) := by
    exact eq_neg_of_add_eq_zero_left hodd
  calc
    nativeChirality.comp (T.comp nativeChirality) =
        (nativeChirality.comp T).comp nativeChirality := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = (-(T.comp nativeChirality)).comp nativeChirality := by
          rw [hodd']
    _ = -(T.comp (nativeChirality.comp nativeChirality)) := by
          rw [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc]
    _ = -T := by
          rw [nativeChirality_sq]
          simp

theorem nativeHodgeDirac_krein_skew_adjoint :
    nativeKreinAdjoint nativeHodgeDirac = -nativeHodgeDirac := by
  exact nativeKreinAdjoint_eq_neg_of_self_adjoint_of_anticomm
    nativeHodgeDirac nativeHodgeDirac_hilbert_self_adjoint
      nativeHodgeDirac_anticomm_chirality

theorem nativeNormalizedDirac_anticomm_chirality :
    (nativeChirality).comp nativeNormalizedDirac +
        (nativeNormalizedDirac).comp nativeChirality = 0 := by
  unfold nativeChirality nativeNormalizedDirac
  rw [← nativeContinuous_mul, ← nativeContinuous_mul, ← nativeContinuous_add]
  have h : MasterChirality * masterBoundedTransform +
      masterBoundedTransform * MasterChirality = 0 := by
    rw [add_comm]
    exact masterBoundedTransform_anticomm_chirality
  rw [h, nativeContinuous_zero]

theorem nativeNormalizedDirac_krein_skew_adjoint :
    nativeKreinAdjoint nativeNormalizedDirac = -nativeNormalizedDirac := by
  exact nativeKreinAdjoint_eq_neg_of_self_adjoint_of_anticomm
    nativeNormalizedDirac nativeNormalizedDirac_hilbert_self_adjoint
      nativeNormalizedDirac_anticomm_chirality

set_option synthInstance.maxHeartbeats 100000 in
theorem nativeNormalizedDirac_defect_scalar :
    nativeNormalizedDirac.comp nativeNormalizedDirac -
        ContinuousLinearMap.id ℝ NativeSpinorCarrier =
      (-1 / 4 : ℝ) • ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun T : NativeSpinorCLM => T v) nativeNormalizedDirac_sq
  have h' : nativeNormalizedDirac (nativeNormalizedDirac v) =
      (3 / 4 : ℝ) • v := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply] using h
  change nativeNormalizedDirac (nativeNormalizedDirac v) - v =
    (-1 / 4 : ℝ) • v
  rw [h']
  module

theorem nativeNormalizedDirac_comp_chiralProjectorPlus :
    nativeNormalizedDirac.comp nativeChiralProjectorPlus =
      nativeChiralProjectorMinus.comp nativeNormalizedDirac := by
  unfold nativeNormalizedDirac nativeChiralProjectorPlus nativeChiralProjectorMinus
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous masterBoundedTransform_chiral_transitions.1

theorem nativeNormalizedDirac_comp_chiralProjectorMinus :
    nativeNormalizedDirac.comp nativeChiralProjectorMinus =
      nativeChiralProjectorPlus.comp nativeNormalizedDirac := by
  unfold nativeNormalizedDirac nativeChiralProjectorPlus nativeChiralProjectorMinus
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous masterBoundedTransform_chiral_transitions.2

theorem nativeG2Action_commutes_hodge (g : G2SpinorRepresentation) :
    (nativeG2Action g).comp nativeHodgeDirac =
      nativeHodgeDirac.comp (nativeG2Action g) := by
  unfold nativeG2Action nativeHodgeDirac
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous g.commutes_hodge

theorem nativeG2Action_commutes_chirality (g : G2SpinorRepresentation) :
    (nativeG2Action g).comp nativeChirality =
      nativeChirality.comp (nativeG2Action g) := by
  unfold nativeG2Action nativeChirality
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous g.even_parity

theorem nativeG2Action_commutes_normalizedDirac (g : G2SpinorRepresentation) :
    (nativeG2Action g).comp nativeNormalizedDirac =
      nativeNormalizedDirac.comp (nativeG2Action g) := by
  unfold nativeG2Action nativeNormalizedDirac
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous (masterBoundedTransform_comm_g2 g)

theorem nativeG2Action_bracket (g h : G2SpinorRepresentation) :
    nativeG2Action (g2SpinorBracket g h) =
      (nativeG2Action g).comp (nativeG2Action h) -
        (nativeG2Action h).comp (nativeG2Action g) := by
  unfold nativeG2Action
  rw [g2SpinorBracket_rho, ← nativeContinuous_mul, ← nativeContinuous_mul,
    ← nativeContinuous_sub]

/-! The same transport, restricted to the actual Lie subalgebra carrier, is
packaged as a native Lie algebra morphism.  This remains infinitesimal: no
integration to a noncompact group is implicit. -/

noncomputable def nativeG2LieHom :
    g2SpinorLieSubalgebra →ₗ⁅ℝ⁆ NativeSpinorCLM where
  toFun := fun A => nativeContinuous (A : Mat32)
  map_add' := by
    intro A B
    exact nativeContinuous_add A B
  map_smul' := by
    intro r A
    exact nativeContinuous_smul r A
  map_lie' := by
    intro A B
    change nativeContinuous ((A : Mat32) * (B : Mat32) -
      (B : Mat32) * (A : Mat32)) =
      (nativeContinuous (A : Mat32)).comp (nativeContinuous (B : Mat32)) -
        (nativeContinuous (B : Mat32)).comp (nativeContinuous (A : Mat32))
    rw [← nativeContinuous_mul, ← nativeContinuous_mul, ← nativeContinuous_sub]

@[simp] theorem nativeG2LieHom_apply (A : g2SpinorLieSubalgebra) :
    nativeG2LieHom A = nativeContinuous (A : Mat32) := rfl

theorem nativeG2LieHom_commutes_chirality (A : g2SpinorLieSubalgebra) :
    (nativeG2LieHom A).comp nativeChirality =
      nativeChirality.comp (nativeG2LieHom A) := by
  change (nativeContinuous (A : Mat32)).comp nativeChirality =
    nativeChirality.comp (nativeContinuous (A : Mat32))
  unfold nativeChirality
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous A.property.1

theorem nativeG2LieHom_commutes_hodge (A : g2SpinorLieSubalgebra) :
    (nativeG2LieHom A).comp nativeHodgeDirac =
      nativeHodgeDirac.comp (nativeG2LieHom A) := by
  change (nativeContinuous (A : Mat32)).comp nativeHodgeDirac =
    nativeHodgeDirac.comp (nativeContinuous (A : Mat32))
  unfold nativeHodgeDirac
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous A.property.2

theorem nativeG2LieHom_commutes_normalizedDirac
    (A : g2SpinorLieSubalgebra) :
    (nativeG2LieHom A).comp nativeNormalizedDirac =
      nativeNormalizedDirac.comp (nativeG2LieHom A) := by
  change (nativeContinuous (A : Mat32)).comp nativeNormalizedDirac =
    nativeNormalizedDirac.comp (nativeContinuous (A : Mat32))
  unfold nativeNormalizedDirac
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  have h : (A : Mat32) * masterBoundedTransform =
      masterBoundedTransform * (A : Mat32) := by
    unfold masterBoundedTransform
    rw [mul_smul_comm, smul_mul_assoc, A.property.2]
  exact congrArg nativeContinuous h

theorem nativeMasterHestenesPhase_sq :
    nativeMasterHestenesPhase.comp nativeMasterHestenesPhase =
      -ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  unfold nativeMasterHestenesPhase
  rw [← nativeContinuous_mul, masterHestenesPhase_sq,
    nativeContinuous_neg, nativeContinuous_one]

theorem nativeMasterHestenesPhase_anticomm_chirality :
    nativeMasterHestenesPhase.comp nativeChirality +
        nativeChirality.comp nativeMasterHestenesPhase = 0 := by
  unfold nativeMasterHestenesPhase nativeChirality
  rw [← nativeContinuous_mul, ← nativeContinuous_mul, ← nativeContinuous_add]
  have h := masterHestenesPhase_anticomm_chirality
  simpa [MasterChirality] using
    (congrArg nativeContinuous h).trans nativeContinuous_zero

theorem nativeMasterHestenesPhase_comp_chiralProjectorPlus :
    nativeMasterHestenesPhase.comp nativeChiralProjectorPlus =
      nativeChiralProjectorMinus.comp nativeMasterHestenesPhase := by
  unfold nativeMasterHestenesPhase nativeChiralProjectorPlus
    nativeChiralProjectorMinus
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  simpa [masterChiralProjectorPlus, masterChiralProjectorMinus,
    chiralProjPlus, chiralProjMinus, MasterChirality] using
    congrArg nativeContinuous masterHestenesPhase_mul_chiralProjPlus

theorem nativeMasterHestenesPhase_comp_chiralProjectorMinus :
    nativeMasterHestenesPhase.comp nativeChiralProjectorMinus =
      nativeChiralProjectorPlus.comp nativeMasterHestenesPhase := by
  unfold nativeMasterHestenesPhase nativeChiralProjectorPlus
    nativeChiralProjectorMinus
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  simpa [masterChiralProjectorPlus, masterChiralProjectorMinus,
    chiralProjPlus, chiralProjMinus, MasterChirality] using
    congrArg nativeContinuous masterHestenesPhase_mul_chiralProjMinus

theorem nativeMasterHestenesPhase_commutes_hodge_square :
    nativeMasterHestenesPhase.comp (nativeHodgeDirac.comp nativeHodgeDirac) =
      (nativeHodgeDirac.comp nativeHodgeDirac).comp nativeMasterHestenesPhase := by
  unfold nativeMasterHestenesPhase nativeHodgeDirac
  simpa only [nativeContinuous_mul] using
    congrArg nativeContinuous masterHestenesPhase_commutes_hodgeDirac_square

theorem nativeContinuous_is_compact_operator (A : Mat32) :
    IsCompactOperator (nativeContinuous A) := by
  change IsCompactOperator (nativeContinuous A).toLinearMap
  rw [isCompactOperator_iff_isCompact_closure_image_closedBall
    (nativeContinuous A).toLinearMap (by norm_num : (0 : ℝ) < 1)]
  exact ((isCompact_closedBall (0 : NativeSpinorCarrier) 1).image
    (nativeContinuous A).continuous).closure

theorem nativeHodgeDirac_is_compact_operator :
    IsCompactOperator nativeHodgeDirac := by
  exact nativeContinuous_is_compact_operator embeddedSplitOctonionHodgeDirac

theorem nativeChirality_is_compact_operator :
    IsCompactOperator nativeChirality := by
  exact nativeContinuous_is_compact_operator MasterChirality

theorem nativeNormalizedDirac_is_compact_operator :
    IsCompactOperator nativeNormalizedDirac := by
  exact nativeContinuous_is_compact_operator masterBoundedTransform

def nativeHodgeDiracInverse : NativeSpinorCLM :=
  (1 / 3 : ℝ) • nativeHodgeDirac

theorem nativeHodgeDirac_inverse_comp :
    nativeHodgeDiracInverse.comp nativeHodgeDirac =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  unfold nativeHodgeDiracInverse
  rw [ContinuousLinearMap.smul_comp, nativeHodgeDirac_sq]
  norm_num [smul_smul]

theorem nativeHodgeDirac_comp_inverse :
    nativeHodgeDirac.comp nativeHodgeDiracInverse =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  unfold nativeHodgeDiracInverse
  rw [ContinuousLinearMap.comp_smul, nativeHodgeDirac_sq]
  norm_num [smul_smul]

def nativeNormalizedDiracInverse : NativeSpinorCLM :=
  (4 / 3 : ℝ) • nativeNormalizedDirac

theorem nativeNormalizedDirac_inverse_comp :
    nativeNormalizedDiracInverse.comp nativeNormalizedDirac =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  unfold nativeNormalizedDiracInverse
  rw [ContinuousLinearMap.smul_comp, nativeNormalizedDirac_sq]
  norm_num [smul_smul]

theorem nativeNormalizedDirac_comp_inverse :
    nativeNormalizedDirac.comp nativeNormalizedDiracInverse =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  unfold nativeNormalizedDiracInverse
  rw [ContinuousLinearMap.comp_smul, nativeNormalizedDirac_sq]
  norm_num [smul_smul]

theorem nativeNormalizedDirac_bijective :
    Function.Bijective nativeNormalizedDirac := by
  constructor
  · intro x y hxy
    calc
      x = nativeNormalizedDiracInverse (nativeNormalizedDirac x) := by
        simpa [ContinuousLinearMap.comp_apply] using
          (congrArg (fun T : NativeSpinorCLM => T x)
            nativeNormalizedDirac_inverse_comp).symm
      _ = nativeNormalizedDiracInverse (nativeNormalizedDirac y) := by rw [hxy]
      _ = y := by
        simpa [ContinuousLinearMap.comp_apply] using
          congrArg (fun T : NativeSpinorCLM => T y)
            nativeNormalizedDirac_inverse_comp
  · intro y
    refine ⟨nativeNormalizedDiracInverse y, ?_⟩
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : NativeSpinorCLM => T y)
        nativeNormalizedDirac_comp_inverse

theorem nativeNormalizedDirac_apply_eq_zero_iff (x : NativeSpinorCarrier) :
    nativeNormalizedDirac x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    exact nativeNormalizedDirac_bijective.1 (by simpa [hx])
  · intro hx
    simp [hx]

theorem nativeNormalizedDirac_no_harmonic_vectors :
    ∀ x : NativeSpinorCarrier, nativeNormalizedDirac x = 0 → x = 0 := by
  intro x hx
  exact nativeNormalizedDirac_apply_eq_zero_iff x |>.mp hx

theorem nativeHodgeDirac_injective : Function.Injective nativeHodgeDirac := by
  intro x y hxy
  calc
    x = nativeHodgeDiracInverse (nativeHodgeDirac x) := by
      simpa [ContinuousLinearMap.comp_apply] using
        (congrArg (fun T : NativeSpinorCLM => T x)
          nativeHodgeDirac_inverse_comp).symm
    _ = nativeHodgeDiracInverse (nativeHodgeDirac y) := by rw [hxy]
    _ = y := by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun T : NativeSpinorCLM => T y) nativeHodgeDirac_inverse_comp

/-! The scalar square relation has a stronger finite-dimensional consequence:
the concrete master Hodge--Dirac operator has no harmonic vectors.  This is a
statement about this finite carrier only; it is not an index theorem for a
boundary or infinite-dimensional Dirac realization. -/

theorem nativeHodgeDirac_apply_eq_zero_iff (x : NativeSpinorCarrier) :
    nativeHodgeDirac x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply nativeHodgeDirac_injective
    simp [hx]
  · intro hx
    simp [hx]

theorem nativeHodgeDirac_no_harmonic_vectors :
    ∀ x : NativeSpinorCarrier, nativeHodgeDirac x = 0 → x = 0 := by
  intro x hx
  exact nativeHodgeDirac_apply_eq_zero_iff x |>.mp hx

theorem nativeHodgeDirac_bijective :
    Function.Bijective nativeHodgeDirac := by
  constructor
  · exact nativeHodgeDirac_injective
  · intro y
    refine ⟨nativeHodgeDiracInverse y, ?_⟩
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : NativeSpinorCLM => T y) nativeHodgeDirac_comp_inverse

theorem nativeChiralProjectorPlus_sq :
    nativeChiralProjectorPlus.comp nativeChiralProjectorPlus =
      nativeChiralProjectorPlus := by
  unfold nativeChiralProjectorPlus
  rw [← nativeContinuous_mul, masterChiralProjectorPlus_sq]

theorem nativeChiralProjectorMinus_sq :
    nativeChiralProjectorMinus.comp nativeChiralProjectorMinus =
      nativeChiralProjectorMinus := by
  unfold nativeChiralProjectorMinus
  rw [← nativeContinuous_mul, masterChiralProjectorMinus_sq]

theorem nativeChiralProjectors_orthogonal :
    nativeChiralProjectorPlus.comp nativeChiralProjectorMinus = 0 ∧
      nativeChiralProjectorMinus.comp nativeChiralProjectorPlus = 0 := by
  constructor
  · unfold nativeChiralProjectorPlus nativeChiralProjectorMinus
    rw [← nativeContinuous_mul, masterChiralProjectors_orthogonal.1,
      nativeContinuous_zero]
  · unfold nativeChiralProjectorPlus nativeChiralProjectorMinus
    rw [← nativeContinuous_mul, masterChiralProjectors_orthogonal.2,
      nativeContinuous_zero]

theorem nativeChiralProjectors_sum :
    nativeChiralProjectorPlus + nativeChiralProjectorMinus =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  unfold nativeChiralProjectorPlus nativeChiralProjectorMinus
  rw [← nativeContinuous_add, masterChiralProjectors_sum, nativeContinuous_one]

theorem masterChiralProjectorPlus_transpose :
    masterChiralProjectorPlusᵀ = masterChiralProjectorPlus := by
  simp [masterChiralProjectorPlus, masterChirality_transpose]

theorem masterChiralProjectorMinus_transpose :
    masterChiralProjectorMinusᵀ = masterChiralProjectorMinus := by
  simp [masterChiralProjectorMinus, masterChirality_transpose]

theorem nativeChiralProjectorPlus_hilbert_self_adjoint :
    ContinuousLinearMap.adjoint nativeChiralProjectorPlus =
      nativeChiralProjectorPlus := by
  exact nativeContinuous_self_adjoint_of_transpose
    masterChiralProjectorPlus masterChiralProjectorPlus_transpose

theorem nativeChiralProjectorMinus_hilbert_self_adjoint :
    ContinuousLinearMap.adjoint nativeChiralProjectorMinus =
      nativeChiralProjectorMinus := by
  exact nativeContinuous_self_adjoint_of_transpose
    masterChiralProjectorMinus masterChiralProjectorMinus_transpose

def nativeSuperchargePlus : NativeSpinorCLM :=
  nativeSuperchargeQ.comp nativeChiralProjectorPlus

def nativeSuperchargeMinus : NativeSpinorCLM :=
  nativeSuperchargeQ.comp nativeChiralProjectorMinus

theorem nativeSupercharge_decomposition :
    nativeSuperchargePlus + nativeSuperchargeMinus = nativeSuperchargeQ := by
  unfold nativeSuperchargePlus nativeSuperchargeMinus
  rw [← ContinuousLinearMap.comp_add, nativeChiralProjectors_sum,
    ContinuousLinearMap.comp_id]

set_option maxHeartbeats 1000000 in
theorem nativeSuperchargePlus_sq_zero :
    nativeSuperchargePlus.comp nativeSuperchargePlus = 0 := by
  unfold nativeSuperchargePlus
  calc
    (nativeSuperchargeQ.comp nativeChiralProjectorPlus).comp
          (nativeSuperchargeQ.comp nativeChiralProjectorPlus) =
        nativeSuperchargeQ.comp
          (nativeChiralProjectorPlus.comp
            (nativeSuperchargeQ.comp nativeChiralProjectorPlus)) := by
              rw [ContinuousLinearMap.comp_assoc]
    _ = nativeSuperchargeQ.comp
          ((nativeSuperchargeQ.comp nativeChiralProjectorMinus).comp
            nativeChiralProjectorPlus) := by
              apply congrArg (ContinuousLinearMap.comp nativeSuperchargeQ)
              rw [← ContinuousLinearMap.comp_assoc,
                nativeSuperchargeQ_comp_projectorMinus]
    _ = nativeSuperchargeQ.comp
          (nativeSuperchargeQ.comp
            (nativeChiralProjectorMinus.comp nativeChiralProjectorPlus)) := by
              apply congrArg (ContinuousLinearMap.comp nativeSuperchargeQ)
              rw [ContinuousLinearMap.comp_assoc]
    _ = 0 := by
          rw [nativeChiralProjectors_orthogonal.2]
          simp only [ContinuousLinearMap.comp_zero]

set_option maxHeartbeats 1000000 in
theorem nativeSuperchargeMinus_sq_zero :
    nativeSuperchargeMinus.comp nativeSuperchargeMinus = 0 := by
  unfold nativeSuperchargeMinus
  calc
    (nativeSuperchargeQ.comp nativeChiralProjectorMinus).comp
          (nativeSuperchargeQ.comp nativeChiralProjectorMinus) =
        nativeSuperchargeQ.comp
          (nativeChiralProjectorMinus.comp
            (nativeSuperchargeQ.comp nativeChiralProjectorMinus)) := by
              rw [ContinuousLinearMap.comp_assoc]
    _ = nativeSuperchargeQ.comp
          ((nativeSuperchargeQ.comp nativeChiralProjectorPlus).comp
            nativeChiralProjectorMinus) := by
              apply congrArg (ContinuousLinearMap.comp nativeSuperchargeQ)
              rw [← ContinuousLinearMap.comp_assoc,
                nativeSuperchargeQ_comp_projectorPlus]
    _ = nativeSuperchargeQ.comp
          (nativeSuperchargeQ.comp
            (nativeChiralProjectorPlus.comp nativeChiralProjectorMinus)) := by
              apply congrArg (ContinuousLinearMap.comp nativeSuperchargeQ)
              rw [ContinuousLinearMap.comp_assoc]
    _ = 0 := by
          rw [nativeChiralProjectors_orthogonal.1]
          simp only [ContinuousLinearMap.comp_zero]

def nativeSuperchargeBarPlus : NativeSpinorCLM :=
  nativeSuperchargeQBar.comp nativeChiralProjectorPlus

def nativeSuperchargeBarMinus : NativeSpinorCLM :=
  nativeSuperchargeQBar.comp nativeChiralProjectorMinus

theorem nativeSuperchargeBar_decomposition :
    nativeSuperchargeBarPlus + nativeSuperchargeBarMinus =
      nativeSuperchargeQBar := by
  unfold nativeSuperchargeBarPlus nativeSuperchargeBarMinus
  rw [← ContinuousLinearMap.comp_add, nativeChiralProjectors_sum,
    ContinuousLinearMap.comp_id]

set_option maxHeartbeats 1000000 in
theorem nativeSuperchargeBarPlus_sq_zero :
    nativeSuperchargeBarPlus.comp nativeSuperchargeBarPlus = 0 := by
  unfold nativeSuperchargeBarPlus
  calc
    (nativeSuperchargeQBar.comp nativeChiralProjectorPlus).comp
          (nativeSuperchargeQBar.comp nativeChiralProjectorPlus) =
        nativeSuperchargeQBar.comp
          (nativeChiralProjectorPlus.comp
            (nativeSuperchargeQBar.comp nativeChiralProjectorPlus)) := by
              rw [ContinuousLinearMap.comp_assoc]
    _ = nativeSuperchargeQBar.comp
          ((nativeSuperchargeQBar.comp nativeChiralProjectorMinus).comp
            nativeChiralProjectorPlus) := by
              apply congrArg (ContinuousLinearMap.comp nativeSuperchargeQBar)
              rw [← ContinuousLinearMap.comp_assoc,
                nativeSuperchargeQBar_comp_projectorMinus]
    _ = nativeSuperchargeQBar.comp
          (nativeSuperchargeQBar.comp
            (nativeChiralProjectorMinus.comp nativeChiralProjectorPlus)) := by
              apply congrArg (ContinuousLinearMap.comp nativeSuperchargeQBar)
              rw [ContinuousLinearMap.comp_assoc]
    _ = 0 := by
          rw [nativeChiralProjectors_orthogonal.2]
          simp only [ContinuousLinearMap.comp_zero]

set_option maxHeartbeats 1000000 in
theorem nativeSuperchargeBarMinus_sq_zero :
    nativeSuperchargeBarMinus.comp nativeSuperchargeBarMinus = 0 := by
  unfold nativeSuperchargeBarMinus
  calc
    (nativeSuperchargeQBar.comp nativeChiralProjectorMinus).comp
          (nativeSuperchargeQBar.comp nativeChiralProjectorMinus) =
        nativeSuperchargeQBar.comp
          (nativeChiralProjectorMinus.comp
            (nativeSuperchargeQBar.comp nativeChiralProjectorMinus)) := by
              rw [ContinuousLinearMap.comp_assoc]
    _ = nativeSuperchargeQBar.comp
          ((nativeSuperchargeQBar.comp nativeChiralProjectorPlus).comp
            nativeChiralProjectorMinus) := by
              apply congrArg (ContinuousLinearMap.comp nativeSuperchargeQBar)
              rw [← ContinuousLinearMap.comp_assoc,
                nativeSuperchargeQBar_comp_projectorPlus]
    _ = nativeSuperchargeQBar.comp
          (nativeSuperchargeQBar.comp
            (nativeChiralProjectorPlus.comp nativeChiralProjectorMinus)) := by
              apply congrArg (ContinuousLinearMap.comp nativeSuperchargeQBar)
              rw [ContinuousLinearMap.comp_assoc]
    _ = 0 := by
          rw [nativeChiralProjectors_orthogonal.1]
          simp only [ContinuousLinearMap.comp_zero]

theorem nativeSuperchargePlus_hilbert_adjoint :
    ContinuousLinearMap.adjoint nativeSuperchargePlus =
      nativeSuperchargeBarMinus := by
  unfold nativeSuperchargePlus nativeSuperchargeBarMinus
  rw [ContinuousLinearMap.adjoint_comp,
    nativeChiralProjectorPlus_hilbert_self_adjoint,
    nativeSuperchargeQBar_is_hilbert_adjoint,
    ← nativeSuperchargeQBar_comp_projectorMinus]

theorem nativeSuperchargeMinus_hilbert_adjoint :
    ContinuousLinearMap.adjoint nativeSuperchargeMinus =
      nativeSuperchargeBarPlus := by
  unfold nativeSuperchargeMinus nativeSuperchargeBarPlus
  rw [ContinuousLinearMap.adjoint_comp,
    nativeChiralProjectorMinus_hilbert_self_adjoint,
    nativeSuperchargeQBar_is_hilbert_adjoint,
    ← nativeSuperchargeQBar_comp_projectorPlus]

theorem nativeSuperchargeBarPlus_hilbert_adjoint :
    ContinuousLinearMap.adjoint nativeSuperchargeBarPlus =
      nativeSuperchargeMinus := by
  unfold nativeSuperchargeBarPlus nativeSuperchargeMinus
  rw [ContinuousLinearMap.adjoint_comp,
    nativeChiralProjectorPlus_hilbert_self_adjoint,
    nativeSuperchargeQ_is_hilbert_adjoint,
    ← nativeSuperchargeQ_comp_projectorMinus]

theorem nativeSuperchargeBarMinus_hilbert_adjoint :
    ContinuousLinearMap.adjoint nativeSuperchargeBarMinus =
      nativeSuperchargePlus := by
  unfold nativeSuperchargeBarMinus nativeSuperchargePlus
  rw [ContinuousLinearMap.adjoint_comp,
    nativeChiralProjectorMinus_hilbert_self_adjoint,
    nativeSuperchargeQ_is_hilbert_adjoint,
    ← nativeSuperchargeQ_comp_projectorPlus]

theorem nativeHodgeDirac_comp_chiralProjectorPlus :
    nativeHodgeDirac.comp nativeChiralProjectorPlus =
      nativeChiralProjectorMinus.comp nativeHodgeDirac := by
  unfold nativeHodgeDirac nativeChiralProjectorPlus nativeChiralProjectorMinus
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous masterHodgeDirac_comp_projectorPlus

theorem nativeHodgeDirac_comp_chiralProjectorMinus :
    nativeHodgeDirac.comp nativeChiralProjectorMinus =
      nativeChiralProjectorPlus.comp nativeHodgeDirac := by
  unfold nativeHodgeDirac nativeChiralProjectorPlus nativeChiralProjectorMinus
  rw [← nativeContinuous_mul, ← nativeContinuous_mul]
  exact congrArg nativeContinuous masterHodgeDirac_comp_projectorMinus

theorem nativeChiralDiracPlus_sq_zero :
    nativeChiralDiracPlus.comp nativeChiralDiracPlus = 0 := by
  unfold nativeChiralDiracPlus
  rw [← nativeContinuous_mul, masterChiralDiracPlus_sq_zero,
    nativeContinuous_zero]

theorem nativeChiralDiracMinus_sq_zero :
    nativeChiralDiracMinus.comp nativeChiralDiracMinus = 0 := by
  unfold nativeChiralDiracMinus
  rw [← nativeContinuous_mul, masterChiralDiracMinus_sq_zero,
    nativeContinuous_zero]

theorem nativeChiralDirac_decomposition :
    nativeChiralDiracPlus + nativeChiralDiracMinus = nativeHodgeDirac := by
  unfold nativeChiralDiracPlus nativeChiralDiracMinus nativeHodgeDirac
  rw [← nativeContinuous_add, masterChiralDirac_decomposition]

def nativeHodgeLaplacian : NativeSpinorCLM :=
  nativeHodgeDirac.comp nativeHodgeDirac

theorem nativeHodgeLaplacian_commutes_inducedEvenMomentum :
    nativeHodgeLaplacian.comp nativeInducedEvenMomentum =
      nativeInducedEvenMomentum.comp nativeHodgeLaplacian := by
  unfold nativeHodgeLaplacian
  calc
    (nativeHodgeDirac.comp nativeHodgeDirac).comp nativeInducedEvenMomentum =
        nativeHodgeDirac.comp (nativeHodgeDirac.comp nativeInducedEvenMomentum) := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = nativeHodgeDirac.comp (nativeInducedEvenMomentum.comp nativeHodgeDirac) := by
          rw [nativeHodgeDirac_commutes_inducedEvenMomentum]
    _ = (nativeHodgeDirac.comp nativeInducedEvenMomentum).comp nativeHodgeDirac := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = (nativeInducedEvenMomentum.comp nativeHodgeDirac).comp nativeHodgeDirac := by
          rw [nativeHodgeDirac_commutes_inducedEvenMomentum]
    _ = nativeInducedEvenMomentum.comp (nativeHodgeDirac.comp nativeHodgeDirac) := by
          rw [ContinuousLinearMap.comp_assoc]

theorem nativeMasterHestenesPhase_commutes_hodgeLaplacian :
    nativeMasterHestenesPhase.comp nativeHodgeLaplacian =
      nativeHodgeLaplacian.comp nativeMasterHestenesPhase := by
  simpa [nativeHodgeLaplacian] using
    nativeMasterHestenesPhase_commutes_hodge_square

def nativeChiralLaplacianPlus : NativeSpinorCLM :=
  nativeChiralDiracMinus.comp nativeChiralDiracPlus

def nativeChiralLaplacianMinus : NativeSpinorCLM :=
  nativeChiralDiracPlus.comp nativeChiralDiracMinus

theorem nativeHodgeLaplacian_eq_three :
    nativeHodgeLaplacian =
      (3 : ℝ) • ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  exact nativeHodgeDirac_sq

theorem nativeChiralLaplacianPlus_eq_three_projector :
    nativeChiralLaplacianPlus = (3 : ℝ) • nativeChiralProjectorPlus := by
  unfold nativeChiralLaplacianPlus nativeChiralDiracMinus nativeChiralDiracPlus
  calc
    (nativeContinuous masterChiralDiracMinus).comp
        (nativeContinuous masterChiralDiracPlus) =
        nativeContinuous (masterChiralDiracMinus * masterChiralDiracPlus) :=
          (nativeContinuous_mul _ _).symm
    _ = nativeContinuous masterChiralLaplacianPlus := rfl
    _ = nativeContinuous ((3 : ℝ) • masterChiralProjectorPlus) :=
      congrArg nativeContinuous masterChiralLaplacianPlus_eq_three_projector
    _ = (3 : ℝ) • nativeChiralProjectorPlus := nativeContinuous_smul _ _

theorem nativeChiralLaplacianMinus_eq_three_projector :
    nativeChiralLaplacianMinus = (3 : ℝ) • nativeChiralProjectorMinus := by
  unfold nativeChiralLaplacianMinus nativeChiralDiracPlus nativeChiralDiracMinus
  calc
    (nativeContinuous masterChiralDiracPlus).comp
        (nativeContinuous masterChiralDiracMinus) =
        nativeContinuous (masterChiralDiracPlus * masterChiralDiracMinus) :=
          (nativeContinuous_mul _ _).symm
    _ = nativeContinuous masterChiralLaplacianMinus := rfl
    _ = nativeContinuous ((3 : ℝ) • masterChiralProjectorMinus) :=
      congrArg nativeContinuous masterChiralLaplacianMinus_eq_three_projector
    _ = (3 : ℝ) • nativeChiralProjectorMinus := nativeContinuous_smul _ _

theorem nativeChiralLaplacian_decomposition :
    nativeChiralLaplacianPlus + nativeChiralLaplacianMinus =
      nativeHodgeLaplacian := by
  rw [nativeChiralLaplacianPlus_eq_three_projector,
    nativeChiralLaplacianMinus_eq_three_projector]
  calc
    (3 : ℝ) • nativeChiralProjectorPlus +
        (3 : ℝ) • nativeChiralProjectorMinus =
        (3 : ℝ) • (nativeChiralProjectorPlus + nativeChiralProjectorMinus) := by
          exact (smul_add 3 nativeChiralProjectorPlus nativeChiralProjectorMinus).symm
    _ = (3 : ℝ) • ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
      rw [nativeChiralProjectors_sum]
    _ = nativeHodgeLaplacian := nativeHodgeLaplacian_eq_three.symm

/-! Native CAR transport and a finite Fredholm-style packet.  This is a
concrete Mathlib package for the already verified operators; it deliberately
stops short of the analytic hypotheses of a standard (equivariant) Kasparov
module. -/

structure NativeCAR5Profile where
  creation : Fin 5 → NativeSpinorCLM
  annihilation : Fin 5 → NativeSpinorCLM
  creation_hilbert_adjoint : ∀ i,
    ContinuousLinearMap.adjoint (creation i) = annihilation i
  annihilation_hilbert_adjoint : ∀ i,
    ContinuousLinearMap.adjoint (annihilation i) = creation i
  creation_sq : ∀ i, (creation i).comp (creation i) = 0
  annihilation_sq : ∀ i, (annihilation i).comp (annihilation i) = 0
  same_site : ∀ i,
    (creation i).comp (annihilation i) +
        (annihilation i).comp (creation i) =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier
  cross_creation : ∀ {i j}, i ≠ j →
    (creation i).comp (creation j) +
        (creation j).comp (creation i) = 0
  cross_annihilation : ∀ {i j}, i ≠ j →
    (annihilation i).comp (annihilation j) +
        (annihilation j).comp (annihilation i) = 0
  cross_creation_annihilation : ∀ {i j}, i ≠ j →
    (creation i).comp (annihilation j) +
        (annihilation j).comp (creation i) = 0
  cross_annihilation_creation : ∀ {i j}, i ≠ j →
    (annihilation i).comp (creation j) +
        (creation j).comp (annihilation i) = 0

def canonicalNativeCAR5Profile : NativeCAR5Profile where
  creation := nativeCreation
  annihilation := nativeAnnihilation
  creation_hilbert_adjoint := nativeCreation_hilbert_adjoint
  annihilation_hilbert_adjoint := nativeAnnihilation_hilbert_adjoint
  creation_sq := by
    intro i
    unfold nativeCreation
    rw [← nativeContinuous_mul, masterCreation_sq, nativeContinuous_zero]
  annihilation_sq := by
    intro i
    unfold nativeAnnihilation
    rw [← nativeContinuous_mul, masterAnnihilation_sq, nativeContinuous_zero]
  same_site := by
    intro i
    unfold nativeCreation nativeAnnihilation
    rw [← nativeContinuous_mul, ← nativeContinuous_mul,
      ← nativeContinuous_add, masterCAR_same_site, nativeContinuous_one]
  cross_creation := by
    intro i j hij
    unfold nativeCreation
    simpa only [nativeContinuous_zero, nativeContinuous_add, nativeContinuous_mul] using
      congrArg nativeContinuous (masterCAR_cross_site hij).1
  cross_annihilation := by
    intro i j hij
    unfold nativeAnnihilation
    simpa only [nativeContinuous_zero, nativeContinuous_add, nativeContinuous_mul] using
      congrArg nativeContinuous (masterCAR_cross_site hij).2.1
  cross_creation_annihilation := by
    intro i j hij
    unfold nativeCreation nativeAnnihilation
    simpa only [nativeContinuous_zero, nativeContinuous_add, nativeContinuous_mul] using
      congrArg nativeContinuous (masterCAR_cross_site hij).2.2
  cross_annihilation_creation := by
    intro i j hij
    unfold nativeAnnihilation nativeCreation
    simpa only [nativeContinuous_zero, nativeContinuous_add, nativeContinuous_mul,
      masterCreation, masterAnnihilation] using
      congrArg nativeContinuous
        (InfoGeometry.Canonical.Cl55WittCAR.annihilation_creation_cross_anticommute hij)

structure NativeFiniteFredholmDatum where
  clifford : NativeCAR5Profile
  gamma : NativeSpinorCLM
  gamma_sq : gamma.comp gamma = ContinuousLinearMap.id ℝ NativeSpinorCarrier
  gamma_hilbert_self_adjoint :
    ContinuousLinearMap.adjoint gamma = gamma
  F : NativeSpinorCLM
  F_hilbert_self_adjoint :
    ContinuousLinearMap.adjoint F = F
  F_odd : gamma.comp F + F.comp gamma = 0
  F_defect :
    F.comp F - ContinuousLinearMap.id ℝ NativeSpinorCarrier =
      (-1 / 4 : ℝ) • ContinuousLinearMap.id ℝ NativeSpinorCarrier
  F_compact : IsCompactOperator F
  F_krein_skew : nativeKreinAdjoint F = -F

def canonicalNativeFiniteFredholmDatum : NativeFiniteFredholmDatum where
  clifford := canonicalNativeCAR5Profile
  gamma := nativeChirality
  gamma_sq := nativeChirality_sq
  gamma_hilbert_self_adjoint := nativeChirality_hilbert_self_adjoint
  F := nativeNormalizedDirac
  F_hilbert_self_adjoint := nativeNormalizedDirac_hilbert_self_adjoint
  F_odd := nativeNormalizedDirac_anticomm_chirality
  F_defect := nativeNormalizedDirac_defect_scalar
  F_compact := nativeNormalizedDirac_is_compact_operator
  F_krein_skew := nativeNormalizedDirac_krein_skew_adjoint

theorem canonicalNativeFiniteFredholmDatum_F_defect :
    canonicalNativeFiniteFredholmDatum.F.comp
        canonicalNativeFiniteFredholmDatum.F -
        ContinuousLinearMap.id ℝ NativeSpinorCarrier =
      (-1 / 4 : ℝ) • ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  exact canonicalNativeFiniteFredholmDatum.F_defect

/-! Infinitesimal equivariance package.  The action is a Lie-algebra action
on the finite native carrier; no locally compact group or integrated
equivariant Kasparov class is asserted. -/

structure NativeG2EquivariantFiniteFredholmDatum where
  base : NativeFiniteFredholmDatum
  action : g2SpinorLieSubalgebra →ₗ⁅ℝ⁆ NativeSpinorCLM
  action_commutes_gamma : ∀ A,
    (action A).comp base.gamma = base.gamma.comp (action A)
  action_commutes_hodge : ∀ A,
    (action A).comp nativeHodgeDirac =
      nativeHodgeDirac.comp (action A)
  action_commutes_F : ∀ A,
    (action A).comp base.F = base.F.comp (action A)

def canonicalNativeG2EquivariantFiniteFredholmDatum :
    NativeG2EquivariantFiniteFredholmDatum where
  base := canonicalNativeFiniteFredholmDatum
  action := nativeG2LieHom
  action_commutes_gamma := by
    intro A
    simpa using nativeG2LieHom_commutes_chirality A
  action_commutes_hodge := nativeG2LieHom_commutes_hodge
  action_commutes_F := by
    intro A
    simpa using nativeG2LieHom_commutes_normalizedDirac A

end InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
