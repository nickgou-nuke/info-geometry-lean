import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import DAG.MatrixRepresentation
import InfoGeometry.MassSpectrometry.PeakFragmentMatching
import InfoGeometry.MassSpectrometry.CausalCrossGramian
import InfoGeometry.MassSpectrometry.DirectedOperatorDoubling
import InfoGeometry.Quantum.MajoranaPfaffianBridge
import InfoGeometry.Quantum.FiniteMajoranaPairingBlocks
import InfoGeometry.Quantum.FiniteMajoranaPerfectMatching
import InfoGeometry.Clifford.HestenesDirac
import InfoGeometry.Canonical.KitaevChainMajoranaZeroModes

/-!
# Chiral discrete graph / Majorana-Pfaffian bridge

The repository's DAG owner uses the algebraic pattern `A = ΓD`: a chiral-even
Dirac carrier `D` anticommutes with `Γ`, so `ΓD` is skew and supports Pfaffian
readouts. This module applies the same construction to the mass-spectrometry
doubled directed operator.

The bridge is structural. It does not identify molecular fragments with
physical Majorana particles. In the single-channel case, however, the matrix
entries reduce exactly to the canonical `2 × 2` Majorana pairing block already
owned by `FiniteMajoranaPairingBlocks`.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open Matrix

/-- Skew chiral shadow of the directed doubled transfer, `A_K = Γ D_K`. -/
def directedMajoranaOperator {n : ℕ} (K : AssignmentMatrix n) :
    Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  gradingMatrix n * doubledOperator K

/-- The mass-spectrometry Majorana shadow is exactly the left grading action. -/
theorem directedMajoranaOperator_eq_gradeLeft {n : ℕ} (K : AssignmentMatrix n) :
    directedMajoranaOperator K = gradeLeft (doubledOperator K) := by
  exact gradingMatrix_mul_eq_gradeLeft (doubledOperator K)

/-- `ΓD_K` is skew-symmetric. This is the same algebraic mechanism as the
finite graph Majorana owner. -/
theorem directedMajoranaOperator_transpose_eq_neg
    {n : ℕ} (K : AssignmentMatrix n) :
    (directedMajoranaOperator K).transpose = -directedMajoranaOperator K := by
  ext i j
  cases i <;> cases j <;>
    simp [directedMajoranaOperator, gradingMatrix, Matrix.diagonal_mul,
      doubledOperator, doubledSign]

/-- Cross-Gramian source followed by the chiral skew conversion. -/
def crossGramMajoranaOperator {n d : ℕ}
    (Z₁ Z₂ : Matrix (Fin n) (Fin d) ℝ) :
    Matrix (DoubledIndex n) (DoubledIndex n) ℝ :=
  directedMajoranaOperator (crossGramOperator Z₁ Z₂)

/-- Every square causal cross-Gramian has a skew chiral Majorana shadow. -/
theorem crossGramMajoranaOperator_transpose_eq_neg
    {n d : ℕ} (Z₁ Z₂ : Matrix (Fin n) (Fin d) ℝ) :
    (crossGramMajoranaOperator Z₁ Z₂).transpose =
      -crossGramMajoranaOperator Z₁ Z₂ := by
  exact directedMajoranaOperator_transpose_eq_neg (crossGramOperator Z₁ Z₂)

/-! ## Re-export of the discrete graph foundation -/

/-- The existing DAG Majorana matrix is skew-symmetric in matrix form. -/
theorem dagMajoranaOperator_transpose_eq_neg
    {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℚ)
    (B2 : Matrix (Fin n1) (Fin n2) ℚ) :
    (DAG.MatrixRepresentation.majoranaOp B1 B2).transpose =
      -DAG.MatrixRepresentation.majoranaOp B1 B2 := by
  ext i j
  simpa [Matrix.transpose_apply] using
    DAG.MatrixRepresentation.majorana_skew_symmetric B1 B2 j i

/-- The existing discrete graph Dirac carrier anticommutes with chirality. -/
theorem dagDirac_anticommutes_chirality
    {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℚ)
    (B2 : Matrix (Fin n1) (Fin n2) ℚ) :
    DAG.MatrixRepresentation.chiralGamma (n0 := n0) (n1 := n1) (n2 := n2) *
        DAG.MatrixRepresentation.diracOp B1 B2 +
      DAG.MatrixRepresentation.diracOp B1 B2 *
        DAG.MatrixRepresentation.chiralGamma (n0 := n0) (n1 := n1) (n2 := n2) = 0 := by
  exact DAG.MatrixRepresentation.chiral_anticommutation B1 B2

/-! ## Exact single-channel Majorana pairing readout -/

/-- One scalar directed channel. -/
def singleDirectedKernel (a : ℝ) : AssignmentMatrix 1 :=
  fun _ _ => a

@[simp] theorem directedMajorana_single_ll (a : ℝ) :
    directedMajoranaOperator (singleDirectedKernel a)
      (Sum.inl (0 : Fin 1)) (Sum.inl (0 : Fin 1)) = 0 := by
  simp [directedMajoranaOperator, gradingMatrix, Matrix.diagonal_mul,
    doubledOperator, doubledSign, singleDirectedKernel]

@[simp] theorem directedMajorana_single_lr (a : ℝ) :
    directedMajoranaOperator (singleDirectedKernel a)
      (Sum.inl (0 : Fin 1)) (Sum.inr (0 : Fin 1)) = a := by
  simp [directedMajoranaOperator, gradingMatrix, Matrix.diagonal_mul,
    doubledOperator, doubledSign, singleDirectedKernel]

@[simp] theorem directedMajorana_single_rl (a : ℝ) :
    directedMajoranaOperator (singleDirectedKernel a)
      (Sum.inr (0 : Fin 1)) (Sum.inl (0 : Fin 1)) = -a := by
  simp [directedMajoranaOperator, gradingMatrix, Matrix.diagonal_mul,
    doubledOperator, doubledSign, singleDirectedKernel]

@[simp] theorem directedMajorana_single_rr (a : ℝ) :
    directedMajoranaOperator (singleDirectedKernel a)
      (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1)) = 0 := by
  simp [directedMajoranaOperator, gradingMatrix, Matrix.diagonal_mul,
    doubledOperator, doubledSign, singleDirectedKernel]

/-- Canonical `Fin 2` coordinate readout of the one-channel chiral skew block. -/
def twoModeMajoranaReadout (a : ℝ) :
    InfoGeometry.Quantum.MajoranaPfaffianBridge.M2R :=
  InfoGeometry.Quantum.FiniteMajoranaPairingBlocks.pairingBlock a

/-- The four entries of the canonical two-mode readout agree with the four
entries of `ΓD_K` for a one-channel transfer. -/
theorem twoModeMajoranaReadout_matches_directed_entries (a : ℝ) :
    twoModeMajoranaReadout a 0 0 =
        directedMajoranaOperator (singleDirectedKernel a)
          (Sum.inl (0 : Fin 1)) (Sum.inl (0 : Fin 1)) ∧
    twoModeMajoranaReadout a 0 1 =
        directedMajoranaOperator (singleDirectedKernel a)
          (Sum.inl (0 : Fin 1)) (Sum.inr (0 : Fin 1)) ∧
    twoModeMajoranaReadout a 1 0 =
        directedMajoranaOperator (singleDirectedKernel a)
          (Sum.inr (0 : Fin 1)) (Sum.inl (0 : Fin 1)) ∧
    twoModeMajoranaReadout a 1 1 =
        directedMajoranaOperator (singleDirectedKernel a)
          (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1)) := by
  simp [twoModeMajoranaReadout,
    InfoGeometry.Quantum.FiniteMajoranaPairingBlocks.pairingBlock]

/-- The two-mode Pfaffian is exactly the directed scalar coupling. -/
theorem twoModeMajoranaReadout_pfaffian (a : ℝ) :
    InfoGeometry.Quantum.MajoranaPfaffianBridge.pfaffian2
      (twoModeMajoranaReadout a) = a := by
  rfl

/-- The determinant is the square of the directed coupling. -/
theorem twoModeMajoranaReadout_det (a : ℝ) :
    (twoModeMajoranaReadout a).det = a ^ 2 := by
  exact InfoGeometry.Quantum.FiniteMajoranaPairingBlocks.pairingBlock_det a

/-- The singular locus of the one-channel chiral block is exactly zero coupling. -/
theorem twoModeMajoranaReadout_det_zero_iff (a : ℝ) :
    (twoModeMajoranaReadout a).det = 0 ↔ a = 0 := by
  rw [twoModeMajoranaReadout_det]
  constructor
  · intro h
    nlinarith
  · intro h
    simp [h]

/-- Equivalently, determinant zero and Pfaffian zero define the same two-mode
singular locus. -/
theorem twoModeMajoranaReadout_det_zero_iff_pfaffian_zero (a : ℝ) :
    (twoModeMajoranaReadout a).det = 0 ↔
      InfoGeometry.Quantum.MajoranaPfaffianBridge.pfaffian2
        (twoModeMajoranaReadout a) = 0 := by
  rw [twoModeMajoranaReadout_det_zero_iff, twoModeMajoranaReadout_pfaffian]

/-! ## Existing finite matching and four-mode zero-mode owners -/

/-- Canonical finite Majorana matching retains the determinant-square invariant. -/
theorem finiteMajoranaMatching_weight_squared_eq_determinant
    {N : ℕ} (a : Fin N → ℝ) :
    (InfoGeometry.Quantum.FiniteMajoranaPerfectMatching.matchingWeight a) ^ 2 =
      InfoGeometry.Quantum.FiniteMajoranaPairingBlocks.finitePairingDeterminant a := by
  exact
    InfoGeometry.Quantum.FiniteMajoranaPerfectMatching.canonicalMatching_weight_squared_eq_blockDeterminant
      a

/-- Existing real `4 × 4` Majorana/BdG owner: determinant-zero is exactly
Pfaffian-zero. -/
theorem hestenesMajorana_zero_mode_iff_pfaffian_zero
    (a : InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates) :
    InfoGeometry.Clifford.HestenesDirac.determinantSkew4
        (InfoGeometry.Clifford.HestenesDirac.concreteMajoranaBdGMatrix a) = 0 ↔
      InfoGeometry.Clifford.HestenesDirac.RealMatrix4.pfaffianSkew4
        (InfoGeometry.Clifford.HestenesDirac.concreteMajoranaBdGMatrix a) = 0 := by
  exact InfoGeometry.Clifford.HestenesDirac.concreteMajoranaBdG_zero_mode_iff_pfaffian_zero a

/-- Existing algebraic Majorana-basis predicate from the Kitaev-chain owner. -/
abbrev IsMajoranaBasis {R : Type*} [Ring R] (N : ℕ)
    (gamma : Fin (2 * N) → R) : Prop :=
  InfoGeometry.Canonical.KitaevChainMajoranaZeroModes.IsMajoranaBasis N gamma

end InfoGeometry.MassSpectrometry
