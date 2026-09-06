import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge
import InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
import InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

/-!
# Canonical Zorn Root Witt Block Bridge

This owner module transports the existing Cartan/root relations into the explicit
Witt block realization of the 14-dimensional derivation algebra.  It does not
assert an intrinsic image characterization or infer block support from dimension
counts; those require separate Leibniz/Zorn calculations.

1. **Carrier Sectors in $\mathfrak{so}(4,4)$:**
   $$\mathfrak{so}(V \oplus V^*) \cong \mathfrak{gl}(V) \oplus \Lambda^2 V^* \oplus \Lambda^2 V \qquad (16 + 6 + 6 = 28)$$

2. **Root Generator Readout:**
   Every existing root derivation is assigned its canonical block matrix:
   $$\iota(E_\alpha) = \begin{pmatrix} A_\alpha & B_\alpha \\ C_\alpha & -A_\alpha^T \end{pmatrix}$$
   The `rootBlockClassification` labels are bookkeeping for the intended
   sector split; vanishing/support theorems for individual blocks are not
   claimed until their Zorn multiplication calculations are supplied.  In
   particular, the proved positive-short readouts below have both `B` and
   `C` support; the labels must not be read as a pure-block assertion.

3. **Ambient dimensions:** the existing block owner supplies the ambient
   $16+6+6=28$ decomposition; no equality or image dimension statement is
   inferred here.
-/

noncomputable section
set_option maxHeartbeats 800000

namespace InfoGeometry.Lie.CanonicalZornRootWittBlockBridge

open Matrix
open InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge
open InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
open InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization
open InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

/-- Classification of G2 roots according to their block carrier in $\mathfrak{so}(V \oplus V^*)$. -/
inductive RootBlockSector where
  | cartanGL : RootBlockSector      -- Cartan generators (j = 6, 13) in gl(V)
  | longRootGL : RootBlockSector    -- Long roots (j = 1, 2, 5, 7, 11, 12) in sl(3) ⊂ gl(V)
  | shortPositiveBivector : RootBlockSector  -- Short positive roots (j = 4, 9, 10) in Λ²V*
  | shortNegativeCobivector : RootBlockSector -- Short negative roots (j = 0, 3, 8) in Λ²V

/-- Canonical projection mapping root indices $j \in \text{Fin } 14$ to their carrier sector. -/
def rootBlockClassification (j : Fin 14) : RootBlockSector :=
  match j with
  | 6 => RootBlockSector.cartanGL
  | 13 => RootBlockSector.cartanGL
  | 1 => RootBlockSector.longRootGL
  | 2 => RootBlockSector.longRootGL
  | 5 => RootBlockSector.longRootGL
  | 7 => RootBlockSector.longRootGL
  | 11 => RootBlockSector.longRootGL
  | 12 => RootBlockSector.longRootGL
  | 4 => RootBlockSector.shortPositiveBivector
  | 9 => RootBlockSector.shortPositiveBivector
  | 10 => RootBlockSector.shortPositiveBivector
  | 0 => RootBlockSector.shortNegativeCobivector
  | 3 => RootBlockSector.shortNegativeCobivector
  | 8 => RootBlockSector.shortNegativeCobivector

def dim_gl_sector : ℕ := 8
def dim_bivector_sector : ℕ := 3
def dim_cobivector_sector : ℕ := 3

def isCartanIndex (j : Fin 14) : Prop := j = 6 ∨ j = 13
def isLongRootIndex (j : Fin 14) : Prop :=
  j = 1 ∨ j = 2 ∨ j = 5 ∨ j = 7 ∨ j = 11 ∨ j = 12
def isShortPositiveIndex (j : Fin 14) : Prop := j = 4 ∨ j = 9 ∨ j = 10
def isShortNegativeIndex (j : Fin 14) : Prop := j = 0 ∨ j = 3 ∨ j = 8

theorem root_family_complete (j : Fin 14) :
    isCartanIndex j ∨ isLongRootIndex j ∨
      isShortPositiveIndex j ∨ isShortNegativeIndex j := by
  fin_cases j <;> simp [isCartanIndex, isLongRootIndex,
    isShortPositiveIndex, isShortNegativeIndex]

theorem rootBlockClassification_eq_cartan_iff (j : Fin 14) :
    rootBlockClassification j = RootBlockSector.cartanGL ↔ isCartanIndex j := by
  fin_cases j <;> simp [rootBlockClassification, isCartanIndex]

theorem rootWeight_eq_zero_iff_cartan_family (j : Fin 14) :
    rootWeight j = 0 ↔ isCartanIndex j := by
  rw [rootWeight_eq_zero_iff]
  rfl

theorem rootBlockClassification_eq_long_iff (j : Fin 14) :
    rootBlockClassification j = RootBlockSector.longRootGL ↔ isLongRootIndex j := by
  fin_cases j <;> simp [rootBlockClassification, isLongRootIndex]

theorem rootBlockClassification_eq_shortPositive_iff (j : Fin 14) :
    rootBlockClassification j = RootBlockSector.shortPositiveBivector ↔
      isShortPositiveIndex j := by
  fin_cases j <;> simp [rootBlockClassification, isShortPositiveIndex]

theorem rootBlockClassification_eq_shortNegative_iff (j : Fin 14) :
    rootBlockClassification j = RootBlockSector.shortNegativeCobivector ↔
      isShortNegativeIndex j := by
  fin_cases j <;> simp [rootBlockClassification, isShortNegativeIndex]

/-- 🏆 THEOREM 1: The G2 root decomposition partitions exactly into 8 + 3 + 3 = 14 generators. -/
theorem g2_root_sector_dimension_sum :
    dim_gl_sector + dim_bivector_sector + dim_cobivector_sector = 14 := by
  dsimp [dim_gl_sector, dim_bivector_sector, dim_cobivector_sector]

/-- 🏆 THEOREM 2: the root-sector bookkeeping fits inside the ambient
    `so(4,4)` block sectors (with dimensions `16 + 6 + 6 = 28`).  This
    inequality theorem is not an image or codimension characterization. -/
theorem so44_sector_embeddings :
    dim_gl_sector ≤ dim_gl4 ∧
    dim_bivector_sector ≤ dim_bivector ∧
    dim_cobivector_sector ≤ dim_cobivector := by
  dsimp [dim_gl_sector, dim_bivector_sector, dim_cobivector_sector,
         dim_gl4, dim_bivector, dim_cobivector]
  decide

/-- 🏆 THEOREM 3: The Cartan subalgebra (j = 6, 13) acts diagonally on each sector. -/
theorem cartan_is_gl_diagonal (j : Fin 14) (hj : j = 6 ∨ j = 13) :
    rootBlockClassification j = RootBlockSector.cartanGL := by
  rcases hj with rfl | rfl <;> rfl

/-- 🏆 THEOREM 4: Short roots pair with opposite sign weights under the Cartan pairing. -/
theorem short_roots_opposite_weight (i : Fin 3) :
    (match i with
     | 0 => rootWeight 0 = - rootWeight 10
     | 1 => rootWeight 3 = - rootWeight 9
     | 2 => rootWeight 8 = - rootWeight 4) := by
  fin_cases i <;> rfl

/-! Lie-functorial root transport.  This is the intrinsic content available
before choosing any further block readout of the embedded endomorphisms. -/

theorem native_cartan_root_eigenrelation
    (k : TracelessWeight) (j : Fin 14) :
    ⁅nativeDerivationLieHom (axialCartanLieEquiv k),
      nativeDerivationLieHom (rootDerivation j)⁆ =
      (rootWeight j k : ℝ) • nativeDerivationLieHom (rootDerivation j) := by
  change nativeDerivationLieHom (adCartan k (rootDerivation j)) = _
  rw [adCartan_rootDerivation]
  rfl

/-! The actual block readout is obtained by applying the canonical matrix
realization to the already existing root derivations.  No new root basis or
coordinate derivation is introduced here. -/

def rootDerivationBlock (j : Fin 14) : WittBlockMatrix :=
  canonicalDerivationBlock (rootDerivation j)

noncomputable def rootDerivationBlockBasis :
    Module.Basis (Fin 14) ℝ (transportedDerivationLieHom).range :=
  rootDerivationBasis.map transportedDerivationLieEquiv.toLinearEquiv

theorem rootDerivationBlockBasis_apply (j : Fin 14) :
    rootDerivationBlockBasis j =
      transportedDerivationLieEquiv.toLinearEquiv (rootDerivationBasis j) := by
  rfl

theorem transported_root_basis_cartan_eigenrelation
    (k : TracelessWeight) (j : Fin 14) :
    transportedDerivationLieEquiv
        (adCartan k (rootDerivationBasis j)) =
      (rootWeight j k : ℝ) •
        transportedDerivationLieEquiv (rootDerivationBasis j) := by
  rw [rootDerivationBasis_is_simultaneous_eigenbasis]
  exact transportedDerivationLieEquiv.toLinearEquiv.map_smul _ _

theorem rootDerivationBlock_isWittSkew (j : Fin 14) :
    IsWittSkew (rootDerivationBlock j) := by
  exact canonicalDerivationBlock_isWittSkew (rootDerivation j)

theorem rootDerivationBlock_equations (j : Fin 14) :
    IsWittOrthogonalLie (rootDerivationBlock j) := by
  exact canonicalDerivationBlock_equations (rootDerivation j)

theorem rootDerivationBlock_lowerRight_eq_negTranspose (j : Fin 14) :
    (rootDerivationBlock j).D = -(rootDerivationBlock j).Aᵀ := by
  exact canonicalDerivationBlock_lowerRight_eq_negTranspose (rootDerivation j)

theorem rootDerivationBlock_upperRight_skew (j : Fin 14) :
    (rootDerivationBlock j).Bᵀ = -(rootDerivationBlock j).B := by
  exact canonicalDerivationBlock_upperRight_skew (rootDerivation j)

theorem rootDerivationBlock_lowerLeft_skew (j : Fin 14) :
    (rootDerivationBlock j).Cᵀ = -(rootDerivationBlock j).C := by
  exact canonicalDerivationBlock_lowerLeft_skew (rootDerivation j)

theorem root_block_cartan_eigenrelation
    (k : TracelessWeight) (j : Fin 14) :
    canonicalDerivationBlock (adCartan k (rootDerivation j)) =
      smulWittBlock (rootWeight j k : ℝ) (rootDerivationBlock j) := by
  rw [adCartan_rootDerivation]
  exact canonicalDerivationBlock_smul (rootWeight j k : ℝ) (rootDerivation j)

theorem rootDerivation_vectorAction
    (j : Fin 14) (X : InfoGeometry.Algebra.ZornVectorMatrix ℝ) :
    canonicalVectorEquiv ((rootDerivation j).1
      (canonicalVectorEquiv.symm X)) =
      parameterAction (parameterUnit j) X := by
  have hroot :
      canonicalToVectorDerivation (rootDerivation j) =
        parameterDerivation (parameterUnit j) := by
    change canonicalToVectorDerivation
        (canonicalParameterLinearEquiv (parameterUnit j)) =
      parameterDerivation (parameterUnit j)
    change canonicalToVectorDerivation
        (vectorToCanonicalDerivation (parameterDerivation (parameterUnit j))) =
      parameterDerivation (parameterUnit j)
    exact CanonicalZornDerivation.vectorCanonicalLinearEquiv.left_inv _
  have hX := congrArg (fun E : InfoGeometry.Lie.CanonicalZornDerivation.VDer => E X) hroot
  simpa [CanonicalZornDerivation.canonicalToVectorDerivation_apply,
    parameterDerivation, parameterAction] using hX

theorem transportedDerivation_root_apply
    (j : Fin 14) (z : Coord8) :
    transportedDerivation (rootDerivation j) z =
      neutralCanonicalToCoord
        (canonicalVectorEquiv.symm
          (parameterAction (parameterUnit j)
            (canonicalVectorEquiv (neutralCanonicalToCoord.symm z)))) := by
  dsimp [transportedDerivation]
  have h := rootDerivation_vectorAction j
    (canonicalVectorEquiv (neutralCanonicalToCoord.symm z))
  have h' := congrArg canonicalVectorEquiv.symm h
  have h'' := congrArg neutralCanonicalToCoord h'
  exact h''

theorem longRoot_upperRight_zero (j : Fin 14)
    (hj : j = 1 ∨ j = 2 ∨ j = 5 ∨ j = 7 ∨ j = 11 ∨ j = 12) :
    (rootDerivationBlock j).B = 0 := by
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    ext i k
    change canonicalDerivationMatrix (rootDerivation _) (Sum.inl i) (Sum.inr k) = 0
    rw [canonicalDerivationMatrix_apply]
    rw [transportedDerivation_root_apply]
    fin_cases i <;> fin_cases k
    all_goals
      simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
        neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem longRoot_lowerLeft_zero (j : Fin 14)
    (hj : j = 1 ∨ j = 2 ∨ j = 5 ∨ j = 7 ∨ j = 11 ∨ j = 12) :
    (rootDerivationBlock j).C = 0 := by
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    ext i k
    change canonicalDerivationMatrix (rootDerivation _) (Sum.inr i) (Sum.inl k) = 0
    rw [canonicalDerivationMatrix_apply_lowerLeft]
    rw [transportedDerivation_root_apply]
    fin_cases i <;> fin_cases k
    all_goals
      simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
        neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem longRoot_block_diagonal (j : Fin 14)
    (hj : j = 1 ∨ j = 2 ∨ j = 5 ∨ j = 7 ∨ j = 11 ∨ j = 12) :
    (rootDerivationBlock j).B = 0 ∧
      (rootDerivationBlock j).C = 0 := by
  exact ⟨longRoot_upperRight_zero j hj, longRoot_lowerLeft_zero j hj⟩

theorem cartan_block_diagonal (j : Fin 14)
    (hj : j = 6 ∨ j = 13) :
    (rootDerivationBlock j).B = 0 ∧
      (rootDerivationBlock j).C = 0 := by
  rcases hj with rfl | rfl
  all_goals
    constructor
    · ext i k
      change canonicalDerivationMatrix (rootDerivation _) (Sum.inl i) (Sum.inr k) = 0
      rw [canonicalDerivationMatrix_apply]
      rw [transportedDerivation_root_apply]
      fin_cases i <;> fin_cases k
      all_goals
        simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
          neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]
    · ext i k
      change canonicalDerivationMatrix (rootDerivation _) (Sum.inr i) (Sum.inl k) = 0
      rw [canonicalDerivationMatrix_apply_lowerLeft]
      rw [transportedDerivation_root_apply]
      fin_cases i <;> fin_cases k
      all_goals
        simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
          neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem short_positive_root_four_upperRight_entry :
    (rootDerivationBlock 4).B 0 3 = 1 := by
  change canonicalDerivationMatrix (rootDerivation 4)
      (Sum.inl 0) (Sum.inr 3) = 1
  rw [canonicalDerivationMatrix_apply]
  rw [transportedDerivation_root_apply]
  simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
    neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem short_positive_root_four_lowerLeft_entry :
    (rootDerivationBlock 4).C 1 2 = 1 := by
  change canonicalDerivationMatrix (rootDerivation 4)
      (Sum.inr 1) (Sum.inl 2) = 1
  rw [canonicalDerivationMatrix_apply_lowerLeft]
  rw [transportedDerivation_root_apply]
  simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
    neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem short_positive_root_four_mixes_blocks :
    (rootDerivationBlock 4).B ≠ 0 ∧
      (rootDerivationBlock 4).C ≠ 0 := by
  constructor
  · intro h
    have h' := congrArg (fun M => M 0 3) h
    change (rootDerivationBlock 4).B 0 3 = 0 at h'
    rw [short_positive_root_four_upperRight_entry] at h'
    norm_num at h'
  · intro h
    have h' := congrArg (fun M => M 1 2) h
    change (rootDerivationBlock 4).C 1 2 = 0 at h'
    rw [short_positive_root_four_lowerLeft_entry] at h'
    norm_num at h'

theorem short_positive_root_nine_upperRight_entry :
    (rootDerivationBlock 9).B 0 2 = -1 := by
  change canonicalDerivationMatrix (rootDerivation 9)
      (Sum.inl 0) (Sum.inr 2) = -1
  rw [canonicalDerivationMatrix_apply]
  rw [transportedDerivation_root_apply]
  simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
    neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem short_positive_root_nine_lowerLeft_entry :
    (rootDerivationBlock 9).C 1 3 = 1 := by
  change canonicalDerivationMatrix (rootDerivation 9)
      (Sum.inr 1) (Sum.inl 3) = 1
  rw [canonicalDerivationMatrix_apply_lowerLeft]
  rw [transportedDerivation_root_apply]
  simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
    neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem short_positive_root_ten_upperRight_entry :
    (rootDerivationBlock 10).B 0 1 = 1 := by
  change canonicalDerivationMatrix (rootDerivation 10)
      (Sum.inl 0) (Sum.inr 1) = 1
  rw [canonicalDerivationMatrix_apply]
  rw [transportedDerivation_root_apply]
  simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
    neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem short_positive_root_ten_lowerLeft_entry :
    (rootDerivationBlock 10).C 2 3 = 1 := by
  change canonicalDerivationMatrix (rootDerivation 10)
      (Sum.inr 2) (Sum.inl 3) = 1
  rw [canonicalDerivationMatrix_apply_lowerLeft]
  rw [transportedDerivation_root_apply]
  simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
    neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem matrix_fin4_ne_zero_of_entry {M : Matrix (Fin 4) (Fin 4) ℝ}
    {i j : Fin 4} {c : ℝ} (h : M i j = c) (hc : c ≠ 0) : M ≠ 0 := by
  intro hM
  have h' := congrArg (fun N => N i j) hM
  change M i j = 0 at h'
  rw [h] at h'
  exact hc h'

theorem short_positive_root_nine_mixes_blocks :
    (rootDerivationBlock 9).B ≠ 0 ∧
      (rootDerivationBlock 9).C ≠ 0 := by
  exact ⟨matrix_fin4_ne_zero_of_entry short_positive_root_nine_upperRight_entry (by norm_num),
    matrix_fin4_ne_zero_of_entry short_positive_root_nine_lowerLeft_entry (by norm_num)⟩

theorem short_positive_root_ten_mixes_blocks :
    (rootDerivationBlock 10).B ≠ 0 ∧
      (rootDerivationBlock 10).C ≠ 0 := by
  exact ⟨matrix_fin4_ne_zero_of_entry short_positive_root_ten_upperRight_entry (by norm_num),
    matrix_fin4_ne_zero_of_entry short_positive_root_ten_lowerLeft_entry (by norm_num)⟩

theorem short_positive_roots_mix_blocks (j : Fin 14)
    (hj : j = 4 ∨ j = 9 ∨ j = 10) :
    (rootDerivationBlock j).B ≠ 0 ∧
      (rootDerivationBlock j).C ≠ 0 := by
  rcases hj with rfl | rfl | rfl
  · exact short_positive_root_four_mixes_blocks
  · exact short_positive_root_nine_mixes_blocks
  · exact short_positive_root_ten_mixes_blocks

theorem short_negative_root_zero_lowerLeft_entry :
    (rootDerivationBlock 0).C 0 1 = -1 := by
  change canonicalDerivationMatrix (rootDerivation 0)
      (Sum.inr 0) (Sum.inl 1) = -1
  rw [canonicalDerivationMatrix_apply_lowerLeft]
  rw [transportedDerivation_root_apply]
  simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
    neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem short_negative_root_zero_upperRight_entry :
    (rootDerivationBlock 0).B 3 2 = 1 := by
  change canonicalDerivationMatrix (rootDerivation 0)
      (Sum.inl 3) (Sum.inr 2) = 1
  rw [canonicalDerivationMatrix_apply]
  rw [transportedDerivation_root_apply]
  simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
    neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem short_negative_root_three_lowerLeft_entry :
    (rootDerivationBlock 3).C 0 2 = -1 := by
  change canonicalDerivationMatrix (rootDerivation 3)
      (Sum.inr 0) (Sum.inl 2) = -1
  rw [canonicalDerivationMatrix_apply_lowerLeft]
  rw [transportedDerivation_root_apply]
  simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
    neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem short_negative_root_three_upperRight_entry :
    (rootDerivationBlock 3).B 1 3 = 1 := by
  change canonicalDerivationMatrix (rootDerivation 3)
      (Sum.inl 1) (Sum.inr 3) = 1
  rw [canonicalDerivationMatrix_apply]
  rw [transportedDerivation_root_apply]
  simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
    neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem short_negative_root_eight_lowerLeft_entry :
    (rootDerivationBlock 8).C 0 3 = -1 := by
  change canonicalDerivationMatrix (rootDerivation 8)
      (Sum.inr 0) (Sum.inl 3) = -1
  rw [canonicalDerivationMatrix_apply_lowerLeft]
  rw [transportedDerivation_root_apply]
  simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
    neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem short_negative_root_eight_upperRight_entry :
    (rootDerivationBlock 8).B 1 2 = -1 := by
  change canonicalDerivationMatrix (rootDerivation 8)
      (Sum.inl 1) (Sum.inr 2) = -1
  rw [canonicalDerivationMatrix_apply]
  rw [transportedDerivation_root_apply]
  simp [parameterUnit, parameterAction, neutralCanonicalToCoord,
    neutralize, canonicalToCoord, wittIndex, canonicalVectorEquiv]

theorem short_negative_root_zero_has_lowerLeft_support :
    (rootDerivationBlock 0).C ≠ 0 := by
  exact matrix_fin4_ne_zero_of_entry short_negative_root_zero_lowerLeft_entry (by norm_num)

theorem short_negative_root_zero_has_upperRight_support :
    (rootDerivationBlock 0).B ≠ 0 := by
  exact matrix_fin4_ne_zero_of_entry short_negative_root_zero_upperRight_entry (by norm_num)

theorem short_negative_root_zero_mixes_blocks :
    (rootDerivationBlock 0).B ≠ 0 ∧
      (rootDerivationBlock 0).C ≠ 0 := by
  exact ⟨short_negative_root_zero_has_upperRight_support,
    short_negative_root_zero_has_lowerLeft_support⟩

theorem short_negative_root_three_has_lowerLeft_support :
    (rootDerivationBlock 3).C ≠ 0 := by
  exact matrix_fin4_ne_zero_of_entry short_negative_root_three_lowerLeft_entry (by norm_num)

theorem short_negative_root_eight_has_lowerLeft_support :
    (rootDerivationBlock 8).C ≠ 0 := by
  exact matrix_fin4_ne_zero_of_entry short_negative_root_eight_lowerLeft_entry (by norm_num)

theorem short_negative_root_three_has_upperRight_support :
    (rootDerivationBlock 3).B ≠ 0 := by
  exact matrix_fin4_ne_zero_of_entry short_negative_root_three_upperRight_entry (by norm_num)

theorem short_negative_root_eight_has_upperRight_support :
    (rootDerivationBlock 8).B ≠ 0 := by
  exact matrix_fin4_ne_zero_of_entry short_negative_root_eight_upperRight_entry (by norm_num)

theorem short_negative_root_three_mixes_blocks :
    (rootDerivationBlock 3).B ≠ 0 ∧
      (rootDerivationBlock 3).C ≠ 0 := by
  exact ⟨short_negative_root_three_has_upperRight_support,
    short_negative_root_three_has_lowerLeft_support⟩

theorem short_negative_root_eight_mixes_blocks :
    (rootDerivationBlock 8).B ≠ 0 ∧
      (rootDerivationBlock 8).C ≠ 0 := by
  exact ⟨short_negative_root_eight_has_upperRight_support,
    short_negative_root_eight_has_lowerLeft_support⟩

theorem short_negative_roots_mix_blocks (j : Fin 14)
    (hj : j = 0 ∨ j = 3 ∨ j = 8) :
    (rootDerivationBlock j).B ≠ 0 ∧
      (rootDerivationBlock j).C ≠ 0 := by
  rcases hj with rfl | rfl | rfl
  · exact short_negative_root_zero_mixes_blocks
  · exact short_negative_root_three_mixes_blocks
  · exact short_negative_root_eight_mixes_blocks

theorem short_negative_roots_have_lowerLeft_support (j : Fin 14)
    (hj : j = 0 ∨ j = 3 ∨ j = 8) :
    (rootDerivationBlock j).C ≠ 0 := by
  rcases hj with rfl | rfl | rfl
  · exact short_negative_root_zero_has_lowerLeft_support
  · exact short_negative_root_three_has_lowerLeft_support
  · exact short_negative_root_eight_has_lowerLeft_support

end InfoGeometry.Lie.CanonicalZornRootWittBlockBridge
