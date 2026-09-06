import InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport
import InfoGeometry.Lie.G2DoubleStarRootDecomposition
import InfoGeometry.Lie.CanonicalZornRootSystemComparison

/-!
# Basis-entry and double-star readout

This module exposes the owner-level `LinearMap.toMatrix` entry formula in the
real diagonal circular basis.  It performs no matrix inversion or finite
enumeration; all coordinate extraction is delegated to the basis `repr`.
-/

namespace InfoGeometry.Lie.CanonicalZornG2ToMatrixBridge

noncomputable section

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport
open InfoGeometry.Lie.SplitOctonionEllClosedFlow
open InfoGeometry.Lie.G2DoubleStarRootDecomposition
open InfoGeometry.Lie.CanonicalZornRootSystemComparison
open InfoGeometry.Lie.CanonicalZornRootPairing
open InfoGeometry.Lie.CanonicalZornG2LiteratureBridge

abbrev Der := CanonicalZornCartanAdjointRootDecomposition.Der
abbrev EndCZ := Module.End ℝ CanonicalZornDerivation.CZ

def derivationToCircularMatrix (D : EndCZ) : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix diagCircularBasis diagCircularBasis D

theorem derivationToCircularMatrix_entry (D : EndCZ) (i j : Fin 8) :
    derivationToCircularMatrix D i j =
      (diagCircularBasis.repr (D (diagCircularBasis j))) i := by
  simp [derivationToCircularMatrix, LinearMap.toMatrix_apply]

theorem nativeParameterMatrix_eq_derivationToCircularMatrix (k : Fin 14) :
    nativeParameterMatrix k =
      derivationToCircularMatrix (rootDerivationBasis k : Der).1 :=
  rfl

theorem derivationToCircularMatrix_rootDerivation_entry
    (q : Fin 14 × Fin 8 × Fin 8) :
    derivationToCircularMatrix (rootDerivationBasis q.1 : Der).1
        q.2.1 q.2.2 = rootDerivationMatrix q.1 q.2.1 q.2.2 := by
  rfl

theorem doubleStar_card : doubleStarIndices.card = 12 :=
  doubleStarIndices_card

theorem rootWeight_ne_zero_iff_mem_doubleStar (k : Fin 14) :
    rootWeight k ≠ 0 ↔ k ∈ doubleStarIndices := by
  have hmem : k ∈ doubleStarIndices ↔ rootWeight k ≠ 0 := by
    change k ∈ (doubleStarIndices : Set (Fin 14)) ↔ rootWeight k ≠ 0
    have hk := congrArg (fun s : Set (Fin 14) => k ∈ s)
      doubleStarIndices_eq_nonzero_root_indices
    simpa using hk
  exact hmem.symm

def doubleStarIndexToNonzero
    (k : {j : Fin 14 // j ∈ doubleStarIndices}) : nonzeroIndex :=
  ⟨k.1, by
    have hne : rootWeight k.1 ≠ 0 :=
      (rootWeight_ne_zero_iff_mem_doubleStar k.1).2 k.2
    constructor
    · intro h
      apply hne
      rw [rootWeight_eq_zero_iff]
      exact Or.inl h
    · intro h
      apply hne
      rw [rootWeight_eq_zero_iff]
      exact Or.inr h⟩

theorem doubleStarIndexToNonzero_bijective :
    Function.Bijective doubleStarIndexToNonzero := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : nonzeroIndex => x.1) hab
  · intro j
    have hne : rootWeight j.1 ≠ 0 := by
      intro hzero
      rcases (rootWeight_eq_zero_iff j.1).mp hzero with h | h
      · exact j.2.1 h
      · exact j.2.2 h
    have hmem : j.1 ∈ doubleStarIndices :=
      (rootWeight_ne_zero_iff_mem_doubleStar j.1).1 hne
    exact ⟨⟨j.1, hmem⟩, Subtype.ext rfl⟩

noncomputable def doubleStarIndexEquiv :
    {j : Fin 14 // j ∈ doubleStarIndices} ≃ nonzeroIndex :=
  Equiv.ofBijective doubleStarIndexToNonzero doubleStarIndexToNonzero_bijective

noncomputable def doubleStarRootIndexEquiv :
    {j : Fin 14 // j ∈ doubleStarIndices} ≃ RootIndex :=
  doubleStarIndexEquiv.trans nativeRootIndexEquiv

def rootPlaneCoordinates (j : Fin 14) : Fin 2 → ℝ := fun i =>
  if i = 0 then
    rootWeight j shortSimpleCoroot
  else
    rootWeight j longSimpleCoroot

def rootPlanarReadout (j : Fin 14) : ℝ × ℝ :=
  (rootPlaneCoordinates j 0, rootPlaneCoordinates j 1)

theorem rootPlaneCoordinates_simple_roots :
    rootPlaneCoordinates 10 0 = 2 ∧
      rootPlaneCoordinates 10 1 = -1 ∧
      rootPlaneCoordinates 1 0 = -3 ∧
      rootPlaneCoordinates 1 1 = 2 := by
  simpa [rootPlaneCoordinates] using paper_simple_root_calibration

theorem rootPlanarReadout_simple_roots :
    rootPlanarReadout 10 = (2, -1) ∧
      rootPlanarReadout 1 = (-3, 2) := by
  constructor
  · apply Prod.ext
    · exact rootPlaneCoordinates_simple_roots.1
    · exact rootPlaneCoordinates_simple_roots.2.1
  · apply Prod.ext
    · exact rootPlaneCoordinates_simple_roots.2.2.1
    · exact rootPlaneCoordinates_simple_roots.2.2.2

theorem rootPlaneCoordinates_root_nine_additive :
    rootPlaneCoordinates 9 =
      rootPlaneCoordinates 10 + rootPlaneCoordinates 1 := by
  have hchain := paper_positive_root_chain
  unfold rootPlaneCoordinates
  rw [hchain.2.2.1]
  rw [← hchain.1, ← hchain.2.1]
  funext i
  fin_cases i <;> simp [Pi.add_apply]

theorem rootPlaneCoordinates_root_eight_additive :
    rootPlaneCoordinates 8 =
      2 • rootPlaneCoordinates 10 + rootPlaneCoordinates 1 := by
  have hchain := paper_positive_root_chain
  unfold rootPlaneCoordinates
  rw [hchain.2.2.2.1, ← hchain.1, ← hchain.2.1]
  funext i
  fin_cases i <;> simp [Pi.add_apply]

theorem rootPlaneCoordinates_root_eleven_additive :
    rootPlaneCoordinates 11 =
      3 • rootPlaneCoordinates 10 + rootPlaneCoordinates 1 := by
  rcases paper_positive_root_chain with ⟨h10, h1, h9, h8, h11, h12⟩
  unfold rootPlaneCoordinates
  rw [h11, ← h10, ← h1]
  funext i
  fin_cases i <;> simp [Pi.add_apply]

theorem rootPlaneCoordinates_root_twelve_additive :
    rootPlaneCoordinates 12 =
      3 • rootPlaneCoordinates 10 + 2 • rootPlaneCoordinates 1 := by
  rcases paper_positive_root_chain with ⟨h10, h1, h9, h8, h11, h12⟩
  unfold rootPlaneCoordinates
  rw [h12, ← h10, ← h1]
  funext i
  fin_cases i <;> simp [Pi.add_apply]

theorem rootPlanarReadout_root_twelve :
    rootPlanarReadout 12 = (0, 1) := by
  apply Prod.ext
  · change rootPlaneCoordinates 12 0 = 0
    rw [rootPlaneCoordinates_root_twelve_additive]
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [rootPlaneCoordinates_simple_roots.1,
      rootPlaneCoordinates_simple_roots.2.2.1]
    norm_num
  · change rootPlaneCoordinates 12 1 = 1
    rw [rootPlaneCoordinates_root_twelve_additive]
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [rootPlaneCoordinates_simple_roots.2.1,
      rootPlaneCoordinates_simple_roots.2.2.2]
    norm_num

theorem rootPlanarReadout_root_eight :
    rootPlanarReadout 8 = (1, 0) := by
  apply Prod.ext
  · change rootPlaneCoordinates 8 0 = 1
    rw [rootPlaneCoordinates_root_eight_additive]
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [rootPlaneCoordinates_simple_roots.1,
      rootPlaneCoordinates_simple_roots.2.2.1]
    norm_num
  · change rootPlaneCoordinates 8 1 = 0
    rw [rootPlaneCoordinates_root_eight_additive]
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [rootPlaneCoordinates_simple_roots.2.1,
      rootPlaneCoordinates_simple_roots.2.2.2]
    norm_num

theorem rootPlanarReadout_root_nine :
    rootPlanarReadout 9 = (-1, 1) := by
  apply Prod.ext
  · change rootPlaneCoordinates 9 0 = -1
    rw [rootPlaneCoordinates_root_nine_additive]
    simp only [Pi.add_apply]
    rw [rootPlaneCoordinates_simple_roots.1,
      rootPlaneCoordinates_simple_roots.2.2.1]
    norm_num
  · change rootPlaneCoordinates 9 1 = 1
    rw [rootPlaneCoordinates_root_nine_additive]
    simp only [Pi.add_apply]
    rw [rootPlaneCoordinates_simple_roots.2.1,
      rootPlaneCoordinates_simple_roots.2.2.2]
    norm_num

theorem rootPlanarReadout_root_eleven :
    rootPlanarReadout 11 = (3, -1) := by
  apply Prod.ext
  · change rootPlaneCoordinates 11 0 = 3
    rw [rootPlaneCoordinates_root_eleven_additive]
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [rootPlaneCoordinates_simple_roots.1,
      rootPlaneCoordinates_simple_roots.2.2.1]
    norm_num
  · change rootPlaneCoordinates 11 1 = -1
    rw [rootPlaneCoordinates_root_eleven_additive]
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [rootPlaneCoordinates_simple_roots.2.1,
      rootPlaneCoordinates_simple_roots.2.2.2]
    norm_num

theorem rootPlaneCoordinates_neg_of_weight_neg
    (a b : Fin 14) (h : rootWeight a = -rootWeight b) :
    rootPlaneCoordinates a = -rootPlaneCoordinates b := by
  unfold rootPlaneCoordinates
  rw [h]
  funext i
  fin_cases i <;> simp [Pi.neg_apply]

theorem rootPlanarReadout_neg_of_weight_neg
    (a b : Fin 14) (h : rootWeight a = -rootWeight b) :
    rootPlanarReadout a = -rootPlanarReadout b := by
  apply Prod.ext
  · change rootPlaneCoordinates a 0 = -(rootPlaneCoordinates b 0)
    exact congrFun (rootPlaneCoordinates_neg_of_weight_neg a b h) 0
  · change rootPlaneCoordinates a 1 = -(rootPlaneCoordinates b 1)
    exact congrFun (rootPlaneCoordinates_neg_of_weight_neg a b h) 1

theorem rootPlaneCoordinates_opposite_pairs :
    rootPlaneCoordinates 10 = -rootPlaneCoordinates 0 ∧
      rootPlaneCoordinates 9 = -rootPlaneCoordinates 3 ∧
      rootPlaneCoordinates 4 = -rootPlaneCoordinates 8 ∧
      rootPlaneCoordinates 5 = -rootPlaneCoordinates 1 ∧
      rootPlaneCoordinates 11 = -rootPlaneCoordinates 2 ∧
      rootPlaneCoordinates 12 = -rootPlaneCoordinates 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply rootPlaneCoordinates_neg_of_weight_neg 10 0
    apply LinearMap.ext
    intro k
    exact rootWeight_neg_pair_0_10 k
  · apply rootPlaneCoordinates_neg_of_weight_neg 9 3
    apply LinearMap.ext
    intro k
    exact rootWeight_neg_pair_3_9 k
  · apply rootPlaneCoordinates_neg_of_weight_neg 4 8
    apply LinearMap.ext
    intro k
    exact rootWeight_neg_pair_4_8 k
  · apply rootPlaneCoordinates_neg_of_weight_neg 5 1
    apply LinearMap.ext
    intro k
    exact rootWeight_neg_pair_1_5 k
  · apply rootPlaneCoordinates_neg_of_weight_neg 11 2
    apply LinearMap.ext
    intro k
    exact rootWeight_neg_pair_2_11 k
  · apply rootPlaneCoordinates_neg_of_weight_neg 12 7
    apply LinearMap.ext
    intro k
    exact rootWeight_neg_pair_7_12 k

theorem rootPlanarReadout_root_seven :
    rootPlanarReadout 7 = (0, -1) := by
  have h : rootPlanarReadout 12 = -rootPlanarReadout 7 :=
    rootPlanarReadout_neg_of_weight_neg 12 7 (by
      apply LinearMap.ext
      intro k
      exact rootWeight_neg_pair_7_12 k)
  rw [rootPlanarReadout_root_twelve] at h
  apply Prod.ext
  · have hf := congrArg Prod.fst h
    simpa using hf.symm
  · have hs := congrArg Prod.snd h
    change (1 : ℝ) = -(rootPlanarReadout 7).2 at hs
    linarith

theorem rootPlanarReadout_root_zero :
    rootPlanarReadout 0 = (-2, 1) := by
  have h : rootPlanarReadout 10 = -rootPlanarReadout 0 :=
    rootPlanarReadout_neg_of_weight_neg 10 0 (by
      apply LinearMap.ext
      intro k
      exact rootWeight_neg_pair_0_10 k)
  rw [rootPlanarReadout_simple_roots.1] at h
  apply Prod.ext
  · have hf := congrArg Prod.fst h
    change (2 : ℝ) = -(rootPlanarReadout 0).1 at hf
    linarith
  · have hs := congrArg Prod.snd h
    change (-1 : ℝ) = -(rootPlanarReadout 0).2 at hs
    linarith

theorem rootPlanarReadout_root_three :
    rootPlanarReadout 3 = (1, -1) := by
  have h : rootPlanarReadout 9 = -rootPlanarReadout 3 :=
    rootPlanarReadout_neg_of_weight_neg 9 3 (by
      apply LinearMap.ext
      intro k
      exact rootWeight_neg_pair_3_9 k)
  rw [rootPlanarReadout_root_nine] at h
  apply Prod.ext
  · have hf := congrArg Prod.fst h
    change (-1 : ℝ) = -(rootPlanarReadout 3).1 at hf
    linarith
  · have hs := congrArg Prod.snd h
    change (1 : ℝ) = -(rootPlanarReadout 3).2 at hs
    linarith

theorem rootPlanarReadout_root_four :
    rootPlanarReadout 4 = (-1, 0) := by
  have h : rootPlanarReadout 4 = -rootPlanarReadout 8 :=
    rootPlanarReadout_neg_of_weight_neg 4 8 (by
      apply LinearMap.ext
      intro k
      exact rootWeight_neg_pair_4_8 k)
  rw [rootPlanarReadout_root_eight] at h
  apply Prod.ext
  · have hf := congrArg Prod.fst h
    change (rootPlanarReadout 4).1 = -(1 : ℝ) at hf
    linarith
  · have hs := congrArg Prod.snd h
    change (rootPlanarReadout 4).2 = -(0 : ℝ) at hs
    linarith

theorem rootPlanarReadout_root_five :
    rootPlanarReadout 5 = (3, -2) := by
  have h : rootPlanarReadout 5 = -rootPlanarReadout 1 :=
    rootPlanarReadout_neg_of_weight_neg 5 1 (by
      apply LinearMap.ext
      intro k
      exact rootWeight_neg_pair_1_5 k)
  rw [rootPlanarReadout_simple_roots.2] at h
  apply Prod.ext
  · have hf := congrArg Prod.fst h
    change (rootPlanarReadout 5).1 = -(-3 : ℝ) at hf
    linarith
  · have hs := congrArg Prod.snd h
    change (rootPlanarReadout 5).2 = -(2 : ℝ) at hs
    linarith

theorem rootPlanarReadout_root_two :
    rootPlanarReadout 2 = (-3, 1) := by
  have h : rootPlanarReadout 11 = -rootPlanarReadout 2 :=
    rootPlanarReadout_neg_of_weight_neg 11 2 (by
      apply LinearMap.ext
      intro k
      exact rootWeight_neg_pair_2_11 k)
  rw [rootPlanarReadout_root_eleven] at h
  apply Prod.ext
  · have hf := congrArg Prod.fst h
    change (3 : ℝ) = -(rootPlanarReadout 2).1 at hf
    linarith
  · have hs := congrArg Prod.snd h
    change (-1 : ℝ) = -(rootPlanarReadout 2).2 at hs
    linarith

theorem rootPlanarReadout_explicit_table :
    rootPlanarReadout 0 = (-2, 1) ∧
      rootPlanarReadout 1 = (-3, 2) ∧
      rootPlanarReadout 2 = (-3, 1) ∧
      rootPlanarReadout 3 = (1, -1) ∧
      rootPlanarReadout 4 = (-1, 0) ∧
      rootPlanarReadout 5 = (3, -2) ∧
      rootPlanarReadout 7 = (0, -1) ∧
      rootPlanarReadout 8 = (1, 0) ∧
      rootPlanarReadout 9 = (-1, 1) ∧
      rootPlanarReadout 10 = (2, -1) ∧
      rootPlanarReadout 11 = (3, -1) ∧
      rootPlanarReadout 12 = (0, 1) := by
  exact ⟨rootPlanarReadout_root_zero,
    rootPlanarReadout_simple_roots.2,
    rootPlanarReadout_root_two,
    rootPlanarReadout_root_three,
    rootPlanarReadout_root_four,
    rootPlanarReadout_root_five,
    rootPlanarReadout_root_seven,
    rootPlanarReadout_root_eight,
    rootPlanarReadout_root_nine,
    rootPlanarReadout_simple_roots.1,
    rootPlanarReadout_root_eleven,
    rootPlanarReadout_root_twelve⟩

end
end InfoGeometry.Lie.CanonicalZornG2ToMatrixBridge
