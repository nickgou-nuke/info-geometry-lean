import InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native fourteen-channel Cartan decomposition

This owner consumes the generic joint-eigenspace calculus and computes the
concrete fourteen-dimensional spectrum from the existing parameter equivalence.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

abbrev Der := CanonicalZornCartanAdjointAction.Der

open InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum
open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

instance : SMul ℝ Der where
  smul r D := ⟨r • (D : CanonicalZornDerivation.EndCZ),
    SMulMemClass.smul_mem r D.property⟩

instance : Module ℝ Der where
  smul := (inferInstance : SMul ℝ Der).smul
  one_smul D := Subtype.ext (_root_.one_smul ℝ (D : CanonicalZornDerivation.EndCZ))
  mul_smul a b D := Subtype.ext (SemigroupAction.mul_smul a b
    (D : CanonicalZornDerivation.EndCZ))
  smul_zero r := Subtype.ext (_root_.smul_zero r)
  smul_add r D E := Subtype.ext (_root_.smul_add r
    (D : CanonicalZornDerivation.EndCZ) (E : CanonicalZornDerivation.EndCZ))
  add_smul a b D := Subtype.ext (_root_.add_smul a b
    (D : CanonicalZornDerivation.EndCZ))
  zero_smul D := Subtype.ext (_root_.zero_smul ℝ
    (D : CanonicalZornDerivation.EndCZ))

def parameterUnit (j : Fin 14) : Params :=
  fun i => if i = j then 1 else 0

def coordWeight (j : Fin 3) : Weight where
  toFun k := k.1 j
  map_add' k l := rfl
  map_smul' a k := rfl

def rootWeight (j : Fin 14) : Weight :=
  match j with
  | 0 => - coordWeight 0
  | 1 => coordWeight 1 - coordWeight 0
  | 2 => coordWeight 2 - coordWeight 0
  | 3 => - coordWeight 1
  | 4 => coordWeight 2
  | 5 => coordWeight 0 - coordWeight 1
  | 6 => 0
  | 7 => coordWeight 2 - coordWeight 1
  | 8 => - coordWeight 2
  | 9 => coordWeight 1
  | 10 => coordWeight 0
  | 11 => coordWeight 0 - coordWeight 2
  | 12 => coordWeight 1 - coordWeight 2
  | 13 => 0

def shortRootWeights : Set Weight :=
  {coordWeight 0, -coordWeight 0,
    coordWeight 1, -coordWeight 1,
    coordWeight 2, -coordWeight 2}

def longRootWeights : Set Weight :=
  {coordWeight 1 - coordWeight 0, coordWeight 0 - coordWeight 1,
    coordWeight 2 - coordWeight 0, coordWeight 0 - coordWeight 2,
    coordWeight 2 - coordWeight 1, coordWeight 1 - coordWeight 2}

theorem rootWeight_range_eq_zero_union_short_long :
    Set.range (rootWeight : Fin 14 → Weight) =
      {(0 : Weight)} ∪ shortRootWeights ∪ longRootWeights := by
  ext w
  simp only [Set.mem_range, shortRootWeights, longRootWeights,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp [rootWeight]
  · intro h
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · rcases h with h | h
      · exact ⟨6, by simpa [rootWeight] using h.symm⟩
      · rcases h with h | h
        · exact ⟨10, by simpa [rootWeight] using h.symm⟩
        · rcases h with h | h
          · exact ⟨0, by simpa [rootWeight] using h.symm⟩
          · rcases h with h | h
            · exact ⟨9, by simpa [rootWeight] using h.symm⟩
            · rcases h with h | h
              · exact ⟨3, by simpa [rootWeight] using h.symm⟩
              · rcases h with h | h
                · exact ⟨4, by simpa [rootWeight] using h.symm⟩
                · exact ⟨8, by simpa [rootWeight] using h.symm⟩
    · rcases h with h | h
      · exact ⟨1, by simpa [rootWeight] using h.symm⟩
      · rcases h with h | h
        · exact ⟨5, by simpa [rootWeight] using h.symm⟩
        · rcases h with h | h
          · exact ⟨2, by simpa [rootWeight] using h.symm⟩
          · rcases h with h | h
            · exact ⟨11, by simpa [rootWeight] using h.symm⟩
            · rcases h with h | h
              · exact ⟨7, by simpa [rootWeight] using h.symm⟩
              · exact ⟨12, by simpa [rootWeight] using h.symm⟩

theorem rootWeight_range_neg_closed :
    {w : Weight | ∃ v ∈ Set.range rootWeight, w = -v} =
      Set.range rootWeight := by
  have hneg (j : Fin 14) : -rootWeight j ∈ Set.range rootWeight := by
    fin_cases j
    · exact ⟨10, by simp [rootWeight]⟩
    · exact ⟨5, by simp [rootWeight]⟩
    · exact ⟨11, by simp [rootWeight]⟩
    · exact ⟨9, by simp [rootWeight]⟩
    · exact ⟨8, by simp [rootWeight]⟩
    · exact ⟨1, by simp [rootWeight]⟩
    · exact ⟨6, by simp [rootWeight]⟩
    · exact ⟨12, by simp [rootWeight]⟩
    · exact ⟨4, by simp [rootWeight]⟩
    · exact ⟨3, by simp [rootWeight]⟩
    · exact ⟨0, by simp [rootWeight]⟩
    · exact ⟨2, by simp [rootWeight]⟩
    · exact ⟨7, by simp [rootWeight]⟩
    · exact ⟨13, by simp [rootWeight]⟩
  ext w
  constructor
  · rintro ⟨v, ⟨j, rfl⟩, rfl⟩
    exact hneg j
  · intro hw
    obtain ⟨j, rfl⟩ := hw
    exact ⟨-rootWeight j, hneg j, by simp⟩

/-! The named coordinate weights are exactly the coefficients of the native
adjoint coordinate formula.  The three entries written using a single
traceless coordinate use the defining relation `k₀ + k₁ + k₂ = 0`; this is a
coordinate readout theorem, not an identification with an abstract root
system. -/

theorem rootWeight_eq_adCartanDiagonalCoefficient
    (k : TracelessWeight) (j : Fin 14) :
    rootWeight j k = adCartanDiagonalCoefficient k j := by
  have h := k.2
  change ∑ i, k.1 i = 0 at h
  have h' : k.1 0 + k.1 1 + k.1 2 = 0 := by
    simpa [Fin.sum_univ_three] using h
  fin_cases j <;>
    simp [rootWeight, coordWeight, adCartanDiagonalCoefficient,
      Fin.sum_univ_three] at * <;>
    linarith

theorem adCartanCoordinates_parameterUnit (k : TracelessWeight) (j : Fin 14) :
    adCartanCoordinates k (parameterUnit j) =
      (rootWeight j k) • parameterUnit j := by
  rw [rootWeight_eq_adCartanDiagonalCoefficient]
  have hunit : parameterUnit j = Pi.single j (1 : ℝ) := by
    funext i
    by_cases h : i = j <;> simp [parameterUnit, Pi.single_apply, h]
  rw [hunit]
  exact adCartanCoordinates_basis_eigen k j

/-! The fourteen coordinate weights now exhibit the expected two zero
weights and six opposite pairs.  This is the finite spectral count; the
short/long root-system interpretation is intentionally left to a later
Cartan-metric theorem. -/

theorem rootWeight_zero_6 (k : TracelessWeight) : rootWeight 6 k = 0 := by
  rfl

theorem rootWeight_zero_13 (k : TracelessWeight) : rootWeight 13 k = 0 := by
  rfl

theorem rootWeight_neg_pair_0_10 (k : TracelessWeight) :
    rootWeight 10 k = -rootWeight 0 k := by
  simp [rootWeight, coordWeight]

theorem rootWeight_neg_pair_3_9 (k : TracelessWeight) :
    rootWeight 9 k = -rootWeight 3 k := by
  simp [rootWeight, coordWeight]

theorem rootWeight_neg_pair_4_8 (k : TracelessWeight) :
    rootWeight 4 k = -rootWeight 8 k := by
  simp [rootWeight, coordWeight]

theorem rootWeight_neg_pair_1_5 (k : TracelessWeight) :
    rootWeight 5 k = -rootWeight 1 k := by
  simp [rootWeight, coordWeight]

theorem rootWeight_neg_pair_2_11 (k : TracelessWeight) :
    rootWeight 11 k = -rootWeight 2 k := by
  simp [rootWeight, coordWeight]

theorem rootWeight_neg_pair_7_12 (k : TracelessWeight) :
    rootWeight 12 k = -rootWeight 7 k := by
  simp [rootWeight, coordWeight]

noncomputable def rootDerivation (j : Fin 14) : Der :=
  canonicalParameterLinearEquiv (parameterUnit j)

noncomputable def rootDerivationBasis : Module.Basis (Fin 14) ℝ Der :=
  (Pi.basisFun ℝ (Fin 14)).map canonicalParameterLinearEquiv

theorem rootDerivationBasis_apply (j : Fin 14) :
    rootDerivationBasis j = rootDerivation j := by
  rw [rootDerivationBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  congr 1
  ext i
  by_cases h : j = i
  · subst i
    simp [parameterUnit]
  · have h' : i ≠ j := Ne.symm h
    simp [parameterUnit, Pi.single_apply, h, h']

theorem adCartan_rootDerivation (k : TracelessWeight) (j : Fin 14) :
    adCartan k (rootDerivation j) =
      ((rootWeight j k : ℝ) • (rootDerivation j : Der) : Der) := by
  apply canonicalParameterLinearEquiv.symm.injective
  change adCartanCoordinates k (parameterUnit j) = _
  rw [adCartanCoordinates_parameterUnit]
  simp [rootDerivation]

theorem parameterUnit_ne_zero (j : Fin 14) : parameterUnit j ≠ 0 := by
  intro h
  have hj := congrFun h j
  simp [parameterUnit] at hj

theorem rootDerivation_ne_zero (j : Fin 14) : rootDerivation j ≠ 0 := by
  intro h
  apply parameterUnit_ne_zero j
  apply canonicalParameterLinearEquiv.injective
  change canonicalParameterLinearEquiv (parameterUnit j) =
    canonicalParameterLinearEquiv 0
  simpa [rootDerivation] using h

theorem rootDerivationBasis_is_simultaneous_eigenbasis :
    ∀ j k, adCartan k (rootDerivationBasis j) =
      ((rootWeight j k : ℝ) • (rootDerivationBasis j : Der) : Der) := by
  intro j k
  rw [rootDerivationBasis_apply]
  exact adCartan_rootDerivation k j

theorem rootDerivationBasis_span :
    Submodule.span ℝ (Set.range rootDerivationBasis) = ⊤ :=
  rootDerivationBasis.span_eq

theorem rootWeight_ne_zero_of_ne_zero_indices (j : Fin 14)
    (h6 : j ≠ 6) (h13 : j ≠ 13) : rootWeight j ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : Weight => f (cartanBasis 0)) h
  have h1 := congrArg (fun f : Weight => f (cartanBasis 1)) h
  fin_cases j <;>
    simp [rootWeight, coordWeight, cartanBasis, tracelessWeightEquiv] at h0 h1 h6 h13

theorem rootWeight_eq_zero_iff (j : Fin 14) :
    rootWeight j = 0 ↔ j = 6 ∨ j = 13 := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    exact rootWeight_ne_zero_of_ne_zero_indices j hne.1 hne.2 h
  · intro h
    rcases h with rfl | rfl
    · rfl
    · rfl

def shortRootIndices : Finset (Fin 14) := {0, 3, 4, 8, 9, 10}

def longRootIndices : Finset (Fin 14) := {1, 2, 5, 7, 11, 12}

theorem shortRootIndices_card : shortRootIndices.card = 6 := by
  decide

theorem longRootIndices_card : longRootIndices.card = 6 := by
  decide

theorem rootWeight_short_indices_nonzero (j : Fin 14)
    (hj : j ∈ shortRootIndices) : rootWeight j ≠ 0 := by
  apply rootWeight_ne_zero_of_ne_zero_indices j
  · intro h
    subst j
    simp [shortRootIndices] at hj
  · intro h
    subst j
    simp [shortRootIndices] at hj

theorem rootWeight_long_indices_nonzero (j : Fin 14)
    (hj : j ∈ longRootIndices) : rootWeight j ≠ 0 := by
  apply rootWeight_ne_zero_of_ne_zero_indices j
  · intro h
    subst j
    simp [longRootIndices] at hj
  · intro h
    subst j
    simp [longRootIndices] at hj

def rootWeightCode : Fin 14 → Fin 2 → ℤ := ![
  ![-1, 0], ![-1, 1], ![-2, -1], ![0, -1], ![-1, -1], ![1, -1],
  ![0, 0], ![-1, -2], ![1, 1], ![0, 1], ![1, 0], ![2, 1],
  ![1, 2], ![0, 0]]

theorem rootWeightCode_injective_on_nonzero :
    ∀ i j : Fin 14, j ≠ 6 → j ≠ 13 →
      rootWeightCode i = rootWeightCode j → i = j := by
  decide

theorem rootWeight_eval_code (j : Fin 14) (i : Fin 2) :
    rootWeight j (tracelessWeightEquiv (Pi.single i (1 : ℝ))) =
      (rootWeightCode j i : ℝ) := by
  fin_cases j <;> fin_cases i <;>
    simp [rootWeight, coordWeight, rootWeightCode, tracelessWeightEquiv,
      Fin.sum_univ_three]
  <;> norm_num

theorem adCartanWeight_separates_nonzero_indices
    (i j : Fin 14) (hij : i ≠ j) (h6 : j ≠ 6) (h13 : j ≠ 13) :
    ∃ k : TracelessWeight,
      adCartanDiagonalCoefficient k i ≠ rootWeight j k := by
  by_contra h
  push_neg at h
  have hroot : rootWeight i = rootWeight j := by
    ext k
    rw [rootWeight_eq_adCartanDiagonalCoefficient]
    exact h k
  have hcode : rootWeightCode i = rootWeightCode j := by
    funext q
    fin_cases q
    · simpa [rootWeight_eval_code] using
        congrArg (fun w : Weight => w
          (tracelessWeightEquiv (Pi.single 0 (1 : ℝ)))) hroot
    · simpa [rootWeight_eval_code] using
        congrArg (fun w : Weight => w
          (tracelessWeightEquiv (Pi.single 1 (1 : ℝ)))) hroot
  exact hij (rootWeightCode_injective_on_nonzero i j h6 h13 hcode)

theorem jointEigenspace_eq_span_rootDerivation
    (j : Fin 14) (h6 : j ≠ 6) (h13 : j ≠ 13) :
    jointEigenspace (rootWeight j) = ℝ ∙ rootDerivation j := by
  apply le_antisymm
  · intro D hD
    let p : Params := canonicalParameterLinearEquiv.symm D
    have hp (k : TracelessWeight) :
        adCartanCoordinates k p = (rootWeight j k) • p := by
      have htransport := congrArg
        (fun X : Der => (canonicalParameterLinearEquiv.symm X : Params)) (hD k)
      change canonicalParameterLinearEquiv.symm (adCartan k D) =
        canonicalParameterLinearEquiv.symm ((rootWeight j k) • D) at htransport
      rw [map_smul] at htransport
      simpa [p, adCartanCoordinates] using htransport
    have hzero (i : Fin 14) (hi : i ≠ j) : p i = 0 := by
      obtain ⟨k, hk⟩ := adCartanWeight_separates_nonzero_indices i j hi h6 h13
      have hpi := congrFun (hp k) i
      rw [adCartanCoordinates_apply_diagonal] at hpi
      have hmul :
          (adCartanDiagonalCoefficient k i - rootWeight j k) * p i = 0 := by
        have :
            adCartanDiagonalCoefficient k i * p i =
              rootWeight j k * p i := by
          simpa [smul_eq_mul] using hpi
        linarith
      rcases mul_eq_zero.mp hmul with hd | hi0
      · exact False.elim (hk (sub_eq_zero.mp hd))
      · exact hi0
    have hpform : p = p j • parameterUnit j := by
      funext i
      by_cases hi : i = j
      · subst i
        simp [parameterUnit]
      · simp [hzero i hi, parameterUnit, hi]
    have hDform : D = ((p j : ℝ) • rootDerivation j : Der) := by
      apply (canonicalParameterLinearEquiv.symm).injective
      change p = canonicalParameterLinearEquiv.symm
        ((p j : ℝ) • rootDerivation j : Der)
      rw [map_smul]
      simpa only [rootDerivation, LinearEquiv.symm_apply_apply] using hpform
    rw [hDform]
    exact Submodule.mem_span_singleton.mpr ⟨p j, rfl⟩
  · intro D hD
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hD
    rw [mem_jointEigenspace_iff]
    intro k
    change adCartan k (c • rootDerivation j) =
      ((rootWeight j k : ℝ) • (c • rootDerivation j) : Der)
    rw [(adCartan k).map_smul, adCartan_rootDerivation]
    simp [smul_smul, mul_comm]

def cartanRootSpan : Submodule ℝ Der :=
  Submodule.span ℝ ({rootDerivation 6, rootDerivation 13} : Set Der)

theorem jointEigenspace_zero_eq_cartanRootSpan :
    jointEigenspace 0 = cartanRootSpan := by
  apply le_antisymm
  · intro D hD
    let p : Params := canonicalParameterLinearEquiv.symm D
    have hp (k : TracelessWeight) :
        adCartanCoordinates k p = (0 : Weight) k • p := by
      have htransport := congrArg
        (fun X : Der => (canonicalParameterLinearEquiv.symm X : Params)) (hD k)
      change canonicalParameterLinearEquiv.symm (adCartan k D) =
        canonicalParameterLinearEquiv.symm ((0 : Weight) k • D) at htransport
      rw [map_smul] at htransport
      simpa [p, adCartanCoordinates] using htransport
    have hzero (i : Fin 14) (hi6 : i ≠ 6) (hi13 : i ≠ 13) : p i = 0 := by
      have hwi : rootWeight i ≠ 0 :=
        rootWeight_ne_zero_of_ne_zero_indices i hi6 hi13
      obtain ⟨k, hk⟩ : ∃ k : TracelessWeight, rootWeight i k ≠ 0 := by
        by_contra hn
        push_neg at hn
        apply hwi
        ext k
        exact hn k
      have hpi := congrFun (hp k) i
      rw [adCartanCoordinates_apply_diagonal] at hpi
      have hmul : adCartanDiagonalCoefficient k i * p i = 0 := by
        simpa [smul_eq_mul] using hpi
      rcases mul_eq_zero.mp hmul with hc | hi0
      · exact False.elim (hk (by simpa [rootWeight_eq_adCartanDiagonalCoefficient] using hc))
      · exact hi0
    have hpform : p = p 6 • parameterUnit 6 + p 13 • parameterUnit 13 := by
      funext i
      fin_cases i <;>
        simp [parameterUnit, hzero, p]
    have hDform : D =
        p 6 • rootDerivation 6 + p 13 • rootDerivation 13 := by
      apply (canonicalParameterLinearEquiv.symm).injective
      change p = canonicalParameterLinearEquiv.symm
        (p 6 • rootDerivation 6 + p 13 • rootDerivation 13)
      simp only [map_add, map_smul]
      simpa only [rootDerivation, LinearEquiv.symm_apply_apply] using hpform
    rw [hDform]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (by simp))
  · apply Submodule.span_le.2
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · apply (mem_jointEigenspace_iff 0 (rootDerivation 6)).2
      intro k
      rw [adCartan_rootDerivation, rootWeight_zero_6]
      have hk : (0 : Weight) k = 0 := rfl
      rw [hk]
      have hs : SMul.smul (0 : ℝ) (rootDerivation 6 : Der) = 0 := by
        apply Subtype.ext
        change (0 : ℝ) • (rootDerivation 6 : CanonicalZornDerivation.EndCZ) = 0
        exact _root_.zero_smul ℝ _
      calc
        (0 : ℝ) • (rootDerivation 6 : Der) = 0 := _root_.zero_smul ℝ _
        _ = SMul.smul 0 (rootDerivation 6 : Der) := hs.symm
    · apply (mem_jointEigenspace_iff 0 (rootDerivation 13)).2
      intro k
      rw [adCartan_rootDerivation, rootWeight_zero_13]
      have hk : (0 : Weight) k = 0 := rfl
      rw [hk]
      have hs : SMul.smul (0 : ℝ) (rootDerivation 13 : Der) = 0 := by
        apply Subtype.ext
        change (0 : ℝ) • (rootDerivation 13 : CanonicalZornDerivation.EndCZ) = 0
        exact _root_.zero_smul ℝ _
      calc
        (0 : ℝ) • (rootDerivation 13 : Der) = 0 := _root_.zero_smul ℝ _
        _ = SMul.smul 0 (rootDerivation 13 : Der) := hs.symm

theorem cartanRootSpan_finrank : Module.finrank ℝ cartanRootSpan = 2 := by
  letI : FiniteDimensional ℝ Der :=
    FiniteDimensional.of_fintype_basis rootDerivationBasis
  letI : FiniteDimensional ℝ cartanRootSpan :=
    FiniteDimensional.finiteDimensional_submodule cartanRootSpan
  let v : Fin 2 → Der := ![rootDerivation 6, rootDerivation 13]
  have hv : LinearIndependent ℝ v := by
    rw [linearIndependent_fin2]
    constructor
    · exact rootDerivation_ne_zero 13
    · intro a ha
      have ha' := congrArg
        (fun D : Der => canonicalParameterLinearEquiv.symm D) ha
      have hcoord := congrFun ha' 6
      simp [v, rootDerivation, parameterUnit] at hcoord
  have hrange : Set.range v =
      ({rootDerivation 6, rootDerivation 13} : Set Der) := by
    ext D
    simp [v, or_comm]
  change Module.finrank ℝ
      (Submodule.span ℝ
        ({rootDerivation 6, rootDerivation 13} : Set Der)) = 2
  rw [← hrange, finrank_span_eq_card hv]
  rfl

theorem nativeCartan_eq_cartanRootSpan :
    (axialCartanLieSubalgebra : Submodule ℝ Der) = cartanRootSpan := by
  letI : FiniteDimensional ℝ Der :=
    FiniteDimensional.of_fintype_basis rootDerivationBasis
  apply Submodule.eq_of_le_of_finrank_eq
  · intro D hD
    have hJ : D ∈ jointEigenspace 0 := by
      rcases hD with ⟨k, hk⟩
      rw [← hk]
      exact cartan_mem_jointEigenspace_zero k
    rw [jointEigenspace_zero_eq_cartanRootSpan] at hJ
    exact hJ
  · simpa only [cartanRootSpan_finrank] using
      axialCartanLieSubalgebra_finrank

def nonzeroIndex := {j : Fin 14 // j ≠ 6 ∧ j ≠ 13}
deriving DecidableEq, Fintype

theorem rootWeight_injective_on_nonzero
    (i j : nonzeroIndex) (hij : i ≠ j) : rootWeight i.1 ≠ rootWeight j.1 := by
  intro hEq
  obtain ⟨k, hk⟩ := adCartanWeight_separates_nonzero_indices
    i.1 j.1 (by
      intro h
      apply hij
      exact Subtype.ext h) j.2.1 j.2.2
  apply hk
  rw [← rootWeight_eq_adCartanDiagonalCoefficient k i.1, hEq]

def rootSpace (j : Fin 14) : Submodule ℝ Der :=
  ℝ ∙ rootDerivation j

def rootSpaceSum : Submodule ℝ Der :=
  ⨆ j : nonzeroIndex, rootSpace j.1

theorem rootSpaceSum_mem (j : nonzeroIndex) :
    rootDerivation j.1 ∈ rootSpaceSum := by
  apply le_iSup (fun j : nonzeroIndex => rootSpace j.1) j
  exact Submodule.mem_span_singleton.mpr ⟨1, by
    exact one_smul ℝ (rootDerivation j.1)⟩

theorem cartanRootSpan_sup_rootSpaceSum_eq_top :
    cartanRootSpan ⊔ rootSpaceSum = ⊤ := by
  apply top_unique
  rw [← rootDerivationBasis_span]
  apply Submodule.span_le.2
  intro x hx
  obtain ⟨j, rfl⟩ := hx
  have hjbasis := rootDerivationBasis_apply j
  by_cases h6 : j = 6
  · subst j
    rw [hjbasis]
    exact Submodule.mem_sup_left
      (Submodule.subset_span (by simp))
  by_cases h13 : j = 13
  · subst j
    rw [hjbasis]
    exact Submodule.mem_sup_left
      (Submodule.subset_span (by simp))
  rw [hjbasis]
  exact Submodule.mem_sup_right
    (rootSpaceSum_mem ⟨j, h6, h13⟩)

theorem jointEigenspace_zero_coordinate
    {D : Der} (hD : D ∈ jointEigenspace 0) (i : Fin 14)
    (hi6 : i ≠ 6) (hi13 : i ≠ 13) :
    (canonicalParameterLinearEquiv.symm D) i = 0 := by
  let p : Params := canonicalParameterLinearEquiv.symm D
  have hp (k : TracelessWeight) :
      adCartanCoordinates k p = (0 : Weight) k • p := by
    have htransport := congrArg
      (fun X : Der => (canonicalParameterLinearEquiv.symm X : Params)) (hD k)
    change canonicalParameterLinearEquiv.symm (adCartan k D) =
      canonicalParameterLinearEquiv.symm ((0 : Weight) k • D) at htransport
    rw [map_smul] at htransport
    simpa [p, adCartanCoordinates] using htransport
  have hwi : rootWeight i ≠ 0 :=
    rootWeight_ne_zero_of_ne_zero_indices i hi6 hi13
  obtain ⟨k, hk⟩ : ∃ k : TracelessWeight, rootWeight i k ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hwi
    ext k
    exact hn k
  have hpi := congrFun (hp k) i
  rw [adCartanCoordinates_apply_diagonal] at hpi
  have hmul : adCartanDiagonalCoefficient k i * p i = 0 := by
    simpa [smul_eq_mul] using hpi
  rcases mul_eq_zero.mp hmul with hc | hi0
  · exact False.elim (hk (by simpa [rootWeight_eq_adCartanDiagonalCoefficient] using hc))
  · exact hi0

theorem rootSpaceSum_coordinates_zero
    {D : Der} (hD : D ∈ rootSpaceSum) :
    (canonicalParameterLinearEquiv.symm D) 6 = 0 ∧
      (canonicalParameterLinearEquiv.symm D) 13 = 0 := by
  refine Submodule.iSup_induction
    (fun j : nonzeroIndex => rootSpace j.1) hD
    (motive := fun D : Der =>
      (canonicalParameterLinearEquiv.symm D) 6 = 0 ∧
        (canonicalParameterLinearEquiv.symm D) 13 = 0) ?_ ?_ ?_
  · intro j x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    constructor
    · change (canonicalParameterLinearEquiv.symm
        (c • canonicalParameterLinearEquiv (parameterUnit j.1))) 6 = 0
      rw [map_smul, LinearEquiv.symm_apply_apply]
      simp [parameterUnit, Ne.symm j.2.1]
    · change (canonicalParameterLinearEquiv.symm
        (c • canonicalParameterLinearEquiv (parameterUnit j.1))) 13 = 0
      rw [map_smul, LinearEquiv.symm_apply_apply]
      simp [parameterUnit, Ne.symm j.2.2]
  · exact ⟨by simp, by simp⟩
  · intro x y hx hy
    constructor
    · change (canonicalParameterLinearEquiv.symm x) 6 +
        (canonicalParameterLinearEquiv.symm y) 6 = 0
      rw [hx.1, hy.1, _root_.add_zero]
    · change (canonicalParameterLinearEquiv.symm x) 13 +
        (canonicalParameterLinearEquiv.symm y) 13 = 0
      rw [hx.2, hy.2, _root_.add_zero]

theorem cartanRootSpan_disjoint_rootSpaceSum :
    Disjoint cartanRootSpan rootSpaceSum := by
  rw [Submodule.disjoint_def]
  intro D hC hR
  have hJ : D ∈ jointEigenspace 0 := by
    rw [jointEigenspace_zero_eq_cartanRootSpan]
    exact hC
  have hnonzero (i : Fin 14) (hi6 : i ≠ 6) (hi13 : i ≠ 13) :
      (canonicalParameterLinearEquiv.symm D) i = 0 :=
    jointEigenspace_zero_coordinate hJ i hi6 hi13
  have hz := rootSpaceSum_coordinates_zero hR
  have hpzero : canonicalParameterLinearEquiv.symm D = 0 := by
    funext i
    by_cases h6i : i = 6
    · simpa [h6i] using hz.1
    by_cases h13i : i = 13
    · simpa [h13i] using hz.2
    · exact hnonzero i h6i h13i
  apply (canonicalParameterLinearEquiv.symm).injective
  simpa using hpzero

theorem cartanRootSpan_inf_rootSpaceSum_eq_bot :
    cartanRootSpan ⊓ rootSpaceSum = ⊥ :=
  disjoint_iff.mp cartanRootSpan_disjoint_rootSpaceSum

theorem cartanRootSpan_isComplement_rootSpaceSum :
    IsCompl cartanRootSpan rootSpaceSum :=
  ⟨cartanRootSpan_disjoint_rootSpaceSum,
    codisjoint_iff.mpr cartanRootSpan_sup_rootSpaceSum_eq_top⟩

theorem nonzeroIndex_card : Fintype.card nonzeroIndex = 12 := by
  decide

theorem rootSpace_eq_jointEigenspace (j : nonzeroIndex) :
    rootSpace j.1 = jointEigenspace (rootWeight j.1) := by
  exact (jointEigenspace_eq_span_rootDerivation j.1 j.2.1 j.2.2).symm

theorem rootSpace_bracket_mem_jointEigenspace_add
    (i j : nonzeroIndex) {X Y : Der}
    (hX : X ∈ rootSpace i.1) (hY : Y ∈ rootSpace j.1) :
    ⁅X, Y⁆ ∈ jointEigenspace (rootWeight i.1 + rootWeight j.1) := by
  apply lie_mem_jointEigenspace_add (rootWeight i.1) (rootWeight j.1)
  · rw [← rootSpace_eq_jointEigenspace i]
    exact hX
  · rw [← rootSpace_eq_jointEigenspace j]
    exact hY

theorem rootSpace_finrank (j : nonzeroIndex) :
    Module.finrank ℝ (rootSpace j.1) = 1 := by
  letI : FiniteDimensional ℝ Der :=
    FiniteDimensional.of_fintype_basis rootDerivationBasis
  exact finrank_span_singleton (rootDerivation_ne_zero j.1)

theorem rootDerivation_nonzero_linearIndependent :
    LinearIndependent ℝ (fun j : nonzeroIndex => rootDerivation j.1) := by
  simpa [Function.comp_def, rootDerivationBasis_apply] using
    rootDerivationBasis.linearIndependent.comp (fun j : nonzeroIndex => j.1)
      Subtype.val_injective

theorem rootSpace_iSupIndep :
    iSupIndep (fun j : nonzeroIndex => rootSpace j.1) := by
  simpa [rootSpace] using
    rootDerivation_nonzero_linearIndependent.iSupIndep_span_singleton

theorem rootDerivation_bracket_mem_cartan_of_neg
    (i j : nonzeroIndex) (hij : rootWeight j.1 = -rootWeight i.1) :
    ⁅rootDerivation i.1, rootDerivation j.1⁆ ∈ cartanRootSpan := by
  have hX : rootDerivation i.1 ∈ jointEigenspace (rootWeight i.1) := by
    rw [jointEigenspace_eq_span_rootDerivation i.1 (by
      -- Prove i.1 ≠ 6
      intro h
      have h₁ : i.1 = 6 := h
      have h₂ : i.1 ≠ 6 := i.2.1
      exact h₂ h₁) (by
      -- Prove i.1 ≠ 13
      intro h
      have h₁ : i.1 = 13 := h
      have h₂ : i.1 ≠ 13 := i.2.2
      exact h₂ h₁)]
    exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩

  have hY : rootDerivation j.1 ∈ jointEigenspace (rootWeight j.1) := by
    rw [jointEigenspace_eq_span_rootDerivation j.1 (by
      -- Prove j.1 ≠ 6
      intro h
      have h₁ : j.1 = 6 := h
      have h₂ : j.1 ≠ 6 := j.2.1
      exact h₂ h₁) (by
      -- Prove j.1 ≠ 13
      intro h
      have h₁ : j.1 = 13 := h
      have h₂ : j.1 ≠ 13 := j.2.2
      exact h₂ h₁)]
    exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩

  have hmem : ⁅rootDerivation i.1, rootDerivation j.1⁆ ∈ jointEigenspace (rootWeight i.1 + rootWeight j.1) := by
    apply lie_mem_jointEigenspace_add (rootWeight i.1) (rootWeight j.1) hX hY

  rw [hij, add_neg_cancel] at hmem
  exact jointEigenspace_zero_eq_cartanRootSpan ▸ hmem

theorem rootSpaceSum_finrank : Module.finrank ℝ rootSpaceSum = 12 := by
  letI : FiniteDimensional ℝ Der :=
    FiniteDimensional.of_fintype_basis rootDerivationBasis
  have hdim := Submodule.finrank_add_eq_of_isCompl
    cartanRootSpan_isComplement_rootSpaceSum
  rw [cartanRootSpan_finrank,
    CanonicalZornDerivationDimension.finrank_canonicalZornDerivations] at hdim
  linarith

theorem derivation_cartan_rootSpace_two_add_twelve :
    Module.finrank ℝ cartanRootSpan = 2 ∧
      Module.finrank ℝ rootSpaceSum = 12 := by
  exact ⟨cartanRootSpan_finrank, rootSpaceSum_finrank⟩

theorem derivation_cartan_rootSpace_finrank_add :
    Module.finrank ℝ cartanRootSpan + Module.finrank ℝ rootSpaceSum = 14 := by
  rw [cartanRootSpan_finrank, rootSpaceSum_finrank]

end InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
