import InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum

/-!
# Native fourteen-channel Cartan decomposition

This owner consumes the generic joint-eigenspace calculus and computes the
concrete fourteen-dimensional spectrum from the existing parameter equivalence.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

open InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum
open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

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
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨6, rfl⟩
    · exact ⟨10, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨9, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨11, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨12, rfl⟩

theorem rootWeight_range_neg_closed :
    {w : Weight | ∃ v ∈ Set.range rootWeight, w = -v} =
      Set.range rootWeight := by
  rw [rootWeight_range_eq_zero_union_short_long]
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    simp only [Set.mem_union, Set.mem_singleton_iff] at hv
    rcases hv with rfl | hv
    · simp
    · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [shortRootWeights, longRootWeights]
  · intro hw
    rw [rootWeight_range_eq_zero_union_short_long] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact ⟨0, by simp [rootWeight_range_eq_zero_union_short_long]⟩
      | exact ⟨coordWeight 0, by simp [shortRootWeights], by simp⟩
      | exact ⟨-coordWeight 0, by simp [shortRootWeights], by simp⟩
      | exact ⟨coordWeight 1, by simp [shortRootWeights], by simp⟩
      | exact ⟨-coordWeight 1, by simp [shortRootWeights], by simp⟩
      | exact ⟨coordWeight 2, by simp [shortRootWeights], by simp⟩
      | exact ⟨-coordWeight 2, by simp [shortRootWeights], by simp⟩

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
    simp [rootWeight, coordWeight, adCartanDiagonalCoefficient] <;>
    linarith

set_option maxHeartbeats 20000000 in
theorem adCartanCoordinates_parameterUnit (k : TracelessWeight) (j : Fin 14) :
    adCartanCoordinates k (parameterUnit j) =
      (rootWeight j k) • parameterUnit j := by
  fin_cases j <;> funext i <;> fin_cases i <;>
    simp [adCartanCoordinates, adCartan, parameterUnit, rootWeight, coordWeight,
      canonicalParameterLinearEquiv, parameterLinearEquiv,
      parameterAction, parameterDerivation, derivationParameters,
      vectorCanonicalLinearEquiv, canonicalToVectorDerivation,
      vectorToCanonicalDerivation, vectorToCanonicalEnd,
      axialCartanDerivationLinear, axialCartanDerivation,
      Algebra.ZornVectorMatrix.E22, Algebra.ZornVectorMatrix.U,
      Algebra.ZornVectorMatrix.V, Algebra.ZornVec3.basis] <;>
    ring

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
  simp [parameterUnit]

theorem adCartan_rootDerivation (k : TracelessWeight) (j : Fin 14) :
    adCartan k (rootDerivation j) =
      (rootWeight j k) • rootDerivation j := by
  apply canonicalParameterLinearEquiv.injective
  change adCartanCoordinates k (parameterUnit j) = _
  rw [adCartanCoordinates_parameterUnit]
  rfl

theorem parameterUnit_ne_zero (j : Fin 14) : parameterUnit j ≠ 0 := by
  intro h
  have hj := congrFun h j
  simp [parameterUnit] at hj

theorem rootDerivation_ne_zero (j : Fin 14) : rootDerivation j ≠ 0 := by
  intro h
  apply parameterUnit_ne_zero j
  apply canonicalParameterLinearEquiv.injective
  simpa [rootDerivation] using h

theorem rootDerivationBasis_is_simultaneous_eigenbasis :
    ∀ j k, adCartan k (rootDerivationBasis j) =
      (rootWeight j k) • rootDerivationBasis j := by
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
    · exact LinearMap.zero_apply _
    · exact LinearMap.zero_apply _

def shortRootIndices : Finset (Fin 14) := {0, 3, 4, 8, 9, 10}

def longRootIndices : Finset (Fin 14) := {1, 2, 5, 7, 11, 12}

theorem shortRootIndices_card : shortRootIndices.card = 6 := by
  native_decide

theorem longRootIndices_card : longRootIndices.card = 6 := by
  native_decide

theorem rootWeight_short_indices_nonzero (j : Fin 14)
    (hj : j ∈ shortRootIndices) : rootWeight j ≠ 0 := by
  fin_cases j <;> simp [shortRootIndices, rootWeight_ne_zero_of_ne_zero_indices]

theorem rootWeight_long_indices_nonzero (j : Fin 14)
    (hj : j ∈ longRootIndices) : rootWeight j ≠ 0 := by
  fin_cases j <;> simp [longRootIndices, rootWeight_ne_zero_of_ne_zero_indices]

set_option maxHeartbeats 20000000 in
theorem adCartanWeight_separates_nonzero_indices
    (i j : Fin 14) (hij : i ≠ j) (h6 : j ≠ 6) (h13 : j ≠ 13) :
    ∃ k : TracelessWeight,
      adCartanDiagonalCoefficient k i ≠ rootWeight j k := by
  fin_cases i <;> fin_cases j <;>
    simp_all [rootWeight, coordWeight, adCartanDiagonalCoefficient,
      cartanBasis, tracelessWeightEquiv] <;>
    first
    | exact ⟨cartanBasis 0, by
        simp [rootWeight, coordWeight, adCartanDiagonalCoefficient,
          cartanBasis, tracelessWeightEquiv, weightSum, Fin.sum_univ_three]
        norm_num⟩
    | exact ⟨cartanBasis 1, by
        simp [rootWeight, coordWeight, adCartanDiagonalCoefficient,
          cartanBasis, tracelessWeightEquiv, weightSum, Fin.sum_univ_three]
        norm_num⟩

theorem jointEigenspace_eq_span_rootDerivation
    (j : Fin 14) (h6 : j ≠ 6) (h13 : j ≠ 13) :
    jointEigenspace (rootWeight j) = ℝ ∙ rootDerivation j := by
  apply le_antisymm
  · intro D hD
    let p : Params := canonicalParameterLinearEquiv.symm D
    have hp (k : TracelessWeight) :
        adCartanCoordinates k p = (rootWeight j k) • p := by
      simpa [p, adCartanCoordinates] using
        congrArg canonicalParameterLinearEquiv.symm (hD k)
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
    have hDform : D = p j • rootDerivation j := by
      apply canonicalParameterLinearEquiv.injective
      change p = _
      simpa [p, rootDerivation, hpform]
    rw [hDform]
    exact Submodule.mem_span_singleton.mpr ⟨p j, rfl⟩
  · intro D hD
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hD
    change adCartan _ (c • rootDerivation j) = _
    rw [(adCartan _).map_smul, adCartan_rootDerivation]
    rw [smul_eq_mul]
    module

def cartanRootSpan : Submodule ℝ Der :=
  Submodule.span ℝ ({rootDerivation 6, rootDerivation 13} : Set Der)

theorem jointEigenspace_zero_eq_cartanRootSpan :
    jointEigenspace 0 = cartanRootSpan := by
  apply le_antisymm
  · intro D hD
    let p : Params := canonicalParameterLinearEquiv.symm D
    have hp (k : TracelessWeight) :
        adCartanCoordinates k p = (0 : Weight) k • p := by
      simpa [p, adCartanCoordinates] using
        congrArg canonicalParameterLinearEquiv.symm (hD k)
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
      apply canonicalParameterLinearEquiv.injective
      change p = _
      simpa [p, rootDerivation, hpform]
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
    · rw [mem_jointEigenspace_iff]
      intro k
      rw [adCartan_rootDerivation, rootWeight_zero_6]
      exact (Module.zero_smul _).symm
    · rw [mem_jointEigenspace_iff]
      intro k
      rw [adCartan_rootDerivation, rootWeight_zero_13]
      exact (Module.zero_smul _).symm

theorem cartanRootSpan_finrank : Module.finrank ℝ cartanRootSpan = 2 := by
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
  exact rootWeight_eq_adCartanDiagonalCoefficient k j.1

def rootSpace (j : Fin 14) : Submodule ℝ Der :=
  ℝ ∙ rootDerivation j

def rootSpaceSum : Submodule ℝ Der :=
  ⨆ j : nonzeroIndex, rootSpace j.1

theorem rootSpaceSum_mem (j : nonzeroIndex) :
    rootDerivation j.1 ∈ rootSpaceSum := by
  exact le_iSup (fun j : nonzeroIndex => rootSpace j.1) j
    (Submodule.mem_span_singleton.mpr ⟨1, by simp⟩)

theorem cartanRootSpan_sup_rootSpaceSum_eq_top :
    cartanRootSpan ⊔ rootSpaceSum = ⊤ := by
  apply top_unique
  rw [← rootDerivationBasis_span]
  apply Submodule.span_le.2
  intro x hx
  obtain ⟨j, rfl⟩ := hx
  fin_cases j
  all_goals
    first
    | exact Submodule.mem_sup_left
        (jointEigenspace_zero_eq_cartanRootSpan ▸
          cartan_mem_jointEigenspace_zero (tracelessWeightEquiv (Pi.single 0 1)))
    | exact Submodule.mem_sup_left
        (jointEigenspace_zero_eq_cartanRootSpan ▸
          cartan_mem_jointEigenspace_zero (tracelessWeightEquiv (Pi.single 0 1)))
    | exact Submodule.mem_sup_right
        (rootSpaceSum_mem ⟨_, by simp, by simp⟩)

theorem jointEigenspace_zero_coordinate
    {D : Der} (hD : D ∈ jointEigenspace 0) (i : Fin 14)
    (hi6 : i ≠ 6) (hi13 : i ≠ 13) :
    (canonicalParameterLinearEquiv.symm D) i = 0 := by
  let p : Params := canonicalParameterLinearEquiv.symm D
  have hp (k : TracelessWeight) :
      adCartanCoordinates k p = (0 : Weight) k • p := by
    simpa [p, adCartanCoordinates] using
      congrArg canonicalParameterLinearEquiv.symm (hD k)
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
    (fun j : nonzeroIndex => rootSpace j.1) hD ?_ ?_ ?_
  · intro j x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    constructor <;>
      simp [rootDerivation, parameterUnit, canonicalParameterLinearEquiv]
  · exact ⟨by simp, by simp⟩
  · intro x y hx hy
    constructor
    · simpa using congrArg (fun z : Der =>
        (canonicalParameterLinearEquiv.symm z) 6) (add_zero x y)
    · simpa using congrArg (fun z : Der =>
        (canonicalParameterLinearEquiv.symm z) 13) (add_zero x y)

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
    fin_cases i <;>
      simp_all [hnonzero, canonicalParameterLinearEquiv]
  apply canonicalParameterLinearEquiv.injective
  simpa using hpzero

theorem cartanRootSpan_inf_rootSpaceSum_eq_bot :
    cartanRootSpan ⊓ rootSpaceSum = ⊥ :=
  (disjoint_iff.mp cartanRootSpan_disjoint_rootSpaceSum)

theorem cartanRootSpan_isComplement_rootSpaceSum :
    IsCompl cartanRootSpan rootSpaceSum := by
  constructor
  · exact cartanRootSpan_inf_rootSpaceSum_eq_bot
  · exact sup_eq_top_iff.mpr cartanRootSpan_sup_rootSpaceSum_eq_top

theorem nonzeroIndex_card : Fintype.card nonzeroIndex = 12 := by
  native_decide

theorem rootSpace_eq_jointEigenspace (j : nonzeroIndex) :
    rootSpace j.1 = jointEigenspace (rootWeight j.1) := by
  exact (jointEigenspace_eq_span_rootDerivation j.1 j.2.1 j.2.2).symm

theorem rootSpace_finrank (j : nonzeroIndex) :
    Module.finrank ℝ (rootSpace j.1) = 1 := by
  exact finrank_span_singleton (rootDerivation_ne_zero j.1)

theorem rootDerivation_nonzero_linearIndependent :
    LinearIndependent ℝ (fun j : nonzeroIndex => rootDerivation j.1) := by
  simpa only [rootDerivationBasis_apply] using
    rootDerivationBasis.linearIndependent.comp (fun j : nonzeroIndex => j.1)
      Subtype.val_injective

theorem rootSpace_iSupIndep :
    iSupIndep (fun j : nonzeroIndex => rootSpace j.1) := by
  simpa [rootSpace] using
    rootDerivation_nonzero_linearIndependent.iSupIndep_span_singleton

def rootSpaceOnSum (j : nonzeroIndex) : Submodule ℝ rootSpaceSum :=
  (rootSpace j.1).comap rootSpaceSum.subtype

theorem rootSpaceOnSum_isInternal :
    DirectSum.IsInternal rootSpaceOnSum := by
  simpa [rootSpaceOnSum, rootSpaceSum] using
    DirectSum.isInternal_biSup_submodule_of_iSupIndep
      (A := fun j : nonzeroIndex => rootSpace j.1)
      (s := (Set.univ : Set nonzeroIndex)) rootSpace_iSupIndep

theorem rootDerivation_bracket_mem_cartan_of_neg
    (i j : nonzeroIndex) (hij : rootWeight j.1 = -rootWeight i.1) :
    ⁅rootDerivation i.1, rootDerivation j.1⁆ ∈ cartanRootSpan := by
  have hmem :
      ⁅rootDerivation i.1, rootDerivation j.1⁆ ∈
        jointEigenspace (rootWeight i.1 + rootWeight j.1) := by
    exact lie_mem_jointEigenspace_add
      (adCartan_rootDerivation i.1) (adCartan_rootDerivation j.1)
  rw [hij, add_neg_cancel] at hmem
  exact jointEigenspace_zero_eq_cartanRootSpan ▸ hmem

theorem rootSpaceSum_finrank : Module.finrank ℝ rootSpaceSum = 12 := by
  have hdim := Submodule.finrank_add_eq_of_isCompl
    cartanRootSpan_isComplement_rootSpaceSum
  rw [cartanRootSpan_finrank, canonical_derivation_finrank] at hdim
  linarith

theorem derivation_cartan_rootSpace_two_add_twelve :
    Module.finrank ℝ cartanRootSpan = 2 ∧
      Module.finrank ℝ rootSpaceSum = 12 := by
  exact ⟨cartanRootSpan_finrank, rootSpaceSum_finrank⟩

theorem derivation_cartan_rootSpace_finrank_add :
    Module.finrank ℝ cartanRootSpan + Module.finrank ℝ rootSpaceSum = 14 := by
  rw [cartanRootSpan_finrank, rootSpaceSum_finrank]

/-! ## Native Euclidean calibration of the two root lengths

The traceless Cartan plane is represented inside `ℝ³` with the standard
Euclidean quadratic form.  These representatives record the concrete
short/long length ratio without asserting a Weyl-group structure. -/

def shortRootRepresentative : Fin 3 → ℝ :=
  ![2 / 3, -(1 / 3), -(1 / 3)]

def longRootRepresentative : Fin 3 → ℝ :=
  ![-1, 1, 0]

def euclideanNormSq (v : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, v i * v i

theorem shortRootRepresentative_sum_zero :
    ∑ i : Fin 3, shortRootRepresentative i = 0 := by
  simp [shortRootRepresentative, Fin.sum_univ_three]

theorem longRootRepresentative_sum_zero :
    ∑ i : Fin 3, longRootRepresentative i = 0 := by
  simp [longRootRepresentative, Fin.sum_univ_three]

theorem shortRootRepresentative_normSq :
    euclideanNormSq shortRootRepresentative = (2 / 3 : ℝ) := by
  simp [euclideanNormSq, shortRootRepresentative, Fin.sum_univ_three]
  norm_num

theorem longRootRepresentative_normSq :
    euclideanNormSq longRootRepresentative = (2 : ℝ) := by
  simp [euclideanNormSq, longRootRepresentative, Fin.sum_univ_three]
  norm_num

theorem long_short_normSq_ratio :
    euclideanNormSq longRootRepresentative =
      3 * euclideanNormSq shortRootRepresentative := by
  rw [longRootRepresentative_normSq, shortRootRepresentative_normSq]
  norm_num

def euclideanInner (v w : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, v i * w i

theorem shortRootRepresentative_longRootRepresentative_inner :
    euclideanInner shortRootRepresentative longRootRepresentative = -1 := by
  simp [euclideanInner, shortRootRepresentative, longRootRepresentative,
    Fin.sum_univ_three]
  norm_num

def nativeCartanPairing (v w : Fin 3 → ℝ) : ℝ :=
  2 * euclideanInner v w / euclideanNormSq v

theorem nativeCartanPairing_short_long :
    nativeCartanPairing shortRootRepresentative longRootRepresentative = -3 := by
  rw [nativeCartanPairing,
    shortRootRepresentative_longRootRepresentative_inner,
    shortRootRepresentative_normSq]
  norm_num

theorem nativeCartanPairing_long_short :
    nativeCartanPairing longRootRepresentative shortRootRepresentative = -1 := by
  rw [nativeCartanPairing, euclideanInner, shortRootRepresentative,
    longRootRepresentative, Fin.sum_univ_three,
    longRootRepresentative_normSq]
  norm_num

/-! Concrete simple reflections for the calibrated Cartan plane.  These are
linear maps on the ambient `ℝ³` coordinate model; their restriction to the
traceless plane is the finite Coxeter shadow associated with the two calibrated
root representatives. -/

def shortRootReflection : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![
    (-1 / 3) * x 0 + (2 / 3) * x 1 + (2 / 3) * x 2,
    (2 / 3) * x 0 + (2 / 3) * x 1 + (-1 / 3) * x 2,
    (2 / 3) * x 0 + (-1 / 3) * x 1 + (2 / 3) * x 2]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp <;> ring

def longRootReflection : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![x 1, x 0, x 2]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

theorem shortRootReflection_preserves_euclideanNormSq (x : Fin 3 → ℝ) :
    euclideanNormSq (shortRootReflection x) = euclideanNormSq x := by
  simp [euclideanNormSq, shortRootReflection, Fin.sum_univ_three]
  ring

theorem longRootReflection_preserves_euclideanNormSq (x : Fin 3 → ℝ) :
    euclideanNormSq (longRootReflection x) = euclideanNormSq x := by
  simp [euclideanNormSq, longRootReflection, Fin.sum_univ_three]

theorem shortRootReflection_shortRootRepresentative :
    shortRootReflection shortRootRepresentative = -shortRootRepresentative := by
  funext i
  fin_cases i <;>
    simp [shortRootReflection, shortRootRepresentative]
  <;> norm_num

theorem longRootReflection_longRootRepresentative :
    longRootReflection longRootRepresentative = -longRootRepresentative := by
  funext i
  fin_cases i <;>
    simp [longRootReflection, longRootRepresentative]

theorem shortRootReflection_formula (x : Fin 3 → ℝ) :
    shortRootReflection x =
      x - nativeCartanPairing shortRootRepresentative x •
        shortRootRepresentative := by
  funext i
  fin_cases i <;>
    simp [shortRootReflection, nativeCartanPairing, euclideanInner,
      shortRootRepresentative, euclideanNormSq, Fin.sum_univ_three]
  <;> ring

theorem longRootReflection_formula (x : Fin 3 → ℝ) :
    longRootReflection x =
      x - nativeCartanPairing longRootRepresentative x •
        longRootRepresentative := by
  funext i
  fin_cases i <;>
    simp [longRootReflection, nativeCartanPairing, euclideanInner,
      longRootRepresentative, euclideanNormSq, Fin.sum_univ_three]
  <;> ring

theorem shortRootReflection_preserves_traceless (k : TracelessWeight) :
    ∑ i : Fin 3, shortRootReflection k.1 i = 0 := by
  have h := k.2
  simp [shortRootReflection, Fin.sum_univ_three] at *
  linarith

theorem longRootReflection_preserves_traceless (k : TracelessWeight) :
    ∑ i : Fin 3, longRootReflection k.1 i = 0 := by
  have h := k.2
  simp [longRootReflection, Fin.sum_univ_three] at *
  linarith

/-! The calibrated reflections therefore act on the native traceless Cartan
plane itself, not only on its ambient `ℝ³` coordinate model. -/
def shortRootReflectionOnCartan : TracelessWeight →ₗ[ℝ] TracelessWeight where
  toFun k := ⟨shortRootReflection k.1, shortRootReflection_preserves_traceless k⟩
  map_add' k l := by
    apply Subtype.ext
    simp [shortRootReflection]
  map_smul' a k := by
    apply Subtype.ext
    simp [shortRootReflection]

def longRootReflectionOnCartan : TracelessWeight →ₗ[ℝ] TracelessWeight where
  toFun k := ⟨longRootReflection k.1, longRootReflection_preserves_traceless k⟩
  map_add' k l := by
    apply Subtype.ext
    simp [longRootReflection]
  map_smul' a k := by
    apply Subtype.ext
    simp [longRootReflection]

def cartanWeightPullback
    (s : TracelessWeight →ₗ[ℝ] TracelessWeight) (α : Weight) : Weight :=
  α.comp s

@[simp] theorem cartanWeightPullback_apply
    (s : TracelessWeight →ₗ[ℝ] TracelessWeight) (α : Weight)
    (k : TracelessWeight) :
    cartanWeightPullback s α k = α (s k) := rfl

theorem shortRootReflectionOnCartan_coordWeight (i : Fin 3) :
    cartanWeightPullback shortRootReflectionOnCartan (coordWeight i) =
      match i with
      | 0 => -coordWeight 0
      | 1 => -coordWeight 2
      | 2 => -coordWeight 1 := by
  fin_cases i
  · apply LinearMap.ext
    intro k
    have h := k.2
    simp [cartanWeightPullback, shortRootReflectionOnCartan,
      shortRootReflection, coordWeight, Fin.sum_univ_three] at *
    linarith
  · apply LinearMap.ext
    intro k
    have h := k.2
    simp [cartanWeightPullback, shortRootReflectionOnCartan,
      shortRootReflection, coordWeight, Fin.sum_univ_three] at *
    linarith
  · apply LinearMap.ext
    intro k
    have h := k.2
    simp [cartanWeightPullback, shortRootReflectionOnCartan,
      shortRootReflection, coordWeight, Fin.sum_univ_three] at *
    linarith

theorem longRootReflectionOnCartan_coordWeight (i : Fin 3) :
    cartanWeightPullback longRootReflectionOnCartan (coordWeight i) =
      match i with
      | 0 => coordWeight 1
      | 1 => coordWeight 0
      | 2 => coordWeight 2 := by
  fin_cases i <;>
    apply LinearMap.ext <;> intro k <;>
    simp [cartanWeightPullback, longRootReflectionOnCartan,
      longRootReflection, coordWeight]

/-! The calibrated reflections preserve the corresponding crystallographic
weight hexagons.  These are concrete set-stability statements for the native
functionals; they do not yet package a generated Weyl-group object. -/

theorem shortRootReflection_mapsTo_shortRootWeights :
    Set.MapsTo (cartanWeightPullback shortRootReflectionOnCartan)
      shortRootWeights shortRootWeights := by
  intro α hα
  simp only [shortRootWeights, Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [shortRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_neg, shortRootReflectionOnCartan_coordWeight]
    simp
  · rw [shortRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_neg, shortRootReflectionOnCartan_coordWeight]
    simp
  · rw [shortRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_neg, shortRootReflectionOnCartan_coordWeight]
    simp

theorem longRootReflection_mapsTo_longRootWeights :
    Set.MapsTo (cartanWeightPullback longRootReflectionOnCartan)
      longRootWeights longRootWeights := by
  intro α hα
  simp only [longRootWeights, Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [map_sub, longRootReflectionOnCartan_coordWeight,
      longRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_sub, longRootReflectionOnCartan_coordWeight,
      longRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_sub, longRootReflectionOnCartan_coordWeight,
      longRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_sub, longRootReflectionOnCartan_coordWeight,
      longRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_sub, longRootReflectionOnCartan_coordWeight,
      longRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_sub, longRootReflectionOnCartan_coordWeight,
      longRootReflectionOnCartan_coordWeight]
    simp

theorem shortRootReflection_mapsTo_longRootWeights :
    Set.MapsTo (cartanWeightPullback shortRootReflectionOnCartan)
      longRootWeights longRootWeights := by
  intro α hα
  simp only [longRootWeights, Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [map_sub, shortRootReflectionOnCartan_coordWeight,
      shortRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_sub, shortRootReflectionOnCartan_coordWeight,
      shortRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_sub, shortRootReflectionOnCartan_coordWeight,
      shortRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_sub, shortRootReflectionOnCartan_coordWeight,
      shortRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_sub, shortRootReflectionOnCartan_coordWeight,
      shortRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_sub, shortRootReflectionOnCartan_coordWeight,
      shortRootReflectionOnCartan_coordWeight]
    simp

theorem longRootReflection_mapsTo_shortRootWeights :
    Set.MapsTo (cartanWeightPullback longRootReflectionOnCartan)
      shortRootWeights shortRootWeights := by
  intro α hα
  simp only [shortRootWeights, Set.mem_insert_iff, Set.mem_singleton_iff] at hα ⊢
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [longRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_neg, longRootReflectionOnCartan_coordWeight]
    simp
  · rw [longRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_neg, longRootReflectionOnCartan_coordWeight]
    simp
  · rw [longRootReflectionOnCartan_coordWeight]
    simp
  · rw [map_neg, longRootReflectionOnCartan_coordWeight]
    simp

theorem shortRootReflection_sq :
    shortRootReflection.comp shortRootReflection = LinearMap.id := by
  ext x i
  fin_cases i <;>
    simp [shortRootReflection, LinearMap.comp_apply] <;>
    ring

theorem longRootReflection_sq :
    longRootReflection.comp longRootReflection = LinearMap.id := by
  ext x i
  fin_cases i <;>
    simp [longRootReflection, LinearMap.comp_apply]

theorem nativeCartanReflections_braid :
    (shortRootReflection.comp longRootReflection) ^ 3 =
      (longRootReflection.comp shortRootReflection) ^ 3 := by
  ext x i
  fin_cases i <;>
    simp [shortRootReflection, longRootReflection,
      LinearMap.comp_apply, pow_succ] <;>
    ring

theorem shortRootReflectionOnCartan_sq :
    shortRootReflectionOnCartan.comp shortRootReflectionOnCartan = LinearMap.id := by
  apply LinearMap.ext
  intro k
  apply Subtype.ext
  have h := congrArg (fun f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) => f k.1)
    shortRootReflection_sq
  simpa [shortRootReflectionOnCartan, LinearMap.comp_apply] using h

theorem longRootReflectionOnCartan_sq :
    longRootReflectionOnCartan.comp longRootReflectionOnCartan = LinearMap.id := by
  apply LinearMap.ext
  intro k
  apply Subtype.ext
  have h := congrArg (fun f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) => f k.1)
    longRootReflection_sq
  simpa [longRootReflectionOnCartan, LinearMap.comp_apply] using h

theorem nativeCartanReflectionsOnCartan_braid :
    (shortRootReflectionOnCartan.comp longRootReflectionOnCartan) ^ 3 =
      (longRootReflectionOnCartan.comp shortRootReflectionOnCartan) ^ 3 := by
  apply LinearMap.ext
  intro k
  apply Subtype.ext
  have h := congrArg (fun f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) => f k.1)
    nativeCartanReflections_braid
  simpa [shortRootReflectionOnCartan, longRootReflectionOnCartan,
    LinearMap.comp_apply, pow_succ] using h


end InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
