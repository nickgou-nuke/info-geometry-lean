import InfoGeometry.Lie.CanonicalZornMathlibBridge
import InfoGeometry.Lie.CanonicalZornG2LiteratureBridge
import InfoGeometry.Lie.CanonicalZornIsKilling
import Mathlib.LinearAlgebra.RootSystem.Finite.G2

/-!
# Native root-index comparison

The explicit Zorn weights are function-valued because they are used by the
adjoint root-space API.  Mathlib's root finset stores `LieModule.Weight`
objects, which additionally carry the proof that the corresponding generalized
weight space is nontrivial.  This file supplies exactly that package and the
resulting index equivalence; coroots remain downstream.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornRootSystemComparison

open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornMathlibBridge
open InfoGeometry.Lie.CanonicalZornRootPairing
open InfoGeometry.Lie.CanonicalZornG2LiteratureBridge
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

abbrev Der := CanonicalZornCartanAdjointRootDecomposition.Der
abbrev Cartan := axialCartanLieSubalgebra
abbrev RootIndex := ↥(LieSubalgebra.root (K := ℝ) (L := Der) (H := Cartan))

theorem native_rootDerivation_span_eq_top :
    Submodule.span ℝ (Set.range (rootDerivation : Fin 14 → Der)) = ⊤ := by
  have hrange : Set.range (rootDerivation : Fin 14 → Der) =
      Set.range (rootDerivationBasis : Fin 14 → Der) := by
    ext X
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rootDerivationBasis_apply i⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, (rootDerivationBasis_apply i).symm⟩
  rw [hrange]
  exact rootDerivationBasis.span_eq

def nativeRootWeightMathlib (i : nonzeroIndex) :
    LieModule.Weight ℝ Cartan Der :=
  { toFun := nativeRootWeight i
    genWeightSpace_ne_bot' := by
      intro hbot
      have hmem := rootDerivation_mem_rootSpace i
      change rootDerivation i.1 ∈ LieModule.genWeightSpace Der
        (nativeRootWeight i) at hmem
      rw [hbot] at hmem
      exact rootDerivation_ne_zero i.1 (by simpa using hmem) }

def nativeRootIndex (i : nonzeroIndex) : RootIndex :=
  ⟨nativeRootWeightMathlib i, by
    letI : IsNoetherian ℝ Der := IsNoetherian.iff_fg.mpr inferInstance
    have hne : (nativeRootWeight i : Cartan → ℝ) ≠ 0 := by
      intro hzero
      have hroot : rootWeight i.1 ≠ 0 :=
        rootWeight_ne_zero_of_ne_zero_indices i.1 i.2.1 i.2.2
      apply hroot
      apply LinearMap.ext
      intro k
      have hz := congrFun hzero (axialCartanLieEquiv k)
      simpa [nativeRootWeight] using hz
    have hne' : (nativeRootWeightMathlib i).IsNonZero := by exact hne
    rw [LieSubalgebra.root]
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hne'⟩

@[simp] theorem nativeRootIndex_value (i : nonzeroIndex) :
    (nativeRootIndex i).1 = nativeRootWeightMathlib i := rfl

theorem nativeRootIndex_injective :
    Function.Injective nativeRootIndex := by
  intro i j hij
  by_contra hne
  apply rootWeight_injective_on_nonzero i j hne
  have h := congrArg (fun x : RootIndex => x.1) hij
  apply LinearMap.ext
  intro k
  have hval := congrArg
    (fun w : LieModule.Weight ℝ Cartan Der => w.toFun (axialCartanLieEquiv k)) h
  simpa [nativeRootWeightMathlib, nativeRootWeight] using hval

theorem root_eq_nativeRootIndex (α : RootIndex) :
    ∃ i : nonzeroIndex, nativeRootIndex i = α := by
  letI : IsNoetherian ℝ Der := isNoetherian_of_isNoetherianRing_of_finite ℝ Der
  have hα := α.2
  simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and] at hα
  obtain ⟨i, hi⟩ := mathlib_nonzero_weight_eq_nativeRootWeight α.1 hα
  refine ⟨i, Subtype.ext ?_⟩
  apply LieModule.Weight.ext
  intro x
  exact (congrFun hi.symm x).symm

theorem nativeRootIndex_surjective :
    Function.Surjective nativeRootIndex := by
  intro α
  exact root_eq_nativeRootIndex α

def nativeShortSimpleIndex : nonzeroIndex := ⟨10, by decide, by decide⟩
def nativeLongSimpleIndex : nonzeroIndex := ⟨1, by decide, by decide⟩

def simpleWeightOnCartan (i : Fin 2) : Cartan → ℝ :=
  fun x => simpleWeight i (axialCartanLieEquiv.symm x)

theorem nativeShortSimpleWeight_value :
    (nativeRootWeightMathlib nativeShortSimpleIndex).toFun =
      simpleWeightOnCartan 0 := by
  funext x
  simpa [nativeRootWeightMathlib, nativeRootWeight, nativeShortSimpleIndex,
    simpleWeightOnCartan] using
      congrArg (fun f : Weight => f (axialCartanLieEquiv.symm x)) paper_e10_weight

theorem nativeLongSimpleWeight_value :
    (nativeRootWeightMathlib nativeLongSimpleIndex).toFun =
      simpleWeightOnCartan 1 := by
  funext x
  simpa [nativeRootWeightMathlib, nativeRootWeight, nativeLongSimpleIndex,
    simpleWeightOnCartan] using
      congrArg (fun f : Weight => f (axialCartanLieEquiv.symm x)) paper_e01_weight

theorem nativePositiveRootWeight_chain :
    (nativeRootWeightMathlib ⟨9, by decide, by decide⟩).toFun =
        simpleWeightOnCartan 0 + simpleWeightOnCartan 1 ∧
      (nativeRootWeightMathlib ⟨8, by decide, by decide⟩).toFun =
        2 • simpleWeightOnCartan 0 + simpleWeightOnCartan 1 ∧
      (nativeRootWeightMathlib ⟨11, by decide, by decide⟩).toFun =
        3 • simpleWeightOnCartan 0 + simpleWeightOnCartan 1 := by
  rcases paper_positive_root_chain with ⟨_, _, h9, h8, h11, _⟩
  refine ⟨?_, ?_, ?_⟩ <;> funext x
  · simpa [nativeRootWeightMathlib, nativeRootWeight, simpleWeightOnCartan] using
      congrArg (fun f : Weight => f (axialCartanLieEquiv.symm x)) h9
  · simpa [nativeRootWeightMathlib, nativeRootWeight, simpleWeightOnCartan] using
      congrArg (fun f : Weight => f (axialCartanLieEquiv.symm x)) h8
  · simpa [nativeRootWeightMathlib, nativeRootWeight, simpleWeightOnCartan] using
      congrArg (fun f : Weight => f (axialCartanLieEquiv.symm x)) h11

theorem native_highest_root_weight :
    (nativeRootWeightMathlib ⟨12, by decide, by decide⟩).toFun =
      3 • simpleWeightOnCartan 0 + 2 • simpleWeightOnCartan 1 := by
  rcases paper_positive_root_chain with ⟨_, _, _, _, _, h12⟩
  funext x
  simpa [nativeRootWeightMathlib, nativeRootWeight, simpleWeightOnCartan] using
    congrArg (fun f : Weight => f (axialCartanLieEquiv.symm x)) h12

theorem native_root_string_top_nontrivial :
    LieAlgebra.rootSpace Cartan
        (3 • (nativeRootWeightMathlib nativeShortSimpleIndex).toFun +
          (nativeRootWeightMathlib nativeLongSimpleIndex).toFun) ≠ ⊥ := by
  have hchain := (nativePositiveRootWeight_chain).2.2
  have hmem := rootDerivation_mem_rootSpace
    (⟨11, by decide, by decide⟩ : nonzeroIndex)
  change rootDerivation 11 ∈ LieModule.genWeightSpace Der
    (nativeRootWeight ⟨11, by decide, by decide⟩) at hmem
  have hweight : nativeRootWeight ⟨11, by decide, by decide⟩ =
      3 • nativeRootWeight nativeShortSimpleIndex +
        nativeRootWeight nativeLongSimpleIndex := by
        funext x
        simpa [nativeRootWeightMathlib, nativeRootWeight,
          nativeShortSimpleIndex, nativeLongSimpleIndex] using congrFun hchain x
  rw [hweight] at hmem
  intro hbot
  change LieModule.genWeightSpace Der
    (3 • (nativeRootWeightMathlib nativeShortSimpleIndex).toFun +
      (nativeRootWeightMathlib nativeLongSimpleIndex).toFun) = ⊥ at hbot
  have hmem' : rootDerivation 11 ∈ LieModule.genWeightSpace Der
      (3 • (nativeRootWeightMathlib nativeShortSimpleIndex).toFun +
        (nativeRootWeightMathlib nativeLongSimpleIndex).toFun) := by
    simpa [nativeRootWeightMathlib, nativeRootWeight,
      nativeShortSimpleIndex, nativeLongSimpleIndex] using hmem
  rw [hbot] at hmem'
  exact rootDerivation_ne_zero 11 (by simpa using hmem')

private theorem rootWeight_four_short_add_long_not_mem_range :
    4 • rootWeight 10 + rootWeight 1 ∉ Set.range (rootWeight : Fin 14 → Weight) := by
  rintro ⟨j, hj⟩
  have h0 := congrArg (fun w : Weight =>
    w (tracelessWeightEquiv (Pi.single 0 (1 : ℝ)))) hj
  have h1 := congrArg (fun w : Weight =>
    w (tracelessWeightEquiv (Pi.single 1 (1 : ℝ)))) hj
  change rootWeight j (tracelessWeightEquiv (Pi.single 0 (1 : ℝ))) = _ at h0
  change rootWeight j (tracelessWeightEquiv (Pi.single 1 (1 : ℝ))) = _ at h1
  fin_cases j <;>
    simp [rootWeight, coordWeight,
      tracelessWeightEquiv] at h0 h1 <;>
    try norm_num at h0

theorem native_root_string_next_vanishing :
    LieAlgebra.rootSpace Cartan
        (4 • (nativeRootWeightMathlib nativeShortSimpleIndex).toFun +
          (nativeRootWeightMathlib nativeLongSimpleIndex).toFun) = ⊥ := by
  apply mathlib_rootSpace_eq_bot_of_not_native_rootWeight
  intro j hj
  have hEq : rootWeight j = 4 • rootWeight 10 + rootWeight 1 := by
    apply LinearMap.ext
    intro k
    have hh := congrFun hj (axialCartanLieEquiv k)
    simpa [LinearEquiv.symm_apply_apply, nativeRootWeightMathlib,
      nativeRootWeight, nativeShortSimpleIndex, nativeLongSimpleIndex, rootWeight] using hh
  exact rootWeight_four_short_add_long_not_mem_range ⟨j, hEq⟩

local instance canonicalZorn_isNoetherian : IsNoetherian ℝ Der :=
  isNoetherian_of_isNoetherianRing_of_finite ℝ Der

theorem native_short_long_chainTopCoeff :
    LieModule.chainTopCoeff
        (nativeRootWeightMathlib nativeShortSimpleIndex).toFun
        (nativeRootWeightMathlib nativeLongSimpleIndex) = 3 := by
  let α := nativeRootWeightMathlib nativeShortSimpleIndex
  let β := nativeRootWeightMathlib nativeLongSimpleIndex
  have hα : α.IsNonZero := by
    intro hzero
    apply rootWeight_ne_zero_of_ne_zero_indices nativeShortSimpleIndex.1
      nativeShortSimpleIndex.2.1 nativeShortSimpleIndex.2.2
    apply LinearMap.ext
    intro k
    have hz := congrFun hzero (axialCartanLieEquiv k)
    simpa [α, nativeRootWeightMathlib, nativeRootWeight,
      nativeShortSimpleIndex] using hz
  have h3 : (3 : ℤ) ≤ LieModule.chainTopCoeff α.toFun β := by
    exact ((LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff α β hα 3).mp (by
      simpa [α, β] using native_root_string_top_nontrivial)).1
  have h4not : ¬ (4 : ℤ) ≤ LieModule.chainTopCoeff α.toFun β := by
    intro h4
    have hbot : -(4 : ℤ) ≤ (LieModule.chainBotCoeff α.toFun β : ℤ) := by omega
    have hne := (LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff α β hα 4).mpr
      ⟨h4, hbot⟩
    exact hne (by simpa [α, β] using native_root_string_next_vanishing)
  have htop : LieModule.chainTopCoeff α.toFun β < 4 := by
    by_contra h
    apply h4not
    exact_mod_cast (Nat.le_of_not_gt h)
  have h3nat : 3 ≤ LieModule.chainTopCoeff α.toFun β := by
    exact_mod_cast h3
  apply Nat.le_antisymm
  · exact Nat.le_of_lt_succ htop
  · exact h3nat

private theorem rootWeight_long_sub_short_not_mem_range :
    rootWeight 1 - rootWeight 10 ∉ Set.range (rootWeight : Fin 14 → Weight) := by
  rintro ⟨j, hj⟩
  have h0 := congrArg (fun w : Weight =>
    w (tracelessWeightEquiv (Pi.single 0 (1 : ℝ)))) hj
  have h1 := congrArg (fun w : Weight =>
    w (tracelessWeightEquiv (Pi.single 1 (1 : ℝ)))) hj
  change rootWeight j (tracelessWeightEquiv (Pi.single 0 (1 : ℝ))) = _ at h0
  change rootWeight j (tracelessWeightEquiv (Pi.single 1 (1 : ℝ))) = _ at h1
  fin_cases j <;>
    simp [rootWeight, coordWeight, tracelessWeightEquiv] at h0 h1 <;>
    try norm_num at h0 <;> try norm_num at h1

theorem native_short_long_chainBotCoeff :
    LieModule.chainBotCoeff
        (nativeRootWeightMathlib nativeShortSimpleIndex).toFun
        (nativeRootWeightMathlib nativeLongSimpleIndex) = 0 := by
  let α := nativeRootWeightMathlib nativeShortSimpleIndex
  let β := nativeRootWeightMathlib nativeLongSimpleIndex
  have hα : α.IsNonZero := by
    intro hzero
    apply rootWeight_ne_zero_of_ne_zero_indices nativeShortSimpleIndex.1
      nativeShortSimpleIndex.2.1 nativeShortSimpleIndex.2.2
    apply LinearMap.ext
    intro k
    have hz := congrFun hzero (axialCartanLieEquiv k)
    simpa [α, nativeRootWeightMathlib, nativeRootWeight,
      nativeShortSimpleIndex] using hz
  have hneg : LieAlgebra.rootSpace Cartan
      (-(α.toFun) + β.toFun) = ⊥ := by
    apply mathlib_rootSpace_eq_bot_of_not_native_rootWeight
    intro j hj
    have hEq : rootWeight j = rootWeight 1 - rootWeight 10 := by
      apply LinearMap.ext
      intro k
      have hh := congrFun hj (axialCartanLieEquiv k)
      simpa [LinearEquiv.symm_apply_apply, α, β, nativeRootWeightMathlib,
        nativeRootWeight, nativeShortSimpleIndex, nativeLongSimpleIndex,
        rootWeight, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hh
    exact rootWeight_long_sub_short_not_mem_range ⟨j, hEq⟩
  have hnot : ¬ (1 : ℤ) ≤ LieModule.chainBotCoeff α.toFun β := by
    intro h1
    have htop : (-1 : ℤ) ≤ LieModule.chainTopCoeff α.toFun β := by omega
    have hne := (LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff α β hα (-1)).mpr
      ⟨htop, h1⟩
    apply hne
    simpa [α, β, sub_eq_add_neg, add_comm] using hneg
  exact Nat.eq_zero_of_not_pos (by
    simpa [Nat.one_le_iff_ne_zero] using hnot)

abbrev P := InfoGeometry.Lie.CanonicalZornIsKilling.canonicalZornRootSystem

theorem native_short_coroot_on_long_root :
    (P.root (nativeRootIndex nativeLongSimpleIndex))
        (P.coroot (nativeRootIndex nativeShortSimpleIndex)) = -3 := by
  let α := nativeRootWeightMathlib nativeShortSimpleIndex
  let β := nativeRootWeightMathlib nativeLongSimpleIndex
  have h := LieAlgebra.IsKilling.apply_coroot_eq_cast α β
  dsimp [α, β] at h
  have hb : LieModule.chainBotCoeff α.toFun β = 0 := by
    simpa [α, β] using native_short_long_chainBotCoeff
  have ht : LieModule.chainTopCoeff α.toFun β = 3 := by
    simpa [α, β] using native_short_long_chainTopCoeff
  change LieModule.chainBotCoeff (⇑α) β = 0 at hb
  change LieModule.chainTopCoeff (⇑α) β = 3 at ht
  rw [hb, ht] at h
  have h' : β.toFun (LieAlgebra.IsKilling.coroot α) = -3 := by
    simpa [α, β] using h
  simpa [P, α, β, nativeRootIndex_value] using h'

theorem native_long_string_top_nontrivial :
    LieAlgebra.rootSpace Cartan
        ((nativeRootWeightMathlib nativeLongSimpleIndex).toFun +
          (nativeRootWeightMathlib nativeShortSimpleIndex).toFun) ≠ ⊥ := by
  have hchain := (nativePositiveRootWeight_chain).1
  have hmem := rootDerivation_mem_rootSpace
    (⟨9, by decide, by decide⟩ : nonzeroIndex)
  change rootDerivation 9 ∈ LieModule.genWeightSpace Der
    (nativeRootWeight ⟨9, by decide, by decide⟩) at hmem
  have hweight : nativeRootWeight ⟨9, by decide, by decide⟩ =
      nativeRootWeight nativeLongSimpleIndex + nativeRootWeight nativeShortSimpleIndex := by
    funext x
    simpa [nativeRootWeightMathlib, nativeRootWeight,
      nativeShortSimpleIndex, nativeLongSimpleIndex, simpleWeightOnCartan,
      simpleWeight, paper_e01_weight, paper_e10_weight] using congrFun hchain x
  rw [hweight] at hmem
  intro hbot
  change LieModule.genWeightSpace Der
    ((nativeRootWeightMathlib nativeLongSimpleIndex).toFun +
      (nativeRootWeightMathlib nativeShortSimpleIndex).toFun) = ⊥ at hbot
  have hmem' : rootDerivation 9 ∈ LieModule.genWeightSpace Der
      ((nativeRootWeightMathlib nativeLongSimpleIndex).toFun +
        (nativeRootWeightMathlib nativeShortSimpleIndex).toFun) := by
    simpa [nativeRootWeightMathlib, nativeRootWeight,
      nativeShortSimpleIndex, nativeLongSimpleIndex] using hmem
  rw [hbot] at hmem'
  exact rootDerivation_ne_zero 9 (by simpa using hmem')

private theorem rootWeight_two_long_add_short_not_mem_range :
    2 • rootWeight 1 + rootWeight 10 ∉ Set.range (rootWeight : Fin 14 → Weight) := by
  rintro ⟨j, hj⟩
  have h0 := congrArg (fun w : Weight =>
    w (tracelessWeightEquiv (Pi.single 0 (1 : ℝ)))) hj
  have h1 := congrArg (fun w : Weight =>
    w (tracelessWeightEquiv (Pi.single 1 (1 : ℝ)))) hj
  change rootWeight j (tracelessWeightEquiv (Pi.single 0 (1 : ℝ))) = _ at h0
  change rootWeight j (tracelessWeightEquiv (Pi.single 1 (1 : ℝ))) = _ at h1
  fin_cases j <;>
    simp [rootWeight, coordWeight, tracelessWeightEquiv] at h0 h1 <;>
    try norm_num at h0 <;> try norm_num at h1

theorem native_long_string_next_vanishing :
    LieAlgebra.rootSpace Cartan
        (2 • (nativeRootWeightMathlib nativeLongSimpleIndex).toFun +
          (nativeRootWeightMathlib nativeShortSimpleIndex).toFun) = ⊥ := by
  apply mathlib_rootSpace_eq_bot_of_not_native_rootWeight
  intro j hj
  have hEq : rootWeight j = 2 • rootWeight 1 + rootWeight 10 := by
    apply LinearMap.ext
    intro k
    have hh := congrFun hj (axialCartanLieEquiv k)
    simpa [LinearEquiv.symm_apply_apply, nativeRootWeightMathlib,
      nativeRootWeight, nativeShortSimpleIndex, nativeLongSimpleIndex, rootWeight] using hh
  exact rootWeight_two_long_add_short_not_mem_range ⟨j, hEq⟩

theorem native_long_short_chainTopCoeff :
    LieModule.chainTopCoeff
        (nativeRootWeightMathlib nativeLongSimpleIndex).toFun
        (nativeRootWeightMathlib nativeShortSimpleIndex) = 1 := by
  let α := nativeRootWeightMathlib nativeLongSimpleIndex
  let β := nativeRootWeightMathlib nativeShortSimpleIndex
  have hα : α.IsNonZero := by
    intro hzero
    apply rootWeight_ne_zero_of_ne_zero_indices nativeLongSimpleIndex.1
      nativeLongSimpleIndex.2.1 nativeLongSimpleIndex.2.2
    apply LinearMap.ext
    intro k
    have hz := congrFun hzero (axialCartanLieEquiv k)
    simpa [α, nativeRootWeightMathlib, nativeRootWeight,
      nativeLongSimpleIndex] using hz
  have h1 : (1 : ℤ) ≤ LieModule.chainTopCoeff α.toFun β := by
    exact ((LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff α β hα 1).mp (by
      simpa [α, β] using native_long_string_top_nontrivial)).1
  have h2not : ¬ (2 : ℤ) ≤ LieModule.chainTopCoeff α.toFun β := by
    intro h2
    have hbot : -(2 : ℤ) ≤ (LieModule.chainBotCoeff α.toFun β : ℤ) := by omega
    have hne := (LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff α β hα 2).mpr
      ⟨h2, hbot⟩
    exact hne (by simpa [α, β] using native_long_string_next_vanishing)
  have htop : LieModule.chainTopCoeff α.toFun β < 2 := by
    by_contra h
    apply h2not
    exact_mod_cast (Nat.le_of_not_gt h)
  have h1nat : 1 ≤ LieModule.chainTopCoeff α.toFun β := by
    exact_mod_cast h1
  apply Nat.le_antisymm
  · exact Nat.le_of_lt_succ htop
  · exact h1nat

private theorem rootWeight_short_sub_long_not_mem_range :
    rootWeight 10 - rootWeight 1 ∉ Set.range (rootWeight : Fin 14 → Weight) := by
  rintro ⟨j, hj⟩
  have h0 := congrArg (fun w : Weight =>
    w (tracelessWeightEquiv (Pi.single 0 (1 : ℝ)))) hj
  have h1 := congrArg (fun w : Weight =>
    w (tracelessWeightEquiv (Pi.single 1 (1 : ℝ)))) hj
  change rootWeight j (tracelessWeightEquiv (Pi.single 0 (1 : ℝ))) = _ at h0
  change rootWeight j (tracelessWeightEquiv (Pi.single 1 (1 : ℝ))) = _ at h1
  fin_cases j <;>
    simp [rootWeight, coordWeight, tracelessWeightEquiv] at h0 h1 <;>
    try norm_num at h0 <;> try norm_num at h1

theorem native_long_short_chainBotCoeff :
    LieModule.chainBotCoeff
        (nativeRootWeightMathlib nativeLongSimpleIndex).toFun
        (nativeRootWeightMathlib nativeShortSimpleIndex) = 0 := by
  let α := nativeRootWeightMathlib nativeLongSimpleIndex
  let β := nativeRootWeightMathlib nativeShortSimpleIndex
  have hα : α.IsNonZero := by
    intro hzero
    apply rootWeight_ne_zero_of_ne_zero_indices nativeLongSimpleIndex.1
      nativeLongSimpleIndex.2.1 nativeLongSimpleIndex.2.2
    apply LinearMap.ext
    intro k
    have hz := congrFun hzero (axialCartanLieEquiv k)
    simpa [α, nativeRootWeightMathlib, nativeRootWeight,
      nativeLongSimpleIndex] using hz
  have hneg : LieAlgebra.rootSpace Cartan (-α.toFun + β.toFun) = ⊥ := by
    apply mathlib_rootSpace_eq_bot_of_not_native_rootWeight
    intro j hj
    have hEq : rootWeight j = rootWeight 10 - rootWeight 1 := by
      apply LinearMap.ext
      intro k
      have hh := congrFun hj (axialCartanLieEquiv k)
      simpa [LinearEquiv.symm_apply_apply, α, β, nativeRootWeightMathlib,
        nativeRootWeight, nativeShortSimpleIndex, nativeLongSimpleIndex,
        rootWeight, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hh
    exact rootWeight_short_sub_long_not_mem_range ⟨j, hEq⟩
  have hnot : ¬ (1 : ℤ) ≤ LieModule.chainBotCoeff α.toFun β := by
    intro h1
    have htop : (-1 : ℤ) ≤ LieModule.chainTopCoeff α.toFun β := by omega
    have hne := (LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff α β hα (-1)).mpr
      ⟨htop, h1⟩
    apply hne
    simpa [α, β, sub_eq_add_neg, add_comm] using hneg
  exact Nat.eq_zero_of_not_pos (by
    simpa [Nat.one_le_iff_ne_zero] using hnot)

theorem native_long_coroot_on_short_root :
    (P.root (nativeRootIndex nativeShortSimpleIndex))
        (P.coroot (nativeRootIndex nativeLongSimpleIndex)) = -1 := by
  let α := nativeRootWeightMathlib nativeLongSimpleIndex
  let β := nativeRootWeightMathlib nativeShortSimpleIndex
  have h := LieAlgebra.IsKilling.apply_coroot_eq_cast α β
  dsimp [α, β] at h
  have hb : LieModule.chainBotCoeff α.toFun β = 0 := by
    simpa [α, β] using native_long_short_chainBotCoeff
  have ht : LieModule.chainTopCoeff α.toFun β = 1 := by
    simpa [α, β] using native_long_short_chainTopCoeff
  change LieModule.chainBotCoeff (⇑α) β = 0 at hb
  change LieModule.chainTopCoeff (⇑α) β = 1 at ht
  rw [hb, ht] at h
  have h' : β.toFun (LieAlgebra.IsKilling.coroot α) = -1 := by
    simpa [α, β] using h
  simpa [P, α, β, nativeRootIndex_value] using h'

/-! The calibrated simple roots instantiate Mathlib's native embedded-G₂ API. -/
noncomputable def nativeEmbeddedG2 : P.EmbeddedG2 := by
  letI : LieSubalgebra.IsCartanSubalgebra (Cartan : LieSubalgebra ℝ Der) :=
    axialCartan_isCartanSubalgebra
  letI : LieModule.IsTriangularizable ℝ Cartan Der :=
    cartanIsTriangularizable
  letI : P.IsCrystallographic := by
    change (LieAlgebra.IsKilling.rootSystem
      (Cartan : LieSubalgebra ℝ Der)).IsCrystallographic
    infer_instance
  letI : P.IsReduced := by
    change (LieAlgebra.IsKilling.rootSystem
      (Cartan : LieSubalgebra ℝ Der)).IsReduced
    infer_instance
  exact {
    long := nativeRootIndex nativeLongSimpleIndex
    short := nativeRootIndex nativeShortSimpleIndex
    pairingIn_long_short := by
      apply (FaithfulSMul.algebraMap_injective ℤ ℝ)
      rw [P.algebraMap_pairingIn]
      simpa using native_short_coroot_on_long_root }

theorem nativeRootIndex_self_coroot_pairing (i : nonzeroIndex) :
    (P.root (nativeRootIndex i)) (P.coroot (nativeRootIndex i)) = 2 := by
  letI : LieSubalgebra.IsCartanSubalgebra (Cartan : LieSubalgebra ℝ Der) :=
    axialCartan_isCartanSubalgebra
  letI : LieModule.IsTriangularizable ℝ Cartan Der :=
    cartanIsTriangularizable
  letI : Nonempty (LieModule.Weight ℝ Cartan Der) :=
    ⟨nativeRootWeightMathlib nativeShortSimpleIndex⟩
  have hα : (nativeRootIndex i).1.IsNonZero := by
    simpa [LieSubalgebra.root] using (nativeRootIndex i).2
  have h := LieAlgebra.IsKilling.root_apply_coroot
    (α := (nativeRootIndex i).1) hα
  simpa [P] using h

theorem nativeRootIndex_pairing_apply (i j : nonzeroIndex) :
    P.pairing (nativeRootIndex j) (nativeRootIndex i) =
      (P.root (nativeRootIndex j)) (P.coroot (nativeRootIndex i)) := by
  letI : LieSubalgebra.IsCartanSubalgebra (Cartan : LieSubalgebra ℝ Der) :=
    axialCartan_isCartanSubalgebra
  letI : LieModule.IsTriangularizable ℝ Cartan Der :=
    cartanIsTriangularizable
  exact LieAlgebra.IsKilling.rootSystem_pairing_apply
    (Cartan : LieSubalgebra ℝ Der)
    (nativeRootIndex i) (nativeRootIndex j)

def nativeSimpleIndex : Fin 2 → nonzeroIndex
  | 0 => nativeShortSimpleIndex
  | 1 => nativeLongSimpleIndex

theorem native_simple_cartan_matrix (i j : Fin 2) :
    (P.root (nativeRootIndex (nativeSimpleIndex i)))
        (P.coroot (nativeRootIndex (nativeSimpleIndex j))) =
      simpleCartanMatrix i j := by
  fin_cases i <;> fin_cases j
  · exact nativeRootIndex_self_coroot_pairing nativeShortSimpleIndex
  · exact native_long_coroot_on_short_root
  · exact native_short_coroot_on_long_root
  · exact nativeRootIndex_self_coroot_pairing nativeLongSimpleIndex

theorem native_simple_root_pairing (i j : Fin 2) :
    P.pairing (nativeRootIndex (nativeSimpleIndex i))
        (nativeRootIndex (nativeSimpleIndex j)) =
      simpleCartanMatrix i j := by
  calc
    P.pairing (nativeRootIndex (nativeSimpleIndex i))
        (nativeRootIndex (nativeSimpleIndex j)) =
        P.root (nativeRootIndex (nativeSimpleIndex i))
          (P.coroot (nativeRootIndex (nativeSimpleIndex j))) :=
      nativeRootIndex_pairing_apply (nativeSimpleIndex j) (nativeSimpleIndex i)
    _ = simpleCartanMatrix i j := native_simple_cartan_matrix i j

theorem native_long_reflection_short :
    P.reflectionPerm (nativeRootIndex nativeLongSimpleIndex)
        (nativeRootIndex nativeShortSimpleIndex) =
      nativeRootIndex ⟨9, by decide, by decide⟩ := by
  apply P.root.injective
  rw [P.root_reflectionPerm]
  rw [P.reflection_apply_root]
  have hp := native_simple_root_pairing (0 : Fin 2) 1
  change P.pairing (nativeRootIndex nativeShortSimpleIndex)
      (nativeRootIndex nativeLongSimpleIndex) = _ at hp
  rw [hp]
  norm_num [simpleCartanMatrix, smul_eq_mul]
  apply LinearMap.ext
  intro x
  change (nativeRootWeightMathlib nativeShortSimpleIndex).toFun x +
      (nativeRootWeightMathlib nativeLongSimpleIndex).toFun x =
    (nativeRootWeightMathlib ⟨9, by decide, by decide⟩).toFun x
  have hshort := congrArg (fun f => f x) nativeShortSimpleWeight_value
  have hlong := congrArg (fun f => f x) nativeLongSimpleWeight_value
  have hchain := congrArg (fun f => f x) nativePositiveRootWeight_chain.1
  have hshort' :
      (nativeRootWeightMathlib nativeShortSimpleIndex).toFun x =
        simpleWeightOnCartan 0 x := by
    simpa using hshort
  have hlong' :
      (nativeRootWeightMathlib nativeLongSimpleIndex).toFun x =
        simpleWeightOnCartan 1 x := by
    simpa using hlong
  have hchain' :
      (nativeRootWeightMathlib ⟨9, by decide, by decide⟩).toFun x =
        simpleWeightOnCartan 0 x + simpleWeightOnCartan 1 x := by
    simpa using hchain
  calc
    (nativeRootWeightMathlib nativeShortSimpleIndex).toFun x +
        (nativeRootWeightMathlib nativeLongSimpleIndex).toFun x =
        simpleWeightOnCartan 0 x + simpleWeightOnCartan 1 x := by
          rw [hshort', hlong']
    _ = (nativeRootWeightMathlib ⟨9, by decide, by decide⟩).toFun x := by
      exact hchain'.symm

theorem nativeEmbeddedG2_shortAddLong_index :
    @RootPairing.EmbeddedG2.shortAddLong _ _ _ _ _ _ _ _ _ P nativeEmbeddedG2 =
      nativeRootIndex ⟨9, by decide, by decide⟩ := by
  change P.reflectionPerm
      (nativeRootIndex nativeLongSimpleIndex)
      (nativeRootIndex nativeShortSimpleIndex) = _
  exact native_long_reflection_short

theorem native_short_reflection_long :
    P.reflectionPerm (nativeRootIndex nativeShortSimpleIndex)
        (nativeRootIndex nativeLongSimpleIndex) =
      nativeRootIndex ⟨11, by decide, by decide⟩ := by
  apply P.root.injective
  rw [P.root_reflectionPerm, P.reflection_apply_root]
  have hp := native_simple_root_pairing (1 : Fin 2) 0
  change P.pairing (nativeRootIndex nativeLongSimpleIndex)
      (nativeRootIndex nativeShortSimpleIndex) = _ at hp
  rw [hp]
  norm_num [simpleCartanMatrix, smul_eq_mul]
  have hroot (i : nonzeroIndex) :
      P.root (nativeRootIndex i) =
        (nativeRootWeightMathlib i).toFun := by
    rfl
  apply LinearMap.ext
  intro x
  change P.root (nativeRootIndex nativeLongSimpleIndex) x +
      3 * P.root (nativeRootIndex nativeShortSimpleIndex) x =
    (nativeRootWeightMathlib ⟨11, by decide, by decide⟩).toFun x
  rw [congrFun (hroot nativeLongSimpleIndex) x,
    congrFun (hroot nativeShortSimpleIndex) x]
  have hshort := congrArg (fun f => f x) nativeShortSimpleWeight_value
  have hlong := congrArg (fun f => f x) nativeLongSimpleWeight_value
  have hchain := congrArg (fun f => f x) nativePositiveRootWeight_chain.2.2
  have hshort' :
      (nativeRootWeightMathlib nativeShortSimpleIndex).toFun x =
        simpleWeightOnCartan 0 x := by simpa using hshort
  have hlong' :
      (nativeRootWeightMathlib nativeLongSimpleIndex).toFun x =
        simpleWeightOnCartan 1 x := by simpa using hlong
  have hchain' :
      (nativeRootWeightMathlib ⟨11, by decide, by decide⟩).toFun x =
        3 • simpleWeightOnCartan 0 x + simpleWeightOnCartan 1 x := by
    simpa using hchain
  rw [hshort', hlong', hchain']
  ring

/-! The explicit root exhaustion also gives the finite cardinality readout
    that later finite-root-system constructions consume. -/

noncomputable def nativeRootIndexEquiv : nonzeroIndex ≃ RootIndex :=
  Equiv.ofBijective nativeRootIndex
    ⟨nativeRootIndex_injective, nativeRootIndex_surjective⟩

theorem rootIndex_card : Fintype.card RootIndex = 12 := by
  rw [← Fintype.card_congr nativeRootIndexEquiv]
  decide

theorem native_simple_root_pairing_eq_paper_calibration (i j : Fin 2) :
    P.pairing (nativeRootIndex (nativeSimpleIndex i))
        (nativeRootIndex (nativeSimpleIndex j)) =
      (fun i j => simpleWeight i (simpleCoroot j)) i j := by
  rw [native_simple_root_pairing, paper_cartan_matrix]

/-! A single Mathlib-facing comparison packet.  The carrier and root pairing
    remain Mathlib's objects; this theorem only records the concrete native
    indexing, cardinality, simple-root calibration, and the two simple Weyl
    reflection readouts. -/
theorem nativeRootSystem_comparison :
    Function.Bijective nativeRootIndex ∧
      Fintype.card RootIndex = 12 ∧
      (∀ i j : Fin 2,
        P.pairing (nativeRootIndex (nativeSimpleIndex i))
            (nativeRootIndex (nativeSimpleIndex j)) =
          simpleCartanMatrix i j) ∧
      P.reflectionPerm (nativeRootIndex nativeLongSimpleIndex)
          (nativeRootIndex nativeShortSimpleIndex) =
        nativeRootIndex ⟨9, by decide, by decide⟩ ∧
      P.reflectionPerm (nativeRootIndex nativeShortSimpleIndex)
          (nativeRootIndex nativeLongSimpleIndex) =
        nativeRootIndex ⟨11, by decide, by decide⟩ := by
  refine ⟨⟨nativeRootIndex_injective, nativeRootIndex_surjective⟩, rootIndex_card,
    ?_, native_long_reflection_short, native_short_reflection_long⟩
  intro i j
  exact native_simple_root_pairing i j

end InfoGeometry.Lie.CanonicalZornRootSystemComparison
