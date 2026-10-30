import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic
import Omega.RatioResultant.RatioResultantDiscRigidity

namespace Omega.RatioResultant

/-- Ratio-resultant data with at least four root labels. The operator group
below is the full permutation group of these labels; no field-Galois
identification is part of this carrier. -/
structure RatioFieldFullSymmetricData (K : Type*) [Field K] where
  resultantData : RatioResultantData K
  hrootCount : 4 ≤ resultantData.rootCount

namespace RatioFieldFullSymmetricData

/-- Distinguished first root index. -/
def baseZero {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K) :
    Fin D.resultantData.rootCount :=
  ⟨0, lt_of_lt_of_le (by decide) D.hrootCount⟩

/-- Distinguished second root index. -/
def baseOne {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K) :
    Fin D.resultantData.rootCount :=
  ⟨1, lt_of_lt_of_le (by decide : 1 < 4) D.hrootCount⟩

/-! The full root-label permutation group is represented faithfully by
invertible operators on functions on the actual root-label carrier. -/

/-- Inverse reindexing by a root-label permutation, as a linear operator. -/
def rootPermutationOperator {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K)
    (σ : Equiv.Perm (Fin D.resultantData.rootCount)) :
    Module.End K (Fin D.resultantData.rootCount → K) where
  toFun f i := f (σ⁻¹ i)
  map_add' f g := by funext i; rfl
  map_smul' c f := by funext i; rfl

/-- The root-label permutation operator packaged as a unit. -/
def rootPermutationOperatorUnit {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K)
    (σ : Equiv.Perm (Fin D.resultantData.rootCount)) :
    (Module.End K (Fin D.resultantData.rootCount → K))ˣ where
  val := rootPermutationOperator D σ
  inv := rootPermutationOperator D σ⁻¹
  val_inv := by ext f i; simp [rootPermutationOperator]
  inv_val := by ext f i; simp [rootPermutationOperator]

/-- The group homomorphism representing root-label permutations by operators. -/
def rootPermutationOperatorRep {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K) :
    Equiv.Perm (Fin D.resultantData.rootCount) →*
      (Module.End K (Fin D.resultantData.rootCount → K))ˣ where
  toFun := rootPermutationOperatorUnit D
  map_one' := by apply Units.ext; ext f i; rfl
  map_mul' σ τ := by apply Units.ext; ext f i; rfl

/-- Function probes make the root-label operator representation faithful. -/
theorem rootPermutationOperatorRep_injective {K : Type*} [Field K]
    (D : RatioFieldFullSymmetricData K) : Function.Injective (rootPermutationOperatorRep D) := by
  classical
  intro σ τ hστ
  have hop : rootPermutationOperator D σ = rootPermutationOperator D τ :=
    congrArg Units.val hστ
  have hinv : σ⁻¹ = τ⁻¹ := by
    apply Equiv.ext
    intro i
    let xσ := σ⁻¹ i
    let xτ := τ⁻¹ i
    let δ : Fin D.resultantData.rootCount → K := fun x => if x = xσ then 1 else 0
    have heval := congrArg (fun T : Module.End K (Fin D.resultantData.rootCount → K) => T δ i) hop
    change δ xσ = δ xτ at heval
    have hargs : xτ = xσ := by
      by_cases h : xτ = xσ
      · exact h
      · simp [δ, xσ, xτ] at heval
        exact False.elim (h heval)
    exact hargs.symm
  apply Equiv.ext
  intro i
  have h := congrArg (fun p : Equiv.Perm (Fin D.resultantData.rootCount) => p i)
    (congrArg Inv.inv hinv)
  simpa using h

/-- The full root-label permutation group as a concrete subgroup of the
invertible endomorphisms of the root-function module. -/
def rootPermutationOperatorGroup {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K) :
    Subgroup (Module.End K (Fin D.resultantData.rootCount → K))ˣ :=
  (⊤ : Subgroup (Equiv.Perm (Fin D.resultantData.rootCount))).map
    (rootPermutationOperatorRep D)

/-- Adjacent root-label transpositions witness noncommutativity in the
operator-unit image when there are at least three roots. -/
theorem rootPermutationOperatorGroup_noncommutative {K : Type*} [Field K]
    (D : RatioFieldFullSymmetricData K) :
    ∃ u v : ↥(rootPermutationOperatorGroup D), u * v ≠ v * u := by
  let i₀ : Fin D.resultantData.rootCount := D.baseZero
  let i₁ : Fin D.resultantData.rootCount := D.baseOne
  let i₂ : Fin D.resultantData.rootCount := ⟨2,
    lt_of_lt_of_le (by decide : 2 < 4) D.hrootCount⟩
  have h01 : i₀ ≠ i₁ := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [i₀, i₁, RatioFieldFullSymmetricData.baseZero,
      RatioFieldFullSymmetricData.baseOne] at hv
  have h12' : i₁ ≠ i₂ := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [i₁, i₂, RatioFieldFullSymmetricData.baseOne] at hv
  have h02 : i₀ ≠ i₂ := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [i₀, i₂, RatioFieldFullSymmetricData.baseZero] at hv
  let a : Equiv.Perm (Fin D.resultantData.rootCount) := Equiv.swap i₀ i₁
  let b : Equiv.Perm (Fin D.resultantData.rootCount) := Equiv.swap i₁ i₂
  have hab : a * b ≠ b * a := by
    intro h
    have heval := congrArg (fun p : Equiv.Perm (Fin D.resultantData.rootCount) => p i₀) h
    have hleft : (a * b) i₀ = i₁ := by
      change a (b i₀) = i₁
      rw [show b i₀ = i₀ by
        change Equiv.swap i₁ i₂ i₀ = i₀
        exact Equiv.swap_apply_of_ne_of_ne h01 h02]
      change Equiv.swap i₀ i₁ i₀ = i₁
      exact Equiv.swap_apply_left i₀ i₁
    have hright : (b * a) i₀ = i₂ := by
      change Equiv.swap i₁ i₂ (Equiv.swap i₀ i₁ i₀) = i₂
      rw [Equiv.swap_apply_left]
      exact Equiv.swap_apply_left i₁ i₂
    rw [hleft, hright] at heval
    exact h12' heval
  have hrep := rootPermutationOperatorRep_injective D
  have hne : rootPermutationOperatorRep D a * rootPermutationOperatorRep D b ≠
      rootPermutationOperatorRep D b * rootPermutationOperatorRep D a := by
    intro h
    exact hab (hrep (by simpa using h))
  refine ⟨⟨rootPermutationOperatorRep D a, ?_⟩, ⟨rootPermutationOperatorRep D b, ?_⟩, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨a, trivial, rfl⟩
  · exact Subgroup.mem_map.mpr ⟨b, trivial, rfl⟩
  · intro h
    exact hne (congrArg Subtype.val h)

/-- Ordered-pair irreducibility: any ordered pair of distinct indices lies in the orbit of the
base pair `(0,1)` under the full symmetric action. -/
def orderedPairIrreducible {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K) : Prop :=
  ∀ i j : Fin D.resultantData.rootCount, i ≠ j →
    ∃ σ : Equiv.Perm (Fin D.resultantData.rootCount), σ D.baseZero = i ∧ σ D.baseOne = j

/-- The root-label symmetry package combines discriminant-character rigidity,
ordered-pair transitivity, and a noncommutative operator realization of the
full permutation group. This does not identify the group with a field
Galois group. -/
def rootLabelOperatorSymmetryStatement {K : Type*} [Field K]
    (D : RatioFieldFullSymmetricData K) : Prop :=
  D.resultantData.discriminantQuadraticRigidity ∧
    D.orderedPairIrreducible ∧
    ∃ u v : ↥(D.rootPermutationOperatorGroup), u * v ≠ v * u

end RatioFieldFullSymmetricData

open RatioFieldFullSymmetricData

private def orderedPairBaseZero {n : ℕ} (h2 : 2 ≤ n) : Fin n :=
  ⟨0, lt_of_lt_of_le (by decide) h2⟩

private def orderedPairBaseOne {n : ℕ} (h2 : 2 ≤ n) : Fin n :=
  ⟨1, lt_of_lt_of_le (by decide : 1 < 2) h2⟩

private lemma baseZero_ne_baseOne {n : ℕ} (h2 : 2 ≤ n) :
    orderedPairBaseZero h2 ≠ orderedPairBaseOne h2 := by
  intro h
  have hval : (orderedPairBaseZero h2).val = (orderedPairBaseOne h2).val := congrArg Fin.val h
  simp [orderedPairBaseZero, orderedPairBaseOne] at hval

private lemma exists_perm_send_ordered_pair {n : ℕ} (h2 : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin n),
      σ (orderedPairBaseZero h2) = i ∧ σ (orderedPairBaseOne h2) = j := by
  let a : Fin n := orderedPairBaseZero h2
  let b : Fin n := orderedPairBaseOne h2
  have hab : a ≠ b := baseZero_ne_baseOne h2
  by_cases hi : i = a
  · subst hi
    by_cases hj : j = b
    · subst hj
      exact ⟨1, rfl, rfl⟩
    · refine ⟨Equiv.swap b j, ?_, ?_⟩
      · simpa using Equiv.swap_apply_of_ne_of_ne hab hij
      · simp [b]
  · let τ : Equiv.Perm (Fin n) := Equiv.swap a i
    refine ⟨Equiv.swap (τ b) j * τ, ?_, ?_⟩
    · have hτa : τ a = i := by
        simp [τ]
      have hτb_ne_i : τ b ≠ i := by
        intro h
        have hba : b = a := τ.injective (h.trans hτa.symm)
        exact hab hba.symm
      have hi_ne_τb : i ≠ τ b := by
        intro h
        exact hτb_ne_i h.symm
      change Equiv.swap (τ b) j (τ a) = i
      rw [hτa]
      exact Equiv.swap_apply_of_ne_of_ne hi_ne_τb hij
    · change Equiv.swap (τ b) j (τ b) = j
      simp

/-- Root-label operator symmetry completion: discriminant rigidity, ordered-pair
transitivity, and noncommuting operators from adjacent root-label transpositions.
    cor:ratio-field-full-symmetric -/
theorem rootLabelOperatorSymmetry {K : Type*} [Field K] (D : RatioFieldFullSymmetricData K) :
    D.rootLabelOperatorSymmetryStatement := by
  have hRigidity : D.resultantData.discriminantQuadraticRigidity :=
    paper_ratio_resultant_disc_rigidity D.resultantData
  have hPairs : D.orderedPairIrreducible := by
    intro i j hij
    exact exists_perm_send_ordered_pair
      (le_trans (by decide : 2 ≤ 4) D.hrootCount) i j hij
  exact ⟨hRigidity, hPairs, rootPermutationOperatorGroup_noncommutative D⟩

end Omega.RatioResultant
