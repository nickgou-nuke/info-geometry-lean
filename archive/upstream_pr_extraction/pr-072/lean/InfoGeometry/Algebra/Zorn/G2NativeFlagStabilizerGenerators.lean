import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2TwoPCConjugation

/-!
# Fixed Lean-PC generators for the native flag-stabilizer readback

The six words below are written in the repository's fixed `PCExponent`
coordinate order.  This owner records only the native subgroup facts that
can be proved without importing an external PCGS basis or a CAS certificate.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
-- `pcWord` is qualified below to keep the two PC namespaces unambiguous.
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoPCConjugation

local notation "pcWord" => G2TwoSylowSubgroup.pcWord

def pcBits (b₀ b₁ b₂ b₃ b₄ b₅ : Bool) : G2TwoSylowSubgroup.PCWordExp := fun (i : Fin 6) =>
  if i = 0 then b₀ else
  if i = 1 then b₁ else
  if i = 2 then b₂ else
  if i = 3 then b₃ else
  if i = 4 then b₄ else b₅

def stabilizerPCGenerators :
    Set SplitOctF2Aut :=
  Set.insert (pcWord (pcBits false false false false false true))
    (Set.insert (pcWord (pcBits false false false true false true))
      (Set.insert (pcWord (pcBits false false true false true false))
        (Set.insert (pcWord (pcBits false true true false false true))
          (Set.insert (pcWord (pcBits true false false false false false))
            (Set.singleton
              (pcWord (pcBits true false true true false true)))))))

theorem stabilizerPCGenerators_subset_unipotentSubgroup :
    stabilizerPCGenerators ⊆ unipotentSubgroup.carrier := by
  intro g hg
  have hg' :
      g = pcWord (pcBits false false false false false true) ∨
      g = pcWord (pcBits false false false true false true) ∨
      g = pcWord (pcBits false false true false true false) ∨
      g = pcWord (pcBits false true true false false true) ∨
      g = pcWord (pcBits true false false false false false) ∨
      g = pcWord (pcBits true false true true false true) := by
    simpa [stabilizerPCGenerators] using hg
  rcases hg' with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨_, rfl⟩

theorem stabilizerPCGenerators_closure_le_unipotentSubgroup :
    Subgroup.closure stabilizerPCGenerators ≤ unipotentSubgroup := by
  exact (Subgroup.closure_le _).2 stabilizerPCGenerators_subset_unipotentSubgroup

/-! The direct full-flag CAS probe returns the following smaller generating
set.  This declaration records only the native PC words; generation of the
stabilizer itself remains a separate readback obligation. -/
def directFlagPCGenerators :
    Set SplitOctF2Aut :=
  Set.insert (pcWord (pcBits true false false false false false))
    (Set.insert (pcWord (pcBits false true false false false false))
      (Set.insert (pcWord (pcBits false false true false false false))
        (Set.singleton (pcWord (pcBits false false false false true false)))))

theorem directFlagPCGenerators_subset_unipotentSubgroup :
    directFlagPCGenerators ⊆ unipotentSubgroup.carrier := by
  intro g hg
  have hg' :
      g = pcWord (pcBits true false false false false false) ∨
      g = pcWord (pcBits false true false false false false) ∨
      g = pcWord (pcBits false false true false false false) ∨
      g = pcWord (pcBits false false false false true false) := by
    simpa [directFlagPCGenerators] using hg
  rcases hg' with (rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

theorem directFlagPCGenerators_closure_le_unipotentSubgroup :
    Subgroup.closure directFlagPCGenerators ≤ unipotentSubgroup := by
  exact (Subgroup.closure_le _).2 directFlagPCGenerators_subset_unipotentSubgroup

theorem pcWord_pcBits_0 : pcWord (pcBits true false false false false false) = pc1Aut := by
  change pc1Aut * 1 * 1 * 1 * 1 * 1 = pc1Aut
  group

theorem pcWord_pcBits_1 : pcWord (pcBits false true false false false false) = pc2Aut := by
  change 1 * pc2Aut * 1 * 1 * 1 * 1 = pc2Aut
  group

theorem pcWord_pcBits_2 : pcWord (pcBits false false true false false false) = pc3Aut := by
  change 1 * 1 * pc3Aut * 1 * 1 * 1 = pc3Aut
  group

theorem pcWord_pcBits_4 : pcWord (pcBits false false false false true false) = pc5Aut := by
  change 1 * 1 * 1 * 1 * pc5Aut * 1 = pc5Aut
  group

theorem unipotentSubgroup_le_directFlagPCGenerators_closure :
    unipotentSubgroup ≤ Subgroup.closure directFlagPCGenerators := by
  let H := Subgroup.closure directFlagPCGenerators
  have h0 : pc1Aut ∈ H := by
    rw [← pcWord_pcBits_0]
    exact Subgroup.subset_closure (Or.inl rfl)
  have h1 : pc2Aut ∈ H := by
    rw [← pcWord_pcBits_1]
    exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have h2 : pc3Aut ∈ H := by
    rw [← pcWord_pcBits_2]
    exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : pc5Aut ∈ H := by
    rw [← pcWord_pcBits_4]
    exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))
  have h5 : pc6Aut ∈ H := by
    rw [← pc2Aut_sq_eq_pc6Aut]
    exact H.mul_mem h1 h1
  have h3 : pc4Aut ∈ H := by
    have hc : pc5Aut⁻¹ * pc1Aut * pc5Aut = pc1Aut * pc4Aut :=
      pc5Aut_conj_pc1Aut
    have hp : pc1Aut * pc4Aut ∈ H := by
      rw [← hc]
      exact H.mul_mem (H.mul_mem (H.inv_mem h4) h0) h4
    have h4_eq : pc4Aut = pc1Aut⁻¹ * (pc1Aut * pc4Aut) := by group
    rw [h4_eq]
    exact H.mul_mem (H.inv_mem h0) hp
  have hgen : ∀ i : Fin 6, pcGenerator i ∈ H := by
    intro i
    fin_cases i
    · simpa [pcGenerator] using h0
    · simpa [pcGenerator] using h1
    · simpa [pcGenerator] using h2
    · simpa [pcGenerator] using h3
    · simpa [pcGenerator] using h4
    · simpa [pcGenerator] using h5
  have hrange : Set.range pcGenerator ⊆ (H : Set SplitOctF2Aut) := by
    rintro g ⟨i, rfl⟩
    exact hgen i
  rw [← sylowTwoSubgroup_eq_unipotentSubgroup]
  exact (Subgroup.closure_le H).mpr hrange

theorem directFlagPCGenerators_closure_eq_unipotentSubgroup :
    Subgroup.closure directFlagPCGenerators = unipotentSubgroup :=
  le_antisymm directFlagPCGenerators_closure_le_unipotentSubgroup
    unipotentSubgroup_le_directFlagPCGenerators_closure

end InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators
