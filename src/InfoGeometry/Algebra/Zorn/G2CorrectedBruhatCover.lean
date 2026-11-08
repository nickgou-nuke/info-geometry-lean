/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2CorrectedCosetSignature
import InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessAssembly

/-! Transport the certified group factorizations through inverse quotient
enumeration. This establishes coverage, not separation of the cells. -/
namespace InfoGeometry.Algebra.Zorn.G2CorrectedBruhatCover

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open G2CorrectedQuotientCertificate G2CorrectedCosetSignature
open G2FlagOrbitPartitionCertificate G2FlagWordEvaluator G2FlagWordCertificate
open G2TwoBruhatClassification G2TwoPCSubgroupClosure G2TwoSylowSubgroup
open G2ConcreteWeylG2

theorem correctedRepresentative_eq_flagRepresentative (i : Fin 189) :
    correctedQuotientRepresentative i = flagRepresentative i := by rfl

theorem inverse_mem_cell {g w : SplitOctF2Aut}
    (h : g ∈ concreteBruhatCell w) : g⁻¹ ∈ concreteBruhatCell w⁻¹ := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  refine ⟨b⁻¹, a⁻¹, sylowTwoSubgroup.inv_mem hb,
    sylowTwoSubgroup.inv_mem ha, ?_⟩
  simp [mul_inv_rev, mul_assoc]

theorem inverse_correctedRepresentative_mem (k : Fin 12) (i : Fin 189)
    (hi : i ∈ orbitCells k) :
    (correctedQuotientRepresentative i)⁻¹ ∈
      concreteBruhatCell ((weylNF (orbitWeyl k).1 (orbitWeyl k).2)⁻¹) := by
  rw [correctedRepresentative_eq_flagRepresentative]
  exact inverse_mem_cell
    (G2GAPFlagWitnessAssembly.flagRepresentative_mem_concreteBruhatCell k i hi)

theorem concrete_cover : concreteBruhatCovering = Set.univ := by
  apply concreteBruhatCoverObligation_iff_covering_eq_univ.mp
  intro g
  obtain ⟨i, hi⟩ := correctedCosetEquiv.surjective (QuotientGroup.mk g)
  have hmem : i ∈ Finset.univ.biUnion orbitCells := by
    rw [orbitCells_partition]
    exact Finset.mem_univ i
  obtain ⟨k, _, hki⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨m, e, hw⟩ := weylNF_inv_exists (orbitWeyl k).1 (orbitWeyl k).2
  refine ⟨(m, e), ?_⟩
  have hr := inverse_correctedRepresentative_mem k i hki
  rw [hw] at hr
  rw [correctedCosetEquiv_apply, QuotientGroup.eq] at hi
  have hu : (correctedQuotientRepresentative i) * g ∈ sylowTwoSubgroup := by
    rw [sylowTwoSubgroup_eq_unipotentSubgroup]
    simpa using hi
  have h := concreteBruhatCell_right_mul (weylNF m e)
    (correctedQuotientRepresentative i * g)
    ((correctedQuotientRepresentative i)⁻¹) hu hr
  simpa [mul_assoc] using h

end InfoGeometry.Algebra.Zorn.G2CorrectedBruhatCover
