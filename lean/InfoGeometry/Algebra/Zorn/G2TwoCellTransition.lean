/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.G2SignatureCompleteness
import InfoGeometry.Algebra.Zorn.G2ConcreteGeneratorInfrastructure

/-! Two specified target cells for the corrected simple reflections. -/
namespace InfoGeometry.Algebra.Zorn.G2TwoCellTransition

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open G2CorrectedCosetSignature G2SignatureCompleteness
open G2ConcreteWeylG2 G2ConcreteBN2CorrectSecondConjugation
open G2TwoBruhatClassification G2TwoSylowSubgroup G2TwoPCSubgroupClosure

noncomputable def reflection (b : Bool) : SplitOctF2Aut :=
  if b then correctedT else s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem signature_transition :
    ∀ (b : Bool) (p : WeylG2) (e : PCWordExp), ∃ a : PCWordExp,
      cosetSignature (reflection b * pcWord e * weylNF p.1 p.2) =
        cosetSignature (pcWord a * weylNF p.1 p.2) ∨
      cosetSignature (reflection b * pcWord e * weylNF p.1 p.2) =
        cosetSignature (pcWord a * (reflection b * weylNF p.1 p.2)) := by
  decide

theorem mem_cell_of_signature {x w : SplitOctF2Aut} (a : PCWordExp)
    (h : cosetSignature x = cosetSignature (pcWord a * w)) :
    x ∈ concreteBruhatCell w := by
  have hu := cosetSignature_eq_iff_inv_mul_mem.mp h.symm
  refine ⟨pcWord a, (pcWord a * w)⁻¹ * x, ?_, ?_, ?_⟩
  · rw [sylowTwoSubgroup_eq_unipotentSubgroup]
    exact ⟨a, rfl⟩
  · rwa [sylowTwoSubgroup_eq_unipotentSubgroup]
  · group

theorem reflection_mul_cell (b : Bool) (p : WeylG2)
    {g : SplitOctF2Aut} (hg : g ∈ concreteBruhatCell (weylNF p.1 p.2)) :
    reflection b * g ∈ concreteBruhatCell (weylNF p.1 p.2) ∨
      reflection b * g ∈ concreteBruhatCell (reflection b * weylNF p.1 p.2) := by
  obtain ⟨a, v, ha, hv, rfl⟩ := hg
  rw [sylowTwoSubgroup_eq_unipotentSubgroup] at ha
  obtain ⟨e, rfl⟩ := ha
  obtain ⟨c, hc | hc⟩ := signature_transition b p e
  · exact Or.inl (by
      simpa only [mul_assoc] using
        concreteBruhatCell_right_mul _ v _ hv (mem_cell_of_signature c hc))
  · exact Or.inr (by
      simpa only [mul_assoc] using
        concreteBruhatCell_right_mul _ v _ hv (mem_cell_of_signature c hc))

theorem corrected_two_cell_transition {r : SplitOctF2Aut}
    (hr : r ∈ ({s, correctedT} : Set SplitOctF2Aut)) (p : WeylG2)
    {g : SplitOctF2Aut} (hg : g ∈ concreteBruhatCell (weylNF p.1 p.2)) :
    r * g ∈ concreteBruhatCell (weylNF p.1 p.2) ∨
      r * g ∈ concreteBruhatCell (r * weylNF p.1 p.2) := by
  rcases hr with rfl | hr
  · exact reflection_mul_cell false p hg
  · have heq : r = correctedT := hr
    subst r
    exact reflection_mul_cell true p hg

end InfoGeometry.Algebra.Zorn.G2TwoCellTransition
