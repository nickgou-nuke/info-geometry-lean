import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep4
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

/-!
# Carrier audit for the Peirce-frame stabilizer

The ordered frame `(ePlus,eMinus)` is not the flag whose stabilizer is the
unipotent radical in the native Boolean Zorn carrier.  This owner records the
kernel-checked obstruction: the first PC generator moves `ePlus` by the
`down1` direction.  Consequently a future parabolic construction must use a
projective/flag carrier, rather than silently reusing this ordered frame.
-/

namespace InfoGeometry.Algebra.Zorn.G2PeirceCarrierAudit

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep4
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

theorem pc1Aut_not_fix_ePlus :
    G2TwoSylowPCAutomorphisms.pc1Aut.1 ePlus ≠ ePlus := by
  rw [pc1Aut_ePlus_image]
  intro h
  have hcoord := congrArg (fun X : SplitOctF2 => X.y1) h
  simp [add, add2, ePlus, basis8, down1] at hcoord

/-!
The proposed canonical-prefix stabilizer theorem cannot use
`unipotentSubgroup` with `ePlus` as its first coordinate.  The first PC
generator is already an element of that subgroup, but it moves `ePlus`.
This is a carrier-level obstruction, not a missing proof tactic: the
unipotent subgroup fixes the native flag carrier, whereas `ePlus` is the
first coordinate of the admissible-basis carrier.
-/
theorem pc1Aut_mem_unipotentSubgroup :
    G2TwoSylowPCAutomorphisms.pc1Aut ∈ unipotentSubgroup := by
  exact pcGenerator_mem_pcWord_range 0

theorem unipotentSubgroup_not_fixing_ePlus :
    ¬ (∀ g : SplitOctF2Aut, g ∈ unipotentSubgroup → g.1 ePlus = ePlus) := by
  intro hfix
  exact pc1Aut_not_fix_ePlus (hfix _ pc1Aut_mem_unipotentSubgroup)

end InfoGeometry.Algebra.Zorn.G2PeirceCarrierAudit
