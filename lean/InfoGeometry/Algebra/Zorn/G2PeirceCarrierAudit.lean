import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep4

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

theorem pc1Aut_not_fix_ePlus :
    G2TwoSylowPCAutomorphisms.pc1Aut.1 ePlus ≠ ePlus := by
  rw [pc1Aut_ePlus_image]
  intro h
  have hcoord := congrArg (fun X : SplitOctF2 => X.y1) h
  simp [add, add2, ePlus, basis8, down1] at hcoord

end InfoGeometry.Algebra.Zorn.G2PeirceCarrierAudit
