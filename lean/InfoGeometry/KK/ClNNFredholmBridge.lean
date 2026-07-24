import InfoGeometry.KK.RealSplitKreinKasparovCycle
import InfoGeometry.Quantum.RealSplitClifford
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.KK.ClNNFredholmBridge

Adjacent bridge from the first split `Cl(n,n)` step to the current bounded
real split-Krein Fredholm/Kasparov seed.

This file does not introduce a new KK ontology. It records that whenever the
cycle carries the canonical doubled-space split `Cl(1,1)` atom, the primitive
cycle generators are exactly the first-step Clifford seeds already owned by the
repo.
-/

namespace InfoGeometry.KK.ClNNFredholmBridge

open InfoGeometry.KK
open InfoGeometry.Krein
open InfoGeometry.Quantum

section FirstStep

variable {A B E : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

@[rep_depth operator] theorem
    RealSplitKreinKasparovCycle.firstStep_leftGenerator_eq_cl11Rep
    (X : RealSplitKreinKasparovCycle A B (DoubledSpace E))
    (hcl11 : X.cl11 = doubledSpaceCl11Action (E := E)) :
    X.cl11.J
      = InfoGeometry.Krein.cl11Rep (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)) := by
  simpa [hcl11] using doubledSpaceCl11Action_J_eq_cl11Rep_leftGenerator (E := E)

@[rep_depth operator] theorem
    RealSplitKreinKasparovCycle.firstStep_rightGenerator_eq_cl11Rep
    (X : RealSplitKreinKasparovCycle A B (DoubledSpace E))
    (hcl11 : X.cl11 = doubledSpaceCl11Action (E := E)) :
    X.K
      = InfoGeometry.Krein.cl11Rep (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) := by
  simpa [RealSplitKreinKasparovCycle.K, hcl11] using
    doubledSpaceCl11Action_K_eq_cl11Rep_rightGenerator (E := E)

@[rep_depth operator] theorem
    RealSplitKreinKasparovCycle.firstStep_pseudoscalar_eq_cl11Rep
    (X : RealSplitKreinKasparovCycle A B (DoubledSpace E))
    (hcl11 : X.cl11 = doubledSpaceCl11Action (E := E)) :
    X.cl11.eps
      = InfoGeometry.Krein.cl11Rep (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)
            * CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) := by
  simpa [hcl11] using doubledSpaceCl11Action_eps_eq_cl11Rep_pseudoscalar (E := E)

end FirstStep

end InfoGeometry.KK.ClNNFredholmBridge
