import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

/-- Peel step 0 using exact inverse pc1Aut⁻¹ = pc1Aut. -/
def peel0 (f : SplitOctF2Aut) : SplitOctF2Aut :=
  (if (f.1 (basis8 7)).x0 then pc1Aut else 1) * f

/-- Peel step 1 using exact inverse pc2Aut⁻¹ = pc6Aut * pc2Aut. -/
def peel1 (f : SplitOctF2Aut) : SplitOctF2Aut :=
  (if (f.1 (basis8 2)).x1 then pc6Aut * pc2Aut else 1) * f

/-- Peel step 2 using exact inverse pc3Aut⁻¹ = pc6Aut * pc3Aut. -/
def peel2 (f : SplitOctF2Aut) : SplitOctF2Aut :=
  (if (f.1 (basis8 7)).x1 then pc6Aut * pc3Aut else 1) * f

/-- Peel step 4 and 3 using exact inverses pc5Aut and pc4Aut. -/
def peel34 (f : SplitOctF2Aut) : SplitOctF2Aut :=
  let e4 := (f.1 (basis8 2)).y1
  let e3 := (f.1 (basis8 3)).x2 ^^ e4
  (if e4 then pc5Aut else 1) * (if e3 then pc4Aut else 1) * f

/-- Peel step 5 using exact inverse pc6Aut⁻¹ = pc6Aut. -/
def peel5 (f : SplitOctF2Aut) : SplitOctF2Aut :=
  (if (f.1 (basis8 2)).x2 then pc6Aut else 1) * f

/-- Complete sequential peeling to identity. -/
def fullPeel (f : SplitOctF2Aut) : SplitOctF2Aut :=
  peel5 (peel34 (peel2 (peel1 (peel0 f))))

/-- Extraction of bit 0 from an automorphism. -/
def extractBit0 (f : SplitOctF2Aut) : Bool :=
  (f.1 (basis8 7)).x0

/-- Extraction of bit 1 after peeling bit 0. -/
def extractBit1 (f : SplitOctF2Aut) : Bool :=
  ((peel0 f).1 (basis8 2)).x1

/-- Extraction of bit 2 after peeling bits 0 and 1. -/
def extractBit2 (f : SplitOctF2Aut) : Bool :=
  ((peel1 (peel0 f)).1 (basis8 7)).x1

/-- Extraction of bit 4 after peeling bits 0, 1, and 2. -/
def extractBit4 (f : SplitOctF2Aut) : Bool :=
  ((peel2 (peel1 (peel0 f))).1 (basis8 2)).y1

/-- Extraction of bit 3 after peeling bits 0, 1, and 2. -/
def extractBit3 (f : SplitOctF2Aut) : Bool :=
  let f3 := peel2 (peel1 (peel0 f))
  (f3.1 (basis8 3)).x2 ^^ (f3.1 (basis8 2)).y1

/-- Extraction of bit 5 after peeling bits 0, 1, 2, 3, and 4. -/
def extractBit5 (f : SplitOctF2Aut) : Bool :=
  ((peel34 (peel2 (peel1 (peel0 f)))).1 (basis8 2)).x2

/-- Bundled 6-bit recovery map from sequential peeling. -/
def extractAllBits (f : SplitOctF2Aut) : Fin 6 → Bool
  | 0 => extractBit0 f
  | 1 => extractBit1 f
  | 2 => extractBit2 f
  | 3 => extractBit3 f
  | 4 => extractBit4 f
  | 5 => extractBit5 f

end InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
