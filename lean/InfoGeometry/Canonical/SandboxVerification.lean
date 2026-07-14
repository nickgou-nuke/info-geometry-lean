import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.RealBdG
import InfoGeometry.Krein.DoubledSpace
import Mathlib.Analysis.Normed.Algebra.Exponential

namespace SandboxVerification

open InfoGeometry.Krein
open InfoGeometry.Canonical.RealBdG

section Basic

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Test operator composition and exponential. -/
noncomputable def testOperatorExp (X A : EndH) (t : ℝ) : EndH :=
  (NormedSpace.exp (t • X)).comp A

/-- Test grand canonical structure. -/
noncomputable def testGrandCanonical (β μ : ℝ) (H N : EndH) : EndH :=
  NormedSpace.exp ((-β) • (H - (μ • N)))

end Basic

end SandboxVerification
