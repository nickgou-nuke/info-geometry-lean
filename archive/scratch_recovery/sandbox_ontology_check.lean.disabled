import InfoGeometry.KK.DiracFredholmModule
import InfoGeometry.Canonical.CertifiedInverseKernel

/-!
SANDBOX: ONTOLOGY CHECK
Verification of field names for RealSplitKreinDiracFredholmModule.
-/

noncomputable section

open InfoGeometry.KK
open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Test: Can we construct a module with the current fields?
def testConstruct (cl11 : InfoGeometry.Quantum.RealSplitCl11Action (DoubledSpace E)) :
    RealSplitKreinDiracFredholmModule ℝ ℝ (DoubledSpace E) := {
  cl11 := cl11
  π := 0
  ρ := 0
  π_even := fun _ => sorry
  ρ_even := fun _ => sorry
  F := 0
  F_odd := sorry
  F_skewAdj := sorry
  F_sq_one_compact := sorry
  comm_compact := fun _ => sorry
  superComm_eps_compact := sorry
  superComm_J_compact := sorry
}
