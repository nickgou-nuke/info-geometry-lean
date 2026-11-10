/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Omega.GU.TerminalGamma6Rigidity
import Omega.GU.Window6IntrinsicBracketFiniteIntegerReduction
import Omega.TypedAddressBiaxialCompletion.CertificateLoop

namespace Omega.GU

/-- Chapter-level wrapper combining the intrinsic-bracket finite reduction, the Toeplitz--PSD
certificate loop, and the terminal `Γ₆` rigidity package.
    thm:window6-bracket-uniqueness-mixed-certificate-reduction -/
theorem paper_window6_bracket_uniqueness_mixed_certificate_reduction
    (D : Omega.GU.Window6IntrinsicBracketFiniteIntegerReductionData)
    (C : Omega.TypedAddressBiaxialCompletion.TypedAddressCertificateLoopData)
    (hUnitarySliceLocked : C.unitarySliceLocked)
    (R : Omega.GU.TerminalGamma6RigidityData) :
    (∀ c, c ∈ D.finiteIntegerSystem → ∀ i k, c i i k = 0) ∧
      (C.repulsionRadiusTendsToOne ↔ C.toeplitzPsdAll) ∧
      (C.toeplitzPsdAll ↔ C.toeplitzPsdCofinal) ∧
      (R.graphConnected ∧ R.automorphismGroupTrivial) := by
  have hCertificateLoop :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_certificate_loop
      C hUnitarySliceLocked
  refine ⟨?_, ?_, ?_,
    paper_terminal_gamma6_rigidity R⟩
  · intro c hc i k
    exact window6_antisymmetry_forces_diagonal_structure_constants_zero D c hc i k
  · exact hCertificateLoop.2.2.1
  · exact hCertificateLoop.2.2.2

end Omega.GU
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
