import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesComplexTranslation

/-!
# Finite Hestenes--Krein conjugation packet

This owner records the proved operator identity supplied by the existing
Hestenes translation.  It deliberately does not promote spectral-support
premises or the Riemann hypothesis to a theorem.
-/

noncomputable section

namespace InfoGeometry.GrandUnification.Capstone

theorem modular_conjugation_packet
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    InfoGeometry.Krein.modular_j (E := E) *
        InfoGeometry.Krein.complex_i (E := E) *
        InfoGeometry.Krein.modular_j (E := E) =
      -InfoGeometry.Krein.complex_i (E := E) := by
  simpa using
    (InfoGeometry.Canonical.HestenesComplexTranslation.modular_j_conjugates_complex_i
      (E := E))

end InfoGeometry.GrandUnification.Capstone
