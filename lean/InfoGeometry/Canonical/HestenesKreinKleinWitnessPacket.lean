import InfoGeometry.Clifford.Grading
import InfoGeometry.Canonical.HadjiivanovMonodromyProjection

-- Finite Lean packet mirroring `tools/sympy/hestenes_krein_klein_witness.py`.
-- This is a witness-alias surface for:
-- grading split / fixed-point decomposition,
-- Hadjiivanov monodromy projection facts owned by imported modules.

noncomputable section

namespace HestenesKreinKleinWitnessPacket

open scoped BigOperators
open InfoGeometry.Krein

section Grading

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- SymPy witness: grading split.
theorem grading_fixed_point_split (v : DoubledSpace E) :
    v = spectralPlusProj (E := E) v + spectralMinusProj (E := E) v := by
  simpa using krein_projector_decomposition (E := E) v

end Grading

end HestenesKreinKleinWitnessPacket
