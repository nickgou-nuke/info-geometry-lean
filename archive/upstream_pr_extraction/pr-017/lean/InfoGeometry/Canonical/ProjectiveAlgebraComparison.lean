import InfoGeometry.Canonical.ProjectiveSectorDecomposition

/-!
# InfoGeometry.Canonical.ProjectiveAlgebraComparison

Projective comparison facts stated on the current strict projectivization
surface.
-/

namespace InfoGeometry.Canonical.ProjectiveAlgebraComparison

open InfoGeometry.Krein
open InfoGeometry.Canonical.ProjectiveSplitQ11Realization

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/--
The descended strict-projective epsilon action agrees with the doubled-space
`spectral_epsilon` action on representatives.
-/
theorem epsilon_is_mathlib_involute (v : H₂) (hv : v ≠ 0) :
    mathlibProjectiveEpsilon (E := E) (strictProjectivize (E := E) v hv) =
      strictProjectivize (E := E)
        (spectral_epsilon (E := E) v)
        (spectral_epsilon_ne_zero (E := E) hv) := by
  exact mathlibProjectiveEpsilon_projectivize (E := E) v hv

end InfoGeometry.Canonical.ProjectiveAlgebraComparison
