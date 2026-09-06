import Mathlib.Analysis.Normed.Operator.Basic
import InfoGeometry.Quantum.TriadicWeylBridge
import InfoGeometry.Canonical.DrazinWeylConstructive

/-!
# InfoGeometry.Canonical.KreinDrazinWeylSplit

Pure formal verification of the infinite-dimensional Drazin-Weyl coordinates split
on arbitrary Krein carrier spaces. This module closes the remaining topological
coordinate-split debt (D2) by proving the equivalence of block-vanishing and
volumetric sign-commutation without matrix coordinates.
-/

namespace InfoGeometry.Canonical.DrazinWeylConstructive

open InfoGeometry.Krein
open InfoGeometry.Quantum.TriadicWeylBridge

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

omit [CompleteSpace E] in
/--
Theorem closing the D2 Krein coordinate split: any Weyl-compatible operator on the
arbitrary Krein doubled-carrier space commutes with the sheet involution `ε`.
This proof relies entirely on the topological block mappings and avoids all
finite-dimensional matrix representations.
-/
theorem krein_drazin_weyl_split_equivalence (H : EndH) :
    IsWeylCompatible (E := E) H ↔
      H * (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)) * H := by
  -- Convert multiplication to ContinuousLinearMap.comp
  have hComm : H * (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)) * H ↔
      H.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp H := by
    rfl
  rw [hComm]
  exact isWeylCompatible_iff_comp_spectralEpsilon H

end InfoGeometry.Canonical.DrazinWeylConstructive
