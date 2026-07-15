import InfoGeometry.Canonical.TomitaTakesaki

open scoped InnerProductSpace

/-!
# OperatorAlgebraModularAtom

Tomita-Takesaki modular atom facts used by the operator-algebra bridge.
-/

namespace InfoGeometry.Canonical.OperatorAlgebraBridge

open InfoGeometry.Krein
open TomitaTakesaki

section ModularAtom

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Tomita modular pair realizes split `Cl(1,1)` on doubled real space. -/
theorem modular_atom_is_cl11 :
    InfoGeometry.Krein.cl11_algebra
      (modularConjugationJ (E := E))
      (modularSignEpsilon (E := E)) := by
  simpa [modularConjugationJ, modularSignEpsilon] using
    (InfoGeometry.Krein.modular_j_spectral_epsilon_is_cl11 (E := E))

/-- Owner-name form of the same split `Cl(1,1)` realization. -/
theorem modular_atom_is_cl11_root :
    InfoGeometry.Krein.cl11_algebra
      (modular_j (E := E))
      (spectral_epsilon (E := E)) := by
  exact InfoGeometry.Krein.modular_j_spectral_epsilon_is_cl11 (E := E)

end ModularAtom

end InfoGeometry.Canonical.OperatorAlgebraBridge
