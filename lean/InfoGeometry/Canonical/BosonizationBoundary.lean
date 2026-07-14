import InfoGeometry.Canonical.ModeExtensionBoundary
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.External.Virasoro.HeisenbergAlgebra

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.BosonizationBoundary

Conservative bosonization boundary for the finite Tomita/Krein atom.

This module does **not** construct a Heisenberg current algebra from the split
`Cl(1,1)` seed. It only packages:

* the finite bilinear seed `J⁽⁰⁾ := [u₊, u₋]`, which is just `ε`,
* the fact that this seed has no Heisenberg anomaly.

The actual missing theorem remains constructive bosonization:
split completion + normal ordering + mode labels `⇒` Heisenberg currents.
-/

namespace BosonizationBoundary

open InfoGeometry.Canonical.ModeExtensionBoundary
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.BogoliubovFockSuper
open VirasoroProject

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Finite current seed `J⁽⁰⁾ = [u₊, u₋]` built from the split-null atom. -/
@[rep_depth krein]
noncomputable abbrev finiteBilinearCurrentSeed : FockEndomorphism E :=
  CCRBracket (E := E) (concreteCARCreation (E := E)) (concreteCARAnnihilation (E := E))

/-- The finite bilinear current seed is the Krein grading sign, not a Heisenberg current. -/
@[rep_depth krein]
theorem finiteBilinearCurrentSeed_eq_epsilon :
    finiteBilinearCurrentSeed (E := E) = InfoGeometry.Krein.spectral_epsilon (E := E) :=
  concrete_car_creation_annihilation_ccrBracket_eq_spectral_epsilon (E := E)

/-- The conservative zero-mode current seed: `J⁽⁰⁾₀ = J⁽⁰⁾`, nonzero modes vanish. -/
@[rep_depth krein]
noncomputable abbrev zeroModeCurrentSeed (n : ℤ) : FockEndomorphism E :=
  if n = 0 then finiteBilinearCurrentSeed (E := E) else 0

/-- At zero mode, the current seed recovers the finite Krein sign. -/
@[rep_depth krein, simp]
theorem zeroModeCurrentSeed_zero :
    zeroModeCurrentSeed (E := E) 0 = InfoGeometry.Krein.spectral_epsilon (E := E) := by
  rw [zeroModeCurrentSeed, if_pos rfl, finiteBilinearCurrentSeed_eq_epsilon]

/-- Off the zero mode, the conservative current seed vanishes. -/
@[rep_depth krein, simp]
theorem zeroModeCurrentSeed_ne_zero {n : ℤ} (hn : n ≠ 0) :
    zeroModeCurrentSeed (E := E) n = 0 := by
  simp [zeroModeCurrentSeed, hn]

/-- The zero-mode seed has no Heisenberg anomaly. -/
@[rep_depth krein]
theorem zeroModeCurrentSeed_ccrBracket (m n : ℤ) :
    CCRBracket (E := E)
      (zeroModeCurrentSeed (E := E) m)
      (zeroModeCurrentSeed (E := E) n) = 0 := by
  by_cases hm : m = 0
  · by_cases hn : n = 0
    · simp [zeroModeCurrentSeed, hm, hn, finiteBilinearCurrentSeed, CCRBracket,
        fockCommutator, superBracket_even_left]
    · simp [zeroModeCurrentSeed, hm, hn, CCRBracket, fockCommutator, superBracket_even_left]
  · simp [zeroModeCurrentSeed, hm, CCRBracket, fockCommutator, superBracket_even_left]

/-- The zero-mode seed commutes with the split finite grading sign. -/
@[rep_depth krein]
theorem zeroModeCurrentSeed_ccrBracket_with_epsilon (n : ℤ) :
    CCRBracket (E := E) (zeroModeCurrentSeed (E := E) n)
      (InfoGeometry.Krein.spectral_epsilon (E := E)) = 0 := by
  by_cases hn : n = 0
  · rw [show zeroModeCurrentSeed (E := E) n = InfoGeometry.Krein.spectral_epsilon (E := E) by
        simp [hn]]
    simp [CCRBracket, fockCommutator, superBracket_even_left]
  · simp [zeroModeCurrentSeed, hn, CCRBracket, fockCommutator, superBracket_even_left]

end Core

section ExternalReference

/--
The target Heisenberg current law already exists in the external Virasoro
corridor.  The local theorem surface records this law without reimplementing
the external algebra.
-/
@[rep_depth transport]
theorem external_heisenberg_current_law_reference (m n : ℤ) :
    ⁅HeisenbergAlgebra.jgen ℝ m, HeisenbergAlgebra.jgen ℝ n⁆ =
      (if m + n = 0 then (m : ℝ) • HeisenbergAlgebra.kgen ℝ else 0) :=
  HeisenbergAlgebra.lie_jgen ℝ m n

end ExternalReference

end BosonizationBoundary
