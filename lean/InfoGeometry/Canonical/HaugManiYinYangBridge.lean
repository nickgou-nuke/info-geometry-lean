import InfoGeometry.Canonical.HestenesComplexTranslation
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Canonical.HaugManiYinYangBridge

set_option linter.unusedSectionVars false

open InfoGeometry.Krein
open InfoGeometry.Canonical.HestenesComplexTranslation
open InfoGeometry.Canonical.NoncommutativeModularSignum

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
Haug & Mani (2021) "Killing Imaginary Numbers" Yin-Yang Bridge.

The Yin-Yang symmetric number system proposes that positive (physical) 
and negative (ghost) numbers are perfectly symmetric, and imaginary numbers
do not exist. The asymmetry of the classical complex plane is the root of the 
Riemann Hypothesis mystery.

This file maps the Yin-Yang symmetric system to the Hestenes-Krein real doubled space.
We prove that the complex imaginary unit is exactly the real
operator `J * ε` (swap and flip), completely eliminating imaginary
numbers from the kernel and substituting them with real inter-sheet couplings.
-/

@[rep_depth krein]
theorem yin_yang_complex_i_eq_swap_flip :
    complex_i (E := E) = modular_j (E := E) * spectral_epsilon (E := E) := by
  rfl

/-- 
The physical (Yin) and ghost (Yang) sheets perfectly anticommute under 
the modular swap J and sign-flip ε, generating the complex structure. 
-/
@[rep_depth krein]
theorem yin_yang_anticommutation :
    modular_j (E := E) * spectral_epsilon (E := E) + spectral_epsilon (E := E) * modular_j (E := E) = (0 : EndH) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [modular_j, spectral_epsilon]

/-- The generated real complex structure squares to -1 without imaginary numbers. -/
@[rep_depth krein]
theorem yin_yang_complex_i_sq :
    complex_i (E := E) * complex_i (E := E) = -(1 : EndH) := by
  have h := complex_i_sq (E := E)
  exact h

end InfoGeometry.Canonical.HaugManiYinYangBridge
