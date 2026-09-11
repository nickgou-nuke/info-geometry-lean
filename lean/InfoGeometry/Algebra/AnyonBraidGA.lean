import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Geometric-algebra rotor substrate for braid interfaces

This file records only a Clifford/geometric-algebra substrate interface.  It is
not a formalization of Fibonacci anyon braiding, and it does not prove an Artin
braid representation.

#### BUCKET 1: CLOSED FINITE THEOREMS

`rotor_substrate_readout`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

The readout is conditional on an explicitly supplied Clifford anti-commutator
identity.

#### BUCKET 3: OPEN CLOSURE DEBT

Deriving the anti-commutator from quadratic-form orthogonality and connecting
the resulting rotors to Fibonacci F/R matrices remain open here.
-/

namespace InfoGeometry.Algebra.AnyonBraidGA

open CliffordAlgebra

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- Clifford anti-commutator for two vectors in the chosen quadratic space. -/
def CliffordVectorAnticommutes (u v : M) : Prop :=
  (ι Q u) * (ι Q v) + (ι Q v) * (ι Q u) = 0

/-- Orthogonality implies Clifford anti-commutation. -/
theorem CliffordVectorAnticommutes_of_isOrtho {u v : M} (h : Q.IsOrtho u v) :
    CliffordVectorAnticommutes Q u v := by
  dsimp [CliffordVectorAnticommutes]
  simpa using (CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho (Q := Q) (a := u) (b := v) h)

/--
Geometric-algebra substrate readout.

This now has a genuine finite logical witness: the anti-commutator vanishes
whenever the vectors are orthogonal for the chosen quadratic form.
-/
theorem rotor_substrate_readout_of_isOrtho (u v : M)
    (h : Q.IsOrtho u v) :
    (ι Q u) * (ι Q v) + (ι Q v) * (ι Q u) = 0 := by
  simpa [CliffordVectorAnticommutes] using
    (CliffordVectorAnticommutes_of_isOrtho (Q := Q) (u := u) (v := v) h)

end InfoGeometry.Algebra.AnyonBraidGA
