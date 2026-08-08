import Mathlib

/-!
# Spectral-triple commutator compatibility

This is a small typed socket between a continuous representation, a bounded
Dirac operator, and a supplied bounded-commutator readout.  It does not assert
the remaining axioms of a spectral triple (self-adjointness, compact
resolvent, or a `C*`-algebra structure).
-/

namespace InfoGeometry.Canonical

noncomputable section

variable {A H : Type*}
  [NormedRing A] [NormedAlgebra ℝ A]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/--
The bounded commutator of `D` with the represented element `a` is carried by
an explicit continuous-operator-valued readout.

The field is oriented as
`D * representation(a) - representation(a) * D = bounded_commutator(a)`.
This makes the compatibility property reusable without introducing an
unjustified commutator construction for an unbounded operator.
-/
structure SpectralTripleCommutatorData where
  D : H →L[ℝ] H
  representation : A →L[ℝ] (H →L[ℝ] H)
  bounded_commutator : A →L[ℝ] (H →L[ℝ] H)
  commutator :
    ∀ a,
      D.comp (representation a) - (representation a).comp D =
        bounded_commutator a

namespace SpectralTripleCommutatorData

variable (S : SpectralTripleCommutatorData (A := A) (H := H))

@[simp] theorem commutator_eq (a : A) :
    S.D.comp (S.representation a) - (S.representation a).comp S.D =
      S.bounded_commutator a :=
  S.commutator a

@[simp] theorem bounded_commutator_eq (a : A) :
    S.bounded_commutator a =
      S.D.comp (S.representation a) - (S.representation a).comp S.D :=
  (S.commutator a).symm

end SpectralTripleCommutatorData

end
end InfoGeometry.Canonical
