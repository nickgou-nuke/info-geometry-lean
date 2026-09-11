import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Spectral-triple commutator compatibility

This is a small typed interface between a continuous representation, a bounded
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
structure SpectralTripleCommutatorDatum where
  D : H →L[ℝ] H
  representation : A →L[ℝ] (H →L[ℝ] H)

def boundedCommutator
    (S : SpectralTripleCommutatorDatum (A := A) (H := H)) (a : A) :
    H →L[ℝ] H :=
  S.D.comp (S.representation a) - (S.representation a).comp S.D

abbrev SpectralTripleCommutatorData :=
  SpectralTripleCommutatorDatum (A := A) (H := H)

namespace SpectralTripleCommutatorData

variable (S : SpectralTripleCommutatorData (A := A) (H := H))

@[simp] theorem commutator_eq (a : A) :
    S.D.comp (S.representation a) - (S.representation a).comp S.D =
      boundedCommutator S a :=
  rfl

@[simp] theorem bounded_commutator_eq (a : A) :
    boundedCommutator S a =
      S.D.comp (S.representation a) - (S.representation a).comp S.D :=
  rfl

@[simp] theorem commutator_zero :
    S.D.comp (S.representation 0) - (S.representation 0).comp S.D = 0 := by
  simp [SpectralTripleCommutatorDatum.representation]

theorem commutator_add (a b : A) :
    S.D.comp (S.representation (a + b)) -
        (S.representation (a + b)).comp S.D =
      (S.D.comp (S.representation a) - (S.representation a).comp S.D) +
        (S.D.comp (S.representation b) - (S.representation b).comp S.D) := by
  ext v
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

theorem commutator_smul (c : ℝ) (a : A) :
    S.D.comp (S.representation (c • a)) -
        (S.representation (c • a)).comp S.D =
      c • (S.D.comp (S.representation a) - (S.representation a).comp S.D) := by
  ext v
  simp [sub_eq_add_neg, smul_sub, add_comm]

end SpectralTripleCommutatorData

end
end InfoGeometry.Canonical
