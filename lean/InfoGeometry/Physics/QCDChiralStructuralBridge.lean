import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearOperatorSuperSoloviev
import InfoGeometry.Physics.NuclearInternalExternalParityFactorization
import InfoGeometry.MassSpectrometry.DirectedOperatorDoubling

/-!
# Structural chiral bridge toward a QCD-facing lane

This module records only the common `ℤ₂`-graded operator shape already proved
in the nuclear and mass-spectrometry corridors.

It does **not** identify the grading with the physical Dirac `γ₅`, does not
construct a QCD Dirac operator, and does not prove chiral symmetry breaking or
mass generation.  Those are separate representation/physics theorems.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDChiralStructuralBridge

open InfoGeometry.Physics.NuclearOperatorSuperSoloviev
open InfoGeometry.Physics.NuclearInternalExternalParityFactorization
open InfoGeometry.MassSpectrometry

variable {A : Type*} [Ring A]

/-- Nuclear odd off-diagonal channels and the spectroscopy doubled operator
satisfy the same grading-conjugation sign law on their respective carriers. -/
theorem nuclear_massspec_chiral_packet
    (P : InternalParity A) (E0 E1 V W : A)
    (hE0 : P.IsEven E0) (hE1 : P.IsEven E1)
    (hV : P.IsOdd V) (hW : P.IsOdd W)
    {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) :
    internalParity P * blockHamiltonian E0 E1 V W * internalParity P =
        reflectOffDiagonal E0 E1 V W ∧
      gradingMatrix n * doubledOperator K * gradingMatrix n =
        -doubledOperator K :=
  ⟨internalParity_reflection_of_even_diagonal_odd_offDiagonal
      P E0 E1 V W hE0 hE1 hV hW,
    grading_conjugates_doubledOperator_to_neg K⟩

/-- The two grading elements used in the structural bridge are involutions. -/
theorem nuclear_massspec_grading_involution_packet
    (P : InternalParity A) (n : ℕ) :
    internalParity P * internalParity P = 1 ∧
      gradingMatrix n * gradingMatrix n = 1 :=
  ⟨internalParity_sq P, gradingMatrix_sq n⟩

end InfoGeometry.Physics.QCDChiralStructuralBridge

end noncomputable section
