import InfoGeometry.Analysis.CliffordWaveletNativeL2
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Analysis.CliffordWaveletUncertainty

Operatorial uncertainty estimates used by the Clifford-wavelet development.

The owner is the ordinary complex Hilbert-space geometry of centered bounded
operators.  A Clifford-wavelet representation supplies concrete position and
frequency operators; it does not supply the uncertainty inequality as a
record field.

Literature:
H. Banouh, A. Ben Mabrouk, M. Kesri,
"Clifford-wavelet Transform and the uncertainty principle",
arXiv:1905.10169.
-/

noncomputable section

namespace InfoGeometry.Analysis.CliffordWaveletUncertainty

open InfoGeometry.Analysis.CliffordWaveletNativeL2

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/--
Robertson uncertainty for two bounded operators in a chosen state.

The deviations are norms of the centered operator vectors.  The theorem is
therefore valid on a noncommutative operator carrier and requires no spectral
diagonalization.
-/
theorem heisenberg
    (A B : H →L[ℂ] H) (ψ : H) :
    |RCLike.im
        (inner ℂ (centeredOperatorVector A ψ)
          (centeredOperatorVector B ψ))| ≤
      operatorDeviation A ψ * operatorDeviation B ψ :=
  centered_operator_uncertainty A B ψ

/--
A nonzero antisymmetric pairing prevents simultaneous collapse of both
operator deviations.
-/
theorem noncollapse
    (A B : H →L[ℂ] H) (ψ : H)
    (hpair :
      RCLike.im
          (inner ℂ (centeredOperatorVector A ψ)
            (centeredOperatorVector B ψ)) ≠ 0) :
    operatorDeviation A ψ ≠ 0 ∨ operatorDeviation B ψ ≠ 0 := by
  by_contra h
  push_neg at h
  have hA : centeredOperatorVector A ψ = 0 := by
    exact norm_eq_zero.mp h.1
  have hB : centeredOperatorVector B ψ = 0 := by
    exact norm_eq_zero.mp h.2
  apply hpair
  simp [hA, hB]

end InfoGeometry.Analysis.CliffordWaveletUncertainty
