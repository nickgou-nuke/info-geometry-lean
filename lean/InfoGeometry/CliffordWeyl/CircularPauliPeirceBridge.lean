import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.OperatorAlgebra.ChiralProjectorFromInvolution

/-!
# Circular modes from the real Pauli Peirce splitting

The real Peirce projectors select the two coordinate axes. After complexifying
the real rotation generator `Eminus`, its eigenvectors are the clockwise and
counterclockwise combinations of those axes. The corresponding spectral
projectors are constructive chiral projectors for the involution `-I * Eminus`.

Convention: `Eminus = !![0, 1; -1, 0]` generates clockwise rotation in the
standard `(x,y)` coordinates. Thus its `+I` eigenspace is called clockwise.
-/

noncomputable section

namespace InfoGeometry.CliffordWeyl.CircularPauliPeirceBridge

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.OperatorAlgebra

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The complexification of the real rotation generator `Eminus`. -/
def EminusC : Mat2C := !![(0 : ℂ), 1; -1, 0]

/-- The complexified real chiral matrix `Eplus`. -/
def EplusC : Mat2C := !![(1 : ℂ), 0; 0, -1]

/-- The left chiral basis vector, the range of the complexified `Pleft`. -/
def leftChiralVector : Fin 2 → ℂ := ![1, 0]

/-- The right chiral basis vector, the range of the complexified `Pright`. -/
def rightChiralVector : Fin 2 → ℂ := ![0, 1]

/-- The clockwise circular basis vector, the sum of left chirality and `i` times
right chirality. -/
def clockwiseVector : Fin 2 → ℂ := leftChiralVector + Complex.I • rightChiralVector

/-- The counterclockwise circular basis vector, the opposite chiral combination. -/
def counterclockwiseVector : Fin 2 → ℂ :=
  leftChiralVector - Complex.I • rightChiralVector

theorem EminusC_sq : EminusC * EminusC = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [EminusC, Matrix.mul_apply, Fin.sum_univ_two]

/-- The normalized elliptic generator is an involution and hence has chiral
projectors over `ℂ`. Its `+1` eigenspace is the `+I` eigenspace of `EminusC`. -/
def clockwiseChirality : ChiralInvolution Mat2C where
  chi := (-Complex.I) • EminusC
  chi_sq := by
    rw [smul_mul_smul, EminusC_sq]
    simp [Complex.I_mul_I]

/-- The clockwise projector, obtained from the chiral involution `-I * EminusC`. -/
def clockwiseProjector : Mat2C := clockwiseChirality.Pleft

/-- The counterclockwise projector, complementary to the clockwise projector. -/
def counterclockwiseProjector : Mat2C := clockwiseChirality.Pright

theorem clockwiseProjector_eq_matrix :
    clockwiseProjector = !![(1 / 2 : ℂ), -Complex.I / 2;
      Complex.I / 2, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockwiseProjector, clockwiseChirality, ChiralInvolution.Pleft,
      EminusC, Matrix.add_apply] <;> ring

theorem counterclockwiseProjector_eq_matrix :
    counterclockwiseProjector = !![(1 / 2 : ℂ), Complex.I / 2;
      -Complex.I / 2, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [counterclockwiseProjector, clockwiseChirality,
      ChiralInvolution.Pright, EminusC, Matrix.sub_apply] <;> ring

@[simp] theorem clockwiseProjector_idempotent :
    clockwiseProjector * clockwiseProjector = clockwiseProjector :=
  ChiralInvolution.Pleft_idem clockwiseChirality

@[simp] theorem counterclockwiseProjector_idempotent :
    counterclockwiseProjector * counterclockwiseProjector =
      counterclockwiseProjector :=
  ChiralInvolution.Pright_idem clockwiseChirality

theorem circularProjectors_complementary :
    clockwiseProjector + counterclockwiseProjector = 1 :=
  ChiralInvolution.Pleft_add_Pright clockwiseChirality

theorem EminusC_mulVec_clockwise :
    Matrix.mulVec EminusC clockwiseVector = Complex.I • clockwiseVector := by
  ext i
  fin_cases i <;>
    simp [EminusC, clockwiseVector, leftChiralVector, rightChiralVector,
      Matrix.mulVec, Complex.I_mul_I]

theorem EminusC_mulVec_counterclockwise :
    Matrix.mulVec EminusC counterclockwiseVector =
      -Complex.I • counterclockwiseVector := by
  ext i
  fin_cases i <;>
    simp [EminusC, counterclockwiseVector, leftChiralVector, rightChiralVector,
      Matrix.mulVec, Complex.I_mul_I]

/-- The right/left Peirce coordinates are the equal-weight sums and differences
of the clockwise/counterclockwise modes. No normalization is needed for these
exact basis identities. -/
theorem clockwise_add_counterclockwise :
    clockwiseVector + counterclockwiseVector = ![(2 : ℂ), 0] := by
  ext i
  fin_cases i <;>
    simp [clockwiseVector, counterclockwiseVector,
      leftChiralVector, rightChiralVector]; ring

theorem clockwise_sub_counterclockwise :
    clockwiseVector - counterclockwiseVector = ![(0 : ℂ), 2 * Complex.I] := by
  ext i
  fin_cases i <;>
    simp [clockwiseVector, counterclockwiseVector,
      leftChiralVector, rightChiralVector]; ring

end InfoGeometry.CliffordWeyl.CircularPauliPeirceBridge

end
