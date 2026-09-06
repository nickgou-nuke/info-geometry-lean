import InfoGeometry.Arithmetic.MellinBogoliubovNullEigenvalueBridge
import InfoGeometry.Canonical.BogoliubovCovariantMellinKreinQuantizationBridge

/-!
# Matrix readout of Mellin Bogoliubov null eigenvalues

The scalar Mellin bridge identifies `cosh r - sinh r` and
`cosh r + sinh r` with the two real Mellin powers.  This owner exposes the
same identities as readouts of the existing complex squeezing matrix.  It
does not introduce a Fock implementation or assert an inverse law for the
phase-boost product.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.MellinBogoliubovMatrixReadoutBridge

open InfoGeometry.Arithmetic.MellinBogoliubovNullEigenvalueBridge
open InfoGeometry.Canonical.BogoliubovMellinKrein

theorem squeezingMatrix_mellin_null_eigenvalue_minus
    (n : ℕ) (u : ℝ) (hn : 0 < (n : ℝ)) :
    (squeezingMatrix (bogoliubovRapidity n u)) 0 0 -
      (squeezingMatrix (bogoliubovRapidity n u)) 0 1 =
      (((n : ℝ) ^ (-u) : ℝ) : ℂ) := by
  simpa [squeezingMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using
    congrArg (fun x : ℝ => (x : ℂ))
      (mellin_null_eigenvalue_minus n u hn)

theorem squeezingMatrix_mellin_null_eigenvalue_plus
    (n : ℕ) (u : ℝ) (hn : 0 < (n : ℝ)) :
    (squeezingMatrix (bogoliubovRapidity n u)) 0 0 +
      (squeezingMatrix (bogoliubovRapidity n u)) 0 1 =
      (((n : ℝ) ^ u : ℝ) : ℂ) := by
  simpa [squeezingMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using
    congrArg (fun x : ℝ => (x : ℂ))
      (mellin_null_eigenvalue_plus n u hn)

end InfoGeometry.Arithmetic.MellinBogoliubovMatrixReadoutBridge
