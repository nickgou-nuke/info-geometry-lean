import InfoGeometry.Physics.Thermodynamics.ChiralChemicalPotentialDeformation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.JaynesMaxEntKMSBridge

namespace InfoGeometry.Physics.Thermodynamics

open InfoGeometry.Physics

/-!
# Finite BdG Gibbs/KMS specialization

The repository already owns the finite trace-cyclic KMS identity in
`JaynesMaxEntKMSBridge`.  This file only specializes it to the native `Fin 2`
BdG block and uses the Gibbs factor from the chemical-potential owner.
No positivity, normalization, or analytic KMS-strip assertion is added here.
-/

theorem bdg_gibbs_kms
    (mu : ℝ) (X Y : BdGBlock ℝ) :
    jaynesGibbsState (rho := gibbsFactor mu)
        (X * modularImaginaryFlow (gibbsFactor mu)
          (gibbsFactor (-mu)) Y) =
      jaynesGibbsState (rho := gibbsFactor mu) (Y * X) := by
  exact jaynes_state_is_strictly_kms
    (gibbsFactor mu) (gibbsFactor (-mu)) X Y
    (by simpa using gibbsFactor_inv (-mu))

end InfoGeometry.Physics.Thermodynamics
