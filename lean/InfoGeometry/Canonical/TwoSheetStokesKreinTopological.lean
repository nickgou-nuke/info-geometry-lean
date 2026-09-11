import InfoGeometry.Canonical.TwoSheetStokesTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TwoSheetKreinTopological

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetStokesKreinTopological

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates
open InfoGeometry.Canonical.TwoSheetStokesCoordinates
open InfoGeometry.Canonical.TwoSheetKreinAdjoint
open InfoGeometry.Canonical.TwoSheetStokesTopological
open InfoGeometry.Canonical.TwoSheetKreinTopological

def stokesKreinAdjointHomeomorph : StokesQuad ≃ₜ StokesQuad :=
  operatorStokesHomeomorph.symm.trans
    (kreinAdjointHomeomorph.trans operatorStokesHomeomorph)

theorem stokesKreinAdjointHomeomorph_apply (q : StokesQuad) :
    stokesKreinAdjointHomeomorph q = stokesKreinAdjoint q := by
  change operatorStokesLinearEquiv
      (kreinAdjoint (operatorStokesLinearEquiv.symm q)) =
    stokesKreinAdjoint q
  exact kreinAdjoint_stokes q

theorem stokesKreinAdjointHomeomorph_involutive :
    stokesKreinAdjointHomeomorph.trans stokesKreinAdjointHomeomorph =
      Homeomorph.refl StokesQuad := by
  apply Homeomorph.ext
  intro q
  simp only [Homeomorph.trans_apply,
    stokesKreinAdjointHomeomorph_apply, Homeomorph.refl_apply]
  rcases q with ⟨q0, q1, q2, q3⟩
  simp [stokesKreinAdjoint, star_star]

end InfoGeometry.Canonical.TwoSheetStokesKreinTopological
