import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.CartanLieDerivativeMagicBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Finite Dirac-Kähler operator `D = d + d*` in `Module.End R (ExteriorAlgebra R V)`. -/
def diracKahlerOp (d dstar : Module.End R (ExteriorAlgebra R V)) : Module.End R (ExteriorAlgebra R V) :=
  d + dstar

/-- Finite Hodge-de Rham Laplacian `Δ = d ∘ d* + d* ∘ d`. -/
def hodgeDeRhamLaplacian (d dstar : Module.End R (ExteriorAlgebra R V)) : Module.End R (ExteriorAlgebra R V) :=
  d.comp dstar + dstar.comp d

/-- The finite square identity `D² = Δ` under the nilpotence hypotheses `d² = 0`
and `(d*)² = 0`. -/
theorem dirac_kahler_sq_eq_laplacian
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (hd2 : d.comp d = 0) (hdstar2 : dstar.comp dstar = 0) :
    (diracKahlerOp d dstar).comp (diracKahlerOp d dstar) = hodgeDeRhamLaplacian d dstar := by
  dsimp [diracKahlerOp, hodgeDeRhamLaplacian]
  ext omega
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  have hd_sq : ∀ x, d (d x) = 0 := fun x => LinearMap.congr_fun hd2 x
  have hdstar_sq : ∀ x, dstar (dstar x) = 0 := fun x => LinearMap.congr_fun hdstar2 x
  rw [LinearMap.map_add, LinearMap.map_add, hd_sq omega, hdstar_sq omega]
  abel

end InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
