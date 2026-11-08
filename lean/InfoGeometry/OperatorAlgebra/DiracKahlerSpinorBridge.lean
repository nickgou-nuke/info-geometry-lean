import InfoGeometry.OperatorAlgebra.ColeFuryIdeals
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge

/-!
# Dirac-Kähler Spinor Bridge

This module packages a finite transport of the already proved operator identity
`D² = Δ` through an explicit linear equivalence between a 32-dimensional
spinor carrier and an exterior-algebra carrier.

It does **not** construct a continuum spin geometry or prove a new
spinor/exterior-algebra classification theorem; it reuses the owner identity
from `InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DiracKahler

open InfoGeometry.OperatorAlgebra.ColeFury
open InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge

variable {R : Type*} [CommRing R]
variable {V_base : Type*} [AddCommGroup V_base] [Module R V_base]

/-- 
A formal equivalence between the 32-dimensional spinor carrier and an exterior
algebra carrier.
-/
abbrev SpinorExteriorEquiv (R : Type*) [CommRing R]
    (V_base : Type*) [AddCommGroup V_base] [Module R V_base] :=
  (Fin 32 → R) ≃ₗ[R] ExteriorAlgebra R V_base

namespace SpinorExteriorEquiv

abbrev equiv {R : Type*} [CommRing R]
    {V_base : Type*} [AddCommGroup V_base] [Module R V_base]
    (e : SpinorExteriorEquiv R V_base) :
    (Fin 32 → R) ≃ₗ[R] ExteriorAlgebra R V_base :=
  e

end SpinorExteriorEquiv

/--
The Dirac-Kähler operator transported to the 32-dimensional spinor carrier.
It is induced by pushing the operator identity through the supplied linear
equivalence.
-/
def spinDiracKahlerOp 
    (spinEq : SpinorExteriorEquiv (R:=R) (V_base:=V_base))
    (d dstar : Module.End R (ExteriorAlgebra R V_base)) : 
    Module.End R (Fin 32 → R) :=
  spinEq.equiv.symm.conj (diracKahlerOp d dstar)

/--
The Hodge-de Rham Laplacian transported to the spinor carrier.
-/
def spinLaplacianOp 
    (spinEq : SpinorExteriorEquiv (R:=R) (V_base:=V_base))
    (d dstar : Module.End R (ExteriorAlgebra R V_base)) : 
    Module.End R (Fin 32 → R) :=
  spinEq.equiv.symm.conj (hodgeDeRhamLaplacian d dstar)

/--
The finite operator identity `D² = Δ` survives transport to the spinor carrier.
-/
theorem spin_dirac_kahler_sq_eq_laplacian
    (spinEq : SpinorExteriorEquiv (R:=R) (V_base:=V_base))
    (d dstar : Module.End R (ExteriorAlgebra R V_base))
    (hd2 : d.comp d = 0) (hdstar2 : dstar.comp dstar = 0) :
    (spinDiracKahlerOp spinEq d dstar).comp (spinDiracKahlerOp spinEq d dstar) = 
    spinLaplacianOp spinEq d dstar := by
  apply LinearMap.ext
  intro v
  dsimp [spinDiracKahlerOp, spinLaplacianOp, LinearEquiv.conj]
  simp only [LinearEquiv.apply_symm_apply]
  have h_base := InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge.dirac_kahler_sq_eq_laplacian d dstar hd2 hdstar2
  have h_eval := LinearMap.congr_fun h_base (spinEq.equiv v)
  exact congr_arg spinEq.equiv.symm h_eval

end InfoGeometry.OperatorAlgebra.DiracKahler
