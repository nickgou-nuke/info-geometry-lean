import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearKleinParameterBundle
import InfoGeometry.MassSpectrometry.DirectedOperatorDoubling
import InfoGeometry.Topology.WallpaperKleinBottlePresentation

/-!
# Nuclear Klein holonomy, spectroscopy grading, and the Klein presentation

This module records a cross-corridor structural packet already supported by
independent theorem owners:

* nuclear operator-valued Soloviev fields transform under the finite Klein
  glide by internal parity conjugation;
* doubled mass-spectrometry transfer operators are odd under their native
  chiral grading;
* the repository's concrete `pg` wallpaper action satisfies the Klein
  presentation relation `G T_y G⁻¹ = T_y⁻¹`.

These are packaged together only as structural manifestations of involutive /
orientation-reversing algebra.  No theorem here identifies the nuclear
parameter quotient with the mass-spectrometry state space, identifies either
parity matrix with the wallpaper glide, or derives a physical Klein topology
for an instrument.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearKleinPresentationOperatorBridge

open InfoGeometry.Physics.NuclearKleinParameterBundle
open InfoGeometry.Physics.NuclearOperatorSuperSoloviev
open InfoGeometry.Physics.NuclearInternalExternalParityFactorization
open InfoGeometry.MassSpectrometry
open InfoGeometry.Topology.Wallpaper
open InfoGeometry.Topology.WallpaperKleinBottlePresentation

variable {A : Type*} [Ring A]

/-- The repository's concrete wallpaper action supplies the Klein relation. -/
theorem wallpaper_klein_relation (p : Lattice2D) :
    concretePG.G (concretePG.T_y (concretePG.G.symm p)) =
      concretePG.T_y.symm p :=
  concrete_kleinBottlePresentation_relation p

/-- Cross-domain theorem packet.  Each conjunct is owned independently and no
carrier identification is asserted. -/
theorem nuclear_spectroscopy_klein_presentation_packet
    {P : InternalParity A}
    (H : KleinEquivariantHamiltonian P)
    (p : ParameterCell)
    {n : ℕ}
    (K : Matrix (Fin n) (Fin n) ℝ)
    (q : Lattice2D) :
    internalParity P * H.blockAt p * internalParity P =
        H.blockAt (InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient.glide p) ∧
      gradingMatrix n * doubledOperator K * gradingMatrix n =
        -doubledOperator K ∧
      concretePG.G (concretePG.T_y (concretePG.G.symm q)) =
        concretePG.T_y.symm q := by
  refine ⟨H.internalParity_holonomy p, ?_, wallpaper_klein_relation q⟩
  exact grading_conjugates_doubledOperator_to_neg K

/-- The two operator involutions relevant to the packet square to identity.
This does not identify their carriers or their physical meaning. -/
theorem nuclear_and_spectroscopy_involutions_packet
    {P : InternalParity A} (n : ℕ) :
    internalParity P * internalParity P = (1 : Block2 A) ∧
      gradingMatrix n * gradingMatrix n = 1 :=
  ⟨internalParity_sq P, gradingMatrix_sq n⟩

end InfoGeometry.Physics.NuclearKleinPresentationOperatorBridge

end noncomputable section
