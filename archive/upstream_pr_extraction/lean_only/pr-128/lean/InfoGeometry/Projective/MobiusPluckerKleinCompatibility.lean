import InfoGeometry.Quantum.MobiusSL2CRealification
import InfoGeometry.Projective.Quadrics.PluckerKlein

/-!
# Möbius action on the finite Plücker/Klein readout

The realified `SL(2,ℂ)` action is applied to two real carrier vectors and
then read in Plücker coordinates.  The Klein relation follows from
decomposability; this file does not claim a Grassmannian quotient or an
amplituhedron positivity theorem.
-/

namespace InfoGeometry.Projective.MobiusPluckerKleinCompatibility

open InfoGeometry.Projective.Quadrics.PluckerKlein
open InfoGeometry.Quantum.DualFlatKreinGraph
open InfoGeometry.Quantum.MobiusSL2CRealification

abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

noncomputable def realifiedPiAction (g : SL2C) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  (EuclideanSpace.equiv (Fin 4) ℝ)
    (realifiedSL2C g ((EuclideanSpace.equiv (Fin 4) ℝ).symm x))

theorem realifiedPiAction_plucker_Klein
    (g : SL2C) (x y : Fin 4 → ℝ) :
    KleinRel
      (pluckerCoord (realifiedPiAction g x) (realifiedPiAction g y) 0 1)
      (pluckerCoord (realifiedPiAction g x) (realifiedPiAction g y) 0 2)
      (pluckerCoord (realifiedPiAction g x) (realifiedPiAction g y) 0 3)
      (pluckerCoord (realifiedPiAction g x) (realifiedPiAction g y) 1 2)
      (pluckerCoord (realifiedPiAction g x) (realifiedPiAction g y) 1 3)
      (pluckerCoord (realifiedPiAction g x) (realifiedPiAction g y) 2 3) := by
  exact plucker_coordinates_satisfy_KleinRel
    (realifiedPiAction g x) (realifiedPiAction g y)

end InfoGeometry.Projective.MobiusPluckerKleinCompatibility
