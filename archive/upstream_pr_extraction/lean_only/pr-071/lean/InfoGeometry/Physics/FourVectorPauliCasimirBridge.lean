import InfoGeometry.Physics.ChiralPoincareSouriauBridge
import InfoGeometry.Physics.LorentzBoostMinkowski
import InfoGeometry.Geometry.PauliParavectorBridge
import InfoGeometry.Physics.ZornMatrixSU3.Vector3
import InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge

/-!
# Four-vectors, finite Casimirs, spin projection, and cross products

This is a thin consolidation layer over the existing finite owners.  It does
not introduce a Poincare Lie algebra or a Pauli--Lubanski classification.  It
records the concrete statements that are already meaningful in the present
finite carriers:

* the Lorentz quadratic form is the mass Casimir and is boost invariant;
* Pauli soldering realizes the same quadratic form as a determinant;
* the two-state spin/helicity projection is an involution;
* the spatial cross product is the antisymmetric channel and is orthogonal to
  both inputs.

The scalar/vector-potential Maxwell equations remain owned by the exterior
calculus modules; this file only supplies the finite algebraic readouts.
-/

noncomputable section

namespace InfoGeometry.Physics.FourVectorPauliCasimirBridge

open InfoGeometry.Physics.LorentzBoostMinkowski
open InfoGeometry.Physics.ZornMatrixSU3

/-! ## Poincare mass Casimir on the real four-vector carrier -/

/-- The first Poincare Casimir in the finite momentum carrier. -/
def poincareMassCasimir (p : FourVector) : ℝ :=
  minkowskiSq p

@[simp] theorem poincareMassCasimir_eq_minkowskiPair (p : FourVector) :
    poincareMassCasimir p = minkowskiPair p p :=
  rfl

theorem poincareMassCasimir_boost_invariant (φ : ℝ) (p : FourVector) :
    poincareMassCasimir (boostX φ p) = poincareMassCasimir p := by
  exact boostX_preserves_minkowskiSq φ p

/-! ## Pauli soldering readout of the same Casimir -/

abbrev ComplexFourMomentum :=
  InfoGeometry.Physics.ChiralPoincareSouriauBridge.FourMomentum

def pauliMassCasimir (P : ComplexFourMomentum) : ℂ :=
  (InfoGeometry.Physics.ChiralPoincareSouriauBridge.pauliMomentum P).det

theorem pauliMassCasimir_eq_minkowskiSq (P : ComplexFourMomentum) :
    pauliMassCasimir P =
      InfoGeometry.Physics.ChiralPoincareSouriauBridge.minkowskiSq P := by
  exact InfoGeometry.Physics.ChiralPoincareSouriauBridge.det_pauliMomentum P

/-! ## Finite spin/helicity projection -/

abbrev SpinProjection :=
  InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.CircularMatrix

def helicityProjection : SpinProjection :=
  InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.circularHelicity

theorem helicityProjection_sq :
    helicityProjection * helicityProjection = 1 := by
  exact InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.circularHelicity_sq

/-! ## Cross product as the antisymmetric spatial channel -/

theorem crossProduct_orthogonal_left (x y : Fin 3 → ℝ) :
    ZornMatrixSU3.dotProduct x (ZornMatrixSU3.crossProduct x y) = 0 := by
  exact ZornMatrixSU3.dotProduct_crossProduct_left x y

theorem crossProduct_orthogonal_right (x y : Fin 3 → ℝ) :
    ZornMatrixSU3.dotProduct y (ZornMatrixSU3.crossProduct x y) = 0 := by
  exact ZornMatrixSU3.dotProduct_crossProduct_right x y

theorem crossProduct_is_antisymmetric (x y : Fin 3 → ℝ) :
    ZornMatrixSU3.crossProduct x y =
      -(ZornMatrixSU3.crossProduct y x) := by
  exact ZornMatrixSU3.crossProduct_anticomm x y

end InfoGeometry.Physics.FourVectorPauliCasimirBridge
