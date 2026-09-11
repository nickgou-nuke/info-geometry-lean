import InfoGeometry.Canonical.Cl11CoordinateHestenesBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.QuaternionCl44TwistedConjugationLift

set_option autoImplicit false

/-!
# Hestenes split quaternions soldered into the `Cl(4,4)` operator model

This module composes two maintained representation chains.  The coordinate
equivalence identifies the native `Cl(1,1)` packet with the Hestenes
split-quaternion carrier; the fixed-colour soldering identifies that packet
with an associative `(2,2)` plane in the split-octonionic `(4,4)` carrier.
The resulting Dirac readout uses the existing sixteen-dimensional real gamma
representation.
-/

noncomputable section

namespace InfoGeometry.Optics.HestenesCl11Cl44OperatorBridge

open InfoGeometry.Canonical.Cl11CoordinateHestenesBridge
open InfoGeometry.Canonical.HestenesDiracAdjoint
open InfoGeometry.Clifford.Cl11CoordinateAlgebra
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation
open InfoGeometry.Optics.Cl11QuaternionTwistedConjugationBridge
open InfoGeometry.Optics.QuaternionCl44DiracOperatorBridge
open CanonicalZornRealSpin44

/-- A Hestenes split quaternion soldered into one fixed-colour associative
plane of the global quaternionic `(4+4)` coordinate carrier. -/
def hestenesCartesian (i : Fin 3) (q : HestenesCl11) : CartesianCoordinates :=
  cl11Cartesian i (ofHestenes q)

/-- The existing real `Cl(4,4)` gamma representation evaluated on the
Hestenes-soldered coordinate. -/
def hestenesGamma (i : Fin 3) (q : HestenesCl11) : DiracEnd44 :=
  cartesianGammaLinear (hestenesCartesian i q)

/-- Ordered Hestenes basis `1,e,f,ef`. -/
def hestenesBasis (a : Fin 4) : HestenesCl11 :=
  match a with
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0⟩
  | 3 => ⟨0, 0, 0, 1⟩

/-- Diagonal signature attached to the ordered basis `1,e,f,ef`. -/
def hestenesSignature (a : Fin 4) : ℝ :=
  match a with
  | 0 => 1
  | 1 => -1
  | 2 => 1
  | 3 => -1

/-- The Hestenes basis exposes the split-quaternion `(2,2)` signature. -/
@[simp] theorem normSq_hestenesBasis (a : Fin 4) :
    SplitQuaternion.normSq (hestenesBasis a) =
      hestenesSignature a := by
  fin_cases a <;> norm_num [hestenesBasis, hestenesSignature,
    SplitQuaternion.normSq]

@[simp] theorem ofHestenes_cliffordConjugation (q : HestenesCl11) :
    ofHestenes (SplitQuaternion.cliffordConjugation q) =
      cliffordConjugate (ofHestenes q) := by
  apply coordinateEquiv.injective
  change toHestenes (ofHestenes (SplitQuaternion.cliffordConjugation q)) =
    toHestenes (cliffordConjugate (ofHestenes q))
  rw [toHestenes_cliffordConjugate]
  simp only [toHestenes_ofHestenes]

/-- Global split-octonion conjugation restricts to the canonical Hestenes
split-quaternion Clifford conjugation on every fixed-colour plane. -/
@[simp] theorem cartesianTwistedConj_hestenesCartesian
    (i : Fin 3) (q : HestenesCl11) :
    cartesianTwistedConj (hestenesCartesian i q) =
      hestenesCartesian i (SplitQuaternion.cliffordConjugation q) := by
  rw [hestenesCartesian, cartesianTwistedConj_cl11Cartesian,
    hestenesCartesian, ofHestenes_cliffordConjugation]

/-- The global `(4,4)` quadratic form restricts exactly to the Hestenes
split-quaternion norm of signature `(2,2)`. -/
@[simp] theorem cartesianQuadratic44_hestenesCartesian
    (i : Fin 3) (q : HestenesCl11) :
    cartesianQuadratic44 (hestenesCartesian i q) =
      SplitQuaternion.normSq q := by
  rw [hestenesCartesian, cartesianQuadratic44_apply,
    normDifference_cl11Cartesian]
  simpa using (normSq_toHestenes (ofHestenes q)).symm

/-- Polarization of the ambient `(4,4)` form restricts to twice the Hestenes
Krein bilinear form. -/
theorem cartesianNormPolar_hestenesCartesian
    (i : Fin 3) (q r : HestenesCl11) :
    cartesianNormPolar (hestenesCartesian i q) (hestenesCartesian i r) =
      2 * hestenesBilinear q r := by
  rw [hestenesCartesian, hestenesCartesian,
    cartesianNormPolar_cl11Cartesian]
  simpa using congrArg (fun x : ℝ => 2 * x)
    (hestenesBilinear_toHestenes (ofHestenes q) (ofHestenes r)).symm

/-- The soldered Hestenes gamma is a genuine Clifford generator: its square
is the represented `(2,2)` norm. -/
theorem hestenesGamma_sq (i : Fin 3) (q : HestenesCl11) :
    hestenesGamma i q * hestenesGamma i q =
      algebraMap ℝ DiracEnd44 (SplitQuaternion.normSq q) := by
  rw [hestenesGamma, hestenesCartesian, cl11Cartesian_gamma_sq]
  congr 1

/-- Full polarized Dirac relation on the Hestenes split-quaternion plane. -/
theorem hestenesGamma_anticommutator
    (i : Fin 3) (q r : HestenesCl11) :
    hestenesGamma i q * hestenesGamma i r +
        hestenesGamma i r * hestenesGamma i q =
      algebraMap ℝ DiracEnd44 (2 * hestenesBilinear q r) := by
  rw [hestenesGamma, hestenesGamma, hestenesCartesian, hestenesCartesian,
    cl11Cartesian_gamma_anticommutator]
  congr 1

/-- The transported split-octonion conjugation is read by the maintained
sixteen-dimensional representation as the gamma of the Hestenes Clifford
conjugate. -/
theorem represented_twistedConj_hestenesGamma
    (i : Fin 3) (q : HestenesCl11) :
    realClifford44Representation
        (CliffordAlgebra.ι realQuadratic44
          (cartesianToRealSplit44
            (cartesianTwistedConj (hestenesCartesian i q)))) =
      hestenesGamma i (SplitQuaternion.cliffordConjugation q) := by
  rw [hestenesCartesian, cartesianTwistedConj_cl11Cartesian]
  change realClifford44Representation
      (CliffordAlgebra.ι realQuadratic44
        (cartesianToRealSplit44
          (cl11Cartesian i (cliffordConjugate (ofHestenes q))))) =
    cartesianGammaLinear
      (cl11Cartesian i
        (ofHestenes (SplitQuaternion.cliffordConjugation q)))
  rw [ofHestenes_cliffordConjugation, realClifford44Representation_ι]
  rfl

/-- Each of the four Hestenes axes becomes a genuine represented Clifford
generator with the corresponding split signature sign. -/
theorem hestenesGamma_basis_sq (i : Fin 3) (a : Fin 4) :
    hestenesGamma i (hestenesBasis a) * hestenesGamma i (hestenesBasis a) =
      algebraMap ℝ DiracEnd44 (hestenesSignature a) := by
  rw [hestenesGamma_sq, normSq_hestenesBasis]

/-- One theorem records the complete Hestenes → split-octonion → `Cl(4,4)`
operator closure: the correct canonical involution, the `(2,2)` norm, and the
Dirac anticommutator are transported by the same soldering map. -/
theorem hestenes_cl11_cl44_operator_packet
    (i : Fin 3) (q r : HestenesCl11) :
    cartesianTwistedConj (hestenesCartesian i q) =
        hestenesCartesian i (SplitQuaternion.cliffordConjugation q) ∧
      cartesianQuadratic44 (hestenesCartesian i q) =
        SplitQuaternion.normSq q ∧
      hestenesGamma i q * hestenesGamma i r +
          hestenesGamma i r * hestenesGamma i q =
        algebraMap ℝ DiracEnd44 (2 * hestenesBilinear q r) := by
  exact ⟨cartesianTwistedConj_hestenesCartesian i q,
    cartesianQuadratic44_hestenesCartesian i q,
    hestenesGamma_anticommutator i q r⟩

end InfoGeometry.Optics.HestenesCl11Cl44OperatorBridge
