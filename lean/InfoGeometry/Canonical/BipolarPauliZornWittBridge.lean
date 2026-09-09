import InfoGeometry.Canonical.BipolarPauliHestenesSolderingBridge
import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Lie.SplitOctonionCircularMinkowskiPauliBridge
import Mathlib.Tactic

/-!
# Corrected Pauli--Zorn--Witt quadratic bridge

A real Minkowski paravector has several useful finite coordinate realizations:

* its Hermitian Pauli matrix;
* the diagonal slice of the repository's circular `(4,4)` Witt carrier;
* a four-dimensional quadratic slice of the real Zorn matrix carrier.

The informal source placed `(px, py, 0)` in one Zorn off-diagonal slot and
`(px, -py, 0)` in the other, but their ordinary real dot product is then
`px²-py²`.  To recover the standard transverse Euclidean contribution
`px²+py²`, the real Zorn slice used here places the same transverse vector in
both slots.

The resulting theorem is equality of quadratic readouts.  It is not an algebra
isomorphism between the associative algebra `M₂(ℂ)` and the nonassociative Zorn
algebra, and no exceptional-group action is inferred.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarPauliZornWittBridge

open InfoGeometry.Canonical.BipolarPauliHestenesSolderingBridge
open InfoGeometry.Canonical.BipolarCartanLorentzBridge
open InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Lie.SplitOctonionCircularWittForm


/-- Real four-coordinate readout of a Pauli paravector. -/
def pauliMomentumCoordinates (P : PauliParavector) : Fin 4 → ℝ :=
  ![P.energy, P.px, P.py, P.pz]

/-- Transverse vector used in both off-diagonal Zorn slots. -/
def transverseVector (P : PauliParavector) : InfoGeometry.Algebra.Vec3 ℝ :=
  ![P.px, P.py, 0]

/-- Sign-reflected transverse vector from the informal proposal. -/
def reflectedTransverseVector (P : PauliParavector) :
    InfoGeometry.Algebra.Vec3 ℝ :=
  ![P.px, -P.py, 0]

/-- Self-pairing of the corrected transverse vector is the Euclidean
transverse square. -/
theorem transverseVector_dot_self (P : PauliParavector) :
    Vec3.dot (transverseVector P) (transverseVector P) =
      P.px ^ 2 + P.py ^ 2 := by
  simp [transverseVector, Vec3.dot]
  ring

/-- Pairing with the sign-reflected slot instead produces split signature in
the transverse plane. -/
theorem transverseVector_dot_reflected (P : PauliParavector) :
    Vec3.dot (transverseVector P) (reflectedTransverseVector P) =
      P.px ^ 2 - P.py ^ 2 := by
  simp [transverseVector, reflectedTransverseVector, Vec3.dot]
  ring

/-- Correct real Zorn slice of a Pauli paravector. -/
def pauliZorn (P : PauliParavector) : InfoGeometry.Algebra.ZornMatrix ℝ where
  a := P.energy + P.pz
  v := transverseVector P
  w := transverseVector P
  b := P.energy - P.pz

/-- The Zorn quadratic norm of the corrected slice is the Minkowski norm. -/
theorem zornNorm_pauliZorn (P : PauliParavector) :
    ZornMatrix.zornNorm (pauliZorn P) = P.minkowskiNormSq := by
  simp [ZornMatrix.zornNorm, pauliZorn, transverseVector,
    Vec3.dot, PauliParavector.minkowskiNormSq]
  ring

/-- The circular Witt diagonal slice carries the same Minkowski quadratic
readout. -/
theorem circularWittQuadratic_pauli (P : PauliParavector) :
    circularWittQuadratic
        (minkowskiDiagonalEmbedding (pauliMomentumCoordinates P)) =
      P.minkowskiNormSq := by
  rw [circularWittQuadratic_minkowskiDiagonal]
  simp [pauliMomentumCoordinates, PauliParavector.minkowskiNormSq]
  ring

/-- Canonical Pauli determinant equals the corrected Zorn norm. -/
theorem pauliMatrix_det_eq_zornNorm (P : PauliParavector) :
    Matrix.det P.pauliMatrix =
      ((ZornMatrix.zornNorm (pauliZorn P) : ℝ) : ℂ) := by
  rw [zornNorm_pauliZorn,
    PauliParavector.det_pauliMatrix_eq_minkowskiNormSq]

/-- Canonical Pauli determinant equals the circular Witt diagonal quadratic
readout. -/
theorem pauliMatrix_det_eq_circularWittQuadratic (P : PauliParavector) :
    Matrix.det P.pauliMatrix =
      (circularWittQuadratic
        (minkowskiDiagonalEmbedding (pauliMomentumCoordinates P)) : ℂ) := by
  rw [circularWittQuadratic_pauli,
    PauliParavector.det_pauliMatrix_eq_minkowskiNormSq]

/-- The bipolar `SL₂(ℂ)` Cartan action preserves the corrected Zorn quadratic
readout of the underlying Pauli paravector. -/
theorem bipolarSolderingAction_det_eq_zornNorm
    (s : ℂ) (P : PauliParavector) :
    Matrix.det (bipolarSolderingAction s (pauliHermitian P)).mat =
        ((ZornMatrix.zornNorm (pauliZorn P) : ℝ) : ℂ) := by
  rw [bipolarSolderingAction_pauli_det, zornNorm_pauliZorn]

/-- The same transformed determinant equals the circular Witt diagonal
quadratic readout. -/
theorem bipolarSolderingAction_det_eq_circularWittQuadratic
    (s : ℂ) (P : PauliParavector) :
    Matrix.det (bipolarSolderingAction s (pauliHermitian P)).mat =
      (circularWittQuadratic
        (minkowskiDiagonalEmbedding (pauliMomentumCoordinates P)) : ℂ) := by
  rw [bipolarSolderingAction_pauli_det, circularWittQuadratic_pauli]

/-- Compact Pauli--Zorn--Witt invariant packet. -/
theorem bipolar_pauli_zorn_witt_packet
    (s : ℂ) (P : PauliParavector) :
    ZornMatrix.zornNorm (pauliZorn P) = P.minkowskiNormSq ∧
      circularWittQuadratic
          (minkowskiDiagonalEmbedding (pauliMomentumCoordinates P)) =
        P.minkowskiNormSq ∧
      Matrix.det (bipolarSolderingAction s (pauliHermitian P)).mat =
        ((ZornMatrix.zornNorm (pauliZorn P) : ℝ) : ℂ) ∧
      Matrix.det (bipolarSolderingAction s (pauliHermitian P)).mat =
        (circularWittQuadratic
          (minkowskiDiagonalEmbedding (pauliMomentumCoordinates P)) : ℂ) := by
  exact ⟨zornNorm_pauliZorn P,
    circularWittQuadratic_pauli P,
    bipolarSolderingAction_det_eq_zornNorm s P,
    bipolarSolderingAction_det_eq_circularWittQuadratic s P⟩

end InfoGeometry.Canonical.BipolarPauliZornWittBridge
