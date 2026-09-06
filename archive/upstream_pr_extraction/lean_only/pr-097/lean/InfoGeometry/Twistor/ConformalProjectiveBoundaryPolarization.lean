import InfoGeometry.Twistor.ChiralTwistorPeirceSheets
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
import InfoGeometry.Geometry.ParavectorZornBoundary
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-!
# Conformal/projective null boundary from the polarized Zorn norm

This owner isolates the exact algebraic content of the boundary statement.
A Penrose twistor is first transported by the already established real-linear
map into the canonical split-octonion/Zorn carrier.  Its boundary defect is the
Zorn reduced norm.

The circular Peirce formula shows that nullness is intrinsically a cross-sheet
condition: the positive scalar/vector coordinates are paired with the negative
scalar/vector coordinates.  This file does not identify braid/anyon states with
four-vectors and does not derive mass or zitterbewegung dynamics from nullness.
Those are separate theorem targets.
-/

noncomputable section

namespace InfoGeometry.Twistor.ConformalProjectiveBoundaryPolarization

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
open InfoGeometry.Twistor.ChiralTwistorPeirceSheets
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Geometry.ParavectorZornBoundary
open InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-- The scalar defect measuring departure from the split-octonion null cone. -/
def twistorBoundaryDefect (Z : Twistor4) : ℝ :=
  InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (twistorRealEquivZorn Z)

/-- The affine null-boundary condition before projectivization. -/
def IsTwistorBoundaryNull (Z : Twistor4) : Prop :=
  twistorBoundaryDefect Z = 0

/-- Off-boundary means exactly nonzero reduced-norm defect. -/
def IsTwistorOffBoundary (Z : Twistor4) : Prop :=
  twistorBoundaryDefect Z ≠ 0

@[simp] theorem isTwistorOffBoundary_iff (Z : Twistor4) :
    IsTwistorOffBoundary Z ↔ ¬ IsTwistorBoundaryNull Z := by
  rfl

/-- The boundary defect may be read after the existing chiral-sheet
factorization of the twistor-to-Zorn map. -/
theorem twistorBoundaryDefect_sheet_factorization (Z : Twistor4) :
    twistorBoundaryDefect Z =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (plusZornMap Z.1 + minusZornMap Z.2) := by
  rw [twistorBoundaryDefect, twistor_zorn_sheet_decomposition]

/-- Exact cross-sheet Peirce equation for the twistor null boundary.

The repository ordering is `u₊ | V₊ | u₋ | V₋`.  Thus nullness is the balance
`c₊ c₋ = <v₊,v₋>` and not a condition on either chiral sheet in isolation. -/
theorem twistorBoundaryNull_iff_peirce_sheet_balance (Z : Twistor4) :
    IsTwistorBoundaryNull Z ↔
      circularCoordinate
          (cartesianZornLinearEquiv.symm (twistorRealEquivZorn Z)) 0 *
          circularCoordinate
            (cartesianZornLinearEquiv.symm (twistorRealEquivZorn Z)) 4 =
        circularCoordinate
            (cartesianZornLinearEquiv.symm (twistorRealEquivZorn Z)) 1 *
            circularCoordinate
              (cartesianZornLinearEquiv.symm (twistorRealEquivZorn Z)) 5 +
          circularCoordinate
              (cartesianZornLinearEquiv.symm (twistorRealEquivZorn Z)) 2 *
              circularCoordinate
                (cartesianZornLinearEquiv.symm (twistorRealEquivZorn Z)) 6 +
          circularCoordinate
              (cartesianZornLinearEquiv.symm (twistorRealEquivZorn Z)) 3 *
              circularCoordinate
                (cartesianZornLinearEquiv.symm (twistorRealEquivZorn Z)) 7 := by
  change InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (twistorRealEquivZorn Z) = 0 ↔ _
  exact circularPeirceBasis_null_iff (twistorRealEquivZorn Z)

/-- The finite paravector boundary map has exactly the same null equation in
its explicit Zorn realization. -/
theorem paravector_null_iff_zorn_boundary_null (v : Minkowski4) :
    v.IsNull ↔ IsZornNull (zornBoundaryOfMinkowski4 v) := by
  exact (isZornNull_boundary_iff_isNull v).symm

/-- The same scalar which vanishes on the null boundary becomes `m²` on a
mass shell.  This is an invariant readout, not a derivation of mass dynamics. -/
theorem paravector_mass_shell_iff_zorn_norm
    (p : Minkowski4) (m : ℝ) :
    p.OnMassShell m ↔ zornNorm (zornBoundaryOfMinkowski4 p) = m ^ 2 := by
  rw [Minkowski4.OnMassShell, zornNorm_boundary_eq_minkowski_q]

/-- The Pauli determinant, Minkowski quadratic form, and Zorn boundary norm are
three readouts of the same finite boundary defect. -/
theorem paravector_boundary_defect_triple_readout (v : Minkowski4) :
    zornNorm (zornBoundaryOfMinkowski4 v) = v.q ∧
      Matrix.det (pauliMatrix v) = ((v.q : ℝ) : ℂ) := by
  exact ⟨zornNorm_boundary_eq_minkowski_q v, det_pauliMatrix v⟩

end InfoGeometry.Twistor.ConformalProjectiveBoundaryPolarization
