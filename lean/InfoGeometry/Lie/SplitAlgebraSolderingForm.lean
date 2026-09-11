import InfoGeometry.Lie.SplitOctonionCircularHyperbolicZornFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Soldering form for the canonical split-octonion carrier

The circular Peirce basis identifies the native split-octonion carrier with
its eight-dimensional split coordinate model.  This is the algebraic
soldering form: it is a linear equivalence, and the flow covariance theorem
states that the coordinate action is the pullback of the native flow.

This owner does not identify the algebraic carrier with a manifold tangent
bundle.  Such an identification requires a separately specified base and
tangent family.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitAlgebraSolderingForm

open InfoGeometry.Lie.SplitOctonionCircularHyperbolicZornFlow
open InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
open InfoGeometry.Lie.SplitOctonionCircularNormCone
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.ZornMatrix

abbrev SplitCarrier := InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.CZ
abbrev SplitCoordinates := InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow.Coord

/-- The circular Peirce soldering form of the canonical split carrier. -/
noncomputable def canonicalSoldering : SplitCarrier ≃ₗ[ℝ] SplitCoordinates :=
  circularPeirceBasis.equivFun

@[simp] theorem canonicalSoldering_apply (X : SplitCarrier) :
    canonicalSoldering X = circularPeirceBasis.equivFun X := rfl

@[simp] theorem canonicalSoldering_symm_apply (x : SplitCoordinates) :
    canonicalSoldering.symm x = circularPeirceBasis.equivFun.symm x := rfl

theorem canonicalSoldering_roundtrip (X : SplitCarrier) :
    canonicalSoldering.symm (canonicalSoldering X) = X := by
  exact canonicalSoldering.symm_apply_apply X

theorem canonicalSoldering_coordinate_roundtrip (x : SplitCoordinates) :
    canonicalSoldering (canonicalSoldering.symm x) = x := by
  exact canonicalSoldering.apply_symm_apply x

theorem canonicalSoldering_norm_pullback (X : SplitCarrier) :
    detZ realCrossProduct3 X = circularNormQuad (canonicalSoldering X) := by
  rw [circularNorm_eq X, canonicalSoldering_apply,
    circularPeirceBasis_coordinate_eq_equivFun]
  rfl

/-! The soldering form identifies the split null cone with the coordinate
    null cone.  This is the zero-locus form of the quadratic pullback above. -/
theorem canonicalSoldering_null_cone (X : SplitCarrier) :
    detZ realCrossProduct3 X = 0 ↔ circularNormQuad (canonicalSoldering X) = 0 := by
  rw [← canonicalSoldering_norm_pullback]

theorem canonicalSoldering_flow_equivariant (t : ℝ) (X : SplitCarrier) :
    canonicalSoldering (hyperbolicFlowZorn t X) =
      hyperbolicFlowCoordinate t (canonicalSoldering X) := by
  rw [canonicalSoldering_apply, hyperbolicFlowZorn_apply,
    canonicalSoldering_apply, LinearEquiv.apply_symm_apply]

theorem canonicalSoldering_flow_preserves_norm (t : ℝ) (X : SplitCarrier) :
    circularNormQuad (canonicalSoldering (hyperbolicFlowZorn t X)) =
      circularNormQuad (canonicalSoldering X) := by
  rw [canonicalSoldering_flow_equivariant]
  exact circularNormQuad_hyperbolicFlow t (canonicalSoldering X)

theorem canonicalSoldering_flow_preserves_null_cone (t : ℝ) (X : SplitCarrier) :
    detZ realCrossProduct3 (hyperbolicFlowZorn t X) = 0 ↔
      detZ realCrossProduct3 X = 0 := by
  constructor
  · intro h
    apply (canonicalSoldering_null_cone X).mpr
    rw [← canonicalSoldering_flow_preserves_norm t X]
    exact (canonicalSoldering_null_cone (hyperbolicFlowZorn t X)).mp h
  · intro h
    apply (canonicalSoldering_null_cone (hyperbolicFlowZorn t X)).mpr
    rw [canonicalSoldering_flow_preserves_norm t X]
    exact (canonicalSoldering_null_cone X).mp h

end InfoGeometry.Lie.SplitAlgebraSolderingForm
