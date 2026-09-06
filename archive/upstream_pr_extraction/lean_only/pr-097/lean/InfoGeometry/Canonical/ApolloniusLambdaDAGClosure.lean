import Mathlib
import InfoGeometry.Arithmetic.RiemannApolloniusRiccatiBridge
import InfoGeometry.Arithmetic.RiemannApolloniusVectorFields
import InfoGeometry.Arithmetic.RiemannZetaGeometricDynamicsCorridor
import InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

/-!
# Apollonius lambda-DAG topological closure

This owner forgets any Riemann-hypothesis interpretation and records only the
compositional topology of theorem-owned constructions already present in the
repository.

A node is a typed stage in the construction.  `Edge a b` means that the target
stage is obtained from the source by a native theorem-owned construction or a
canonical packaging step.  `Reachable a b` is the reflexive-transitive closure,
so it is the free finite lambda-composition of these primitive arrows.

The graph is explicitly ranked.  Every primitive edge strictly increases rank,
which provides a topological-order certificate and prevents directed cycles.
-/

noncomputable section

namespace InfoGeometry.Canonical.ApolloniusLambdaDAGClosure

open InfoGeometry.Arithmetic.RiemannApolloniusRiccatiBridge
open InfoGeometry.Arithmetic.RiemannApolloniusVectorFields
open InfoGeometry.Arithmetic.RiemannZetaGeometricDynamicsCorridor
open InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

/-- The theorem-owned stages reachable from the corrected Apollonius seed. -/
inductive Node where
  | affineCoordinate
  | centeredCoordinate
  | reflectionParity
  | ratioCoordinate
  | ratioInversion
  | logarithmicScale
  | riccatiPolynomial
  | sl2Generator
  | rotationalField
  | dilationField
  | orthogonalSplit
  | criticalTangentNormal
  | unitCircleChart
  | apolloniusLeaf
  | fisherMetric
  | informationPotential
  | selfConcordantLyapunov
  | naturalGradientFlow
  | entropyGradient
  | metriplecticScalarFlow
  | dilationGroup
  | phaseCircleTransport
  | transferOperator
  deriving DecidableEq, Repr, Inhabited

/-- Primitive lambda/dependency arrows.  These are deliberately narrower than
mere conceptual adjacency. -/
inductive Edge : Node → Node → Prop where
  | affine_centered : Edge .affineCoordinate .centeredCoordinate
  | centered_reflection : Edge .centeredCoordinate .reflectionParity
  | reflection_ratio : Edge .reflectionParity .ratioCoordinate
  | ratio_inversion : Edge .ratioCoordinate .ratioInversion
  | centered_scale : Edge .centeredCoordinate .logarithmicScale
  | scale_riccati : Edge .logarithmicScale .riccatiPolynomial
  | riccati_sl2 : Edge .riccatiPolynomial .sl2Generator
  | scale_rotation : Edge .logarithmicScale .rotationalField
  | scale_dilation : Edge .logarithmicScale .dilationField
  | fields_orthogonal : Edge .rotationalField .orthogonalSplit
  | dilation_orthogonal : Edge .dilationField .orthogonalSplit
  | orthogonal_critical : Edge .orthogonalSplit .criticalTangentNormal
  | critical_circle : Edge .criticalTangentNormal .unitCircleChart
  | circle_apollonius : Edge .unitCircleChart .apolloniusLeaf
  | apollonius_fisher : Edge .apolloniusLeaf .fisherMetric
  | fisher_potential : Edge .fisherMetric .informationPotential
  | potential_lyapunov : Edge .informationPotential .selfConcordantLyapunov
  | lyapunov_gradient : Edge .selfConcordantLyapunov .naturalGradientFlow
  | gradient_entropy : Edge .naturalGradientFlow .entropyGradient
  | entropy_metriplectic : Edge .entropyGradient .metriplecticScalarFlow
  | critical_dilation : Edge .criticalTangentNormal .dilationGroup
  | dilation_phase : Edge .dilationGroup .phaseCircleTransport
  | phase_transfer : Edge .phaseCircleTransport .transferOperator

/-- Finite lambda-composition / graph reachability. -/
abbrev Reachable : Node → Node → Prop := Relation.ReflTransGen Edge

/-- One primitive arrow is reachable. -/
theorem edge_reachable {a b : Node} (h : Edge a b) : Reachable a b :=
  Relation.ReflTransGen.single h

/-- Reachability composes exactly as lambda-term composition. -/
theorem reachable_trans {a b c : Node}
    (hab : Reachable a b) (hbc : Reachable b c) : Reachable a c :=
  hab.trans hbc

/-- Explicit topological rank. -/
def rank : Node → Nat
  | .affineCoordinate => 0
  | .centeredCoordinate => 1
  | .reflectionParity => 2
  | .ratioCoordinate => 3
  | .ratioInversion => 4
  | .logarithmicScale => 3
  | .riccatiPolynomial => 4
  | .sl2Generator => 5
  | .rotationalField => 4
  | .dilationField => 4
  | .orthogonalSplit => 5
  | .criticalTangentNormal => 6
  | .unitCircleChart => 7
  | .apolloniusLeaf => 8
  | .fisherMetric => 9
  | .informationPotential => 10
  | .selfConcordantLyapunov => 11
  | .naturalGradientFlow => 12
  | .entropyGradient => 13
  | .metriplecticScalarFlow => 14
  | .dilationGroup => 7
  | .phaseCircleTransport => 8
  | .transferOperator => 9

/-- Every primitive edge is forward in the declared topological order. -/
theorem edge_rank_lt {a b : Node} (h : Edge a b) : rank a < rank b := by
  cases h <;> decide

/-- No primitive self-loop exists. -/
theorem edge_irrefl (a : Node) : ¬ Edge a a := by
  intro h
  have := edge_rank_lt h
  exact (Nat.lt_irrefl _ this)

/-! ## Concrete theorem witnesses behind the primitive graph -/

/-- Centering conjugates affine reflection to parity. -/
theorem lambda_centered_reflection (s : ℂ) :
    centered (1 - s) = -centered s :=
  centered_reflection s

/-- Reflection becomes inversion in the ratio chart. -/
theorem lambda_ratio_inversion
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    apolloniusRatio (1 - s) = (apolloniusRatio s)⁻¹ :=
  apolloniusRatio_reflection s hs0 hs1

/-- The inverse logarithmic scale is the Riccati polynomial. -/
theorem lambda_scale_riccati (z : ℂ) :
    centeredScale z =
      InfoGeometry.Canonical.ComplexRiccatiSL2.riccatiField 0 (1 / 4 : ℂ) 1 z :=
  centeredScale_eq_riccatiField z

/-- The two coordinate directions are orthogonal. -/
theorem lambda_vector_fields_orthogonal (sigma t : ℝ) :
    (rotationalField sigma t).1 * (dilationCoordinateField sigma t).1 +
      (rotationalField sigma t).2 * (dilationCoordinateField sigma t).2 = 0 :=
  rotational_dilation_orthogonal sigma t

/-- The phase field is tangent on the central leaf. -/
theorem lambda_phase_tangent (t : ℝ) :
    (rotationalField (1 / 2) t).1 = 0 :=
  rotationalField_criticalLine_transverse_zero t

/-- The scale coordinate field is normal on the central leaf. -/
theorem lambda_scale_normal (t : ℝ) :
    (dilationCoordinateField (1 / 2) t).2 = 0 :=
  dilationCoordinateField_criticalLine_longitudinal_zero t

/-- The native Cayley chart sends the central imaginary axis to the unit circle. -/
theorem lambda_unit_circle_chart (t : ℝ) :
    Complex.normSq
      (InfoGeometry.Topology.ProjectiveCayleyZetaBridge.cayley
        (Complex.I * (t : ℂ))) = 1 :=
  cayley_critical_line_to_unit_circle t

/-- The Apollonius Fisher metric is positive definite on nonzero tangent vectors. -/
theorem lambda_fisher_positive
    (st : InfoGeometry.Quantum.ApolloniusFisherInformation.ApolloniusState)
    (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    0 < InfoGeometry.Quantum.ApolloniusFisherInformation.
      apolloniusFisherQuadraticForm st v :=
  apollonius_fisher_positive st v hv

/-- The normalized log-generating potential is a globally strict
self-concordant Lyapunov function for its Hessian natural-gradient flow. -/
theorem lambda_global_selfConcordant_lyapunov
    (kappa x : ℝ) (hkappa : 0 < kappa) (hx : 0 < x) :=
  global_selfConcordant_lyapunov kappa x hkappa hx

/-- The native dilation group composes. -/
theorem lambda_dilation_group (t1 t2 x : ℝ) :
    InfoGeometry.Canonical.BerryKeatingDilations.dilationFlow t1
        (InfoGeometry.Canonical.BerryKeatingDilations.dilationFlow t2 x) =
      InfoGeometry.Canonical.BerryKeatingDilations.dilationFlow (t1 + t2) x :=
  dilation_group_law t1 t2 x

/-- The uniform transfer operator fixes the unit observable. -/
theorem lambda_transfer_unit {n : ℕ}
    (w : InfoGeometry.Quantum.RuellePerronFrobeniusTransferOperator.BitWord n) :
    InfoGeometry.Quantum.RuellePerronFrobeniusTransferOperator.transferOperator
      InfoGeometry.Quantum.RuellePerronFrobeniusTransferOperator.uniformPotential
      (fun _ => 1) w = 1 :=
  uniform_transfer_preserves_one w

/-! ## Topological reachability capstones -/

/-- The Riccati/sl2 branch is reachable from the affine coordinate seed. -/
theorem affine_reaches_sl2Generator :
    Reachable .affineCoordinate .sl2Generator := by
  apply reachable_trans (edge_reachable Edge.affine_centered)
  apply reachable_trans (edge_reachable Edge.centered_scale)
  apply reachable_trans (edge_reachable Edge.scale_riccati)
  exact edge_reachable Edge.riccati_sl2

/-- The information-geometric branch is reachable from the affine seed. -/
theorem affine_reaches_informationPotential :
    Reachable .affineCoordinate .informationPotential := by
  apply reachable_trans (edge_reachable Edge.affine_centered)
  apply reachable_trans (edge_reachable Edge.centered_scale)
  apply reachable_trans (edge_reachable Edge.scale_rotation)
  apply reachable_trans (edge_reachable Edge.fields_orthogonal)
  apply reachable_trans (edge_reachable Edge.orthogonal_critical)
  apply reachable_trans (edge_reachable Edge.critical_circle)
  apply reachable_trans (edge_reachable Edge.circle_apollonius)
  apply reachable_trans (edge_reachable Edge.apollonius_fisher)
  exact edge_reachable Edge.fisher_potential

/-- The globally strict Lyapunov node is reachable from the affine seed. -/
theorem affine_reaches_selfConcordantLyapunov :
    Reachable .affineCoordinate .selfConcordantLyapunov := by
  apply reachable_trans affine_reaches_informationPotential
  exact edge_reachable Edge.potential_lyapunov

/-- The Hessian natural-gradient flow is reachable from the affine seed. -/
theorem affine_reaches_naturalGradientFlow :
    Reachable .affineCoordinate .naturalGradientFlow := by
  apply reachable_trans affine_reaches_selfConcordantLyapunov
  exact edge_reachable Edge.lyapunov_gradient

/-- The scalar metriplectic branch is reachable from the affine seed. -/
theorem affine_reaches_metriplecticScalarFlow :
    Reachable .affineCoordinate .metriplecticScalarFlow := by
  apply reachable_trans affine_reaches_naturalGradientFlow
  apply reachable_trans (edge_reachable Edge.gradient_entropy)
  exact edge_reachable Edge.entropy_metriplectic

/-- The transfer-operator branch is reachable from the same central-leaf split. -/
theorem affine_reaches_transferOperator :
    Reachable .affineCoordinate .transferOperator := by
  apply reachable_trans (edge_reachable Edge.affine_centered)
  apply reachable_trans (edge_reachable Edge.centered_scale)
  apply reachable_trans (edge_reachable Edge.scale_rotation)
  apply reachable_trans (edge_reachable Edge.fields_orthogonal)
  apply reachable_trans (edge_reachable Edge.orthogonal_critical)
  apply reachable_trans (edge_reachable Edge.critical_dilation)
  apply reachable_trans (edge_reachable Edge.dilation_phase)
  exact edge_reachable Edge.phase_transfer

/-- Current maximal theorem-safe topological closure from the affine seed. -/
theorem current_topological_closure :
    Reachable .affineCoordinate .sl2Generator ∧
    Reachable .affineCoordinate .selfConcordantLyapunov ∧
    Reachable .affineCoordinate .metriplecticScalarFlow ∧
    Reachable .affineCoordinate .transferOperator :=
  ⟨affine_reaches_sl2Generator,
    affine_reaches_selfConcordantLyapunov,
    affine_reaches_metriplecticScalarFlow,
    affine_reaches_transferOperator⟩

end InfoGeometry.Canonical.ApolloniusLambdaDAGClosure

end noncomputable section
