import Mathlib.Algebra.Group.Defs

/-!
# InfoGeometry.Canonical.ErlangenOperator2

Erlangen Operator 2.0:
geometry as invariant tensorial data under an operator symmetry action.

This file is a pure synthesis layer. It does not construct:

* split-Clifford CAR source currents;
* split-octonion projective incidence geometry;
* affine current algebra;
* Sugawara/Virasoro representations;
* concrete `G₂(2)` or `Spin(5,5)` coadjoint-orbit models.

Those remain separate owner branches.

Repository policy boundary:
this file packages invariance predicates under supplied group actions and does
not assert trajectory-level entropy production statements (`dS/dt = 0`).
-/

noncomputable section

namespace InfoGeometry.Canonical.ErlangenOperator2

/--
A scalar functional is a generalized Casimir for a symmetry action if it is
constant along all symmetry directions.
-/
def IsGeneralizedCasimir
    {𝕜 G State : Type*}
    (S : State → 𝕜)
    (stateAct : G → State → State) : Prop :=
  ∀ g s, S (stateAct g s) = S s

/--
A response tensor is geometry-invariant if it is preserved by the symmetry
action on both the state/base point and observable/tangent slots.
-/
def IsGeometryInvariant
    {𝕜 G State Obs : Type*}
    (metric : State → Obs → Obs → 𝕜)
    (stateAct : G → State → State)
    (obsAct : G → Obs → Obs) : Prop :=
  ∀ g A B s,
    metric (stateAct g s) (obsAct g A) (obsAct g B) = metric s A B

/--
Onsager/J reciprocity condition.
-/
def HasJReciprocity
    {𝕜 State Obs : Type*}
    (pairing : State → Obs → Obs → 𝕜)
    (J : Obs → Obs) : Prop :=
  ∀ A B s, pairing s A B = pairing s (J B) (J A)

/--
Erlangen Operator 2.0 datum.

This packages symmetry actions and invariant readouts without claiming that any
lower layer constructs them.
-/
structure ErlangenOperatorDatum
    (𝕜 G State Obs : Type*) [Group G] where
  entropy : State → 𝕜
  responseMetric : State → Obs → Obs → 𝕜
  onsagerPairing : State → Obs → Obs → 𝕜
  stateAct : G → State → State
  obsAct : G → Obs → Obs
  casimirJ : Obs → Obs
  stateAct_one : ∀ s, stateAct 1 s = s
  stateAct_mul : ∀ g h s, stateAct (g * h) s = stateAct g (stateAct h s)
  obsAct_one : ∀ A, obsAct 1 A = A
  obsAct_mul : ∀ g h A, obsAct (g * h) A = obsAct g (obsAct h A)
  entropy_invariant : IsGeneralizedCasimir entropy stateAct
  response_invariant : IsGeometryInvariant responseMetric stateAct obsAct
  onsager_reciprocity : HasJReciprocity onsagerPairing casimirJ

namespace ErlangenOperatorDatum

variable {𝕜 G State Obs : Type*} [Group G]

/--
Bundled closure data for Erlangen Operator 2.0.
-/
structure ErlangenOperatorGeometry
    (E : ErlangenOperatorDatum 𝕜 G State Obs) where
  entropy_is_casimir : IsGeneralizedCasimir E.entropy E.stateAct
  response_is_geometry : IsGeometryInvariant E.responseMetric E.stateAct E.obsAct
  onsager_has_J_reciprocity : HasJReciprocity E.onsagerPairing E.casimirJ

/--
Main Erlangen Operator 2.0 theorem:
geometry is invariant tensorial data under symmetry action.
-/
theorem geometry_as_symmetry_invariants
    (E : ErlangenOperatorDatum 𝕜 G State Obs) :
    ErlangenOperatorGeometry E where
  entropy_is_casimir := E.entropy_invariant
  response_is_geometry := E.response_invariant
  onsager_has_J_reciprocity := E.onsager_reciprocity

/-- Readout: entropy is invariant. -/
theorem entropy_is_generalized_casimir
    (E : ErlangenOperatorDatum 𝕜 G State Obs) :
    IsGeneralizedCasimir E.entropy E.stateAct :=
  E.entropy_invariant

/-- Readout: response metric is invariant geometry. -/
theorem responseMetric_is_geometryInvariant
    (E : ErlangenOperatorDatum 𝕜 G State Obs) :
    IsGeometryInvariant E.responseMetric E.stateAct E.obsAct :=
  E.response_invariant

/-- Readout: Onsager pairing satisfies J-reciprocity. -/
theorem onsagerPairing_has_J_reciprocity
    (E : ErlangenOperatorDatum 𝕜 G State Obs) :
    HasJReciprocity E.onsagerPairing E.casimirJ :=
  E.onsager_reciprocity

/-- Alias theorem name used by downstream bridge files. -/
theorem erlangen_operator_geometry_closure
    (E : ErlangenOperatorDatum 𝕜 G State Obs) :
    ErlangenOperatorGeometry E :=
  geometry_as_symmetry_invariants E

end ErlangenOperatorDatum

end InfoGeometry.Canonical.ErlangenOperator2
