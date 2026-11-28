# Arnold flow, derivative pushforward, and Erlangen closure

## Intake and source provenance

The 2026-11-28 request proposes five maps: conjugation/pushforward, invariant
closure, adjoining invariants, scale separation, and infinitesimal bracket
closure. Its requested implementation is an actual Mathlib group action on
fields and one-parameter motions, a derivative compatibility theorem, and a
volume-invariant specialization of the Erlangen Galois closure.

The implementation baseline is current upstream main
`e2aa23c786c63c8992e8936346ed5f7782e4e164`, observed through the live Git remote
on 2026-11-28. The initial GitHub branch snapshot was stale. Source recovery
began at `05b23a2133cc3daf6f477559acc7b09de5979a3f`, then task-owned changes were
transferred onto the newer main while preserving its other changes. Current
main contains the prerequisite smooth/Beltrami owners.
The reported background push `task-20007` is outside this checkout and is not
stopped, resumed, or treated as evidence of publication.

## Exact theorem contract

| Owner | Carrier and construction | Intended checked conclusion |
| --- | --- | --- |
| `ArnoldBeltramiSmoothFlow` | The existing physical flow homomorphism included in the smooth acting group | The four pre-existing declarations are moved verbatim, with unchanged fully qualified names, out of the broader information-geometry aggregation surface |
| `SmoothVectorFieldPushforward` | The existing subgroup of smooth real homeomorphisms; actual Fréchet derivative on fields `E → E` | A group action, preservation of smoothness, agreement with native inverse pullback, Lie-bracket naturality under the stated analytic hypotheses, and derivative equivariance of conjugated motions |
| `FlowConjugation` | An arbitrary monoid `T`, group `G`, and native homomorphism type `T →* G` | Conjugation action, stabilizer equal to image centralizer, family fixing subgroup equal to the centralizer of all time values, and actual orbit/coset equivalence |
| `FlowErlangenClosure` | An arbitrary group action on an explicit invariant carrier `X` | Native Galois closure on `Subgroup G`, preservation of fixed points, closed stabilizers, and closure bounds from common invariants |
| `ArnoldSDiffFlowErlangenClosure` | The existing smooth measure action and actual `smoothFlowHom s` | Generated volume-preserving motions have measure-action closure contained in SDiff; flow symmetry implies velocity symmetry; explicit restricted symmetry subgroup and quotient |

The central definitions and conventions are

\[
(g_*X)(y)=Dg(g^{-1}y)X(g^{-1}y),\qquad
(g\cdot\Phi)(t)=g\Phi(t)g^{-1},
\]

\[
\mathrm{cl}_X(H)=\operatorname{Fix}_G(X^H),\qquad
H_\Phi=\langle\Phi_i(t):i\in I,t\in T\rangle.
\]

The dependency order is the actual action laws, then stabilizers and fixed
points, then the native Galois closure, then its measure/Beltrami specialization.
The derivative theorem separately connects the two action carriers. A group
homomorphism with real time does not, by its type alone, assert continuity or
differentiability in time.

## Selecting the actions

Import the integration owner and explicitly select derivative pushforward:

```lean
import InfoGeometry.Canonical.ArnoldSDiffFlowErlangenClosure

open InfoGeometry.Canonical
open scoped VectorFieldPushforward
```

For a theorem using the conjugation action on motions, install its named
action in that theorem or section:

```lean
letI := FlowConjugation.flowConjugationAction
  (Multiplicative ℝ) (smoothDiffeomorphismSubgroup E)
```

Importing the owner alone leaves ordinary pointwise action on functions
available. The scoped scalar action and the group action use the same
derivative construction. The declaration-audit module also checks consumers
outside and inside the scope, composition, and both factors of the native
measure/field product action.

## Reuse and boundaries

The construction reuses Mathlib's `fixingSubgroup_fixedPoints_gc`, native
`ClosureOperator`, `MulAut.conj`, centralizers, stabilizer conjugacy, and
`orbitEquivQuotientStabilizer`. The older operator Erlangen owner requires a
semiring action; measures and fields are handled at the more general native
group-action layer without introducing a fictitious semiring structure.

The existing `measure_stabilizer_eq_comap` identifies the measure stabilizer
with the existing smooth volume-preserving subgroup inside the smooth group.
The existing `smoothFlowHom_fixes_volume` supplies volume invariance for the
concrete real Beltrami family. The generator is its already proved velocity,
using `hasDerivAt_flow`, rather than an assumed generator packaged into a new
structure.

The joint Beltrami result uses the actual product carrier
`Measure Space × (Space → Space)`. Closure of the time-image subgroup for
this action lies in the intersection of the volume stabilizer and the
velocity stabilizer. This does not identify that closure with the closure
computed using measures alone.

The following qualifications preserve the mathematical content of the intake:

* A common invariant gives `cl_X(H) ≤ Stab(x)`. Equality is not implied by the
  existence of one invariant. Closure always names its action carrier.
  This is an order-theoretic closure on subgroups. `Subgroup.closure` in the
  flow-family definition means the subgroup generated by the time maps.
  Neither operation asserts topological density or Lie-bracket generation.
* Adjoining invariants gives intersections of stabilizers. Contact,
  symplectic, isometry, and flow symmetry groups do not form an unconditional
  inclusion chain; the chosen tensors and volumes must be compatible.
* A flow centralizer fixes each time value. Setwise preservation of a
  distribution, reparametrization, and normalization of a subgroup are
  different claims and are not identified here.
* The actual measure orbit is not asserted to contain all fixed-mass smooth
  densities. The existing finite-nonzero-measure result excludes nontrivial
  mass scaling within that orbit. Lebesgue measure on the whole spatial
  carrier is not a finite measure.
* SDiff is a stabilizer, not generally a normal subgroup of all Diff. A
  Jacobian is generally a function-valued cocycle, not a scalar character.
  Existing log-Jacobian owners are not extended to a general exact sequence.
  The source subgroup preserves a measure, not an oriented volume form.
  Consequently no `det Dg = 1` criterion for arbitrary measures or arbitrary
  normed spaces is asserted. Even for finite-dimensional Lebesgue measure,
  orientation must be considered separately from absolute Jacobian. The
  concrete Beltrami flow already has its own proved determinant-one formula.
* Lie-bracket naturality does not prove global flow existence, accessibility,
  a Tanaka prolongation, a Lie groupoid, or a quotient manifold.
* With the usual bracket convention, the derivative of positive-time
  pushforward by the flow of `Y` is `[X,Y]`; the Lie derivative `[Y,X]` uses
  the opposite time convention. No infinitesimal-sign identification is
  silently inferred from the conjugated-generator theorem.
* A finite multiplication-closed carrier needs nonemptiness before identity
  and inverses can be inferred. Forward-time closure and group closure are
  distinct; the generic generated subgroup explicitly adjoins inverses.

## Literature convention

Khesin, Misiołek and Modin, [*Information geometry of diffeomorphism groups*](https://arxiv.org/html/2411.03265v1),
§3.3, Proposition 3.9 and Remark 3.10, distinguish the analytic principal-bundle
result from its orbit/coset description. Their pushforward convention uses
left cosets, matching the existing measure action here. The present Lean
construction proves the abstract action and stabilizer statements; it does
not add their tame Fréchet structures or Moser transitivity theorem.

## Validation status

The focused validation surface contains ten local modules: the five
mathematical owners listed above and five unchanged prerequisites
(`ArnoldBeltramiFlow`, `ArnoldBeltramiVolume`,
`NavierStokesShearReconstruction`, `SmoothDiffeomorphismDensityOrbit`, and
`SmoothVolumePreservingGroup`). Previously compiled dependency artifacts may
be reused only after their source snapshots, successful check records,
compiler version, and dependency pins match the current source. The five
owners and the consumer/declaration audit are to be checked with warnings
treated as errors. This is a selected source-closure check, not a claim that
all ten modules were freshly compiled or that the broader aggregation
surface and whole repository passed.

Independent semantic source review is complete. The maintained selected-closure
checker is queued behind an occupied shared build lock; its current-main
compiler run and consumer/declaration audit have not started. No final native
verification, staged-gate result, pre-push result, commit, or publication is
claimed at this checkpoint. The existing background push remains untouched.

The checker itself has a two-line repair: the incomplete Git subprocess call
is completed, and baseline comparison respects the effective `--owner` list.
All non-owner dependency sources still have to match the selected baseline.
Source review accepted this repair; execution and a changed-dependency
negative control remain pending with the compiler lane.

Dependency pins and the toolchain remain unchanged. The older six-path
dependency-repair proposal is superseded for this newer main: HomotopyHypothesis
and Stacks already have tracked gitlinks, and the bootstrap script records the
Atlas revision. Any different LeanArchitect revision remains a separate,
conditional proposal requiring an observed compatibility failure and explicit
authorization.
