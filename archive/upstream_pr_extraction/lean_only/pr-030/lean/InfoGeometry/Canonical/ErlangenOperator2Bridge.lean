import InfoGeometry.Canonical.ErlangenOperator2
import InfoGeometry.Canonical.SouriauFenchelOnsagerBridge

/-!
# Erlangen Operator 2.0 Bridge

Bridge from the existing coadjoint entropy symmetry interface to the abstract
`ErlangenOperatorDatum` synthesis layer.

This file is intentionally compositional: it does not construct concrete
response tensors, Onsager pairings, or Casimir involutions. Those are supplied
as owner data.
-/

namespace InfoGeometry
namespace Canonical

open InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
open InfoGeometry.Canonical.ErlangenOperator2
open InfoGeometry.Canonical.ErlangenOperator2.ErlangenOperatorDatum

/--
Pull back a coadjoint response tensor along the moment map.
-/
def responseMetricPullback
    {Sym G Gdual State : Type*}
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : Gdual → Sym → Sym → ℝ) :
    State → Sym → Sym → ℝ :=
  fun s A B => responseMetric (C.data.moment s) A B

/--
Pull back a coadjoint Onsager pairing along the moment map.
-/
def onsagerPairingPullback
    {Sym G Gdual State : Type*}
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (onsagerPairing : Gdual → Sym → Sym → ℝ) :
    State → Sym → Sym → ℝ :=
  fun s A B => onsagerPairing (C.data.moment s) A B

/--
State-space invariance of the pullback response tensor follows from
coadjoint invariance plus moment equivariance.
-/
theorem responseMetricPullback_invariant
    {Sym G Gdual State : Type*}
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : Gdual → Sym → Sym → ℝ)
    (hresp :
      ∀ X A B ξ,
        responseMetric (C.coadjointAction X ξ) A B =
          responseMetric ξ A B) :
    ∀ X A B s,
      responseMetricPullback C responseMetric (C.stateAction X s) A B =
        responseMetricPullback C responseMetric s A B := by
  intro X A B s
  unfold responseMetricPullback
  rw [C.moment_equivariant X s]
  exact hresp X A B (C.data.moment s)

/--
State-space `J`-reciprocity of the pullback Onsager pairing follows directly
from the coadjoint pairing reciprocity.
-/
theorem onsagerPairingPullback_reciprocity
    {Sym G Gdual State : Type*}
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (onsagerPairing : Gdual → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hons :
      ∀ A B ξ,
        onsagerPairing ξ A B =
          onsagerPairing ξ (casimirJ B) (casimirJ A)) :
    ∀ A B s,
      onsagerPairingPullback C onsagerPairing s A B =
        onsagerPairingPullback C onsagerPairing s (casimirJ B) (casimirJ A) := by
  intro A B s
  unfold onsagerPairingPullback
  exact hons A B (C.data.moment s)

/--
Build an Erlangen datum on the coadjoint carrier directly from a coadjoint
entropy symmetry context, with supplied response and Onsager/J channels.
-/
def coadjointErlangenDatum
    {Sym G Gdual State : Type*} [Group Sym]
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : Gdual → Sym → Sym → ℝ)
    (onsagerPairing : Gdual → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hStateActOne : ∀ ξ : Gdual, C.coadjointAction 1 ξ = ξ)
    (hStateActMul :
      ∀ g h : Sym, ∀ ξ : Gdual,
        C.coadjointAction (g * h) ξ =
          C.coadjointAction g (C.coadjointAction h ξ))
    (hresp :
      ∀ X A B ξ,
        responseMetric (C.coadjointAction X ξ) A B =
          responseMetric ξ A B)
    (hons :
      ∀ A B ξ,
        onsagerPairing ξ A B =
          onsagerPairing ξ (casimirJ B) (casimirJ A)) :
    ErlangenOperatorDatum ℝ Sym Gdual Sym where
  entropy := C.entropy
  responseMetric := responseMetric
  onsagerPairing := onsagerPairing
  stateAct := C.coadjointAction
  obsAct := fun _ A => A
  casimirJ := casimirJ
  stateAct_one := hStateActOne
  stateAct_mul := hStateActMul
  obsAct_one := by
    intro A
    rfl
  obsAct_mul := by
    intro g h A
    rfl
  entropy_invariant := C.entropy_casimir_invariant
  response_invariant := by
    intro X A B s
    simpa using hresp X A B s
  onsager_reciprocity := hons

/--
Build an Erlangen datum on the underlying state carrier by pulling back entropy
through the context moment map, with supplied state-level response and Onsager/J
channels.
-/
def stateMomentErlangenDatum
    {Sym G Gdual State : Type*} [Group Sym]
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : State → Sym → Sym → ℝ)
    (onsagerPairing : State → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hStateActOne : ∀ s : State, C.stateAction 1 s = s)
    (hStateActMul :
      ∀ g h : Sym, ∀ s : State,
        C.stateAction (g * h) s = C.stateAction g (C.stateAction h s))
    (hresp :
      ∀ X A B s,
        responseMetric (C.stateAction X s) A B =
          responseMetric s A B)
    (hons :
      ∀ A B s,
        onsagerPairing s A B =
          onsagerPairing s (casimirJ B) (casimirJ A)) :
    ErlangenOperatorDatum ℝ Sym State Sym where
  entropy := fun s => C.entropy (C.data.moment s)
  responseMetric := responseMetric
  onsagerPairing := onsagerPairing
  stateAct := C.stateAction
  obsAct := fun _ A => A
  casimirJ := casimirJ
  stateAct_one := hStateActOne
  stateAct_mul := hStateActMul
  obsAct_one := by
    intro A
    rfl
  obsAct_mul := by
    intro g h A
    rfl
  entropy_invariant := by
    intro X s
    exact C.entropy_invariant_on_state_orbit X s
  response_invariant := by
    intro X A B s
    simpa using hresp X A B s
  onsager_reciprocity := hons

/--
Bridge closure theorem on the coadjoint carrier:
the bridge-assembled datum satisfies the Erlangen geometry synthesis theorem.
-/
theorem coadjoint_geometry_as_symmetry_invariants
    {Sym G Gdual State : Type*} [Group Sym]
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : Gdual → Sym → Sym → ℝ)
    (onsagerPairing : Gdual → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hStateActOne : ∀ ξ : Gdual, C.coadjointAction 1 ξ = ξ)
    (hStateActMul :
      ∀ g h : Sym, ∀ ξ : Gdual,
        C.coadjointAction (g * h) ξ =
          C.coadjointAction g (C.coadjointAction h ξ))
    (hresp :
      ∀ X A B ξ,
        responseMetric (C.coadjointAction X ξ) A B =
          responseMetric ξ A B)
    (hons :
      ∀ A B ξ,
        onsagerPairing ξ A B =
          onsagerPairing ξ (casimirJ B) (casimirJ A)) :
    ErlangenOperatorGeometry
      (coadjointErlangenDatum C responseMetric onsagerPairing casimirJ
        hStateActOne hStateActMul hresp hons) :=
  geometry_as_symmetry_invariants
    (coadjointErlangenDatum C responseMetric onsagerPairing casimirJ
      hStateActOne hStateActMul hresp hons)

/--
Bridge closure theorem on the state carrier:
the moment-pullback bridge datum satisfies the Erlangen geometry synthesis
theorem.
-/
theorem state_geometry_as_symmetry_invariants
    {Sym G Gdual State : Type*} [Group Sym]
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : State → Sym → Sym → ℝ)
    (onsagerPairing : State → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hStateActOne : ∀ s : State, C.stateAction 1 s = s)
    (hStateActMul :
      ∀ g h : Sym, ∀ s : State,
        C.stateAction (g * h) s = C.stateAction g (C.stateAction h s))
    (hresp :
      ∀ X A B s,
        responseMetric (C.stateAction X s) A B =
          responseMetric s A B)
    (hons :
      ∀ A B s,
        onsagerPairing s A B =
          onsagerPairing s (casimirJ B) (casimirJ A)) :
    ErlangenOperatorGeometry
      (stateMomentErlangenDatum C responseMetric onsagerPairing casimirJ
        hStateActOne hStateActMul hresp hons) :=
  geometry_as_symmetry_invariants
    (stateMomentErlangenDatum C responseMetric onsagerPairing casimirJ
      hStateActOne hStateActMul hresp hons)

/--
Canonical pulled-back state datum from coadjoint response and Onsager channels.
-/
def stateMomentErlangenDatum_of_pullback
    {Sym G Gdual State : Type*} [Group Sym]
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : Gdual → Sym → Sym → ℝ)
    (onsagerPairing : Gdual → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hStateActOne : ∀ s : State, C.stateAction 1 s = s)
    (hStateActMul :
      ∀ g h : Sym, ∀ s : State,
        C.stateAction (g * h) s = C.stateAction g (C.stateAction h s))
    (hresp :
      ∀ X A B ξ,
        responseMetric (C.coadjointAction X ξ) A B =
          responseMetric ξ A B)
    (hons :
      ∀ A B ξ,
        onsagerPairing ξ A B =
          onsagerPairing ξ (casimirJ B) (casimirJ A)) :
    ErlangenOperatorDatum ℝ Sym State Sym :=
  stateMomentErlangenDatum
    C
    (responseMetricPullback C responseMetric)
    (onsagerPairingPullback C onsagerPairing)
    casimirJ
    hStateActOne
    hStateActMul
    (responseMetricPullback_invariant C responseMetric hresp)
    (onsagerPairingPullback_reciprocity C onsagerPairing casimirJ hons)

/--
Closure theorem for the canonical pullback state datum.
-/
theorem state_pullback_geometry_as_symmetry_invariants
    {Sym G Gdual State : Type*} [Group Sym]
    (C : CoadjointEntropySymmetryContext Sym G Gdual State)
    (responseMetric : Gdual → Sym → Sym → ℝ)
    (onsagerPairing : Gdual → Sym → Sym → ℝ)
    (casimirJ : Sym → Sym)
    (hStateActOne : ∀ s : State, C.stateAction 1 s = s)
    (hStateActMul :
      ∀ g h : Sym, ∀ s : State,
        C.stateAction (g * h) s = C.stateAction g (C.stateAction h s))
    (hresp :
      ∀ X A B ξ,
        responseMetric (C.coadjointAction X ξ) A B =
          responseMetric ξ A B)
    (hons :
      ∀ A B ξ,
        onsagerPairing ξ A B =
          onsagerPairing ξ (casimirJ B) (casimirJ A)) :
    ErlangenOperatorGeometry
      (stateMomentErlangenDatum_of_pullback C responseMetric onsagerPairing casimirJ
        hStateActOne hStateActMul hresp hons) :=
  geometry_as_symmetry_invariants
    (stateMomentErlangenDatum_of_pullback C responseMetric onsagerPairing casimirJ
      hStateActOne hStateActMul hresp hons)

end Canonical
end InfoGeometry
