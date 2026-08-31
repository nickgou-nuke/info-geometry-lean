import InfoGeometry.Canonical.SouriauKleinOperatorOrbitGeometry
import InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
import InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge

/-!
# Split Cl(5,5) pure-spinor orbit geometry

This file is a conservative bridge between three repository-native layers:

* the projective pure-spinor / maximal-neutral Grassmannian geometry of
  `SplitClifford55ProjectivePureSpinor` and
  `SplitClifford55PureSpinorGrassmannianBridge`;
* the Souriau--Klein operator-orbit geometry and its five-grade KKS selection
  rules;
* the para-Kahler symmetric/skew response interface.

The bridge deliberately does **not** identify the split `(5,5)` pure-spinor
variety with the classical Klein quadric.  The latter parametrizes projective
2-planes in a four-dimensional carrier, whereas the pure-spinor annihilator
used here is a maximal totally-null 5-plane in the ten-dimensional neutral
carrier.  Any comparison between those projective geometries must therefore be
provided by an explicit readout map and proved equivariant separately.

No spacetime, Yang--Mills, renormalization-group, or gravitational
interpretation is asserted by this owner.
-/

noncomputable section

namespace InfoGeometry.Twistor.SplitClifford55PureSpinorOrbitGeometry

open scoped LinearAlgebra.Projectivization
open SouriauKKS
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
open InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge
open InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
open InfoGeometry.Canonical.SouriauKleinOperatorOrbitGeometry
open InfoGeometry.Physics.SouriauLieThermodynamics
open InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

/-! ## Projective pure-spinor readout -/

/-- A nonzero projective spinor satisfying the repository's concrete split
`(5,5)` pure-spinor predicate. -/
abbrev ProjectivePureSpinorPoint :=
  {p : ℙ ℝ Spinor // p ∈ ProjectivePureSpinor}

/-- The canonical maximal-neutral Grassmannian point read out from a projective
pure-spinor line. -/
def maximalNeutralReadout
    (p : ProjectivePureSpinorPoint) : MaximalNeutralGrassmannian :=
  projectivePureSpinorGrassmannianPoint p

@[simp] theorem maximalNeutralReadout_val
    (p : ProjectivePureSpinorPoint) :
    (maximalNeutralReadout p).1 = projectivePureSpinorAnnihilator p.1 := by
  rfl

/-- Every split `(5,5)` pure-spinor point determines a five-dimensional
maximal-null annihilator plane. -/
theorem maximalNeutralReadout_finrank
    (p : ProjectivePureSpinorPoint) :
    Module.finrank ℝ (maximalNeutralReadout p).1 = 5 := by
  exact projectivePureSpinorGrassmannianPoint_finrank p

/-- The annihilator plane read out from a pure spinor is totally null for the
neutral pairing. -/
theorem maximalNeutralReadout_totallyNull
    (p : ProjectivePureSpinorPoint) :
    InfoGeometry.Clifford.BudinichSpinorsNullVectors.IsTotallyNull
      neutralPairing (maximalNeutralReadout p).1 := by
  exact projectivePureSpinorGrassmannianPoint_totallyNull p

/-- The projective vacuum is a distinguished pure-spinor point. -/
def vacuumProjectivePureSpinorPoint : ProjectivePureSpinorPoint :=
  ⟨Projectivization.mk ℝ (1 : Spinor) one_ne_zero,
    projective_vacuum_isPureSpinor⟩

@[simp] theorem vacuum_maximalNeutralReadout :
    maximalNeutralReadout vacuumProjectivePureSpinorPoint =
      ⟨neutralAnnihilator (1 : Spinor),
        vacuum_neutralAnnihilator_isMaximalNeutralTotallyNull⟩ := by
  rfl

/-! ## Explicit operator-orbit adapter -/

section OperatorReadout

variable {L A : Type*}
variable [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable [Ring A] [Algebra ℝ A]

/--
An explicit adapter from projective pure-spinor points into the symmetry Lie
algebra of an operator-orbit model.

The map `direction` is data, not a theorem: the pure-spinor Grassmannian does
not canonically determine an arbitrary operator-orbit Lie direction.  Once such
a readout is supplied, the existing `QuantumMomentMap`, KKS form, and
five-grading become available without redefining them.
-/
structure OperatorPureSpinorReadout where
  grading : FiveGrading L
  momentMap : QuantumMomentMap (R := ℝ) (g := L) (A := A)
  direction : ProjectivePureSpinorPoint → L

namespace OperatorPureSpinorReadout

variable (D : OperatorPureSpinorReadout (L := L) (A := A))

/-- Observable obtained by composing the pure-spinor direction readout with the
repository quantum moment map. -/
def observable (p : ProjectivePureSpinorPoint) : A :=
  D.momentMap.toLinearMap (D.direction p)

/-- KKS response between two projective pure-spinor readout directions. -/
def kksResponse
    (μ : Module.Dual ℝ L)
    (p q : ProjectivePureSpinorPoint) : ℝ :=
  kksForm μ (D.direction p) (D.direction q)

/-- The KKS pure-spinor response is skew under interchange of the two
projective points. -/
theorem kksResponse_skew
    (μ : Module.Dual ℝ L)
    (p q : ProjectivePureSpinorPoint) :
    D.kksResponse μ p q = - D.kksResponse μ q p := by
  exact kksForm_skew μ (D.direction p) (D.direction q)

/-- If two pure-spinor readout directions land in grades `-1` and `+1`, their
KKS response probes a grade-zero bracket component. -/
theorem kksResponse_negOne_posOne_selection
    (μ : Module.Dual ℝ L)
    (p q : ProjectivePureSpinorPoint)
    (hp : D.direction p ∈ D.grading.gNegOne)
    (hq : D.direction q ∈ D.grading.gPosOne) :
    ∃ Z : L, Z ∈ D.grading.gZero ∧ D.kksResponse μ p q = μ Z := by
  exact grade_selection_kks_negOne_posOne D.grading μ hp hq

/-- If the dual state annihilates grade zero, every `(-1,+1)` pure-spinor KKS
block vanishes. -/
theorem kksResponse_negOne_posOne_vanishes
    (μ : Module.Dual ℝ L)
    (hμ : ∀ Z : L, Z ∈ D.grading.gZero → μ Z = 0)
    (p q : ProjectivePureSpinorPoint)
    (hp : D.direction p ∈ D.grading.gNegOne)
    (hq : D.direction q ∈ D.grading.gPosOne) :
    D.kksResponse μ p q = 0 := by
  exact grade_selection_kks_vanishes μ
    D.grading.gNegOne D.grading.gPosOne D.grading.gZero
    (fun hp' hq' => D.grading.negOne_posOne_mem_zero hp' hq')
    hμ hp hq

/-- Moment-map compatibility remains exact after a supplied symmetry/algebra
transport.  This is the operator-orbit equivariance square evaluated on a
pure-spinor readout direction. -/
theorem observable_transport_equivariant
    (e : L ≃ₗ[ℝ] L)
    (hLie : ∀ X Y : L, e ⁅X, Y⁆ = ⁅e X, e Y⁆)
    (φ : A ≃ₐ[ℝ] A)
    (p : ProjectivePureSpinorPoint) :
    (transportQuantumMomentMap e hLie φ D.momentMap).toLinearMap
        (e (D.direction p)) =
      φ (D.observable p) := by
  exact momentMap_equivariant e hLie φ D.momentMap (D.direction p)

/-- KKS invariance under the same bracket-preserving symmetry transport,
evaluated on pure-spinor readout directions. -/
theorem kksResponse_transport_invariant
    (e : L ≃ₗ[ℝ] L)
    (hLie : ∀ X Y : L, e ⁅X, Y⁆ = ⁅e X, e Y⁆)
    (μ : Module.Dual ℝ L)
    (p q : ProjectivePureSpinorPoint) :
    kksForm
        (InfoGeometry.Canonical.SouriauContragredientPairing.contragredient e μ)
        (e (D.direction p)) (e (D.direction q)) =
      D.kksResponse μ p q := by
  exact kks_transport_invariant e hLie μ (D.direction p) (D.direction q)

end OperatorPureSpinorReadout

end OperatorReadout

/-! ## Para-Kahler response adapter -/

section ParaKahlerReadout

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/--
An explicit tangent readout from projective pure-spinor points into a carrier
with a para-Kahler response datum.

As with the operator readout above, `tangent` is deliberately explicit.  This
owner does not postulate that a pure-spinor line is itself a tangent vector or
that the para-Kahler metric is a spacetime metric.
-/
structure ParaKahlerPureSpinorReadout where
  datum : ParaKahlerDatum ℝ V
  tangent : ProjectivePureSpinorPoint → V

namespace ParaKahlerPureSpinorReadout

variable (D : ParaKahlerPureSpinorReadout (V := V))

/-- Para-QGT evaluated on the tangent readouts of two projective pure-spinor
points. -/
def qgtResponse
    (p q : ProjectivePureSpinorPoint) : SplitScalar ℝ :=
  paraQGT D.datum (D.tangent p) (D.tangent q)

@[simp] theorem qgtResponse_re
    (p q : ProjectivePureSpinorPoint) :
    (D.qgtResponse p q).re = D.datum.metric (D.tangent p) (D.tangent q) := by
  rfl

@[simp] theorem qgtResponse_ep
    (p q : ProjectivePureSpinorPoint) :
    (D.qgtResponse p q).ep =
      D.datum.paraBerryTwoForm (D.tangent p) (D.tangent q) := by
  rfl

/-- Swapping the pure-spinor arguments preserves the symmetric response and
reverses the para-Berry response. -/
theorem qgtResponse_swap
    (p q : ProjectivePureSpinorPoint) :
    (D.qgtResponse q p).re = (D.qgtResponse p q).re ∧
    (D.qgtResponse q p).ep = - (D.qgtResponse p q).ep := by
  exact paraQGT_conjugation D.datum (D.tangent p) (D.tangent q)

/-- A pure-spinor tangent readout lying in the `+1` para-complex eigenspace is
metric-isotropic in the exact algebraic sense already proved by the para-Kahler
owner. -/
theorem chiralPureSpinorReadout_isotropic
    (p : ProjectivePureSpinorPoint)
    (hp : D.datum.para.K (D.tangent p) = D.tangent p) :
    D.datum.metric (D.tangent p) (D.tangent p) +
      D.datum.metric (D.tangent p) (D.tangent p) = 0 := by
  exact D.datum.chiral_mode_isotropic (D.tangent p) hp

end ParaKahlerPureSpinorReadout

end ParaKahlerReadout

/-! ## Unified readout packet -/

section UnifiedReadout

variable {L A V : Type*}
variable [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable [Ring A] [Algebra ℝ A]
variable [AddCommGroup V] [Module ℝ V]

/--
The conservative unifying contract: one projective pure-spinor source with an
operator-orbit readout and a para-Kahler tangent readout.

The structure contains no claim that the two targets are identical.  Concrete
physics owners may add commuting/equivariant diagrams relating them.
-/
structure PureSpinorOrbitGeometry where
  operator : OperatorPureSpinorReadout (L := L) (A := A)
  paraKahler : ParaKahlerPureSpinorReadout (V := V)

namespace PureSpinorOrbitGeometry

variable (D : PureSpinorOrbitGeometry (L := L) (A := A) (V := V))

/-- Paired symmetric/skew response readouts attached to two projective
pure-spinor points. -/
def responsePair
    (μ : Module.Dual ℝ L)
    (p q : ProjectivePureSpinorPoint) : ℝ × SplitScalar ℝ :=
  (D.operator.kksResponse μ p q, D.paraKahler.qgtResponse p q)

@[simp] theorem responsePair_kks
    (μ : Module.Dual ℝ L)
    (p q : ProjectivePureSpinorPoint) :
    (D.responsePair μ p q).1 = D.operator.kksResponse μ p q := by
  rfl

@[simp] theorem responsePair_qgt
    (μ : Module.Dual ℝ L)
    (p q : ProjectivePureSpinorPoint) :
    (D.responsePair μ p q).2 = D.paraKahler.qgtResponse p q := by
  rfl

/-- The unified response exposes the two independently proved parity laws:
KKS is skew, while para-QGT splits into a symmetric real and skew split part. -/
theorem responsePair_swap
    (μ : Module.Dual ℝ L)
    (p q : ProjectivePureSpinorPoint) :
    (D.responsePair μ p q).1 = - (D.responsePair μ q p).1 ∧
    ((D.responsePair μ q p).2).re = ((D.responsePair μ p q).2).re ∧
    ((D.responsePair μ q p).2).ep = - ((D.responsePair μ p q).2).ep := by
  constructor
  · exact D.operator.kksResponse_skew μ p q
  · exact D.paraKahler.qgtResponse_swap p q

end PureSpinorOrbitGeometry

end UnifiedReadout

end InfoGeometry.Twistor.SplitClifford55PureSpinorOrbitGeometry
