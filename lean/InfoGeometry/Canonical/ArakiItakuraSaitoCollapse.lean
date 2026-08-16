import InfoGeometry.Canonical.SouriauModularBregmanOperator
import InfoGeometry.Canonical.SouriauOperatorBregmanModular
import InfoGeometry.Canonical.KANColimitBridge
import InfoGeometry.Topology.ThermodynamicGauge

/-!
# Araki--Itakura--Saito Collapse

Repository-native noncommutative bridge for the proposed restriction of Araki
relative entropy to the parabolic/Burg--Itakura--Saito lane.

The owner object is not only a scalar divergence.  It is the operatorial
Bregman readout already formalized in
`InfoGeometry.Canonical.SouriauModularBregmanOperator`:

`operatorBregman readout Φ gradientΦ X Y`.

This file only names the Itakura--Saito/Burg specialization interface and proves
readback lemmas from explicit collapse premises.  It does not construct a GNS
representation, unbounded relative modular logarithm, or full Araki relative
entropy theorem.

#### BUCKET 1: CLOSED FINITE THEOREMS
The operatorial Bregman diagonal identity, symmetry-invariance readback, bounded
doubled-carrier conversion, and KAN colimit nilpotency readback are proved by
composition with existing owners.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
The Araki comparison assumes an explicit equality between a chosen restricted
Araki relative-entropy readout and the noncommutative Itakura--Saito/Burg
packet.  The entropy-production comparison assumes an explicit scalar readout.

#### BUCKET 3: OPEN CLOSURE DEBT
The GNS representation, Tomita--Takesaki relative modular operator, and
unbounded logarithm definition of Araki relative entropy are not constructed in
this file.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArakiItakuraSaitoCollapse

open InfoGeometry.Canonical.SouriauModularBregmanOperator
open InfoGeometry.Canonical.SouriauOperatorBregmanModular
open InfoGeometry.Topology.ThermodynamicGauge

/-! ## Generic noncommutative Itakura--Saito/Burg operator packet -/

section GenericOperator

variable {Op : Type*} [AddGroup Op]

/--
Noncommutative Itakura--Saito/Burg packet.

`potential` and `gradient` are the operator log/Burg data; the scalar value is
obtained only through the repository-owned product/readout interface.
-/
@[rep_depth operator]
structure NoncommutativeItakuraSaitoModel (Op : Type*) [AddGroup Op] where
  /-- Product/readout interface: trace, KMS state, vector state, or regularized weight. -/
  readout : OperatorPrimalDualSocket Op
  /-- Operator Burg/log potential. -/
  potential : Op → ℝ
  /-- Operator gradient of the Burg/log potential. -/
  gradient : Op → Op

namespace NoncommutativeItakuraSaitoModel

variable (P : NoncommutativeItakuraSaitoModel Op)

/-- The noncommutative Itakura--Saito value is the repo-native operator Bregman readout. -/
@[rep_depth operator]
def divergence (X Y : Op) : ℝ :=
  operatorBregman P.readout P.potential P.gradient X Y

@[simp, rep_depth operator]
theorem divergence_eq_operatorBregman (X Y : Op) :
    P.divergence X Y = operatorBregman P.readout P.potential P.gradient X Y :=
  rfl

/-- Diagonal vanishing inherited from the operatorial Bregman owner. -/
@[simp, rep_depth operator]
theorem divergence_self (X : Op) :
    P.divergence X X = 0 := by
  simp [divergence]

end NoncommutativeItakuraSaitoModel

section LinearSymmetry

variable {Op : Type*} [AddCommGroup Op] [Module ℝ Op]
variable (P : NoncommutativeItakuraSaitoModel Op)

/--
Operator Itakura--Saito invariance under a linear symmetry preserving the
operator potential and the product/readout pairing.
-/
@[rep_depth operator]
theorem divergence_invariant_of_linear_symmetry
    (T : Op →ₗ[ℝ] Op)
    (hΦ : ∀ X : Op, P.potential (T X) = P.potential X)
    (hPair :
      ∀ X Y : Op,
        P.readout.pairing (P.gradient (T X)) (T Y) =
          P.readout.pairing (P.gradient X) Y)
    (X Y : Op) :
    P.divergence (T X) (T Y) = P.divergence X Y := by
  simpa [NoncommutativeItakuraSaitoModel.divergence] using
    operatorBregman_invariant_of_linear_symmetry
      P.readout P.potential P.gradient T hΦ hPair X Y

end LinearSymmetry

end GenericOperator

/-! ## Araki restriction readback -/

/-- Restrict an abstract Araki relative-entropy readout to selected states. -/
@[rep_depth operator]
def restrictedAraki {State : Type*}
    (arakiRelativeEntropy : State → State → ℝ)
    (ω φ : State) : ℝ :=
  arakiRelativeEntropy ω φ

/--
Explicit-premise noncommutative collapse:
if the restricted Araki readout is identified with the operator
Itakura--Saito/Burg packet on a parabolic chart, Lean exposes the equality.
-/
@[rep_depth operator]
theorem restrictedAraki_eq_noncommutative_itakuraSaito
    {State Op : Type*} [AddGroup Op]
    (arakiRelativeEntropy : State → State → ℝ)
    (toOperator : State → Op)
    (P : NoncommutativeItakuraSaitoModel Op)
    (ω φ : State)
    (hcollapse :
      restrictedAraki arakiRelativeEntropy ω φ =
        P.divergence (toOperator ω) (toOperator φ)) :
    restrictedAraki arakiRelativeEntropy ω φ =
      operatorBregman P.readout P.potential P.gradient
        (toOperator ω) (toOperator φ) := by
  simpa [NoncommutativeItakuraSaitoModel.divergence] using hcollapse

/-- Self-Araki vanishing after an explicit operator Itakura--Saito collapse. -/
@[rep_depth operator]
theorem restrictedAraki_self_eq_zero_of_noncommutative_collapse
    {State Op : Type*} [AddGroup Op]
    (arakiRelativeEntropy : State → State → ℝ)
    (toOperator : State → Op)
    (P : NoncommutativeItakuraSaitoModel Op)
    (ω : State)
    (hcollapse :
      restrictedAraki arakiRelativeEntropy ω ω =
        P.divergence (toOperator ω) (toOperator ω)) :
    restrictedAraki arakiRelativeEntropy ω ω = 0 := by
  rw [hcollapse]
  exact P.divergence_self (toOperator ω)

/--
Thermodynamic comparison readout after the noncommutative Araki/IS collapse.

The scalar extraction from the noncommutative operator is deliberately an
explicit map: KMS state, vector state, trace weight, or continuous-core weight
must be supplied by the owner lane.
-/
@[rep_depth thermo]
theorem restrictedAraki_eq_entropyProductionScalar_of_operator_readouts
    {State Op Alg : Type*} [AddGroup Op] [Ring Alg]
    (arakiRelativeEntropy : State → State → ℝ)
    (toOperator : State → Op)
    (P : NoncommutativeItakuraSaitoModel Op)
    (flow : CausalNonequilibriumFlow Alg)
    (entropyProductionScalar : CausalNonequilibriumFlow Alg → ℝ)
    (ω φ : State)
    (hcollapse :
      restrictedAraki arakiRelativeEntropy ω φ =
        P.divergence (toOperator ω) (toOperator φ))
    (hIS_entropy :
      P.divergence (toOperator ω) (toOperator φ) =
        entropyProductionScalar flow) :
    restrictedAraki arakiRelativeEntropy ω φ = entropyProductionScalar flow :=
  hcollapse.trans hIS_entropy

/--
KAN colimit compatibility readback for the parabolic/nilpotent sector.

This deliberately does not use a matrix direct-limit carrier as an
operator-Bregman carrier.  It only reads the nilpotent signature through the
repository-owned `KANStageTower`.
-/
@[rep_depth operator]
theorem KAN_colimit_parabolic_nilpotent_readout
    (T : InfoGeometry.Canonical.KANColimitBridge.KANStageTower)
    {n : ℕ} {x : T.Stage n}
    (hx : (T.stage n).nilpotentN x) :
    T.limit.nilpotentNInf (T.toLimit n x) :=
  T.nilpotent_directLimit hx

/-! ## Bounded doubled-carrier specialization -/

section BoundedDoubledCarrier

open scoped InnerProductSpace

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Convert the bounded Souriau operatorial Bregman packet into the IS/Burg interface. -/
@[rep_depth operator]
def ofSouriauOperatorialBregmanPacket
    {LieAlgebra : Type*}
    (P : SouriauOperatorialBregmanPacket (E := E) LieAlgebra) :
    NoncommutativeItakuraSaitoModel EndH where
  readout := P.socket
  potential := P.potential
  gradient := P.gradient

omit [CompleteSpace E] in
/-- Readback: the converted packet has exactly the Souriau packet divergence. -/
@[simp, rep_depth operator]
theorem ofSouriauOperatorialBregmanPacket_divergence
    {LieAlgebra : Type*}
    (P : SouriauOperatorialBregmanPacket (E := E) LieAlgebra)
    (X Y : EndH) :
    (ofSouriauOperatorialBregmanPacket (E := E) P).divergence X Y =
      P.divergence X Y :=
  rfl

end BoundedDoubledCarrier

end InfoGeometry.Canonical.ArakiItakuraSaitoCollapse

end noncomputable section
