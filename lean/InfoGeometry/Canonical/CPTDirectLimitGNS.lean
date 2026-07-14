import InfoGeometry.Canonical.CPTTensorColimitIdentification
import InfoGeometry.Prequantum.AlgebraicGNSState

/-!
# CPT direct-limit GNS packet

This file formalizes the next theorem-level step after the direct-limit carrier
identification:

* the direct-limit carrier is the already-identified `Limit`;
* a GNS-style packet may be installed on that carrier by supplying an explicit
  involution, state functional, and finite-stage readback data;
* the stagewise data remain visible through the canonical embeddings.

The file does **not** claim a canonical transported `StarRing` instance on the
direct-limit carrier.  That is a separate carrier-transport theorem.  Here we
record the explicit algebraic GNS socket over the identified carrier.
-/

noncomputable section

namespace CPTDirectLimitGNS

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.CPTTensorColimitIdentification
open InfoGeometry.Prequantum.AlgebraicGNSState

/-- The identified direct-limit carrier used by the CPT GNS packet. -/
abbrev CPTGNSCarrier : Type := cptTensorInductiveLimit.AInf

/--
GNS-style algebraic packet over the identified CPT direct-limit carrier.

This is the conservative representation surface: the caller supplies the
involution and the state on the direct-limit carrier, together with stagewise
readback data compatible with the canonical embeddings.
-/
structure CPTDirectLimitGNSPacket where
  /-- Carrier-level involution on the identified direct-limit algebra. -/
  carrierStar : CPTGNSCarrier → CPTGNSCarrier
  /-- Involution law. -/
  star_involutive : Function.Involutive carrierStar
  /-- Anti-multiplicativity on the carrier. -/
  star_mul : ∀ x y : CPTGNSCarrier, carrierStar (x * y) = carrierStar y * carrierStar x
  /-- Additivity of the carrier involution. -/
  star_add : ∀ x y : CPTGNSCarrier, carrierStar (x + y) = carrierStar x + carrierStar y
  /-- The direct-limit state functional on the carrier. -/
  state : CPTGNSCarrier →ₗ[ℝ] ℝ
  /-- Normalization of the state. -/
  normalized : state 1 = 1
  /-- Positivity on algebraic squares. -/
  positive : ∀ x : CPTGNSCarrier, 0 ≤ state (carrierStar x * x)
  /-- Symmetry of the quadratic pairing. -/
  symmetric : ∀ x y : CPTGNSCarrier, state (carrierStar y * x) = state (carrierStar x * y)
  /-- Finite-stage algebraic states at every depth. -/
  stage_state : ∀ n : ℕ, RealAlgebraicState (Stage n)
  /-- The carrier state reads back each finite stage through the canonical embedding. -/
  stage_readback :
    ∀ n : ℕ, ∀ x : Stage n, state (cptTensorInductiveLimit.inj n x) =
      (stage_state n).eval x
  /-- The carrier involution reads back the stagewise involution. -/
  stage_star_readback :
    ∀ n : ℕ, ∀ x : Stage n, carrierStar (cptTensorInductiveLimit.inj n x) =
      cptTensorInductiveLimit.inj n (star x)

namespace CPTDirectLimitGNSPacket

variable (P : CPTDirectLimitGNSPacket)

/-- The GNS null set on the identified direct-limit carrier. -/
def gnsNullSet : Set CPTGNSCarrier :=
  {x | P.state (P.carrierStar x * x) = 0}

@[simp] theorem mem_gnsNullSet_iff (x : CPTGNSCarrier) :
    x ∈ P.gnsNullSet ↔ P.state (P.carrierStar x * x) = 0 :=
  Iff.rfl

/-- The direct-limit unit is normalized. -/
theorem eval_one : P.state 1 = 1 :=
  P.normalized

/-- Stage readback at depth `n`. -/
theorem stage_eval (n : ℕ) (x : Stage n) :
    P.state (cptTensorInductiveLimit.inj n x) = (P.stage_state n).eval x :=
  P.stage_readback n x

/-- Stagewise carrier involution readback at depth `n`. -/
theorem stage_star (n : ℕ) (x : Stage n) :
    P.carrierStar (cptTensorInductiveLimit.inj n x) =
      cptTensorInductiveLimit.inj n (star x) :=
  P.stage_star_readback n x

end CPTDirectLimitGNSPacket

end CPTDirectLimitGNS
