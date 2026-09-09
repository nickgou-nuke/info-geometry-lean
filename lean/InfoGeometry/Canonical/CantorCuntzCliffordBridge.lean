import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Canonical.HodgeDrazinEnvelope
import InfoGeometry.Canonical.FierzReadout
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.SocketTarget

noncomputable section

namespace InfoGeometry.Canonical

/-!
# Cantor/Cuntz/Clifford bridge

Cantor cylinders -> Cuntz branching -> CAR -> Clifford generators.

Key correction:

`Cuntz` isometries are not Clifford generators by themselves.  The theorem-safe
bridge first constructs a CAR generator from the Cuntz shifts,

`a = S_left * S_right*`,

then treats Clifford generators and Fierz laws as downstream witness-gated
structure.
-/

open InfoGeometry.Topology
open InfoGeometry.Canonical.HodgeDrazinEnvelope
open InfoGeometry.Canonical.FierzReadout

/-- Symbolic Cantor space as infinite binary sequences. -/
abbrev CantorSpace := ℕ → Bool

/-- A finite binary cylinder word. -/
abbrev BinaryWord := List Bool

/-- A bitstream observable. -/
abbrev BitStream := ℕ → Bool

/-- Reuse the topology owner for abstract Cuntz `O₂` data. -/
abbrev CantorCuntzO2Carrier
    (Op : Type*) [Ring Op] [StarRing Op] :=
  InfoGeometry.Topology.CuntzO2Carrier Op

/-- Anticommutator in an abstract ring. -/
@[rep_depth operator]
def cantorAnticommutator
    {Op : Type*} [Add Op] [Mul Op]
    (x y : Op) : Op :=
  x * y + y * x

/--
The first CAR generator obtained from Cuntz generators:

`a = S_left * S_right*`.
-/
@[rep_depth operator]
def carFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) : Op :=
  C.S_left * star C.S_right

/-- The adjoint of the Cuntz-derived CAR generator is `S_right * S_left*`. -/
@[rep_depth operator]
theorem star_carFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    star (carFromCuntz C) = C.S_right * star C.S_left := by
  unfold carFromCuntz
  rw [star_mul, star_star]

/-- The Cuntz-derived CAR generator is nilpotent. -/
@[rep_depth operator]
theorem carFromCuntz_sq_eq_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    carFromCuntz C * carFromCuntz C = 0 := by
  unfold carFromCuntz
  calc
    (C.S_left * star C.S_right) * (C.S_left * star C.S_right)
        = C.S_left * (star C.S_right * C.S_left) * star C.S_right := by
          noncomm_ring
    _ = C.S_left * 0 * star C.S_right := by
          rw [C.orthogonal_ranges.2]
    _ = 0 := by
          simp

/-- The Cuntz-derived CAR generator satisfies `{a, a*} = 1`. -/
@[rep_depth operator]
theorem carFromCuntz_anticommutator_star_eq_one
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    cantorAnticommutator (carFromCuntz C) (star (carFromCuntz C)) = 1 := by
  unfold cantorAnticommutator carFromCuntz
  rw [star_mul, star_star]
  calc
    (C.S_left * star C.S_right) * (C.S_right * star C.S_left)
        + (C.S_right * star C.S_left) * (C.S_left * star C.S_right)
        = C.S_left * (star C.S_right * C.S_right) * star C.S_left
          + C.S_right * (star C.S_left * C.S_left) * star C.S_right := by
            noncomm_ring
    _ = C.S_left * 1 * star C.S_left
          + C.S_right * 1 * star C.S_right := by
            rw [C.right_isometry, C.left_isometry]
    _ = C.S_left * star C.S_left + C.S_right * star C.S_right := by
            simp
    _ = 1 := C.range_sum

/-- CAR witness for one fermionic generator. -/
@[rep_depth operator]
structure CARGenerator
    (Op : Type*) [Ring Op] [StarRing Op] where
  a : Op

  nilpotent :
    a * a = 0

  car :
    cantorAnticommutator a (star a) = 1

/-- The Cuntz-to-CAR bridge, theorem-derived from the Cuntz relations. -/
@[rep_depth operator]
def carGeneratorFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) : CARGenerator Op where
  a := carFromCuntz C
  nilpotent := carFromCuntz_sq_eq_zero C
  car := carFromCuntz_anticommutator_star_eq_one C

/-- Two Clifford generators supplied downstream from a CAR generator. -/
@[rep_depth operator]
structure CliffordPair
    (Op : Type*) [Ring Op] [StarRing Op] where
  gamma1 : Op
  gamma2 : Op

  gamma1_sq :
    gamma1 * gamma1 = 1

  gamma2_sq :
    gamma2 * gamma2 = 1

  anticomm :
    cantorAnticommutator gamma1 gamma2 = 0

/--
Cuntz-to-CAR-to-Clifford socket.

The CAR generator is theorem-derived from Cuntz data.  The Clifford pair is a
separate witness because signature, phase, and real-structure choices are model
data.
-/
@[socket_debt_tag, rep_depth operator]
structure CantorCuntzCliffordSocket
    (Op : Type*) [Ring Op] [StarRing Op] where
  cuntz : CantorCuntzO2Carrier Op
  car : CARGenerator Op
  car_eq : car.a = carFromCuntz cuntz
  clifford : CliffordPair Op

/-- Build the CAR part of the socket directly from Cuntz data. -/
@[rep_depth operator]
def derivedCuntzCARSocket
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op)
    (Cl : CliffordPair Op) : CantorCuntzCliffordSocket Op where
  cuntz := C
  car := carGeneratorFromCuntz C
  car_eq := rfl
  clifford := Cl

/-- Drazin horizon support for a signal operator. -/
abbrev CantorDrazinHorizon
    (Op : Type*) [Ring Op] [Star Op] :=
  SignalDrazinSupport Op

/-- Drazin-Green data for a Cantor-scale frequency operator. -/
abbrev CantorScaleGreen
    (Op : Type*) [Ring Op] [Star Op] :=
  FrequencyDrazinGreen Op

/--
The Cantor-Clifford physical envelope:

`x_phys = H_L * (p_A * x * p_A) * H_L`.
-/
@[rep_depth operator]
def cantorCliffordEnvelope
    {Op : Type*} [Ring Op] [Star Op]
    (D : CantorDrazinHorizon Op)
    (G : CantorScaleGreen Op)
    (x : Op) : Op :=
  G.P_harm * (D.p * x * D.p) * G.P_harm

/-- Fierz readout on an operator carrier. -/
@[rep_depth operator]
structure CantorFierzReadout
    (Op : Type*) where
  channel : FierzChannelReadout → Op → ℝ

/-- Fierz coordinate extracted from the Cantor-Clifford Drazin envelope. -/
@[rep_depth operator]
def cantorFierzCoordinate
    {Op : Type*} [Ring Op] [Star Op]
    (D : CantorDrazinHorizon Op)
    (G : CantorScaleGreen Op)
    (R : CantorFierzReadout Op)
    (readout : FierzChannelReadout)
    (x : Op) : ℝ :=
  R.channel readout (cantorCliffordEnvelope D G x)

/--
Fierz admissibility of the Cantor-Clifford envelope.

This is not automatic from Cuntz or CAR.  Concrete Clifford/Fierz models supply
this witness.
-/
@[rep_depth operator]
structure CantorFierzAdmissible
    (Op : Type*) [Ring Op] [Star Op] where
  residual : (FierzChannelReadout → ℝ) → ℝ
  admissible : (FierzChannelReadout → ℝ) → Prop

/-- Full theorem-safe Cantor -> Cuntz -> CAR -> Clifford -> envelope -> Fierz socket. -/
@[socket_debt_tag, rep_depth operator]
structure CantorCuntzCliffordFierzSocket
    (Op : Type*) [Ring Op] [StarRing Op] where
  spinSocket : CantorCuntzCliffordSocket Op
  horizon : CantorDrazinHorizon Op
  scaleGreen : CantorScaleGreen Op
  readout : CantorFierzReadout Op
  admissibility : CantorFierzAdmissible Op

/-- Re-export: the spin socket's CAR generator is the Cuntz-derived generator. -/
@[bridge_target_tag, rep_depth operator]
theorem socket_car_eq_carFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (S : CantorCuntzCliffordSocket Op) :
    S.car.a = carFromCuntz S.cuntz :=
  S.car_eq

/-- Re-export: the Cuntz-derived generator in a socket is nilpotent. -/
@[bridge_target_tag, rep_depth operator]
theorem socket_car_nilpotent
    {Op : Type*} [Ring Op] [StarRing Op]
    (S : CantorCuntzCliffordSocket Op) :
    S.car.a * S.car.a = 0 :=
  S.car.nilpotent

/-- Re-export: the Cuntz-derived generator in a socket satisfies CAR. -/
@[bridge_target_tag, rep_depth operator]
theorem socket_car_anticommutator
    {Op : Type*} [Ring Op] [StarRing Op]
    (S : CantorCuntzCliffordSocket Op) :
    cantorAnticommutator S.car.a (star S.car.a) = 1 :=
  S.car.car

end InfoGeometry.Canonical
