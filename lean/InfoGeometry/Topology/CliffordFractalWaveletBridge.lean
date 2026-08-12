import Mathlib.Tactic
import InfoGeometry.Topology.FractalCantorFockWitness
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Topology.CliffordFractalWaveletBridge

Clifford fractal wavelets.

The bit is not the physical object.  The bit is address data.  A finite binary
word indexes a Cantor cylinder, and the corresponding physical carrier is a
fractal wavelet mode attached to that address.  Tilt/switch operators act on
these modes as Clifford/Walsh operations.  Drazin support and the Hodge/Drazin
harmonic projector then extract the stable physical envelope.

The theorem-safe chain is:

`binary word -> Cantor cylinder -> fractal wavelet mode -> tilt/switch Clifford
 action -> Fock/CAR mode -> Drazin-Hodge envelope -> Fierz-Klein readout`.
-/

noncomputable section

namespace InfoGeometry.Topology.CliffordFractalWaveletBridge

open InfoGeometry.Topology.FractalCantorFockWitness

/-! ## 1. Binary addresses and fractal wavelet modes -/

/-- Fractal wavelet modes indexed by finite binary words. -/
@[rep_depth transport]
structure FractalWaveletAddress where
  depth : ℕ
  WaveletMode : Type
  waveletOfWord : Fin depth → Bool → WaveletMode

/--
Abstract Clifford fractal wavelet socket.

This is the primitive socket for the corrected slogan:
`geometry from Clifford fractal wavelets`.
-/
@[socket_debt_tag, rep_depth operator]
structure CliffordFractalWaveletSocket
    (Op : Type*) [Ring Op] where
  address : FractalWaveletAddress
  representation : RealDoubledCantorCliffordRepresentation Op

namespace CliffordFractalWaveletSocket

variable {Op : Type*} [Ring Op]
variable (C : CliffordFractalWaveletSocket Op)

/-- Tilt squares to one. -/
@[rep_depth operator]
theorem tilt_sq (j : ℕ) :
    C.representation.tiltSwitch.T j * C.representation.tiltSwitch.T j = 1 :=
  C.representation.tiltSwitch.T_sq j

/-- Switch squares to one. -/
@[rep_depth operator]
theorem switch_sq (j : ℕ) :
    C.representation.tiltSwitch.S j * C.representation.tiltSwitch.S j = 1 :=
  C.representation.tiltSwitch.S_sq j

/-- Tilt and switch anticommute at the same address slot. -/
@[rep_depth operator]
theorem tilt_switch_anticomm (j : ℕ) :
    C.representation.tiltSwitch.T j * C.representation.tiltSwitch.S j +
        C.representation.tiltSwitch.S j * C.representation.tiltSwitch.T j = 0 := by
  rw [C.representation.tiltSwitch.T_S_anticomm j]
  simp

theorem tilt_switch_commutator_ne {i j : ℕ} (hij : i ≠ j) :
    C.representation.tiltSwitch.T i * C.representation.tiltSwitch.S j -
        C.representation.tiltSwitch.S j * C.representation.tiltSwitch.T i = 0 := by
  rw [C.representation.tiltSwitch.T_S_comm_ne i j hij]
  exact sub_self _

/-- Clifford generator square law. -/
@[rep_depth operator]
theorem gamma_square (i : ℕ) :
    C.representation.gamma i * C.representation.gamma i = 1 :=
  C.representation.gamma_sq i

/-- Clifford generator anticommutator law. -/
@[rep_depth operator]
theorem gamma_anticommutator {i j : ℕ} (hij : i ≠ j) :
    C.representation.gamma i * C.representation.gamma j +
        C.representation.gamma j * C.representation.gamma i = 0 := by
  rw [C.representation.gamma_anticomm i j hij]
  simp

theorem gamma_commutator {i j : ℕ} (hij : i ≠ j) :
    C.representation.gamma i * C.representation.gamma j -
        C.representation.gamma j * C.representation.gamma i =
      2 * (C.representation.gamma i * C.representation.gamma j) := by
  rw [C.representation.gamma_anticomm i j hij]
  simpa [sub_eq_add_neg] using
    (two_mul (-(C.representation.gamma j * C.representation.gamma i))).symm

end CliffordFractalWaveletSocket

/-! ## Direct relation for the Clifford fractal wavelet generators -/

def IsCliffordFractalWaveletSystem
    {Op : Type*} [Ring Op]
    (T S gamma : ℕ → Op) : Prop :=
  (∀ j, T j * T j = 1) ∧
  (∀ j, S j * S j = 1) ∧
  (∀ j, T j * S j = -(S j * T j)) ∧
  (∀ i j, i ≠ j → T i * S j = S j * T i) ∧
  (∀ i, gamma i * gamma i = 1) ∧
  (∀ i j, i ≠ j → gamma i * gamma j = -(gamma j * gamma i))

theorem CliffordFractalWaveletSocket.isSystem
    {Op : Type*} [Ring Op]
    (C : CliffordFractalWaveletSocket Op) :
    IsCliffordFractalWaveletSystem
      C.representation.tiltSwitch.T C.representation.tiltSwitch.S
      C.representation.gamma := by
  exact ⟨C.representation.tiltSwitch.T_sq,
    C.representation.tiltSwitch.S_sq,
    C.representation.tiltSwitch.T_S_anticomm,
    C.representation.tiltSwitch.T_S_comm_ne,
    C.representation.gamma_sq, C.representation.gamma_anticomm⟩

theorem CliffordFractalWaveletSocket.tilt_switch_product_sq
    {Op : Type*} [Ring Op]
    (C : CliffordFractalWaveletSocket Op) (j : ℕ) :
    (C.representation.tiltSwitch.T j * C.representation.tiltSwitch.S j) *
        (C.representation.tiltSwitch.T j * C.representation.tiltSwitch.S j) = -1 := by
  have hrev : C.representation.tiltSwitch.S j * C.representation.tiltSwitch.T j =
      -(C.representation.tiltSwitch.T j * C.representation.tiltSwitch.S j) := by
    rw [C.representation.tiltSwitch.T_S_anticomm j]
    simp
  calc
    (C.representation.tiltSwitch.T j * C.representation.tiltSwitch.S j) *
        (C.representation.tiltSwitch.T j * C.representation.tiltSwitch.S j) =
        C.representation.tiltSwitch.T j *
          (C.representation.tiltSwitch.S j * C.representation.tiltSwitch.T j) *
          C.representation.tiltSwitch.S j := by
          simp [mul_assoc]
    _ = C.representation.tiltSwitch.T j *
          (-(C.representation.tiltSwitch.T j * C.representation.tiltSwitch.S j)) *
          C.representation.tiltSwitch.S j := by rw [hrev]
    _ = -(C.representation.tiltSwitch.T j * C.representation.tiltSwitch.T j) *
          (C.representation.tiltSwitch.S j * C.representation.tiltSwitch.S j) := by
      noncomm_ring
    _ = -1 := by
      rw [C.representation.tiltSwitch.T_sq j,
        C.representation.tiltSwitch.S_sq j]
      simp

/-! ## 2. Drazin-Hodge scaling/detail split -/

/-- Scaling, or low-pass, projector: the Drazin-Green harmonic projector. -/
@[rep_depth operator]
def scalingProjector
    {Op : Type*} [Ring Op]
    (G : DrazinGreenHarmonic Op) : Op :=
  G.H

/-- Detail, or high-pass, projector: the regular frequency support `L Lᴰ`. -/
@[rep_depth operator]
def detailProjector
    {Op : Type*} [Ring Op]
    (G : DrazinGreenHarmonic Op) : Op :=
  G.L * G.LD

/-- Scaling/detail complement law: `H + L Lᴰ = 1`. -/
@[rep_depth operator]
theorem scaling_add_detail_eq_one
    {Op : Type*} [Ring Op]
    (G : DrazinGreenHarmonic Op) :
    scalingProjector G + detailProjector G = 1 := by
  simp [scalingProjector, detailProjector, G.H_def]

/-- Scaling projector is idempotent. -/
@[rep_depth operator]
theorem scalingProjector_idempotent
    {Op : Type*} [Ring Op]
    (G : DrazinGreenHarmonic Op) :
    scalingProjector G * scalingProjector G = scalingProjector G := by
  simpa [scalingProjector] using G.H_idempotent

/-- Physical Clifford fractal wavelet envelope. -/
@[rep_depth operator]
def physicalCliffordFractalWavelet
    {Op : Type*} [Ring Op]
    (pA HL x : Op) : Op :=
  HL * (pA * x * pA) * HL

/-! ## 3. Stabilized Clifford fractal wavelet packets -/

/--
Stabilized Clifford fractal wavelet packet.

`rawWaveletObservable` is the Clifford fractal wavelet field before filtering.
The physical coefficient is the harmonic Drazin envelope.
-/
@[rep_depth operator]
structure StabilizedCliffordFractalWavelet
    (Op : Type*) [Ring Op] where
  wavelet : CliffordFractalWaveletSocket Op
  horizon : DrazinHorizon Op
  harmonic : DrazinGreenHarmonic Op
  rawWaveletObservable : Op

namespace StabilizedCliffordFractalWavelet

variable {Op : Type*} [Ring Op]
variable (W : StabilizedCliffordFractalWavelet Op)

/-- Signal-compressed raw wavelet observable. -/
@[rep_depth operator]
def supportCompressedWavelet : Op :=
  W.horizon.p * W.rawWaveletObservable * W.horizon.p

/-- Retained harmonic/scaling coefficient. -/
@[rep_depth operator]
def physicalEnvelope : Op :=
  physicalCliffordFractalWavelet
    W.horizon.p W.harmonic.H W.rawWaveletObservable

/-- Detail/high-pass coefficient, kept separate from the physical envelope. -/
@[rep_depth operator]
def detailEnvelope : Op :=
  detailProjector W.harmonic *
    W.supportCompressedWavelet *
      detailProjector W.harmonic

/-- The physical envelope is the existing Drazin-Hodge matter envelope. -/
@[rep_depth operator]
theorem physicalEnvelope_eq_matterEnvelope :
    W.physicalEnvelope =
      fractalFockMatterEnvelope W.horizon W.harmonic W.rawWaveletObservable := by
  rfl

/-- The low/high projectors split the Drazin-Green frequency lane. -/
@[rep_depth operator]
theorem low_high_projector_sum :
    scalingProjector W.harmonic + detailProjector W.harmonic = 1 :=
  scaling_add_detail_eq_one W.harmonic

end StabilizedCliffordFractalWavelet

/-! ## 4. Fierz-Klein readout -/

/--
Fierz-Klein readout from the stabilized Clifford fractal wavelet envelope.

The coordinates are required to be read from `physicalEnvelope`, not from a raw
bit or unfiltered wavelet observable.
-/
@[rep_depth operator]
structure CliffordFractalWaveletFierzKleinLaw
    (Op : Type*) [Ring Op] where
  stabilized : StabilizedCliffordFractalWavelet Op
  readout : FierzReadout Op
  coords : FierzChannel → ℝ
  residual : (FierzChannel → ℝ) → ℝ

  coords_def :
    ∀ ch : FierzChannel,
      coords ch = readout.channel ch stabilized.physicalEnvelope

  quadric_zero_property :
    residual coords = 0

namespace CliffordFractalWaveletFierzKleinLaw

variable {Op : Type*} [Ring Op]
variable (L : CliffordFractalWaveletFierzKleinLaw Op)

/-- Coordinates are read from the harmonic Drazin envelope. -/
@[rep_depth operator]
theorem coords_from_physicalEnvelope (ch : FierzChannel) :
    L.coords ch = L.readout.channel ch L.stabilized.physicalEnvelope :=
  L.coords_def ch

/-- The wavelet envelope lies on the chosen Fierz-Klein quadric. -/
@[rep_depth operator]
theorem quadric_zero :
    L.residual L.coords = 0 :=
  L.quadric_zero_property

end CliffordFractalWaveletFierzKleinLaw

end InfoGeometry.Topology.CliffordFractalWaveletBridge
