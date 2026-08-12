import Mathlib.Tactic
import InfoGeometry.Canonical.CantorCuntzCliffordBridge
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.FractalCantorCuntzKacMoodyVirasoroBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.MoebiusBogoliubovVirasoro

Theorem-safe bridge for the Möbius / Lorentz / Bogoliubov / Virasoro lane.

This file does not derive the full conformal field theory pipeline from raw
binary words.  It records the exact owner-level readouts already supported by
the repository:

* diagonal Möbius boosts as determinant-one matrices;
* the associated hyperbolic Bogoliubov tilt angle;
* a finite binary-word `L₀` depth-dilation readout.

The bridge is intentionally narrow and proof-carrying.
-/

noncomputable section

namespace InfoGeometry.Canonical.MoebiusBogoliubovVirasoro

open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical
open InfoGeometry.Canonical.FractalCantorCuntzKacMoodyVirasoroBridge
open InfoGeometry.Canonical.TypeIIIModularCantorSystem

/-! ## 1. Möbius matrices and diagonal boosts -/

/-- A real Möbius matrix with determinant one. -/
@[rep_depth projective]
structure MoebiusMatrix (R : Type*) [CommRing R] where
  a : R
  b : R
  c : R
  d : R
  det_one : a * d - b * c = 1

/-- The diagonal Lorentz/Möbius boost `diag(η, η⁻¹)`. -/
@[rep_depth projective]
def diagonalBoost (η : ℝ) (hη : 0 < η) : MoebiusMatrix ℝ where
  a := η
  b := 0
  c := 0
  d := η⁻¹
  det_one := by
    have hne : η ≠ 0 := ne_of_gt hη
    simp [hne]

/-- A canonical hyperbolic tilt extracted from a positive boost factor. -/
@[rep_depth projective]
def bogoliubovTiltOfBoost (η : ℝ) : BogoliubovMixingParams :=
  HyperbolicMixingParams.ofAngle (Real.log η)

/-! ## 2. Tilted Cuntz/CAR readout -/

/--
Tilted CAR generator from Cuntz isometries.

This is the native readout used by the integration hub.  The CAR/CCR phase
transition itself is not derivable from the bare Cuntz relations, so the
nontrivial commutation readouts are stored as property fields in
`TiltedCuntzCARPacket`.
-/
@[rep_depth operator]
def tiltedCARFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op] [Module ℝ Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (B : BogoliubovMixingParams) : Op :=
  B.u • ((InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) + B.v • ((InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C))

/-- The tilted CAR generator reduces to the untitled Cuntz CAR channel at zero tilt. -/
@[rep_depth operator]
theorem tiltedCARFromCuntz_zero_tilt
    {Op : Type*} [Ring Op] [StarRing Op] [Module ℝ Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    tiltedCARFromCuntz C (HyperbolicMixingParams.ofAngle 0)
      = (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
  simp [tiltedCARFromCuntz, HyperbolicMixingParams.ofAngle]

/--
Proof-carrying packet for the tilted Cuntz/CAR readout.

The mixed and self anticommutator formulas are not claimed from the Cuntz
relations alone; they are explicit model data that downstream files may
instantiate when they have a concrete representation.
-/
@[rep_depth operator]
structure TiltedCuntzCARPacket
    (Op : Type*) [Ring Op] [StarRing Op] [Module ℝ Op] where
  cuntz : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op
  tilt : BogoliubovMixingParams
  tiltedCAR : Op
  tiltedCAR_eq :
    tiltedCAR = tiltedCARFromCuntz cuntz tilt
  mixedAnticommutator : Op
  mixedAnticommutator_eq :
    mixedAnticommutator =
      (tiltedCAR * star tiltedCAR + star tiltedCAR * tiltedCAR)
  mixedAnticommutator_readout :
    mixedAnticommutator = (tilt.u ^ 2 + tilt.v ^ 2) • (1 : Op)
  selfAnticommutator : Op
  selfAnticommutator_eq :
    selfAnticommutator = (tiltedCAR * tiltedCAR + tiltedCAR * tiltedCAR)
  selfAnticommutator_readout :
    selfAnticommutator = (2 * tilt.u * tilt.v) • (1 : Op)

/--
The diagonal Möbius boost induces the standard hyperbolic Bogoliubov
parameters `u = cosh(log η)` and `v = sinh(log η)`.
-/
@[rep_depth projective]
theorem moebius_to_bogoliubov_mapping
    (η : ℝ) (hη : 0 < η) :
    let B : BogoliubovMixingParams := bogoliubovTiltOfBoost η
    B.u = (η + η⁻¹) / 2 ∧ B.v = (η - η⁻¹) / 2 := by
  dsimp [bogoliubovTiltOfBoost]
  constructor
  · simp [HyperbolicMixingParams.ofAngle, Real.cosh_log hη]
  · simp [HyperbolicMixingParams.ofAngle, Real.sinh_log hη]

/-! ## 2. Virasoro `L₀` as a binary-depth dilation readout -/

/-- Depth of a finite binary path. -/
@[rep_depth operator]
def wordDepth
    (w : List Bool) : ℕ :=
  w.length

/-- Hyperbolic `L₀`-style dilation on a binary word. -/
@[rep_depth operator]
def virasoroL0Dilation
    (L0 : ℝ)
    (w : List Bool) : ℝ :=
  Real.exp L0 * (wordDepth w : ℝ)

/-- One child step increases the binary depth by one. -/
@[rep_depth operator]
theorem wordDepth_child
    (w : List Bool) (b : Bool) :
    wordDepth (TypeIIIModularCantorSystem.child w b) = wordDepth w + 1 := by
  simp [wordDepth, TypeIIIModularCantorSystem.child]

/-- `L₀` dilation on a child word is one exponential step larger. -/
@[rep_depth operator]
theorem virasoroL0Dilation_child
    (L0 : ℝ) (w : List Bool) (b : Bool) :
    virasoroL0Dilation L0 (TypeIIIModularCantorSystem.child w b)
      = virasoroL0Dilation L0 w + Real.exp L0 := by
  rw [virasoroL0Dilation, wordDepth_child, virasoroL0Dilation]
  rw [Nat.cast_add, Nat.cast_one]
  ring

/-! ## 3. Bridge packet -/

/--
Bridge packet for the Möbius / Bogoliubov / Virasoro lane.

The packet reuses the already-owned Cantor/Cuntz/Kac--Moody/Virasoro backbone
and records the exact diagonal boost and `L₀`-dilation readouts.
-/
@[rep_depth operator]
structure MoebiusBogoliubovVirasoroBridge
    (E Op Hilb Spin Finite Alg : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup Hilb] [NormedSpace ℂ Hilb] [SMul Op Hilb]
    [NormedAddCommGroup Spin] [InnerProductSpace ℝ Spin] [CompleteSpace Spin]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  /-- The binary Cantor / Cuntz / CAR / Kac--Moody / Virasoro backbone. -/
  fractal :
    FractalCantorCuntzKacMoodyVirasoroBridge
      E Op Hilb Finite Alg

  /-- The diagonal Möbius boost readout. -/
  moebiusMatrix : MoebiusMatrix ℝ

  /-- The Möbius matrix is the explicit diagonal boost readout. -/
  moebiusMatrix_eq_diagonalBoost :
    moebiusMatrix = diagonalBoost boostParameter boostParameter_pos

  /-- The positive boost parameter extracted from the Möbius sector. -/
  boostParameter : ℝ

  /-- The boost parameter is positive so the diagonal boost is well-posed. -/
  boostParameter_pos : 0 < boostParameter

  /-- The Bogoliubov tilt angle is the logarithmic boost readout. -/
  tilt :
    BogoliubovMixingParams

  /-- The tilt is normalized as `ofAngle (log boostParameter)`. -/
  tilt_eq_ofAngle :
    tilt = bogoliubovTiltOfBoost boostParameter

  /-- The Virasoro depth parameter. -/
  virasoroL0 : ℝ

  /-- The `L₀` dilation readout on finite binary words. -/
  virasoroDilation : List Bool → ℝ

  /-- The dilation readout is exactly the exponential depth scale. -/
  virasoroDilation_eq :
    ∀ w : List Bool,
      virasoroDilation w = virasoroL0Dilation virasoroL0 w

variable
    {E Op Hilb Spin Finite Alg : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup Hilb] [NormedSpace ℂ Hilb] [SMul Op Hilb]
    [NormedAddCommGroup Spin] [InnerProductSpace ℝ Spin] [CompleteSpace Spin]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B : MoebiusBogoliubovVirasoroBridge E Op Hilb Spin Finite Alg)

/-- The Möbius boost matrix is the explicit diagonal boost readout. -/
@[rep_depth projective]
theorem moebiusMatrix_eq_diagonalBoost_holds :
    B.moebiusMatrix =
      diagonalBoost B.boostParameter B.boostParameter_pos :=
  B.moebiusMatrix_eq_diagonalBoost

/-- The hyperbolic Bogoliubov tilt is normalized as the boost-induced angle. -/
@[rep_depth projective]
theorem tilt_normalized_holds :
    B.tilt = bogoliubovTiltOfBoost B.boostParameter :=
  B.tilt_eq_ofAngle

/-- The Virasoro dilation readout is exactly the exponential depth scale. -/
@[rep_depth operator]
theorem virasoroDilation_eq_holds :
    ∀ w : List Bool,
      B.virasoroDilation w = virasoroL0Dilation B.virasoroL0 w :=
  B.virasoroDilation_eq

end InfoGeometry.Canonical.MoebiusBogoliubovVirasoro
