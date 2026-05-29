import Mathlib
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
import InfoGeometry.Core.MajoranaLiftPacket
import InfoGeometry.Canonical.MajoranaLiftPacketBridge
import InfoGeometry.Geometry.RealMoebiusAction
import InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
import InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.FractalCantorCuntzKacMoodyVirasoroBridge

Theorem-safe owner packet for compatible structures drawn from several levels:

`binary Cantor lattice`, `Cuntz O₂`, `CAR/Fock`, `affine Kac--Moody`,
`Virasoro`, `Sugawara`, and `super-Virasoro`.

This is not a derivation of the high current/conformal layers from the finite
Cantor/Cuntz/CAR seed.  The affine, Virasoro, Sugawara, and super-Virasoro
fields are supplied owner data, and the theorems below read back their
compatibility laws.

This file records the already-owned theorem surfaces as a single compatibility
packet, now expanded to include:

* Real Bogoljubov Transformations (CAR symmetries);
* Boosts and Lorentz Symmetry (Spinor square-root layer);
* Tilt Operators (Cantor code switches);
* Discrete Möbius Symmetry (UHP action);
* Majorana Lift (Real carrier doubling).

Boundary: no raw finite-algebra isomorphism is asserted here, and no
source-side normal-ordering construction is supplied by this packet.
-/

noncomputable section

namespace InfoGeometry.Canonical.FractalCantorCuntzKacMoodyVirasoroBridge

open InfoGeometry.Core
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
open InfoGeometry.Geometry
open InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost
open InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
open InfoGeometry.OperatorAlgebra.SuperVirasoroExtension
open InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift

/-- Re-export of the infinite symbolic Cantor boundary. -/
@[rep_depth operator]
abbrev InfiniteBinaryWordSpace :=
  InfoGeometry.Canonical.FractalCantorCliffordFockBridge.InfiniteBinaryWordSpace

/-- Re-export of the finite binary path codes. -/
@[rep_depth operator]
abbrev FiniteBinaryWord :=
  InfoGeometry.Canonical.FractalCantorCliffordFockBridge.FiniteBinaryWord

/--
Compatibility packet for the Cantor/Cuntz/Kac--Moody/Virasoro owner surfaces.

The bridge is intentionally theorem-safe and proof-carrying, but the
current/conformal layers are owner fields rather than consequences of the
finite Cantor/Cuntz/CAR data:

* `fractal` carries the binary Cantor/Cuntz/CAR/Fock backbone;
* `tilt` carries the bit-code tilt/switch algebra;
* `moebius` carries the discrete fractional-linear action;
* `boost` carries the prime-mode spinor square-root dictionary;
* `majorana` carries the real-carrier doubling lift;
* `bogoljubov` carries the real Bogoliubov KAN shadow;
* `kacMoody` carries the supplied affine current algebra;
* `virasoro` carries the supplied Virasoro modes and central element;
* `bridge` ties the supplied affine and Virasoro layers together;
* `sugawara` carries the supplied mode-sum construction;
* `superVirasoro` carries the supplied super-Virasoro extension.
-/
@[rep_depth operator]
structure FractalCantorCuntzKacMoodyVirasoroBridge
    (E Op H Finite Alg : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  /-- The binary Cantor / Cuntz / CAR / Fock backbone. -/
  fractal :
    InfoGeometry.Topology.CuntzCantorSpectralTriple Op H

  /-- Bit-code tilt/switch system on the Cantor code. -/
  tilt :
    BinaryWordTiltReadout Op

  /-- Discrete Möbius action on the real upper half-plane. -/
  moebius :
    RealUpperHalfPlane

  /-- The prime-mode spinor square-root dictionary. -/
  boost :
    PrimeSpinorSquareRootPacket ℕ ℝ Op Op

  /-- The canonical Majorana lift packet. -/
  majorana :
    MajoranaLiftPacket (E := E)

  /-- Real Bogoliubov transformation shadow data. -/
  bogoljubov :
    BogoliubovKANShadowPacket E Op Op Op Op Op

  /-- The affine-current Kac--Moody owner datum. -/
  kacMoody :
    AffineCurrentDatum Finite Alg

  /-- The Virasoro owner datum. -/
  virasoro :
    VirasoroDatum Alg

  /-- The combined affine-current / Virasoro bridge. -/
  bridge :
    AffineVirasoroBridgeDatum Finite Alg

  /-- The bridge's affine layer is the supplied Kac--Moody datum. -/
  bridge_affine_eq :
    bridge.affine = kacMoody

  /-- The bridge's Virasoro layer is the supplied Virasoro datum. -/
  bridge_virasoro_eq :
    bridge.virasoro = virasoro

  /-- The supplied Sugawara mode-sum construction. -/
  sugawara :
    SugawaraModeConstructionDatum Finite Alg

  /-- The Sugawara datum uses the same affine/Virasoro bridge. -/
  sugawara_uses_bridge :
    sugawara.bridge = bridge

  /-- The super-Virasoro owner datum. -/
  superVirasoro :
    SuperVirasoroAlgebraDatum Alg


namespace FractalCantorCuntzKacMoodyVirasoroBridge

variable
    {E Op H Finite Alg : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B : FractalCantorCuntzKacMoodyVirasoroBridge E Op H Finite Alg)

/-- The spinor-boost dictionary validates the bilinear partition law. -/
@[rep_depth operator]
theorem boost_bilinear_partition_valid :
    finitePrimeSpinorBilinearProduct B.boost.modes B.boost.amplitude =
      finitePrimeWeylDenominator B.boost.modes
        (fun p => scalarWeightFromSpinor (B.boost.amplitude p)) :=
  B.boost.bilinear_partition

/-- The Majorana packet exposes the phase-axis square law. -/
@[rep_depth krein]
theorem majorana_packet_K_sq_eq_neg_id :
    B.majorana.K.comp B.majorana.K =
      -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) := by
  simpa using
    (InfoGeometry.Core.MajoranaLiftPacket.K_sq_eq_neg_id
      (E := E) (P := B.majorana))

/-- Backwards-compatible name for the Majorana packet square law. -/
@[rep_depth krein]
theorem majorana_packet_valid :
    B.majorana.K.comp B.majorana.K =
      -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) :=
  majorana_packet_K_sq_eq_neg_id (B := B)

/-- The Bogoliubov shadow exposes the phase-axis force law from the Cartan shadow. -/
@[rep_depth operator]
theorem bogoljubov_packet_phaseAxisForce_from_cartanScaleShadow
    [CompleteSpace E]
    (H : InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowPacket.doubledKreinEnd
        (E := E)) :
    InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowPacket.cartanGaugeShadow
        (E := E) H +
      InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowPacket.cartanScaleShadow
        (E := E) H =
        BogoliubovTransport.modularTransportGenerator (E := E) H := by
  simpa using
    (InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowPacket.cartanGaugeShadow_add_cartanScaleShadow
      (E := E) H)

/-- Backwards-compatible name for the Bogoljubov phase-axis force law. -/
@[rep_depth operator]
theorem bogoljubov_packet_valid
    [CompleteSpace E]
    (H : InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowPacket.doubledKreinEnd
        (E := E)) :
  InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowPacket.cartanGaugeShadow
        (E := E) H +
      InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowPacket.cartanScaleShadow
        (E := E) H =
        BogoliubovTransport.modularTransportGenerator (E := E) H :=
  bogoljubov_packet_phaseAxisForce_from_cartanScaleShadow (E := E) H

end FractalCantorCuntzKacMoodyVirasoroBridge

end InfoGeometry.Canonical.FractalCantorCuntzKacMoodyVirasoroBridge
