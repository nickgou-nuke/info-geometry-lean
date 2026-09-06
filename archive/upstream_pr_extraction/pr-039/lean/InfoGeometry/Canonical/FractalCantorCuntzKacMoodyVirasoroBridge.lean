import Mathlib.Tactic
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
import InfoGeometry.Core.MajoranaLiftPacket
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Geometry.RealMoebiusAction
import InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost
import InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
import InfoGeometry.OperatorAlgebra.VirasoroProjectBridge
import InfoGeometry.OperatorAlgebra.SuperVirasoroExtension
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

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.FractalCantorCuntzKacMoodyVirasoroBridge

open InfoGeometry.Core
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
open InfoGeometry.Geometry
open InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost
open InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
open InfoGeometry.OperatorAlgebra.VirasoroProjectBridge
open InfoGeometry.OperatorAlgebra.SuperVirasoroExtension
open InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift

/-! ## Native VirasoroProject owner -/

/--
The fractal/Cuntz bridge imports a concrete Virasoro owner rather than treating
the existence of Virasoro generators as an evidence field.
-/
@[rep_depth operator]
theorem virasoroProject_owner_exists :
    ∃ V : VirasoroDatum (VirasoroProject.VirasoroAlgebra ℝ),
      VirasoroProjectRealizes V :=
  virasoro_project_has_realized_datum

/--
The central element in the imported Virasoro owner genuinely commutes with
every Virasoro element.
-/
@[rep_depth operator]
theorem virasoroProject_central_commutes :
    ∀ X : VirasoroProject.VirasoroAlgebra ℝ,
      ⁅virasoroProjectVirasoroDatum.central, X⁆ = 0 :=
  virasoroProjectVirasoroDatum_central_commutes

/--
The imported Virasoro generators satisfy the native coefficient-normalized
Virasoro bracket.
-/
@[rep_depth operator]
theorem virasoroProject_bracket :
    ∀ m n : ℤ,
      ⁅virasoroProjectVirasoroDatum.Lmode m,
          virasoroProjectVirasoroDatum.Lmode n⁆ =
        (m - n : ℝ) • virasoroProjectVirasoroDatum.Lmode (m + n) +
          (virasoroCentralCoefficient m n : ℝ) •
            virasoroProjectVirasoroDatum.central :=
  virasoroProjectVirasoroDatum_bracket


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
* `sugawara` carries the supplied mode-sum construction and owns its
  affine/Virasoro bridge;
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
    PrimeSpinorSquareRootData ℕ ℝ

  /-- Real Bogoliubov transformation shadow data. -/
  bogoljubov :
    InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowData
      E Op Op Op Op Op

  /--
  The supplied Sugawara mode-sum construction.

  Its `bridge` field is the unique owner of the affine-current and Virasoro
  data, avoiding parallel carriers connected only by equality fields.
  -/
  sugawara :
    SugawaraModeConstructionDatum Finite Alg

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

/-- The affine/Virasoro bridge owned by the Sugawara construction. -/
@[rep_depth operator]
abbrev bridge : AffineVirasoroBridgeDatum Finite Alg :=
  B.sugawara.bridge

/-- The affine-current datum owned by the Sugawara bridge. -/
@[rep_depth operator]
abbrev kacMoody : AffineCurrentDatum Finite Alg :=
  B.sugawara.bridge.affine

/-- The Virasoro datum owned by the Sugawara bridge. -/
@[rep_depth operator]
abbrev virasoro : VirasoroDatum Alg :=
  B.sugawara.bridge.virasoro


/-- The spinor-boost dictionary validates the bilinear partition law. -/
@[rep_depth operator]
theorem boost_bilinear_partition_holds :
    finitePrimeSpinorBilinearProduct B.boost.modes B.boost.amplitude =
      finitePrimeWeylDenominator B.boost.modes
        (fun p => scalarWeightFromSpinor (B.boost.amplitude p)) :=
  B.boost.bilinear_partition

/-- The canonical doubled-space Majorana phase axis squares to `-Id`. -/
@[rep_depth krein]
theorem majorana_phase_axis_sq_eq_neg_id :
    (InfoGeometry.Krein.complex_i (E := E)).comp
        (InfoGeometry.Krein.complex_i (E := E)) =
      -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) := by
  exact InfoGeometry.Krein.complex_i_sq (E := E)

/--
Recovered Majorana API: the canonical owner phase axis squares to `-Id`.

Unlike the former packet theorem, this statement is directly about the
repo-owned continuous linear map and stores no duplicate operator or proof
field.
-/
@[rep_depth krein]
theorem majorana_packet_K_sq_eq_neg_id :
    (InfoGeometry.Core.canonicalMajoranaK (E := E)).comp
        (InfoGeometry.Core.canonicalMajoranaK (E := E)) =
      -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) :=
  InfoGeometry.Core.canonicalMajoranaK_sq_eq_neg_id (E := E)


/-- The Bogoliubov shadow exposes the phase-axis force law from the Cartan shadow. -/
@[rep_depth operator]
theorem bogoljubov_packet_phaseAxisForce_from_cartanScaleShadow
    [CompleteSpace E]
    (H : InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowData.doubledKreinEnd
        (E := E)) :
    InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowData.cartanGaugeShadow
        (E := E) H +
      InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowData.cartanScaleShadow
        (E := E) H =
        BogoliubovTransport.modularTransportGenerator (E := E) H := by
  simpa using
    (InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift.BogoliubovKANShadowData.cartanGaugeShadow_add_cartanScaleShadow
      (E := E) H)


end FractalCantorCuntzKacMoodyVirasoroBridge

end InfoGeometry.Canonical.FractalCantorCuntzKacMoodyVirasoroBridge
