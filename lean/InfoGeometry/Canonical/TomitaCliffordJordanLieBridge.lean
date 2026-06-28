import InfoGeometry.OperatorAlgebra.TomitaCartanSplit
import InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge

/-!
# Tomita-Cartan parity to Clifford Jordan/Lie readouts

This module is the narrow connector between two existing corridors:

* `TomitaCartanSplit`: compact lifts are mirror-even and noncompact lifts are
  mirror-odd;
* `SplitCl44TKKJordanLieBridge`: anticommutators are the symmetric Jordan
  channel and commutators are the antisymmetric Lie channel.

It deliberately does not identify factor overlap with the isotropic cone, and
it does not assert any new `Cl(4,4)` classification theorem.  Concrete models
must supply the two calibration certificates saying that their mirror-even
sector feeds the symmetric/Jordan observable readout and their mirror-odd
sector feeds the antisymmetric/Lie generator readout.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.TomitaCliffordJordanLieBridge

open InfoGeometry.OperatorAlgebra.TomitaCartanSplit
open InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge

variable {α : Type _}
variable {Op : Type _} [Ring Op]
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ## Bridge datum -/

/--
Proof-carrying bridge from Tomita-Cartan mirror parity to the repo-owned
Clifford/TKK Jordan-Lie readouts.

The actual parity-to-physics calibration is intentionally stored as data:

* compact/mirror-even sector feeds the symmetric observable/Jordan readout;
* noncompact/mirror-odd sector feeds the antisymmetric generator/Lie readout.

The algebraic parity laws and the Jordan/Lie product identities are proved
by the imported owner modules and re-exported below.
-/
@[rep_depth transport]
structure TomitaCliffordJordanLieBridge where
  /-- Tomita-style mirror involution on the algebraic operator lane. -/
  mirror : MirrorInvolution Op

  /-- Split `Cl(4,4)` / TKK / Jordan-Lie packet. -/
  packet : SplitCl44TKKJordanLiePacket (α := α) (H := H)

  /--
  Calibration law: the compact/mirror-even sector feeds the symmetric
  observable/Jordan readout.
  -/
  compactEvenFeedsJordan : Prop

  /-- Evidence for the compact/Jordan calibration law. -/
  compact_even_feeds_jordan :
    compactEvenFeedsJordan

  /--
  Calibration law: the noncompact/mirror-odd sector feeds the antisymmetric
  generator/Lie readout.
  -/
  noncompactOddFeedsLie : Prop

  /-- Evidence for the noncompact/Lie calibration law. -/
  noncompact_odd_feeds_lie :
    noncompactOddFeedsLie

namespace TomitaCliffordJordanLieBridge

variable (B : TomitaCliffordJordanLieBridge (α := α) (Op := Op) (H := H))

/-! ## Tomita-Cartan parity re-exports -/

/-- Compact Tomita-Cartan lifts are mirror-even. -/
@[rep_depth transport]
theorem compactLift_mirror_even
    (x : Op) :
    B.mirror.mirror (B.mirror.compactLift x) = B.mirror.compactLift x :=
  B.mirror.mirror_compactLift x

/-- Noncompact Tomita-Cartan lifts are mirror-odd. -/
@[rep_depth transport]
theorem noncompactLift_mirror_odd
    (x : Op) :
    B.mirror.mirror (B.mirror.noncompactLift x) = -B.mirror.noncompactLift x :=
  B.mirror.mirror_noncompactLift x

/-! ## Clifford/TKK Jordan-Lie readout re-exports -/

/-- The commutator channel is twice the antisymmetric Lie product. -/
@[rep_depth transport]
theorem commutator_eq_two_smul_lieProduct :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator (E := H)
      B.packet.closure.gibbs.conformalGeometricTemperature
      B.packet.closure.weylTemperature =
        (2 : ℝ) • B.packet.closure.lieProductTemperatureWeyl :=
  B.packet.fockCommutator_temperature_weyl_eq_two_smul_lieProduct

/-- The anticommutator channel is twice the symmetric Jordan product. -/
@[rep_depth transport]
theorem anticommutator_eq_two_smul_jordanProduct :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator (E := H)
      B.packet.closure.gibbs.conformalGeometricTemperature
      B.packet.closure.weylTemperature =
        (2 : ℝ) • B.packet.closure.jordanProductTemperatureWeyl :=
  B.packet.fockAnticommutator_temperature_weyl_eq_two_smul_jordanProduct

/-! ## Calibration re-exports -/

/--
Stored calibration: compact/mirror-even Tomita-Cartan parity feeds the
symmetric observable/Jordan readout.
-/
@[rep_depth transport]
theorem compact_even_feeds_jordan_holds :
    B.compactEvenFeedsJordan :=
  B.compact_even_feeds_jordan

/--
Stored calibration: noncompact/mirror-odd Tomita-Cartan parity feeds the
antisymmetric generator/Lie readout.
-/
@[rep_depth transport]
theorem noncompact_odd_feeds_lie_holds :
    B.noncompactOddFeedsLie :=
  B.noncompact_odd_feeds_lie

/--
Consolidated Tomita/Clifford/Jordan-Lie bridge packet.

This theorem is intentionally narrow: it packages exactly the mirror parity
facts, the repo-owned commutator/anticommutator readouts, and the two supplied
calibration certificates.
-/
@[rep_depth transport]
theorem tomita_clifford_jordan_lie_packet
    (x y : Op) :
    B.mirror.mirror (B.mirror.compactLift x) = B.mirror.compactLift x
      ∧ B.mirror.mirror (B.mirror.noncompactLift y) = -B.mirror.noncompactLift y
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator (E := H)
          B.packet.closure.gibbs.conformalGeometricTemperature
          B.packet.closure.weylTemperature =
            (2 : ℝ) • B.packet.closure.lieProductTemperatureWeyl
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator (E := H)
          B.packet.closure.gibbs.conformalGeometricTemperature
          B.packet.closure.weylTemperature =
            (2 : ℝ) • B.packet.closure.jordanProductTemperatureWeyl
      ∧ B.compactEvenFeedsJordan
      ∧ B.noncompactOddFeedsLie := by
  exact
    ⟨B.compactLift_mirror_even x,
      B.noncompactLift_mirror_odd y,
      B.commutator_eq_two_smul_lieProduct,
      B.anticommutator_eq_two_smul_jordanProduct,
      B.compact_even_feeds_jordan_holds,
      B.noncompact_odd_feeds_lie_holds⟩

end TomitaCliffordJordanLieBridge

/-! ## Owner target -/

universe uα uOp

/--
Owner target for a concrete Tomita-Cartan parity to Clifford Jordan/Lie bridge.

The target is not mere inhabitation of a socket.  A supplied bridge must read
out the Tomita parity laws, the Clifford/TKK Jordan-Lie product laws, and the
two calibration certificates.
-/
def TomitaCliffordJordanLieBridgeOwnerTarget
    (α : Type uα) (Op : Type uOp) (H : Type) [Ring Op]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] : Prop :=
  ∀ (B : TomitaCliffordJordanLieBridge.{uα, uOp, 0} (α := α) (Op := Op) (H := H))
    (x y : Op),
    B.mirror.mirror (B.mirror.compactLift x) = B.mirror.compactLift x
      ∧ B.mirror.mirror (B.mirror.noncompactLift y) = -B.mirror.noncompactLift y
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator (E := H)
          B.packet.closure.gibbs.conformalGeometricTemperature
          B.packet.closure.weylTemperature =
            (2 : ℝ) • B.packet.closure.lieProductTemperatureWeyl
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator (E := H)
          B.packet.closure.gibbs.conformalGeometricTemperature
          B.packet.closure.weylTemperature =
            (2 : ℝ) • B.packet.closure.jordanProductTemperatureWeyl
      ∧ B.compactEvenFeedsJordan
      ∧ B.noncompactOddFeedsLie

@[rep_depth transport]
theorem tomitaCliffordJordanLieBridgeOwnerTarget
    (α : Type uα) (Op : Type uOp) (H : Type) [Ring Op]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    TomitaCliffordJordanLieBridgeOwnerTarget α Op H := by
  intro B x y
  exact B.tomita_clifford_jordan_lie_packet x y

end InfoGeometry.Canonical.TomitaCliffordJordanLieBridge
