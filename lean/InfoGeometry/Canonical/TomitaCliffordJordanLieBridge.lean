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
must supply the two calibration proof fields saying that their mirror-even
sector feeds the symmetric/Jordan observable readout and their mirror-odd
sector feeds the antisymmetric/Lie generator readout.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.TomitaCliffordJordanLieBridge

open InfoGeometry.OperatorAlgebra.TomitaCartanSplit
open InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge
open InfoGeometry.Canonical.SouriauConformalKKT

variable {α : Type _}
variable {Op : Type _} [Ring Op]
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ## Bridge data -/

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
structure Bridge where
  /-- Tomita-style mirror involution on the algebraic operator lane. -/
  mirror : MirrorInvolution Op

  gibbs : @ConformalGibbsSouriauOperatorContext α H _ _ _
  weylGauge : WeylGaugeField (InfoGeometry.Krein.DoubledSpace H →L[ℝ] InfoGeometry.Krein.DoubledSpace H) (InfoGeometry.Krein.DoubledSpace H →L[ℝ] InfoGeometry.Krein.DoubledSpace H)

  /-- A selected compact generator in the mirror-even sector. -/
  compactEvenGenerator : Op

  /-- The selected compact generator is fixed by the Tomita mirror. -/
  compactEvenGenerator_mirror_even :
    mirror.mirror (mirror.compactLift compactEvenGenerator) =
      mirror.compactLift compactEvenGenerator

  /-- A selected noncompact generator in the mirror-odd sector. -/
  noncompactOddGenerator : Op

  /-- The selected noncompact generator is odd under the Tomita mirror. -/
  noncompactOddGenerator_mirror_odd :
    mirror.mirror (mirror.noncompactLift noncompactOddGenerator) =
      -mirror.noncompactLift noncompactOddGenerator

  /-- The concrete Jordan readout law on the imported TKK owner carrier. -/
  compactEvenFeedsJordan :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator (E := H)
      gibbs.conformalGeometricTemperature
      (InfoGeometry.Canonical.SouriauConformalKKT.weylTemperature gibbs weylGauge) =
        (2 : ℝ) • InfoGeometry.Canonical.SouriauConformalKKT.jordanProductTemperatureWeyl gibbs weylGauge

  /-- The concrete Lie readout law on the imported TKK owner carrier. -/
  noncompactOddFeedsLie :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator (E := H)
      gibbs.conformalGeometricTemperature
      (InfoGeometry.Canonical.SouriauConformalKKT.weylTemperature gibbs weylGauge) =
        (2 : ℝ) • InfoGeometry.Canonical.SouriauConformalKKT.lieProductTemperatureWeyl gibbs weylGauge

namespace Bridge

variable (B : _root_.InfoGeometry.Canonical.TomitaCliffordJordanLieBridge.Bridge (α := α) (Op := Op) (H := H))

/-! ## Tomita-Cartan parity re-exports -/

/-- Compact Tomita-Cartan lifts are mirror-even. -/
@[rep_depth transport]
theorem compactLift_mirror_even
    (x : Op) :
    B.mirror.mirror (B.mirror.compactLift x) = B.mirror.compactLift x :=
  B.mirror.mirror_compactLift x

/-! The selected generators expose the calibration's parity data directly. -/

@[rep_depth transport]
theorem selectedCompactEvenGenerator_mirror_even :
    B.mirror.mirror (B.mirror.compactLift B.compactEvenGenerator) =
      B.mirror.compactLift B.compactEvenGenerator :=
  B.compactEvenGenerator_mirror_even

@[rep_depth transport]
theorem selectedNoncompactOddGenerator_mirror_odd :
    B.mirror.mirror (B.mirror.noncompactLift B.noncompactOddGenerator) =
      -B.mirror.noncompactLift B.noncompactOddGenerator :=
  B.noncompactOddGenerator_mirror_odd

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
      B.gibbs.conformalGeometricTemperature
      (InfoGeometry.Canonical.SouriauConformalKKT.weylTemperature B.gibbs B.weylGauge) =
        (2 : ℝ) • InfoGeometry.Canonical.SouriauConformalKKT.lieProductTemperatureWeyl B.gibbs B.weylGauge :=
  B.noncompactOddFeedsLie

/-- The anticommutator channel is twice the symmetric Jordan product. -/
@[rep_depth transport]
theorem anticommutator_eq_two_smul_jordanProduct :
    InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator (E := H)
      B.gibbs.conformalGeometricTemperature
      (InfoGeometry.Canonical.SouriauConformalKKT.weylTemperature B.gibbs B.weylGauge) =
        (2 : ℝ) • InfoGeometry.Canonical.SouriauConformalKKT.jordanProductTemperatureWeyl B.gibbs B.weylGauge :=
  B.compactEvenFeedsJordan

end Bridge

/-! ## Owner target -/

universe uα uOp

/--
Owner target for a concrete Tomita-Cartan parity to Clifford Jordan/Lie bridge.

The target is not mere inhabitation of a socket.  A supplied bridge must read
out the Tomita parity laws, the Clifford/TKK Jordan-Lie product laws, and the
two calibration proof fields.
-/
def TomitaCliffordJordanLieBridgeOwnerTarget
    (α : Type uα) (Op : Type uOp) (H : Type) [Ring Op]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] : Prop :=
  ∀ (B : _root_.InfoGeometry.Canonical.TomitaCliffordJordanLieBridge.Bridge (α := α) (Op := Op) (H := H))
    (x y : Op),
    B.mirror.mirror (B.mirror.compactLift x) = B.mirror.compactLift x
      ∧ B.mirror.mirror (B.mirror.noncompactLift y) = -B.mirror.noncompactLift y
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator (E := H)
          B.gibbs.conformalGeometricTemperature
          (InfoGeometry.Canonical.SouriauConformalKKT.weylTemperature B.gibbs B.weylGauge) =
            (2 : ℝ) • InfoGeometry.Canonical.SouriauConformalKKT.lieProductTemperatureWeyl B.gibbs B.weylGauge
      ∧ InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator (E := H)
          B.gibbs.conformalGeometricTemperature
          (InfoGeometry.Canonical.SouriauConformalKKT.weylTemperature B.gibbs B.weylGauge) =
            (2 : ℝ) • InfoGeometry.Canonical.SouriauConformalKKT.jordanProductTemperatureWeyl B.gibbs B.weylGauge
      ∧ B.mirror.mirror (B.mirror.compactLift B.compactEvenGenerator) =
          B.mirror.compactLift B.compactEvenGenerator
      ∧ B.mirror.mirror (B.mirror.noncompactLift B.noncompactOddGenerator) =
          -B.mirror.noncompactLift B.noncompactOddGenerator

@[rep_depth transport]
theorem tomitaCliffordJordanLieBridgeOwnerTarget
    (α : Type uα) (Op : Type uOp) (H : Type) [Ring Op]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    TomitaCliffordJordanLieBridgeOwnerTarget α Op H := by
  intro B x y
  exact
    ⟨B.compactLift_mirror_even x,
      B.noncompactLift_mirror_odd y,
      B.commutator_eq_two_smul_lieProduct,
      B.anticommutator_eq_two_smul_jordanProduct,
      B.compactEvenGenerator_mirror_even,
      B.noncompactOddGenerator_mirror_odd⟩

end InfoGeometry.Canonical.TomitaCliffordJordanLieBridge
