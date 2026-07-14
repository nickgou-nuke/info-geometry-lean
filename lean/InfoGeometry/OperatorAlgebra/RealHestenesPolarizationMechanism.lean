import InfoGeometry.Krein.PolarizedSector
import InfoGeometry.Krein.SplitCliffordNN
import InfoGeometry.Quantum.RealMajorana
import InfoGeometry.Canonical.BogoliubovPolarizationBridge

/-!
# Real Hestenes Polarization Mechanism

This file exposes the real-only splitting/polarization mechanism as one theorem
surface.

It does not introduce complex scalar structure.
It does not identify finite diagonal data as primitive.
It records that splitting is produced by real involutions/projectors on the
doubled Krein carrier, and that Bogoliubov transforms transport these
polarizations by real conjugation.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace RealHestenesPolarizationMechanism

open InfoGeometry.Krein
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Quantum.RealMajorana
open InfoGeometry.Canonical.BogoliubovPolarizationBridge

section DoubledKrein

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H2" => DoubledSpace E
local notation "Pplus" => spectralPlusProj (E := E)
local notation "Pminus" => spectralMinusProj (E := E)

/--
The doubled real Krein carrier splits into the `+` and `-` spectral sheets of
`epsilon`.

This is the basic real polarization decomposition.
-/
@[rep_depth krein]
theorem doubledKrein_spectral_decomposition
    (u : H2) :
    Pplus u + Pminus u = u :=
  InfoGeometry.Krein.PolarizedSector.frameDiagonal_sheet_decomposition
    (E := E) u

/-- The plus spectral projector is idempotent. -/
@[rep_depth krein]
theorem doubledKrein_plus_idempotent
    (u : H2) :
    Pplus (Pplus u) = Pplus u :=
  InfoGeometry.Krein.PolarizedSector.frameDiagonal_plus_idempotent
    (E := E) u

/-- The minus spectral projector is idempotent. -/
@[rep_depth krein]
theorem doubledKrein_minus_idempotent
    (u : H2) :
    Pminus (Pminus u) = Pminus u :=
  InfoGeometry.Krein.PolarizedSector.frameDiagonal_minus_idempotent
    (E := E) u

/-- The plus spectral readout lands in the plus sheet. -/
@[rep_depth krein]
theorem doubledKrein_plus_mem
    (u : H2) :
    Pplus u ∈ InfoGeometry.Krein.SplitQuadraticSheets.plusSheet (E := E) :=
  InfoGeometry.Krein.PolarizedSector.frameDiagonal_plus_mem
    (E := E) u

/-- The minus spectral readout lands in the minus sheet. -/
@[rep_depth krein]
theorem doubledKrein_minus_mem
    (u : H2) :
    Pminus u ∈ InfoGeometry.Krein.SplitQuadraticSheets.minusSheet (E := E) :=
  InfoGeometry.Krein.PolarizedSector.frameDiagonal_minus_mem
    (E := E) u

end DoubledKrein

section RealMajoranaPolarization

variable {S : Type}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]

/--
The Hestenes internal axis of a real Majorana datum squares to `-1`.

This is the real replacement for complex scalar multiplication by `i`.
-/
@[rep_depth operator]
theorem hestenesAxis_square_minus_one
    (M : RealMajoranaDatum (S := S)) :
    M.K.comp M.K = -(ContinuousLinearMap.id ℝ S) :=
  M.K_sq

/--
A `K`-compatible polarization sends the plus sector to the minus sector under
the real Hestenes axis `K = J epsilon`.
-/
@[rep_depth operator]
theorem KPolarization_K_maps_plus_to_minus
    {M : RealMajoranaDatum (S := S)}
    (P : KPolarization (S := S) M)
    (x : S)
    (hx : x ∈ P.plus) :
    M.K x ∈ P.minus :=
  P.K_maps_plus_to_minus x hx

/--
A `K`-compatible polarization sends the minus sector to the plus sector under
the real Hestenes axis `K = J epsilon`.
-/
@[rep_depth operator]
theorem KPolarization_K_maps_minus_to_plus
    {M : RealMajoranaDatum (S := S)}
    (P : KPolarization (S := S) M)
    (x : S)
    (hx : x ∈ P.minus) :
    M.K x ∈ P.plus :=
  P.K_maps_minus_to_plus x hx

/--
The canonical chirality polarization has `P = J`.
-/
@[simp, rep_depth operator]
theorem chiralityPolarization_is_J
    (M : RealMajoranaDatum (S := S)) :
    (M.chiralityPolarization).P = M.J :=
  rfl

/--
The canonical chirality polarization plus sector is the real Weyl-plus sector.
-/
@[simp, rep_depth operator]
theorem chiralityPolarization_plus_is_weylPlus
    (M : RealMajoranaDatum (S := S)) :
    (M.chiralityPolarization).plus = M.weylPlus :=
  rfl

/--
The canonical chirality polarization minus sector is the real Weyl-minus sector.
-/
@[simp, rep_depth operator]
theorem chiralityPolarization_minus_is_weylMinus
    (M : RealMajoranaDatum (S := S)) :
    (M.chiralityPolarization).minus = M.weylMinus :=
  rfl

end RealMajoranaPolarization

section BogoliubovTransport

variable {S : Type}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
variable {M : RealMajoranaDatum (S := S)}

/--
Real Bogoliubov transport preserves the square-minus-one law of the Hestenes
axis.
-/
@[rep_depth transport]
theorem bogoliubov_transportK_square_minus_one
    (T : RealBogoliubovTransform (S := S) M) :
    T.transportK.comp T.transportK = -(ContinuousLinearMap.id ℝ S) :=
  T.transportK_sq

/--
Transported `K` is the transported `J` followed by the transported `epsilon`.
-/
@[rep_depth transport]
theorem bogoliubov_transportK_def
    (T : RealBogoliubovTransform (S := S) M) :
    T.transportK = T.transportJ.comp T.transportEps :=
  T.transportK_def

/--
A real Bogoliubov transform preserves a polarization exactly when the
transported polarization involution is unchanged.
-/
@[rep_depth transport]
theorem bogoliubov_preservesPolarization_iff_transportP_eq
    (T : RealBogoliubovTransform (S := S) M)
    (P : KPolarization (S := S) M) :
    T.preservesPolarization P ↔ T.transportP P = P.P :=
  T.preservesPolarization_iff_transportP_eq P

/--
A real Bogoliubov transform either preserves a polarization or mixes it.

This is the explicit fork that prevents hidden diagonal assumptions.
-/
@[rep_depth transport]
theorem bogoliubov_preserves_or_mixes
    (T : RealBogoliubovTransform (S := S) M)
    (P : KPolarization (S := S) M) :
    T.preservesPolarization P ∨ T.mixesPolarization P :=
  T.preserves_or_mixes P

/--
If a real Bogoliubov transform preserves the polarization, it maps plus to plus.
-/
@[rep_depth transport]
theorem bogoliubov_maps_plus_of_preserves
    (T : RealBogoliubovTransform (S := S) M)
    (P : KPolarization (S := S) M)
    (hpres : T.preservesPolarization P)
    (x : S)
    (hx : x ∈ P.plus) :
    T.B x ∈ P.plus :=
  T.map_plus_of_preserves P hpres x hx

/--
If a real Bogoliubov transform preserves the polarization, it maps minus to
minus.
-/
@[rep_depth transport]
theorem bogoliubov_maps_minus_of_preserves
    (T : RealBogoliubovTransform (S := S) M)
    (P : KPolarization (S := S) M)
    (hpres : T.preservesPolarization P)
    (x : S)
    (hx : x ∈ P.minus) :
    T.B x ∈ P.minus :=
  T.map_minus_of_preserves P hpres x hx

end BogoliubovTransport

section MechanismPacket

/--
Transparent real splitting/polarization mechanism.

This is only a witness packet tying together the already formalized mechanisms.
It does not make diagonal operators primitive.

The diagonal/Cartan lane is a later KAN shadow of a real Bogoliubov transform.
-/
structure RealHestenesPolarizationMechanismPacket where
  /-- Real doubled carrier data. -/
  DoubledKreinCarrier : Type

  /-- Fundamental sign / spectral involution data. -/
  SpectralEpsilonData : Type

  /-- Plus/minus spectral projector data. -/
  SpectralProjectorData : Type

  /-- Real Majorana/Hestenes datum `(J, epsilon, K = J epsilon)`. -/
  RealMajoranaData : Type

  /-- `K`-compatible polarization datum. -/
  KCompatiblePolarizationData : Type

  /-- Real Bogoliubov transport datum. -/
  RealBogoliubovTransportData : Type

  /-- Witness that `P+ + P- = 1`. -/
  spectralDecompositionWitness : Type

  /-- Witness that `P+^2 = P+` and `P-^2 = P-`. -/
  projectorIdempotenceWitness : Type

  /-- Witness that `K^2 = -1`. -/
  hestenesAxisSquareWitness : Type

  /-- Witness that `K` swaps plus/minus sectors. -/
  KSwapsPolarizationWitness : Type

  /-- Witness that Bogoliubov transport conjugates/transports polarizations. -/
  bogoliubovTransportsPolarizationWitness : Type

  /--
  Guard: diagonal/Cartan data are not primitive; they are only later KAN
  shadows after choosing the real polarized Bogoliubov representation.
  -/
  diagonalOnlyKANShadowWitness : Type

  /-- Guard: no complex scalar owner lane is used. -/
  realOnlyNoComplexScalarWitness : Type

/-- Owner target for the transparent real Hestenes polarization mechanism. -/
abbrev RealHestenesPolarizationMechanismTarget : Type 1 :=
  RealHestenesPolarizationMechanismPacket

/-- Construct the mechanism target from explicit packet data. -/
def constructRealHestenesPolarizationMechanismTarget
    (P : RealHestenesPolarizationMechanismPacket) :
    RealHestenesPolarizationMechanismTarget :=
  P

namespace RealHestenesPolarizationMechanismPacket

/-- Expose the guard that diagonal data are only KAN shadows. -/
def diagonalShadowGuard
    (P : RealHestenesPolarizationMechanismPacket) : Type :=
  P.diagonalOnlyKANShadowWitness

@[simp] theorem diagonalShadowGuard_eq
    (P : RealHestenesPolarizationMechanismPacket) :
    P.diagonalShadowGuard = P.diagonalOnlyKANShadowWitness :=
  rfl

/-- Expose the guard that the owner lane is real-only. -/
def realOnlyGuard
    (P : RealHestenesPolarizationMechanismPacket) : Type :=
  P.realOnlyNoComplexScalarWitness

@[simp] theorem realOnlyGuard_eq
    (P : RealHestenesPolarizationMechanismPacket) :
    P.realOnlyGuard = P.realOnlyNoComplexScalarWitness :=
  rfl

/-- Constructing the packet preserves the two explicit guard lanes. -/
theorem constructRealHestenesPolarizationMechanismTarget_guards
    (P : RealHestenesPolarizationMechanismPacket) :
    (constructRealHestenesPolarizationMechanismTarget P).diagonalShadowGuard =
        P.diagonalOnlyKANShadowWitness ∧
      (constructRealHestenesPolarizationMechanismTarget P).realOnlyGuard =
        P.realOnlyNoComplexScalarWitness := by
  exact ⟨rfl, rfl⟩

end RealHestenesPolarizationMechanismPacket

end MechanismPacket

end RealHestenesPolarizationMechanism
