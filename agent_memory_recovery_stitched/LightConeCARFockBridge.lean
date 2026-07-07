/-
InfoGeometry/Canonical/LightConeCARFockBridge.lean

Dictionary between Drazin light-cone arrows and genuine CAR/Fock ladders.

This file does not prove that every Drazin/Peirce light-cone pair is a CAR
pair.  It separates:

* nilpotent off-diagonal projector channels from `DrazinLightConeDictionary`;
* genuine creation/annihilation operators satisfying `IsCARPair`;
* separate CAR/Fock data.  Any representation theorem identifying a chosen
  light-cone pair with a chosen CAR/Fock pair must be proved explicitly outside
  the data carrier.
-/

import InfoGeometry.Canonical.DrazinLightConeDictionary
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.SuperSouriauFermionGasBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.LightConeCARFockBridge

open InfoGeometry.Canonical.DrazinLightConeDictionary
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge

/--
A Drazin/projector light-cone pair.

This records only the nilpotent Peirce-channel structure.  It is not a CAR
pair because it does not include the mixed normalization `{a,a†}=1`.
-/
@[rep_depth operator]
structure LightConeNilpotentPair
    (A : Type*) [Ring A] where
  split : ProjectorSplit A
  Xplus : A
  Xminus : A

namespace LightConeNilpotentPair

variable {A : Type*} [Ring A]
variable (L : LightConeNilpotentPair A)

/-- Read back the `u⁺` nilpotence law. -/
@[rep_depth operator]
theorem uPlus_sq_zero_holds :
    L.split.uPlus L.Xplus * L.split.uPlus L.Xplus = 0 :=
  L.split.uPlus_mul_uPlus_eq_zero L.Xplus L.Xplus

/-- Read back the `u⁻` nilpotence law. -/
@[rep_depth operator]
theorem uMinus_sq_zero_holds :
    L.split.uMinus L.Xminus * L.split.uMinus L.Xminus = 0 :=
  L.split.uMinus_mul_uMinus_eq_zero L.Xminus L.Xminus

/-- Any projector split supplies nilpotent light-cone channels for chosen seeds. -/
@[rep_depth operator]
def ofProjectorSplit
    (split : ProjectorSplit A)
    (Xplus Xminus : A) :
    LightConeNilpotentPair A where
  split := split
  Xplus := Xplus
  Xminus := Xminus

end LightConeNilpotentPair

/--
CAR/Fock data associated with a light-cone pair.

This structure stores the algebraic light-cone data, a representation map, and
a genuine CAR pair.  It does not assert that the represented light-cone channels
are the CAR operators; concrete models must prove those equations separately.
-/
@[rep_depth operator]
structure LightConeCARFockBridge
    (E : Type) (A : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Ring A] where

  /-- The algebraic Drazin/projector light-cone pair. -/
  lightcone : LightConeNilpotentPair A

  /-- Representation/readout from the light-cone algebra to Fock endomorphisms. -/
  realize : A → FockEndomorphism E

  /-- Genuine annihilation operator. -/
  annihilation : FockEndomorphism E

  /-- Genuine creation operator. -/
  creation : FockEndomorphism E

  /-- Genuine CAR law for the chosen Fock realization. -/
  car : IsCARPair (E := E) annihilation creation

namespace LightConeCARFockBridge
