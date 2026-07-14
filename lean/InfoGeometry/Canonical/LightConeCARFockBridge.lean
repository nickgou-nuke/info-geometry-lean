/-
InfoGeometry/Canonical/LightConeCARFockBridge.lean

Dictionary between Drazin light-cone arrows and genuine CAR/Fock ladders.

This file does not prove that every Drazin/Peirce light-cone pair is a CAR
pair.  It separates:

* nilpotent off-diagonal projector channels from `DrazinLightConeDictionary`;
* genuine creation/annihilation operators satisfying `IsCARPair`;
* explicit representation equations identifying a chosen light-cone pair with
  a chosen CAR/Fock pair.
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
  uPlus_sq_zero :
    split.uPlus Xplus * split.uPlus Xplus = 0
  uMinus_sq_zero :
    split.uMinus Xminus * split.uMinus Xminus = 0

namespace LightConeNilpotentPair

variable {A : Type*} [Ring A]
variable (L : LightConeNilpotentPair A)

/-- Any projector split supplies nilpotent light-cone channels for chosen seeds. -/
@[rep_depth operator]
def ofProjectorSplit
    (split : ProjectorSplit A)
    (Xplus Xminus : A) :
    LightConeNilpotentPair A where
  split := split
  Xplus := Xplus
  Xminus := Xminus
  uPlus_sq_zero := split.uPlus_mul_uPlus_eq_zero Xplus Xplus
  uMinus_sq_zero := split.uMinus_mul_uMinus_eq_zero Xminus Xminus

end LightConeNilpotentPair

/--
A proof-carrying CAR/Fock realization of a light-cone pair.

The realization laws are equations, not comments: the represented light-cone
channels must equal the supplied annihilation and creation operators.  Without
these fields, no CAR conclusion is exported from a Drazin projector split.
-/
@[rep_depth operator]
structure Bridge
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

  /-- The chosen light-cone `u⁺` channel is represented by annihilation. -/
  uPlus_realization_eq :
    realize (lightcone.split.uPlus lightcone.Xplus) = annihilation

  /-- The chosen light-cone `u⁻` channel is represented by creation. -/
  uMinus_realization_eq :
    realize (lightcone.split.uMinus lightcone.Xminus) = creation

/-! ## Concrete split-`Cl(1,1)` CAR/Fock readback -/

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Concrete split-`Cl(1,1)` CAR/Fock readback.

This is intentionally not a `Bridge`: it supplies the genuine
CAR pair, but it does not assert an arbitrary Drazin projector split realizes
that pair.  A full bridge is obtained only when the two realization equations
in `Bridge` are supplied.
-/
@[rep_depth operator]
structure ConcreteCl11CARFockReadback where
  annihilation : FockEndomorphism E
  creation : FockEndomorphism E
  car : IsCARPair (E := E) annihilation creation

/-- The repo-owned concrete split-`Cl(1,1)` CAR pair as a Fock readback. -/
@[rep_depth operator]
noncomputable def concreteCl11CARFockReadback :
    ConcreteCl11CARFockReadback (E := E) where
  annihilation := concreteCARAnnihilation (E := E)
  creation := concreteCARCreation (E := E)
  car := concrete_car_pair (E := E)

/--
The doubled projector-super pair is still only a projector-super pair here;
this bridge does not promote it to a standard CAR pair.
-/
@[rep_depth operator]
theorem annihilation_creation_is_projector_super_pair :
    IsProjectorSuperPair (E := E)
      (InfoGeometry.Quantum.annihilationOp (E := E))
      (InfoGeometry.Quantum.creationOp (E := E)) :=
  InfoGeometry.Canonical.SuperSouriauFermionGasBridge.projector_super_pair_is_not_claimed_as_CAR
    (E := E)

end InfoGeometry.Canonical.LightConeCARFockBridge
