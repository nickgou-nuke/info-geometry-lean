/-
InfoGeometry/OperatorAlgebra/StinespringTomitaLightcone.lean

Stinespring-Tomita dilation over the chiral lightcone.

This module formalizes the statement:

  local loss/absorption in the observable algebra is a compressed view of a
  global dilation, and the lost component is explicitly routed into the
  Tomita commutant.

If the lost component also has a carrier readout on the chiral lightcone, then
local absorption is certified as reflection into the commutant chiral
lightcone.

This file does not claim that every CP map automatically routes into the
commutant. That routing is a proof-carrying Tomita/Stinespring witness.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.TomitaCartanSplit
import InfoGeometry.OperatorAlgebra.OperatorChiralLightcone
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.StinespringTomitaLightcone

open InfoGeometry.OperatorAlgebra.TomitaCartanSplit
open InfoGeometry.OperatorAlgebra.OperatorChiralLightcone

/-! ## 1. Local channels -/

/--
A local observable channel.

This is the algebraic carrier for a unital local observable map. Concrete
operator-algebraic positivity should be supplied by a separate owner theorem.
-/
structure LocalChannel
    (Op : Type*) [Ring Op] [Module ℝ Op] where
  /-- The local observable map. -/
  map : Op →ₗ[ℝ] Op

  /-- Unitality, when the channel is meant to preserve the unit. -/
  map_one : map 1 = 1

namespace LocalChannel

variable {Op : Type*} [Ring Op] [Module ℝ Op]
variable (Φ : LocalChannel Op)

/--
An observable is locally lost/absorbed by the channel when its local output is
zero.
-/
def IsLocallyLost
    (x : Op) : Prop :=
  Φ.map x = 0

end LocalChannel

/-! ## 2. Stinespring-Tomita dilation with commutant accounting -/

/--
A Stinespring-Tomita dilation of a local channel.

`GlobalOp` is the dilated/global algebra.

`embed` inserts the local observable into the global algebra.

`compress` is the local observer's compression/restriction back to `Op`.

`globalEvolution` is the dilated evolution.

`leakage x` is the part not seen by the local observer. The key Tomita
certificate is that this leakage lies in the commutant side.
-/
structure StinespringTomitaDilation
    (Op GlobalOp : Type*)
    [Ring Op] [Module ℝ Op]
    [Ring GlobalOp] [Module ℝ GlobalOp]
    (Φ : LocalChannel Op) where

  /-- Tomita algebra/commutant pair on the global algebra. -/
  tomita : TomitaAlgebraPair GlobalOp

  /-- Embedding of local observables into the global algebra. -/
  embed : Op →ₗ[ℝ] GlobalOp

  /-- Local observer compression/restriction. -/
  compress : GlobalOp →ₗ[ℝ] Op

  /-- Global/dilated evolution. -/
  globalEvolution : GlobalOp →ₗ[ℝ] GlobalOp

  /--
  Stinespring-type factorization:

  locally, the channel is the compression of the global evolution.
  -/
  channel_factorization :
    ∀ x : Op,
      Φ.map x = compress (globalEvolution (embed x))

  /-- Embedded local observables lie in the observable algebra side. -/
  embed_mem_observable :
    ∀ x : Op, embed x ∈ tomita.M

  /-- The part not visible in the local channel. -/
  leakage : Op → GlobalOp

  /-- Leakage is routed into the Tomita commutant. -/
  leakage_mem_commutant :
    ∀ x : Op, leakage x ∈ tomita.Mcomm

  /--
  Global accounting law:

  global evolution = visible embedded channel output + commutant leakage.
  -/
  accounting :
    ∀ x : Op,
      globalEvolution (embed x) =
        embed (Φ.map x) + leakage x

namespace StinespringTomitaDilation

variable
    {Op GlobalOp : Type*}
    [Ring Op] [Module ℝ Op]
    [Ring GlobalOp] [Module ℝ GlobalOp]
    {Φ : LocalChannel Op}

variable (D : StinespringTomitaDilation Op GlobalOp Φ)

/--
The local channel is the compressed global evolution.
-/
theorem channel_eq_compressed_global
    (x : Op) :
    Φ.map x = D.compress (D.globalEvolution (D.embed x)) :=
  D.channel_factorization x

/--
If an observable is locally lost, then the global evolved observable is exactly
the commutant leakage term.
-/
theorem locally_lost_global_eq_leakage
    {x : Op}
    (hx : Φ.IsLocallyLost x) :
    D.globalEvolution (D.embed x) = D.leakage x := by
  dsimp [LocalChannel.IsLocallyLost] at hx
  have h := D.accounting x
  rw [hx] at h
  simpa using h

/--
If an observable is locally lost, then its global evolved representative lies
in the Tomita commutant.

This is the formal version of:

  local absorption = reflection/routing into the dark commutant sector.
-/
theorem locally_lost_global_in_commutant
    {x : Op}
    (hx : Φ.IsLocallyLost x) :
    D.globalEvolution (D.embed x) ∈ D.tomita.Mcomm := by
  rw [D.locally_lost_global_eq_leakage hx]
  exact D.leakage_mem_commutant x

/--
A locally lost observable was originally inserted into the observable side.
-/
theorem embedded_local_observable_mem_M
    (x : Op) :
    D.embed x ∈ D.tomita.M :=
  D.embed_mem_observable x

end StinespringTomitaDilation

/-! ## 3. Chiral-lightcone refinement -/

/--
A Stinespring-Tomita dilation whose leakage is read on a chiral lightcone.

This is the bridge between:

* local channel loss;
* Tomita commutant routing;
* chiral/null carrier geometry.
-/
structure StinespringTomitaChiralLightconeDilation
    (Op GlobalOp H : Type*)
    [Ring Op] [Module ℝ Op]
    [Ring GlobalOp] [Module ℝ GlobalOp]
    [AddCommGroup H] [Module ℝ H]
    (Q : InfoGeometry.OperatorAlgebra.KreinIsotropicCone.KreinQuadraticDatum H)
    (C : ModuleCircularPolarization H)
    (Φ : LocalChannel Op) where

  /-- Underlying Stinespring-Tomita dilation. -/
  dilation : StinespringTomitaDilation Op GlobalOp Φ

  /-- Carrier readout of global operators. -/
  carrierReadout : GlobalOp → H

  /--
  Locally lost observables have leakage whose carrier readout lies on a
  chiral lightcone.
  -/
  leakage_hits_chiral_lightcone :
    ∀ x : Op,
      Φ.IsLocallyLost x →
        ∃ side : ChiralSide,
          carrierReadout (dilation.leakage x) ∈ ChiralLightcone Q C side

namespace StinespringTomitaChiralLightconeDilation

variable
    {Op GlobalOp H : Type*}
    [Ring Op] [Module ℝ Op]
    [Ring GlobalOp] [Module ℝ GlobalOp]
    [AddCommGroup H] [Module ℝ H]
    {Q : InfoGeometry.OperatorAlgebra.KreinIsotropicCone.KreinQuadraticDatum H}
    {C : ModuleCircularPolarization H}
    {Φ : LocalChannel Op}

variable (D : StinespringTomitaChiralLightconeDilation Op GlobalOp H Q C Φ)

/--
Local loss routes the global evolved observable into the Tomita commutant.
-/
theorem locally_lost_global_in_commutant
    {x : Op}
    (hx : Φ.IsLocallyLost x) :
    D.dilation.globalEvolution (D.dilation.embed x) ∈
      D.dilation.tomita.Mcomm :=
  D.dilation.locally_lost_global_in_commutant hx

/--
Local loss has a chiral-lightlike carrier readout.
-/
theorem locally_lost_has_chiral_lightcone_readout
    {x : Op}
    (hx : Φ.IsLocallyLost x) :
    ∃ side : ChiralSide,
      D.carrierReadout (D.dilation.leakage x) ∈
        ChiralLightcone Q C side :=
  D.leakage_hits_chiral_lightcone x hx

/--
If an observable is locally lost, then the global evolved observable is both
commutant-routed and chiral-lightlike after carrier readout.
-/
theorem locally_lost_is_commutant_chiral_lightcone
    {x : Op}
    (hx : Φ.IsLocallyLost x) :
    D.dilation.globalEvolution (D.dilation.embed x) ∈
        D.dilation.tomita.Mcomm ∧
      ∃ side : ChiralSide,
        D.carrierReadout (D.dilation.leakage x) ∈
          ChiralLightcone Q C side := by
  exact
    ⟨D.locally_lost_global_in_commutant hx,
     D.locally_lost_has_chiral_lightcone_readout hx⟩

end StinespringTomitaChiralLightconeDilation

/-! ## 4. CPT/Tomita lightcone mirror compatibility -/

/--
Compatibility between a Tomita commutant route and a chiral-lightcone mirror.

This packages the statement that the commutant route is also the CPT branch
which swaps the left and right chiral lightcones.
-/
structure TomitaLightconeMirrorCompatibility
    (GlobalOp H : Type*)
    [Ring GlobalOp] [Module ℝ GlobalOp]
    [AddCommGroup H] [Module ℝ H]
    (Q : InfoGeometry.OperatorAlgebra.KreinIsotropicCone.KreinQuadraticDatum H)
    (C : ModuleCircularPolarization H)
    (T : TomitaAlgebraPair GlobalOp) where

  /-- Carrier readout of global operators. -/
  carrierReadout : GlobalOp → H

  /-- Carrier-level chiral lightcone mirror. -/
  mirror : ChiralLightconeMirror H Q C

  /--
  Tomita commutant routing is compatible with carrier mirror readout.
  -/
  tomita_readout_compatibility :
    ∀ x : GlobalOp,
      carrierReadout (T.Jconj x) = mirror.J (carrierReadout x)

namespace TomitaLightconeMirrorCompatibility

variable
    {GlobalOp H : Type*}
    [Ring GlobalOp] [Module ℝ GlobalOp]
    [AddCommGroup H] [Module ℝ H]
    {Q : InfoGeometry.OperatorAlgebra.KreinIsotropicCone.KreinQuadraticDatum H}
    {C : ModuleCircularPolarization H}
    {T : TomitaAlgebraPair GlobalOp}

variable (M : TomitaLightconeMirrorCompatibility GlobalOp H Q C T)

/--
If a global operator has left-lightcone readout, then its Tomita mirror has
right-lightcone readout.
-/
theorem tomita_maps_left_readout_to_right
    {x : GlobalOp}
    (hx : M.carrierReadout x ∈ LeftChiralLightcone Q C) :
    M.carrierReadout (T.Jconj x) ∈ RightChiralLightcone Q C := by
  rw [M.tomita_readout_compatibility x]
  exact M.mirror.maps_left_lightcone_to_right hx

/--
If a global operator has right-lightcone readout, then its Tomita mirror has
left-lightcone readout.
-/
theorem tomita_maps_right_readout_to_left
    {x : GlobalOp}
    (hx : M.carrierReadout x ∈ RightChiralLightcone Q C) :
    M.carrierReadout (T.Jconj x) ∈ LeftChiralLightcone Q C := by
  rw [M.tomita_readout_compatibility x]
  exact M.mirror.maps_right_lightcone_to_left hx

end TomitaLightconeMirrorCompatibility

/-! ## 5. Owner targets -/

/--
Compatibility data for constructing the Stinespring-Tomita dilation.

Concrete implementations require complete positivity, a representation,
compression map, and Tomita-compatible global routing.
-/
structure StinespringTomitaDilationCompatibility
    (Op GlobalOp : Type*)
    [Ring Op] [Module ℝ Op]
    [Ring GlobalOp] [Module ℝ GlobalOp]
    (Φ : LocalChannel Op) where
  witness :
    StinespringTomitaDilation Op GlobalOp Φ

/--
Owner target for the Stinespring-Tomita dilation theorem.
-/
@[owner_target_tag]
def StinespringTomitaDilationOwnerTarget : Prop :=
  ∀ (Op GlobalOp : Type*)
    [Ring Op] [Module ℝ Op]
    [Ring GlobalOp] [Module ℝ GlobalOp],
  ∀ Φ : LocalChannel Op,
    StinespringTomitaDilationCompatibility Op GlobalOp Φ →
      Nonempty (StinespringTomitaDilation Op GlobalOp Φ)

/--
The owner target follows once the compatibility witness is supplied.
-/
theorem stinespringTomitaDilationOwnerTarget :
    StinespringTomitaDilationOwnerTarget := by
  intro Op GlobalOp _ _ _ _ Φ h
  exact ⟨h.witness⟩

/--
Compatibility data for constructing the chiral-lightcone refinement.
-/
structure StinespringTomitaChiralLightconeCompatibility
    (Op GlobalOp H : Type*)
    [Ring Op] [Module ℝ Op]
    [Ring GlobalOp] [Module ℝ GlobalOp]
    [AddCommGroup H] [Module ℝ H]
    (Q : InfoGeometry.OperatorAlgebra.KreinIsotropicCone.KreinQuadraticDatum H)
    (C : ModuleCircularPolarization H)
    (Φ : LocalChannel Op) where
  witness :
    StinespringTomitaChiralLightconeDilation Op GlobalOp H Q C Φ

/--
Owner target for the chiral-lightcone Stinespring-Tomita theorem.
-/
@[owner_target_tag]
def StinespringTomitaChiralLightconeOwnerTarget : Prop :=
  ∀ (Op GlobalOp H : Type*)
    [Ring Op] [Module ℝ Op]
    [Ring GlobalOp] [Module ℝ GlobalOp]
    [AddCommGroup H] [Module ℝ H],
  ∀ (Q : InfoGeometry.OperatorAlgebra.KreinIsotropicCone.KreinQuadraticDatum H),
  ∀ (C : ModuleCircularPolarization H),
  ∀ Φ : LocalChannel Op,
    StinespringTomitaChiralLightconeCompatibility Op GlobalOp H Q C Φ →
      Nonempty
        (StinespringTomitaChiralLightconeDilation Op GlobalOp H Q C Φ)

/--
The chiral-lightcone owner target follows once the compatibility witness is
supplied.
-/
theorem stinespringTomitaChiralLightconeOwnerTarget :
    StinespringTomitaChiralLightconeOwnerTarget := by
  intro Op GlobalOp H _ _ _ _ _ _ Q C Φ h
  exact ⟨h.witness⟩

end InfoGeometry.OperatorAlgebra.StinespringTomitaLightcone
