/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Lean
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Meta.ArchetypeDischarge
import InfoGeometry.Canonical.ZornChiralAssociatorDemodulation
import InfoGeometry.Canonical.IwasawaKANTriad

open Lean Meta Elab Command Term Tactic
open InfoGeometry.MetaCompiler
open InfoGeometry.Canonical.ZornChiralAssociatorDemodulation
open InfoGeometry.Canonical.IwasawaKANTriad
open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open InfoGeometry.Canonical.GaugedZornDiracKahler
open InfoGeometry.Canonical.ZornAssociatorDerivationCurvature

namespace InfoGeometry.Bridge

/-!
# Production Epistemic Archetype Bridge

Connects verified mathematical theorems from the canonical modules:
- `ZornChiralAssociatorDemodulation`: 3D coordinate associator defect identity.
- `IwasawaKANTriad`: Iwasawa KAN factor reconstruction and projector orthogonality.

Provides a heartbeat-budgeted discharge wrapper to prevent non-terminating
metaprogramming loops during automated batch promotion.
-/

-- ============================================================================
-- 1. Heartbeat-Budgeted Discharge Infrastructure
-- ============================================================================

/--
Tactic syntax wrapper that sets a hard ceiling on evaluation heartbeats.
Usage in promotion blocks:
  `#promote_archetype cand as target by with_heartbeat_limit 20000 (tacticSeq)`
-/
syntax (name := withHeartbeatLimit) "with_heartbeat_limit " num tacticSeq : tactic

@[tactic withHeartbeatLimit]
def elabWithHeartbeatLimit : Tactic := fun stx => do
  match stx with
  | `(tactic| with_heartbeat_limit $hb:num $tac:tacticSeq) =>
    let maxHB := hb.getNat * 1000
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := maxHB }) do
      evalTactic tac
  | _ => throwUnsupportedSyntax

-- ============================================================================
-- 2. Zorn Chiral Associator Defect Archetype
-- ============================================================================

variable {R : Type*} [CommRing R]

def zornAssociatorDefectArchetype : TypedArchetype (Vec3 R × Vec3 R × Vec3 R) .proved where
  name     := `zornAssociatorDefectArchetype
  phase    := 1
  claim    := fun (S, p, eps) =>
    let T := dot3 S (cross3 p eps)
    zornAssociator (ZornMatrix.quark S) (ZornMatrix.quark p) (ZornMatrix.quark eps) =
    ZornMatrix.sub (ZornMatrix.smul T ZornMatrix.PMinus) (ZornMatrix.smul T ZornMatrix.PPlus)
  evidence := fun (S, p, eps) => zorn_associator_three_quarks_demodulation S p eps

#register_archetype zornAssociatorDefectArchetype

/- Compatibility name retained for clients of the earlier promotion API. -/
abbrev zornAssociatorDefectProved {R : Type*} [CommRing R] :=
  zornAssociatorDefectArchetype (R := R)

-- ============================================================================
-- 3. Iwasawa KAN Triad Reconstruction Archetype
-- ============================================================================

def kanTriadArchetype : TypedArchetype R .proved where
  name     := `kanTriadArchetype
  phase    := 2
  claim    := fun x => N_grp R x * P_minus R = P_minus R + x • e_plus R
  evidence := fun x => N_mediates_peirce_polarization R x

#register_archetype kanTriadArchetype

/- Compatibility name retained for clients of the earlier promotion API. -/
abbrev kanTriadProved {R : Type*} [CommRing R] := kanTriadArchetype (R := R)

-- ============================================================================
-- 4. Compile-Time QMS Registry Disposition
-- ============================================================================

#audit_archetype zornAssociatorDefectArchetype
#audit_archetype kanTriadArchetype

#search_typed_archetypes

end InfoGeometry.Bridge
