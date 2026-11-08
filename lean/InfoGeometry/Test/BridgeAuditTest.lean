import Lean
import InfoGeometry.Algebra.ArchetypeInstances

open Lean Meta Elab Command
open InfoGeometry.MetaCompiler
open InfoGeometry.Bridge
open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open InfoGeometry.Canonical.GaugedZornDiracKahler
open InfoGeometry.Canonical.IwasawaKANTriad
open InfoGeometry.Canonical.ZornAssociatorDerivationCurvature

-- 1. Verify static extraction works seamlessly for downstream consumers
example {R : Type*} [CommRing R] (S p eps : Vec3 R) :
    let T := dot3 S (cross3 p eps)
    zornAssociator (ZornMatrix.quark S) (ZornMatrix.quark p) (ZornMatrix.quark eps) =
    ZornMatrix.sub (ZornMatrix.smul T ZornMatrix.PMinus) (ZornMatrix.smul T ZornMatrix.PPlus) := by
  discharge_archetype zornAssociatorDefectProved (S, p, eps)

example {R : Type*} [CommRing R] (x : R) : N_grp R x * P_minus R = P_minus R + x • e_plus R := by
  have_archetype kanTriadProved with x as hReconstruct
  exact hReconstruct

-- 2. Verify heartbeat protection triggers when tactics loop or blow budget
def expensiveLoopCandidate : TypedArchetype Nat .candidate where
  name     := `expensiveLoopCandidate
  phase    := 0
  claim    := fun n => n = n
  evidence := trivial

#register_archetype expensiveLoopCandidate

-- The following command will fail cleanly with a heartbeat exhaustion error
-- rather than freezing the elaboration server:
/-
#promote_archetype expensiveLoopCandidate as loopFails by
  with_heartbeat_limit 1  -- 1,000 heartbeats (insufficient for elaboration)
    intro n
    rfl
-/
