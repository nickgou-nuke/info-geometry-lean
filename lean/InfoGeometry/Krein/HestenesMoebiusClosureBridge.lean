import InfoGeometry.Krein.HestenesConnesWilsonBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace BigOperators

noncomputable section

/-!
# InfoGeometry.Krein.HestenesMoebiusClosureBridge

Möbius closure socket for the Hestenes--Krein / Connes--Wilson lane.

This file deliberately does **not** construct a global conformal field theory,
a representation theorem for `SL(2,ℝ)`, or a compactification theorem for a
Cantor boundary.  Instead it provides a theorem-safe calibration interface:

* a determinant-one Möbius parameter record;
* a supplied projective action on the finite atom/face index set;
* a supplied bounded ring-automorphism action on operators;
* a supplied Krein-isometric vector action fixing the vacuum `Ω`;
* invariance readbacks for Ω-expectations and Connes--Wilson holonomies.

The mathematical doctrine is witness-gated: a concrete CFT/Jones/Cantor backend
supplies the Möbius representation laws, while this bridge records the exact
consequences needed by the real Hestenes--Krein volume pipeline.
-/

namespace HestenesMoebiusClosureBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.HestenesModularKMSBridge
open InfoGeometry.Krein.HestenesKreinVacuumBridge
open InfoGeometry.Krein.HestenesConnesWilsonBridge
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Canonical.StandardFormOmegaVolumeBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance moebiusClosureNormedRing : NormedRing EndH := inferInstance
noncomputable local instance moebiusClosureNormedAlgebra : NormedAlgebra ℝ EndH :=
  inferInstance
noncomputable local instance moebiusClosureNormedAlgebraRat : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance moebiusClosureTopologicalRing : IsTopologicalRing EndH := inferInstance
local instance moebiusClosureCompleteSpace : CompleteSpace EndH := inferInstance
local instance moebiusClosureSMulCommClass : SMulCommClass ℝ EndH EndH := inferInstance
local instance moebiusClosureIsScalarTower : IsScalarTower ℝ EndH EndH := inferInstance

/--
A determinant-one real Möbius parameter, read as an `SL(2,ℝ)` matrix
`[[a,b],[c,d]]` at this socket level.
-/
@[rep_depth projective]
structure MoebiusParameter where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  det_one : a * d - b * c = 1

namespace MoebiusParameter

/-- Readback of the determinant-one condition. -/
@[rep_depth projective]
theorem determinant_one (g : MoebiusParameter) :
    g.a * g.d - g.b * g.c = 1 :=
  g.det_one

end MoebiusParameter

/-- Hestenes--Krein null cone associated to the Wilson/KMS carrier. -/
@[rep_depth krein]
def HestenesNullCone (_P : HestenesKreinKMSPacket (E := H₂)) : Set H₂ :=
  { ξ : H₂ | KreinSpace.kreinInner (H := H₂) ξ ξ = 0 }

/--
Final Möbius closure bridge.

`Word` is a finite face/atom layer.  A concrete backend may instantiate it by
binary words at a fixed depth, Jones tower atoms, or another finite boundary
slice.  The Möbius action on that finite layer is supplied as a permutation.
-/
@[rep_depth krein]
structure Bridge
    (Word : Type*) [Fintype Word] [DecidableEq Word] where
  /-- Previously installed Hestenes--Connes--Wilson detailed-balance bridge. -/
  wilson :
    _root_.InfoGeometry.Krein.HestenesConnesWilsonBridge.Bridge (E := E) Word

  /-- Möbius action on vectors in the real doubled carrier. -/
  vectorAction : MoebiusParameter → H₂ → H₂

  /-- The vector action is Krein-isometric. -/
  vectorAction_krein_isometry :
    ∀ (g : MoebiusParameter) (ξ η : H₂),
      KreinSpace.kreinInner (H := H₂) (vectorAction g ξ) (vectorAction g η) =
        KreinSpace.kreinInner (H := H₂) ξ η

  /-- The vacuum apex `Ω` is fixed by the Möbius vector action. -/
  vectorAction_fixes_omega :
    ∀ g : MoebiusParameter,
      vectorAction g wilson.vacuum.omega = wilson.vacuum.omega

  /-- Möbius action on bounded doubled-space operators. -/
  operatorAction : MoebiusParameter → EndH ≃+* EndH

  /-- The Möbius operator action fixes the Hestenes phase axis `K`. -/
  operatorAction_phaseAxis_fixed :
    ∀ g : MoebiusParameter,
      operatorAction g (clockAxis (E := E)) = clockAxis (E := E)

  /-- The Ω-volume state is invariant under the Möbius operator action. -/
  volumeState_operatorAction_invariant :
    ∀ (g : MoebiusParameter) (A : EndH),
      wilson.volume.volumeState (operatorAction g A) = wilson.volume.volumeState A

  /-- Möbius permutation of the finite atom/face layer. -/
  wordAction : MoebiusParameter → Equiv.Perm Word

  /-- Atom weights are invariant under the Möbius face permutation. -/
  atomExpectation_wordAction_invariant :
    ∀ (g : MoebiusParameter) (w : Word),
      wilson.volume.atomExpectation ((wordAction g) w) =
        wilson.volume.atomExpectation w

  /-- Connes--Wilson holonomy is invariant under Möbius reparameterization. -/
  wilsonHolonomy_wordAction_invariant :
    ∀ (g : MoebiusParameter) (parent child : Word),
      wilson.wilsonHolonomy ((wordAction g) parent) ((wordAction g) child) =
        wilson.wilsonHolonomy parent child

namespace Bridge

variable {Word : Type*}
variable [Fintype Word] [DecidableEq Word]
variable (M : Bridge (E := E) Word)

/-- Vacuum vector fixedness under the supplied Möbius action. -/
@[rep_depth krein]
theorem moebius_vacuum_vector_fixed (g : MoebiusParameter) :
    M.vectorAction g M.wilson.vacuum.omega = M.wilson.vacuum.omega :=
  M.vectorAction_fixes_omega g

/-- Möbius transformations preserve the Hestenes natural cone shadow. -/
@[rep_depth krein]
theorem moebius_preserves_naturalCone
    (g : MoebiusParameter) {ξ : H₂}
    (hξ : ξ ∈ M.wilson.kmsPacket.HestenesNaturalCone) :
    M.vectorAction g ξ ∈ M.wilson.kmsPacket.HestenesNaturalCone := by
  change 0 ≤ KreinSpace.kreinInner (H := H₂) ξ ξ at hξ
  change 0 ≤
    KreinSpace.kreinInner (H := H₂) (M.vectorAction g ξ) (M.vectorAction g ξ)
  rw [M.vectorAction_krein_isometry]
  exact hξ

/-- Möbius transformations preserve the Krein null cone. -/
@[rep_depth krein]
theorem moebius_preserves_nullCone
    (g : MoebiusParameter) {ξ : H₂}
    (hξ : ξ ∈ HestenesNullCone M.wilson.kmsPacket) :
    M.vectorAction g ξ ∈ HestenesNullCone M.wilson.kmsPacket := by
  change KreinSpace.kreinInner (H := H₂) ξ ξ = 0 at hξ
  change KreinSpace.kreinInner (H := H₂)
      (M.vectorAction g ξ) (M.vectorAction g ξ) = 0
  rw [M.vectorAction_krein_isometry]
  exact hξ

/-- The Möbius action keeps the vacuum normalized. -/
@[rep_depth krein]
theorem moebius_vacuum_norm_invariant (g : MoebiusParameter) :
    KreinSpace.kreinInner (H := H₂)
        (M.vectorAction g M.wilson.vacuum.omega)
        (M.vectorAction g M.wilson.vacuum.omega) = 1 := by
  rw [M.vectorAction_krein_isometry]
  exact M.wilson.vacuum.omega_normalized

/--
The Möbius closure invariant: pairing the transformed vacuum with `Ω` still
returns unit volume.
-/
@[rep_depth krein]
theorem moebius_vacuum_closure_invariant (g : MoebiusParameter) :
    KreinSpace.kreinInner (H := H₂)
        (M.vectorAction g M.wilson.vacuum.omega)
        M.wilson.vacuum.omega = 1 := by
  rw [M.vectorAction_fixes_omega]
  exact M.wilson.vacuum.omega_normalized

/-- The Möbius operator action fixes the Hestenes phase axis. -/
@[rep_depth krein]
theorem moebius_phaseAxis_fixed (g : MoebiusParameter) :
    M.operatorAction g (clockAxis (E := E)) = clockAxis (E := E) :=
  M.operatorAction_phaseAxis_fixed g

/-- The Möbius operator action preserves Hestenes analytic/K-linear operators. -/
@[rep_depth krein]
theorem moebius_preserves_hestenesAnalyticSymmetry
    (g : MoebiusParameter) {A : EndH}
    (hA : IsHestenesAnalyticSymmetry (E := E) A) :
    IsHestenesAnalyticSymmetry (E := E) (M.operatorAction g A) := by
  let K : EndH := clockAxis (E := E)
  unfold IsHestenesAnalyticSymmetry at hA ⊢
  unfold IsHestenesHolomorphicDifferential at hA ⊢
  change A * K = K * A at hA
  change (M.operatorAction g A) * K = K * (M.operatorAction g A)
  have hK : M.operatorAction g K = K := M.operatorAction_phaseAxis_fixed g
  calc
    (M.operatorAction g A) * K
        = (M.operatorAction g A) * (M.operatorAction g K) := by rw [hK]
    _ = M.operatorAction g (A * K) := by
          rw [(M.operatorAction g).map_mul]
    _ = M.operatorAction g (K * A) := by
          rw [hA]
    _ = (M.operatorAction g K) * (M.operatorAction g A) := by
          rw [(M.operatorAction g).map_mul]
    _ = K * (M.operatorAction g A) := by rw [hK]

/-- Ω-volume state invariance under Möbius operator action. -/
@[rep_depth krein]
theorem volumeState_moebius_invariant
    (g : MoebiusParameter) (A : EndH) :
    M.wilson.volume.volumeState (M.operatorAction g A) =
      M.wilson.volume.volumeState A :=
  M.volumeState_operatorAction_invariant g A

/-- Vacuum real state invariance under Möbius operator action. -/
@[rep_depth krein]
theorem vacuumRealState_moebius_invariant
    (g : MoebiusParameter) (A : EndH) :
    M.wilson.vacuum.vacuumRealState (M.operatorAction g A) =
      M.wilson.vacuum.vacuumRealState A := by
  calc
    M.wilson.vacuum.vacuumRealState (M.operatorAction g A)
        = M.wilson.volume.volumeState (M.operatorAction g A) := by
            exact (M.wilson.volumeState_eq_vacuumRealState (M.operatorAction g A)).symm
    _ = M.wilson.volume.volumeState A :=
            M.volumeState_moebius_invariant g A
    _ = M.wilson.vacuum.vacuumRealState A :=
            M.wilson.volumeState_eq_vacuumRealState A

/-- The Möbius transform of the operator unit still has unit vacuum expectation. -/
@[rep_depth krein]
theorem moebius_unit_vacuum_expectation (g : MoebiusParameter) :
    M.wilson.vacuum.vacuumRealState (M.operatorAction g (1 : EndH)) = 1 := by
  calc
    M.wilson.vacuum.vacuumRealState (M.operatorAction g (1 : EndH))
        = M.wilson.vacuum.vacuumRealState (1 : EndH) :=
            M.vacuumRealState_moebius_invariant g (1 : EndH)
    _ = 1 := by
          simpa using M.wilson.vacuum.vacuumRealState_id

/-- Möbius invariance of atom weights. -/
@[rep_depth projective]
theorem atomExpectation_moebius_invariant
    (g : MoebiusParameter) (w : Word) :
    M.wilson.volume.atomExpectation ((M.wordAction g) w) =
      M.wilson.volume.atomExpectation w :=
  M.atomExpectation_wordAction_invariant g w

/-- The finite total atom volume is invariant under Möbius reindexing. -/
@[rep_depth projective]
theorem total_atom_volume_moebius_invariant (g : MoebiusParameter) :
    (∑ w : Word,
      M.wilson.volume.atomExpectation ((M.wordAction g) w)) = 1 := by
  calc
    (∑ w : Word,
      M.wilson.volume.atomExpectation ((M.wordAction g) w))
        = ∑ w : Word, M.wilson.volume.atomExpectation w := by
            apply Finset.sum_congr rfl
            intro w _hw
            exact M.atomExpectation_moebius_invariant g w
    _ = 1 := M.wilson.volume.total_expectation_is_unity

/-- Connes--Wilson holonomy is blind to Möbius reparameterization of faces. -/
@[rep_depth projective]
theorem connes_wilson_loop_moebius_invariant
    (g : MoebiusParameter) (parent child : Word) :
    M.wilson.wilsonHolonomy ((M.wordAction g) parent) ((M.wordAction g) child) =
      M.wilson.wilsonHolonomy parent child :=
  M.wilsonHolonomy_wordAction_invariant g parent child

/-- Radon--Nikodym log increments are Möbius invariant. -/
@[rep_depth projective]
theorem radonNikodymLog_moebius_invariant
    (g : MoebiusParameter) (parent child : Word) :
    M.wilson.radonNikodymLog ((M.wordAction g) parent) ((M.wordAction g) child) =
      M.wilson.radonNikodymLog parent child := by
  calc
    M.wilson.radonNikodymLog ((M.wordAction g) parent) ((M.wordAction g) child)
        = M.wilson.wilsonHolonomy ((M.wordAction g) parent) ((M.wordAction g) child) :=
            (M.wilson.wilsonHolonomy_eq_radonNikodymLog
              ((M.wordAction g) parent) ((M.wordAction g) child)).symm
    _ = M.wilson.wilsonHolonomy parent child :=
            M.connes_wilson_loop_moebius_invariant g parent child
    _ = M.wilson.radonNikodymLog parent child :=
            M.wilson.wilsonHolonomy_eq_radonNikodymLog parent child

/-- The Ω-volume modular logarithmic increment is Möbius invariant. -/
@[rep_depth projective]
theorem modularVolumeIncrement_moebius_invariant
    (g : MoebiusParameter) (parent child : Word) :
    M.wilson.volume.modularVolumeIncrement
        ((M.wordAction g) parent) ((M.wordAction g) child) =
      M.wilson.volume.modularVolumeIncrement parent child := by
  calc
    M.wilson.volume.modularVolumeIncrement
        ((M.wordAction g) parent) ((M.wordAction g) child)
        = M.wilson.radonNikodymLog ((M.wordAction g) parent) ((M.wordAction g) child) :=
            (M.wilson.radonNikodymLog_eq_modularVolumeIncrement
              ((M.wordAction g) parent) ((M.wordAction g) child)).symm
    _ = M.wilson.radonNikodymLog parent child :=
            M.radonNikodymLog_moebius_invariant g parent child
    _ = M.wilson.volume.modularVolumeIncrement parent child :=
            M.wilson.radonNikodymLog_eq_modularVolumeIncrement parent child

/--
Alias for the final finite-level projective closure readback.

This is the theorem-safe "closure of the universe" statement at this socket:
Möbius reindexing of the finite atom layer preserves the normalized total
Ω-volume.  No compactification theorem or global CFT representation theorem is
claimed here.
-/
@[rep_depth projective]
theorem universe_projective_closure
    (g : MoebiusParameter) :
    (∑ w : Word,
      M.wilson.volume.atomExpectation ((M.wordAction g) w)) = 1 :=
  M.total_atom_volume_moebius_invariant g

/--
Alias for Möbius invariance of the Connes--Weyl logarithmic scale.

This is the finite Connes--Wilson/Weyl readback: Möbius reparameterization of
faces preserves the calibrated logarithmic Radon--Nikodym increment.
-/
@[rep_depth projective]
theorem connes_weyl_scale_moebius_closed
    (g : MoebiusParameter) (parent child : Word) :
    M.wilson.radonNikodymLog ((M.wordAction g) parent) ((M.wordAction g) child) =
      M.wilson.radonNikodymLog parent child :=
  M.radonNikodymLog_moebius_invariant g parent child

end Bridge

end Core

end HestenesMoebiusClosureBridge

end
