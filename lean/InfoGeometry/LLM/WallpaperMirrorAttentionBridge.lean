import InfoGeometry.Topology.WallpaperToWeylBridge
import InfoGeometry.LLM.MirrorPhaseCuntzAttention

/-!
# Wallpaper glide to Mirror Phase attention bridge

This module connects the finite `pg` wallpaper glide relation to the finite
Mirror Phase attention projector.

It proves only finite algebraic statements:

* the `pg` glide supplies an orientation-reversing relation;
* orientation reversal is invisible to the `ZMod 2` Weyl total-charge readout;
* exact dyadic Mirror Phase attention kills the real two-branch anomaly.

It does not prove any theorem about trained transformers, semantic reliability,
or physical materials.

#### BUCKET 1: CLOSED FINITE THEOREMS

`pg_glide_and_mirror_attention_kill_branch_anomaly` and
`pg_glide_charge_and_attention_anomaly_packet`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

Real transformer approximation bounds, quotient-space topology, and physical
band-structure semantics remain outside this finite bridge.
-/

noncomputable section

namespace WallpaperMirrorAttentionBridge

open InfoGeometry.Topology.Wallpaper
open InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal
open InfoGeometry.LLM.MirrorPhaseCuntzAttention

/--
The wallpaper glide relation and the Mirror Phase branch-anomaly annihilation
hold simultaneously in the finite bridge.
-/
theorem pg_glide_and_mirror_attention_kill_branch_anomaly
    (pg : WallpaperGroupPG) (p : Lattice2D) (v : TwoBranchVector) :
    pg.G (pg.T_y p) = pg.T_y.symm (pg.G p) ∧
      branchAnomaly (applyMirrorAttention v) = 0 := by
  exact ⟨pg_generates_klein_bottle_relation pg p,
    mirrorAttention_kills_branchAnomaly v⟩

/--
Full finite packet: the same `pg` orientation-reversing glide supports both
the mod-two Weyl charge invariance and the real Mirror Phase anomaly projection.
-/
theorem pg_glide_charge_and_attention_anomaly_packet
    (pg : WallpaperGroupPG) (p : Lattice2D)
    {ι : Type} [Fintype ι] (charge : ι → ℤ)
    (v : TwoBranchVector) :
    pg.G (pg.T_y p) = pg.T_y.symm (pg.G p) ∧
      totalChargeModTwo (fun i => -charge i) = totalChargeModTwo charge ∧
        branchAnomaly (applyMirrorAttention v) = 0 := by
  exact ⟨pg_generates_klein_bottle_relation pg p,
    totalChargeModTwo_orientation_reversal_invariant charge,
    mirrorAttention_kills_branchAnomaly v⟩

end WallpaperMirrorAttentionBridge

end noncomputable section
