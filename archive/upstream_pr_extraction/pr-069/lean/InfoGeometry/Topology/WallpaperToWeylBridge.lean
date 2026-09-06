import InfoGeometry.Topology.WallpaperSymmetry
import InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal

/-!
# Wallpaper `pg` to non-orientable Weyl charge bridge

This module connects the finite `pg` wallpaper glide relation to the
non-orientable Weyl semimetal mod-two charge corridor.

It does not prove a full quotient-manifold classification, a cellular
calculation of `K^2 × S^1`, or the analytic topology of a physical material.
It proves the exact finite bridge used downstream: the `pg` glide supplies the
orientation-reversing relation, and Weyl charges are invariant under that
orientation reversal after reduction to `ZMod 2`.

#### BUCKET 1: CLOSED FINITE THEOREMS

`pg_relation_and_mod_two_charge_invariance` and
`concrete_pg_relation_and_mod_two_charge_invariance`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

`pg_exactness_gives_nonorientable_weyl_cancellation` depends on the explicit
premise `ExactAtLocalCharges β`.

#### BUCKET 3: OPEN CLOSURE DEBT

The quotient-space proof that the `pg` presentation yields a Klein bottle, the
twisted Mayer--Vietoris sequence, and the full semimetal invariant
classification remain open outside this finite bridge.
-/

noncomputable section

namespace InfoGeometry.Topology.WallpaperToWeylBridge

open InfoGeometry.Topology.Wallpaper
open InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal

/--
The finite bridge from the `pg` wallpaper relation to the Weyl mod-two readout.

The first component is the geometric glide relation
`G * T_y = T_y^{-1} * G`.  The second component is the charge-theoretic
consequence needed for non-orientable Weyl semimetals: reversing local
orientations does not change the `ZMod 2` total charge.
-/
theorem pg_relation_and_mod_two_charge_invariance
    (pg : WallpaperGroupPG) (p : Lattice2D)
    {ι : Type} [Fintype ι] (charge : ι → ℤ) :
    pg.G (pg.T_y p) = pg.T_y.symm (pg.G p) ∧
      totalChargeModTwo (fun i => -charge i) = totalChargeModTwo charge := by
  exact ⟨pg_generates_klein_bottle_relation pg p,
    totalChargeModTwo_orientation_reversal_invariant charge⟩

/-- Concrete Euclidean `pg` instance of the wallpaper-to-Weyl bridge. -/
theorem concrete_pg_relation_and_mod_two_charge_invariance
    (p : Lattice2D) {ι : Type} [Fintype ι] (charge : ι → ℤ) :
    concretePG.G (concretePG.T_y p) = concretePG.T_y.symm (concretePG.G p) ∧
      totalChargeModTwo (fun i => -charge i) = totalChargeModTwo charge := by
  exact pg_relation_and_mod_two_charge_invariance concretePG p charge

/--
Conditional bridge from the wallpaper relation and exactness of the local
charge sequence to non-orientable Weyl charge cancellation.

The wallpaper component certifies the orientation-reversing glide relation.
The exactness premise is the finite substitute for the paper's twisted
Mayer--Vietoris exactness at the local charge group.
-/
theorem pg_exactness_gives_nonorientable_weyl_cancellation
    (pg : WallpaperGroupPG) (p : Lattice2D)
    {Semimetal ι : Type} [Fintype ι]
    (β : Semimetal → ι → ℤ)
    (hExact : ∀ s, ModTwoChargeNeutral (β s))
    (s : Semimetal) :
    pg.G (pg.T_y p) = pg.T_y.symm (pg.G p) ∧
      ModTwoChargeNeutral (β s) := by
  exact ⟨pg_generates_klein_bottle_relation pg p,
    exactness_gives_mod_two_charge_cancellation β hExact s⟩

end InfoGeometry.Topology.WallpaperToWeylBridge

end noncomputable section
