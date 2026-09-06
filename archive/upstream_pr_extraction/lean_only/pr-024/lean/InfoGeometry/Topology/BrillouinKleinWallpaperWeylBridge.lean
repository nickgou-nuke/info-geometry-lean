import Mathlib
import InfoGeometry.Topology.WallpaperSymmetry
import InfoGeometry.Topology.BrillouinKleinGaugeInvariant
import InfoGeometry.Topology.BrillouinKleinExceptionalTopology
import InfoGeometry.Topology.BrillouinKleinBerryConnectionFinite
import InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge
import InfoGeometry.Canonical.WallpaperPin55RootCrossSection

/-!
# Brillouin Klein wallpaper/Weyl bridge

This module packages the finite, theorem-safe bridge between:

* the `pg` glide relation on the Klein-bottle wallpaper chart;
* the `Z₂` Brillouin invariant and even boundary-charge readout;
* the exact coordinate-level `D₅` lift used by the wallpaper-to-Weyl packet.

It does **not** construct a global Brillouin-zone manifold classification, a
full `Q₈` or `Pin(5,5)` quotient, or a momentum-space band theorem.
-/

noncomputable section

namespace InfoGeometry.Topology.BrillouinKleinWallpaperWeylBridge

open InfoGeometry.Topology.Wallpaper
open InfoGeometry.Topology.BrillouinKleinGauge
open InfoGeometry.Topology.BrillouinKlein
open InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge
open InfoGeometry.Canonical.WallpaperPin55RootCrossSection

/--
Finite Brillouin/Klein bridge packet.

The fields are exactly the owner-file facts already present in the repo:

* the `pg` glide relation;
* the `Z₂` orientation-reversal cancellation;
* the even boundary charge readout on the Klein boundary;
* the gauge-stable `Z₂` readout under adding two crossings;
* the exact affine `D₅` coordinate bridge.
-/
structure BrillouinKleinWallpaperWeylPacket where
  glide : ∀ p : Lattice2D,
    concretePG.G (concretePG.T_y p) = concretePG.T_y.symm (concretePG.G p)
  z2Cancel : ∀ theta : ℤ,
    klein_bottle_z2_invariant theta (-theta) = 0
  boundaryChargeEven :
    ∀ {Path : Type} [AddCommGroup Path] (a b : Path) (int_charge : Path →+ ℤ),
      int_charge (klein_bottle_boundary Path a b) = 2 * int_charge a
  gaugeStable : ∀ theta n : ℤ,
    klein_bottle_z2_invariant (theta + 2 * n) (-theta) =
      klein_bottle_z2_invariant theta (-theta)
  affineWeyl : ∀ (t : Z2),
    (latticeEmbed t 0 + latticeEmbed t 1 + latticeEmbed t 2 +
        latticeEmbed t 3 + latticeEmbed t 4 = 0) ∧
      matVec5 sigmaXMatrix (latticeEmbed t) = latticeEmbed (sigmaX t) ∧
      matVec5 sigmaDMatrix (latticeEmbed t) = latticeEmbed (sigmaD t)

/-- Construct the finite Brillouin/Klein bridge packet from the owner theorems. -/
def brillouin_klein_wallpaper_weyl_packet : BrillouinKleinWallpaperWeylPacket where
  glide := concrete_pg_generates_klein_bottle_relation
  z2Cancel := fun theta => by
    simp [klein_bottle_z2_invariant]
  boundaryChargeEven := fun a b int_charge => fermion_doubling_violation a b int_charge
  gaugeStable := fun theta n => klein_bottle_invariant_gauge_stable theta (-theta) n
  affineWeyl := wallpaper_to_affine_weyl_d5_packet

end InfoGeometry.Topology.BrillouinKleinWallpaperWeylBridge
