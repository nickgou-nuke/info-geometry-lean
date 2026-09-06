import Mathlib
import InfoGeometry.Physics.NuclearKleinParameterBundle
import InfoGeometry.Canonical.Pin55WallpaperQuotientBridge
import InfoGeometry.Canonical.KleinBottleBoundaryActionPacket

/-!
# Nuclear Klein topology ↔ Pin/wallpaper/boundary structural bridge

The repository already contains two independent finite Klein corridors:

* a `Pin(5,5)` reflection projected through a Weyl/wallpaper glide satisfying
  the Klein presentation relation;
* a two-sheet boundary action whose glide reflection is involutive.

This file places the nuclear Klein-equivariant Hamiltonian beside those owners.
It does not identify their parity operators, prove a global Pin structure on
the nuclear parameter space, or assert a common physical holonomy.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearKleinPinWallpaperBridge

open InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient
open InfoGeometry.Physics.NuclearOperatorSuperSoloviev
open InfoGeometry.Physics.NuclearOperatorSchurComplement
open InfoGeometry.Physics.NuclearKleinParameterBundle
open InfoGeometry.Canonical.Pin55WeylWallpaper
open InfoGeometry.Canonical.WallpaperKleinBottleCartan
open InfoGeometry.Topology.Wallpaper
open InfoGeometry.Topology.WallpaperKleinBottlePresentation
open InfoGeometry.Canonical.Pin55WallpaperQuotientBridge
open InfoGeometry.Canonical.KleinBottleBoundaryActionPacket

variable {A : Type*} [Ring A]
variable {P : InternalParity A}

/-- The nuclear glide-invariant effective observable and the existing
Pin/wallpaper glide theorem coexist as exact finite Klein-compatible data. -/
theorem nuclear_pin_wallpaper_glide_packet
    (H : KleinEquivariantHamiltonian P) (R : ResolventData A)
    (p : TorusCell) (v : Torus5D) :
    H.effectiveAt R (glide p) = H.effectiveAt R p ∧
      project_2d (affine_shift (weyl_reflect v alpha_12)) =
        (v 1 + 1, v 0 + 1) := by
  exact ⟨H.effectiveAt_glide R p,
    Pin55D5WallpaperQuotientPacket.wallpaper_glide v⟩

/-- The nuclear glide law can be displayed together with the already-proved
wallpaper Klein presentation relation.  This is a structural packet only. -/
theorem nuclear_wallpaper_klein_relation_packet
    (H : KleinEquivariantHamiltonian P) (R : ResolventData A)
    (p : TorusCell) (q : Lattice2D) :
    H.effectiveAt R (glide p) = H.effectiveAt R p ∧
      concretePG.G (concretePG.T_y (concretePG.G.symm q)) =
        concretePG.T_y.symm q := by
  exact ⟨H.effectiveAt_glide R p,
    Pin55D5WallpaperQuotientPacket.klein_bottle_presentation q⟩

/-- Both the nuclear total parity and the existing finite Klein boundary glide
are involutive actions, stated without identifying their carriers. -/
theorem nuclear_boundary_involution_packet
    (H : KleinEquivariantHamiltonian P) (p : TorusCell)
    (M : Matrix (Fin 2) (Fin 2) ℤ) :
    totalParity P * (totalParity P * H.blockAt p * totalParity P) *
        totalParity P = H.blockAt p ∧
      glideReflection (glideReflection M) = M := by
  exact ⟨totalParity_action_twice P (H.blockAt p),
    glideReflection_involutive M⟩

end InfoGeometry.Physics.NuclearKleinPinWallpaperBridge

end noncomputable section
