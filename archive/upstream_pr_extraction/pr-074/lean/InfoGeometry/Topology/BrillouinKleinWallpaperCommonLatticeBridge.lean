import Mathlib.Tactic
import InfoGeometry.Topology.WallpaperSymmetry
import InfoGeometry.Canonical.AffineWeylD5WallpaperQuotient

/-!
# Common lattice carrier for the wallpaper and `D₅` shadow actions

This owner connects the same integral `D₄` action in two faithful coordinate
readouts:

* the realification `ℤ² → Lattice2D = ℝ × ℝ`;
* the existing `latticeEmbed : ℤ² → ℚ⁵` and its `weylD5CrossSection2` action.

The affine `pg` glide is deliberately not identified with this linear action:
its half-translation is not an element of the integral lattice carrier.
Likewise, `sigmaDMatrix` is used through its proved lattice action and is not
claimed to be the literal representative `weylD5CrossSection 5`.
-/

noncomputable section

namespace InfoGeometry.Topology.BrillouinKleinWallpaperCommonLatticeBridge

open InfoGeometry.Topology.Wallpaper
open InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge
open InfoGeometry.Canonical.AffineWeylD5WallpaperQuotient
open InfoGeometry.Canonical.WallpaperPin55RootCrossSection

abbrev IntegralLattice := Z2

def realifyLattice (t : IntegralLattice) : Lattice2D :=
  (t.1, t.2)

def realD4Action (g : Fin 8) (p : Lattice2D) : Lattice2D :=
  match g with
  | 0 => (p.1, p.2)
  | 1 => (-p.2, p.1)
  | 2 => (-p.1, -p.2)
  | 3 => (p.2, -p.1)
  | 4 => (p.1, -p.2)
  | 5 => (p.2, p.1)
  | 6 => (-p.1, p.2)
  | 7 => (-p.2, -p.1)

theorem realifyLattice_injective : Function.Injective realifyLattice := by
  intro a b h
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  simp [realifyLattice] at h
  exact Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem realify_d4_action (g : Fin 8) (t : IntegralLattice) :
    realifyLattice (d4_action_on_Z2 g t) =
      realD4Action g (realifyLattice t) := by
  rcases t with ⟨u, v⟩
  fin_cases g <;>
    ext <;>
    simp [realifyLattice, realD4Action, d4_action_on_Z2]

theorem realify_sigmaX (t : IntegralLattice) :
    realifyLattice (sigmaX t) =
      realD4Action 6 (realifyLattice t) := by
  rcases t with ⟨u, v⟩
  ext <;> simp [realifyLattice, realD4Action, sigmaX]

theorem realify_sigmaD (t : IntegralLattice) :
    realifyLattice (sigmaD t) =
      realD4Action 5 (realifyLattice t) := by
  rcases t with ⟨u, v⟩
  ext <;> simp [realifyLattice, realD4Action, sigmaD]

theorem common_lattice_sigma_coherence (t : IntegralLattice) :
    (realifyLattice (sigmaX t) =
        realD4Action 6 (realifyLattice t)) ∧
      (matVec5 sigmaXMatrix (latticeEmbed t) =
        latticeEmbed (sigmaX t)) ∧
      (realifyLattice (sigmaD t) =
        realD4Action 5 (realifyLattice t)) ∧
      (matVec5 sigmaDMatrix (latticeEmbed t) =
        latticeEmbed (sigmaD t)) := by
  refine ⟨realify_sigmaX t, latticeEmbed_sigmaX t,
    realify_sigmaD t, latticeEmbed_sigmaD t⟩

theorem common_lattice_d4_coherence (g : Fin 8) (t : IntegralLattice) :
    realifyLattice (d4_action_on_Z2 g t) =
        realD4Action g (realifyLattice t) ∧
      matVec5 (weylD5CrossSection2 g) (latticeEmbed t) =
        latticeEmbed (d4_action_on_Z2 g t) := by
  exact ⟨realify_d4_action g t,
    weylD5CrossSection2_latticeEmbed_commutation g t⟩

theorem common_lattice_d4_coherence_packet (t : IntegralLattice) :
    (realifyLattice (d4_action_on_Z2 4 t) =
        realD4Action 4 (realifyLattice t)) ∧
      (matVec5 (weylD5CrossSection2 4) (latticeEmbed t) =
        latticeEmbed (d4_action_on_Z2 4 t)) ∧
      (realifyLattice (d4_action_on_Z2 6 t) =
        realD4Action 6 (realifyLattice t)) ∧
      (matVec5 (weylD5CrossSection2 6) (latticeEmbed t) =
        latticeEmbed (d4_action_on_Z2 6 t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact realify_d4_action 4 t
  · exact weylD5CrossSection2_latticeEmbed_commutation 4 t
  · exact realify_d4_action 6 t
  · exact weylD5CrossSection2_latticeEmbed_commutation 6 t

end InfoGeometry.Topology.BrillouinKleinWallpaperCommonLatticeBridge
