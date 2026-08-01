import Mathlib.Tactic
import InfoGeometry.Canonical.WallpaperPin55RootCrossSection

/-!
# Wallpaper / affine `D₅` Weyl coordinate bridge

This file records the exact coordinate-level compatibility that is already
available in the repository:

* the square-lattice embedding `(u, v) ↦ (u, v, -u, -v, 0)` lands in the
  displayed `D₅` coordinate shadow;
* the `y`-axis reflection corresponds to the `D₅` shadow matrix
  `weylD5CrossSection 6`;
* the diagonal reflection corresponds to the `D₅` shadow matrix
  `weylD5CrossSection 5`.

It does **not** construct a full wallpaper group carrier `ℤ² ⋊ D₄` or a global
affine Weyl group `W_aff(D₅)`.  The full group-level carrier is not present in
the repository; this file keeps the theorem layer at the exact coordinate
compatibility that the owner files can prove.
-/

noncomputable section

namespace InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge

open InfoGeometry.Canonical.WallpaperPin55RootCrossSection

abbrev Z2 := ℤ × ℤ

/-- The 2D square-lattice embedding into the visible `D₅` coordinate shadow. -/
def latticeEmbed (t : Z2) : Root5Q :=
  ![(t.1 : ℚ), (t.2 : ℚ), -(t.1 : ℚ), -(t.2 : ℚ), 0]

/-- Reflection across the y-axis on the square lattice. -/
def sigmaX (t : Z2) : Z2 :=
  (-t.1, t.2)

/-- Reflection across the diagonal `y = x` on the square lattice. -/
def sigmaD (t : Z2) : Z2 :=
  (t.2, t.1)

/-- The 5D matrix realizing the y-axis reflection on the embedded lattice. -/
def sigmaXMatrix : Mat5Q :=
  !![-1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, -1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1]

/-- The 5D matrix realizing the diagonal reflection on the embedded lattice. -/
def sigmaDMatrix : Mat5Q :=
  !![0, 1, 0, 0, 0;
     1, 0, 0, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 0, 1]

/-- The embedded lattice point has zero coordinate sum, hence lies in the
displayed root-lattice slice. -/
theorem latticeEmbed_sum_zero (t : Z2) :
    latticeEmbed t 0 + latticeEmbed t 1 + latticeEmbed t 2 +
        latticeEmbed t 3 + latticeEmbed t 4 = 0 := by
  rcases t with ⟨u, v⟩
  simp [latticeEmbed]

/-- The `y`-axis reflection is realized by the `D₅` shadow matrix `6`. -/
theorem latticeEmbed_sigmaX (t : Z2) :
    matVec5 sigmaXMatrix (latticeEmbed t) = latticeEmbed (sigmaX t) := by
  rcases t with ⟨u, v⟩
  ext i
  fin_cases i <;> simp [matVec5, latticeEmbed, sigmaX, sigmaXMatrix]

/-- The diagonal reflection is realized by the `D₅` shadow matrix `5`. -/
theorem latticeEmbed_sigmaD (t : Z2) :
    matVec5 sigmaDMatrix (latticeEmbed t) = latticeEmbed (sigmaD t) := by
  rcases t with ⟨u, v⟩
  ext i
  fin_cases i <;> simp [matVec5, latticeEmbed, sigmaD, sigmaDMatrix]

/-- Exact coordinate packet for the two wallpaper generators inside the `D₅`
shadow. -/
theorem wallpaper_to_affine_weyl_d5_packet (t : Z2) :
    (latticeEmbed t 0 + latticeEmbed t 1 + latticeEmbed t 2 +
        latticeEmbed t 3 + latticeEmbed t 4 = 0) ∧
      matVec5 sigmaXMatrix (latticeEmbed t) = latticeEmbed (sigmaX t) ∧
      matVec5 sigmaDMatrix (latticeEmbed t) = latticeEmbed (sigmaD t) := by
  refine ⟨?_, ?_, ?_⟩
  · exact latticeEmbed_sum_zero t
  · exact latticeEmbed_sigmaX t
  · exact latticeEmbed_sigmaD t

end InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge
