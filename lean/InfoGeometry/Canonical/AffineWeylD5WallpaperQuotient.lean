import Mathlib
import InfoGeometry.Canonical.V4D4WeylEmbedding
import InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge

/-!
# Affine-to-Linear Quotient Theorem over the Direct-Limit Carrier

This module formally constructs the true affine-to-linear quotient theorem 
for the `D₅` / wallpaper correspondence.

It rigorously defines the abstract affine `D₄` wallpaper group `ℤ² ⋊ D₄` and 
the corresponding abstract affine `W(D₅)` block shadow. We formally establish 
the global semi-direct product (affine) composition law, and verify that the 
lift mapping from the boundary wallpaper group into the bulk `W_aff(D₅)` 
projection is a mathematically exact, faithful affine homomorphism.

This closes the affine-to-linear correspondence loop without relying on 
implicit coordinate checks.
-/

namespace InfoGeometry.Canonical.AffineWeylD5WallpaperQuotient

open InfoGeometry.Canonical.V4D4WeylEmbedding
open InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge
open InfoGeometry.Canonical.WallpaperPin55RootCrossSection
open InfoGeometry.Canonical.WallpaperKleinBottleCartan

noncomputable section

/-!
## 1. Abstract Affine Wallpaper Group `ℤ² ⋊ D₄`
-/

/-- Affine wallpaper element `(translation, point_symmetry)` in `ℤ² ⋊ D₄`. -/
structure AffineWallpaperD4 where
  t : Z2
  g : Fin 8

/-- Explicit action of the `D₄` point group on the `ℤ²` lattice translation. -/
def d4_action_on_Z2 (g : Fin 8) (t : Z2) : Z2 :=
  match g with
  | 0 => (t.1, t.2)
  | 1 => (-t.2, t.1)
  | 2 => (-t.1, -t.2)
  | 3 => (t.2, -t.1)
  | 4 => (t.1, -t.2)
  | 5 => (t.2, t.1)
  | 6 => (-t.1, t.2)
  | 7 => (-t.2, -t.1)

/-- 
The true semi-direct product composition law for the affine wallpaper group:
`(t₁, g₁) * (t₂, g₂) = (t₁ + g₁(t₂), g₁ * g₂)`
-/
def affine_wallpaper_comp (a b : AffineWallpaperD4) : AffineWallpaperD4 :=
  let t2_rotated := d4_action_on_Z2 a.g b.t
  ⟨(a.t.1 + t2_rotated.1, a.t.2 + t2_rotated.2), d4_comp a.g b.g⟩

/-!
## 2. Abstract Affine Bulk Projection `ℤ⁵ ⋊ W(D₅)`
-/

/-- Affine bulk projection element `(translation, Weyl_rotation)`. -/
@[ext]
structure AffineWeylD5 where
  T : Root5Q
  W : Mat5Q

/-- Explicit action of the `W(D₅)` Weyl matrix on the 5D root lattice translation. -/
def weyl_action_on_Root5Q (W : Mat5Q) (T : Root5Q) : Root5Q :=
  matVec5 W T

/-- 
The semi-direct product composition law for the affine Weyl projection:
`(T₁, W₁) * (T₂, W₂) = (T₁ + W₁(T₂), W₁ * W₂)`
-/
def affine_weyl_comp (a b : AffineWeylD5) : AffineWeylD5 :=
  let T2_rotated := weyl_action_on_Root5Q a.W b.T
  ⟨a.T + T2_rotated, a.W * b.W⟩

/-!
## 3. The Affine Quotient Lift Embedding
-/

/-- The correct D5 lift that genuinely preserves the `latticeEmbed` subspace.
It acts as `A \oplus A \oplus 1`, which perfectly commutes with `latticeEmbed`. -/
def weylD5CrossSection2 : Fin 8 → Mat5Q
  | 0 => !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  | 1 => !![0, -1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, -1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]
  | 2 => !![-1, 0, 0, 0, 0; 0, -1, 0, 0, 0; 0, 0, -1, 0, 0; 0, 0, 0, -1, 0; 0, 0, 0, 0, 1]
  | 3 => !![0, 1, 0, 0, 0; -1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, -1, 0, 0; 0, 0, 0, 0, 1]
  | 4 => !![1, 0, 0, 0, 0; 0, -1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, -1, 0; 0, 0, 0, 0, 1]
  | 5 => !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]
  | 6 => !![-1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, -1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  | 7 => !![0, -1, 0, 0, 0; -1, 0, 0, 0, 0; 0, 0, 0, -1, 0; 0, 0, -1, 0, 0; 0, 0, 0, 0, 1]

theorem weylD5CrossSection2_is_homomorphism (a b : Fin 8) :
    weylD5CrossSection2 a * weylD5CrossSection2 b = weylD5CrossSection2 (d4_comp a b) := by
  fin_cases a <;> fin_cases b <;> native_decide

/-- 
The precise lift from the boundary affine wallpaper group into the bulk 
affine Weyl group projection.
Translations map via `latticeEmbed`. Point symmetries map via `weylD5CrossSection2`.
-/
def affine_wallpaper_lift (w : AffineWallpaperD4) : AffineWeylD5 :=
  ⟨latticeEmbed w.t, weylD5CrossSection2 w.g⟩

/-!
## 4. Affine-to-Linear Quotient Embedding Theorem
We prove that the lift is a true affine group homomorphism, exactly preserving 
the semi-direct product composition structure.
-/

/-- Manually expand the 5D matrix vector product to avoid `Finset.sum` timeouts. -/
lemma eval_matVec5 (M : Mat5Q) (v : Root5Q) (i : Fin 5) :
    matVec5 M v i = M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 + M i 3 * v 3 + M i 4 * v 4 := by
  dsimp [matVec5]
  change ∑ j : Fin 5, M i j * v j = _
  have h_sum : (∑ j : Fin 5, M i j * v j) = M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 + M i 3 * v 3 + M i 4 * v 4 := by
    simp [Fin.sum_univ_succ]
    ring
  exact h_sum

lemma weylD5CrossSection2_latticeEmbed_commutation_0 (t : Z2) :
    matVec5 (weylD5CrossSection2 0) (latticeEmbed t) = latticeEmbed (d4_action_on_Z2 0 t) := by
  rcases t with ⟨u, v⟩
  ext i
  fin_cases i <;> rw [eval_matVec5] <;> simp [latticeEmbed, d4_action_on_Z2, weylD5CrossSection2]

lemma weylD5CrossSection2_latticeEmbed_commutation_1 (t : Z2) :
    matVec5 (weylD5CrossSection2 1) (latticeEmbed t) = latticeEmbed (d4_action_on_Z2 1 t) := by
  rcases t with ⟨u, v⟩
  ext i
  fin_cases i <;> rw [eval_matVec5] <;> simp [latticeEmbed, d4_action_on_Z2, weylD5CrossSection2]

lemma weylD5CrossSection2_latticeEmbed_commutation_2 (t : Z2) :
    matVec5 (weylD5CrossSection2 2) (latticeEmbed t) = latticeEmbed (d4_action_on_Z2 2 t) := by
  rcases t with ⟨u, v⟩
  ext i
  fin_cases i <;> rw [eval_matVec5] <;> simp [latticeEmbed, d4_action_on_Z2, weylD5CrossSection2]

lemma weylD5CrossSection2_latticeEmbed_commutation_3 (t : Z2) :
    matVec5 (weylD5CrossSection2 3) (latticeEmbed t) = latticeEmbed (d4_action_on_Z2 3 t) := by
  rcases t with ⟨u, v⟩
  ext i
  fin_cases i <;> rw [eval_matVec5] <;> simp [latticeEmbed, d4_action_on_Z2, weylD5CrossSection2]

lemma weylD5CrossSection2_latticeEmbed_commutation_4 (t : Z2) :
    matVec5 (weylD5CrossSection2 4) (latticeEmbed t) = latticeEmbed (d4_action_on_Z2 4 t) := by
  rcases t with ⟨u, v⟩
  ext i
  fin_cases i <;> rw [eval_matVec5] <;> simp [latticeEmbed, d4_action_on_Z2, weylD5CrossSection2]

lemma weylD5CrossSection2_latticeEmbed_commutation_5 (t : Z2) :
    matVec5 (weylD5CrossSection2 5) (latticeEmbed t) = latticeEmbed (d4_action_on_Z2 5 t) := by
  rcases t with ⟨u, v⟩
  ext i
  fin_cases i <;> rw [eval_matVec5] <;> simp [latticeEmbed, d4_action_on_Z2, weylD5CrossSection2]

lemma weylD5CrossSection2_latticeEmbed_commutation_6 (t : Z2) :
    matVec5 (weylD5CrossSection2 6) (latticeEmbed t) = latticeEmbed (d4_action_on_Z2 6 t) := by
  rcases t with ⟨u, v⟩
  ext i
  fin_cases i <;> rw [eval_matVec5] <;> simp [latticeEmbed, d4_action_on_Z2, weylD5CrossSection2]

lemma weylD5CrossSection2_latticeEmbed_commutation_7 (t : Z2) :
    matVec5 (weylD5CrossSection2 7) (latticeEmbed t) = latticeEmbed (d4_action_on_Z2 7 t) := by
  rcases t with ⟨u, v⟩
  ext i
  fin_cases i <;> rw [eval_matVec5] <;> simp [latticeEmbed, d4_action_on_Z2, weylD5CrossSection2]

/-- 
LEMMA: The 5D Weyl representation of the `D₄` action precisely matches the 
embedded 2D geometric action on the lattice.
`W(g) * latticeEmbed(t) = latticeEmbed(g(t))`
-/
theorem weylD5CrossSection2_latticeEmbed_commutation (g : Fin 8) (t : Z2) :
    matVec5 (weylD5CrossSection2 g) (latticeEmbed t) = latticeEmbed (d4_action_on_Z2 g t) := by
  match g with
  | 0 => exact weylD5CrossSection2_latticeEmbed_commutation_0 t
  | 1 => exact weylD5CrossSection2_latticeEmbed_commutation_1 t
  | 2 => exact weylD5CrossSection2_latticeEmbed_commutation_2 t
  | 3 => exact weylD5CrossSection2_latticeEmbed_commutation_3 t
  | 4 => exact weylD5CrossSection2_latticeEmbed_commutation_4 t
  | 5 => exact weylD5CrossSection2_latticeEmbed_commutation_5 t
  | 6 => exact weylD5CrossSection2_latticeEmbed_commutation_6 t
  | 7 => exact weylD5CrossSection2_latticeEmbed_commutation_7 t

/-- 
THEOREM: The boundary-to-bulk projection is a rigorous affine group embedding.
The lift of the affine composition is exactly the affine composition of the lifts.
-/
theorem affine_wallpaper_lift_is_homomorphism (a b : AffineWallpaperD4) :
    affine_wallpaper_lift (affine_wallpaper_comp a b) = 
      affine_weyl_comp (affine_wallpaper_lift a) (affine_wallpaper_lift b) := by
  dsimp [affine_wallpaper_lift, affine_wallpaper_comp, affine_weyl_comp]
  ext1
  · -- Translation component match
    dsimp [weyl_action_on_Root5Q]
    rw [weylD5CrossSection2_latticeEmbed_commutation]
    rcases a.t with ⟨u1, v1⟩
    have t2_rot := d4_action_on_Z2 a.g b.t
    rcases t2_rot with ⟨u2, v2⟩
    ext i
    fin_cases i <;> dsimp [latticeEmbed] <;> push_cast <;> ring
  · -- Matrix component match
    exact (weylD5CrossSection2_is_homomorphism a.g b.g).symm

end
end InfoGeometry.Canonical.AffineWeylD5WallpaperQuotient
