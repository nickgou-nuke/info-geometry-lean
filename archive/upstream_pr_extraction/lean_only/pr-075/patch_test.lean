import InfoGeometry.Canonical.V4D4WeylEmbedding
import InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge

open InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge
open InfoGeometry.Canonical.WallpaperPin55RootCrossSection
open InfoGeometry.Canonical.WallpaperKleinBottleCartan



def d4_action_on_InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.Z2_local (g : Fin 8) (t : InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.Z2) : InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.Z2 :=
  match g with
  | 0 => (t.1, t.2)
  | 1 => (-t.2, t.1)
  | 2 => (-t.1, -t.2)
  | 3 => (t.2, -t.1)
  | 4 => (t.1, -t.2)
  | 5 => (t.2, t.1)
  | 6 => (-t.1, t.2)
  | 7 => (-t.2, -t.1)

def weylD5CrossSection2 : Fin 8 → Mat5Q
  | 0 => !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  | 1 => !![0, -1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, -1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]
  | 2 => !![-1, 0, 0, 0, 0; 0, -1, 0, 0, 0; 0, 0, -1, 0, 0; 0, 0, 0, -1, 0; 0, 0, 0, 0, 1]
  | 3 => !![0, 1, 0, 0, 0; -1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, -1, 0, 0; 0, 0, 0, 0, 1]
  | 4 => !![1, 0, 0, 0, 0; 0, -1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, -1, 0; 0, 0, 0, 0, 1]
  | 5 => !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]
  | 6 => !![-1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, -1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  | 7 => !![0, -1, 0, 0, 0; -1, 0, 0, 0, 0; 0, 0, 0, -1, 0; 0, 0, -1, 0, 0; 0, 0, 0, 0, 1]

lemma eval_matVec5 (M : Mat5Q) (v : Root5Q) (i : Fin 5) :
    matVec5 M v i = M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 + M i 3 * v 3 + M i 4 * v 4 := by
  dsimp [matVec5]
  change ∑ j : Fin 5, M i j * v j = _
  have h_sum : (∑ j : Fin 5, M i j * v j) = M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 + M i 3 * v 3 + M i 4 * v 4 := by
    simp [Fin.sum_univ_succ]
    ring
  exact h_sum

lemma test_4 (t : InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.Z2) :
    matVec5 (weylD5CrossSection2 4) (latticeEmbed t) = latticeEmbed (d4_action_on_InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.Z2_local 4 t) := by
  rcases t with ⟨u, v⟩
  ext i
  fin_cases i <;> rw [eval_matVec5] <;> simp [latticeEmbed, d4_action_on_InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.Z2_local, weylD5CrossSection2] <;> push_cast <;> ring
