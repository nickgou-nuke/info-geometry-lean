import InfoGeometry.Canonical.CuntzStarInductiveSystem
import InfoGeometry.Canonical.CStarCuntzFamilyTopology

/-!
# Topological naturality of Cuntz generator actions

The Cuntz tower already proves that transitions preserve old generators.  This
owner upgrades that fact to commuting squares for left multiplication by a
generator and right multiplication by its adjoint.  These are the continuous
action maps needed for a topological descent of the finite Fock/Cuntz action.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzTowerGeneratorActionTopological

open CategoryTheory
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Physics.CStarCuntzTensorQuotient
open InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

def towerTransitionTopCatHom
    {m n : ℕ} (hmn : m ≤ n) :
    TopCat.of (Stage m) ⟶ TopCat.of (Stage n) :=
  TopCat.ofHom (T.map hmn)

def towerLeftGeneratorActionTopCatHom
    {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    TopCat.of (Stage m) ⟶ TopCat.of (Stage n) :=
  towerTransitionTopCatHom Stage T hmn ≫
    (T.family n).leftGeneratorActionTopCatHom (Fin.castLE hmn i)

def towerRightAdjointGeneratorActionTopCatHom
    {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    TopCat.of (Stage m) ⟶ TopCat.of (Stage n) :=
  (T.family m).rightAdjointGeneratorActionTopCatHom i ≫
    towerTransitionTopCatHom Stage T hmn

theorem tower_left_generator_action_natural
    {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    towerLeftGeneratorActionTopCatHom Stage T hmn i =
      (T.family m).leftGeneratorActionTopCatHom i ≫
        towerTransitionTopCatHom Stage T hmn := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  change (T.family n).S (Fin.castLE hmn i) * T.map hmn a =
    T.map hmn ((T.family m).S i * a)
  rw [map_mul, T.map_generator hmn i]

theorem tower_right_adjoint_generator_action_natural
    {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    towerRightAdjointGeneratorActionTopCatHom Stage T hmn i =
      towerTransitionTopCatHom Stage T hmn ≫
        (T.family n).rightAdjointGeneratorActionTopCatHom
          (Fin.castLE hmn i) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  change T.map hmn (a * star ((T.family m).S i)) =
    T.map hmn a * star ((T.family n).S (Fin.castLE hmn i))
  rw [map_mul,
    CuntzStarTower.map_generator_star (Stage := Stage) T hmn i]

@[simp] theorem towerTransitionTopCatHom_apply
    {m n : ℕ} (hmn : m ≤ n) (a : Stage m) :
    towerTransitionTopCatHom Stage T hmn a = T.map hmn a :=
  rfl

end InfoGeometry.Canonical.CuntzTowerGeneratorActionTopological
