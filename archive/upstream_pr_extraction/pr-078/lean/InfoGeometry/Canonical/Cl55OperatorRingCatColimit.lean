import Mathlib.Algebra.Category.Ring.Colimits
import InfoGeometry.Canonical.Cl55OperatorAlgebraHom

/-!
# Ring-category colimit transport of the operator Cl(5,5) boundary packet

This file uses Mathlib's native `RingCat` colimit and its canonical cocone
injections.  It introduces no alternate colimit object: the only maps used
are `(colimit.ι F j).hom`, which are native ring homomorphisms.
-/

open CategoryTheory CategoryTheory.Limits

variable {J : Type*} [Category J]
variable {F : J ⥤ RingCat} [HasColimit F]

namespace NoncommutativeGeometry

open InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary

theorem ringCat_colimit_ι_operatorCl55
    (j : J) (e f : Fin 5 → F.obj j)
    [Algebra ℚ (F.obj j)] [Algebra ℚ (colimit F).carrier]
    [hCl : OperatorCl55 e f] :
    OperatorCl55
      (fun i => (colimit.ι F j).hom (e i))
      (fun i => (colimit.ι F j).hom (f i)) := by
  exact ringHom_map_operatorCl55 e f (colimit.ι F j).hom

theorem ringCat_colimit_ι_boundary_annihilator_sq
    (j : J) (e f : Fin 5 → F.obj j)
    [Algebra ℚ (F.obj j)] [hCl : OperatorCl55 e f] :
    (colimit.ι F j).hom (boundaryAnnihilator e f) *
        (colimit.ι F j).hom (boundaryAnnihilator e f) = 0 := by
  exact ringHom_map_boundary_annihilator_sq e f (colimit.ι F j).hom

theorem ringCat_colimit_ι_boundary_creator_sq
    (j : J) (e f : Fin 5 → F.obj j)
    [Algebra ℚ (F.obj j)] [hCl : OperatorCl55 e f] :
    (colimit.ι F j).hom (boundaryCreator e f) *
        (colimit.ι F j).hom (boundaryCreator e f) = 0 := by
  exact ringHom_map_boundary_creator_sq e f (colimit.ι F j).hom

theorem ringCat_colimit_ι_boundary_car
    (j : J) (e f : Fin 5 → F.obj j)
    [Algebra ℚ (F.obj j)] [hCl : OperatorCl55 e f] :
    (colimit.ι F j).hom (boundaryAnnihilator e f) *
        (colimit.ι F j).hom (boundaryCreator e f) +
        (colimit.ι F j).hom (boundaryCreator e f) *
        (colimit.ι F j).hom (boundaryAnnihilator e f) = 1 := by
  exact ringHom_map_boundary_car e f (colimit.ι F j).hom

theorem ringCat_colimit_ι_boundary_tkk_scale
    (j : J) (e f : Fin 5 → F.obj j)
    [Algebra ℚ (F.obj j)] [hCl : OperatorCl55 e f] :
    lie_bracket (lie_bracket ((colimit.ι F j).hom (boundaryAnnihilator e f))
      ((colimit.ι F j).hom (boundaryCreator e f)))
      ((colimit.ι F j).hom (boundaryAnnihilator e f)) =
      (colimit.ι F j).hom (boundaryAnnihilator e f) +
        (colimit.ι F j).hom (boundaryAnnihilator e f) := by
  exact ringHom_map_boundary_tkk_scale e f (colimit.ι F j).hom

end NoncommutativeGeometry
