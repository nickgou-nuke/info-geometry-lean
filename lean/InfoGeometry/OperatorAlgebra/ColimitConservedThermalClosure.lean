import InfoGeometry.OperatorAlgebra.ColimitBracketTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Colimit inheritance of conserved grand-canonical operators

This file records a noncommutative inheritance theorem for the canonical
`RingCat` colimit injections.  The coefficient ring is only a ring: no
complex scalar structure is introduced at the colimit level.
-/

namespace InfoGeometry.OperatorAlgebra

open CategoryTheory CategoryTheory.Limits

universe u

variable {J : Type u} [Category.{u} J]
variable (F : J ⥤ RingCat.{u}) [HasColimit F]

theorem colimit_ι_grandCanonical_commutes_of_conserved
    (j : J) (β H μ N μχ Q : F.obj j)
    (hβQ : β * Q = Q * β)
    (hμQ : μ * Q = Q * μ)
    (hμχQ : μχ * Q = Q * μχ)
    (hHQ : quadraticCommutator H Q = 0)
    (hNQ : quadraticCommutator N Q = 0) :
    quadraticCommutator
        ((colimit.ι F j).hom (grandCanonicalOperator β H μ N μχ Q))
        ((colimit.ι F j).hom Q) = 0 := by
  rw [colimit_ι_map_grandCanonicalOperator F j β H μ N μχ Q]
  rw [grandCanonicalOperator_commutes_of_conserved
    ((colimit.ι F j).hom β)
    ((colimit.ι F j).hom H)
    ((colimit.ι F j).hom μ)
    ((colimit.ι F j).hom N)
    ((colimit.ι F j).hom μχ)
    ((colimit.ι F j).hom Q)]
  · simpa using congrArg (colimit.ι F j).hom hβQ
  · simpa using congrArg (colimit.ι F j).hom hμQ
  · simpa using congrArg (colimit.ι F j).hom hμχQ
  · rw [← colimit_ι_map_quadraticCommutator F j H Q, hHQ]
    exact map_zero (colimit.ι F j).hom
  · rw [← colimit_ι_map_quadraticCommutator F j N Q, hNQ]
    exact map_zero (colimit.ι F j).hom

end InfoGeometry.OperatorAlgebra
