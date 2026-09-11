import InfoGeometry.Canonical.Cl55WittLieRouting
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Concrete five-grade channel readouts

These lemmas concern the associative `MatStage 5` Witt/CAR realization.  They
do not identify that carrier with the non-associative operator-valued Zorn
carrier; the latter has its own channel theorems.
-/

namespace InfoGeometry.Canonical

open Cl55WittLieRouting
open Cl55WittCAR

theorem creation_creation_channel (i j : Fin 5) :
    bracket (creation i) (creation j) ∈ wittPosTwo := by
  exact wittPosOne_bracket_mem_wittPosTwo
    (Submodule.subset_span (Set.mem_range_self i))
    (Submodule.subset_span (Set.mem_range_self j))

theorem annihilation_annihilation_channel (i j : Fin 5) :
    bracket (annihilation i) (annihilation j) ∈ wittNegTwo := by
  exact wittNegOne_bracket_mem_wittNegTwo
    (Submodule.subset_span (Set.mem_range_self i))
    (Submodule.subset_span (Set.mem_range_self j))

theorem creation_annihilation_channel (i j : Fin 5) :
    bracket (creation i) (annihilation j) ∈ wittZero := by
  exact wittPosOne_bracket_mem_wittZero
    (Submodule.subset_span (Set.mem_range_self i))
    (Submodule.subset_span (Set.mem_range_self j))

end InfoGeometry.Canonical
