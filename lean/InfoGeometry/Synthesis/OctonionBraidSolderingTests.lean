import InfoGeometry.Synthesis.OctonionBraidSoldering

namespace InfoGeometry.Synthesis.OctonionBraidSoldering.Tests

open InfoGeometry.Canonical.ArtinBraidFilteredColimit
open InfoGeometry.Canonical.SplitOctonionRightRegularBraid

example : braidUnit 0 * braidUnit 1 * braidUnit 0 = braidUnit 1 * braidUnit 0 * braidUnit 1 :=
  braidUnit_artin

example : braidUnit 0 ≠ 1 := braidUnit_ne_one 0

example (index : Fin 2) : braidRepresentation (PresentedGroup.of index) = braidUnit index :=
  braidRepresentation_generator index

example (first second : ArtinBraid 2) (operator : EndCZ) :
    braidConjugation (first * second) operator =
      braidConjugation first (braidConjugation second operator) :=
  braidConjugation_mul first second operator

example (metric left right : EndCZ) :
    braidConjugation 1 (sandwich metric left right) = sandwich metric left right :=
  braidConjugation_one _

#print axioms braidUnit_artin
#print axioms braidRepresentation
#print axioms fock_braid_intertwines
#print axioms represented_artin_on_sandwich
#print axioms braidUnit_ne_one

end InfoGeometry.Synthesis.OctonionBraidSoldering.Tests
