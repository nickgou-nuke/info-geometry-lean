import InfoGeometry.Lie.CanonicalZornOperatorDerivationLane
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.DerivationWeightPreservation

/-!
# Grade preservation for the canonical Zorn operator action

The canonical Zorn derivation lane acts on the associative algebra of
endomorphisms by an inner commutator.  This owner specializes the generic
Leibniz/weight theorem to that actual action; no commutative model or new
grading carrier is introduced.
-/

namespace InfoGeometry.Lie.CanonicalZornOperatorGradePreservation

open InfoGeometry.Algebra
open InfoGeometry.Algebra.NonAssocDerivation
open InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornOperatorDerivationLane

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

theorem operatorAdjoint_preserves_grade
    (D : canonicalZornDerivations) (N : EndCZ) (k : ℤ)
    (hN : (operatorAdjointDerivation D : OperatorDer).1 N = 0) :
    Set.MapsTo (operatorAdjointDerivation D : OperatorDer).1
      (gradeSubmodule N k : Set EndCZ)
      (gradeSubmodule N k : Set EndCZ) := by
  intro X hX
  exact (derivation_preserves_gradeSubmodule
    (operatorAdjointDerivation D : OperatorDer).1
    (operatorAdjointDerivation D).property
    N k hN) hX

theorem operatorAdjoint_preserves_grade_family
    (D : canonicalZornDerivations) (N : EndCZ)
    (hN : (operatorAdjointDerivation D : OperatorDer).1 N = 0) :
    PreservesGrade
      (fun k : ℤ => (gradeSubmodule N k : Set EndCZ))
      (fun _ : Unit => (operatorAdjointDerivation D : OperatorDer).1) := by
  intro _ k X hX
  exact operatorAdjoint_preserves_grade D N k hN hX

end InfoGeometry.Lie.CanonicalZornOperatorGradePreservation
