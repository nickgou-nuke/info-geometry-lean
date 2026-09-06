import InfoGeometry.Algebra.CuntzKMSCondition
import InfoGeometry.Physics.B3PresentedGroup
import InfoGeometry.Physics.JonesBraidB3

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzKMSCondition
open InfoGeometry.Physics.B3PresentedGroup

/-!
## Native Cuntz, Toeplitz--Cuntz, KMS, and braid forwarding surface

The algebraic owners are authoritative:

* `CuntzTensorQuotient` defines `CuntzAlg` and `CuntzToeplitzAlg`;
* `CuntzModularAutomorphism`/`CuntzKMSCondition` define the modular dynamics;
* `B3PresentedGroup` and `JonesBraidB3` define genuine braid-group
  presentations and a matrix representation.

This file only exposes direct consequences of those owners.  It introduces no
diagonal scalar model, no fake Toeplitz vacuum projector, and no permutation
substitute for the braid group.
-/

theorem c3_cuntz_orthogonality (i j : Fin 3) :
    cuntzSdag 3 i * cuntzS 3 j = if i = j then 1 else 0 :=
  cuntz_orthogonality 3 i j

theorem c3_toeplitz_orthogonality (i j : Fin 3) :
    toeplitzSdag 3 i * toeplitzS 3 j = if i = j then 1 else 0 :=
  toeplitz_orthogonality 3 i j

theorem c3_cuntz_partition_of_unity :
    (∑ i : Fin 3, cuntzS 3 i * cuntzSdag 3 i) =
      (1 : CuntzAlg 3) :=
  cuntz_ranges_sum_one 3

theorem c3_cuntz_defect_eq_zero :
    (1 : CuntzAlg 3) - ∑ i : Fin 3, cuntzS 3 i * cuntzSdag 3 i = 0 := by
  rw [c3_cuntz_partition_of_unity]
  simp

theorem c3_modular_projector_fixed
    (primes : Fin 3 → ℕ) (z : ℂ) (i : Fin 3) :
    sigmaComplex 3 primes z (cuntzS 3 i * cuntzSdag 3 i) =
      cuntzS 3 i * cuntzSdag 3 i :=
  sigmaComplex_fixes_projector 3 primes z i

theorem b3_matrix_artin_relation :
    InfoGeometry.Physics.JonesBraidB3.s0 *
        InfoGeometry.Physics.JonesBraidB3.s1 *
        InfoGeometry.Physics.JonesBraidB3.s0 =
      InfoGeometry.Physics.JonesBraidB3.s1 *
        InfoGeometry.Physics.JonesBraidB3.s0 *
        InfoGeometry.Physics.JonesBraidB3.s1 :=
  InfoGeometry.Physics.JonesBraidB3.artin_braid_relation

theorem b3_presented_group_relation :
    FreeGroup.lift braidMap b3Relation = 1 :=
  b3_relation_holds

end InfoGeometry.Canonical
