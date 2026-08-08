import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.OperatorAlgebra.ErlangenJaynesGromov

/-!
# Stable Algebraic Semantics

This module formalizes the categorical skeleton behind the repository's
inductive/operator-algebra method:

* local finite-stage generators and relations;
* functorial transition maps;
* an algebraic direct-limit recipient;
* compatible realizations into another algebra;
* laws proved only from preserved relations.

The point is deliberately algebraic.  No Hilbert-space representation,
operator-norm closure, positivity theorem, spectral theorem, or analytic
thermodynamic limit is asserted here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.StableAlgebraicSemantics

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.OperatorAlgebra.ErlangenJaynesGromov

universe uR uA uS uL uStage

/-! ## 1. Dimension-free square-zero integration -/

/--
The universal parabolic power law in any semiring with a square-zero element.

This is the scalar-free form of the parabolic law: no vector-space or analytic
structure is required.  It is enough that `ε * ε = 0`.
-/
theorem one_add_squareZero_pow
    {A : Type uA} [Semiring A]
    (ε : A) (hε : ε * ε = 0) (n : ℕ) :
    (1 + ε) ^ n = 1 + n • ε := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih]
      have hnε : (n • ε) * ε = 0 := by
        rw [nsmul_eq_mul, mul_assoc, hε, mul_zero]
      rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, hnε]
      simp [Nat.cast_succ, add_mul, one_mul, add_assoc, add_left_comm, add_comm]

/-- Square-zero laws are preserved by semiring homomorphisms. -/
theorem map_squareZero
    {A : Type uA} {B : Type uL} [Semiring A] [Semiring B]
    (f : A →+* B) {ε : A} (hε : ε * ε = 0) :
    f ε * f ε = 0 := by
  simpa [map_mul] using congrArg f hε

/-! ## 2. Stable relations along a finite-to-colimit tower -/

section Tower

variable {Stage : Nat → Type uStage} [∀ n : Nat, Semiring (Stage n)]

/--
A square-zero generator transported along an inductive semiring tower.

This is the abstract categorical version of the split-Clifford nilpotent shield:
the finite-stage representatives are compatible with the bonding maps, and the
stage-zero representative satisfies the local relation.
-/
structure SquareZeroTower
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1)) where
  /-- Compatible finite-stage representatives. -/
  property : ∀ n : Nat, Stage n
  /-- The representatives are preserved by one-step transition maps. -/
  transport : ∀ n : Nat, bond n (property n) = property (n + 1)
  /-- The local relation at the initial stage. -/
  squareZero_zero : property 0 * property 0 = 0

namespace SquareZeroTower

variable {bond : ∀ n : Nat, Stage n →+* Stage (n + 1)}
variable (T : SquareZeroTower (Stage := Stage) bond)

/-- The square-zero relation holds at every finite stage. -/
theorem squareZero_stage (n : Nat) :
    T.property n * T.property n = 0 :=
  InfoGeometry.Algebra.InductiveSuperClosureLemmas.squareZero_all
    bond T.property T.squareZero_zero T.transport n

/-- Canonical image of the stable generator at a finite stage. -/
def colimitWitness (n : Nat) : DirectLimitSuperClosure bond :=
  directLimitOf bond n (T.property n)

/-- All compatible finite representatives define the same direct-limit element. -/
theorem colimitWitness_eq_zeroStage (n : Nat) :
    T.colimitWitness n = T.colimitWitness 0 := by
  exact directLimitOf_eq_zero_stage bond T.property T.transport n

/-- The direct-limit stable generator is square-zero. -/
theorem colimitWitness_squareZero (n : Nat) :
    T.colimitWitness n * T.colimitWitness n = 0 := by
  exact map_squareZero (directLimitOf bond n) (T.squareZero_stage n)

/-- The direct-limit stable generator satisfies the parabolic power law. -/
theorem colimitWitness_parabolic_pow (n k : Nat) :
    (1 + T.colimitWitness n) ^ k = 1 + k • T.colimitWitness n := by
  exact one_add_squareZero_pow (T.colimitWitness n) (T.colimitWitness_squareZero n) k

variable {Limit : Type uStage} [Semiring Limit]

/--
A compatible realization of the tower reads the stable generator as a
square-zero element in the realization algebra.
-/
theorem realization_squareZero
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (n : Nat) :
    toLimit n (T.property n) * toLimit n (T.property n) = 0 := by
  exact map_squareZero (toLimit n) (T.squareZero_stage n)

/--
Every compatible realization inherits the same parabolic power law.

The compatibility cone is not needed for the pointwise law; it matters for
identifying different finite representatives as the same realized stable datum.
-/
theorem realization_parabolic_pow
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (n k : Nat) :
    (1 + toLimit n (T.property n)) ^ k = 1 + k • toLimit n (T.property n) := by
  exact one_add_squareZero_pow
    (toLimit n (T.property n)) (T.realization_squareZero toLimit n) k

/-- A compatible realization reads all finite witnesses as the same stable element. -/
theorem realization_stage_constant
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : CompatibleCone bond toLimit)
    (n : Nat) :
    toLimit n (T.property n) = toLimit 0 (T.property 0) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [← T.transport n, hcone n (T.property n), ih]

end SquareZeroTower

end Tower

/-! ## 3. Erlangen/Jaynes/Gromov packets with a stable parabolic generator -/

section Erlangen

variable {R : Type uR} {A : Type uA} {S : Type uS}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Monoid S]

/--
An Erlangen/Jaynes/Gromov system equipped with a square-zero parabolic
generator that is stable under both symmetry and coarse-graining.
-/
structure StableParabolicPacket where
  /-- Operator algebra plus symmetry action. -/
  system : OperatorErlangenSystem R A S
  /-- Reference algebraic state/readout. -/
  referenceState : OperatorErlangenSystem.AlgebraicState (R := R) (A := A)
  /-- Equivariant coarse-graining projection. -/
  projection : OperatorErlangenSystem.SemigroupProjection system
  /-- The parabolic generator. -/
  generator : A
  /-- Local square-zero relation. -/
  generator_squareZero : generator * generator = 0
  /-- The generator is a symmetry invariant observable. -/
  generator_invariant : system.IsObservableInvariant generator
  /-- Coarse graining fixes the parabolic generator. -/
  projection_fixes_generator : projection.project generator = generator

namespace StableParabolicPacket

variable (P : StableParabolicPacket (R := R) (A := A) (S := S))

/-- The parabolic generator belongs to the invariant geometry. -/
theorem generator_mem_invariantSubalgebra :
    P.generator ∈ P.system.invariantSubalgebra :=
  P.generator_invariant

/-- Symmetry acts trivially on the stable parabolic generator. -/
theorem symmetry_fixes_generator (s : S) :
    P.system.act s P.generator = P.generator :=
  P.generator_invariant s

/-- Coarse graining acts trivially on the stable parabolic generator. -/
theorem projection_fixes :
    P.projection.project P.generator = P.generator :=
  P.projection_fixes_generator

/-- Scalar parabolic translations of the generator obey the universal power law. -/
theorem scalar_parabolic_power (t : R) (n : Nat) :
    (1 + t • P.generator) ^ n = 1 + ((n : R) * t) • P.generator := by
  exact OperatorErlangenSystem.nilpotent_power_law
    (R := R) (A := A) P.generator P.generator_squareZero t n

/-- The scalar-free parabolic law is also available without using the `R` action. -/
theorem nsmul_parabolic_power (n : Nat) :
    (1 + P.generator) ^ n = 1 + n • P.generator := by
  exact one_add_squareZero_pow P.generator P.generator_squareZero n

/-- Symmetry invariance gives state-level invariance of generator readouts. -/
theorem pullback_generator_readout (s : S) :
    OperatorErlangenSystem.pullbackState P.system s P.referenceState P.generator =
      P.referenceState P.generator := by
  calc
    OperatorErlangenSystem.pullbackState P.system s P.referenceState P.generator
        = P.referenceState (P.system.act s P.generator) := by
            rfl
    _ = P.referenceState P.generator := by
            rw [P.symmetry_fixes_generator s]

end StableParabolicPacket

end Erlangen

end InfoGeometry.OperatorAlgebra.StableAlgebraicSemantics
