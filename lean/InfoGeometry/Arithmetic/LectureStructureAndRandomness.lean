/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.LiouvilleFiniteCorrelation
import InfoGeometry.Arithmetic.SarnakLocalCertification
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Arithmetic structure and finite statistical observations

This is the finite arithmetic and symmetry corridor extracted from the lecture.
The dependency poset records the organization of this corridor, not implications
between conjectures. Spectral statistics requires spectral input independently
of functional symmetry.

Gauss sums and reciprocity use Mathlib directly. Liouville counting and zero
reflection pairing retain their existing owners. No asymptotic cancellation,
normality of pi, Riemann hypothesis, quantum gate optimality, or random-matrix
universality theorem is asserted here.
-/

namespace InfoGeometry.Arithmetic.LectureStructureAndRandomness

open scoped BigOperators
open BostConnesSystem

export LiouvilleFiniteCorrelation
  (shiftedLiouville finite_sign_correlation liouville_correlation_count
    liouville_correlation_zero_iff liouville_self_correlation
    liouville_correlation_abs_le liouville_correlation_ne_zero_of_odd_card)

export SarnakLocalCertification
  (critical_reflection_involutive
    entireRiemannXi_zero_reflection
    entireRiemannXi_zero_reflection_iff counterexample_f
    counterexample_reflection_zero symmetric_zero_can_be_off_horizon)

export InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
  (antiunitaryCriticalReflection)

inductive Archetype
  | finiteFields
  | characters
  | gaussIdentities
  | primeFactorization
  | liouvilleParity
  | finiteCounting
  | finiteCorrelations
  | functionalSymmetry
  | zeroPairing
  | spectralRealization
  | spectralStatistics
  deriving DecidableEq

private def archetypeEquivFin : Archetype ≃ Fin 11 where
  toFun
    | .finiteFields => 0
    | .characters => 1
    | .gaussIdentities => 2
    | .primeFactorization => 3
    | .liouvilleParity => 4
    | .finiteCounting => 5
    | .finiteCorrelations => 6
    | .functionalSymmetry => 7
    | .zeroPairing => 8
    | .spectralRealization => 9
    | .spectralStatistics => 10
  invFun
    | 0 => .finiteFields
    | 1 => .characters
    | 2 => .gaussIdentities
    | 3 => .primeFactorization
    | 4 => .liouvilleParity
    | 5 => .finiteCounting
    | 6 => .finiteCorrelations
    | 7 => .functionalSymmetry
    | 8 => .zeroPairing
    | 9 => .spectralRealization
    | 10 => .spectralStatistics
    | _ => .finiteFields
  left_inv a := by cases a <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Archetype := Fintype.ofEquiv (Fin 11) archetypeEquivFin.symm

def prerequisites : Archetype → Finset ℕ
  | .finiteFields => {0}
  | .characters => {0, 1}
  | .gaussIdentities => {0, 1, 2}
  | .primeFactorization => {3}
  | .liouvilleParity => {3, 4}
  | .finiteCounting => {5}
  | .finiteCorrelations => {3, 4, 5, 6}
  | .functionalSymmetry => {7}
  | .zeroPairing => {7, 8}
  | .spectralRealization => {9}
  | .spectralStatistics => {9, 10}

theorem prerequisites_injective : Function.Injective prerequisites := by
  decide

instance : PartialOrder Archetype :=
  PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := Archetype) (· ≤ ·) :=
  fun first second =>
    inferInstanceAs (Decidable (prerequisites first ⊆ prerequisites second))

theorem gauss_branch :
    Archetype.finiteFields ≤ Archetype.characters ∧
      Archetype.characters ≤ Archetype.gaussIdentities := by
  decide

theorem correlation_branch :
    Archetype.primeFactorization ≤ Archetype.liouvilleParity ∧
      Archetype.liouvilleParity ≤ Archetype.finiteCorrelations ∧
      Archetype.finiteCounting ≤ Archetype.finiteCorrelations := by
  decide

theorem symmetry_branch :
    Archetype.functionalSymmetry ≤ Archetype.zeroPairing := by
  decide

theorem spectral_branch :
    Archetype.spectralRealization ≤ Archetype.spectralStatistics := by
  decide

theorem symmetry_and_spectral_realization_incomparable :
    ¬ Archetype.zeroPairing ≤ Archetype.spectralRealization ∧
      ¬ Archetype.spectralRealization ≤ Archetype.zeroPairing := by
  decide

theorem dependency_antisymmetric (first second : Archetype)
    (forward : first ≤ second) (backward : second ≤ first) :
    first = second :=
  le_antisymm forward backward

section GaussSums

variable {FieldType : Type*} [Field FieldType] [Fintype FieldType]
variable {multiplicative : MulChar FieldType ℂ}
variable {additive : AddChar FieldType ℂ}

theorem gauss_duality (nontrivial : multiplicative ≠ 1)
    (primitive : additive.IsPrimitive) :
    gaussSum multiplicative additive *
        gaussSum multiplicative⁻¹ additive⁻¹ =
      (Fintype.card FieldType : ℂ) :=
  gaussSum_mul_gaussSum_eq_card nontrivial primitive

theorem quadratic_gauss_square (nontrivial : multiplicative ≠ 1)
    (quadratic : multiplicative.IsQuadratic) (primitive : additive.IsPrimitive) :
    gaussSum multiplicative additive ^ 2 =
      multiplicative (-1) * (Fintype.card FieldType : ℂ) :=
  gaussSum_sq nontrivial quadratic primitive

end GaussSums

theorem quadratic_reciprocity_one_mod_four (firstPrime secondPrime : ℕ)
    [Fact firstPrime.Prime] [Fact secondPrime.Prime]
    (first_mod_four : firstPrime % 4 = 1) (second_odd : secondPrime ≠ 2) :
    legendreSym secondPrime firstPrime = legendreSym firstPrime secondPrime :=
  legendreSym.quadratic_reciprocity_one_mod_four first_mod_four second_odd

theorem liouville_completely_multiplicative (first second : ℕ+) :
    liouville (first.val * second.val) = liouville first * liouville second :=
  liouville_mul first second first.pos second.pos first.ne_zero second.ne_zero

theorem dilation_correlation (samples : Finset ℕ+) (multiplier : ℕ+) :
    (∑ index ∈ samples, liouville index * liouville (multiplier.val * index.val)) =
      liouville multiplier * (samples.card : ℤ) := by
  calc
    (∑ index ∈ samples, liouville index * liouville (multiplier.val * index.val)) =
        ∑ _index ∈ samples, liouville multiplier := by
      apply Finset.sum_congr rfl
      intro index member
      rw [liouville_completely_multiplicative multiplier index]
      calc
        liouville index * (liouville multiplier * liouville index) =
            liouville multiplier * (liouville index * liouville index) := by ring
        _ = liouville multiplier := by rw [liouville_sq index index.pos, mul_one]
    _ = liouville multiplier * (samples.card : ℤ) := by simp [mul_comm]

theorem prime_dilation_correlation (samples : Finset ℕ+) (prime : ℕ)
    (prime_is_prime : prime.Prime) :
    (∑ index ∈ samples, liouville index * liouville (prime * index.val)) =
      -(samples.card : ℤ) := by
  have identity := dilation_correlation samples ⟨prime, prime_is_prime.pos⟩
  change (∑ index ∈ samples,
    liouville index.val * liouville (prime * index.val)) =
      liouville prime * (samples.card : ℤ) at identity
  rw [liouville_prime prime prime_is_prime, neg_one_mul] at identity
  exact identity

theorem functional_symmetry_pairs_zeros (function : ℂ → ℂ)
    (reflection : ∀ point, function (1 - point) = function point)
    {point : ℂ} (zero_at : function point = 0) :
    function (1 - point) = 0 := by
  rw [reflection point, zero_at]

theorem functional_symmetry_does_not_force_critical_zeros :
    ∃ function : ℂ → ℂ,
      (∀ point, function (1 - point) = function point) ∧
      function 0 = 0 ∧ (0 : ℂ).re ≠ 1 / 2 := by
  refine ⟨counterexample_f, ?_, ?_, ?_⟩
  · intro point
    dsimp [SarnakLocalCertification.counterexample_f]
    ring
  · simp [SarnakLocalCertification.counterexample_f]
  · norm_num

theorem finite_checks_do_not_imply_universal (bound : ℕ) :
    ∃ predicate : ℕ → Prop,
      (∀ index ≤ bound, predicate index) ∧ ¬ ∀ index, predicate index := by
  refine ⟨fun index => index ≤ bound, ?_, ?_⟩
  · intro index within_bound
    exact within_bound
  · intro universal
    have impossible := universal (bound + 1)
    omega

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def lectureArchetypeOperator (P A C X : B) : Archetype → B
  | .finiteFields => P
  | .characters => invS P
  | .gaussIdentities => invS P * invS P
  | .primeFactorization => conePlus P A
  | .liouvilleParity => coneMinus P C
  | .finiteCounting => evenGrade P X + oddGrade P X
  | .finiteCorrelations => genSig P A C
  | .functionalSymmetry => genPhi P A C
  | .zeroPairing => genJ P A C
  | .spectralRealization => genV P A C
  | .spectralStatistics => genSig P A C * genSig P A C - genV P A C * genV P A C

theorem lecture_structure_and_randomness_operator_tetraktys
    {P : B} (hP : P * P = P) (A C X : B) :
    lectureArchetypeOperator P A C X .gaussIdentities = (1 : B) ∧
    lectureArchetypeOperator P A C X .primeFactorization *
      lectureArchetypeOperator P A C X .primeFactorization = 0 ∧
    lectureArchetypeOperator P A C X .liouvilleParity *
      lectureArchetypeOperator P A C X .liouvilleParity = 0 ∧
    lectureArchetypeOperator P A C X .finiteCounting = X ∧
    lectureArchetypeOperator P A C X .functionalSymmetry *
      lectureArchetypeOperator P A C X .functionalSymmetry =
      lectureArchetypeOperator P A C X .spectralRealization ∧
    lectureArchetypeOperator P A C X .zeroPairing *
      lectureArchetypeOperator P A C X .functionalSymmetry =
      lectureArchetypeOperator P A C X .finiteCorrelations ∧
    lectureArchetypeOperator P A C X .spectralStatistics = 0 := by
  dsimp only [lectureArchetypeOperator]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end NonCommutativeOperatorRealization

end InfoGeometry.Arithmetic.LectureStructureAndRandomness
