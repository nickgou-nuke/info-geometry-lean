/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge
import InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement
import InfoGeometry.Topology.KleinBottleQuotient
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Arithmetic.SarnakLocalCertification

open InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge
open InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Topology.KleinBottleQuotient

inductive Archetype
  | arithmetic
  | continuation
  | reflection
  | finitePairing
  deriving DecidableEq

instance : Fintype Archetype where
  elems := {.arithmetic, .continuation, .reflection, .finitePairing}
  complete x := by
    cases x <;> decide

abbrev DependencyContext := Finset Archetype

def reflectionContext : DependencyContext :=
  {.continuation, .reflection}

def finitePairingContext : DependencyContext :=
  {.continuation, .reflection, .finitePairing}

theorem reflection_precedes_finite_pairing :
    reflectionContext ≤ finitePairingContext := by
  decide

theorem critical_reflection_involutive :
    Function.Involutive antiunitaryCriticalReflection := by
  intro point
  simp [antiunitaryCriticalReflection]

theorem entireRiemannXi_zero_reflection {point : ℂ}
    (zeroAt : entireRiemannXi point = 0) :
    entireRiemannXi (antiunitaryCriticalReflection point) = 0 := by
  change entireRiemannXi (1 - star point) = 0
  rw [entireRiemannXi_one_sub, ← entireRiemannXi_conj, zeroAt, star_zero]

theorem entireRiemannXi_zero_reflection_iff (point : ℂ) :
    entireRiemannXi point = 0 ↔
      entireRiemannXi (antiunitaryCriticalReflection point) = 0 := by
  constructor
  · exact entireRiemannXi_zero_reflection
  · intro reflectedZero
    have := entireRiemannXi_zero_reflection reflectedZero
    rw [critical_reflection_involutive point] at this
    exact this

theorem symmetric_functions_need_not_have_critical_zeros :
    ¬ (∀ function : ℂ → ℂ, EvenCentered function →
      ∀ point : ℂ, ZeroAt function point → point.re = 0) := by
  intro claimedConfinement
  obtain ⟨function, point, symmetry, zeroAt, _, offAxis⟩ :=
    even_symmetry_allows_off_axis_zero_pair
  exact offAxis (claimedConfinement function symmetry point zeroAt)

def counterexample_f (point : ℂ) : ℂ :=
  point * (point - 1)

theorem counterexample_reflection_zero (point : ℂ) :
    counterexample_f point = 0 ↔
      counterexample_f (antiunitaryCriticalReflection point) = 0 := by
  have reflected : counterexample_f (antiunitaryCriticalReflection point) =
      star (counterexample_f point) := by
    simp only [counterexample_f, antiunitaryCriticalReflection, star_mul, star_sub, star_one]
    ring
  rw [reflected, star_eq_zero]

theorem symmetric_zero_can_be_off_horizon :
    counterexample_f 0 = 0 ∧ (0 : ℂ).re ≠ 1 / 2 := by
  norm_num [counterexample_f]

section NonCommutativeOperatorRealization

variable {B : Type*} [Ring B]

def sarnakCertificationArchetypeOperator (P A C : B) : Archetype → B
  | .arithmetic => conePlus P A
  | .continuation => genPhi P A C
  | .reflection => invS P
  | .finitePairing => genJ P A C

theorem sarnak_local_certification_operator_tetraktys
    {P : B} (hP : P * P = P) (A C : B) :
    sarnakCertificationArchetypeOperator P A C .arithmetic *
      sarnakCertificationArchetypeOperator P A C .arithmetic = 0 ∧
    sarnakCertificationArchetypeOperator P A C .reflection *
      sarnakCertificationArchetypeOperator P A C .reflection = (1 : B) ∧
    sarnakCertificationArchetypeOperator P A C .reflection *
      sarnakCertificationArchetypeOperator P A C .continuation =
      sarnakCertificationArchetypeOperator P A C .finitePairing ∧
    sarnakCertificationArchetypeOperator P A C .continuation *
      sarnakCertificationArchetypeOperator P A C .continuation +
      sarnakCertificationArchetypeOperator P A C .finitePairing *
        sarnakCertificationArchetypeOperator P A C .finitePairing = 0 := by
  dsimp only [sarnakCertificationArchetypeOperator]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end NonCommutativeOperatorRealization

end InfoGeometry.Arithmetic.SarnakLocalCertification
