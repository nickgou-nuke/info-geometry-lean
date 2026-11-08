/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Arithmetic.RiemannLectureDependencies

open InfoGeometry.OperatorAlgebra.PeirceSpine

inductive Archetype
  | eulerProduct
  | dirichletSeries
  | sumProductIdentification
  | functionalEquation
  | schwarzSymmetry
  | zeroReflection
  | finiteZeroPairing
  deriving DecidableEq

instance : Fintype Archetype where
  elems := {.eulerProduct, .dirichletSeries, .sumProductIdentification,
    .functionalEquation, .schwarzSymmetry, .zeroReflection,
    .finiteZeroPairing}
  complete x := by
    cases x <;> decide

def prerequisites : Archetype → Finset ℕ
  | .eulerProduct => {0}
  | .dirichletSeries => {1}
  | .sumProductIdentification => {0, 1, 2}
  | .functionalEquation => {3}
  | .schwarzSymmetry => {4}
  | .zeroReflection => {3, 4, 5}
  | .finiteZeroPairing => {3, 4, 5, 6}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Archetype :=
  PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := Archetype) (· ≤ ·) :=
  fun left right => inferInstanceAs (Decidable (prerequisites left ⊆ prerequisites right))

theorem arithmetic_branch :
    Archetype.eulerProduct ≤ Archetype.sumProductIdentification ∧
      Archetype.dirichletSeries ≤ Archetype.sumProductIdentification := by decide

theorem symmetry_branch :
    Archetype.functionalEquation ≤ Archetype.zeroReflection ∧
      Archetype.schwarzSymmetry ≤ Archetype.zeroReflection := by decide

theorem finite_zero_pairing_branch :
    Archetype.zeroReflection ≤ Archetype.finiteZeroPairing := by decide

theorem arithmetic_and_finite_zero_pairing_incomparable :
    ¬ Archetype.sumProductIdentification ≤ Archetype.finiteZeroPairing ∧
      ¬ Archetype.finiteZeroPairing ≤ Archetype.sumProductIdentification := by
  decide

theorem no_cycle (left right : Archetype) (forward : left ≤ right)
    (backward : right ≤ left) : left = right :=
  le_antisymm forward backward

section NonCommutativeOperatorRealization

variable {B : Type*} [Ring B]

def riemannLectureArchetypeOperator (P A C X : B) : Archetype → B
  | .eulerProduct => conePlus P A
  | .dirichletSeries => coneMinus P C
  | .sumProductIdentification => evenGrade P X + oddGrade P X
  | .functionalEquation => invS P
  | .schwarzSymmetry => genPhi P A C
  | .zeroReflection => genJ P A C
  | .finiteZeroPairing => genSig P A C

theorem riemann_lecture_dependencies_operator_tetraktys
    {P : B} (hP : P * P = P) (A C X : B) :
    riemannLectureArchetypeOperator P A C X .eulerProduct *
      riemannLectureArchetypeOperator P A C X .eulerProduct = 0 ∧
    riemannLectureArchetypeOperator P A C X .dirichletSeries *
      riemannLectureArchetypeOperator P A C X .dirichletSeries = 0 ∧
    riemannLectureArchetypeOperator P A C X .sumProductIdentification = X ∧
    riemannLectureArchetypeOperator P A C X .functionalEquation *
      riemannLectureArchetypeOperator P A C X .functionalEquation = (1 : B) ∧
    riemannLectureArchetypeOperator P A C X .zeroReflection *
      riemannLectureArchetypeOperator P A C X .schwarzSymmetry =
      riemannLectureArchetypeOperator P A C X .finiteZeroPairing ∧
    riemannLectureArchetypeOperator P A C X .schwarzSymmetry *
      riemannLectureArchetypeOperator P A C X .schwarzSymmetry +
      riemannLectureArchetypeOperator P A C X .zeroReflection *
        riemannLectureArchetypeOperator P A C X .zeroReflection = 0 := by
  dsimp only [riemannLectureArchetypeOperator]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end NonCommutativeOperatorRealization

end InfoGeometry.Arithmetic.RiemannLectureDependencies
