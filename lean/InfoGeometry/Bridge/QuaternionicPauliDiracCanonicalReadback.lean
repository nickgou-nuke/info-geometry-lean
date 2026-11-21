/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.OperatorSymbolCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

/-! Canonical readback of the concrete Pauli--Dirac bridge through the
dimension-free off-diagonal operator owner. -/

noncomputable section

namespace InfoGeometry.Bridge.QuaternionicPauliDiracCanonicalReadback

open Matrix
open scoped Matrix
open InfoGeometry.Algebra.OperatorSymbolCore
open InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

theorem chiralWeylOperator_eq_offDiagonalEnd (A B : PauliBlock) :
    chiralWeylOperator A B =
      offDiagonalEnd A.mulVecLin B.mulVecLin := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  rfl

theorem chiralWeylOperator_sq_from_symbol_core
    (A B : PauliBlock) (ψ : DiracSpinor) :
    chiralWeylOperator A B (chiralWeylOperator A B ψ) =
      ((A * B) *ᵥ ψ.1, (B * A) *ᵥ ψ.2) := by
  rw [chiralWeylOperator_eq_offDiagonalEnd, offDiagonalEnd_sq_apply]
  rcases ψ with ⟨ψL, ψR⟩
  change (A *ᵥ (B *ᵥ ψL), B *ᵥ (A *ᵥ ψR)) =
    ((A * B) *ᵥ ψL, (B * A) *ᵥ ψR)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem soldered_symbol_square_from_core
    (P : InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector)
    (ψ : DiracSpinor) :
    chiralWeylOperator P.pauliMatrix (coSolderingMap P)
        (chiralWeylOperator P.pauliMatrix (coSolderingMap P) ψ) =
      (P.minkowskiNormSq : ℂ) • ψ := by
  exact soldered_chiralWeylOperator_sq_apply P ψ


/-- Positive Peirce projector is the canonical `c† c` CAR projector. -/
theorem chiralPlus_eq_carPlus :
    chiralPlus = carPlus circularPlus circularMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralPlus, carPlus, circularPlus, circularMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Negative Peirce projector is the canonical `c c†` CAR projector. -/
theorem chiralMinus_eq_carMinus :
    chiralMinus = carMinus circularPlus circularMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralMinus, carMinus, circularPlus, circularMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The concrete circular/Peirce packet is an instance of the generic
rank-one CAR theorem. -/
theorem circular_rankOneCAR_packet :
    carPlus circularPlus circularMinus * carPlus circularPlus circularMinus =
        carPlus circularPlus circularMinus ∧
      carMinus circularPlus circularMinus * carMinus circularPlus circularMinus =
        carMinus circularPlus circularMinus ∧
      carPlus circularPlus circularMinus + carMinus circularPlus circularMinus = 1 ∧
      carPlus circularPlus circularMinus * carMinus circularPlus circularMinus = 0 ∧
      carMinus circularPlus circularMinus * carPlus circularPlus circularMinus = 0 ∧
      carPlus circularPlus circularMinus * circularPlus *
          carMinus circularPlus circularMinus = circularPlus ∧
      carMinus circularPlus circularMinus * circularMinus *
          carPlus circularPlus circularMinus = circularMinus := by
  exact rankOneCAR_peirce_packet
    circularPlus_sq_zero circularMinus_sq_zero circular_car

theorem chiralPlus_sq_from_car : chiralPlus * chiralPlus = chiralPlus := by
  rw [chiralPlus_eq_carPlus]
  exact carPlus_idempotent circularPlus_sq_zero circular_car

theorem chiralMinus_sq_from_car : chiralMinus * chiralMinus = chiralMinus := by
  rw [chiralMinus_eq_carMinus]
  exact carMinus_idempotent circularMinus_sq_zero circular_car

theorem chiral_projectors_complete_from_car :
    chiralPlus + chiralMinus = 1 := by
  rw [chiralPlus_eq_carPlus, chiralMinus_eq_carMinus]
  exact car_projectors_complete circular_car

theorem circular_peirce_transport_from_car :
    chiralPlus * circularPlus * chiralMinus = circularPlus ∧
      chiralMinus * circularMinus * chiralPlus = circularMinus := by
  rw [chiralPlus_eq_carPlus, chiralMinus_eq_carMinus]
  exact ⟨car_create_peirce_transport circularPlus_sq_zero circular_car,
    car_annihilate_peirce_transport circularMinus_sq_zero circular_car⟩

end InfoGeometry.Bridge.QuaternionicPauliDiracCanonicalReadback
