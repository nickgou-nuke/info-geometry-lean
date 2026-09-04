import InfoGeometry.Algebra.OperatorSymbolCore
import InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

/-!
# Canonical readback for quaternionic Pauli--Dirac soldering

This file identifies the concrete Pauli/Witt declarations with the new
dimension-free algebraic owners in `OperatorSymbolCore`.

The purpose is architectural: downstream code keeps the established concrete
names, while the reusable mathematical content is owned upstream by generic
module/ring theorems.
-/

noncomputable section

namespace InfoGeometry.Bridge.QuaternionicPauliDiracCanonicalReadback

open Matrix
open scoped Matrix

open InfoGeometry.Algebra.OperatorSymbolCore
open InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

/-! ## Dirac symbol readback -/

/-- The concrete chiral Weyl operator is exactly the universal off-diagonal
module endomorphism instantiated with the two matrix `mulVec` maps. -/
theorem chiralWeylOperator_eq_offDiagonalEnd
    (A B : PauliBlock) :
    chiralWeylOperator A B =
      offDiagonalEnd A.mulVecLin B.mulVecLin := by
  apply LinearMap.ext
  rintro ⟨ψL, ψR⟩
  rfl

/-- The concrete two-block square theorem is the generic off-diagonal square
law read back through the matrix carrier. -/
theorem chiralWeylOperator_sq_from_symbol_core
    (A B : PauliBlock) (ψ : DiracSpinor) :
    chiralWeylOperator A B (chiralWeylOperator A B ψ) =
      ((A * B) *ᵥ ψ.1, (B * A) *ᵥ ψ.2) := by
  rw [chiralWeylOperator_eq_offDiagonalEnd]
  rw [offDiagonalEnd_sq_apply]
  rcases ψ with ⟨ψL, ψR⟩
  simp [Matrix.mulVecLin, Matrix.mulVec_mulVec]

/-- Soldered principal-symbol square, now exposed as a canonical readback of
`offDiagonalEnd_sq_scalar_apply` together with the already-proved Pauli
factorizations. -/
theorem soldered_symbol_square_from_core
    (P : InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector)
    (ψ : DiracSpinor) :
    chiralWeylOperator P.pauliMatrix (coSolderingMap P)
        (chiralWeylOperator P.pauliMatrix (coSolderingMap P) ψ) =
      (P.minkowskiNormSq : ℂ) • ψ := by
  exact soldered_chiralWeylOperator_sq_apply P ψ

/-! ## Rank-one CAR / Peirce readback -/

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

/-- The entire concrete circular/Peirce packet is an instance of the generic
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

/-- Existing positive-projector idempotence follows from the canonical CAR
owner after identifying the projector. -/
theorem chiralPlus_sq_from_car : chiralPlus * chiralPlus = chiralPlus := by
  rw [chiralPlus_eq_carPlus]
  exact carPlus_idempotent circularPlus_sq_zero circular_car

/-- Existing negative-projector idempotence follows from the canonical CAR
owner. -/
theorem chiralMinus_sq_from_car : chiralMinus * chiralMinus = chiralMinus := by
  rw [chiralMinus_eq_carMinus]
  exact carMinus_idempotent circularMinus_sq_zero circular_car

/-- Concrete sector completeness is the CAR anticommutator. -/
theorem chiral_projectors_complete_from_car :
    chiralPlus + chiralMinus = 1 := by
  rw [chiralPlus_eq_carPlus, chiralMinus_eq_carMinus]
  exact car_projectors_complete circular_car

/-- Concrete two-sided Peirce transport is the generic creation/annihilation
transport theorem. -/
theorem circular_peirce_transport_from_car :
    chiralPlus * circularPlus * chiralMinus = circularPlus ∧
      chiralMinus * circularMinus * chiralPlus = circularMinus := by
  rw [chiralPlus_eq_carPlus, chiralMinus_eq_carMinus]
  exact ⟨car_create_peirce_transport circularPlus_sq_zero circular_car,
    car_annihilate_peirce_transport circularMinus_sq_zero circular_car⟩

end InfoGeometry.Bridge.QuaternionicPauliDiracCanonicalReadback
