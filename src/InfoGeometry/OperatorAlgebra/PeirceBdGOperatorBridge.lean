/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.LeftRightActions
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicBridge

/-!
# BdG mass interaction over the Peirce tetraktys operator spine

This bridge uses the existing Peirce tetraktys, left/right superoperator,
adjoint, and cyclotomic owners. It identifies the mass-coupled matrix square
with its Peirce expansion, then identifies the BdG `H⁴ − H² + 1` Higgs
polynomial with the existing `cyclotomicSix` evaluated at `H²`. The Peirce
mass interaction also feeds the left/right superoperators and adjoint table.
The commutator defect is retained in the polynomial argument.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceBdGOperatorBridge

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge

variable {A : Type*} [Ring A] [StarRing A]

private def massUp (M : A) : Matrix (Fin 2) (Fin 2) A := !![0, M; 0, 0]
private def massDown (M : A) : Matrix (Fin 2) (Fin 2) A := !![0, 0; M, 0]

/-- On the matrix carrier, the obstruction in the massive square is exactly
the tetraktys commutator `[evenGrade D, J]`, by the Peirce BdG square law. -/
theorem massiveBdG_square_is_Peirce_tetraktys_expansion (D M : A) :
    InfoGeometry.Physics.massiveBdGHamiltonian D M *
        InfoGeometry.Physics.massiveBdGHamiltonian D M =
      evenGrade (peirceSheetProj (A := A)) (!![D, 0; 0, D]) *
          evenGrade (peirceSheetProj (A := A)) (!![D, 0; 0, D]) +
        genV (peirceSheetProj (A := A)) (!![0, M; 0, 0]) (!![0, 0; M, 0]) +
        comm
          (evenGrade (peirceSheetProj (A := A)) (!![D, 0; 0, D]))
          (genJ (peirceSheetProj (A := A)) (!![0, M; 0, 0]) (!![0, 0; M, 0])) := by
  rw [(massiveBdGHamiltonian_peirce_and_noncomm_sq D M).1]
  exact peirceBdGHamiltonian_sq (peirceSheetProj_idem (A := A))
    (!![D, 0; 0, D]) (!![0, M; 0, 0]) (!![0, 0; M, 0])

/-- The Peirce interaction defect is exactly the off-diagonal anomaly in the
operator-valued BdG square. This identifies the two presentations on their
common matrix carrier, retaining both ordered products `D * M` and `M * D`. -/
theorem massiveBdG_peirce_commutator_eq_andreev_anomaly (D M : A) :
    comm
      (evenGrade (peirceSheetProj (A := A)) (!![D, 0; 0, D]))
      (genJ (peirceSheetProj (A := A)) (!![0, M; 0, 0]) (!![0, 0; M, 0])) =
        InfoGeometry.Physics.massiveBdGCommutatorAnomaly D M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.massiveBdGCommutatorAnomaly,
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade,
      InfoGeometry.OperatorAlgebra.PeirceSpine.peirce11,
      InfoGeometry.OperatorAlgebra.PeirceSpine.peirce00,
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ,
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus,
      peirceSheetProj, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;> noncomm_ring

/-- Andreev reflection acts by `-1` on the Peirce interaction commutator.
This makes the hole-reflected contribution cancel the original anomaly. -/
theorem andreev_reflect_peirce_interaction_defect (D M : A) :
    InfoGeometry.Physics.andreevSwap *
      comm
        (evenGrade (peirceSheetProj (A := A)) (!![D, 0; 0, D]))
        (genJ (peirceSheetProj (A := A)) (!![0, M; 0, 0]) (!![0, 0; M, 0])) *
      InfoGeometry.Physics.andreevSwap =
        -comm
          (evenGrade (peirceSheetProj (A := A)) (!![D, 0; 0, D]))
          (genJ (peirceSheetProj (A := A)) (!![0, M; 0, 0]) (!![0, 0; M, 0])) := by
  rw [massiveBdG_peirce_commutator_eq_andreev_anomaly]
  exact InfoGeometry.Physics.andreev_reflect_mass_commutator_anomaly D M

/-- The sum of the particle and hole-reflected Peirce interaction defects is
zero in every associative coefficient ring; no commutation relation between
the kinetic operator and mass operator is used. -/
theorem andreev_reflected_peirce_anomaly_cancels (D M : A) :
    comm
        (evenGrade (peirceSheetProj (A := A)) (!![D, 0; 0, D]))
        (genJ (peirceSheetProj (A := A)) (!![0, M; 0, 0]) (!![0, 0; M, 0])) +
      InfoGeometry.Physics.andreevSwap *
        comm
          (evenGrade (peirceSheetProj (A := A)) (!![D, 0; 0, D]))
          (genJ (peirceSheetProj (A := A)) (!![0, M; 0, 0]) (!![0, 0; M, 0])) *
        InfoGeometry.Physics.andreevSwap = 0 := by
  rw [andreev_reflect_peirce_interaction_defect]
  exact add_neg_cancel _

/-- The BdG operator-Higgs polynomial `H⁴ − H² + 1` is the existing
operator `cyclotomicSix` evaluated at the noncommutative square `H²`. -/
theorem operatorCyclotomicHiggs_eq_cyclotomicSix_of_square
    (H : InfoGeometry.Physics.BdGBlock A) :
    InfoGeometry.Physics.operatorCyclotomicHiggs H = cyclotomicSix (H * H) := by
  unfold InfoGeometry.Physics.operatorCyclotomicHiggs cyclotomicSix
  noncomm_ring

/-- For the massive matrix operator, the Higgs polynomial is the Peirce
operator cyclotomic polynomial evaluated on the full tetraktys square,
including the `comm (evenGrade D) J` defect. -/
theorem massiveBdG_operatorHiggs_is_Peirce_cyclotomicSix (D M : A) :
    InfoGeometry.Physics.operatorCyclotomicHiggs
        (InfoGeometry.Physics.massiveBdGHamiltonian D M) =
      cyclotomicSix
        (evenGrade (peirceSheetProj (A := A)) (!![D, 0; 0, D]) *
            evenGrade (peirceSheetProj (A := A)) (!![D, 0; 0, D]) +
          genV (peirceSheetProj (A := A)) (!![0, M; 0, 0]) (!![0, 0; M, 0]) +
          comm
            (evenGrade (peirceSheetProj (A := A)) (!![D, 0; 0, D]))
            (genJ (peirceSheetProj (A := A)) (!![0, M; 0, 0]) (!![0, 0; M, 0]))) := by
  rw [operatorCyclotomicHiggs_eq_cyclotomicSix_of_square,
    massiveBdG_square_is_Peirce_tetraktys_expansion]

section TetraktysAdjoints

variable {P : Matrix (Fin 2) (Fin 2) A}
variable (hPs : star P = P)
include hPs

/-- The two self-adjointness types of the tetraktys generators used by the
operator-valued interaction: `Φ` and `V` are self-adjoint, while `J` is
skew-adjoint. This is the existing Peirce star table on the matrix carrier. -/
theorem massive_pairing_tetraktys_adjoint_laws (M : A) (hM : star M = M) :
    star (genPhi P (massUp M) (massDown M)) =
        genPhi P (massUp M) (massDown M) ∧
    star (genJ P (massUp M) (massDown M)) =
        -genJ P (massUp M) (massDown M) ∧
    star (genV P (massUp M) (massDown M)) =
        genV P (massUp M) (massDown M) ∧
    star (genSig P (massUp M) (massDown M)) =
        genSig P (massUp M) (massDown M) := by
  have hUp : star (massUp M) = massDown M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [massUp, massDown, hM]
  rw [← hUp]
  exact ⟨star_genPhi hPs (massUp M), star_genJ hPs (massUp M),
    star_genV hPs (massUp M), star_genSig hPs (massUp M)⟩

end TetraktysAdjoints

section BdGMassSuperoperator

variable (M : A)

/-- For the actual operator-valued BdG pairing, the Peirce left-Dirac
superoperator squares to left multiplication by the operator mass `M²` on
both sheets. This is the `diracLeftPhi_square` theorem specialized to the
upper/lower interaction blocks of the massive matrix. -/
theorem massiveBdG_left_interaction_square (X : Matrix (Fin 2) (Fin 2) A) :
    diracLeftPhi (peirceSheetProj (A := A)) (massUp M) (massDown M)
        (diracLeftPhi (peirceSheetProj (A := A)) (massUp M) (massDown M) X) =
      (4 : ℤ) •
        (genV (peirceSheetProj (A := A)) (massUp M) (massDown M) * X) ∧
    diracRightPhi (peirceSheetProj (A := A)) (massUp M) (massDown M)
        (diracRightPhi (peirceSheetProj (A := A)) (massUp M) (massDown M) X) =
      -((4 : ℤ) •
        (X * genV (peirceSheetProj (A := A)) (massUp M) (massDown M))) ∧
    diracLeftJ (peirceSheetProj (A := A)) (massUp M) (massDown M)
        (diracLeftJ (peirceSheetProj (A := A)) (massUp M) (massDown M) X) =
      -((4 : ℤ) •
        (genV (peirceSheetProj (A := A)) (massUp M) (massDown M) * X)) ∧
    diracRightJ (peirceSheetProj (A := A)) (massUp M) (massDown M)
        (diracRightJ (peirceSheetProj (A := A)) (massUp M) (massDown M) X) =
      (4 : ℤ) •
        (X * genV (peirceSheetProj (A := A)) (massUp M) (massDown M)) ∧
    diracLeftPhi (peirceSheetProj (A := A)) (massUp M) (massDown M)
        (diracRightPhi (peirceSheetProj (A := A)) (massUp M) (massDown M) X) +
      diracRightPhi (peirceSheetProj (A := A)) (massUp M) (massDown M)
        (diracLeftPhi (peirceSheetProj (A := A)) (massUp M) (massDown M) X) = 0 ∧
    diracLeftJ (peirceSheetProj (A := A)) (massUp M) (massDown M)
        (diracRightJ (peirceSheetProj (A := A)) (massUp M) (massDown M) X) +
      diracRightJ (peirceSheetProj (A := A)) (massUp M) (massDown M)
        (diracLeftJ (peirceSheetProj (A := A)) (massUp M) (massDown M) X) = 0 ∧
    genV (peirceSheetProj (A := A)) (massUp M) (massDown M) =
      !![M * M, 0; 0, M * M] := by
  have hP := peirceSheetProj_idem (A := A)
  have hV : genV (peirceSheetProj (A := A)) (massUp M) (massDown M) =
      !![M * M, 0; 0, M * M] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [massUp, massDown, genV, anticomm, conePlus, coneMinus,
        peirceSheetProj, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two]
  exact ⟨diracLeftPhi_square hP (massUp M) (massDown M) X,
    diracRightPhi_square hP (massUp M) (massDown M) X,
    diracLeftJ_square hP (massUp M) (massDown M) X,
    diracRightJ_square hP (massUp M) (massDown M) X,
    diracLeftRightPhi_anticommute hP (massUp M) (massDown M) X,
    diracLeftRightJ_anticommute hP (massUp M) (massDown M) X,
    hV⟩

end BdGMassSuperoperator

/-- The operator-valued off-diagonal pairing is odd under the Peirce chiral
involution, whereas its quadratic self-interaction is even.  The last clause
identifies that even term on the actual matrix carrier as `M²` on both sheets.
This distinguishes breaking by the linear interaction from parity preservation
of its quadratic contribution. -/
theorem massive_pairing_chiral_parity_and_quadratic_self_interaction (M : A) :
    parityConj (peirceSheetProj (A := A))
      (genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M)) =
        -genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M) ∧
    parityConj (peirceSheetProj (A := A))
      (genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M) *
        genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M)) =
      genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M) *
        genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M) ∧
    genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M) *
      genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M) =
        !![M * M, 0; 0, M * M] := by
  have hP := peirceSheetProj_idem (A := A)
  rcases archetype_A27_grading_parities hP (massUp M) (massDown M) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hPhiParity, _⟩
  have hPhiSq := (archetype_A3_nilpotent_cones_and_tetraktys_table hP
    (massUp M) (massDown M)).2.2.1
  rcases massiveBdG_left_interaction_square (A := A) M (0 : Matrix (Fin 2) (Fin 2) A)
    with ⟨_, _, _, _, _, _, hV⟩
  refine ⟨hPhiParity, ?_, ?_⟩
  · calc
      parityConj (peirceSheetProj (A := A))
          (genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M) *
            genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M)) =
          parityConj (peirceSheetProj (A := A))
              (genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M)) *
            parityConj (peirceSheetProj (A := A))
              (genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M)) :=
        (parityConj_involutive_ring_action hP _ _).2.1
      _ = genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M) *
          genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M) := by
        rw [hPhiParity]
        noncomm_ring
  · rw [hPhiSq]
    exact hV

theorem massive_pairing_operator_cyclotomic_norm (M : A) :
    cyclotomicThree (genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M)) *
        cyclotomicSix (genPhi (peirceSheetProj (A := A)) (massUp M) (massDown M)) =
      genV (peirceSheetProj (A := A)) (massUp M) (massDown M) *
        genV (peirceSheetProj (A := A)) (massUp M) (massDown M) +
        genV (peirceSheetProj (A := A)) (massUp M) (massDown M) + 1 :=
  phi_cyclotomic_norm (peirceSheetProj_idem (A := A)) (massUp M) (massDown M)

section OrthogonalChannels

variable {B : Type*} [Ring B]

/-- Orthogonal channel hypotheses are stated on the actual upper and lower
Peirce operators. They remove only the mixed products; no products inside an
individual channel are commuted or discarded. -/
theorem two_channel_Peirce_additivity_of_cross_products_zero
    (P A₁ C₁ A₂ C₂ : B)
    (h₁₂ : conePlus P A₁ * coneMinus P C₂ = 0)
    (h₂₁ : conePlus P A₂ * coneMinus P C₁ = 0)
    (h₁₂' : coneMinus P C₁ * conePlus P A₂ = 0)
    (h₂₁' : coneMinus P C₂ * conePlus P A₁ = 0) :
    genPhi P (A₁ + A₂) (C₁ + C₂) =
        genPhi P A₁ C₁ + genPhi P A₂ C₂ ∧
    genV P (A₁ + A₂) (C₁ + C₂) =
        genV P A₁ C₁ + genV P A₂ C₂ ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P (A₁ + A₂) (C₁ + C₂) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P A₁ C₁ +
          InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P A₂ C₂ := by
  have hPlus : conePlus P (A₁ + A₂) = conePlus P A₁ + conePlus P A₂ := by
    unfold conePlus
    simp only [mul_add, add_mul]
  have hMinus : coneMinus P (C₁ + C₂) = coneMinus P C₁ + coneMinus P C₂ := by
    unfold coneMinus
    simp only [mul_add, add_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold genPhi
    rw [hPlus, hMinus]
    abel
  · unfold genV anticomm
    rw [hPlus, hMinus]
    simp only [add_mul, mul_add, h₁₂, h₂₁, h₁₂', h₂₁']
    abel
  · unfold InfoGeometry.OperatorAlgebra.PeirceSpine.genSig
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    rw [hPlus, hMinus]
    simp only [add_mul, mul_add, h₁₂, h₂₁, h₁₂', h₂₁']
    abel

/-- Without cross-channel orthogonality, the failure of additivity of the
Jordan mass is exactly the sum of the four ordered mixed products. This
records the obstruction instead of assuming it away. -/
theorem two_channel_mass_cross_defect
    (P A₁ C₁ A₂ C₂ : B) :
    genV P (A₁ + A₂) (C₁ + C₂) - (genV P A₁ C₁ + genV P A₂ C₂) =
      conePlus P A₁ * coneMinus P C₂ +
      conePlus P A₂ * coneMinus P C₁ +
      coneMinus P C₁ * conePlus P A₂ +
      coneMinus P C₂ * conePlus P A₁ := by
  have hPlus : conePlus P (A₁ + A₂) = conePlus P A₁ + conePlus P A₂ := by
    unfold conePlus
    simp only [mul_add, add_mul]
  have hMinus : coneMinus P (C₁ + C₂) = coneMinus P C₁ + coneMinus P C₂ := by
    unfold coneMinus
    simp only [mul_add, add_mul]
  unfold genV anticomm
  rw [hPlus, hMinus]
  noncomm_ring

end OrthogonalChannels

end InfoGeometry.OperatorAlgebra.PeirceBdGOperatorBridge
