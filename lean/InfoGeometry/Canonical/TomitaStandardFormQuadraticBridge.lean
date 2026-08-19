import InfoGeometry.Canonical.TomitaTakesakiRealStandardForm
import InfoGeometry.OperatorAlgebra.RealCommutantClosure

/-!
# Conditional left-right quadratic action in a real standard form

The existing standard-form owner supplies the `J`-conjugation transport from
the left carrier to the right carrier. This file records the corresponding
left-right quadratic product and its commutator readout. It does not identify
the right carrier with a von Neumann commutant and does not assert positivity.
-/

noncomputable section

namespace InfoGeometry.Canonical.TomitaStandardFormQuadraticBridge

open InfoGeometry.Canonical.TomitaTakesakiRealStandardForm
open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealCommutantClosure

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => DoubledSpace E →L[ℝ] DoubledSpace E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance

def leftRightQuadratic
    (S : RealStandardForm (E := E)) (A : EndH) : EndH :=
  A * jConjugate S.J A

def IsMutualCommutantStandardForm
    (S : RealStandardForm (E := E)) : Prop :=
  S.rightAlgebra ⊆ realCommutant S.leftAlgebra ∧
    S.leftAlgebra ⊆ realCommutant S.rightAlgebra

theorem leftRightQuadratic_conjugate_mem_right
    (S : RealStandardForm (E := E))
    {A : EndH} (hA : A ∈ S.leftAlgebra) :
    jConjugate S.J A ∈ S.rightAlgebra :=
  S.J_left_to_right hA

theorem jConjugate_involutive
    (S : RealStandardForm (E := E)) (A : EndH) :
    jConjugate S.J (jConjugate S.J A) = A := by
  unfold jConjugate
  calc
    S.J * (S.J * A * S.J) * S.J =
        (S.J * S.J) * A * (S.J * S.J) := by
          noncomm_ring
    _ = A := by rw [S.J_sq]; simp

theorem jConjugate_mul
    (S : RealStandardForm (E := E)) (A B : EndH) :
    jConjugate S.J (A * B) =
      jConjugate S.J A * jConjugate S.J B := by
  unfold jConjugate
  calc
    S.J * (A * B) * S.J =
        S.J * A * (S.J * S.J) * B * S.J := by
          rw [S.J_sq]
          noncomm_ring
    _ = (S.J * A * S.J) * (S.J * B * S.J) := by
          noncomm_ring

theorem leftRightQuadratic_jConjugate
    (S : RealStandardForm (E := E)) (A : EndH) :
    jConjugate S.J (leftRightQuadratic S A) =
      jConjugate S.J A * A := by
  rw [leftRightQuadratic, jConjugate_mul, jConjugate_involutive]

theorem jConjugate_mem_left_iff
    (S : RealStandardForm (E := E)) (A : EndH) :
    jConjugate S.J A ∈ S.leftAlgebra ↔ A ∈ S.rightAlgebra := by
  constructor
  · intro hA
    have hA' := S.J_left_to_right hA
    rw [jConjugate_involutive S A] at hA'
    exact hA'
  · intro hA
    exact S.J_right_to_left hA

theorem leftRightQuadratic_commutator_zero
    (S : RealStandardForm (E := E))
    {A : EndH}
    (hA : A ∈ S.leftAlgebra)
    (hComm : jConjugate S.J A ∈ realCommutant S.leftAlgebra) :
    leftRightQuadratic S A - jConjugate S.J A * A = 0 := by
  unfold leftRightQuadratic
  have h := realCommutant_commutator_eq_zero S.leftAlgebra hComm hA
  calc
    A * jConjugate S.J A - jConjugate S.J A * A =
        -(jConjugate S.J A * A - A * jConjugate S.J A) := by abel
    _ = -0 := by rw [h]
    _ = 0 := by simp

theorem leftRightQuadratic_eq_reverse_of_commutant
    (S : RealStandardForm (E := E))
    {A : EndH}
    (hA : A ∈ S.leftAlgebra)
    (hComm : jConjugate S.J A ∈ realCommutant S.leftAlgebra) :
    leftRightQuadratic S A = jConjugate S.J A * A := by
  exact sub_eq_zero.mp (leftRightQuadratic_commutator_zero S hA hComm)

theorem leftRightQuadratic_commutator_zero_of_mutual_commutant
    (S : RealStandardForm (E := E))
    (hMutual : IsMutualCommutantStandardForm S)
    {A : EndH} (hA : A ∈ S.leftAlgebra) :
    leftRightQuadratic S A - jConjugate S.J A * A = 0 := by
  exact leftRightQuadratic_commutator_zero S hA
    (hMutual.1 (leftRightQuadratic_conjugate_mem_right S hA))

end InfoGeometry.Canonical.TomitaStandardFormQuadraticBridge
