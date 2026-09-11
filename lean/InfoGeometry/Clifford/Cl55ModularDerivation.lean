import InfoGeometry.Clifford.Cl55QuadraticSpinAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Clifford55
import InfoGeometry.OperatorAlgebra.FiveGradeActionPreservation

/-!
# The `Cl(5,5)` modular derivation readout

The generic inner-derivation laws are owned by
`InfoGeometry.Clifford.Cl55QuadraticSpinAction`.  This file supplies the
concrete `Cl55` names used by the modular/Hestenes layer and proves their
readout identities by reuse of that owner.  The carrier is the native
noncommutative Clifford algebra; no scalar or diagonal model is introduced.
-/

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Clifford
open InfoGeometry.OperatorAlgebra

abbrev cl55Commutator (K x : Cl55) : Cl55 :=
  commutatorAction K x

abbrev cl55ModularDerivation (K : Cl55) : Cl55 →ₗ[ℝ] Cl55 :=
  commutatorActionLinear (R := ℝ) K

@[simp] theorem cl55Commutator_apply (K x : Cl55) :
    cl55Commutator K x = K * x - x * K := by
  rfl

theorem cl55Commutator_leibniz (K x y : Cl55) :
    cl55Commutator K (x * y) =
      cl55Commutator K x * y + x * cl55Commutator K y := by
  exact commutatorAction_mul K x y

theorem cl55Commutator_commutator (K L x : Cl55) :
    cl55Commutator K (cl55Commutator L x) -
        cl55Commutator L (cl55Commutator K x) =
      cl55Commutator (K * L - L * K) x := by
  exact commutatorAction_commutator K L x

theorem cl55Commutator_one (K : Cl55) :
    cl55Commutator K 1 = 0 := by
  simp [cl55Commutator]

theorem cl55Commutator_of_commute (K x : Cl55) (h : K * x = x * K) :
    cl55Commutator K x = 0 := by
  simp [cl55Commutator, h]

theorem cl55Commutator_eq_two_left_mul_of_anticommute
    (K x : Cl55) (h : K * x = -(x * K)) :
    cl55Commutator K x = (2 : Cl55) * K * x := by
  unfold cl55Commutator commutatorAction
  have hk : x * K = -(K * x) := by
    rw [h]
    simp
  calc
    K * x - x * K = K * x - (-(K * x)) := by rw [hk]
    _ = K * x + K * x := by rw [sub_neg_eq_add]
    _ = (2 : Cl55) * K * x := by noncomm_ring

theorem cl55Commutator_eq_two_right_mul_of_anticommute
    (K x : Cl55) (h : K * x = -(x * K)) :
    cl55Commutator K x = -(2 : Cl55) * x * K := by
  unfold cl55Commutator commutatorAction
  calc
    K * x - x * K = -(x * K) - x * K := by rw [h]
    _ = -(x * K) + -(x * K) := by simp only [sub_eq_add_neg]
    _ = -(2 : Cl55) * x * K := by noncomm_ring

@[simp] theorem cl55ModularDerivation_apply (K x : Cl55) :
    cl55ModularDerivation K x = K * x - x * K := by
  rfl

theorem cl55ModularDerivation_odd_generator
    (K x : Cl55) (h : K * x = -(x * K)) :
    cl55ModularDerivation K x = (2 : Cl55) * K * x := by
  exact cl55Commutator_eq_two_left_mul_of_anticommute K x h

theorem cl55ModularDerivation_leibniz (K x y : Cl55) :
    cl55ModularDerivation K (x * y) =
      cl55ModularDerivation K x * y + x * cl55ModularDerivation K y := by
  exact commutatorAction_mul K x y

theorem cl55ModularDerivation_bracket (K L x : Cl55) :
    cl55ModularDerivation K (cl55ModularDerivation L x) -
        cl55ModularDerivation L (cl55ModularDerivation K x) =
      cl55ModularDerivation (K * L - L * K) x := by
  exact commutatorAction_commutator K L x

theorem cl55ModularDerivation_eq_lieAlgebra_ad (K : Cl55) :
    cl55ModularDerivation K = LieAlgebra.ad ℝ Cl55 K := by
  exact commutatorActionLinear_eq_lieAlgebra_ad K

theorem cl55ModularDerivation_preserves_grade
    (K X : Cl55) (k : ℤ)
    (hK : K ∈ gradeSubmodule numberOperator55 0)
    (hX : X ∈ gradeSubmodule numberOperator55 k) :
    cl55ModularDerivation K X ∈ gradeSubmodule numberOperator55 k := by
  change HasOperatorGrade numberOperator55
    (K * X - X * K) k
  exact InfoGeometry.OperatorAlgebra.grade_zero_commutator_preserves
    (N := numberOperator55) (K := K) (X := X) hK hX

theorem cl55ModularDerivation_mapsToGrade
    (K : Cl55)
    (hK : K ∈ gradeSubmodule numberOperator55 0) :
    InfoGeometry.OperatorAlgebra.MapsToGradeBetween
      (fun j : ℤ => (gradeSubmodule numberOperator55 j : Set Cl55))
      (fun j : ℤ => (gradeSubmodule numberOperator55 j : Set Cl55))
      (fun _ : Unit => cl55ModularDerivation K)
      (fun _ j => j) := by
  intro _ j X hX
  exact cl55ModularDerivation_preserves_grade K X j hK hX

theorem cl55ModularDerivation_preserves_grade_family
    (K : Cl55) (hK : K ∈ gradeSubmodule numberOperator55 0) :
    InfoGeometry.OperatorAlgebra.PreservesGrade
      (fun j : ℤ => (gradeSubmodule numberOperator55 j : Set Cl55))
      (fun _ : Unit => cl55ModularDerivation K) := by
  intro _ j X hX
  exact cl55ModularDerivation_preserves_grade K X j hK hX

theorem cl55GradeZeroModular_mapsToGrade
    (N : Cl55) :
    InfoGeometry.OperatorAlgebra.MapsToGrade
      (fun j : ℤ => (gradeSubmodule N j : Set Cl55))
      (fun K : {X : Cl55 // X ∈ gradeSubmodule N 0} =>
        fun X => cl55ModularDerivation K.1 X)
      (fun _ j => j) := by
  exact InfoGeometry.OperatorAlgebra.grade_zero_commutator_mapsToGrade N

end InfoGeometry.Clifford.Clifford55
