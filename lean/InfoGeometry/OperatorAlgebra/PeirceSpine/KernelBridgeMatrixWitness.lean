/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.EndogenousKernelBridge
import Mathlib.Basic.Real.Star
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# An eight-dimensional real witness for the endogenous kernel bridge

All operators below inhabit the full native matrix ring `M₈(ℝ)`. The cut
and coupling do not commute. The diagonal perturbation preserves the two
arrows, while its corrected compressed cubic supplies an explicit residual
bridge. The constructed charge has a nonzero square equal to the upper
arrow in this example.

The seed algebra is contained in a proper elliptic centralizer. The example
therefore does not assert generation of the full matrix ring. A separate
off-shell perturbation retains nonzero degree-one and degree-minus-one
eigenvectors, refuting their claimed automatic disappearance off shell.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.KernelBridgeMatrixWitness

abbrev Op8 := Matrix (Fin 8) (Fin 8) ℝ

local notation "E" => (fun i j : Fin 8 => Matrix.single i j (1 : ℝ))

def P8 : Op8 := E 0 0 + E 1 1 + E 2 2 + E 3 3
def A8 : Op8 := E 0 6 + E 1 7 + E 6 0 + E 7 1
def D8 : Op8 := E 0 2 + E 1 3 + E 2 0 + E 3 1 + E 4 6 + E 5 7 + E 6 4 + E 7 5
def G8 : Op8 := E 2 4 + E 3 5 + E 4 2 + E 5 3
def elliptic8 : Op8 := E 0 1 - E 1 0 + E 2 3 - E 3 2 + E 4 5 - E 5 4 + E 6 7 - E 7 6
def Atilde8 : Op8 := A8 + D8

private theorem one_eq_units :
    (1 : Op8) = E 0 0 + E 1 1 + E 2 2 + E 3 3 + E 4 4 + E 5 5 + E 6 6 + E 7 7 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.single_apply, Matrix.one_apply]

private theorem complement_P8 : 1 - P8 = E 4 4 + E 5 5 + E 6 6 + E 7 7 := by
  rw [one_eq_units]
  unfold P8
  abel

macro "matrix_units" : tactic =>
  `(tactic| (norm_num [-Matrix.smul_single, mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg,
    smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, smul_sub,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne] <;> module))

theorem P8_idempotent : P8 * P8 = P8 := by
  unfold P8
  matrix_units

theorem seed8_star : star P8 = P8 ∧ star A8 = A8 ∧ star D8 = D8 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [P8, A8, D8, Matrix.star_eq_conjTranspose] <;> abel

theorem seed8_noncommuting : P8 * Atilde8 ≠ Atilde8 * P8 := by
  intro h
  have h06 := congrArg (fun X : Op8 => X 0 6) h
  norm_num [P8, Atilde8, A8, D8, mul_add, add_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne,
    Matrix.single_apply] at h06

theorem evenGrade_A8 : evenGrade P8 A8 = 0 := by
  rw [evenGrade, complement_P8]
  unfold P8 A8
  matrix_units

theorem evenGrade_D8 : evenGrade P8 D8 = D8 := by
  rw [evenGrade, complement_P8]
  unfold P8 D8
  matrix_units

theorem evenGrade_Atilde8 : evenGrade P8 Atilde8 = D8 := by
  rw [Atilde8, evenGrade_add, evenGrade_A8, evenGrade_D8, zero_add]

theorem upper_A8 : conePlus P8 A8 = E 0 6 + E 1 7 := by
  rw [conePlus, complement_P8]
  unfold P8 A8
  matrix_units

theorem lower_A8 : coneMinus P8 A8 = E 6 0 + E 7 1 := by
  rw [coneMinus, complement_P8]
  unfold P8 A8
  matrix_units

theorem arrows_Atilde8 :
    conePlus P8 Atilde8 = E 0 6 + E 1 7 ∧
      coneMinus P8 Atilde8 = E 6 0 + E 7 1 := by
  have hp := conePlus_evenGrade_shift P8_idempotent A8 D8
  have hm := coneMinus_evenGrade_shift P8_idempotent A8 D8
  rw [evenGrade_D8, upper_A8] at hp
  rw [evenGrade_D8, lower_A8] at hm
  exact ⟨hp, hm⟩

theorem cycles_Atilde8 :
    qgtPlus P8 Atilde8 Atilde8 = E 0 0 + E 1 1 ∧
      qgtMinus P8 Atilde8 Atilde8 = E 6 6 + E 7 7 := by
  simp only [qgtPlus, qgtMinus, arrows_Atilde8.1, arrows_Atilde8.2]
  constructor <;> matrix_units

theorem metric_Atilde8 :
    genV P8 Atilde8 Atilde8 = E 0 0 + E 1 1 + E 6 6 + E 7 7 := by
  change qgtPlus P8 Atilde8 Atilde8 + qgtMinus P8 Atilde8 Atilde8 = _
  rw [cycles_Atilde8.1, cycles_Atilde8.2]
  abel

theorem kernel_Atilde8 :
    1 - genV P8 Atilde8 Atilde8 = E 2 2 + E 3 3 + E 4 4 + E 5 5 := by
  rw [metric_Atilde8, one_eq_units]
  abel

theorem sigma_Atilde8 :
    genSig P8 Atilde8 Atilde8 = E 0 0 + E 1 1 - (E 6 6 + E 7 7) := by
  change qgtPlus P8 Atilde8 Atilde8 - qgtMinus P8 Atilde8 Atilde8 = _
  rw [cycles_Atilde8.1, cycles_Atilde8.2]

theorem metric_Atilde8_idempotent :
    genV P8 Atilde8 Atilde8 * genV P8 Atilde8 Atilde8 = genV P8 Atilde8 Atilde8 := by
  rw [metric_Atilde8]
  matrix_units

theorem D8_square : D8 * D8 = 1 := by
  rw [one_eq_units]
  unfold D8
  matrix_units

theorem D8_A8_D8 : D8 * A8 * D8 = G8 := by
  unfold D8 A8 G8
  matrix_units

theorem compressed_D8_cube :
    (1 - genV P8 Atilde8 Atilde8) * D8 ^ 3 * (1 - genV P8 Atilde8 Atilde8) = 0 := by
  have hc : D8 ^ 3 = D8 := by
    rw [pow_succ, pow_two, D8_square, one_mul]
  rw [hc, kernel_Atilde8]
  unfold D8
  matrix_units

/-- The supplied residual bridge is obtained from the two original seeds. -/
theorem endogenousKernelBridge_value : endogenousKernelBridge P8 Atilde8 = G8 := by
  rw [endogenousKernelBridge_eq_odd_sandwich P8_idempotent,
    evenGrade_Atilde8, kernel_Atilde8]
  simp only [genPhi, arrows_Atilde8.1, arrows_Atilde8.2]
  unfold D8 G8
  matrix_units

theorem G8_nonzero : G8 ≠ 0 := by
  intro h
  have h24 := congrArg (fun X : Op8 => X 2 4) h
  norm_num [G8, Matrix.single_apply] at h24

/-- The actual generic charge specializes to the four-step matrix expression. -/
theorem endogenousCharge_value :
    endogenousCharge P8 Atilde8 = E 0 4 + E 1 5 + E 4 6 + E 5 7 := by
  rw [endogenousCharge, cycles_Atilde8.1, cycles_Atilde8.2,
    evenGrade_Atilde8, endogenousKernelBridge_value, kernel_Atilde8]
  unfold D8 G8
  matrix_units

theorem endogenousCharge_square_upper :
    endogenousCharge P8 Atilde8 ^ 2 = conePlus P8 Atilde8 := by
  rw [endogenousCharge_value, arrows_Atilde8.1, pow_two]
  matrix_units

theorem endogenousCharge_square_nonzero : endogenousCharge P8 Atilde8 ^ 2 ≠ 0 := by
  rw [endogenousCharge_square_upper, arrows_Atilde8.1]
  intro h
  have h06 := congrArg (fun X : Op8 => X 0 6) h
  norm_num [Matrix.single_apply] at h06

theorem endogenousCharge_degree_one :
    comm (genSig P8 Atilde8 Atilde8) (endogenousCharge P8 Atilde8) =
      endogenousCharge P8 Atilde8 :=
  endogenousCharge_comm P8_idempotent Atilde8 metric_Atilde8_idempotent

theorem elliptic8_star : star elliptic8 = -elliptic8 := by
  norm_num [elliptic8, Matrix.star_eq_conjTranspose] <;> abel

theorem elliptic8_square : elliptic8 * elliptic8 = -1 := by
  rw [one_eq_units]
  unfold elliptic8
  matrix_units

theorem elliptic8_commutes :
    Commute elliptic8 P8 ∧ Commute elliptic8 A8 ∧ Commute elliptic8 D8 := by
  refine ⟨?_, ?_, ?_⟩ <;> change _ * _ = _ * _ <;>
    simp only [elliptic8, P8, A8, D8] <;> matrix_units

theorem elliptic8_commutes_Atilde8 : Commute elliptic8 Atilde8 :=
  elliptic8_commutes.2.1.add_right elliptic8_commutes.2.2

theorem ellipticArrowSum_selfAdjoint :
    star (ellipticArrowSum P8 Atilde8 elliptic8) = ellipticArrowSum P8 Atilde8 elliptic8 := by
  apply star_ellipticArrowSum seed8_star.1 _ elliptic8_star
  simp only [Atilde8, star_add, seed8_star.2.1, seed8_star.2.2]

theorem ellipticArrowSum_active_square :
    ellipticArrowSum P8 Atilde8 elliptic8 * ellipticArrowSum P8 Atilde8 elliptic8 =
      genV P8 Atilde8 Atilde8 :=
  ellipticArrowSum_square P8_idempotent elliptic8_commutes.1
    elliptic8_commutes_Atilde8 elliptic8_square

/-- The projected commutator is explicitly nonzero, with the submitted sign. -/
theorem elliptic_commutator_value :
    (1 - genV P8 Atilde8 Atilde8) *
        comm (elliptic8 * coneMinus P8 Atilde8) (endogenousCharge P8 Atilde8) *
        qgtPlus P8 Atilde8 Atilde8 = -(E 4 1 - E 5 0) := by
  rw [kernel_Atilde8, arrows_Atilde8.2, endogenousCharge_value, cycles_Atilde8.1]
  unfold comm elliptic8
  matrix_units

theorem elliptic_commutator_factorization :
    (1 - genV P8 Atilde8 Atilde8) *
        comm (elliptic8 * coneMinus P8 Atilde8) (endogenousCharge P8 Atilde8) *
        qgtPlus P8 Atilde8 Atilde8 =
      -(elliptic8 * (1 - genV P8 Atilde8 Atilde8) * D8 * coneMinus P8 Atilde8) := by
  rw [elliptic_commutator_value, kernel_Atilde8, arrows_Atilde8.2]
  unfold elliptic8 D8
  matrix_units

theorem elliptic_commutator_nonzero :
    (1 - genV P8 Atilde8 Atilde8) *
        comm (elliptic8 * coneMinus P8 Atilde8) (endogenousCharge P8 Atilde8) *
        qgtPlus P8 Atilde8 Atilde8 ≠ 0 := by
  rw [elliptic_commutator_value]
  intro h
  have h41 := congrArg (fun X : Op8 => X 4 1) h
  norm_num [Matrix.single_apply] at h41

/-- The traces count the active and residual coordinates in this finite witness. -/
theorem support8_traces :
    Matrix.trace (genV P8 Atilde8 Atilde8) = 4 ∧
      Matrix.trace (1 - genV P8 Atilde8 Atilde8) = 4 ∧
      Matrix.trace (P8 * (1 - genV P8 Atilde8 Atilde8)) = 2 := by
  rw [kernel_Atilde8, metric_Atilde8]
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [P8, mul_add, add_mul, Matrix.trace_add,
      Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]

/-- The integral on-shell Cayley element keeps the residual identity summand. -/
def U8 : Op8 := 1 - genV P8 Atilde8 Atilde8 + genJ P8 Atilde8 Atilde8

theorem U8_value :
    U8 = E 2 2 + E 3 3 + E 4 4 + E 5 5 + E 0 6 + E 1 7 - E 6 0 - E 7 1 := by
  rw [U8, kernel_Atilde8, genJ, arrows_Atilde8.1, arrows_Atilde8.2]
  abel

theorem U8_star_value :
    star U8 = E 2 2 + E 3 3 + E 4 4 + E 5 5 + E 6 0 + E 7 1 - E 0 6 - E 1 7 := by
  rw [U8_value]
  norm_num [Matrix.star_eq_conjTranspose] <;> abel

theorem U8_unitary_products : star U8 * U8 = 1 ∧ U8 * star U8 = 1 := by
  rw [U8_star_value, U8_value, one_eq_units]
  constructor <;> matrix_units

theorem U8_reverses_sigma :
    U8 * genSig P8 Atilde8 Atilde8 * star U8 = -genSig P8 Atilde8 Atilde8 := by
  rw [U8_star_value, U8_value, sigma_Atilde8]
  matrix_units

theorem U8_partial_flip :
    U8 * P8 * star U8 = qgtMinus P8 Atilde8 Atilde8 +
      P8 * (1 - genV P8 Atilde8 Atilde8) := by
  rw [U8_star_value, U8_value, cycles_Atilde8.2, kernel_Atilde8]
  unfold P8
  matrix_units

/-- Adding the particular missing odd bridge fills the residual support in this example. -/
theorem odd_perturbation_fills_support : genV P8 (A8 + G8) (A8 + G8) = 1 := by
  rw [genV, anticomm, conePlus, coneMinus, complement_P8, one_eq_units]
  unfold P8 A8 G8
  matrix_units

/-- Every generated operator commutes with the actual elliptic matrix. -/
theorem seed_ring_le_elliptic_centralizer :
    Subring.closure ({P8, Atilde8, elliptic8} : Set Op8) ≤
      Subring.centralizer {elliptic8} := by
  apply Subring.closure_le.mpr
  intro X hX
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rcases hX with rfl | rfl | rfl
  · exact Subring.mem_centralizer_iff.mpr (by
      intro Y hY
      obtain rfl := Set.mem_singleton_iff.mp hY
      exact elliptic8_commutes.1)
  · exact Subring.mem_centralizer_iff.mpr (by
      intro Y hY
      obtain rfl := Set.mem_singleton_iff.mp hY
      exact elliptic8_commutes_Atilde8)
  · exact Subring.mem_centralizer_iff.mpr (by
      intro Y hY
      obtain rfl := Set.mem_singleton_iff.mp hY
      exact Commute.refl elliptic8)

theorem matrix_unit_not_in_elliptic_centralizer :
    E 0 0 ∉ Subring.centralizer ({elliptic8} : Set Op8) := by
  intro h
  have hc := Subring.mem_centralizer_iff.mp h elliptic8 (by simp)
  have h01 := congrArg (fun X : Op8 => X 0 1) hc
  norm_num [elliptic8, mul_add, add_mul, mul_sub, sub_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne,
    Matrix.single_apply] at h01

theorem seed_ring_ne_top : Subring.closure ({P8, Atilde8, elliptic8} : Set Op8) ≠ ⊤ := by
  intro h
  have hm : E 0 0 ∈ Subring.closure ({P8, Atilde8, elliptic8} : Set Op8) := by
    rw [h]
    trivial
  exact matrix_unit_not_in_elliptic_centralizer (seed_ring_le_elliptic_centralizer hm)

/-- A single upper matrix unit is an actual nonzero element of degree two. -/
theorem upper_matrix_unit_degree_two :
    comm (genSig P8 Atilde8 Atilde8) (E 0 6) = (2 : ℤ) • (E 0 6) := by
  rw [sigma_Atilde8]
  unfold comm
  matrix_units

theorem upper_matrix_unit_nonzero : (E 0 6 : Op8) ≠ 0 := by
  intro h
  have h06 := congrArg (fun X : Op8 => X 0 6) h
  norm_num [Matrix.single_apply] at h06

/-- This upper matrix unit does not commute with the elliptic operator. -/
theorem upper_matrix_unit_not_in_elliptic_centralizer :
    E 0 6 ∉ Subring.centralizer ({elliptic8} : Set Op8) := by
  intro h
  have hc := Subring.mem_centralizer_iff.mp h elliptic8 (by simp)
  have h16 := congrArg (fun X : Op8 => X 1 6) hc
  norm_num [elliptic8, mul_add, add_mul, mul_sub, sub_mul,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne,
    Matrix.single_apply] at h16

/-- The seed-generated subring misses a nonzero element of the upper extreme grade. -/
theorem upper_matrix_unit_not_in_seed_ring :
    E 0 6 ∉ Subring.closure ({P8, Atilde8, elliptic8} : Set Op8) := by
  intro h
  exact upper_matrix_unit_not_in_elliptic_centralizer (seed_ring_le_elliptic_centralizer h)

/-- The nonzero square established above does not make these seeds generate
the whole degree-two corner. -/
theorem degree_two_not_contained_in_seed_ring :
    ¬ ∀ X : Op8, comm (genSig P8 Atilde8 Atilde8) X = (2 : ℤ) • X →
      X ∈ Subring.closure ({P8, Atilde8, elliptic8} : Set Op8) := by
  intro h
  exact upper_matrix_unit_not_in_seed_ring (h (E 0 6) upper_matrix_unit_degree_two)

noncomputable def offShell8 : Op8 := (3 / 5 : ℝ) • A8 + (4 / 5 : ℝ) • G8

theorem offShell8_selfAdjoint : star offShell8 = offShell8 := by
  norm_num [offShell8, A8, G8, Matrix.star_eq_conjTranspose] <;> module

theorem offShell8_commutes_elliptic : Commute elliptic8 offShell8 := by
  change elliptic8 * offShell8 = offShell8 * elliptic8
  unfold elliptic8 offShell8 A8 G8
  matrix_units

theorem offShell8_metric :
    genV P8 offShell8 offShell8 =
      (9 / 25 : ℝ) • (E 0 0 + E 1 1 + E 6 6 + E 7 7) +
        (16 / 25 : ℝ) • (E 2 2 + E 3 3 + E 4 4 + E 5 5) := by
  rw [genV, anticomm, conePlus, coneMinus, complement_P8]
  unfold offShell8 A8 G8 P8
  matrix_units

theorem offShell8_sigma :
    genSig P8 offShell8 offShell8 =
      (9 / 25 : ℝ) • (E 0 0 + E 1 1 - E 6 6 - E 7 7) +
        (16 / 25 : ℝ) • (E 2 2 + E 3 3 - E 4 4 - E 5 5) := by
  rw [genSig, comm, conePlus, coneMinus, complement_P8]
  unfold offShell8 A8 G8 P8
  matrix_units

theorem offShell8_defect :
    genV P8 offShell8 offShell8 * genV P8 offShell8 offShell8 - genV P8 offShell8 offShell8 =
      (-144 / 625 : ℝ) • (1 : Op8) := by
  rw [offShell8_metric, one_eq_units]
  matrix_units

theorem offShell8_metric_not_idempotent :
    genV P8 offShell8 offShell8 * genV P8 offShell8 offShell8 ≠ genV P8 offShell8 offShell8 := by
  intro h
  have hd := offShell8_defect
  rw [h, sub_self] at hd
  have h00 := congrArg (fun X : Op8 => X 0 0) hd
  norm_num at h00

/-- Nonzero eigenvectors of both odd degrees survive this explicit off-shell defect. -/
theorem offShell8_odd_eigenvectors :
    comm (genSig P8 offShell8 offShell8) (E 0 4) = E 0 4 ∧
      comm (genSig P8 offShell8 offShell8) (E 4 0) = -(E 4 0) ∧
      (E 0 4 : Op8) ≠ 0 ∧ (E 4 0 : Op8) ≠ 0 := by
  rw [offShell8_sigma]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold comm
    matrix_units
  · unfold comm
    matrix_units
  · intro h
    have h04 := congrArg (fun X : Op8 => X 0 4) h
    norm_num [Matrix.single_apply] at h04
  · intro h
    have h40 := congrArg (fun X : Op8 => X 4 0) h
    norm_num [Matrix.single_apply] at h40

/-- Multiplication by a supported lower arrow changes this degree-one charge to degree minus one. -/
theorem lower_times_charge_value :
    coneMinus P8 Atilde8 * endogenousCharge P8 Atilde8 = E 6 4 + E 7 5 := by
  rw [arrows_Atilde8.2, endogenousCharge_value]
  matrix_units

/-- The multiplier lies in the metric centralizer, even though it changes the charge degree. -/
theorem lower_commutes_metric : Commute (genV P8 Atilde8 Atilde8) (coneMinus P8 Atilde8) :=
  genV_commute_of_mem_generated P8_idempotent Atilde8 Atilde8
    (coneMinus_mem_generatedPeirceRing P8 Atilde8 Atilde8)

theorem lower_times_charge_degree_minus_one :
    comm (genSig P8 Atilde8 Atilde8) (coneMinus P8 Atilde8 * endogenousCharge P8 Atilde8) =
      -(coneMinus P8 Atilde8 * endogenousCharge P8 Atilde8) := by
  rw [lower_times_charge_value, sigma_Atilde8]
  unfold comm
  matrix_units

theorem lower_times_charge_not_degree_one :
    comm (genSig P8 Atilde8 Atilde8) (coneMinus P8 Atilde8 * endogenousCharge P8 Atilde8) ≠
      coneMinus P8 Atilde8 * endogenousCharge P8 Atilde8 := by
  rw [lower_times_charge_degree_minus_one, lower_times_charge_value]
  intro h
  have h64 := congrArg (fun X : Op8 => X 6 4) h
  norm_num [Matrix.single_apply] at h64

end InfoGeometry.OperatorAlgebra.PeirceSpine.KernelBridgeMatrixWitness
