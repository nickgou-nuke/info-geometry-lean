/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import InfoGeometry.Clifford.OperatorValuedJonesWalsh
import InfoGeometry.OperatorAlgebra.KnutsenGaborOperatorAlgebra

open Matrix

namespace GrandUnifiedNoncommutativeOperatorSynthesis

/-!
## Shared Infrastructure: Matrix2 Infrastructure
-/

section Matrix2Infrastructure

variable {A : Type*} [Ring A]

def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma of2_00 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 0 = a := rfl
@[simp] lemma of2_01 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 1 = b := rfl
@[simp] lemma of2_10 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 0 = c := rfl
@[simp] lemma of2_11 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 1 = d := rfl

@[simp] lemma matrix_add_entry (M N : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    (M + N) i j = M i j + N i j := rfl

@[simp] lemma matrix_sub_entry (M N : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    (M - N) i j = M i j - N i j := rfl

def sigmaOp    : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![1, 0]]
def omegaOp    : Matrix (Fin 2) (Fin 2) A := ![![0, -1], ![1, 0]]
def gammaOneOp : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, -1]]
def P_plus  : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, 0]]
def P_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![0, 1]]
def F_plus  : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![0, 0]]
def F_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![1, 0]]

def fiberEmbed (x : A) : Matrix (Fin 2) (Fin 2) A := ![![x, 0], ![0, x]]
def kleinTwist (x : A) : Matrix (Fin 2) (Fin 2) A := ![![x, 0], ![0, -x]]

/-- The standard off-diagonal matrix units in the operator matrix algebra. -/
def matrixUnit01 : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![0, 0]]
def matrixUnit10 : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![1, 0]]

lemma ext_fin2 {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- The operator matrix algebra `M₂(A)` is noncommutative whenever its
coefficient ring is nontrivial. -/
theorem matrix_fin2_noncommutative [Nontrivial A] :
    ∃ M N : Matrix (Fin 2) (Fin 2) A, M * N ≠ N * M := by
  refine ⟨matrixUnit01 (A := A), matrixUnit10 (A := A), ?_⟩
  have hleft : matrixUnit01 (A := A) * matrixUnit10 (A := A) = P_plus := by
    apply ext_fin2
    · rw [mul2_00]; simp [matrixUnit01, matrixUnit10, P_plus]
    · rw [mul2_01]; simp [matrixUnit01, matrixUnit10, P_plus]
    · rw [mul2_10]; simp [matrixUnit01, matrixUnit10, P_plus]
    · rw [mul2_11]; simp [matrixUnit01, matrixUnit10, P_plus]
  have hright : matrixUnit10 (A := A) * matrixUnit01 (A := A) = P_minus := by
    apply ext_fin2
    · rw [mul2_00]; simp [matrixUnit01, matrixUnit10, P_minus]
    · rw [mul2_01]; simp [matrixUnit01, matrixUnit10, P_minus]
    · rw [mul2_10]; simp [matrixUnit01, matrixUnit10, P_minus]
    · rw [mul2_11]; simp [matrixUnit01, matrixUnit10, P_minus]
  rw [hleft, hright]
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  have h10 : (1 : A) = 0 := by simpa [P_plus, P_minus] using h00
  exact one_ne_zero h10

theorem coefficient_matrix_fin2_noncommutative [Ring B] [Nontrivial B] :
    ∃ M N : Matrix (Fin 2) (Fin 2) B, M * N ≠ N * M :=
  matrix_fin2_noncommutative (A := B)

theorem cl11_and_witt_car_relations :
    (sigmaOp : Matrix (Fin 2) (Fin 2) A) * sigmaOp = 1 ∧
    (omegaOp : Matrix (Fin 2) (Fin 2) A) * omegaOp = -1 ∧
    (sigmaOp : Matrix (Fin 2) (Fin 2) A) * omegaOp = gammaOneOp ∧
    anticomm (sigmaOp : Matrix (Fin 2) (Fin 2) A) omegaOp = 0 ∧
    (F_plus : Matrix (Fin 2) (Fin 2) A) * F_plus = 0 ∧
    (F_minus : Matrix (Fin 2) (Fin 2) A) * F_minus = 0 ∧
    anticomm (F_plus : Matrix (Fin 2) (Fin 2) A) F_minus = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2
    · rw [mul2_00]; simp [sigmaOp]
    · rw [mul2_01]; simp [sigmaOp]
    · rw [mul2_10]; simp [sigmaOp]
    · rw [mul2_11]; simp [sigmaOp]
  · apply ext_fin2
    · rw [mul2_00]; simp [omegaOp]
    · rw [mul2_01]; simp [omegaOp]
    · rw [mul2_10]; simp [omegaOp]
    · rw [mul2_11]; simp [omegaOp]
  · apply ext_fin2
    · rw [mul2_00]; simp [sigmaOp, omegaOp, gammaOneOp]
    · rw [mul2_01]; simp [sigmaOp, omegaOp, gammaOneOp]
    · rw [mul2_10]; simp [sigmaOp, omegaOp, gammaOneOp]
    · rw [mul2_11]; simp [sigmaOp, omegaOp, gammaOneOp]
  · change (sigmaOp * omegaOp + omegaOp * sigmaOp : Matrix (Fin 2) (Fin 2) A) = 0
    apply ext_fin2
    · rw [Matrix.add_apply, mul2_00, mul2_00]; simp [sigmaOp, omegaOp]
    · rw [Matrix.add_apply, mul2_01, mul2_01]; simp [sigmaOp, omegaOp]
    · rw [Matrix.add_apply, mul2_10, mul2_10]; simp [sigmaOp, omegaOp]
    · rw [Matrix.add_apply, mul2_11, mul2_11]; simp [sigmaOp, omegaOp]
  · apply ext_fin2
    · rw [mul2_00]; simp [F_plus]
    · rw [mul2_01]; simp [F_plus]
    · rw [mul2_10]; simp [F_plus]
    · rw [mul2_11]; simp [F_plus]
  · apply ext_fin2
    · rw [mul2_00]; simp [F_minus]
    · rw [mul2_01]; simp [F_minus]
    · rw [mul2_10]; simp [F_minus]
    · rw [mul2_11]; simp [F_minus]
  · change (F_plus * F_minus + F_minus * F_plus : Matrix (Fin 2) (Fin 2) A) = 1
    apply ext_fin2
    · rw [Matrix.add_apply, mul2_00, mul2_00]; simp [F_plus, F_minus]
    · rw [Matrix.add_apply, mul2_01, mul2_01]; simp [F_plus, F_minus]
    · rw [Matrix.add_apply, mul2_10, mul2_10]; simp [F_plus, F_minus]
    · rw [Matrix.add_apply, mul2_11, mul2_11]; simp [F_plus, F_minus]

theorem brauer_weyl_periodicity_step {e₁ e₂ s₁ s₂ : A}
    (he₁ : e₁ * e₁ = s₁) (he₂ : e₂ * e₂ = s₂) (h_anti : anticomm e₁ e₂ = 0) :
    kleinTwist e₁ * kleinTwist e₁ = fiberEmbed s₁ ∧
    kleinTwist e₂ * kleinTwist e₂ = fiberEmbed s₂ ∧
    anticomm (kleinTwist e₁) (sigmaOp : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    anticomm (kleinTwist e₂) (sigmaOp : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    anticomm (kleinTwist e₁) (omegaOp : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    anticomm (kleinTwist e₂) (omegaOp : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    anticomm (kleinTwist e₁) (kleinTwist e₂) = 0 := by
  have h0 : ∀ x y : A, kleinTwist x * kleinTwist y = fiberEmbed (x * y) := fun x y => by
    apply ext_fin2
    · rw [mul2_00]; simp [kleinTwist, fiberEmbed]
    · rw [mul2_01]; simp [kleinTwist, fiberEmbed]
    · rw [mul2_10]; simp [kleinTwist, fiberEmbed]
    · rw [mul2_11]; simp [kleinTwist, fiberEmbed]

  have hA : anticomm (kleinTwist e₁) (kleinTwist e₂) = fiberEmbed (anticomm e₁ e₂) := by
    change (kleinTwist e₁ * kleinTwist e₂ + kleinTwist e₂ * kleinTwist e₁ : Matrix (Fin 2) (Fin 2) A) = fiberEmbed (e₁ * e₂ + e₂ * e₁)
    apply ext_fin2
    · rw [Matrix.add_apply, mul2_00, mul2_00]; simp [kleinTwist, fiberEmbed]
    · rw [Matrix.add_apply, mul2_01, mul2_01]; simp [kleinTwist, fiberEmbed]
    · rw [Matrix.add_apply, mul2_10, mul2_10]; simp [kleinTwist, fiberEmbed]
    · rw [Matrix.add_apply, mul2_11, mul2_11]; simp [kleinTwist, fiberEmbed]

  refine ⟨by rw [h0, he₁], by rw [h0, he₂], ?_, ?_, ?_, ?_, ?_⟩
  · change (kleinTwist e₁ * sigmaOp + sigmaOp * kleinTwist e₁ : Matrix (Fin 2) (Fin 2) A) = 0
    apply ext_fin2
    · rw [Matrix.add_apply, mul2_00, mul2_00]; simp [kleinTwist, sigmaOp]
    · rw [Matrix.add_apply, mul2_01, mul2_01]; simp [kleinTwist, sigmaOp]
    · rw [Matrix.add_apply, mul2_10, mul2_10]; simp [kleinTwist, sigmaOp]
    · rw [Matrix.add_apply, mul2_11, mul2_11]; simp [kleinTwist, sigmaOp]
  · change (kleinTwist e₂ * sigmaOp + sigmaOp * kleinTwist e₂ : Matrix (Fin 2) (Fin 2) A) = 0
    apply ext_fin2
    · rw [Matrix.add_apply, mul2_00, mul2_00]; simp [kleinTwist, sigmaOp]
    · rw [Matrix.add_apply, mul2_01, mul2_01]; simp [kleinTwist, sigmaOp]
    · rw [Matrix.add_apply, mul2_10, mul2_10]; simp [kleinTwist, sigmaOp]
    · rw [Matrix.add_apply, mul2_11, mul2_11]; simp [kleinTwist, sigmaOp]
  · change (kleinTwist e₁ * omegaOp + omegaOp * kleinTwist e₁ : Matrix (Fin 2) (Fin 2) A) = 0
    apply ext_fin2
    · rw [Matrix.add_apply, mul2_00, mul2_00]; simp [kleinTwist, omegaOp]
    · rw [Matrix.add_apply, mul2_01, mul2_01]; simp [kleinTwist, omegaOp]
    · rw [Matrix.add_apply, mul2_10, mul2_10]; simp [kleinTwist, omegaOp]
    · rw [Matrix.add_apply, mul2_11, mul2_11]; simp [kleinTwist, omegaOp]
  · change (kleinTwist e₂ * omegaOp + omegaOp * kleinTwist e₂ : Matrix (Fin 2) (Fin 2) A) = 0
    apply ext_fin2
    · rw [Matrix.add_apply, mul2_00, mul2_00]; simp [kleinTwist, omegaOp]
    · rw [Matrix.add_apply, mul2_01, mul2_01]; simp [kleinTwist, omegaOp]
    · rw [Matrix.add_apply, mul2_10, mul2_10]; simp [kleinTwist, omegaOp]
    · rw [Matrix.add_apply, mul2_11, mul2_11]; simp [kleinTwist, omegaOp]
  · rw [hA, h_anti]; apply ext_fin2
    · simp [fiberEmbed]
    · simp [fiberEmbed]
    · simp [fiberEmbed]
    · simp [fiberEmbed]

end Matrix2Infrastructure

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-- The first nested Clifford generator is the outer `Cl(1,1)` skew generator. -/
def E₁ {B : Type*} [Ring B] : NestedMat B :=
  omegaOp (A := Matrix (Fin 2) (Fin 2) B)

/-- The second generator is the Klein twist of the inner skew generator. -/
def E₂ {B : Type*} [Ring B] : NestedMat B :=
  kleinTwist (A := Matrix (Fin 2) (Fin 2) B) (omegaOp (A := B))

def E₃ {B : Type*} [Ring B] : NestedMat B := E₁ * E₂

/-- The nested operator generators form the quaternion relations over any ring. -/
theorem nested_quaternion_lie_relations {B : Type*} [Ring B] :
    (E₁ : NestedMat B) * E₁ = -1 ∧
    (E₂ : NestedMat B) * E₂ = -1 ∧
    (E₃ : NestedMat B) * E₃ = -1 ∧
    anticomm (E₁ : NestedMat B) E₂ = 0 ∧
    ⁅(E₁ : NestedMat B), E₂⁆ = 2 • E₃ (B := B) ∧
    ⁅(E₂ : NestedMat B), E₃⁆ = 2 • E₁ (B := B) ∧
    ⁅(E₃ : NestedMat B), E₁⁆ = 2 • E₂ (B := B) := by
  let A := Matrix (Fin 2) (Fin 2) B
  have hbase := cl11_and_witt_car_relations (A := A)
  have hinner := cl11_and_witt_car_relations (A := B)
  have hstep := brauer_weyl_periodicity_step (A := A)
    (e₁ := (0 : A)) (e₂ := omegaOp (A := B)) (s₁ := (0 : A)) (s₂ := -1)
    (by simp) hinner.2.1 (by simp [anticomm])
  have h₁ : (E₁ : NestedMat B) * E₁ = -1 := by
    simpa [E₁] using hbase.2.1
  have hFiberNeg :
      fiberEmbed (A := Matrix (Fin 2) (Fin 2) B) (-1) = (-1 : NestedMat B) := by
    ext i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [fiberEmbed, Matrix.one_apply, Matrix.neg_apply] <;> abel
  have h₂ : (E₂ : NestedMat B) * E₂ = -1 := by
    dsimp [E₂]
    rw [hstep.2.1]
    exact hFiberNeg
  have hanti : anticomm (E₁ : NestedMat B) E₂ = 0 := by
    -- The sixth component is the anticommutator of the twisted inner
    -- generator with the outer skew generator.  The final component instead
    -- concerns the (zero) first input used to obtain the square calculation.
    simpa [E₁, E₂, anticomm, add_comm] using hstep.2.2.2.2.2.1
  have h21 : E₂ (B := B) * E₁ (B := B) =
      -(E₁ (B := B) * E₂ (B := B)) := by
    dsimp [anticomm] at hanti
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hanti)
  have h₃ : (E₃ : NestedMat B) * E₃ = -1 := by
    calc
      E₃ (B := B) * E₃ = E₁ (B := B) *
          (E₂ (B := B) * E₁ (B := B)) * E₂ (B := B) := by
        dsimp [E₃]
        noncomm_ring
      _ = E₁ (B := B) * (-(E₁ (B := B) * E₂ (B := B))) * E₂ (B := B) := by
        rw [h21]
      _ = -((E₁ (B := B) * E₁ (B := B)) *
          (E₂ (B := B) * E₂ (B := B))) := by noncomm_ring
      _ = -((-1) * (-1)) := by rw [h₁, h₂]
      _ = -1 := by noncomm_ring
  refine ⟨h₁, h₂, h₃, hanti, ?_, ?_, ?_⟩
  · rw [Ring.lie_def, h21]
    dsimp [E₃]
    noncomm_ring
  · rw [Ring.lie_def]
    dsimp [E₃]
    calc
      E₂ (B := B) * (E₁ (B := B) * E₂ (B := B)) -
          E₁ (B := B) * E₂ (B := B) * E₂ (B := B) =
        (E₂ (B := B) * E₁ (B := B)) * E₂ (B := B) -
          E₁ (B := B) * (E₂ (B := B) * E₂ (B := B)) := by noncomm_ring
      _ = (-(E₁ (B := B) * E₂ (B := B))) * E₂ (B := B) -
          E₁ (B := B) * (-1 : NestedMat B) := by rw [h21, h₂]
      _ = -(E₁ (B := B) * (E₂ (B := B) * E₂ (B := B))) + E₁ (B := B) := by
        noncomm_ring
      _ = 2 • E₁ (B := B) := by rw [h₂]; noncomm_ring
  · rw [Ring.lie_def]
    dsimp [E₃]
    calc
      E₁ (B := B) * E₂ (B := B) * E₁ (B := B) -
          E₁ (B := B) * (E₁ (B := B) * E₂ (B := B)) =
        E₁ (B := B) * (E₂ (B := B) * E₁ (B := B)) -
          (E₁ (B := B) * E₁ (B := B)) * E₂ (B := B) := by noncomm_ring
      _ = E₁ (B := B) * (-(E₁ (B := B) * E₂ (B := B))) -
          (-1 : NestedMat B) * E₂ (B := B) := by rw [h21, h₁]
      _ = -(E₁ (B := B) * E₁ (B := B)) * E₂ (B := B) + E₂ (B := B) := by
        noncomm_ring
      _ = 2 • E₂ (B := B) := by rw [h₁, two_nsmul]; noncomm_ring

/-!
## Archetype $\mathcal{A}_1$: Associative Lie Envelope & Quadratic Exponential Jet Obstruction
-/

section ArchetypeA1_AssociativeJetObstruction

variable {B : Type*} [Ring B]

def expJet2 (X : B) : B := 2 + 2 * X + X * X

theorem bch_jet2_commutator_obstruction (X Y : B) :
    expJet2 X * expJet2 Y - expJet2 Y * expJet2 X =
      4 * ⁅X, Y⁆ +
      2 * (X * X * Y - Y * (X * X) + X * (Y * Y) - Y * Y * X) +
      (X * X * (Y * Y) - Y * Y * (X * X)) := by
  dsimp [expJet2]
  rw [Ring.lie_def]
  noncomm_ring

theorem bch_jet2_nilpotent_commutator {X Y : B} (hX : X * X = 0) (hY : Y * Y = 0) :
    expJet2 X * expJet2 Y - expJet2 Y * expJet2 X = 4 * ⁅X, Y⁆ := by
  rw [bch_jet2_commutator_obstruction, hX, hY]
  noncomm_ring

end ArchetypeA1_AssociativeJetObstruction

/-! ## Exact scaled BCH product in a two-step nilpotent operator algebra -/

/-- The scaled quadratic exponential jets multiply by the exact class-two
BCH polynomial when every cubic word in the two operators vanishes. The
identity avoids adjoining a scalar half and therefore holds over any ring. -/
theorem bch_jet2_product_expansion {B : Type*} [Ring B] (X Y : B) :
    expJet2 X * expJet2 Y =
      4 + 4 * X + 4 * Y + 2 * (X * X) + 2 * (Y * Y) + 4 * (X * Y) +
        2 * (X * X * Y) + 2 * (X * Y * Y) + X * X * (Y * Y) := by
  dsimp [expJet2]
  noncomm_ring
  norm_num
  abel

/-- The quadratic jets reduce to the displayed truncated product when the
degree-three and degree-four operator words vanish. -/
theorem bch_jet2_product_of_cubic_zero {B : Type*} [Ring B] {X Y : B}
    (hxxy : X * X * Y = 0) (hxyy : X * Y * Y = 0)
    (hxxYY : X * X * (Y * Y) = 0) :
    expJet2 X * expJet2 Y =
      4 + 4 * X + 4 * Y + 2 * (X * X) + 2 * (Y * Y) + 4 * (X * Y) := by
  rw [bch_jet2_product_expansion, hxxy, hxyy, hxxYY]
  noncomm_ring

/-!
## Archetype $\mathcal{A}_2$: Brauer–Weyl $(1,1)$-Periodicity, Witt CAR Ladder & Quaternion Triple in $M_2(M_2(B))$
-/

/- Shared definitions for Archetypes A₂ and A₉ -/
/-- Nested operator matrix $M_2(M_2(B))$ represented as 4×4 block matrix with 2×2 blocks.
Each block is a 2×2 matrix over B. -/
@[simp] lemma nested_mul_apply {B : Type*} [Ring B] (M N : NestedMat B)
    (i j k l : Fin 2) :
    (M * N) i j k l =
      (M i 0 k 0) * (N 0 j 0 l) + (M i 0 k 1) * (N 0 j 1 l) +
      (M i 1 k 0) * (N 1 j 0 l) + (M i 1 k 1) * (N 1 j 1 l) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply]
  abel

/- Extensionality for nested matrices -/
lemma NestedMat.ext {B : Type*} [Ring B] {M N : NestedMat B} (h : ∀ (i j k l : Fin 2), M i j k l = N i j k l) : M = N := by
  ext i j k l
  exact h i j k l

section NestedMatInstances
variable {B : Type*} [Ring B]


end NestedMatInstances

/-!
## Archetype $\mathcal{A}_3$: Noncommutative Ring Derivations, Matrix Lifting & Unit-Inverse Rule
-/

section ArchetypeA3_NoncommutativeDerivations

def IsRingDeriv {B : Type*} [Ring B] (d : B →+ B) : Prop :=
  ∀ a b : B, d (a * b) = d a * b + a * d b

theorem IsRingDeriv.map_one {B : Type*} [Ring B] {d : B →+ B} (hd : IsRingDeriv d) :
    d 1 = 0 := by
  have h₁ : d (1 * 1 : B) = d (1 : B) * (1 : B) + (1 : B) * d (1 : B) := hd 1 1
  have h₂ : d (1 * 1 : B) = d (1 : B) := by simp
  rw [h₂] at h₁
  have h₃ : d (1 : B) * (1 : B) + (1 : B) * d (1 : B) = d (1 : B) + d (1 : B) := by
    simp [one_mul, mul_one]
  rw [h₃] at h₁
  have h₄ : d (1 : B) + d (1 : B) = d (1 : B) := by
    simpa [add_assoc] using h₁
  have h₅ : d (1 : B) = 0 := by
    have h₅₁ : d (1 : B) + d (1 : B) = d (1 : B) := h₄
    have h₅₂ : d (1 : B) = 0 := by
      apply eq_of_sub_eq_zero
      have h₅₃ : d (1 : B) + d (1 : B) - d (1 : B) = 0 := by
        rw [h₅₁]
        simp
      simpa [sub_eq_add_neg, add_assoc] using h₅₃
    exact h₅₂
  exact h₅

theorem IsRingDeriv.map_units_inv {B : Type*} [Ring B] {d : B →+ B}
    (hd : IsRingDeriv d) (u : Bˣ) :
    d (↑u⁻¹ : B) = -(↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by
  have h₁ : d ((u : B) * (↑u⁻¹ : B)) = d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B) := hd (u : B) (↑u⁻¹ : B)
  have h₂ : d ((u : B) * (↑u⁻¹ : B)) = d (1 : B) := by
    simp [Units.mul_inv]
  have h₃ : d (1 : B) = 0 := IsRingDeriv.map_one hd
  have h₄ : d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B) = 0 := by
    calc
      d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B) = d ((u : B) * (↑u⁻¹ : B)) := by rw [h₁]
      _ = d (1 : B) := by rw [h₂]
      _ = 0 := by rw [h₃]
  have h₅ : (u : B) * d (↑u⁻¹ : B) = - (d (u : B) * (↑u⁻¹ : B)) := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h₄)
  have h₆ : d (↑u⁻¹ : B) = (↑u⁻¹ : B) * (-(d (u : B) * (↑u⁻¹ : B))) := by
    have h₆₁ : (u : B) * d (↑u⁻¹ : B) = - (d (u : B) * (↑u⁻¹ : B)) := h₅
    have h₆₂ : (↑u⁻¹ : B) * (u : B) = 1 := by
      simp [Units.inv_mul]
    calc
      d (↑u⁻¹ : B) = 1 * d (↑u⁻¹ : B) := by simp
      _ = ((↑u⁻¹ : B) * (u : B)) * d (↑u⁻¹ : B) := by rw [h₆₂]
      _ = (↑u⁻¹ : B) * ((u : B) * d (↑u⁻¹ : B)) := by rw [mul_assoc]
      _ = (↑u⁻¹ : B) * (-(d (u : B) * (↑u⁻¹ : B))) := by rw [h₆₁]
  calc
    d (↑u⁻¹ : B) = (↑u⁻¹ : B) * (-(d (u : B) * (↑u⁻¹ : B))) := h₆
    _ = (↑u⁻¹ : B) * (-d (u : B) * (↑u⁻¹ : B)) := by
      noncomm_ring
    _ = -(↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by
      noncomm_ring

def liftMatrixDeriv {S : Type*} [Ring S] {n : Type*} [Fintype n] [DecidableEq n]
    (d : S →+ S) : Matrix n n S →+ Matrix n n S where
  toFun M i j := d (M i j)
  map_zero' := by ext i j; simp
  map_add' M N := by
    ext i j
    exact d.map_add (M i j) (N i j)

theorem IsRingDeriv.liftMatrix {S : Type*} [Ring S] {n : Type*} [Fintype n] [DecidableEq n]
    {d : S →+ S} (hd : IsRingDeriv d) :
    IsRingDeriv (liftMatrixDeriv (n := n) d) := by
  intro M N
  ext i k
  change d ((M * N) i k) =
    ((liftMatrixDeriv (n := n) d) M * N + M * (liftMatrixDeriv (n := n) d) N) i k
  rw [Matrix.mul_apply, map_sum, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => hd (M i j) (N j k))

end ArchetypeA3_NoncommutativeDerivations

/-!
## Archetype $\mathcal{A}_4$: Koszul Connections, Maurer–Cartan Curvature & Differential Bianchi Identity
-/

section ArchetypeA4_KoszulMaurerCartanAndBianchi

variable {B : Type*} [Ring B]

def covOp (d : B →+ B) (A ψ : B) : B := d ψ + A * ψ
def mcCurvature (d₁ d₂ : B →+ B) (A₁ A₂ : B) : B := d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆
def dressConn (d : B →+ B) (u : Bˣ) (A : B) : B := (u : B) * A * (↑u⁻¹ : B) - d (u : B) * (↑u⁻¹ : B)
def adjDeriv (d : B →+ B) (A X : B) : B := d X + ⁅A, X⁆

theorem koszul_curvature_multiplication
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (h_comm : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x)) (A₁ A₂ ψ : B) :
    covOp d₁ A₁ (covOp d₂ A₂ ψ) - covOp d₂ A₂ (covOp d₁ A₁ ψ) =
      mcCurvature d₁ d₂ A₁ A₂ * ψ := by
  dsimp [covOp, mcCurvature]
  rw [Ring.lie_def, map_add, map_add, hd₁ A₂ ψ, hd₂ A₁ ψ, h_comm ψ]
  noncomm_ring

theorem koszul_dressing_intertwining
    {d : B →+ B} (hd : IsRingDeriv d) (u : Bˣ) (A ψ : B) :
    covOp d (dressConn d u A) ((u : B) * ψ) = (u : B) * covOp d A ψ := by
  dsimp [covOp, dressConn]; rw [hd (u : B) ψ]
  have hu : (↑u⁻¹ : B) * (u : B) = 1 := Units.inv_mul u
  calc d (u : B) * ψ + (u : B) * d ψ +
        ((u : B) * A * (↑u⁻¹ : B) - d (u : B) * (↑u⁻¹ : B)) * ((u : B) * ψ)
    _ = d (u : B) * ψ + (u : B) * d ψ +
        (u : B) * A * ((↑u⁻¹ : B) * (u : B)) * ψ -
        d (u : B) * ((↑u⁻¹ : B) * (u : B)) * ψ := by
      noncomm_ring
    _ = d (u : B) * ψ + (u : B) * d ψ + (u : B) * A * 1 * ψ - d (u : B) * 1 * ψ := by rw [hu]
    _ = (u : B) * (d ψ + A * ψ) := by noncomm_ring

theorem maurer_cartan_conjugation_covariance
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (h_comm : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x)) (u : Bˣ) (A₁ A₂ : B) :
    mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) =
      (u : B) * mcCurvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : B) := by
  have h_lhs := koszul_curvature_multiplication hd₁ hd₂ h_comm
    (dressConn d₁ u A₁) (dressConn d₂ u A₂) ((u : B) * 1)
  rw [koszul_dressing_intertwining hd₂ u A₂ 1,
      koszul_dressing_intertwining hd₁ u A₁ (covOp d₂ A₂ 1),
      koszul_dressing_intertwining hd₁ u A₁ 1,
      koszul_dressing_intertwining hd₂ u A₂ (covOp d₁ A₁ 1)] at h_lhs
  have h_rhs := koszul_curvature_multiplication hd₁ hd₂ h_comm A₁ A₂ 1
  have h_comb : mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * (u : B) =
      (u : B) * mcCurvature d₁ d₂ A₁ A₂ := by
    calc mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * (u : B)
      _ = mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * ((u : B) * 1) := by rw [mul_one]
      _ = (u : B) * covOp d₁ A₁ (covOp d₂ A₂ 1) -
          (u : B) * covOp d₂ A₂ (covOp d₁ A₁ 1) := h_lhs.symm
      _ = (u : B) * (covOp d₁ A₁ (covOp d₂ A₂ 1) - covOp d₂ A₂ (covOp d₁ A₁ 1)) := by noncomm_ring
      _ = (u : B) * (mcCurvature d₁ d₂ A₁ A₂ * 1) := by rw [h_rhs]
      _ = (u : B) * mcCurvature d₁ d₂ A₁ A₂ := by rw [mul_one]
  calc mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂)
    _ = mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * ((u : B) * (↑u⁻¹ : B)) := by
        rw [Units.mul_inv, mul_one]
    _ = (mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * (u : B)) * (↑u⁻¹ : B) := by
        noncomm_ring
    _ = (u : B) * mcCurvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : B) := by rw [h_comb]

theorem logarithmic_coboundary_flatness
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (h_comm : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x)) (u : Bˣ) :
    mcCurvature d₁ d₂ (-d₁ (u : B) * (↑u⁻¹ : B)) (-d₂ (u : B) * (↑u⁻¹ : B)) = 0 := by
  have h1 : -d₁ (u : B) * (↑u⁻¹ : B) = dressConn d₁ u 0 := by
    dsimp [dressConn]
    noncomm_ring
  have h2 : -d₂ (u : B) * (↑u⁻¹ : B) = dressConn d₂ u 0 := by
    dsimp [dressConn]
    noncomm_ring
  rw [h1, h2, maurer_cartan_conjugation_covariance hd₁ hd₂ h_comm u 0 0]
  dsimp [mcCurvature]; rw [Ring.lie_def, map_zero, map_zero]
  noncomm_ring

theorem differential_bianchi_identity
    {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    (A₁ A₂ A₃ : B) :
    adjDeriv d₁ A₁ (mcCurvature d₂ d₃ A₂ A₃) +
    adjDeriv d₂ A₂ (mcCurvature d₃ d₁ A₃ A₁) +
    adjDeriv d₃ A₃ (mcCurvature d₁ d₂ A₁ A₂) = 0 := by
  dsimp [adjDeriv, mcCurvature]
  simp only [Ring.lie_def, map_add, map_sub]
  rw [hd₁ A₂ A₃, hd₁ A₃ A₂, hd₂ A₃ A₁, hd₂ A₁ A₃, hd₃ A₁ A₂, hd₃ A₂ A₁,
      h12 A₃, h13 A₂, h23 A₁, ← h12 A₃, ← h13 A₂, ← h23 A₁]
  noncomm_ring

theorem uncovariantized_exterior_remainder
    {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    (A₁ A₂ A₃ : B) :
    d₁ (mcCurvature d₂ d₃ A₂ A₃) + d₂ (mcCurvature d₃ d₁ A₃ A₁) + d₃ (mcCurvature d₁ d₂ A₁ A₂) =
      ⁅mcCurvature d₂ d₃ A₂ A₃, A₁⁆ + ⁅mcCurvature d₃ d₁ A₃ A₁, A₂⁆ + ⁅mcCurvature d₁ d₂ A₁ A₂, A₃⁆ := by
  have h := differential_bianchi_identity hd₁ hd₂ hd₃ h12 h23 h13 A₁ A₂ A₃
  calc d₁ (mcCurvature d₂ d₃ A₂ A₃) + d₂ (mcCurvature d₃ d₁ A₃ A₁) + d₃ (mcCurvature d₁ d₂ A₁ A₂)
    _ = (adjDeriv d₁ A₁ (mcCurvature d₂ d₃ A₂ A₃) +
         adjDeriv d₂ A₂ (mcCurvature d₃ d₁ A₃ A₁) +
         adjDeriv d₃ A₃ (mcCurvature d₁ d₂ A₁ A₂)) +
        (⁅mcCurvature d₂ d₃ A₂ A₃, A₁⁆ + ⁅mcCurvature d₃ d₁ A₃ A₁, A₂⁆ +
         ⁅mcCurvature d₁ d₂ A₁ A₂, A₃⁆) := by
          dsimp [adjDeriv]; simp only [Ring.lie_def]; noncomm_ring
    _ = 0 + (⁅mcCurvature d₂ d₃ A₂ A₃, A₁⁆ + ⁅mcCurvature d₃ d₁ A₃ A₁, A₂⁆ +
             ⁅mcCurvature d₁ d₂ A₁ A₂, A₃⁆) := by rw [h]
    _ = ⁅mcCurvature d₂ d₃ A₂ A₃, A₁⁆ + ⁅mcCurvature d₃ d₁ A₃ A₁, A₂⁆ +
        ⁅mcCurvature d₁ d₂ A₁ A₂, A₃⁆ := zero_add _

end ArchetypeA4_KoszulMaurerCartanAndBianchi

/-!
## Archetype $\mathcal{A}_5$: Gerbe-Twisted Operator Bundles, Period-Rank Torsion & Gerbe Flatness
-/

section ArchetypeA5_GerbeTwistedBundlesAndTorsion

variable {B : Type*} [Ring B]

def gerbeEmbed (r : ℕ) (b : B) : Matrix (Fin r) (Fin r) B :=
  Matrix.of (fun i j => if i = j then b else 0)

def ncTrace {r : ℕ} (M : Matrix (Fin r) (Fin r) B) : B :=
  ∑ i : Fin r, M i i

def twistedBundleCurvature {r : ℕ}
    (d₁ d₂ : B →+ B) (A₁ A₂ : Matrix (Fin r) (Fin r) B) (B_gerbe : B) :
    Matrix (Fin r) (Fin r) B :=
  mcCurvature (liftMatrixDeriv d₁) (liftMatrixDeriv d₂) A₁ A₂ + gerbeEmbed r B_gerbe

theorem ncTrace_gerbeEmbed (r : ℕ) (b : B) :
    ncTrace (gerbeEmbed r b) = r • b := by
  dsimp [ncTrace, gerbeEmbed]; simp [Finset.sum_const, Finset.card_fin]

theorem projectively_flat_torsion_anomaly {r : ℕ}
    (d₁ d₂ : B →+ B) (A₁ A₂ : Matrix (Fin r) (Fin r) B) (B_gerbe : B)
    (h_flat : twistedBundleCurvature d₁ d₂ A₁ A₂ B_gerbe = 0) :
    r • B_gerbe = -(d₁ (ncTrace A₂) - d₂ (ncTrace A₁) + ncTrace ⁅A₁, A₂⁆) := by
  have h_tr : ncTrace (twistedBundleCurvature d₁ d₂ A₁ A₂ B_gerbe) = 0 := by
    rw [h_flat]; dsimp [ncTrace]; simp
  have h_decomp : ncTrace (twistedBundleCurvature d₁ d₂ A₁ A₂ B_gerbe) =
      (d₁ (ncTrace A₂) - d₂ (ncTrace A₁) + ncTrace ⁅A₁, A₂⁆) + r • B_gerbe := by
    dsimp [twistedBundleCurvature, mcCurvature, ncTrace, liftMatrixDeriv]
    simp only [Matrix.add_apply, Matrix.sub_apply, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, map_sum, ← ncTrace_gerbeEmbed r B_gerbe]
    rfl
  rw [h_decomp] at h_tr
  exact eq_neg_of_add_eq_zero_right h_tr

theorem projectively_flat_implies_gerbe_flat
    {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    {A₁ A₂ A₃ B₂₃ B₃₁ B₁₂ : B}
    (h_flat₂₃ : mcCurvature d₂ d₃ A₂ A₃ + B₂₃ = 0)
    (h_flat₃₁ : mcCurvature d₃ d₁ A₃ A₁ + B₃₁ = 0)
    (h_flat₁₂ : mcCurvature d₁ d₂ A₁ A₂ + B₁₂ = 0)
    (h_comm₁ : ⁅A₁, B₂₃⁆ = 0) (h_comm₂ : ⁅A₂, B₃₁⁆ = 0) (h_comm₃ : ⁅A₃, B₁₂⁆ = 0) :
    d₁ B₂₃ + d₂ B₃₁ + d₃ B₁₂ = 0 := by
  have h_b := differential_bianchi_identity hd₁ hd₂ hd₃ h12 h23 h13 A₁ A₂ A₃
  have hF₂₃ : mcCurvature d₂ d₃ A₂ A₃ = -B₂₃ := eq_neg_of_add_eq_zero_left h_flat₂₃
  have hF₃₁ : mcCurvature d₃ d₁ A₃ A₁ = -B₃₁ := eq_neg_of_add_eq_zero_left h_flat₃₁
  have hF₁₂ : mcCurvature d₁ d₂ A₁ A₂ = -B₁₂ := eq_neg_of_add_eq_zero_left h_flat₁₂
  rw [hF₂₃, hF₃₁, hF₁₂] at h_b
  dsimp [adjDeriv] at h_b
  simp only [map_neg] at h_b
  have hc₁ : ⁅A₁, -B₂₃⁆ = 0 := by
    rw [Ring.lie_def] at h_comm₁ ⊢
    calc A₁ * -B₂₃ - (-B₂₃) * A₁
        = -(A₁ * B₂₃ - B₂₃ * A₁) := by noncomm_ring
      _ = 0 := by rw [h_comm₁]; simp
  have hc₂ : ⁅A₂, -B₃₁⁆ = 0 := by
    rw [Ring.lie_def] at h_comm₂ ⊢
    calc A₂ * -B₃₁ - (-B₃₁) * A₂
        = -(A₂ * B₃₁ - B₃₁ * A₂) := by noncomm_ring
      _ = 0 := by rw [h_comm₂]; simp
  have hc₃ : ⁅A₃, -B₁₂⁆ = 0 := by
    rw [Ring.lie_def] at h_comm₃ ⊢
    calc A₃ * -B₁₂ - (-B₁₂) * A₃
        = -(A₃ * B₁₂ - B₁₂ * A₃) := by noncomm_ring
      _ = 0 := by rw [h_comm₃]; simp
  rw [hc₁, hc₂, hc₃, add_zero, add_zero, add_zero] at h_b
  calc d₁ B₂₃ + d₂ B₃₁ + d₃ B₁₂
    _ = -(-d₁ B₂₃ + -d₂ B₃₁ + -d₃ B₁₂) := by abel
    _ = -0 := by rw [h_b]
    _ = 0 := neg_zero

end ArchetypeA5_GerbeTwistedBundlesAndTorsion

/-!
## Archetype $\mathcal{A}_6$: Twisted Group Braiding $ZX = QXZ$ & 1-Cocycle Cohomology
-/

section ArchetypeA6_TwistedGroupCocycle

variable {G : Type*} [Group G]

def conjBy (x q : G) : G := x * q * x⁻¹

def twistedCocycle (X Q : G) : ℕ → G
  | 0 => 1
  | n + 1 => Q * conjBy X (twistedCocycle X Q n)

theorem braided_pow_law {X Z Q : G} (h_braid : Z * X = Q * X * Z) (n : ℕ) :
    Z * X ^ n = twistedCocycle X Q n * X ^ n * Z := by
  induction' n with n ih
  · simp [twistedCocycle]
  · calc Z * X ^ (n + 1)
      _ = (Z * X) * X ^ n := by rw [pow_succ', mul_assoc]
      _ = (Q * X * Z) * X ^ n := by rw [h_braid]
      _ = Q * X * (Z * X ^ n) := by group
      _ = Q * X * (twistedCocycle X Q n * X ^ n * Z) := by rw [ih]
      _ = (Q * (X * twistedCocycle X Q n * X⁻¹)) * (X * X ^ n) * Z := by group
      _ = twistedCocycle X Q (n + 1) * X ^ (n + 1) * Z := by
          rw [twistedCocycle, conjBy, ← pow_succ']

theorem twistedCocycle_add (X Q : G) (m n : ℕ) :
    twistedCocycle X Q (m + n) =
      twistedCocycle X Q m * conjBy (X ^ m) (twistedCocycle X Q n) := by
  induction' m with m ih
  · simp [twistedCocycle, conjBy]
  · have h_add : m + 1 + n = (m + n) + 1 := by omega
    rw [h_add, twistedCocycle, ih, twistedCocycle]
    dsimp [conjBy]; rw [pow_succ']; group

/-- With involutive braid generators, the noncentral phase is inverted by
conjugation by either generator. This is the period-two consequence of the
braiding equation `Z * X = Q * X * Z`. -/
theorem involutive_braid_phase_inversion {X Z Q : G}
    (h_braid : Z * X = Q * X * Z)
    (hX : X * X = 1) (hZ : Z * Z = 1) :
    X * Q * X = Q⁻¹ ∧ Z * Q * Z = Q⁻¹ := by
  have hXZ : (X * Z) * (Z * X) = 1 := by
    calc
      (X * Z) * (Z * X) = X * (Z * Z) * X := by group
      _ = X * X := by rw [hZ]; group
      _ = 1 := hX
  have hQ : Q = Z * X * Z * X := by
    calc
      Q = Q * ((X * Z) * (Z * X)) := by rw [hXZ, mul_one]
      _ = (Q * X * Z) * (Z * X) := by group
      _ = (Z * X) * (Z * X) := by rw [← h_braid]
      _ = Z * X * Z * X := by group
  have hXi : X⁻¹ = X := inv_eq_of_mul_eq_one_right hX
  have hZi : Z⁻¹ = Z := inv_eq_of_mul_eq_one_right hZ
  constructor
  · calc
      X * Q * X = X * (Z * X * Z * X) * X := by rw [hQ]
      _ = (X * Z * X * Z) * (X * X) := by group
      _ = X * Z * X * Z := by rw [hX, mul_one]
      _ = (Z * X * Z * X)⁻¹ := by
        calc
          X * Z * X * Z = X⁻¹ * Z⁻¹ * X⁻¹ * Z⁻¹ := by rw [hXi, hZi]
          _ = (Z * X * Z * X)⁻¹ := by group
      _ = Q⁻¹ := by rw [hQ]
  · calc
      Z * Q * Z = Z * (Z * X * Z * X) * Z := by rw [hQ]
      _ = (Z * Z) * (X * Z * X * Z) := by group
      _ = X * Z * X * Z := by rw [hZ, one_mul]
      _ = (Z * X * Z * X)⁻¹ := by
        calc
          X * Z * X * Z = X⁻¹ * Z⁻¹ * X⁻¹ * Z⁻¹ := by rw [hXi, hZi]
          _ = (Z * X * Z * X)⁻¹ := by group
      _ = Q⁻¹ := by rw [hQ]

theorem twistedCocycle_torsion_obstruction {X Z Q : G}
    (h_braid : Z * X = Q * X * Z) {N : ℕ} (hXN : X ^ N = 1) :
    twistedCocycle X Q N = 1 := by
  have h := braided_pow_law h_braid N
  rw [hXN, mul_one, mul_one] at h
  calc twistedCocycle X Q N
    _ = (twistedCocycle X Q N * Z) * Z⁻¹ := by group
    _ = Z * Z⁻¹ := by rw [← h]
    _ = 1 := by group

end ArchetypeA6_TwistedGroupCocycle

/-!
## Archetype A₇: universal unipotent block monodromy

The coefficient ring remains arbitrary. All identities below are in nested
operator matrices; characteristic zero is used only for the infinite-order
consequence.
-/

section ArchetypeA7_UniversalBlockMonodromy

variable {B : Type*} [Ring B]

/-- Explicit 2×2 matrices over B for the block components -/
def Nplus : Matrix (Fin 2) (Fin 2) B :=
  Matrix.of (fun i _ => if i = 0 then -1 else 1)
def Glink : Matrix (Fin 2) (Fin 2) B :=
  Matrix.of (fun i j => if i = 0 then 1 else if j = 0 then 0 else 1)
def Gilink : Matrix (Fin 2) (Fin 2) B :=
  Matrix.of (fun i j => if i = 0 then if j = 0 then 1 else -1
                        else if j = 0 then 0 else 1)
def FminusBlock : Matrix (Fin 2) (Fin 2) B :=
  Matrix.of (fun i j => if i = 1 then if j = 0 then 1 else 0 else 0)
def sigmaGBlock : Matrix (Fin 2) (Fin 2) B :=
  Matrix.of (fun i j => if i = 0 then if j = 0 then 0 else 1
                        else if j = 0 then 1 else -1)
def gammaGBlock : Matrix (Fin 2) (Fin 2) B :=
  Matrix.of (fun i j => if i = 0 then 1 else if j = 0 then 0 else -1)

/-- 4×4 nested operator matrices built from 2×2 blocks.
Each is a 2×2 matrix whose entries are 2×2 matrices over B. -/
def Xblk : NestedMat B :=
  Matrix.of (fun i j => if i = 0 then if j = 1 then Gilink else 0
                        else if j = 0 then Glink else 0)
def Zblk : NestedMat B :=
  Matrix.of (fun i j => if i = 0 then if j = 0 then sigmaOp else 0
                        else if j = 1 then gammaOneOp else 0)
def Nblk : NestedMat B :=
  Matrix.of (fun i j => if i = 0 then if j = 0 then Nplus else 0
                        else if j = 1 then -FminusBlock else 0)
def Qblk : NestedMat B :=
  (Zblk * Xblk) * (Zblk * Xblk)

theorem Xblk_sq : (Xblk (B := B) : NestedMat B) * Xblk = 1 := by
  have hGL : Glink (B := B) * Gilink = 1 := by
    apply ext_fin2
    · rw [mul2_00]
      dsimp [Glink, Gilink, F_plus, Matrix.of_apply, Matrix.one_apply,
        Matrix.add_apply, Matrix.sub_apply]
      noncomm_ring
    · rw [mul2_01]
      dsimp [Glink, Gilink, F_plus, Matrix.of_apply, Matrix.one_apply,
        Matrix.add_apply, Matrix.sub_apply]
      noncomm_ring
    · rw [mul2_10]
      dsimp [Glink, Gilink, F_plus, Matrix.of_apply, Matrix.one_apply,
        Matrix.add_apply, Matrix.sub_apply]
      noncomm_ring
    · rw [mul2_11]
      dsimp [Glink, Gilink, F_plus, Matrix.of_apply, Matrix.one_apply,
        Matrix.add_apply, Matrix.sub_apply]
      noncomm_ring
  have hLG : Gilink * Glink (B := B) = 1 := by
    apply ext_fin2
    · rw [mul2_00]
      dsimp [Glink, Gilink, F_plus, Matrix.of_apply, Matrix.one_apply,
        Matrix.add_apply, Matrix.sub_apply]
      noncomm_ring
    · rw [mul2_01]
      dsimp [Glink, Gilink, F_plus, Matrix.of_apply, Matrix.one_apply,
        Matrix.add_apply, Matrix.sub_apply]
      noncomm_ring
    · rw [mul2_10]
      dsimp [Glink, Gilink, F_plus, Matrix.of_apply, Matrix.one_apply,
        Matrix.add_apply, Matrix.sub_apply]
      noncomm_ring
    · rw [mul2_11]
      dsimp [Glink, Gilink, F_plus, Matrix.of_apply, Matrix.one_apply,
        Matrix.add_apply, Matrix.sub_apply]
      noncomm_ring
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (0 : Matrix (Fin 2) (Fin 2) B) * 0 + Gilink * Glink = 1
    rw [zero_mul, zero_add, hLG]
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (0 : Matrix (Fin 2) (Fin 2) B) * Gilink + Gilink * 0 = 0
    simp
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change Glink * 0 + 0 * Glink = 0
    simp
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change Glink * Gilink + (0 : Matrix (Fin 2) (Fin 2) B) * 0 = 1
    rw [zero_mul, add_zero, hGL]

theorem Zblk_sq : (Zblk (B := B) : NestedMat B) * Zblk = 1 := by
  have hbase := cl11_and_witt_car_relations (A := B)
  have hs : sigmaOp (A := B) * sigmaOp = 1 := hbase.1
  have ho : omegaOp (A := B) * omegaOp = -1 := hbase.2.1
  have hso : sigmaOp (A := B) * omegaOp = gammaOneOp := hbase.2.2.1
  have hanti : sigmaOp (A := B) * omegaOp (A := B) +
      omegaOp (A := B) * sigmaOp (A := B) = 0 := by
    simpa [anticomm] using hbase.2.2.2.1
  have hos : omegaOp (A := B) * sigmaOp (A := B) =
      -(sigmaOp (A := B) * omegaOp (A := B)) := by
    calc
      omegaOp (A := B) * sigmaOp (A := B) =
          (sigmaOp (A := B) * omegaOp (A := B) +
            omegaOp (A := B) * sigmaOp (A := B)) -
            sigmaOp (A := B) * omegaOp (A := B) := by abel
      _ = 0 - sigmaOp (A := B) * omegaOp (A := B) := by rw [hanti]
      _ = -(sigmaOp (A := B) * omegaOp (A := B)) := by simp
  have hg : gammaOneOp (A := B) * gammaOneOp = 1 := by
    rw [← hso]
    calc
      (sigmaOp (A := B) * omegaOp (A := B)) *
          (sigmaOp (A := B) * omegaOp (A := B)) =
          sigmaOp (A := B) * (omegaOp (A := B) * sigmaOp (A := B)) *
            omegaOp (A := B) := by noncomm_ring
      _ = sigmaOp (A := B) *
          (-(sigmaOp (A := B) * omegaOp (A := B))) * omegaOp (A := B) := by rw [hos]
      _ = -((sigmaOp (A := B) * sigmaOp (A := B)) *
          (omegaOp (A := B) * omegaOp (A := B))) := by noncomm_ring
      _ = 1 := by rw [hs, ho]; noncomm_ring
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [Zblk]
    exact hs
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [Zblk]
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [Zblk]
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [Zblk]
    exact hg

theorem Qblk_eq_one_add_Nblk : (Qblk (B := B) : NestedMat B) = 1 + Nblk := by
  have hZX : (Zblk (B := B) : NestedMat B) * Xblk =
      Matrix.of (fun i j : Fin 2 =>
        if i = 0 then if j = 1 then sigmaOp (A := B) * Gilink (B := B) else 0
        else if j = 0 then gammaOneOp (A := B) * Glink (B := B) else 0) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · change (∑ k : Fin 2, Zblk 0 k * Xblk k 0) = 0
      simp [Zblk, Xblk, Glink, Gilink, Fin.sum_univ_two, zero_mul, mul_zero]
    · change (∑ k : Fin 2, Zblk 0 k * Xblk k 1) =
        sigmaOp (A := B) * Gilink (B := B)
      simp [Zblk, Xblk, Glink, Gilink, Fin.sum_univ_two, zero_mul, mul_zero]
    · change (∑ k : Fin 2, Zblk 1 k * Xblk k 0) =
        gammaOneOp (A := B) * Glink (B := B)
      simp [Zblk, Xblk, Glink, Gilink, Fin.sum_univ_two]
    · change (∑ k : Fin 2, Zblk 1 k * Xblk k 1) = 0
      simp [Zblk, Xblk, Glink, Gilink, Fin.sum_univ_two]
    all_goals
      ext a b
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hσG : sigmaOp (A := B) * Gilink (B := B) = sigmaGBlock (B := B) := by
    apply ext_fin2
    · rw [mul2_00]
      dsimp [sigmaGBlock, sigmaOp, Gilink, Matrix.of_apply]
      noncomm_ring
    · rw [mul2_01]
      dsimp [sigmaGBlock, sigmaOp, Gilink, Matrix.of_apply]
      noncomm_ring
    · rw [mul2_10]
      dsimp [sigmaGBlock, sigmaOp, Gilink, Matrix.of_apply]
      noncomm_ring
    · rw [mul2_11]
      dsimp [sigmaGBlock, sigmaOp, Gilink, Matrix.of_apply]
      noncomm_ring
  have hγG : gammaOneOp (A := B) * Glink (B := B) = gammaGBlock (B := B) := by
    apply ext_fin2
    · rw [mul2_00]
      dsimp [gammaGBlock, gammaOneOp, Glink, Matrix.of_apply]
      noncomm_ring
    · rw [mul2_01]
      dsimp [gammaGBlock, gammaOneOp, Glink, Matrix.of_apply]
      noncomm_ring
    · rw [mul2_10]
      dsimp [gammaGBlock, gammaOneOp, Glink, Matrix.of_apply]
      noncomm_ring
    · rw [mul2_11]
      dsimp [gammaGBlock, gammaOneOp, Glink, Matrix.of_apply]
      noncomm_ring
  have htop : (sigmaOp (A := B) * Gilink (B := B)) *
      (gammaOneOp (A := B) * Glink (B := B)) =
      (1 : Matrix (Fin 2) (Fin 2) B) + Nplus := by
    rw [hσG, hγG]
    change sigmaGBlock (B := B) * gammaGBlock (B := B) =
      (1 : Matrix (Fin 2) (Fin 2) B) + Nplus
    apply ext_fin2
    · rw [mul2_00, Matrix.add_apply]
      simp [sigmaGBlock, gammaGBlock, Nplus, Matrix.of_apply]
    · rw [mul2_01, Matrix.add_apply]
      simp [sigmaGBlock, gammaGBlock, Nplus, Matrix.of_apply]
    · rw [mul2_10, Matrix.add_apply]
      simp [sigmaGBlock, gammaGBlock, Nplus, Matrix.of_apply]
    · rw [mul2_11, Matrix.add_apply]
      simp [sigmaGBlock, gammaGBlock, Nplus, Matrix.of_apply]
  have hbot : (gammaOneOp (A := B) * Glink (B := B)) *
      (sigmaOp (A := B) * Gilink (B := B)) =
      (1 : Matrix (Fin 2) (Fin 2) B) - FminusBlock := by
    rw [hγG, hσG]
    change gammaGBlock (B := B) * sigmaGBlock (B := B) =
      (1 : Matrix (Fin 2) (Fin 2) B) - FminusBlock
    apply ext_fin2
    · rw [mul2_00]; dsimp [sigmaGBlock, gammaGBlock, FminusBlock, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply]; noncomm_ring
    · rw [mul2_01]; dsimp [sigmaGBlock, gammaGBlock, FminusBlock, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply]; noncomm_ring
    · rw [mul2_10]; dsimp [sigmaGBlock, gammaGBlock, FminusBlock, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply]; noncomm_ring
    · rw [mul2_11]; dsimp [sigmaGBlock, gammaGBlock, FminusBlock, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply]; noncomm_ring
  have hZXsq := congrArg₂ (fun M N : NestedMat B => M * N) hZX hZX
  have hQ : Qblk = Matrix.of (fun i j : Fin 2 =>
      if i = 0 then if j = 0 then (1 : Matrix (Fin 2) (Fin 2) B) + Nplus
        else 0
      else if j = 0 then 0 else (1 : Matrix (Fin 2) (Fin 2) B) - FminusBlock) := by
    change (Zblk * Xblk) * (Zblk * Xblk) = _
    rw [hZXsq]
    have htop' : sigmaGBlock (B := B) * gammaGBlock (B := B) =
        (1 : Matrix (Fin 2) (Fin 2) B) + Nplus := by
      rw [← hσG, ← hγG]
      exact htop
    have hbot' : gammaGBlock (B := B) * sigmaGBlock (B := B) =
        (1 : Matrix (Fin 2) (Fin 2) B) - FminusBlock := by
      rw [← hγG, ← hσG]
      exact hbot
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j
    · simpa [Matrix.of_apply, hσG, hγG] using htop
    · simp [Matrix.of_apply]
    · simp [Matrix.of_apply]
    · simpa [Matrix.of_apply, hγG, hσG] using hbot
  rw [hQ]
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Nblk, Nplus, FminusBlock, Matrix.add_apply, Matrix.one_apply] <;> noncomm_ring

theorem Nblk_sq : (Nblk (B := B) : NestedMat B) * Nblk = 0 := by
  change (Nblk (B := B) : NestedMat B) * Nblk = (0 : NestedMat B)
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Nblk, Nplus, FminusBlock, nested_mul_apply, Matrix.mul_apply,
      Fin.sum_univ_two, mul2_00, mul2_01, mul2_10, mul2_11] <;> noncomm_ring

theorem Xblk_conjugates_Nblk : (Xblk (B := B) : NestedMat B) * Nblk * Xblk = -Nblk := by
  change (Xblk (B := B) : NestedMat B) * Nblk * Xblk = -Nblk
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Xblk, Nblk, Nplus, Glink, Gilink, F_plus, FminusBlock,
      nested_mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      mul2_00, mul2_01, mul2_10, mul2_11, Matrix.neg_apply] <;> noncomm_ring

theorem Zblk_conjugates_Nblk : (Zblk (B := B) : NestedMat B) * Nblk * Zblk = -Nblk := by
  change (Zblk (B := B) : NestedMat B) * Nblk * Zblk = -Nblk
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Zblk, Nblk, Nplus, sigmaOp, gammaOneOp, FminusBlock,
      nested_mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      mul2_00, mul2_01, mul2_10, mul2_11, Matrix.neg_apply] <;> noncomm_ring

theorem Qblk_braiding_and_cocycle :
    (Zblk (B := B) : NestedMat B) * Xblk = Qblk * Xblk * Zblk ∧
    (Qblk (B := B) : NestedMat B) * (Xblk * Qblk * Xblk) = 1 ∧
    (Zblk * Qblk * Zblk) * (Qblk : NestedMat B) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · symm
    calc
      Qblk * Xblk * Zblk = (Zblk * Xblk) * (Zblk * Xblk) * Xblk * Zblk := by
        rfl
      _ = (Zblk * Xblk) * Zblk * Xblk * Xblk * Zblk := by noncomm_ring
      _ = (Zblk * Xblk) * Zblk * (Xblk * Xblk) * Zblk := by noncomm_ring
      _ = (Zblk * Xblk) * Zblk * (1 : NestedMat B) * Zblk := by
        rw [Xblk_sq (B := B)]
      _ = (Zblk * Xblk) * (Zblk * Zblk) := by noncomm_ring
      _ = Zblk * Xblk := by rw [Zblk_sq (B := B)]; noncomm_ring
  · rw [Qblk_eq_one_add_Nblk]
    have hx : Xblk * ((1 : NestedMat B) + Nblk) * Xblk = (1 : NestedMat B) - Nblk := by
      calc
        Xblk * ((1 : NestedMat B) + Nblk) * Xblk =
            Xblk * Xblk + Xblk * Nblk * Xblk := by noncomm_ring
        _ = (1 : NestedMat B) + -Nblk := by rw [Xblk_sq, Xblk_conjugates_Nblk]
        _ = (1 : NestedMat B) - Nblk := by noncomm_ring
    rw [hx]
    calc
      ((1 : NestedMat B) + Nblk) * ((1 : NestedMat B) - Nblk) =
        1 - Nblk * Nblk := by noncomm_ring
      _ = 1 := by rw [Nblk_sq]; noncomm_ring
  · rw [Qblk_eq_one_add_Nblk]
    have hz : Zblk * ((1 : NestedMat B) + Nblk) * Zblk = (1 : NestedMat B) - Nblk := by
      calc
        Zblk * ((1 : NestedMat B) + Nblk) * Zblk =
            Zblk * Zblk + Zblk * Nblk * Zblk := by noncomm_ring
        _ = (1 : NestedMat B) + -Nblk := by rw [Zblk_sq, Zblk_conjugates_Nblk]
        _ = (1 : NestedMat B) - Nblk := by noncomm_ring
    rw [hz]
    calc
      ((1 : NestedMat B) - Nblk) * ((1 : NestedMat B) + Nblk) =
        1 - Nblk * Nblk := by noncomm_ring
      _ = 1 := by rw [Nblk_sq]; noncomm_ring

theorem Qblk_pow (n : ℕ) : (Qblk (B := B) : NestedMat B) ^ n = 1 + n • Nblk := by
  have h : ∀ (n : ℕ), (1 + Nblk : NestedMat B) ^ n = 1 + n • Nblk := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih]
      have hmul : (n • (Nblk : NestedMat B)) * Nblk = 0 := by
        rw [nsmul_eq_mul, mul_assoc, Nblk_sq, mul_zero]
      calc
        (1 + n • (Nblk : NestedMat B)) * (1 + Nblk) =
            1 + (n • Nblk + Nblk) + (n • Nblk) * Nblk := by noncomm_ring
        _ = 1 + (n • Nblk + Nblk) := by rw [hmul, add_zero]
        _ = 1 + (n + 1) • Nblk := by rw [add_nsmul]; simp
      <;>
      (try noncomm_ring) <;>
      (try simp_all [mul_assoc, mul_add, add_mul, mul_one, one_mul]) <;>
      (try ring_nf at * <;> simp_all [Nblk_sq]) <;>
      (try noncomm_ring) <;>
      (try aesop)
  rw [Qblk_eq_one_add_Nblk]
  exact h n

theorem Qblk_infinite_order [CharZero B] (n : ℕ) (hn : 0 < n) :
    (Qblk (B := B) : NestedMat B) ^ n ≠ 1 := by
  intro h
  have hnil : (n : ℕ) • (Nblk (B := B) : NestedMat B) = 0 := by
    have hp := Qblk_pow (B := B) n
    rw [hp] at h
    have hs : (1 : NestedMat B) + n • Nblk = (1 : NestedMat B) := h
    have hs' : (1 : NestedMat B) + n • Nblk = 1 + (0 : NestedMat B) := by
      simpa using hs
    calc
      n • Nblk = ((1 : NestedMat B) + n • Nblk) - 1 := by noncomm_ring
      _ = (1 : NestedMat B) - 1 := congrArg (fun x : NestedMat B => x - 1) hs
      _ = 0 := sub_self _
  have hentry := congrArg (fun M : NestedMat B => M 0 0 1 0) hnil
  have hcast : (n : B) = 0 := by
    simpa [Nblk, Nplus, Matrix.of_apply] using hentry
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) hcast

end ArchetypeA7_UniversalBlockMonodromy

/-!
## Archetype A₈: Peirce-Walsh reconstruction and the localization variance

The mode extraction and reconstruction remain over a general noncommutative
ring. The variance identity is reused from its star-ring owner.
-/

section ArchetypeA8_PeirceWalshAndFUPVariance

variable {B : Type*} [Ring B]

/-- Self-contained Peirce fiber lift: projects onto the P₊ component and its σ-conjugate. -/
def peirceFiberLift (X : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  InfoGeometry.Clifford.OperatorValuedJonesWalsh.peirceFiberLift X

def mellinCoeffI (M : Matrix (Fin 2) (Fin 2) B) :=
  peirceFiberLift (M + sigmaOp * M * sigmaOp)
def mellinCoeffGamma (M : Matrix (Fin 2) (Fin 2) B) :=
  peirceFiberLift (M - sigmaOp * M * sigmaOp)
def mellinCoeffSigma (M : Matrix (Fin 2) (Fin 2) B) :=
  peirceFiberLift (M * sigmaOp + sigmaOp * M)
def mellinCoeffOmega (M : Matrix (Fin 2) (Fin 2) B) :=
  peirceFiberLift (sigmaOp * M - M * sigmaOp)

theorem cliffordMellinWalshReconstruction (M : Matrix (Fin 2) (Fin 2) B) :
    mellinCoeffI M * (1 : Matrix (Fin 2) (Fin 2) B) +
      mellinCoeffGamma M * gammaOneOp +
      mellinCoeffSigma M * sigmaOp + mellinCoeffOmega M * omegaOp = M + M := by
  have hJ : sigmaOp (A := B) = InfoGeometry.Clifford.J_mat := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [sigmaOp, InfoGeometry.Clifford.J_mat]
  have hI : (1 : Matrix (Fin 2) (Fin 2) B) = InfoGeometry.Clifford.I_mat := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.Clifford.I_mat]
  have hGamma : gammaOneOp (A := B) = InfoGeometry.Clifford.Gamma_mat := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [gammaOneOp, InfoGeometry.Clifford.Gamma_mat]
  have hOmega : omegaOp (A := B) = -InfoGeometry.Clifford.K_mat := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [omegaOp, InfoGeometry.Clifford.K_mat]
  dsimp [mellinCoeffI, mellinCoeffGamma, mellinCoeffSigma, mellinCoeffOmega,
    peirceFiberLift]
  rw [hJ, hGamma, hOmega, hI]
  exact InfoGeometry.Clifford.OperatorValuedJonesWalsh.peirce_walsh_reconstruction M

theorem fupProjectionVariance {R : Type*} [Ring R] [StarRing R]
    {P Q : R} (hPidem : P * P = P) (hPstar : star P = P)
    (hQidem : Q * Q = Q) (hQstar : star Q = Q) :
    P * Q * P - (P * Q * P) * (P * Q * P) =
      (P * star ⁅P, Q⁆) * (⁅P, Q⁆ * P) := by
  exact InfoGeometry.OperatorAlgebra.KnutsenGaborOperatorAlgebra.compressedLocalization_variance_eq_commutator
    hPidem hPstar hQidem hQstar

end ArchetypeA8_PeirceWalshAndFUPVariance

/-!
## Archetype $\mathcal{A}_9$: Quaternionic Artin Braid and Operator Bracket in $M_2(M_2(B))$
-/

section ArchetypeA9_MasterSynthesis

/-- Concrete quaternion basis elements as 4×4 nested operator matrices over B. -/
def quaternionE₁ {B : Type*} [Ring B] : NestedMat B :=
  E₁ (B := B)

def quaternionE₂ {B : Type*} [Ring B] : NestedMat B :=
  E₂ (B := B)

def quaternionE₃ {B : Type*} [Ring B] : NestedMat B :=
  E₃ (B := B)

def quaternionRotorPlus {B : Type*} [Ring B] (E : NestedMat B) : NestedMat B :=
  1 + E

/-- Relations satisfied by the quaternion basis elements -/
theorem quaternionE₁_E₂_relations {B : Type*} [Ring B] :
    (quaternionE₁ (B := B)) * (quaternionE₁ (B := B)) = -1 ∧
    (quaternionE₂ (B := B)) * (quaternionE₂ (B := B)) = -1 ∧
    anticomm (quaternionE₁ (B := B)) (quaternionE₂ (B := B)) = 0 := by
  rcases nested_quaternion_lie_relations (B := B) with ⟨h₁, _, _, hₐ, _, _, _⟩
  exact ⟨h₁, (nested_quaternion_lie_relations (B := B)).2.1, hₐ⟩

theorem quaternionRotor_commutator {B : Type*} [Ring B] :
    ⁅quaternionRotorPlus (quaternionE₁ (B := B)), quaternionRotorPlus (quaternionE₂ (B := B))⁆ =
      (2 : ℕ) • quaternionE₃ (B := B) := by
  have h := (nested_quaternion_lie_relations (B := B)).2.2.2.2.1
  calc
    ⁅quaternionRotorPlus (quaternionE₁ (B := B)),
      quaternionRotorPlus (quaternionE₂ (B := B))⁆ = ⁅E₁, E₂⁆ := by
        change ⁅(1 : NestedMat B) + (E₁ (B := B) : NestedMat B),
          (1 : NestedMat B) + (E₂ (B := B) : NestedMat B)⁆ =
            ⁅(E₁ (B := B) : NestedMat B), (E₂ (B := B) : NestedMat B)⁆
        simp only [Ring.lie_def]
        noncomm_ring
    _ = ⁅(E₁ (B := B) : NestedMat B), (E₂ (B := B) : NestedMat B)⁆ := rfl
    _ = (2 : ℕ) • (E₃ (B := B) : NestedMat B) := h

def R₁₂ {B : Type*} [Ring B] : NestedMat B :=
  quaternionRotorPlus (quaternionE₁ (B := B))
def R₂₃ {B : Type*} [Ring B] : NestedMat B :=
  quaternionRotorPlus (quaternionE₂ (B := B))

theorem clifford_bivector_triple_product {B : Type*} [Ring B] {E₁₂ E₂₃ : B}
    (h12 : E₁₂ * E₁₂ = -1) (h_anti : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0) :
    (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = 2 * (E₁₂ + E₂₃) := by
  have h12' : E₁₂ * E₁₂ + 1 = 0 := by
    calc
      E₁₂ * E₁₂ + 1 = -1 + 1 := by rw [h12]
      _ = 0 := by simp
  calc (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂)
    _ = 2 * (E₁₂ + E₂₃) + (E₁₂ * E₁₂ + 1) * (1 - E₂₃) +
        (1 + E₁₂) * (E₁₂ * E₂₃ + E₂₃ * E₁₂) := by
      calc
        (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂)
          = (1 + E₁₂ + E₂₃ + E₁₂ * E₂₃) * (1 + E₁₂) := by
            simp [mul_add, add_mul, mul_one, one_mul]
            <;> abel
        _ = (1 + E₁₂) * (1 + E₁₂) + (E₂₃ + E₁₂ * E₂₃) * (1 + E₁₂) := by
          simp [add_mul, mul_add, mul_one, one_mul]
          <;> abel
        _ = (1 + E₁₂ + E₁₂ + E₁₂ * E₁₂) + (E₂₃ + E₁₂ * E₂₃) * (1 + E₁₂) := by
          simp [mul_add, add_mul, mul_one, one_mul]
          <;> abel
        _ = 1 + E₁₂ + E₁₂ + E₁₂ * E₁₂ + (E₂₃ * 1 + E₂₃ * E₁₂ + E₁₂ * E₂₃ * 1 + E₁₂ * E₂₃ * E₁₂) := by
          simp [mul_add, add_mul, mul_one, one_mul]
          <;> abel
        _ = 1 + E₁₂ + E₁₂ + E₁₂ * E₁₂ + (E₂₃ + E₂₃ * E₁₂ + E₁₂ * E₂₃ + E₁₂ * E₂₃ * E₁₂) := by
          simp [mul_one]
          <;> abel
        _ = 2 * (E₁₂ + E₂₃) + (E₁₂ * E₁₂ + 1) * (1 - E₂₃) +
            (1 + E₁₂) * (E₁₂ * E₂₃ + E₂₃ * E₁₂) := by
          noncomm_ring
    _ = 2 * (E₁₂ + E₂₃) + 0 * (1 - E₂₃) + (1 + E₁₂) * 0 := by rw [h12', h_anti]
    _ = 2 * (E₁₂ + E₂₃) := by
      noncomm_ring

theorem clifford_artin_braid_relation {B : Type*} [Ring B] {E₁₂ E₂₃ : B}
    (h12 : E₁₂ * E₁₂ = -1) (h23 : E₂₃ * E₂₃ = -1)
    (h_anti : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0) :
    (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = (1 + E₂₃) * (1 + E₁₂) * (1 + E₂₃) := by
  have h_anti' : E₂₃ * E₁₂ + E₁₂ * E₂₃ = 0 := by rw [add_comm, h_anti]
  have h₁ : (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = 2 * (E₁₂ + E₂₃) := clifford_bivector_triple_product h12 h_anti
  have h₂ : (1 + E₂₃) * (1 + E₁₂) * (1 + E₂₃) = 2 * (E₂₃ + E₁₂) := clifford_bivector_triple_product h23 h_anti'
  calc
    (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = 2 * (E₁₂ + E₂₃) := h₁
    _ = 2 * (E₂₃ + E₁₂) := by
      simp [two_mul, add_comm]
      <;> abel
    _ = (1 + E₂₃) * (1 + E₁₂) * (1 + E₂₃) := by rw [h₂]

/- **Quaternionic Artin braid and bracket theorem in the nested operator algebra**.

For every coefficient ring `B`, the nested operator matrices satisfy the braid relation and
their associative bracket is twice the third quaternion generator.  The differential Bianchi
identity is stated separately for arbitrary derivations above; this theorem does not specialize
it to zero derivations, and it does not attach a separate commutative coefficient example. -/
theorem master_braid_and_quaternion_bracket {B : Type*} [Ring B] :
    (R₁₂ : NestedMat B) * R₂₃ * R₁₂ = R₂₃ * R₁₂ * R₂₃ ∧
      ⁅(R₁₂ : NestedMat B), R₂₃⁆ =
        (2 : ℕ) • quaternionE₃ (B := B) := by
  rcases quaternionE₁_E₂_relations (B := B) with ⟨hE₁, hE₂, hAnti⟩
  constructor
  · exact clifford_artin_braid_relation hE₁ hE₂ hAnti
  · simpa [R₁₂, R₂₃, Ring.lie_def] using quaternionRotor_commutator (B := B)

end ArchetypeA9_MasterSynthesis

end GrandUnifiedNoncommutativeOperatorSynthesis
