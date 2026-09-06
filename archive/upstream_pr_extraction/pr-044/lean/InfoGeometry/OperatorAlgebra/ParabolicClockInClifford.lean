import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.DualNumber
import InfoGeometry.Algebraic.SplitQuadraticForm
import InfoGeometry.OperatorAlgebra.CliffordCAR

open CategoryTheory InfoGeometry.Algebraic.SplitSignature
open InfoGeometry.OperatorAlgebra.CliffordCAR

noncomputable section

namespace InfoGeometry.OperatorAlgebra

-- Stage 1: Eliminate Structural Vacuum Holes 1-4
abbrev ParabolicClockAlg : Type := DualNumber ℝ

def ε : ParabolicClockAlg := DualNumber.eps

lemma ε_sq_zero : ε * ε = 0 := DualNumber.eps_mul_eps

-- Stage 2: Constructive Embedding into Cl(1,1)
def cl11_nilpotent : CliffordAlgebra (splitQuadraticForm 1) :=
  CliffordAlgebra.ι (splitQuadraticForm 1) (splitBasisVector (Sum.inl 0)) +
  CliffordAlgebra.ι (splitQuadraticForm 1) (splitBasisVector (Sum.inr 0))

lemma cl11_nilpotent_sq_zero : cl11_nilpotent * cl11_nilpotent = 0 := by
  have h₁ : posG 1 0 * posG 1 0 = 1 := by simpa using p_sq 1 0
  have h₂ : negG 1 0 * negG 1 0 = -1 := by simpa using n_sq 1 0
  have h₃ : posG 1 0 * negG 1 0 + negG 1 0 * posG 1 0 = 0 := by
    simpa using pos_neg_anticomm 1 0 0
  have h₄ : (posG 1 0 + negG 1 0) * (posG 1 0 + negG 1 0) =
      posG 1 0 * posG 1 0 + posG 1 0 * negG 1 0 + negG 1 0 * posG 1 0 + negG 1 0 * negG 1 0 := by
    calc
      (posG 1 0 + negG 1 0) * (posG 1 0 + negG 1 0) =
          posG 1 0 * (posG 1 0 + negG 1 0) + negG 1 0 * (posG 1 0 + negG 1 0) := by
        rw [add_mul]
      _ = posG 1 0 * posG 1 0 + posG 1 0 * negG 1 0 +
            (negG 1 0 * posG 1 0 + negG 1 0 * negG 1 0) := by
        rw [mul_add, mul_add]
      _ = posG 1 0 * posG 1 0 + posG 1 0 * negG 1 0 + negG 1 0 * posG 1 0 + negG 1 0 * negG 1 0 := by
        abel
  calc
    cl11_nilpotent * cl11_nilpotent
        = (posG 1 0 + negG 1 0) * (posG 1 0 + negG 1 0) := by
            simp [cl11_nilpotent, posG, negG, pVec, nVec]
    _ = posG 1 0 * posG 1 0 + posG 1 0 * negG 1 0 + negG 1 0 * posG 1 0 + negG 1 0 * negG 1 0 := by
            rw [h₄]
    _ = 1 + posG 1 0 * negG 1 0 + negG 1 0 * posG 1 0 + (-1) := by rw [h₁, h₂]
    _ = (posG 1 0 * negG 1 0 + negG 1 0 * posG 1 0) := by abel
    _ = 0 := h₃

-- Create the required Subtype bundle for DualNumber.lift
def cl11_nilpotent_bundle : { fe : (ℝ →ₐ[ℝ] CliffordAlgebra (splitQuadraticForm 1)) × CliffordAlgebra (splitQuadraticForm 1) // fe.2 * fe.2 = 0 ∧ ∀ (a : ℝ), Commute fe.2 (fe.1 a) } :=
  ⟨(Algebra.ofId ℝ _, cl11_nilpotent), by
    constructor
    · exact cl11_nilpotent_sq_zero
    · intro r
      exact Algebra.commute_algebraMap_right r cl11_nilpotent⟩

def embed_parabolic_to_Cl11 : ParabolicClockAlg →ₐ[ℝ] CliffordAlgebra (splitQuadraticForm 1) :=
  DualNumber.lift cl11_nilpotent_bundle

lemma embed_preserves_nilpotent : (embed_parabolic_to_Cl11 ε) * (embed_parabolic_to_Cl11 ε) = 0 := by
  rw [← map_mul, ε_sq_zero, map_zero]

-- Stage 3: Constructive Embedding into Cl(n,n)
def clnn_nilpotent {n : ℕ} (hn : 1 ≤ n) : CliffordAlgebra (splitQuadraticForm n) :=
  CliffordAlgebra.ι (splitQuadraticForm n) (splitBasisVector (Sum.inl ⟨0, by omega⟩)) +
  CliffordAlgebra.ι (splitQuadraticForm n) (splitBasisVector (Sum.inr ⟨0, by omega⟩))

lemma clnn_nilpotent_sq_zero {n : ℕ} (hn : 1 ≤ n) : clnn_nilpotent hn * clnn_nilpotent hn = 0 := by
  let i : Fin n := ⟨0, hn⟩
  have h₁ : posG n i * posG n i = 1 := by simpa [i] using p_sq n i
  have h₂ : negG n i * negG n i = -1 := by simpa [i] using n_sq n i
  have h₃ : posG n i * negG n i + negG n i * posG n i = 0 := by
    simpa [i] using pos_neg_anticomm n i i
  have h₄ : (posG n i + negG n i) * (posG n i + negG n i) =
      posG n i * posG n i + posG n i * negG n i + negG n i * posG n i + negG n i * negG n i := by
    calc
      (posG n i + negG n i) * (posG n i + negG n i) =
          posG n i * (posG n i + negG n i) + negG n i * (posG n i + negG n i) := by
        rw [add_mul]
      _ = posG n i * posG n i + posG n i * negG n i +
            (negG n i * posG n i + negG n i * negG n i) := by
        rw [mul_add, mul_add]
      _ = posG n i * posG n i + posG n i * negG n i + negG n i * posG n i + negG n i * negG n i := by
        abel
  calc
    clnn_nilpotent hn * clnn_nilpotent hn
        = (posG n i + negG n i) * (posG n i + negG n i) := by
            simp [clnn_nilpotent, posG, negG, pVec, nVec, i]
    _ = posG n i * posG n i + posG n i * negG n i + negG n i * posG n i + negG n i * negG n i := by
            rw [h₄]
    _ = 1 + posG n i * negG n i + negG n i * posG n i + (-1) := by rw [h₁, h₂]
    _ = (posG n i * negG n i + negG n i * posG n i) := by abel
    _ = 0 := h₃

def clnn_nilpotent_bundle {n : ℕ} (hn : 1 ≤ n) : { fe : (ℝ →ₐ[ℝ] CliffordAlgebra (splitQuadraticForm n)) × CliffordAlgebra (splitQuadraticForm n) // fe.2 * fe.2 = 0 ∧ ∀ (a : ℝ), Commute fe.2 (fe.1 a) } :=
  ⟨(Algebra.ofId ℝ _, clnn_nilpotent hn), by
    constructor
    · exact clnn_nilpotent_sq_zero hn
    · intro r
      exact Algebra.commute_algebraMap_right r (clnn_nilpotent hn)⟩

def embed_parabolic_to_Clnn {n : ℕ} (hn : 1 ≤ n) : ParabolicClockAlg →ₐ[ℝ] CliffordAlgebra (splitQuadraticForm n) :=
  DualNumber.lift (clnn_nilpotent_bundle hn)

-- Stage 4: Remove the `False` existential
theorem parabolic_clock_in_clifford_n {n : ℕ} (hn : 1 ≤ n) :
    ∃ x : CliffordAlgebra (splitQuadraticForm n), x * x = 0 :=
  ⟨embed_parabolic_to_Clnn hn ε, by
    rw [← map_mul, ε_sq_zero, map_zero]⟩

end InfoGeometry.OperatorAlgebra
