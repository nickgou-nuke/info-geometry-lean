import InfoGeometry.Physics.ChiralPoincareSouriauBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Indexed chiral supercharge multiplets

This owner separates the two Weyl charge rails from the even momentum rail.
It proves only the finite associative soldering statement: pointwise mixed
anticommutators assemble into the Pauli operator matrix.  A realization of
the hypotheses by Cuntz generators and Lorentz covariance are separate facts.
-/

noncomputable section

namespace InfoGeometry.Algebra.ChiralSuperchargeMultiplet

open Matrix

variable {A : Type*} [Ring A] [Algebra ℂ A]

abbrev M2A (R : Type*) := Matrix (Fin 2) (Fin 2) R

structure Data where
  QL : Fin 2 → A
  QR : Fin 2 → A
  P : Fin 4 → A

def anticommutator (x y : A) : A := x * y + y * x

def mixedMomentum (M : Data (A := A)) : M2A A :=
  !![((1 / 2 : ℂ) • anticommutator (M.QL 0) (M.QR 0)),
      ((1 / 2 : ℂ) • anticommutator (M.QL 0) (M.QR 1));
      ((1 / 2 : ℂ) • anticommutator (M.QL 1) (M.QR 0)),
      ((1 / 2 : ℂ) • anticommutator (M.QL 1) (M.QR 1))]

def pauliOperatorMomentum (P : Fin 4 → A) : M2A A :=
  !![P 0 + P 3, P 1 - Complex.I • P 2;
     P 1 + Complex.I • P 2, P 0 - P 3]

/-- Factorized left chiral charge `Q_α = λ_α q`. -/
def factorizedLeft (lambda : Fin 2 → ℂ) (q : A) : Fin 2 → A :=
  fun α => lambda α • q

/-- Factorized right chiral charge `Q̄_β = μ_β q̄`. -/
def factorizedRight (mu : Fin 2 → ℂ) (qbar : A) : Fin 2 → A :=
  fun β => mu β • qbar

/-- Rank-one momentum matrix associated with two spinor coefficient vectors. -/
def rankOneMomentum (lambda mu : Fin 2 → ℂ) : M2A A :=
  !![(lambda 0 * mu 0) • (1 : A), (lambda 0 * mu 1) • (1 : A);
     (lambda 1 * mu 0) • (1 : A), (lambda 1 * mu 1) • (1 : A)]

/-- The mixed anticommutator of factorized chiral charges is rank one. -/
theorem factorized_mixed_anticommutator
    (lambda mu : Fin 2 → ℂ) (q qbar : A) (P : Fin 4 → A)
    (h : anticommutator q qbar = (2 : ℂ) • (1 : A)) :
    (let M : Data (A := A) :=
     { QL := factorizedLeft lambda q
       QR := factorizedRight mu qbar
       P := P }
     mixedMomentum M) =
      rankOneMomentum (A := A) lambda mu := by
  have h' : q * qbar + qbar * q = (2 : ℂ) • (1 : A) := by
    simpa [anticommutator] using h
  have hfactor (a b : ℂ) :
      (1 / 2 : ℂ) •
          ((a • q) * (b • qbar) + (b • qbar) * (a • q)) =
        (a * b) • (1 : A) := by
    calc
      (1 / 2 : ℂ) •
          ((a • q) * (b • qbar) + (b • qbar) * (a • q)) =
          ((a * b) / 2 : ℂ) • (q * qbar + qbar * q) := by
            simp only [smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
            congr 1 <;> ring_nf
      _ = (a * b) • (1 : A) := by
        rw [h']
        module
  dsimp [mixedMomentum, factorizedLeft, factorizedRight,
    rankOneMomentum]
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
    | simpa [anticommutator, smul_mul_assoc, mul_smul_comm, smul_smul] using
        hfactor (lambda 0) (mu 0)
    | simpa [anticommutator, smul_mul_assoc, mul_smul_comm, smul_smul] using
        hfactor (lambda 0) (mu 1)
    | simpa [anticommutator, smul_mul_assoc, mul_smul_comm, smul_smul] using
        hfactor (lambda 1) (mu 0)
    | simpa [anticommutator, smul_mul_assoc, mul_smul_comm, smul_smul] using
        hfactor (lambda 1) (mu 1)

theorem mixedMomentum_eq_pauliOperatorMomentum
    (M : Data (A := A))
    (h : ∀ α β : Fin 2,
      anticommutator (M.QL α) (M.QR β) =
        (2 : ℂ) • (pauliOperatorMomentum M.P α β)) :
    mixedMomentum M = pauliOperatorMomentum M.P := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [mixedMomentum, anticommutator] using congrArg (fun x : A => (1 / 2 : ℂ) • x) (h 0 0)
  · simpa [mixedMomentum, anticommutator] using congrArg (fun x : A => (1 / 2 : ℂ) • x) (h 0 1)
  · simpa [mixedMomentum, anticommutator] using congrArg (fun x : A => (1 / 2 : ℂ) • x) (h 1 0)
  · simpa [mixedMomentum, anticommutator] using congrArg (fun x : A => (1 / 2 : ℂ) • x) (h 1 1)

/-! The trace isolates the scalar Pauli channel.  This is the finite
matrix readout of the mixed supercharge relation, not an identification
of the full matrix with a scalar. -/

theorem trace_mixedMomentum_eq_two_smul_scalar
    (M : Data (A := A))
    (h : ∀ α β : Fin 2,
      anticommutator (M.QL α) (M.QR β) =
        (2 : ℂ) • (pauliOperatorMomentum M.P α β)) :
    Matrix.trace (mixedMomentum M) = (2 : ℂ) • M.P 0 := by
  rw [mixedMomentum_eq_pauliOperatorMomentum M h]
  simp [pauliOperatorMomentum, Matrix.trace, Fin.sum_univ_two]
  rw [two_smul]

theorem mixedMomentum_component_readout
    (M : Data (A := A))
    (h : mixedMomentum M = pauliOperatorMomentum M.P) :
    (1 / 2 : ℂ) • anticommutator (M.QL 0) (M.QR 0) = M.P 0 + M.P 3 ∧
    (1 / 2 : ℂ) • anticommutator (M.QL 0) (M.QR 1) =
      M.P 1 - Complex.I • M.P 2 ∧
    (1 / 2 : ℂ) • anticommutator (M.QL 1) (M.QR 0) =
      M.P 1 + Complex.I • M.P 2 ∧
    (1 / 2 : ℂ) • anticommutator (M.QL 1) (M.QR 1) = M.P 0 - M.P 3 := by
  have h00 := congrArg (fun X : M2A A => X 0 0) h
  have h01 := congrArg (fun X : M2A A => X 0 1) h
  have h10 := congrArg (fun X : M2A A => X 1 0) h
  have h11 := congrArg (fun X : M2A A => X 1 1) h
  simp [mixedMomentum, pauliOperatorMomentum] at h00 h01 h10 h11
  have hhalf : (1 / 2 : ℂ) = (2 : ℂ)⁻¹ := by norm_num
  rw [hhalf] at *
  exact ⟨h00, h01, h10, h11⟩

theorem same_chirality_square_zero
    (M : Data (A := A))
    (hL : ∀ α β : Fin 2, anticommutator (M.QL α) (M.QL β) = 0)
    (hR : ∀ α β : Fin 2, anticommutator (M.QR α) (M.QR β) = 0) :
    (∀ α : Fin 2, M.QL α * M.QL α = 0) ∧
      (∀ α : Fin 2, M.QR α * M.QR α = 0) := by
  constructor
  · intro α
    have h₁ := congrArg (fun x : A => (2 : ℂ) • x) (hL α α)
    have h₂ := congrArg (fun x : A => (1 / 2 : ℂ) • x) h₁
    have hsum : M.QL α * M.QL α + M.QL α * M.QL α = 0 := by
      simpa [anticommutator, smul_add, smul_smul] using h₂
    have h₃ := congrArg (fun x : A => (1 / 2 : ℂ) • x) hsum
    simp only [smul_add, map_zero] at h₃
    rw [← add_smul] at h₃
    norm_num at h₃
    exact h₃
  · intro α
    have h₁ := congrArg (fun x : A => (2 : ℂ) • x) (hR α α)
    have h₂ := congrArg (fun x : A => (1 / 2 : ℂ) • x) h₁
    have hsum : M.QR α * M.QR α + M.QR α * M.QR α = 0 := by
      simpa [anticommutator, smul_add, smul_smul] using h₂
    have h₃ := congrArg (fun x : A => (1 / 2 : ℂ) • x) hsum
    simp only [smul_add, map_zero] at h₃
    rw [← add_smul] at h₃
    norm_num at h₃
    exact h₃

end InfoGeometry.Algebra.ChiralSuperchargeMultiplet
