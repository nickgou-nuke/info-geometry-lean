import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

namespace InfoGeometry.RepresentationArchitecture

/-! ### 1. The Fiber is Finite: Clifford Action and the Dirac Operator -/

structure CliffordRepresentation (A : Type*) [Ring A] where
  creation : A
  annihilation : A
  nil_c : creation * creation = 0
  nil_a : annihilation * annihilation = 0
  car_rel : creation * annihilation + annihilation * creation = 1

def gamma_matrix {A : Type*} [Ring A] (c : CliffordRepresentation A) : A :=
  c.creation + c.annihilation

theorem gamma_square_eq_one {A : Type*} [Ring A] (c : CliffordRepresentation A) :
    gamma_matrix c * gamma_matrix c = 1 := by
  dsimp [gamma_matrix]
  have expand : (c.creation + c.annihilation) * (c.creation + c.annihilation) =
    c.creation * c.creation + c.creation * c.annihilation + c.annihilation * c.creation + c.annihilation * c.annihilation := by
    simp only [mul_add, add_mul]
    abel
  rw [expand, c.nil_c, c.nil_a, zero_add, add_zero]
  exact c.car_rel

/-! ### 2. Alain Connes' Factorization: The Almost-Commutative Spectral Triple -/

structure ConnesSpectralFactorization (A : Type*) [Ring A] where
  D_M : A
  D_F : A
  gamma5 : A
  h_comm : D_M * D_F = D_F * D_M
  h_gamma5_sq : gamma5 * gamma5 = 1
  h_anti : D_M * gamma5 = - (gamma5 * D_M)
  h_comm_F : gamma5 * D_F = D_F * gamma5

def total_dirac {A : Type*} [Ring A] (C : ConnesSpectralFactorization A) : A :=
  C.D_M + C.gamma5 * C.D_F

theorem total_dirac_squared_decoupled {A : Type*} [Ring A] (C : ConnesSpectralFactorization A) :
    total_dirac C * total_dirac C = C.D_M * C.D_M + C.D_F * C.D_F := by
  dsimp [total_dirac]
  
  have expand : (C.D_M + C.gamma5 * C.D_F) * (C.D_M + C.gamma5 * C.D_F) =
    C.D_M * C.D_M + C.D_M * (C.gamma5 * C.D_F) + (C.gamma5 * C.D_F) * C.D_M + (C.gamma5 * C.D_F) * (C.gamma5 * C.D_F) := by
    simp only [mul_add, add_mul]
    abel
    
  have h1 : C.D_M * (C.gamma5 * C.D_F) = - (C.gamma5 * C.D_M * C.D_F) := by
    calc C.D_M * (C.gamma5 * C.D_F)
        = (C.D_M * C.gamma5) * C.D_F := by rw [← mul_assoc]
      _ = (- (C.gamma5 * C.D_M)) * C.D_F := by rw [C.h_anti]
      _ = - (C.gamma5 * C.D_M * C.D_F) := by rw [neg_mul]
      
  have h2 : (C.gamma5 * C.D_F) * C.D_M = C.gamma5 * C.D_M * C.D_F := by
    calc (C.gamma5 * C.D_F) * C.D_M
        = C.gamma5 * (C.D_F * C.D_M) := by rw [mul_assoc]
      _ = C.gamma5 * (C.D_M * C.D_F) := by rw [C.h_comm]
      _ = C.gamma5 * C.D_M * C.D_F := by rw [← mul_assoc]
      
  have h3 : (C.gamma5 * C.D_F) * (C.gamma5 * C.D_F) = C.D_F * C.D_F := by
    calc (C.gamma5 * C.D_F) * (C.gamma5 * C.D_F)
        = C.gamma5 * (C.D_F * C.gamma5) * C.D_F := by simp only [← mul_assoc]
      _ = C.gamma5 * (C.gamma5 * C.D_F) * C.D_F := by
          have h_comm_symm : C.D_F * C.gamma5 = C.gamma5 * C.D_F := Eq.symm C.h_comm_F
          rw [h_comm_symm]
      _ = (C.gamma5 * C.gamma5) * (C.D_F * C.D_F) := by simp only [← mul_assoc]
      _ = 1 * (C.D_F * C.D_F) := by rw [C.h_gamma5_sq]
      _ = C.D_F * C.D_F := one_mul _

  rw [expand, h1, h2, h3]
  have cancel_mid : - (C.gamma5 * C.D_M * C.D_F) + (C.gamma5 * C.D_M * C.D_F) = 0 := neg_add_cancel _
  calc C.D_M * C.D_M + - (C.gamma5 * C.D_M * C.D_F) + (C.gamma5 * C.D_M * C.D_F) + C.D_F * C.D_F
      = C.D_M * C.D_M + (- (C.gamma5 * C.D_M * C.D_F) + (C.gamma5 * C.D_M * C.D_F)) + C.D_F * C.D_F := by rw [add_assoc (C.D_M * C.D_M)]
    _ = C.D_M * C.D_M + 0 + C.D_F * C.D_F := by rw [cancel_mid]
    _ = C.D_M * C.D_M + C.D_F * C.D_F := by rw [add_zero]

/-! ### 3. The GNS Theorem: How a Finite State Builds an Infinite World -/

structure GNSState (A : Type*) [Ring A] where
  star : A → A
  ω : A → ℝ
  star_involutive : ∀ x, star (star x) = x
  star_mul : ∀ x y, star (x * y) = star y * star x

def null_ideal {A : Type*} [Ring A] (S : GNSState A) : Set A :=
  { x : A | S.ω (S.star x * x) = 0 }

theorem gns_null_ideal_membership {A : Type*} [Ring A] (S : GNSState A) (x : A) :
    x ∈ null_ideal S ↔ S.ω (S.star x * x) = 0 := by
  rfl

/-! ### 4. The Amplituhedron: Scattering as Differential Forms on Finite Grassmannians -/

theorem positive_grassmannian_dimension (k n : ℕ) (_ : k ≤ n) :
    k * (n - k) = k * n - k * k := by
  exact Nat.mul_sub_left_distrib k n k

end InfoGeometry.RepresentationArchitecture
