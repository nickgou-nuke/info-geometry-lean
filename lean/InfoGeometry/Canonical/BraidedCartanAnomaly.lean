import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

namespace InfoGeometry.BraidedCartanAnomaly

variable {R : Type*} [CommRing R]
variable {Γ : Type*} [AddCommGroup Γ]
variable {A : Type*} [Ring A] [Algebra R A]

structure UnifiedBicharacter (Γ : Type*) [AddCommGroup Γ] (R : Type*) [CommRing R] where
  β : Γ → Γ → Rˣ
  map_add_left : ∀ g₁ g₂ h : Γ, β (g₁ + g₂) h = β g₁ h * β g₂ h
  map_add_right : ∀ g h₁ h₂ : Γ, β g (h₁ + h₂) = β g h₁ * β g h₂

instance : CoeFun (UnifiedBicharacter Γ R) (fun _ => Γ → Γ → R) where
  coe B g h := (B.β g h : R)

def braidedComm (B : UnifiedBicharacter Γ R) (gx gy : Γ) (x y : A) : A :=
  x * y - (B.β gx gy : R) • (y * x)

def associator (x y z : A) : A :=
  (x * y) * z - x * (y * z)

def braidedJacobiator (B : UnifiedBicharacter Γ R) (gx gy gz : Γ) (x y z : A) : A :=
  braidedComm B gx (gy + gz) x (braidedComm B gy gz y z) -
  braidedComm B (gx + gy) gz (braidedComm B gx gy x y) z -
  (B.β gx gy : R) • braidedComm B gy (gx + gz) y (braidedComm B gx gz x z)

theorem braided_jacobi_identity_associative
    (B : UnifiedBicharacter Γ R)
    (h_symm : ∀ g h : Γ, (B.β g h : R) * (B.β h g : R) = 1)
    (gx gy gz : Γ) (x y z : A)
    (h_assoc : ∀ a b c : A, (a * b) * c = a * (b * c)) :
    braidedJacobiator B gx gy gz x y z = 0 := by
  dsimp [braidedJacobiator, braidedComm]
  have h_add_yz : (B.β gx (gy + gz) : R) = (B.β gx gy : R) * (B.β gx gz : R) := by
    rw [B.map_add_right, Units.val_mul]
  have h_add_xy : (B.β (gx + gy) gz : R) = (B.β gx gz : R) * (B.β gy gz : R) := by
    rw [B.map_add_left, Units.val_mul]
  have h_add_xz : (B.β gy (gx + gz) : R) = (B.β gy gx : R) * (B.β gy gz : R) := by
    rw [B.map_add_right, Units.val_mul]
  have h_cross : (B.β gx gy : R) * (B.β gy gx : R) = 1 := h_symm gx gy
  
  rw [h_add_yz, h_add_xy, h_add_xz]
  simp only [sub_mul, mul_sub, smul_sub, smul_smul,
             Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  repeat rw [h_assoc]
  
  have h_cancel1 : (B.β gx gy : R) * ((B.β gy gx : R) * (B.β gy gz : R)) = (B.β gy gz : R) := by
    calc (B.β gx gy : R) * ((B.β gy gx : R) * (B.β gy gz : R))
        = ((B.β gx gy : R) * (B.β gy gx : R)) * (B.β gy gz : R) := by rw [← mul_assoc]
      _ = 1 * (B.β gy gz : R) := by rw [h_cross]
      _ = (B.β gy gz : R) := one_mul _
      
  have h_cancel2 : (B.β gx gy : R) * ((B.β gy gx : R) * (B.β gy gz : R) * (B.β gx gz : R)) =
      (B.β gx gz : R) * (B.β gy gz : R) := by
    calc (B.β gx gy : R) * ((B.β gy gx : R) * (B.β gy gz : R) * (B.β gx gz : R))
        = ((B.β gx gy : R) * (B.β gy gx : R)) * ((B.β gy gz : R) * (B.β gx gz : R)) := by ring
      _ = 1 * ((B.β gy gz : R) * (B.β gx gz : R)) := by rw [h_cross]
      _ = (B.β gx gz : R) * (B.β gy gz : R) := by ring
      
  have h_cancel3 : (B.β gx gz : R) * (B.β gy gz : R) * (B.β gx gy : R) =
      (B.β gx gy : R) * (B.β gx gz : R) * (B.β gy gz : R) := by ring
      
  rw [h_cancel1, h_cancel2, h_cancel3]
  abel

theorem braided_jacobiator_eq_associator_defect
    (B : UnifiedBicharacter Γ R)
    (h_symm : ∀ g h : Γ, (B.β g h : R) * (B.β h g : R) = 1)
    (gx gy gz : Γ) (x y z : A)
    (h_assoc_zero : ∀ a b c : A, associator a b c = 0) :
    braidedJacobiator B gx gy gz x y z = 0 := by
  have h_assoc : ∀ a b c : A, (a * b) * c = a * (b * c) := by
    intro a b c
    have h := h_assoc_zero a b c
    dsimp [associator] at h
    exact sub_eq_zero.mp h
  exact braided_jacobi_identity_associative B h_symm gx gy gz x y z h_assoc

abbrev PhaseSpace := ℤ × ℤ

def symplecticOmega (w₁ w₂ : PhaseSpace) : ℤ :=
  w₁.1 * w₂.2 - w₁.2 * w₂.1

theorem symplecticOmega_skew (w₁ w₂ : PhaseSpace) :
    symplecticOmega w₂ w₁ = - symplecticOmega w₁ w₂ := by
  dsimp [symplecticOmega]
  ring

theorem sylvester_braided_inversion (w₁ w₂ : PhaseSpace) :
    symplecticOmega w₁ w₂ + symplecticOmega w₂ w₁ = 0 := by
  dsimp [symplecticOmega]
  ring

end InfoGeometry.BraidedCartanAnomaly
