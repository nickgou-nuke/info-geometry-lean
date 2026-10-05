import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

namespace InfoGeometry.BraidedCartanAnomaly

variable {R : Type*} [CommRing R]
variable {Γ : Type*} [AddCommGroup Γ]
variable {A : Type*} [Ring A] [Algebra R A]

/-! A bicharacter is represented by Mathlib's iterated multiplicative
homomorphisms. `Multiplicative` converts the additive grading law to the
monoid-homomorphism law, so multiplicativity is part of the native carrier. -/
abbrev UnifiedBicharacter (Γ : Type*) [AddCommGroup Γ] (R : Type*) [CommRing R] :=
  Multiplicative Γ →* (Multiplicative Γ →* Rˣ)

def bicharacterValue (B : UnifiedBicharacter Γ R) (g h : Γ) : Rˣ :=
  B (Multiplicative.ofAdd g) (Multiplicative.ofAdd h)

lemma bicharacterValue_add_left (B : UnifiedBicharacter Γ R) (g₁ g₂ h : Γ) :
    bicharacterValue B (g₁ + g₂) h = bicharacterValue B g₁ h * bicharacterValue B g₂ h := by
  have hm := B.map_mul (Multiplicative.ofAdd g₁) (Multiplicative.ofAdd g₂)
  have he := congrArg (fun f : Multiplicative Γ →* Rˣ => f (Multiplicative.ofAdd h)) hm
  simpa [bicharacterValue] using he

lemma bicharacterValue_add_right (B : UnifiedBicharacter Γ R) (g h₁ h₂ : Γ) :
    bicharacterValue B g (h₁ + h₂) = bicharacterValue B g h₁ * bicharacterValue B g h₂ := by
  exact (B (Multiplicative.ofAdd g)).map_mul (Multiplicative.ofAdd h₁) (Multiplicative.ofAdd h₂)

def braidedComm (B : UnifiedBicharacter Γ R) (gx gy : Γ) (x y : A) : A :=
  x * y - (bicharacterValue B gx gy : R) • (y * x)

def associator (x y z : A) : A :=
  (x * y) * z - x * (y * z)

def braidedJacobiator (B : UnifiedBicharacter Γ R) (gx gy gz : Γ) (x y z : A) : A :=
  braidedComm B gx (gy + gz) x (braidedComm B gy gz y z) -
  braidedComm B (gx + gy) gz (braidedComm B gx gy x y) z -
  (bicharacterValue B gx gy : R) • braidedComm B gy (gx + gz) y (braidedComm B gx gz x z)

theorem braided_jacobi_identity_associative
    (B : UnifiedBicharacter Γ R)
    (h_symm : ∀ g h : Γ, (bicharacterValue B g h : R) * (bicharacterValue B h g : R) = 1)
    (gx gy gz : Γ) (x y z : A)
    (h_assoc : ∀ a b c : A, (a * b) * c = a * (b * c)) :
    braidedJacobiator B gx gy gz x y z = 0 := by
  dsimp [braidedJacobiator, braidedComm]
  have h_add_yz : (bicharacterValue B gx (gy + gz) : R) =
      (bicharacterValue B gx gy : R) * (bicharacterValue B gx gz : R) := by
    exact congrArg (fun u : Rˣ => (u : R)) (bicharacterValue_add_right B gx gy gz)
  have h_add_xy : (bicharacterValue B (gx + gy) gz : R) =
      (bicharacterValue B gx gz : R) * (bicharacterValue B gy gz : R) := by
    exact congrArg (fun u : Rˣ => (u : R)) (bicharacterValue_add_left B gx gy gz)
  have h_add_xz : (bicharacterValue B gy (gx + gz) : R) =
      (bicharacterValue B gy gx : R) * (bicharacterValue B gy gz : R) := by
    exact congrArg (fun u : Rˣ => (u : R)) (bicharacterValue_add_right B gy gx gz)
  have h_cross : (bicharacterValue B gx gy : R) * (bicharacterValue B gy gx : R) = 1 := h_symm gx gy
  
  rw [h_add_yz, h_add_xy, h_add_xz]
  simp only [sub_mul, mul_sub, smul_sub, smul_smul,
             Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  repeat rw [h_assoc]
  
  have h_cancel1 : (bicharacterValue B gx gy : R) *
      ((bicharacterValue B gy gx : R) * (bicharacterValue B gy gz : R)) =
      (bicharacterValue B gy gz : R) := by
    calc (bicharacterValue B gx gy : R) *
          ((bicharacterValue B gy gx : R) * (bicharacterValue B gy gz : R))
        = ((bicharacterValue B gx gy : R) * (bicharacterValue B gy gx : R)) *
            (bicharacterValue B gy gz : R) := by rw [← mul_assoc]
      _ = 1 * (bicharacterValue B gy gz : R) := by rw [h_cross]
      _ = (bicharacterValue B gy gz : R) := one_mul _
      
  have h_cancel2 : (bicharacterValue B gx gy : R) *
      ((bicharacterValue B gy gx : R) * (bicharacterValue B gy gz : R) *
        (bicharacterValue B gx gz : R)) =
      (bicharacterValue B gx gz : R) * (bicharacterValue B gy gz : R) := by
    calc (bicharacterValue B gx gy : R) *
          ((bicharacterValue B gy gx : R) * (bicharacterValue B gy gz : R) *
            (bicharacterValue B gx gz : R))
        = ((bicharacterValue B gx gy : R) * (bicharacterValue B gy gx : R)) *
            ((bicharacterValue B gy gz : R) * (bicharacterValue B gx gz : R)) := by ring
      _ = 1 * ((bicharacterValue B gy gz : R) * (bicharacterValue B gx gz : R)) := by rw [h_cross]
      _ = (bicharacterValue B gx gz : R) * (bicharacterValue B gy gz : R) := by ring
      
  have h_cancel3 : (bicharacterValue B gx gz : R) * (bicharacterValue B gy gz : R) *
      (bicharacterValue B gx gy : R) =
      (bicharacterValue B gx gy : R) * (bicharacterValue B gx gz : R) *
        (bicharacterValue B gy gz : R) := by ring
      
  rw [h_cancel1, h_cancel2, h_cancel3]
  abel

theorem braided_jacobiator_eq_associator_defect
    (B : UnifiedBicharacter Γ R)
    (h_symm : ∀ g h : Γ,
      (bicharacterValue B g h : R) * (bicharacterValue B h g : R) = 1)
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

lemma symplecticOmega_add_left (u v w : PhaseSpace) :
    symplecticOmega (u + v) w = symplecticOmega u w + symplecticOmega v w := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  rcases w with ⟨w₁, w₂⟩
  simp [symplecticOmega]
  ring

lemma symplecticOmega_add_right (u v w : PhaseSpace) :
    symplecticOmega u (v + w) = symplecticOmega u v + symplecticOmega u w := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  rcases w with ⟨w₁, w₂⟩
  simp [symplecticOmega]
  ring

/-! The phase-space bicharacter `q ^ Ω(w₁,w₂)` and its multiplicativity laws. -/
def phaseBicharacter (q : Rˣ) (w₁ w₂ : PhaseSpace) : Rˣ :=
  q ^ symplecticOmega w₁ w₂

theorem phaseBicharacter_add_left (q : Rˣ) (u v w : PhaseSpace) :
    phaseBicharacter q (u + v) w = phaseBicharacter q u w * phaseBicharacter q v w := by
  unfold phaseBicharacter
  rw [symplecticOmega_add_left, zpow_add]

theorem phaseBicharacter_add_right (q : Rˣ) (u v w : PhaseSpace) :
    phaseBicharacter q u (v + w) = phaseBicharacter q u v * phaseBicharacter q u w := by
  unfold phaseBicharacter
  rw [symplecticOmega_add_right, zpow_add]

theorem symplecticOmega_skew (w₁ w₂ : PhaseSpace) :
    symplecticOmega w₂ w₁ = - symplecticOmega w₁ w₂ := by
  dsimp [symplecticOmega]
  ring

theorem sylvester_braided_inversion (w₁ w₂ : PhaseSpace) :
    symplecticOmega w₁ w₂ + symplecticOmega w₂ w₁ = 0 := by
  dsimp [symplecticOmega]
  ring

theorem phaseBicharacter_inverse (q : Rˣ) (w₁ w₂ : PhaseSpace) :
    phaseBicharacter q w₁ w₂ * phaseBicharacter q w₂ w₁ = 1 := by
  rw [phaseBicharacter, phaseBicharacter, symplecticOmega_skew]
  rw [← zpow_add]
  simp

end InfoGeometry.BraidedCartanAnomaly
