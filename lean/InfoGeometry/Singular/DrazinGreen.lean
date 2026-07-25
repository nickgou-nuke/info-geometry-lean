import Mathlib.Tactic
import InfoGeometry.Singular.Drazin

/-!
# InfoGeometry.Singular.DrazinGreen

Drazin inverse as a Green operator on the regular/core sector.

This file is purely algebraic.  It does not assert the existence of an
integral kernel, a PDE Green function, or a resolvent Laurent expansion.  It
records the theorem-safe identities:

* `D = Aᴰ` is the Drazin Green operator;
* `P_D = A * D = D * A` is the regular/core projector;
* `Q_D = 1 - P_D` is the singular/nilpotent residue projector;
* `A * D = D * A = P_D`, so `D` solves equations only after projecting to the
  regular sector.
-/

namespace InfoGeometry.Singular.Drazin

section DrazinGreen

variable {R : Type*} [Ring R]
variable {A D : R} {k : ℕ}

/-- The Drazin Green operator is the Drazin inverse. -/
def Drazin_Green (A D : R) (k : ℕ) (_h : IsDrazinInverse A D k) : R :=
  D

/-- The Drazin residue projector is the complement of the Drazin core projector. -/
def Drazin_ResidueProjector
    (A D : R) (k : ℕ) (h : IsDrazinInverse A D k) : R :=
  1 - Drazin_Projector A D k h

/-- Left Green identity: `A * G = P_D`. -/
theorem A_mul_Drazin_Green_eq_projector
    (h : IsDrazinInverse A D k) :
    A * Drazin_Green A D k h = Drazin_Projector A D k h := by
  rfl

/-- Right Green identity: `G * A = P_D`. -/
theorem Drazin_Green_mul_A_eq_projector
    (h : IsDrazinInverse A D k) :
    Drazin_Green A D k h * A = Drazin_Projector A D k h := by
  unfold Drazin_Green Drazin_Projector
  exact h.comm.symm

/-- The Drazin projector can also be written as `D * A`. -/
theorem Drazin_Projector_eq_green_mul_A
    (h : IsDrazinInverse A D k) :
    Drazin_Projector A D k h = D * A := by
  unfold Drazin_Projector
  exact h.comm

/-- The Drazin core projector acts as identity on the Green operator on the left. -/
theorem Drazin_Projector_mul_Green_eq_Green
    (h : IsDrazinInverse A D k) :
    Drazin_Projector A D k h * Drazin_Green A D k h =
      Drazin_Green A D k h := by
  unfold Drazin_Projector Drazin_Green
  calc
    (A * D) * D = (D * A) * D := by rw [h.comm]
    _ = D * A * D := by simp [mul_assoc]
    _ = D := h.dad_eq_d

/-- The Drazin core projector acts as identity on the Green operator on the right. -/
theorem Green_mul_Drazin_Projector_eq_Green
    (h : IsDrazinInverse A D k) :
    Drazin_Green A D k h * Drazin_Projector A D k h =
      Drazin_Green A D k h := by
  unfold Drazin_Projector Drazin_Green
  calc
    D * (A * D) = D * A * D := by simp [mul_assoc]
    _ = D := h.dad_eq_d

/-- The Drazin core projector commutes with the original operator. -/
theorem Drazin_Projector_mul_A_eq_A_mul_Drazin_Projector
    (h : IsDrazinInverse A D k) :
    Drazin_Projector A D k h * A =
      A * Drazin_Projector A D k h := by
  unfold Drazin_Projector
  calc
    (A * D) * A = A * (D * A) := by simp [mul_assoc]
    _ = A * (A * D) := by rw [← h.comm]

/-- The Drazin residue projector is idempotent. -/
theorem Drazin_ResidueProjector_idempotent
    (h : IsDrazinInverse A D k) :
    Drazin_ResidueProjector A D k h *
      Drazin_ResidueProjector A D k h =
    Drazin_ResidueProjector A D k h := by
  unfold Drazin_ResidueProjector
  let P := Drazin_Projector A D k h
  have hP : P * P = P := Drazin_Projector_idempotent h
  change (1 - P) * (1 - P) = 1 - P
  rw [show (1 - P) * (1 - P) = 1 - P - P + P * P by noncomm_ring]
  rw [hP]
  noncomm_ring

/--
The singular residue is killed by `A^k` on the left.

This is the algebraic Green obstruction statement: after enough powers, the
complementary sector is nilpotent.
-/
theorem A_pow_mul_Drazin_ResidueProjector_eq_zero
    (h : IsDrazinInverse A D k) :
    A ^ k * Drazin_ResidueProjector A D k h = 0 := by
  unfold Drazin_ResidueProjector Drazin_Projector
  calc
    A ^ k * (1 - A * D)
        = A ^ k - A ^ k * (A * D) := by noncomm_ring
    _ = A ^ k - A ^ (k + 1) * D := by
      rw [show A ^ k * (A * D) = A ^ (k + 1) * D by
        rw [pow_succ, mul_assoc]]
    _ = 0 := by
      rw [h.pow_eq_pow_succ_mul]
      simp

end DrazinGreen

section DrazinGreenEnd

variable {K V : Type*}
variable [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Native finite-dimensional Drazin Green operator. -/
noncomputable def drazinGreen (A : Module.End K V) : Module.End K V :=
  drazinInverse A

/-- Native finite-dimensional Drazin residue projector. -/
noncomputable def drazinResidueProjector (A : Module.End K V) : Module.End K V :=
  1 - drazinProjector A

/-- The native Drazin Green operator satisfies `A * G = P_D`. -/
theorem A_mul_drazinGreen_eq_drazinProjector
    (A : Module.End K V) :
    A * drazinGreen A = drazinProjector A := by
  rfl

/-- The native Drazin Green operator satisfies `G * A = P_D`. -/
theorem drazinGreen_mul_A_eq_drazinProjector
    (A : Module.End K V) :
    drazinGreen A * A = drazinProjector A := by
  unfold drazinGreen drazinProjector
  exact (drazinInverse_spec A).comm.symm

end DrazinGreenEnd

end InfoGeometry.Singular.Drazin
