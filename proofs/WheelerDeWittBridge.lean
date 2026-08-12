import Mathlib
import proofs.ZornPeirceBridge

noncomputable section

namespace WheelerDeWitt

open ZornCore
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

structure DeWittCoordinates where
  time : ℝ
  space₁ : ℝ
  space₂ : ℝ

def deWittQuadratic (q : DeWittCoordinates) : ℝ :=
  q.time ^ 2 - q.space₁ ^ 2 - q.space₂ ^ 2

def deWittSymmetricMatrix (q : DeWittCoordinates) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![q.time + q.space₁, q.space₂;
     q.space₂, q.time - q.space₁]

theorem det_deWittSymmetricMatrix (q : DeWittCoordinates) :
    Matrix.det (deWittSymmetricMatrix q) = deWittQuadratic q := by
  simp [deWittSymmetricMatrix, deWittQuadratic, Matrix.det_fin_two]
  ring

def AlgebraicWheelerDeWittConstraint (q : DeWittCoordinates) : Prop :=
  deWittQuadratic q = 0

theorem algebraicWheelerDeWitt_iff_zorn_null
    (e : ZornCore.Vec3) (he : ZornCore.dot e e = 1) (q : DeWittCoordinates) :
    AlgebraicWheelerDeWittConstraint q ↔
      ZornCore.det (zornLineEmbed e he (deWittSymmetricMatrix q)) = 0 := by
  unfold AlgebraicWheelerDeWittConstraint
  rw [zornLineEmbed_norm_eq_det]
  rw [det_deWittSymmetricMatrix]

def PreservesConstraintSector
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H P : Module.End ℂ V) : Prop :=
  H * P = P * H

theorem projected_state_satisfies_constraint
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H P : Module.End ℂ V)
    (hcomm : PreservesConstraintSector H P)
    (ψ : V)
    (hψ : H ψ = 0) :
    H (P ψ) = 0 := by
  have hp := congrArg (fun T : Module.End ℂ V => T ψ) hcomm
  simpa [PreservesConstraintSector, Module.End.mul_apply, hψ] using hp

/-- The Tomita-Takesaki Wheeler-DeWitt Hamiltonian H = Δ - I -/
def tomitaWheelerDeWittHamiltonian (ModularDelta : Module.End ℂ V) : Module.End ℂ V :=
  ModularDelta - 1

/-- 
A state satisfies the Tomita Wheeler-DeWitt constraint if it is 
annihilated by Δ - I, which means it is invariant under the modular operator.
-/
theorem tomita_wdw_iff_invariant (Ψ : V) :
    tomitaWheelerDeWittHamiltonian ModularDelta Ψ = 0 ↔ ModularDelta Ψ = Ψ := by
  dsimp [tomitaWheelerDeWittHamiltonian]
  simp [tomitaWheelerDeWittHamiltonian, sub_eq_zero]

/--
If the modular operator commutes with the QEC code projector P_C,
then projected physical states remain physical.
-/
theorem tomita_preserves_code_sector (P_C : Module.End ℂ V) 
    (h_comm : PreservesConstraintSector (tomitaWheelerDeWittHamiltonian ModularDelta) P_C) 
    (Ψ : V) (h_phys : ModularDelta Ψ = Ψ) :
    ModularDelta (P_C Ψ) = P_C Ψ := by
  have h_zero : tomitaWheelerDeWittHamiltonian ModularDelta Ψ = 0 := 
    (tomita_wdw_iff_invariant (ModularDelta := ModularDelta) Ψ).mpr h_phys
  have h_proj_zero := projected_state_satisfies_constraint 
    (tomitaWheelerDeWittHamiltonian ModularDelta) P_C h_comm Ψ h_zero
  exact (tomita_wdw_iff_invariant (ModularDelta := ModularDelta) (P_C Ψ)).mp h_proj_zero

end WheelerDeWitt
