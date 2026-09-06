import InfoGeometry.Canonical.ChiralCuntzSuperchargeBridge
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Krein.DoubledSpace
import Mathlib.Tactic.NoncommRing

noncomputable section

/-!
# Chiral O₂ representation contract on the doubled carrier

The Cuntz source and the doubled Krein carrier are different objects.  This
file records the exact contract required to connect them; it does not claim
that a Cantor/O₄ representation has already been constructed.
-/

namespace InfoGeometry.Canonical.ChiralSuperchargeRepresentationContract

open InfoGeometry.Krein
open ChiralCuntzSuperchargeBridge
open InfoGeometry.Canonical.SuperchargeCARCCRBridge

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : SMulCommClass ℝ EndH EndH := inferInstance
noncomputable local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- The nilpotent chiral pair induced by the canonical `ε`/`Jε` axes. -/
noncomputable def qPlus : EndH :=
  ((2 : ℝ)⁻¹) • (spectral_epsilon (E := E) + cptSuperchargeOp (E := E))

noncomputable def qMinus : EndH :=
  ((2 : ℝ)⁻¹) • (spectral_epsilon (E := E) - cptSuperchargeOp (E := E))

theorem qPlus_sq : qPlus (E := E) * qPlus (E := E) = 0 := by
  simp only [qPlus, smul_mul_assoc, mul_smul_comm, smul_smul]
  have he : (spectral_epsilon (E := E) : EndH) * spectral_epsilon (E := E) = 1 := by
    change (spectral_epsilon (E := E)).comp (spectral_epsilon (E := E)) =
      ContinuousLinearMap.id ℝ H₂
    exact spectral_epsilon_involution (E := E)
  have hk : (cptSuperchargeOp (E := E) : EndH) * cptSuperchargeOp (E := E) = -1 := by
    change (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E)) =
      -(ContinuousLinearMap.id ℝ H₂)
    exact cptSuperchargeOp_sq (E := E)
  have hek : (spectral_epsilon (E := E) : EndH) * cptSuperchargeOp (E := E) =
      -(cptSuperchargeOp (E := E) * spectral_epsilon (E := E)) := by
    change (spectral_epsilon (E := E)).comp (cptSuperchargeOp (E := E)) =
      -((cptSuperchargeOp (E := E)).comp (spectral_epsilon (E := E)))
    rw [cptSuperchargeOp_eq_complex_i]
    calc
      (spectral_epsilon (E := E)).comp (complex_i (E := E)) =
          -(modular_j (E := E)) := spectral_epsilon_comp_complex_i (E := E)
      _ = -((complex_i (E := E)).comp (spectral_epsilon (E := E))) := by
        rw [complex_i_comp_spectral_epsilon]
  simp only [add_mul, mul_add]
  rw [he, hek, hk]
  module

theorem qMinus_sq : qMinus (E := E) * qMinus (E := E) = 0 := by
  simp only [qMinus, smul_mul_assoc, mul_smul_comm, smul_smul]
  have he : (spectral_epsilon (E := E) : EndH) * spectral_epsilon (E := E) = 1 := by
    change (spectral_epsilon (E := E)).comp (spectral_epsilon (E := E)) =
      ContinuousLinearMap.id ℝ H₂
    exact spectral_epsilon_involution (E := E)
  have hk : (cptSuperchargeOp (E := E) : EndH) * cptSuperchargeOp (E := E) = -1 := by
    change (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E)) =
      -(ContinuousLinearMap.id ℝ H₂)
    exact cptSuperchargeOp_sq (E := E)
  have hek : (spectral_epsilon (E := E) : EndH) * cptSuperchargeOp (E := E) =
      -(cptSuperchargeOp (E := E) * spectral_epsilon (E := E)) := by
    change (spectral_epsilon (E := E)).comp (cptSuperchargeOp (E := E)) =
      -((cptSuperchargeOp (E := E)).comp (spectral_epsilon (E := E)))
    rw [cptSuperchargeOp_eq_complex_i]
    calc
      (spectral_epsilon (E := E)).comp (complex_i (E := E)) =
          -(modular_j (E := E)) := spectral_epsilon_comp_complex_i (E := E)
      _ = -((complex_i (E := E)).comp (spectral_epsilon (E := E))) := by
        rw [complex_i_comp_spectral_epsilon]
  simp only [sub_mul, mul_sub]
  rw [he, hek, hk]
  module

theorem qPlus_qMinus_anticommutator :
    qPlus (E := E) * qMinus (E := E) + qMinus (E := E) * qPlus (E := E) = 1 := by
  simp only [qPlus, qMinus, smul_mul_assoc, mul_smul_comm, smul_smul]
  have he : (spectral_epsilon (E := E) : EndH) * spectral_epsilon (E := E) = 1 := by
    change (spectral_epsilon (E := E)).comp (spectral_epsilon (E := E)) =
      ContinuousLinearMap.id ℝ H₂
    exact spectral_epsilon_involution (E := E)
  have hk : (cptSuperchargeOp (E := E) : EndH) * cptSuperchargeOp (E := E) = -1 := by
    change (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E)) =
      -(ContinuousLinearMap.id ℝ H₂)
    exact cptSuperchargeOp_sq (E := E)
  have hek : (spectral_epsilon (E := E) : EndH) * cptSuperchargeOp (E := E) =
      -(cptSuperchargeOp (E := E) * spectral_epsilon (E := E)) := by
    change (spectral_epsilon (E := E)).comp (cptSuperchargeOp (E := E)) =
      -((cptSuperchargeOp (E := E)).comp (spectral_epsilon (E := E)))
    rw [cptSuperchargeOp_eq_complex_i]
    calc
      (spectral_epsilon (E := E)).comp (complex_i (E := E)) =
          -(modular_j (E := E)) := spectral_epsilon_comp_complex_i (E := E)
      _ = -((complex_i (E := E)).comp (spectral_epsilon (E := E))) := by
        rw [complex_i_comp_spectral_epsilon]
  simp only [add_mul, mul_add, sub_mul, mul_sub]
  rw [he, hek, hk]
  module

theorem qPlus_qMinus_commutator :
    qPlus (E := E) * qMinus (E := E) - qMinus (E := E) * qPlus (E := E) =
      modular_j (E := E) := by
  simp only [qPlus, qMinus, smul_mul_assoc, mul_smul_comm, smul_smul]
  have he : (spectral_epsilon (E := E) : EndH) * spectral_epsilon (E := E) = 1 := by
    change (spectral_epsilon (E := E)).comp (spectral_epsilon (E := E)) =
      ContinuousLinearMap.id ℝ H₂
    exact spectral_epsilon_involution (E := E)
  have hk : (cptSuperchargeOp (E := E) : EndH) * cptSuperchargeOp (E := E) = -1 := by
    change (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E)) =
      -(ContinuousLinearMap.id ℝ H₂)
    exact cptSuperchargeOp_sq (E := E)
  have hek : (spectral_epsilon (E := E) : EndH) * cptSuperchargeOp (E := E) =
      -(cptSuperchargeOp (E := E) * spectral_epsilon (E := E)) := by
    change (spectral_epsilon (E := E)).comp (cptSuperchargeOp (E := E)) =
      -((cptSuperchargeOp (E := E)).comp (spectral_epsilon (E := E)))
    rw [cptSuperchargeOp_eq_complex_i]
    calc
      (spectral_epsilon (E := E)).comp (complex_i (E := E)) =
          -(modular_j (E := E)) := spectral_epsilon_comp_complex_i (E := E)
      _ = -((complex_i (E := E)).comp (spectral_epsilon (E := E))) := by
        rw [complex_i_comp_spectral_epsilon]
  have hJ : (cptSuperchargeOp (E := E) : EndH) * spectral_epsilon (E := E) =
      modular_j (E := E) := by
    change (cptSuperchargeOp (E := E)).comp (spectral_epsilon (E := E)) =
      modular_j (E := E)
    rw [cptSuperchargeOp_eq_complex_i]
    exact complex_i_comp_spectral_epsilon (E := E)
  simp only [add_mul, mul_add, sub_mul, mul_sub]
  rw [he, hek, hk, hJ]
  module

/-- An explicit O₂-to-carrier representation datum. -/
structure O2CarrierRepresentation (R : Type*) [Ring R] [StarRing R]
    (sys : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) R) where
  rho : R →+* EndH
  map_Q_plus : rho (Q_plus sys) = qPlus (E := E)
  map_Q_minus : rho (Q_minus sys) = qMinus (E := E)

theorem representation_transports_chiral_relations
    {R : Type*} [Ring R] [StarRing R]
    {sys : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) R}
    (ρ : O2CarrierRepresentation (E := E) R sys) :
    ρ.rho (Q_plus sys) * ρ.rho (Q_plus sys) = 0 ∧
    ρ.rho (Q_minus sys) * ρ.rho (Q_minus sys) = 0 ∧
    ρ.rho (Q_plus sys) * ρ.rho (Q_minus sys) +
        ρ.rho (Q_minus sys) * ρ.rho (Q_plus sys) = 1 ∧
    qPlus (E := E) * qPlus (E := E) = 0 ∧
    qMinus (E := E) * qMinus (E := E) = 0 ∧
    qPlus (E := E) * qMinus (E := E) + qMinus (E := E) * qPlus (E := E) = 1 := by
  refine ⟨?_, ?_, ?_, qPlus_sq (E := E), qMinus_sq (E := E),
    qPlus_qMinus_anticommutator (E := E)⟩
  · calc
      ρ.rho (Q_plus sys) * ρ.rho (Q_plus sys) =
          ρ.rho (Q_plus sys * Q_plus sys) := (map_mul ρ.rho _ _).symm
      _ = ρ.rho 0 := by rw [Q_plus_sq_zero sys]
      _ = 0 := map_zero ρ.rho
  · calc
      ρ.rho (Q_minus sys) * ρ.rho (Q_minus sys) =
          ρ.rho (Q_minus sys * Q_minus sys) := (map_mul ρ.rho _ _).symm
      _ = ρ.rho 0 := by rw [Q_minus_sq_zero sys]
      _ = 0 := map_zero ρ.rho
  · calc
      ρ.rho (Q_plus sys) * ρ.rho (Q_minus sys) +
          ρ.rho (Q_minus sys) * ρ.rho (Q_plus sys) =
          ρ.rho (Q_plus sys * Q_minus sys + Q_minus sys * Q_plus sys) := by
            rw [map_add, map_mul, map_mul]
      _ = ρ.rho 1 := by rw [chiral_susy_anticommutator_eq_one]
      _ = 1 := map_one ρ.rho

end InfoGeometry.Canonical.ChiralSuperchargeRepresentationContract
