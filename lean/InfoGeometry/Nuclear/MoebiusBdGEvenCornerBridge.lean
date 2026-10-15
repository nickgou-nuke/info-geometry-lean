import Mathlib
import InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge
import InfoGeometry.SuperGrassmannian.MoebiusSuperGrassmannianCPT
import InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY

/-!
# Möbius reflection on the OSp even corner and the finite BdG block

This bridge composes the existing Section 87 even-corner map with the
Section 89 reflection law. It proves equivariance of that restriction and
the induced two-level BdG and QPNM conjugations. The full affine QPNM matrix
has a scalar-center term, which may vanish; its correct parameter
transformation is `(Eqp, ω) ↦ (Eqp + ω, -ω)`, which preserves that center.
-/

namespace InfoGeometry.Nuclear.MoebiusBdGEvenCornerBridge

open Matrix
open InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge
open InfoGeometry.SuperGrassmannian.MoebiusReflection

local notation "τ₁" => InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1 ℝ

private theorem tau_matrix :
    tau (R := ℝ) = !![0, 0, 1; 0, -1, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tau, Gamma,
      InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J,
      Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_three]

/-- The even-corner restriction intertwines the Section 89 reflection with
the existing two-level sheet swap. This is a statement about the specified
corner map, not a claim that the corner is multiplicative on arbitrary
matrices. -/
theorem evenCorner_tau_conjugation (X : M₃) :
    evenCorner (tau (R := ℝ) * X * tau) = τ₁ * evenCorner X * τ₁ := by
  rw [tau_matrix]
  unfold InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [evenCorner, evenIndex, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_two]
    <;> norm_num [evenIndex, Matrix.of_apply]

/-- The Möbius-reflected OSp element restricts to the BdG block with flipped
detuning. This composes the Section 89 conjugation theorem with the Section 87
even-corner identification. -/
theorem evenCorner_reflected_ospPairingElement (ε Δ : ℝ) :
    evenCorner (tau (R := ℝ) * ospPairingElement ε Δ * tau) =
      InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock (-ε) Δ := by
  rw [InfoGeometry.SuperGrassmannian.MoebiusReflection.tau_intertwines_ospPairingElement,
    evenCorner_ospPairingElement]

/-- The 2×2 BdG block inherits the detuning flip from the Section 89 OSp
reflection by restriction to the even corner. -/
theorem tau1_bdgBlock_flip (ε Δ : ℝ) :
    τ₁ * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ * τ₁ =
      InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock (-ε) Δ := by
  calc
    τ₁ * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ * τ₁ =
        τ₁ * evenCorner (ospPairingElement ε Δ) * τ₁ := by
          rw [evenCorner_ospPairingElement]
    _ = evenCorner (tau (R := ℝ) * ospPairingElement ε Δ * tau) :=
          (evenCorner_tau_conjugation (ospPairingElement ε Δ)).symm
    _ = InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock (-ε) Δ := by
          rw [evenCorner_reflected_ospPairingElement]

private theorem tau1_scalar_conjugation (c : ℝ) :
    τ₁ * (c • (1 : M₂)) * τ₁ = c • (1 : M₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The complete two-level QPNM matrix transforms under the same swap when
the scalar center is kept fixed. The energy parameter shift is essential. -/
theorem tau1_qpnmMatrix_reflection (Eqp ω V : ℝ) :
    τ₁ * InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix Eqp ω V * τ₁ =
      InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix
        (Eqp + ω) (-ω) V := by
  rw [qpnmMatrix_eq_center_add_ospCorner Eqp ω V,
    qpnmMatrix_eq_center_add_ospCorner (Eqp + ω) (-ω) V]
  have hcenter :
      InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievCenter Eqp ω =
        InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievCenter
          (Eqp + ω) (-ω) := by
    simp [InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievCenter]
    ring
  have hcoordinate :
      -InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievBdGCoordinate ω =
        InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievBdGCoordinate (-ω) := by
    simp [InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievBdGCoordinate]
    ring
  rw [Matrix.mul_add, Matrix.add_mul, tau1_scalar_conjugation,
    ← evenCorner_tau_conjugation,
    InfoGeometry.SuperGrassmannian.MoebiusReflection.tau_intertwines_ospPairingElement,
    hcenter, hcoordinate]

/-- Kernel-checked package of the two reflection consequences added here. -/
theorem compile_moebius_bdg_even_corner_bridge :
    (∀ X : M₃, evenCorner (tau (R := ℝ) * X * tau) =
      τ₁ * evenCorner X * τ₁) ∧
    (∀ ε Δ : ℝ,
      τ₁ * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ * τ₁ =
        InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock (-ε) Δ) ∧
    (∀ Eqp ω V : ℝ,
      τ₁ * InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix Eqp ω V * τ₁ =
        InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix
          (Eqp + ω) (-ω) V) := by
  exact ⟨evenCorner_tau_conjugation, tau1_bdgBlock_flip,
    tau1_qpnmMatrix_reflection⟩

end InfoGeometry.Nuclear.MoebiusBdGEvenCornerBridge
