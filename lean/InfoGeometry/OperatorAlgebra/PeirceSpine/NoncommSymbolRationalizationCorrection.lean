/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.QuantumAffineFlagClusterPoset

/-!
# Commutator correction for noncommutative symbol-factor products

The product of opposite symbol factors has a commutator correction when the
two coefficients do not commute. This identity gives the exact general
formula; ordinary rationalization follows when the dressed coefficient
commutes with the product of the other coefficient and the square-root term.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

section SymbolCorrection

variable {B : Type*} [Ring B]

/-- Exact noncommutative expansion of the opposite symbol factors, assuming
only that `B_z` commutes with the square-root term. The correction is the
commutator of `Z₀` with `B_z * √Δ`. -/
theorem algSymbolFactor_product_commutator_correction
    {P : B} (hP : P * P = P) (A C Z₀ B_z : B)
    (hBSqrt : B_z * fourMassBoxSqrt P A C = fourMassBoxSqrt P A C * B_z) :
    algSymbolFactorPlus P A C Z₀ B_z * algSymbolFactorMinus P A C Z₀ B_z =
      Z₀ * Z₀ - comm Z₀ (B_z * fourMassBoxSqrt P A C) -
        B_z * B_z * fourMassBoxDisc P A C := by
  have hSq : fourMassBoxSqrt P A C * fourMassBoxSqrt P A C = fourMassBoxDisc P A C :=
    (imaginary_module_and_four_mass_box_letter hP A C).2.2.2.1
  have hProd :
      (B_z * fourMassBoxSqrt P A C) * (B_z * fourMassBoxSqrt P A C) =
        B_z * B_z * fourMassBoxDisc P A C := by
    calc
      (B_z * fourMassBoxSqrt P A C) * (B_z * fourMassBoxSqrt P A C) =
          B_z * (fourMassBoxSqrt P A C * B_z) * fourMassBoxSqrt P A C := by
            simp only [mul_assoc]
      _ = B_z * (B_z * fourMassBoxSqrt P A C) * fourMassBoxSqrt P A C := by
            rw [← hBSqrt]
      _ = B_z * B_z * (fourMassBoxSqrt P A C * fourMassBoxSqrt P A C) := by
            simp only [mul_assoc]
      _ = B_z * B_z * fourMassBoxDisc P A C := by rw [hSq]
  unfold algSymbolFactorPlus algSymbolFactorMinus
  calc
    (Z₀ + B_z * fourMassBoxSqrt P A C) *
        (Z₀ - B_z * fourMassBoxSqrt P A C) =
      Z₀ * Z₀ - comm Z₀ (B_z * fourMassBoxSqrt P A C) -
        (B_z * fourMassBoxSqrt P A C) * (B_z * fourMassBoxSqrt P A C) := by
          unfold comm
          noncomm_ring
    _ = Z₀ * Z₀ - comm Z₀ (B_z * fourMassBoxSqrt P A C) -
        B_z * B_z * fourMassBoxDisc P A C := by rw [hProd]

/-- If the combined coefficient `B_z * √Δ` commutes with `Z₀`, the correction
term vanishes and the standard rationalized product follows. -/
theorem algSymbolFactor_rationalization_of_combined_comm
    {P : B} (hP : P * P = P) (A C Z₀ B_z : B)
    (hBSqrt : B_z * fourMassBoxSqrt P A C = fourMassBoxSqrt P A C * B_z)
    (hZCombined : Z₀ * (B_z * fourMassBoxSqrt P A C) =
      (B_z * fourMassBoxSqrt P A C) * Z₀) :
    algSymbolFactorPlus P A C Z₀ B_z * algSymbolFactorMinus P A C Z₀ B_z =
      Z₀ * Z₀ - B_z * B_z * fourMassBoxDisc P A C := by
  rw [algSymbolFactor_product_commutator_correction hP A C Z₀ B_z hBSqrt]
  unfold comm
  rw [hZCombined]
  simp

end SymbolCorrection

end InfoGeometry.OperatorAlgebra.PeirceSpine
