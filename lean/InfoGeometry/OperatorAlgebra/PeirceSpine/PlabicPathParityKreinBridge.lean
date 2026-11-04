/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.TelegrapherTwoStateMasterPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentZornChainArchetypes
import Mathlib.Tactic.NoncommRing

/-!
# Path parity and Krein reflection compatibility

The alternating parity of a nested three-shell Peirce partition is the
negative of the middle-shell involution. Therefore its algebraic conjugation
agrees with the star-based Krein reflection on self-adjoint readouts.
This identifies the actions only on that self-adjoint sector; it does not
assert wallpaper-glide invariance.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open IdempotentZornChainArchetypes

/-- The alternating path parity of a nested three-shell partition is the
negative middle-shell involution. -/
theorem zornPlabicParity_eq_neg_invS_shell2
    {B : Type*} [Ring B] {P₁ P₂ : B}
    (hP₁ : P₁ * P₁ = P₁) (hP₂ : P₂ * P₂ = P₂)
    (hChain : idemLe P₁ P₂) :
    zornPlabicParity (shell1 P₁) (shell2 P₁ P₂) (shell3 P₂) =
      -invS (shell2 P₁ P₂) := by
  have hsum := (three_shell_partition hP₁ hP₂ hChain).1
  unfold zornPlabicParity shell1 shell2 shell3 invS
  noncomm_ring [hsum]

/-- On a self-adjoint element fixed by path-parity conjugation, the A102
star-based Krein reflection for the middle shell also fixes that element. -/
theorem kreinReflect_fixed_of_pathParity_fixed
    {B : Type*} [Ring B] [StarRing B] {P₁ P₂ X : B}
    (hP₁ : P₁ * P₁ = P₁) (hP₂ : P₂ * P₂ = P₂)
    (hChain : idemLe P₁ P₂) (hXstar : star X = X)
    (hPath : zornPlabicParity (shell1 P₁) (shell2 P₁ P₂) (shell3 P₂) * X *
      zornPlabicParity (shell1 P₁) (shell2 P₁ P₂) (shell3 P₂) = X) :
    kreinReflect (shell2 P₁ P₂) X = X := by
  have hParity := zornPlabicParity_eq_neg_invS_shell2 hP₁ hP₂ hChain
  unfold kreinReflect
  rw [hXstar]
  have hInv : invS (shell2 P₁ P₂) =
      -zornPlabicParity (shell1 P₁) (shell2 P₁ P₂) (shell3 P₂) := by
    rw [hParity]
    rw [neg_neg]
  rw [hInv]
  calc
    -zornPlabicParity (shell1 P₁) (shell2 P₁ P₂) (shell3 P₂) * X *
        -zornPlabicParity (shell1 P₁) (shell2 P₁ P₂) (shell3 P₂) =
        zornPlabicParity (shell1 P₁) (shell2 P₁ P₂) (shell3 P₂) * X *
          zornPlabicParity (shell1 P₁) (shell2 P₁ P₂) (shell3 P₂) := by
      noncomm_ring
    _ = X := hPath

end InfoGeometry.OperatorAlgebra.PeirceSpine
