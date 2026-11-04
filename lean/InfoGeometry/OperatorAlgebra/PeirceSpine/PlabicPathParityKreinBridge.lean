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

/-- Adjoint-compatible forward and reverse link coefficients make both
three-shell contraction readouts self-adjoint. The assumptions pair the
coefficients on each directed link; no commutativity of the ring is needed. -/
theorem nested_zorn_three_corner_readouts_selfAdjoint
    {B : Type*} [Ring B] [StarRing B] {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (hP₁star : star P₁ = P₁) (hP₂star : star P₂ = P₂)
    (hA₁ : star A₁ = C₁) (hA₂ : star A₂ = C₂) :
    let E₁ := shell1 P₁
    let E₂ := shell2 P₁ P₂
    let E₃ := shell3 P₂
    star (E₂ - (root12 E₁ E₂ A₁ * root21 E₂ E₁ C₁ +
      root32 E₃ E₂ C₂ * root23 E₂ E₃ A₂) -
      edgeMajoranaPhi13 E₁ E₂ E₃ A₁ C₁ A₂ C₂) =
        E₂ - (root12 E₁ E₂ A₁ * root21 E₂ E₁ C₁ +
          root32 E₃ E₂ C₂ * root23 E₂ E₃ A₂) -
          edgeMajoranaPhi13 E₁ E₂ E₃ A₁ C₁ A₂ C₂ ∧
    star (E₂ + (root12 E₁ E₂ A₁ * root21 E₂ E₁ C₁ +
      root32 E₃ E₂ C₂ * root23 E₂ E₃ A₂) -
      edgeMajoranaPhi13 E₁ E₂ E₃ A₁ C₁ A₂ C₂) =
        E₂ + (root12 E₁ E₂ A₁ * root21 E₂ E₁ C₁ +
          root32 E₃ E₂ C₂ * root23 E₂ E₃ A₂) -
          edgeMajoranaPhi13 E₁ E₂ E₃ A₁ C₁ A₂ C₂ := by
  intro E₁ E₂ E₃
  have hE₁star : star E₁ = E₁ := by simpa [E₁, shell1] using hP₁star
  have hE₂star : star E₂ = E₂ := by
    dsimp [E₂, shell2]
    rw [star_sub, hP₂star, hP₁star]
  have hE₃star : star E₃ = E₃ := by
    simp [E₃, shell3, hP₂star]
  have hA₁star : star C₁ = A₁ := by
    have h := congrArg star hA₁
    simpa using h.symm
  have hA₂star : star C₂ = A₂ := by
    have h := congrArg star hA₂
    simpa using h.symm
  have h12 : star (root12 E₁ E₂ A₁) = root21 E₂ E₁ C₁ := by
    dsimp [root12, root21]
    rw [star_mul, star_mul, hE₂star, hA₁, hE₁star]
    simp [mul_assoc]
  have h21 : star (root21 E₂ E₁ C₁) = root12 E₁ E₂ A₁ := by
    dsimp [root12, root21]
    rw [star_mul, star_mul, hE₁star, hA₁star, hE₂star]
    simp [mul_assoc]
  have h23 : star (root23 E₂ E₃ A₂) = root32 E₃ E₂ C₂ := by
    dsimp [root23, root32]
    rw [star_mul, star_mul, hE₃star, hA₂, hE₂star]
    simp [mul_assoc]
  have h32 : star (root32 E₃ E₂ C₂) = root23 E₂ E₃ A₂ := by
    dsimp [root23, root32]
    rw [star_mul, star_mul, hE₂star, hA₂star, hE₃star]
    simp [mul_assoc]
  have hSelfEnergy :
      star (root12 E₁ E₂ A₁ * root21 E₂ E₁ C₁ +
        root32 E₃ E₂ C₂ * root23 E₂ E₃ A₂) =
      root12 E₁ E₂ A₁ * root21 E₂ E₁ C₁ +
        root32 E₃ E₂ C₂ * root23 E₂ E₃ A₂ := by
    rw [star_add, star_mul, h21, h12, star_mul, h32, h23]
  have hEdge :
      star (edgeMajoranaPhi13 E₁ E₂ E₃ A₁ C₁ A₂ C₂) =
        edgeMajoranaPhi13 E₁ E₂ E₃ A₁ C₁ A₂ C₂ := by
    dsimp [edgeMajoranaPhi13, edgeRoot13, edgeRoot31]
    rw [star_add, star_mul, h23, h12, star_mul, h32, h21]
    abel
  constructor <;> simp only [star_sub, star_add, hE₂star, hSelfEnergy, hEdge]

/-- Under adjoint-compatible link data, both A116 readouts are also fixed by
the star-based Krein reflection of the middle shell. This closes the
self-adjointness side condition in `kreinReflect_fixed_of_pathParity_fixed`.
-/
theorem nested_zorn_three_corner_readouts_krein_fixed
    {B : Type*} [Ring B] [StarRing B] {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (hP₁ : P₁ * P₁ = P₁) (hP₂ : P₂ * P₂ = P₂)
    (hP₁star : star P₁ = P₁) (hP₂star : star P₂ = P₂)
    (hChain : idemLe P₁ P₂)
    (hA₁ : star A₁ = C₁) (hA₂ : star A₂ = C₂) :
    let E₁ := shell1 P₁
    let E₂ := shell2 P₁ P₂
    let E₃ := shell3 P₂
    kreinReflect E₂
      (E₂ - (root12 E₁ E₂ A₁ * root21 E₂ E₁ C₁ +
        root32 E₃ E₂ C₂ * root23 E₂ E₃ A₂) -
        edgeMajoranaPhi13 E₁ E₂ E₃ A₁ C₁ A₂ C₂) =
      E₂ - (root12 E₁ E₂ A₁ * root21 E₂ E₁ C₁ +
        root32 E₃ E₂ C₂ * root23 E₂ E₃ A₂) -
        edgeMajoranaPhi13 E₁ E₂ E₃ A₁ C₁ A₂ C₂ ∧
    kreinReflect E₂
      (E₂ + (root12 E₁ E₂ A₁ * root21 E₂ E₁ C₁ +
        root32 E₃ E₂ C₂ * root23 E₂ E₃ A₂) -
        edgeMajoranaPhi13 E₁ E₂ E₃ A₁ C₁ A₂ C₂) =
      E₂ + (root12 E₁ E₂ A₁ * root21 E₂ E₁ C₁ +
        root32 E₃ E₂ C₂ * root23 E₂ E₃ A₂) -
        edgeMajoranaPhi13 E₁ E₂ E₃ A₁ C₁ A₂ C₂ := by
  intro E₁ E₂ E₃
  rcases nested_zorn_three_corner_readouts_fixed_by_path_parity
      hP₁ hP₂ hChain with ⟨hPath₁, hPath₂⟩
  rcases nested_zorn_three_corner_readouts_selfAdjoint
      hP₁star hP₂star hA₁ hA₂ with ⟨hStar₁, hStar₂⟩
  exact ⟨kreinReflect_fixed_of_pathParity_fixed hP₁ hP₂ hChain hStar₁ hPath₁,
    kreinReflect_fixed_of_pathParity_fixed hP₁ hP₂ hChain hStar₂ hPath₂⟩


/-- The A116 ordinary and alternating-sign contraction outputs acquire the
same seam translation under the full A102 wallpaper glide. Consequently their
difference is invariant under that glide. The assumptions make the shell
involution self-adjoint and pair the coefficients on each reversed link. -/
theorem nested_zorn_three_corner_readouts_wallpaper_glide
    {B : Type*} [Ring B] [StarRing B] {P₁ P₂ A₁ C₁ A₂ C₂ T : B}
    (hP₁ : P₁ * P₁ = P₁) (hP₂ : P₂ * P₂ = P₂)
    (hP₁star : star P₁ = P₁) (hP₂star : star P₂ = P₂)
    (hChain : idemLe P₁ P₂)
    (hA₁ : star A₁ = C₁) (hA₂ : star A₂ = C₂)
    (hSeamT : kreinReflect (shell2 P₁ P₂) T = T) :
    let E₁ := shell1 P₁
    let E₂ := shell2 P₁ P₂
    let E₃ := shell3 P₂
    let ordinary := E₂ - (root12 E₁ E₂ A₁ * root21 E₂ E₁ C₁ +
      root32 E₃ E₂ C₂ * root23 E₂ E₃ A₂) -
      edgeMajoranaPhi13 E₁ E₂ E₃ A₁ C₁ A₂ C₂
    let alternating := E₂ + (root12 E₁ E₂ A₁ * root21 E₂ E₁ C₁ +
      root32 E₃ E₂ C₂ * root23 E₂ E₃ A₂) -
      edgeMajoranaPhi13 E₁ E₂ E₃ A₁ C₁ A₂ C₂
    wallpaperGlide E₂ T ordinary = ordinary + T ∧
    wallpaperGlide E₂ T alternating = alternating + T ∧
    wallpaperGlide E₂ T ordinary - wallpaperGlide E₂ T alternating =
      ordinary - alternating := by
  intro E₁ E₂ E₃ ordinary alternating
  rcases nested_zorn_three_corner_readouts_krein_fixed
      hP₁ hP₂ hP₁star hP₂star hChain hA₁ hA₂ with ⟨hOrdinary, hAlternating⟩
  have hOrdinary' : kreinReflect E₂ ordinary = ordinary := by
    simpa [ordinary] using hOrdinary
  have hAlternating' : kreinReflect E₂ alternating = alternating := by
    simpa [alternating] using hAlternating
  have hOrdinaryGlide : wallpaperGlide E₂ T ordinary = ordinary + T := by
    simp [wallpaperGlide, hOrdinary']
  have hAlternatingGlide : wallpaperGlide E₂ T alternating = alternating + T := by
    simp [wallpaperGlide, hAlternating']
  refine ⟨hOrdinaryGlide, hAlternatingGlide, ?_⟩
  rw [hOrdinaryGlide, hAlternatingGlide]
  abel

end InfoGeometry.OperatorAlgebra.PeirceSpine
