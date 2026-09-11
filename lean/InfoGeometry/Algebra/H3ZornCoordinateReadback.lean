import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.H3ZornJordanIdentity

namespace InfoGeometry.Algebra.H3ZornCoordinateReadback

open InfoGeometry.Algebra

/-! Component projections of the existing `H3Zorn` instance operations.
These are readback lemmas only; no second additive or scalar structure is
introduced. -/

theorem add_α₁ (X Y : H3Zorn ℝ) :
    (X + Y).α₁ = X.α₁ + Y.α₁ := by
  exact congrArg H3Zorn.α₁ (H3Zorn.add_readback X Y)

theorem add_α₂ (X Y : H3Zorn ℝ) :
    (X + Y).α₂ = X.α₂ + Y.α₂ := by
  exact congrArg H3Zorn.α₂ (H3Zorn.add_readback X Y)

theorem add_α₃ (X Y : H3Zorn ℝ) :
    (X + Y).α₃ = X.α₃ + Y.α₃ := by
  exact congrArg H3Zorn.α₃ (H3Zorn.add_readback X Y)

theorem add_a (X Y : H3Zorn ℝ) :
    (X + Y).a = ZornVectorMatrix.add X.a Y.a := by
  exact congrArg H3Zorn.a (H3Zorn.add_readback X Y)

theorem add_b (X Y : H3Zorn ℝ) :
    (X + Y).b = ZornVectorMatrix.add X.b Y.b := by
  exact congrArg H3Zorn.b (H3Zorn.add_readback X Y)

theorem add_c (X Y : H3Zorn ℝ) :
    (X + Y).c = ZornVectorMatrix.add X.c Y.c := by
  exact congrArg H3Zorn.c (H3Zorn.add_readback X Y)

theorem smul_α₁ (r : ℝ) (X : H3Zorn ℝ) :
    (r • X).α₁ = r * X.α₁ := by
  exact congrArg H3Zorn.α₁ (H3Zorn.smul_readback r X)

theorem smul_α₂ (r : ℝ) (X : H3Zorn ℝ) :
    (r • X).α₂ = r * X.α₂ := by
  exact congrArg H3Zorn.α₂ (H3Zorn.smul_readback r X)

theorem smul_α₃ (r : ℝ) (X : H3Zorn ℝ) :
    (r • X).α₃ = r * X.α₃ := by
  exact congrArg H3Zorn.α₃ (H3Zorn.smul_readback r X)

theorem smul_a (r : ℝ) (X : H3Zorn ℝ) :
    (r • X).a = ZornVectorMatrix.smul r X.a := by
  exact congrArg H3Zorn.a (H3Zorn.smul_readback r X)

theorem smul_b (r : ℝ) (X : H3Zorn ℝ) :
    (r • X).b = ZornVectorMatrix.smul r X.b := by
  exact congrArg H3Zorn.b (H3Zorn.smul_readback r X)

theorem smul_c (r : ℝ) (X : H3Zorn ℝ) :
    (r • X).c = ZornVectorMatrix.smul r X.c := by
  exact congrArg H3Zorn.c (H3Zorn.smul_readback r X)

/-! Scalar native projections used by the RealAlbert transport boundary. -/

theorem linearTrace_coordinate (X : H3Zorn ℝ) :
    H3Zorn.linearTrace X = X.α₁ + X.α₂ + X.α₃ := rfl

theorem traceBilin_coordinate (X Y : H3Zorn ℝ) :
    H3Zorn.traceBilin X Y =
      X.α₁ * Y.α₁ + X.α₂ * Y.α₂ + X.α₃ * Y.α₃ +
        ZornVectorMatrix.trace
          (ZornVectorMatrix.mul X.a (ZornVectorMatrix.conj Y.a)) +
        ZornVectorMatrix.trace
          (ZornVectorMatrix.mul X.b (ZornVectorMatrix.conj Y.b)) +
        ZornVectorMatrix.trace
          (ZornVectorMatrix.mul X.c (ZornVectorMatrix.conj Y.c)) := rfl

theorem adjointQuad_α₁ (X : H3Zorn ℝ) :
    (H3Zorn.adjointQuad X).α₁ = X.α₂ * X.α₃ - ZornVectorMatrix.norm X.b := rfl

theorem adjointQuad_α₂ (X : H3Zorn ℝ) :
    (H3Zorn.adjointQuad X).α₂ = X.α₁ * X.α₃ - ZornVectorMatrix.norm X.c := rfl

theorem adjointQuad_α₃ (X : H3Zorn ℝ) :
    (H3Zorn.adjointQuad X).α₃ = X.α₁ * X.α₂ - ZornVectorMatrix.norm X.a := rfl

theorem adjointQuad_a (X : H3Zorn ℝ) :
    (H3Zorn.adjointQuad X).a =
      ZornVectorMatrix.sub
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.c)
          (ZornVectorMatrix.conj X.b))
        (ZornVectorMatrix.smul X.α₃ X.a) := rfl

theorem adjointQuad_b (X : H3Zorn ℝ) :
    (H3Zorn.adjointQuad X).b =
      ZornVectorMatrix.sub
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.a)
          (ZornVectorMatrix.conj X.c))
        (ZornVectorMatrix.smul X.α₁ X.b) := rfl

theorem adjointQuad_c (X : H3Zorn ℝ) :
    (H3Zorn.adjointQuad X).c =
      ZornVectorMatrix.sub
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.b)
          (ZornVectorMatrix.conj X.a))
        (ZornVectorMatrix.smul X.α₂ X.c) := rfl

theorem crossProduct_a (X Y : H3Zorn ℝ) :
    (H3Zorn.crossProduct X Y).a =
      ZornVectorMatrix.sub (H3Zorn.adjointQuad (X + Y)).a
        (ZornVectorMatrix.add (H3Zorn.adjointQuad X).a
          (H3Zorn.adjointQuad Y).a) := by
  simp [H3Zorn.crossProduct, H3Zorn.sub_readback,
    H3Zorn.add_readback, ZornVectorMatrix.sub_eq_add_neg,
    ← zvm_add_def, ← zvm_neg_def]
  module

theorem crossProduct_b (X Y : H3Zorn ℝ) :
    (H3Zorn.crossProduct X Y).b =
      ZornVectorMatrix.sub (H3Zorn.adjointQuad (X + Y)).b
        (ZornVectorMatrix.add (H3Zorn.adjointQuad X).b
          (H3Zorn.adjointQuad Y).b) := by
  simp [H3Zorn.crossProduct, H3Zorn.sub_readback,
    H3Zorn.add_readback, ZornVectorMatrix.sub_eq_add_neg,
    ← zvm_add_def, ← zvm_neg_def]
  module

theorem crossProduct_c (X Y : H3Zorn ℝ) :
    (H3Zorn.crossProduct X Y).c =
      ZornVectorMatrix.sub (H3Zorn.adjointQuad (X + Y)).c
        (ZornVectorMatrix.add (H3Zorn.adjointQuad X).c
          (H3Zorn.adjointQuad Y).c) := by
  simp [H3Zorn.crossProduct, H3Zorn.sub_readback,
    H3Zorn.add_readback, ZornVectorMatrix.sub_eq_add_neg,
    ← zvm_add_def, ← zvm_neg_def]
  module

theorem crossProduct_α₁ (X Y : H3Zorn ℝ) :
    (H3Zorn.crossProduct X Y).α₁ =
      (H3Zorn.adjointQuad (X + Y)).α₁ -
        (H3Zorn.adjointQuad X).α₁ - (H3Zorn.adjointQuad Y).α₁ := rfl

theorem crossProduct_α₂ (X Y : H3Zorn ℝ) :
    (H3Zorn.crossProduct X Y).α₂ =
      (H3Zorn.adjointQuad (X + Y)).α₂ -
        (H3Zorn.adjointQuad X).α₂ - (H3Zorn.adjointQuad Y).α₂ := rfl

theorem crossProduct_α₃ (X Y : H3Zorn ℝ) :
    (H3Zorn.crossProduct X Y).α₃ =
      (H3Zorn.adjointQuad (X + Y)).α₃ -
        (H3Zorn.adjointQuad X).α₃ - (H3Zorn.adjointQuad Y).α₃ := rfl

end InfoGeometry.Algebra.H3ZornCoordinateReadback
