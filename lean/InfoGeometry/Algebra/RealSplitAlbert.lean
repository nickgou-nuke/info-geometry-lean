import Mathlib

/-!
# Real Split-Albert Carrier

This file provides the real coordinate carrier used by the split-Albert route.
It records the additive and scalar structure together with a candidate product
formula for later transport into the Jordan and derivation surfaces.
-/

namespace InfoGeometry.Algebra

/-- The real split-octonion coordinate carrier `ℝ^8`. -/
@[ext]
structure RealSplitOct where
  a : ℝ
  b : ℝ
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ
  y0 : ℝ
  y1 : ℝ
  y2 : ℝ

noncomputable section
namespace RealSplitOct

def zero : RealSplitOct := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

def add (X Y : RealSplitOct) : RealSplitOct :=
  ⟨X.a + Y.a, X.b + Y.b, X.x0 + Y.x0, X.x1 + Y.x1, X.x2 + Y.x2,
    X.y0 + Y.y0, X.y1 + Y.y1, X.y2 + Y.y2⟩

def neg (X : RealSplitOct) : RealSplitOct :=
  ⟨-X.a, -X.b, -X.x0, -X.x1, -X.x2, -X.y0, -X.y1, -X.y2⟩

def smul (r : ℝ) (X : RealSplitOct) : RealSplitOct :=
  ⟨r * X.a, r * X.b, r * X.x0, r * X.x1, r * X.x2, r * X.y0, r * X.y1, r * X.y2⟩

instance : Add RealSplitOct := ⟨add⟩
instance : Neg RealSplitOct := ⟨neg⟩
instance : Sub RealSplitOct := ⟨fun X Y => add X (neg Y)⟩
instance : Zero RealSplitOct := ⟨zero⟩

/-- Coordinate equivalence used to transport the additive and module structure. -/
def coordEquiv : RealSplitOct ≃ ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ where
  toFun X := (X.a, X.b, X.x0, X.x1, X.x2, X.y0, X.y1, X.y2)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1,
    t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2⟩
  left_inv := by
    intro X
    rfl
  right_inv := by
    intro t
    cases t <;> rfl

instance : AddCommGroup RealSplitOct :=
  Equiv.addCommGroup coordEquiv

instance : Module ℝ RealSplitOct :=
  Equiv.module ℝ coordEquiv

/-- Conjugation of real split octonions. -/
def conj (X : RealSplitOct) : RealSplitOct :=
  ⟨X.b, X.a, -X.x0, -X.x1, -X.x2, -X.y0, -X.y1, -X.y2⟩

/-- Split octonion multiplication over $\mathbb{R}$. -/
def mul (X Y : RealSplitOct) : RealSplitOct :=
  ⟨ X.a * Y.a + (X.x0 * Y.y0 + X.x1 * Y.y1 + X.x2 * Y.y2),
    X.b * Y.b + (X.y0 * Y.x0 + X.y1 * Y.x1 + X.y2 * Y.x2),
    X.a * Y.x0 + Y.b * X.x0 - (X.y1 * Y.y2 - X.y2 * Y.y1),
    X.a * Y.x1 + Y.b * X.x1 - (X.y2 * Y.y0 - X.y0 * Y.y2),
    X.a * Y.x2 + Y.b * X.x2 - (X.y0 * Y.y1 - X.y1 * Y.y0),
    Y.a * X.y0 + X.b * Y.y0 + (X.x1 * Y.x2 - X.x2 * Y.x1),
    Y.a * X.y1 + X.b * Y.y1 + (X.x2 * Y.x0 - X.x0 * Y.x2),
    Y.a * X.y2 + X.b * Y.y2 + (X.x0 * Y.x1 - X.x1 * Y.x0) ⟩

end RealSplitOct

/-- The real Albert matrix coordinate carrier `ℝ^{27}`. -/
@[ext]
structure RealAlbertMatrix where
  α₁ : ℝ
  α₂ : ℝ
  α₃ : ℝ
  z₁ : RealSplitOct
  z₂ : RealSplitOct
  z₃ : RealSplitOct

namespace RealAlbertMatrix

def zero : RealAlbertMatrix := ⟨0, 0, 0, RealSplitOct.zero, RealSplitOct.zero, RealSplitOct.zero⟩

def add (X Y : RealAlbertMatrix) : RealAlbertMatrix :=
  ⟨X.α₁ + Y.α₁, X.α₂ + Y.α₂, X.α₃ + Y.α₃,
   X.z₁ + Y.z₁, X.z₂ + Y.z₂, X.z₃ + Y.z₃⟩

def neg (X : RealAlbertMatrix) : RealAlbertMatrix :=
  ⟨-X.α₁, -X.α₂, -X.α₃, -X.z₁, -X.z₂, -X.z₃⟩

def smul (r : ℝ) (X : RealAlbertMatrix) : RealAlbertMatrix :=
  ⟨r * X.α₁, r * X.α₂, r * X.α₃, r • X.z₁, r • X.z₂, r • X.z₃⟩

instance : Add RealAlbertMatrix := ⟨add⟩
instance : Neg RealAlbertMatrix := ⟨neg⟩
instance : Sub RealAlbertMatrix := ⟨fun X Y => add X (neg Y)⟩
instance : Zero RealAlbertMatrix := ⟨zero⟩

/-- Coordinate equivalence used to transport the additive and module structure. -/
def coordEquiv : RealAlbertMatrix ≃ ℝ × ℝ × ℝ × RealSplitOct × RealSplitOct × RealSplitOct where
  toFun X := (X.α₁, X.α₂, X.α₃, X.z₁, X.z₂, X.z₃)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv := by
    intro X
    rfl
  right_inv := by
    intro t
    cases t <;> rfl

instance : AddCommGroup RealAlbertMatrix :=
  Equiv.addCommGroup coordEquiv

instance : Module ℝ RealAlbertMatrix :=
  Equiv.module ℝ coordEquiv

/-- The split-Albert Jordan product `X ∘ Y = (XY + YX) / 2` in Hermitian
coordinates
`[[α₁, z₃, conj z₂], [conj z₃, α₂, z₁], [z₂, conj z₁, α₃]]`.

The factor `1/2` applies to every paired off-diagonal contribution, including
the diagonal readouts.  The order of the conjugated cross terms is inherited
from the displayed matrix multiplication and cannot be reversed in the
noncommutative split-octonion algebra.
-/
def mul (X Y : RealAlbertMatrix) : RealAlbertMatrix :=
  ⟨ X.α₁ * Y.α₁ + (1 / 2 : ℝ) *
      ((X.z₃.mul Y.z₃.conj).a + (Y.z₃.mul X.z₃.conj).a +
       (X.z₂.conj.mul Y.z₂).a + (Y.z₂.conj.mul X.z₂).a),
    X.α₂ * Y.α₂ + (1 / 2 : ℝ) *
      ((X.z₃.conj.mul Y.z₃).a + (Y.z₃.conj.mul X.z₃).a +
       (X.z₁.mul Y.z₁.conj).a + (Y.z₁.mul X.z₁.conj).a),
    X.α₃ * Y.α₃ + (1 / 2 : ℝ) *
      ((X.z₂.mul Y.z₂.conj).a + (Y.z₂.mul X.z₂.conj).a +
       (X.z₁.conj.mul Y.z₁).a + (Y.z₁.conj.mul X.z₁).a),
    RealSplitOct.smul (1 / 2)
      (X.z₁.smul (Y.α₂ + Y.α₃) + Y.z₁.smul (X.α₂ + X.α₃) +
       X.z₃.conj.mul Y.z₂.conj + Y.z₃.conj.mul X.z₂.conj),
    RealSplitOct.smul (1 / 2)
      (X.z₂.smul (Y.α₃ + Y.α₁) + Y.z₂.smul (X.α₃ + X.α₁) +
       X.z₁.conj.mul Y.z₃.conj + Y.z₁.conj.mul X.z₃.conj),
    RealSplitOct.smul (1 / 2)
      (X.z₃.smul (Y.α₁ + Y.α₂) + Y.z₃.smul (X.α₁ + X.α₂) +
       X.z₂.conj.mul Y.z₁.conj + Y.z₂.conj.mul X.z₁.conj) ⟩

/-- Sparse normalization regression: the Hermitian matrix supported by the
unit split octonion in the `(1,2)` slot squares to the first two primitive
diagonal idempotents, with coefficient `1` rather than the erroneous doubled
coefficient `2`.
-/
theorem mul_upper_unit_self :
    let e : RealSplitOct := ⟨1, 1, 0, 0, 0, 0, 0, 0⟩
    let X : RealAlbertMatrix := ⟨0, 0, 0, RealSplitOct.zero, RealSplitOct.zero, e⟩
    (mul X X).α₁ = 1 ∧ (mul X X).α₂ = 1 ∧ (mul X X).α₃ = 0 := by
  norm_num [mul, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]

end RealAlbertMatrix

end
