import Mathlib

/-!
# Real Split-Albert Carrier

This file provides the genuine $\mathbb{R}$-bilinear vector space for the split-Albert algebra,
which serves as the canonical 27-dimensional carrier for the $F_4$ derivation algebra.

The coordinates are given as an element of $\mathbb{R}^3$ for the diagonal entries,
and three copies of the real split-octonions $\mathbb{R}^8$ for the off-diagonal entries.
-/

namespace InfoGeometry.Algebra

/-- The genuine real split-octonion algebra carrier $\mathbb{R}^8$. -/
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

instance : AddCommGroup RealSplitOct where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  nsmul_zero := sorry
  nsmul_succ := sorry
  sub_eq_add_neg := sorry
  zsmul := zsmulRec
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  neg_add_cancel := sorry
  add_comm := sorry

instance : Module ℝ RealSplitOct where
  smul := smul
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

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

/-- The genuine real Albert matrix algebra carrier $\mathbb{R}^{27}$. -/
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

instance : AddCommGroup RealAlbertMatrix where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  nsmul_zero := sorry
  nsmul_succ := sorry
  sub_eq_add_neg := sorry
  zsmul := zsmulRec
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  neg_add_cancel := sorry
  add_comm := sorry

instance : Module ℝ RealAlbertMatrix where
  smul := smul
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Jordan product of two Albert matrices. -/
def mul (X Y : RealAlbertMatrix) : RealAlbertMatrix :=
  ⟨ X.α₁ * Y.α₁ + (X.z₃.mul Y.z₃.conj).a + (Y.z₃.mul X.z₃.conj).a + (X.z₂.conj.mul Y.z₂).a + (Y.z₂.conj.mul X.z₂).a,
    X.α₂ * Y.α₂ + (X.z₃.conj.mul Y.z₃).a + (Y.z₃.conj.mul X.z₃).a + (X.z₁.mul Y.z₁.conj).a + (Y.z₁.mul X.z₁.conj).a,
    X.α₃ * Y.α₃ + (X.z₂.mul Y.z₂.conj).a + (Y.z₂.mul X.z₂.conj).a + (X.z₁.conj.mul Y.z₁).a + (Y.z₁.conj.mul X.z₁).a,
    RealSplitOct.smul (1/2) (X.z₁.smul (Y.α₂ + Y.α₃) + Y.z₁.smul (X.α₂ + X.α₃) + X.z₂.conj.mul Y.z₃.conj + Y.z₂.conj.mul X.z₃.conj),
    RealSplitOct.smul (1/2) (X.z₂.smul (Y.α₃ + Y.α₁) + Y.z₂.smul (X.α₃ + X.α₁) + X.z₃.conj.mul Y.z₁.conj + Y.z₃.conj.mul X.z₁.conj),
    RealSplitOct.smul (1/2) (X.z₃.smul (Y.α₁ + Y.α₂) + Y.z₃.smul (X.α₁ + X.α₂) + X.z₁.conj.mul Y.z₂.conj + Y.z₁.conj.mul X.z₂.conj) ⟩

end RealAlbertMatrix

end
