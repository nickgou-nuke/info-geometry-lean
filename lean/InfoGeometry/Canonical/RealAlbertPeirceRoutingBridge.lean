import Mathlib.Tactic
import InfoGeometry.Canonical.AlbertPeirceChiralFrameEmbedding

/-!
# Native split-Albert Peirce routing

This file packages the off-diagonal support predicates for the native
`RealAlbertMatrix` carrier.  The coordinate fibres are the three existing
split-octonion embeddings from `AlbertPeirceChiralFrameEmbedding`; this file
does not introduce a second Albert carrier or identify the older abstract
`AlbertMatrix` predicates with them.

The file proves the available exact native Peirce routing identity together
with cyclic support-level routing statements.  It also proves
diagonal-support closure for the Peirce-triangle associator; it does not
assert an explicit associator value or identify it with the split-octonionic
associator.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra

noncomputable section

/-- Native support predicate for the `z₁` / `J₂₃` off-diagonal fibre. -/
def IsRealPeirce23 (X : RealAlbertMatrix) : Prop :=
  X.α₁ = 0 ∧ X.α₂ = 0 ∧ X.α₃ = 0 ∧
    X.z₂ = RealSplitOct.zero ∧ X.z₃ = RealSplitOct.zero

/-- Native support predicate for the `z₂` / `J₃₁` off-diagonal fibre. -/
def IsRealPeirce31 (X : RealAlbertMatrix) : Prop :=
  X.α₁ = 0 ∧ X.α₂ = 0 ∧ X.α₃ = 0 ∧
    X.z₁ = RealSplitOct.zero ∧ X.z₃ = RealSplitOct.zero

/-- Native support predicate for the `z₃` / `J₁₂` off-diagonal fibre. -/
def IsRealPeirce12 (X : RealAlbertMatrix) : Prop :=
  X.α₁ = 0 ∧ X.α₂ = 0 ∧ X.α₃ = 0 ∧
    X.z₁ = RealSplitOct.zero ∧ X.z₂ = RealSplitOct.zero

/-- Native diagonal-support predicate: all three off-diagonal fibres vanish. -/
def IsRealDiagonalSupport (X : RealAlbertMatrix) : Prop :=
  X.z₁ = RealSplitOct.zero ∧
    X.z₂ = RealSplitOct.zero ∧
    X.z₃ = RealSplitOct.zero

/-- The associator of the native split-Albert Jordan product. -/
def realAlbertJordanAssociator
    (X Y Z : RealAlbertMatrix) : RealAlbertMatrix :=
  RealAlbertMatrix.mul (RealAlbertMatrix.mul X Y) Z -
    RealAlbertMatrix.mul X (RealAlbertMatrix.mul Y Z)

@[simp] theorem peirce23_oct_isRealPeirce23 (x : RealSplitOct) :
    IsRealPeirce23 (peirce23_oct x) := by
  simp [IsRealPeirce23, peirce23_oct, RealSplitOct.zero]

@[simp] theorem peirce31_oct_isRealPeirce31 (x : RealSplitOct) :
    IsRealPeirce31 (peirce31_oct x) := by
  simp [IsRealPeirce31, peirce31_oct, RealSplitOct.zero]

@[simp] theorem peirce12_oct_isRealPeirce12 (x : RealSplitOct) :
    IsRealPeirce12 (peirce12_oct x) := by
  simp [IsRealPeirce12, peirce12_oct, RealSplitOct.zero]

theorem realAlbert_peirce23_mul_peirce12_isRealPeirce31
    (x y : RealSplitOct) :
    IsRealPeirce31
      (RealAlbertMatrix.mul (peirce23_oct x) (peirce12_oct y)) := by
  rw [peirce23_oct_mul_peirce12_oct_eq]
  exact peirce31_oct_isRealPeirce31 _

theorem realAlbert_peirce23_square_isDiagonalSupport
    (x : RealSplitOct) :
    IsRealDiagonalSupport
      (RealAlbertMatrix.mul (peirce23_oct x) (peirce23_oct x)) := by
  cases x
  simp [IsRealDiagonalSupport, peirce23_oct, RealAlbertMatrix.mul,
    RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul,
    RealSplitOct.add, RealSplitOct.smul]

theorem realAlbert_peirce31_square_isDiagonalSupport
    (x : RealSplitOct) :
    IsRealDiagonalSupport
      (RealAlbertMatrix.mul (peirce31_oct x) (peirce31_oct x)) := by
  cases x
  simp [IsRealDiagonalSupport, peirce31_oct, RealAlbertMatrix.mul,
    RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul,
    RealSplitOct.add, RealSplitOct.smul]

theorem realAlbert_peirce12_square_isDiagonalSupport
    (x : RealSplitOct) :
    IsRealDiagonalSupport
      (RealAlbertMatrix.mul (peirce12_oct x) (peirce12_oct x)) := by
  cases x
  simp [IsRealDiagonalSupport, peirce12_oct, RealAlbertMatrix.mul,
    RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul,
    RealSplitOct.add, RealSplitOct.smul]

theorem realAlbert_peirce31_mul_peirce23_isRealPeirce12
    (x y : RealSplitOct) :
    IsRealPeirce12
      (RealAlbertMatrix.mul (peirce31_oct x) (peirce23_oct y)) := by
  cases x
  cases y
  simp [IsRealPeirce12, peirce31_oct, peirce23_oct,
    RealAlbertMatrix.mul, RealSplitOct.zero, RealSplitOct.conj,
    RealSplitOct.mul, RealSplitOct.add, RealSplitOct.smul]

theorem realAlbert_peirce12_mul_peirce31_isRealPeirce23
    (x y : RealSplitOct) :
    IsRealPeirce23
      (RealAlbertMatrix.mul (peirce12_oct x) (peirce31_oct y)) := by
  cases x
  cases y
  simp [IsRealPeirce23, peirce12_oct, peirce31_oct,
    RealAlbertMatrix.mul, RealSplitOct.zero, RealSplitOct.conj,
    RealSplitOct.mul, RealSplitOct.add, RealSplitOct.smul]

theorem realAlbert_mul_isDiagonalSupport_of_peirce23
    (X Y : RealAlbertMatrix)
    (hX : IsRealPeirce23 X) (hY : IsRealPeirce23 Y) :
    IsRealDiagonalSupport (RealAlbertMatrix.mul X Y) := by
  rcases hX with ⟨hX₁, hX₂, hX₃, hX₂₃, hX₃₁⟩
  rcases hY with ⟨hY₁, hY₂, hY₃, hY₂₃, hY₃₁⟩
  cases X
  cases Y
  simp_all [IsRealDiagonalSupport, RealAlbertMatrix.mul,
    RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul,
    RealSplitOct.add, RealSplitOct.smul]

theorem realAlbert_mul_isDiagonalSupport_of_peirce31
    (X Y : RealAlbertMatrix)
    (hX : IsRealPeirce31 X) (hY : IsRealPeirce31 Y) :
    IsRealDiagonalSupport (RealAlbertMatrix.mul X Y) := by
  rcases hX with ⟨hX₁, hX₂, hX₃, hX₁₂, hX₃₁⟩
  rcases hY with ⟨hY₁, hY₂, hY₃, hY₁₂, hY₃₁⟩
  cases X
  cases Y
  simp_all [IsRealDiagonalSupport, RealAlbertMatrix.mul,
    RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul,
    RealSplitOct.add, RealSplitOct.smul]

theorem realAlbert_mul_isDiagonalSupport_of_peirce12
    (X Y : RealAlbertMatrix)
    (hX : IsRealPeirce12 X) (hY : IsRealPeirce12 Y) :
    IsRealDiagonalSupport (RealAlbertMatrix.mul X Y) := by
  rcases hX with ⟨hX₁, hX₂, hX₃, hX₂₃, hX₃₁⟩
  rcases hY with ⟨hY₁, hY₂, hY₃, hY₂₃, hY₃₁⟩
  cases X
  cases Y
  simp_all [IsRealDiagonalSupport, RealAlbertMatrix.mul,
    RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul,
    RealSplitOct.add, RealSplitOct.smul]

theorem realAlbert_diagonalSupport_sub
    (X Y : RealAlbertMatrix)
    (hX : IsRealDiagonalSupport X) (hY : IsRealDiagonalSupport Y) :
    IsRealDiagonalSupport (X - Y) := by
  rcases hX with ⟨hX₁, hX₂, hX₃⟩
  rcases hY with ⟨hY₁, hY₂, hY₃⟩
  constructor
  · change X.z₁ + -Y.z₁ = RealSplitOct.zero
    rw [hX₁, hY₁]
    ext <;> simp [RealSplitOct.zero, RealSplitOct.add, RealSplitOct.neg]
  constructor
  · change X.z₂ + -Y.z₂ = RealSplitOct.zero
    rw [hX₂, hY₂]
    ext <;> simp [RealSplitOct.zero, RealSplitOct.add, RealSplitOct.neg]
  · change X.z₃ + -Y.z₃ = RealSplitOct.zero
    rw [hX₃, hY₃]
    ext <;> simp [RealSplitOct.zero, RealSplitOct.add, RealSplitOct.neg]

theorem realAlbert_peirce_triangle_associator_isDiagonalSupport
    (x y z : RealSplitOct) :
    IsRealDiagonalSupport
      (realAlbertJordanAssociator
        (peirce23_oct x) (peirce12_oct y) (peirce31_oct z)) := by
  have hleft :
      IsRealDiagonalSupport
        (RealAlbertMatrix.mul
          (RealAlbertMatrix.mul (peirce23_oct x) (peirce12_oct y))
          (peirce31_oct z)) := by
    rw [peirce23_oct_mul_peirce12_oct_eq]
    exact realAlbert_mul_isDiagonalSupport_of_peirce31 _ _
      (peirce31_oct_isRealPeirce31 _) (peirce31_oct_isRealPeirce31 _)
  have hright :
      IsRealDiagonalSupport
        (RealAlbertMatrix.mul (peirce23_oct x)
          (RealAlbertMatrix.mul (peirce12_oct y) (peirce31_oct z))) :=
    realAlbert_mul_isDiagonalSupport_of_peirce23 _ _
      (peirce23_oct_isRealPeirce23 _)
      (realAlbert_peirce12_mul_peirce31_isRealPeirce23 y z)
  exact realAlbert_diagonalSupport_sub _ _ hleft hright

end
end InfoGeometry.Canonical
