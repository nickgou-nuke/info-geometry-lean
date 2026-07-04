import InfoGeometry.Algebra.Zorn.ConcreteComposition

/-!
# Concrete Zorn adjugate identities

This module records the native adjugate/conjugation identities for the concrete
Zorn composition product.  For a Zorn cell `X`, its conjugate `conjZ X` is the
split-octonion adjugate and both products collapse to the scalar determinant
cell.
-/

namespace InfoGeometry.Algebra.Zorn.ConcreteComposition
namespace ZornCell

variable {R : Type*} [CommRing R]

/-- Multiplicative identity cell for the concrete Zorn product. -/
def oneZ : ZornCell R :=
  ⟨1, 1, 0, 0, 0, 0, 0, 0⟩

/-- Scalar diagonal cell `c · 1`. -/
def scalarZ (c : R) : ZornCell R :=
  ⟨c, c, 0, 0, 0, 0, 0, 0⟩

/-- Coordinatewise scalar multiplication of a concrete Zorn cell. -/
def scaleZ (c : R) (X : ZornCell R) : ZornCell R :=
  ⟨c * X.r, c * X.s, c * X.x1, c * X.x2, c * X.x3,
    c * X.y1, c * X.y2, c * X.y3⟩

/-- Right scalar extraction for the concrete Zorn product. -/
theorem mul_scaleZ_right (c : R) (X Y : ZornCell R) :
    X * scaleZ c Y = scaleZ c (X * Y) := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rcases Y with ⟨r', s', x1', x2', x3', y1', y2', y3'⟩
  change mulZ _ (scaleZ c _) = scaleZ c (mulZ _ _)
  unfold mulZ
  simp [scaleZ]
  repeat' constructor <;> first | ring_nf | trivial

/-- Left scalar extraction for the concrete Zorn product. -/
theorem mul_scaleZ_left (c : R) (X Y : ZornCell R) :
    scaleZ c X * Y = scaleZ c (X * Y) := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rcases Y with ⟨r', s', x1', x2', x3', y1', y2', y3'⟩
  change mulZ (scaleZ c _) _ = scaleZ c (mulZ _ _)
  unfold mulZ
  simp [scaleZ]
  repeat' constructor <;> first | ring_nf | trivial

/-- Zorn conjugation / adjugate: swap diagonal slots and negate vector slots. -/
def conjZ (X : ZornCell R) : ZornCell R :=
  ⟨X.s, X.r, -X.x1, -X.x2, -X.x3, -X.y1, -X.y2, -X.y3⟩

/-- Left adjugate identity: `X * conjZ X = detZ X · 1`. -/
theorem mul_conjZ (X : ZornCell R) :
    X * conjZ X = scalarZ (detZ X) := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  unfold conjZ scalarZ detZ
  change mulZ _ _ = _
  unfold mulZ
  congr <;> ring

/-- Right adjugate identity: `conjZ X * X = detZ X · 1`. -/
theorem conjZ_mul (X : ZornCell R) :
    conjZ X * X = scalarZ (detZ X) := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  unfold conjZ scalarZ detZ
  change mulZ _ _ = _
  unfold mulZ
  congr <;> ring

/-- The adjugate identities as a paired packet. -/
theorem adjugate_identity_packet (X : ZornCell R) :
    X * conjZ X = scalarZ (detZ X) ∧
      conjZ X * X = scalarZ (detZ X) := by
  exact ⟨mul_conjZ X, conjZ_mul X⟩

variable {K : Type*} [Field K]

/-- Scaling a determinant scalar cell by the inverse determinant gives the identity cell. -/
theorem scaleZ_scalarZ_inv_det
    (X : ZornCell K) (h : detZ X ≠ 0) :
    scaleZ (detZ X)⁻¹ (scalarZ (detZ X)) = oneZ := by
  unfold scaleZ scalarZ oneZ
  congr <;> simp [h]

/-- Non-null inverse candidate is a left inverse. -/
theorem inverseCandidate_left
    (X : ZornCell K) (h : detZ X ≠ 0) :
    X * scaleZ (detZ X)⁻¹ (conjZ X) = oneZ := by
  rw [mul_scaleZ_right, mul_conjZ]
  exact scaleZ_scalarZ_inv_det X h

/-- Non-null inverse candidate is a right inverse. -/
theorem inverseCandidate_right
    (X : ZornCell K) (h : detZ X ≠ 0) :
    scaleZ (detZ X)⁻¹ (conjZ X) * X = oneZ := by
  rw [mul_scaleZ_left, conjZ_mul]
  exact scaleZ_scalarZ_inv_det X h

/-- Paired inverse-candidate packet on the non-null determinant locus. -/
theorem inverseCandidate_packet
    (X : ZornCell K) (h : detZ X ≠ 0) :
    X * scaleZ (detZ X)⁻¹ (conjZ X) = oneZ ∧
      scaleZ (detZ X)⁻¹ (conjZ X) * X = oneZ := by
  exact ⟨inverseCandidate_left X h, inverseCandidate_right X h⟩

end ZornCell
end InfoGeometry.Algebra.Zorn.ConcreteComposition
