import Mathlib
import InfoGeometry.Canonical.SplitSpinFactorHomothetySO55

noncomputable section

namespace InfoGeometry.Canonical.SplitSpinFactorTKKSO66

open InfoGeometry.Canonical.SplitSpinFactorHomothetySO55
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
open InfoGeometry.Canonical.SplitOctonionTKKFiniteDimensionalBridges

abbrev V10 := SplitSpacetime10
abbrev Carrier12 := ℝ × V10 × ℝ
abbrev End12 := Module.End ℝ Carrier12

/-- Polar form of the split ten-dimensional quadratic interval. -/
def B10 (u v : V10) : ℝ :=
  (1 / 2 : ℝ) *
    (u.1.1 * v.1.2 + u.1.2 * v.1.1 - zornPolar u.2 v.2)

@[simp] theorem B10_symm (u v : V10) : B10 u v = B10 v u := by
  simp [B10, zornPolar_symm]
  ring

@[simp] theorem B10_self (u : V10) : B10 u u = splitInterval10 u := by
  rw [B10]
  rw [zornPolar_self]
  simp [splitInterval10, InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary.h2SplitDet]
  ring

@[simp] theorem B10_add_left (u v w : V10) :
    B10 (u + v) w = B10 u w + B10 v w := by
  rcases u with ⟨⟨u2,u3⟩,ux⟩
  rcases v with ⟨⟨v2,v3⟩,vx⟩
  rcases w with ⟨⟨w2,w3⟩,wx⟩
  simp [B10, zornPolar, InfoGeometry.Algebra.ZornVectorMatrix.trace,
    InfoGeometry.Algebra.ZornVectorMatrix.mul,
    InfoGeometry.Algebra.ZornVectorMatrix.conj,
    InfoGeometry.Algebra.ZornVectorMatrix.add,
    InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three]
  ring

@[simp] theorem B10_smul_left (r : ℝ) (u v : V10) :
    B10 (r • u) v = r * B10 u v := by
  rcases u with ⟨⟨u2,u3⟩,ux⟩
  rcases v with ⟨⟨v2,v3⟩,vx⟩
  simp [B10, zornPolar, InfoGeometry.Algebra.ZornVectorMatrix.trace,
    InfoGeometry.Algebra.ZornVectorMatrix.mul,
    InfoGeometry.Algebra.ZornVectorMatrix.conj,
    InfoGeometry.Algebra.ZornVectorMatrix.smul,
    InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three]
  ring

@[simp] theorem B10_add_right (u v w : V10) :
    B10 u (v + w) = B10 u v + B10 u w := by
  rw [B10_symm, B10_add_left, B10_symm v u, B10_symm w u]

@[simp] theorem B10_smul_right (r : ℝ) (u v : V10) :
    B10 u (r • v) = r * B10 u v := by
  rw [B10_symm, B10_smul_left, B10_symm v u]

/-- Neutral bilinear form on `ℝ ⊕ V10 ⊕ ℝ`. -/
def B66 (x y : Carrier12) : ℝ :=
  x.1 * y.2.2 + x.2.2 * y.1 + B10 x.2.1 y.2.1

@[simp] theorem B66_symm (x y : Carrier12) : B66 x y = B66 y x := by
  simp [B66, B10_symm]
  ring

/-- Infinitesimal orthogonality condition for the concrete conformal carrier. -/
def IsB66Skew (A : End12) : Prop :=
  ∀ x y, B66 (A x) y + B66 x (A y) = 0

/-- Grade `-1`: translation generator attached to `u`. -/
def translation (u : V10) : End12 where
  toFun x := (-B10 u x.2.1, (x.2.2 • u, 0))
  map_add' x y := by
    ext <;> simp [B10_add_right, add_mul]
  map_smul' r x := by
    ext <;> simp [B10_smul_right, mul_assoc]

/-- Grade `+1`: special-conformal generator attached to `v`. -/
def specialConformal (v : V10) : End12 where
  toFun x := (0, (x.1 • v, -B10 v x.2.1))
  map_add' x y := by
    ext <;> simp [B10_add_right, add_mul]
  map_smul' r x := by
    ext <;> simp [B10_smul_right, mul_assoc]

/-- Grade zero scalar dilation. -/
def dilation (a : ℝ) : End12 where
  toFun x := (a * x.1, (0, -a * x.2.2))
  map_add' x y := by ext <;> simp [mul_add]
  map_smul' r x := by ext <;> simp [mul_assoc, mul_left_comm]

@[simp] theorem translation_isB66Skew (u : V10) : IsB66Skew (translation u) := by
  intro x y
  simp [IsB66Skew, B66, translation, B10_smul_left, B10_smul_right, B10_symm]
  ring

@[simp] theorem specialConformal_isB66Skew (v : V10) :
    IsB66Skew (specialConformal v) := by
  intro x y
  simp [IsB66Skew, B66, specialConformal, B10_smul_left, B10_smul_right, B10_symm]
  ring

@[simp] theorem dilation_isB66Skew (a : ℝ) : IsB66Skew (dilation a) := by
  intro x y
  simp [IsB66Skew, B66, dilation, B10]
  ring

/-- Embed a ten-dimensional infinitesimal orthogonal transformation into the
middle block of the twelve-dimensional conformal carrier. -/
def middleRotation (A : Module.End ℝ V10) : End12 where
  toFun x := (0, (A x.2.1, 0))
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- Any `B10`-skew middle transformation is `B66`-skew after embedding. -/
theorem middleRotation_isB66Skew
    (A : Module.End ℝ V10)
    (hA : ∀ u v, B10 (A u) v + B10 u (A v) = 0) :
    IsB66Skew (middleRotation A) := by
  intro x y
  simpa [IsB66Skew, B66, middleRotation] using hA x.2.1 y.2.1

/-- Endomorphism commutator used for the explicit three-grading laws. -/
def commutator (A B : End12) : End12 := A * B - B * A

@[simp] theorem translation_commutes_translation (u v : V10) :
    commutator (translation u) (translation v) = 0 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [commutator, translation, B10_smul_right, B10_symm] <;> ring

@[simp] theorem specialConformal_commutes_specialConformal (u v : V10) :
    commutator (specialConformal u) (specialConformal v) = 0 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [commutator, specialConformal, B10_smul_right, B10_symm] <;> ring

/-- Dilation acts with weight `+1` on the translation convention used here. -/
theorem dilation_comm_translation (a : ℝ) (u : V10) :
    commutator (dilation a) (translation u) = translation (a • u) := by
  apply LinearMap.ext
  intro x
  ext <;> simp [commutator, dilation, translation, B10_smul_left, B10_smul_right] <;> ring

/-- Dilation acts with the opposite weight on special conformal generators. -/
theorem dilation_comm_specialConformal (a : ℝ) (v : V10) :
    commutator (dilation a) (specialConformal v) =
      - specialConformal (a • v) := by
  apply LinearMap.ext
  intro x
  ext <;> simp [commutator, dilation, specialConformal,
    B10_smul_left, B10_smul_right] <;> ring

/-- Rank-two middle rotation generated by a pair of spin-factor vectors. -/
def rankTwoRotation (u v : V10) : Module.End ℝ V10 where
  toFun z := B10 u z • v - B10 v z • u
  map_add' x y := by
    simp [B10_add_right, add_smul, sub_eq_add_neg]
    module
  map_smul' r x := by
    simp [B10_smul_right, smul_smul, sub_eq_add_neg]
    module

/-- The rank-two middle rotation is infinitesimally `B10`-orthogonal. -/
theorem rankTwoRotation_skew (u v x y : V10) :
    B10 (rankTwoRotation u v x) y + B10 x (rankTwoRotation u v y) = 0 := by
  simp [rankTwoRotation, B10_add_left, B10_add_right, B10_smul_left,
    B10_smul_right, B10_symm]
  ring

/-- The TKK cross-bracket lands in grade zero: one scalar dilation plus one
rank-two orthogonal middle rotation. -/
theorem translation_specialConformal_cross_bracket (u v : V10) :
    commutator (translation u) (specialConformal v) =
      dilation (-B10 u v) + middleRotation (rankTwoRotation u v) := by
  apply LinearMap.ext
  intro x
  ext <;> simp [commutator, translation, specialConformal, dilation,
    middleRotation, rankTwoRotation, B10_smul_left, B10_smul_right, B10_symm] <;> ring

/-- Coordinate dimension packet of the three-graded conformal construction. -/
theorem tkk_dimension_packet :
    Module.finrank ℝ V10 = 10 ∧
    Module.finrank ℝ (So55 × ℝ) = 46 ∧
    10 + 46 + 10 = 66 := by
  constructor
  · simp [V10, SplitSpacetime10, PeirceZeroCoord]
    rw [InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary.zorn_finrank_eq_eight]
    norm_num
  constructor
  · rw [Module.finrank_prod, so55_finrank]
    simp
  · norm_num

/-- Mathlib's split type-D6 target Lie algebra. -/
abbrev TKKTypeD6 := LieAlgebra.Orthogonal.typeD (Fin 6) ℝ

/-- The expected target dimension arithmetic for `so(6,6)`.  The explicit Lie
isomorphism from the generated three-graded subalgebra to `TKKTypeD6` remains a
separate construction. -/
theorem so66_expected_dimension : 12 * 11 / 2 = 66 := by norm_num

end InfoGeometry.Canonical.SplitSpinFactorTKKSO66
