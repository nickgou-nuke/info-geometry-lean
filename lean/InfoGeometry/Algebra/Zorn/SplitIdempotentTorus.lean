import InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation

/-!
# A real split torus fixes both Zorn idempotents

The upper vector transforms by diag(t,1/t,1), and the lower vector by the
inverse transpose. Their determinant is one. The full Zorn product, not
only the quadratic norm, is preserved. This concrete real family must not
be confused with unitary rotations of a positive Hermitian three-space.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.SplitIdempotentTorus

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

local notation "Zorn" => InfoGeometry.Canonical.ZornMatrix ℝ
local notation "U" => InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ)
local notation "polePlus" => InfoGeometry.Canonical.ZornMatrix.zornPlus (R := ℝ)
local notation "poleMinus" => InfoGeometry.Canonical.ZornMatrix.zornMinus (R := ℝ)

/-- The explicit upper-vector and lower-covector action. -/
def torusMap (t : ℝ) (X : Zorn) : Zorn where
  a := X.a
  b := X.b
  x := ![t * X.x 0, t⁻¹ * X.x 1, X.x 2]
  y := ![t⁻¹ * X.y 0, t * X.y 1, X.y 2]

theorem torusMap_inverse (t : ℝ) (ht : t ≠ 0) (X : Zorn) :
    torusMap t⁻¹ (torusMap t X) = X := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [torusMap, ht, mul_assoc]

/-- An actual invertible real-linear map, retaining its regularity domain. -/
def torusEquiv (t : ℝ) (ht : t ≠ 0) : Zorn ≃ₗ[ℝ] Zorn where
  toFun := torusMap t
  invFun := torusMap t⁻¹
  left_inv := torusMap_inverse t ht
  right_inv X := by
    simpa using torusMap_inverse t⁻¹ (inv_ne_zero ht) X
  map_add' X Y := by
    apply InfoGeometry.Canonical.ZornMatrix.ext <;>
      first | (funext k; fin_cases k) | skip
    all_goals simp [torusMap, mul_add]
  map_smul' r X := by
    apply InfoGeometry.Canonical.ZornMatrix.ext <;>
      first | (funext k; fin_cases k) | skip
    all_goals simp [torusMap, mul_left_comm]
    all_goals
      simp only [InfoGeometry.Canonical.ZornMatrix.smul_a,
        InfoGeometry.Canonical.ZornMatrix.smul_b,
        InfoGeometry.Canonical.ZornMatrix.smul_x,
        InfoGeometry.Canonical.ZornMatrix.smul_y]
      all_goals try simp [Pi.smul_apply]
      all_goals try ring

/-- Determinant-one scaling preserves the full native nonassociative product. -/
theorem torusMap_mul (t : ℝ) (ht : t ≠ 0) (X Y : Zorn) :
    torusMap t (X * Y) = torusMap t X * torusMap t Y := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [torusMap, InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals field_simp [ht] <;> ring

/-- Membership in the repository's genuine multiplication automorphism group. -/
def torusAut (t : ℝ) (ht : t ≠ 0) : realZornCompositionAut :=
  ⟨torusEquiv t ht, fun X Y => torusMap_mul t ht X Y⟩

theorem torusMap_fixes_poles (t : ℝ) :
    torusMap t polePlus = polePlus ∧ torusMap t poleMinus = poleMinus := by
  constructor <;> apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [torusMap, InfoGeometry.Canonical.ZornMatrix.zornPlus,
    InfoGeometry.Canonical.ZornMatrix.zornMinus]

theorem torusMap_upper_first (t : ℝ) : torusMap t (U 0) = t • U 0 := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    first | (funext k; fin_cases k) | skip
  all_goals simp [torusMap, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
    InfoGeometry.Canonical.ZornMatrix.smul_a,
    InfoGeometry.Canonical.ZornMatrix.smul_b,
    InfoGeometry.Canonical.ZornMatrix.smul_x,
    InfoGeometry.Canonical.ZornMatrix.smul_y, Pi.single_apply]

/-- The idempotent stabilizer contains real stretches, not only unitary rotations. -/
theorem fixed_poles_not_euclidean_upper_isometry :
    (torusMap 2 (U 0)).x 0 ^ 2 + (torusMap 2 (U 0)).x 1 ^ 2 +
      (torusMap 2 (U 0)).x 2 ^ 2 ≠
      (U 0).x 0 ^ 2 + (U 0).x 1 ^ 2 + (U 0).x 2 ^ 2 := by
  norm_num [torusMap, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
    Pi.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

end InfoGeometry.Algebra.Zorn.SplitIdempotentTorus
