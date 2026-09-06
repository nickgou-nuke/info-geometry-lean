import InfoGeometry.Canonical.ZornVectorMatrixExplicit
import InfoGeometry.Canonical.OperatorZornPolarizationSymmetry

/-!
# The native eight-dimensional Zorn polarization and its positive symmetry

A chiral four-slot sector consists of ONE scalar and THREE vector components.
It is not an independent scalar plus a four-vector. The signed exchange
`(a,b,u,v) ↦ (b,a,-v,-u)` is both multiplicative and a fundamental symmetry
for the polar form of the native scalar reduced norm. This finite result is
not a Tomita conjugation or a Klein-bottle deck construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornPolarizationMetricBridge

open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open InfoGeometry.Canonical.OperatorZornPolarizationSymmetry

/-- The explicit scalar-to-operator-coordinate comparison; multiplication is
still the Zorn product, never ordinary matrix multiplication. -/
def scalarLift (X : ZornCoord) : OperatorZornMatrix ℝ :=
  ⟨zornA X, zornB X, zornX X, zornY X⟩

theorem scalarLift_injective : Function.Injective scalarLift := by
  intro X Y h
  exact Prod.ext (congrArg InfoGeometry.Physics.NCG.NCZornElement.n_plus h)
    (Prod.ext (congrArg InfoGeometry.Physics.NCG.NCZornElement.n_minus h)
      (Prod.ext (congrArg InfoGeometry.Physics.NCG.NCZornElement.sigma_plus h)
        (congrArg InfoGeometry.Physics.NCG.NCZornElement.sigma_minus h)))

theorem scalarLift_mul (X Y : ZornCoord) :
    scalarLift (zornMul X Y) = operatorZornMul (scalarLift X) (scalarLift Y) := by
  apply operatorZornMatrix_ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;>
      simp [scalarLift, zornMul, zornMk, zornA, zornB, zornX, zornY, cross3,
        operatorZornMul, InfoGeometry.Physics.NCG.NCZornElement.mul,
        InfoGeometry.Physics.NCG.NCZornElement.zornCross, smul_eq_mul]
  · funext i
    fin_cases i <;>
      simp [scalarLift, zornMul, zornMk, zornA, zornB, zornX, zornY, cross3,
        operatorZornMul, InfoGeometry.Physics.NCG.NCZornElement.mul,
        InfoGeometry.Physics.NCG.NCZornElement.zornCross, smul_eq_mul] <;> ring

/-- Rearrange the existing scalar coordinates into two null four-dimensional sectors.
The minus sign places the native reduced norm in a positive cross-pairing convention. -/
def nullFourSplit : ZornCoord ≃ₗ[ℝ] ((ℝ × Vec3) × (ℝ × Vec3)) where
  toFun X := ((zornA X, zornX X), (zornB X, -zornY X))
  invFun X := zornMk X.1.1 X.2.1 X.1.2 (-X.2.2)
  left_inv X := by
    rcases X with ⟨a, b, u, v⟩
    simp [zornMk, zornA, zornB, zornX, zornY]
  right_inv X := by
    rcases X with ⟨⟨a, u⟩, ⟨b, v⟩⟩
    simp [zornMk, zornA, zornB, zornX, zornY]
  map_add' X Y := by
    ext <;> simp [zornA, zornB, zornX, zornY]
  map_smul' c X := by
    ext <;> simp [zornA, zornB, zornX, zornY]

theorem native_dimensions :
    Module.finrank ℝ ZornCoord = 8 ∧ Module.finrank ℝ (ℝ × Vec3) = 4 := by
  constructor <;> simp [ZornCoord, Vec3, Module.finrank_prod]

theorem norm_in_nullFourSplit (X : ZornCoord) :
    zornNorm X = (nullFourSplit X).1.1 * (nullFourSplit X).2.1 +
      dot3 (nullFourSplit X).1.2 (nullFourSplit X).2.2 := by
  simp [zornNorm, nullFourSplit, dot3] <;> ring

/-- Signed exchange on the actual scalar Zorn carrier. -/
def fundamental : ZornCoord ≃ₗ[ℝ] ZornCoord where
  toFun X := zornMk (zornB X) (zornA X) (-zornY X) (-zornX X)
  invFun X := zornMk (zornB X) (zornA X) (-zornY X) (-zornX X)
  left_inv X := by
    rcases X with ⟨a, b, u, v⟩
    simp [zornMk, zornA, zornB, zornX, zornY]
  right_inv X := by
    rcases X with ⟨a, b, u, v⟩
    simp [zornMk, zornA, zornB, zornX, zornY]
  map_add' X Y := by
    ext <;> simp [zornMk, zornA, zornB, zornX, zornY]
  map_smul' c X := by
    ext <;> simp [zornMk, zornA, zornB, zornX, zornY]

@[simp] theorem scalarLift_fundamental (X : ZornCoord) :
    scalarLift (fundamental X) = signedExchange (scalarLift X) := rfl

theorem fundamental_mul (X Y : ZornCoord) :
    fundamental (zornMul X Y) = zornMul (fundamental X) (fundamental Y) := by
  apply scalarLift_injective
  simp only [scalarLift_fundamental, scalarLift_mul, signedExchange_mul]

@[simp] theorem fundamental_sq (X : ZornCoord) : fundamental (fundamental X) = X := by
  apply scalarLift_injective
  simp only [scalarLift_fundamental, signedExchange_sq]

theorem fundamental_swaps_nullFour (X : ZornCoord) :
    nullFourSplit (fundamental X) = ((nullFourSplit X).2, (nullFourSplit X).1) := by
  rcases X with ⟨a, b, u, v⟩
  simp [nullFourSplit, fundamental, zornMk, zornA, zornB, zornX, zornY]

/-- The normalized polar pairing of the native reduced norm. -/
def polarPair (X Y : ZornCoord) : ℝ :=
  (zornA X * zornB Y + zornB X * zornA Y -
    dot3 (zornX X) (zornY Y) - dot3 (zornY X) (zornX Y)) / 2

/-- A native Mathlib bilinear form, not merely a numerical quadratic readout. -/
def polarForm : LinearMap.BilinForm ℝ ZornCoord :=
  LinearMap.mk₂ ℝ polarPair
    (by intro X Y Z; simp [polarPair, zornA, zornB, zornX, zornY, dot3] <;> ring)
    (by intro c X Y; simp [polarPair, zornA, zornB, zornX, zornY, dot3, smul_eq_mul] <;> ring)
    (by intro X Y Z; simp [polarPair, zornA, zornB, zornX, zornY, dot3] <;> ring)
    (by intro c X Y; simp [polarPair, zornA, zornB, zornX, zornY, dot3, smul_eq_mul] <;> ring)

@[simp] theorem polarForm_apply (X Y : ZornCoord) : polarForm X Y = polarPair X Y := rfl

theorem polarization_identity (X Y : ZornCoord) :
    2 * polarPair X Y = zornNorm (X + Y) - zornNorm X - zornNorm Y := by
  simp [polarPair, zornNorm, zornA, zornB, zornX, zornY, dot3] <;> ring

theorem polarPair_symm (X Y : ZornCoord) : polarPair X Y = polarPair Y X := by
  unfold polarPair dot3
  ring

@[simp] theorem polarPair_self (X : ZornCoord) : polarPair X X = zornNorm X := by
  unfold polarPair zornNorm dot3
  ring

theorem fundamental_norm (X : ZornCoord) : zornNorm (fundamental X) = zornNorm X := by
  simp [fundamental, zornNorm, zornMk, zornA, zornB, zornX, zornY, dot3] <;> ring

theorem fundamental_preserves_polar (X Y : ZornCoord) :
    polarPair (fundamental X) (fundamental Y) = polarPair X Y := by
  simp [fundamental, polarPair, zornMk, zornA, zornB, zornX, zornY, dot3] <;> ring

/-- The signed exchange supplies the positive Hilbertized form. -/
theorem hilbertized_pair (X Y : ZornCoord) :
    polarPair X (fundamental Y) =
      (zornA X * zornA Y + zornB X * zornB Y +
        dot3 (zornX X) (zornX Y) + dot3 (zornY X) (zornY Y)) / 2 := by
  simp [polarPair, fundamental, zornMk, zornA, zornB, zornX, zornY, dot3] <;> ring

theorem hilbertized_nonneg (X : ZornCoord) : 0 ≤ polarPair X (fundamental X) := by
  rw [hilbertized_pair]
  unfold dot3
  simp only [← pow_two]
  positivity

theorem hilbertized_zero_iff (X : ZornCoord) :
    polarPair X (fundamental X) = 0 ↔ X = 0 := by
  constructor
  · intro h
    rw [hilbertized_pair] at h
    rcases X with ⟨a, b, u, v⟩
    simp only [zornA, zornB, zornX, zornY, dot3] at h
    have ha : a = 0 := mul_self_eq_zero.mp (by nlinarith [sq_nonneg a, sq_nonneg b,
      sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2),
      sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)])
    have hb : b = 0 := mul_self_eq_zero.mp (by nlinarith [sq_nonneg a, sq_nonneg b,
      sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2),
      sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)])
    have hu : u = 0 := by
      funext i
      fin_cases i <;> apply mul_self_eq_zero.mp <;>
        nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (u 0), sq_nonneg (u 1),
          sq_nonneg (u 2), sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    have hv : v = 0 := by
      funext i
      fin_cases i <;> apply mul_self_eq_zero.mp <;>
        nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (u 0), sq_nonneg (u 1),
          sq_nonneg (u 2), sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    simp [ha, hb, hu, hv]
  · rintro rfl
    simp [polarPair, dot3, zornA, zornB, zornX, zornY]

theorem hilbertized_pos {X : ZornCoord} (hX : X ≠ 0) :
    0 < polarPair X (fundamental X) := by
  have hne : polarPair X (fundamental X) ≠ 0 := by
    intro h
    exact hX ((hilbertized_zero_iff X).mp h)
  exact lt_of_le_of_ne (hilbertized_nonneg X) (Ne.symm hne)

/-- The coordinate off-diagonal sign leaves this negative-norm diagonal
vector fixed. It is not a fundamental symmetry for the native reduced norm. -/
theorem diagonal_negative_witness :
    polarPair zornChirality zornChirality = -1 := by
  norm_num [polarPair, zornChirality, zornMk, zornA, zornB, zornX, zornY, dot3]

/-- A nonzero null idempotent separates zero norm from square-zero. -/
theorem null_not_square_zero :
    zornNorm (zornMk 1 0 0 0) = 0 ∧
      zornMul (zornMk 1 0 0 0) (zornMk 1 0 0 0) ≠ 0 := by
  constructor
  · norm_num [zornNorm, zornMk, zornA, zornB, zornX, zornY, dot3]
  · intro h
    have ha := congrArg zornA h
    norm_num [zornMul, zornMk, zornA, zornB, zornX, zornY, dot3] at ha

end InfoGeometry.Canonical.ZornPolarizationMetricBridge
