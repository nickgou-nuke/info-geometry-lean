import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The algebraic KKS form

For a Lie algebra `L` and a linear functional `μ`, the KKS pairing is the
pullback of `μ` along the Lie bracket.  This file deliberately owns only the
algebraic statement.  Smooth orbit manifolds, non-degeneracy on a tangent
space, and Fisher metrics require additional analytic and geometric owners.
-/

namespace SouriauKKS

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The algebraic Kirillov--Kostant--Souriau 2-form at `μ`. -/
def kksForm (μ : Module.Dual R L) (X Y : L) : R := μ ⁅X, Y⁆

theorem kksForm_skew (μ : Module.Dual R L) (X Y : L) :
    kksForm μ X Y = -kksForm μ Y X := by
  unfold kksForm
  calc
    μ ⁅X, Y⁆ = μ (-⁅Y, X⁆) := congrArg μ (lie_skew X Y).symm
    _ = -μ ⁅Y, X⁆ := μ.map_neg _

theorem kksForm_add_left (μ : Module.Dual R L) (X₁ X₂ Y : L) :
    kksForm μ (X₁ + X₂) Y = kksForm μ X₁ Y + kksForm μ X₂ Y := by
  unfold kksForm
  calc
    μ ⁅X₁ + X₂, Y⁆ = μ (⁅X₁, Y⁆ + ⁅X₂, Y⁆) :=
      congrArg μ (add_lie X₁ X₂ Y)
    _ = μ ⁅X₁, Y⁆ + μ ⁅X₂, Y⁆ := μ.map_add _ _

theorem kksForm_add_right (μ : Module.Dual R L) (X Y₁ Y₂ : L) :
    kksForm μ X (Y₁ + Y₂) = kksForm μ X Y₁ + kksForm μ X Y₂ := by
  unfold kksForm
  calc
    μ ⁅X, Y₁ + Y₂⁆ = μ (⁅X, Y₁⁆ + ⁅X, Y₂⁆) :=
      congrArg μ (lie_add X Y₁ Y₂)
    _ = μ ⁅X, Y₁⁆ + μ ⁅X, Y₂⁆ := μ.map_add _ _

theorem kksForm_smul_left (μ : Module.Dual R L) (a : R) (X Y : L) :
    kksForm μ (a • X) Y = a * kksForm μ X Y := by
  unfold kksForm
  calc
    μ ⁅a • X, Y⁆ = μ (a • ⁅X, Y⁆) := congrArg μ (smul_lie a X Y)
    _ = a * μ ⁅X, Y⁆ := by rw [μ.map_smul]; rfl

theorem kksForm_smul_right (μ : Module.Dual R L) (a : R) (X Y : L) :
    kksForm μ X (a • Y) = a * kksForm μ X Y := by
  unfold kksForm
  calc
    μ ⁅X, a • Y⁆ = μ (a • ⁅X, Y⁆) := congrArg μ (lie_smul a X Y)
    _ = a * μ ⁅X, Y⁆ := by rw [μ.map_smul]; rfl

/-- The KKS form is closed in the Lie-algebraic Chevalley--Eilenberg sense. -/
theorem kksForm_jacobi (μ : Module.Dual R L) (X Y Z : L) :
    kksForm μ X ⁅Y, Z⁆ + kksForm μ Y ⁅Z, X⁆ + kksForm μ Z ⁅X, Y⁆ = 0 := by
  unfold kksForm
  calc
    μ ⁅X, ⁅Y, Z⁆⁆ + μ ⁅Y, ⁅Z, X⁆⁆ + μ ⁅Z, ⁅X, Y⁆⁆ =
        μ (⁅X, ⁅Y, Z⁆⁆ + ⁅Y, ⁅Z, X⁆⁆ + ⁅Z, ⁅X, Y⁆⁆) := by
      rw [μ.map_add, μ.map_add]
    _ = μ 0 := congrArg μ (lie_jacobi X Y Z)
    _ = 0 := μ.map_zero

/-- Affine KKS form obtained by adding a Lie-algebra two-cocycle. -/
def affineKksForm
    (μ : Module.Dual R L) (θ : L →ₗ[R] L →ₗ[R] R) (X Y : L) : R :=
  kksForm μ X Y + θ X Y

/-- Skewness of an affine KKS form from skewness of its cocycle. -/
theorem affineKksForm_skew
    (μ : Module.Dual R L) (θ : L →ₗ[R] L →ₗ[R] R)
    (hθ : ∀ X Y, θ X Y = -θ Y X) (X Y : L) :
    affineKksForm μ θ X Y = -affineKksForm μ θ Y X := by
  unfold affineKksForm
  rw [kksForm_skew, hθ]
  abel

/-- Additivity of an affine KKS form in its first Lie-algebra argument. -/
theorem affineKksForm_add_left
    (μ : Module.Dual R L) (θ : L →ₗ[R] L →ₗ[R] R)
    (X₁ X₂ Y : L) :
    affineKksForm μ θ (X₁ + X₂) Y =
      affineKksForm μ θ X₁ Y + affineKksForm μ θ X₂ Y := by
  unfold affineKksForm
  rw [kksForm_add_left, θ.map_add]
  simp only [LinearMap.add_apply]
  abel

/-- Additivity of an affine KKS form in its second Lie-algebra argument. -/
theorem affineKksForm_add_right
    (μ : Module.Dual R L) (θ : L →ₗ[R] L →ₗ[R] R)
    (X Y₁ Y₂ : L) :
    affineKksForm μ θ X (Y₁ + Y₂) =
      affineKksForm μ θ X Y₁ + affineKksForm μ θ X Y₂ := by
  unfold affineKksForm
  rw [kksForm_add_right, (θ X).map_add]
  abel

/-- The affine KKS cyclic cocycle identity. -/
theorem affineKksForm_cocycle
    (μ : Module.Dual R L) (θ : L →ₗ[R] L →ₗ[R] R)
    (hθ : ∀ X Y Z,
      θ X ⁅Y, Z⁆ + θ Y ⁅Z, X⁆ + θ Z ⁅X, Y⁆ = 0)
    (X Y Z : L) :
    affineKksForm μ θ X ⁅Y, Z⁆ +
    affineKksForm μ θ Y ⁅Z, X⁆ +
        affineKksForm μ θ Z ⁅X, Y⁆ = 0 := by
  unfold affineKksForm
  calc
    (kksForm μ X ⁅Y, Z⁆ + θ X ⁅Y, Z⁆) +
        (kksForm μ Y ⁅Z, X⁆ + θ Y ⁅Z, X⁆) +
        (kksForm μ Z ⁅X, Y⁆ + θ Z ⁅X, Y⁆) =
      (kksForm μ X ⁅Y, Z⁆ + kksForm μ Y ⁅Z, X⁆ +
          kksForm μ Z ⁅X, Y⁆) +
        (θ X ⁅Y, Z⁆ + θ Y ⁅Z, X⁆ + θ Z ⁅X, Y⁆) := by abel
    _ = 0 + 0 := by rw [kksForm_jacobi, hθ]
    _ = 0 := add_zero 0

end SouriauKKS
