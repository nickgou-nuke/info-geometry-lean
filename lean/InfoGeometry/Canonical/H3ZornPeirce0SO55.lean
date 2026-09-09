import Mathlib
import InfoGeometry.Canonical.H3ZornPeirce0QuadraticHomothety
import InfoGeometry.Lie.SO55MatrixLieSubalgebra

/-!
# Infinitesimal metric generators on the ten-dimensional Peirce-0 block

This file proves the theorem-safe Lie-algebraic part of the spin-factor
interpretation.  It constructs the elementary bivector generators on the
actual `Minkowski10 = Fin 10 → ℝ` carrier and proves that they are skew for the
polarized quadratic form `BQ10`.

The repository already owns the authoritative matrix Lie subalgebra
`SO55MatrixSubalgebra.so55LieSubalgebra`, defined by
`Mᵀ η + η M = 0`.  We do not create a competing 45-dimensional matrix
carrier, and we do not claim that the bivectors below span that full algebra
until an explicit span/basis theorem is proved.
-/

noncomputable section

namespace InfoGeometry.Canonical.H3ZornPeirce0SO55

open Matrix
open InfoGeometry.Algebra
open InfoGeometry.Canonical.H3ZornPeirce0QuadraticRepresentation
open InfoGeometry.Canonical.H3ZornPeirce0QuadraticHomothety
open InfoGeometry.Lie.SO55MatrixSubalgebra

abbrev V10 := Minkowski10
abbrev End10 := V10 →ₗ[ℝ] V10

/-- Coordinate readback of the polarized spin-factor metric. -/
theorem BQ10_coordinate (u v : V10) :
    BQ10 u v =
      (1 / 2 : ℝ) *
        (u 0 * v 1 + u 1 * v 0 -
          zornPair (zornOfMinkowski10 u) (zornOfMinkowski10 v)) := by
  rfl

/-- Symmetry of the ten-dimensional polarized metric. -/
theorem BQ10_comm (u v : V10) : BQ10 u v = BQ10 v u := by
  unfold BQ10
  exact BPeirce_comm (toH3 u) (toH3 v)

/-- Additivity in the first argument. -/
theorem BQ10_add_left (u₁ u₂ v : V10) :
    BQ10 (u₁ + u₂) v = BQ10 u₁ v + BQ10 u₂ v := by
  rw [BQ10_coordinate, BQ10_coordinate, BQ10_coordinate]
  simp [zornPair, zornOfMinkowski10, ZornVectorMatrix.trace,
    ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVec3.dot,
    Fin.sum_univ_three]
  ring

/-- Homogeneity in the first argument. -/
theorem BQ10_smul_left (r : ℝ) (u v : V10) :
    BQ10 (r • u) v = r * BQ10 u v := by
  rw [BQ10_coordinate, BQ10_coordinate]
  simp [zornPair, zornOfMinkowski10, ZornVectorMatrix.trace,
    ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVec3.dot,
    Fin.sum_univ_three]
  ring

/-- Additivity in the second argument. -/
theorem BQ10_add_right (u v₁ v₂ : V10) :
    BQ10 u (v₁ + v₂) = BQ10 u v₁ + BQ10 u v₂ := by
  rw [BQ10_comm u (v₁ + v₂), BQ10_add_left,
    BQ10_comm v₁ u, BQ10_comm v₂ u]

/-- Homogeneity in the second argument. -/
theorem BQ10_smul_right (r : ℝ) (u v : V10) :
    BQ10 u (r • v) = r * BQ10 u v := by
  rw [BQ10_comm u (r • v), BQ10_smul_left, BQ10_comm v u]

/-- Negation in the first argument. -/
theorem BQ10_neg_left (u v : V10) : BQ10 (-u) v = -BQ10 u v := by
  simpa using BQ10_smul_left (-1 : ℝ) u v

/-- Negation in the second argument. -/
theorem BQ10_neg_right (u v : V10) : BQ10 u (-v) = -BQ10 u v := by
  simpa using BQ10_smul_right (-1 : ℝ) u v

/-- Subtraction in the first argument. -/
theorem BQ10_sub_left (u₁ u₂ v : V10) :
    BQ10 (u₁ - u₂) v = BQ10 u₁ v - BQ10 u₂ v := by
  rw [sub_eq_add_neg, BQ10_add_left, BQ10_neg_left]
  ring

/-- Subtraction in the second argument. -/
theorem BQ10_sub_right (u v₁ v₂ : V10) :
    BQ10 u (v₁ - v₂) = BQ10 u v₁ - BQ10 u v₂ := by
  rw [sub_eq_add_neg, BQ10_add_right, BQ10_neg_right]
  ring

/-- Infinitesimal orthogonality condition for the Peirce metric. -/
def InSO55BQ (T : End10) : Prop :=
  ∀ u v : V10, BQ10 (T u) v + BQ10 u (T v) = 0

/-- The elementary rank-two bivector action
`M_{x,y}(z)=2(B(y,z)x-B(x,z)y)`. -/
noncomputable def bivectorGen (x y : V10) : End10 where
  toFun := fun z =>
    (2 : ℝ) • (BQ10 y z • x - BQ10 x z • y)
  map_add' z w := by
    rw [BQ10_add_right, BQ10_add_right]
    module
  map_smul' r z := by
    rw [BQ10_smul_right, BQ10_smul_right]
    simp [smul_sub, smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- Every elementary bivector is skew-adjoint for `BQ10`. -/
theorem bivectorGen_in_so55 (x y : V10) :
    InSO55BQ (bivectorGen x y) := by
  intro u v
  dsimp [bivectorGen]
  rw [BQ10_smul_left, BQ10_sub_left,
    BQ10_smul_left, BQ10_smul_left,
    BQ10_smul_right, BQ10_sub_right,
    BQ10_smul_right, BQ10_smul_right,
    BQ10_comm x v, BQ10_comm y v,
    BQ10_comm u x, BQ10_comm u y]
  ring

/-- Skewness in the bivector labels. -/
theorem bivectorGen_swap (x y : V10) :
    bivectorGen x y = -bivectorGen y x := by
  ext z i
  dsimp [bivectorGen]
  ring

/-- Commutator of two linear endomorphisms. -/
def bracket (T U : End10) : End10 := T.comp U - U.comp T

/-- The metric-skew condition is closed under commutators. -/
theorem bracket_closed
    {T U : End10} (hT : InSO55BQ T) (hU : InSO55BQ U) :
    InSO55BQ (bracket T U) := by
  intro x y
  rw [bracket]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    BQ10_sub_left, BQ10_sub_right]
  have h1 := hT (U x) y
  have h2 := hU x (T y)
  have h3 := hU (T x) y
  have h4 := hT x (U y)
  linarith

/-- Compact theorem packet for the elementary infinitesimal generators. -/
theorem peirce0_so55_packet :
    (∀ x y : V10, InSO55BQ (bivectorGen x y)) ∧
    (∀ T U : End10,
      InSO55BQ T → InSO55BQ U → InSO55BQ (bracket T U)) := by
  exact ⟨bivectorGen_in_so55, fun T U => bracket_closed⟩

/-- The authoritative native matrix `so(5,5)` carrier already exists in the
repository.  This theorem exposes its defining condition without claiming a
span equivalence from the new bivector family. -/
theorem native_so55_matrix_characterization
    (M : Matrix (Fin 10) (Fin 10) ℝ) :
    M ∈ so55LieSubalgebra ↔ Mᵀ * eta55 + eta55 * M = 0 :=
  Iff.rfl

end InfoGeometry.Canonical.H3ZornPeirce0SO55
