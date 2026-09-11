import Mathlib.CategoryTheory.Category.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

namespace InfoGeometry.Canonical.GeometricTower

open CategoryTheory

/- A sequence of real modules used as finite tower stages. -/
variable (V : ℕ → Type) [∀ n, AddCommGroup (V n)] [∀ n, Module ℝ (V n)]

/-- A linear embedding together with explicit quadratic forms and the preservation law. -/
structure IsometricEmbedding
    (V_n V_m : Type)
    [AddCommGroup V_n] [Module ℝ V_n]
    [AddCommGroup V_m] [Module ℝ V_m] where
  Q_n : QuadraticForm ℝ V_n
  Q_m : QuadraticForm ℝ V_m
  map : V_n →ₗ[ℝ] V_m
  is_isometry : ∀ x, Q_m (map x) = Q_n x

/-- The structure field gives the exact quadratic-form preservation equation. -/
theorem IsometricEmbedding.preserves_quadratic
    {V_n V_m : Type}
    [AddCommGroup V_n] [Module ℝ V_n]
    [AddCommGroup V_m] [Module ℝ V_m]
    (f : IsometricEmbedding V_n V_m) (x : V_n) :
    f.Q_m (f.map x) = f.Q_n x :=
  f.is_isometry x

/- One-step tower maps, each with an explicit quadratic preservation law. -/
variable (tower_maps : ∀ n, IsometricEmbedding (V n) (V (n + 1)))

/-- The `n`th transition preserves its declared quadratic form. -/
theorem tower_map_preserves_quadratic (n : ℕ) (x : V n) :
    (tower_maps n).Q_m ((tower_maps n).map x) = (tower_maps n).Q_n x :=
  (tower_maps n).preserves_quadratic x

end InfoGeometry.Canonical.GeometricTower
