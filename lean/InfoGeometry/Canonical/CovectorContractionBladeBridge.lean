import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.GrassmannianCartanTower
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.CovectorContractionBladeBridge

open ExteriorAlgebra
open InfoGeometry.GrassmannianTower

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: 4-Blade Generator K4 = ι(v1) ∧ ι(v2) ∧ ι(v3) ∧ ι(v4). -/
def blade4 (v1 v2 v3 v4 : V) : ExteriorAlgebra R V :=
  ιMulti R 4 ![v1, v2, v3, v4]

/-- **Definition**: 5-Blade Generator K5 = ι(v1) ∧ ι(v2) ∧ ι(v3) ∧ ι(v4) ∧ ι(v5). -/
def blade5 (v1 v2 v3 v4 v5 : V) : ExteriorAlgebra R V :=
  ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5

/-- **Definition**: Explicit 5-Blade Covector Contraction by Linear Form λ : V →ₗ[R] R. -/
def contractFiveBlade (lambda : V →ₗ[R] R) (u w1 w2 w3 w4 : V) : ExteriorAlgebra R V :=
  algebraMap R (ExteriorAlgebra R V) (lambda u) * blade4 w1 w2 w3 w4 -
  algebraMap R (ExteriorAlgebra R V) (lambda w1) * blade4 u w2 w3 w4 +
  algebraMap R (ExteriorAlgebra R V) (lambda w2) * blade4 u w1 w3 w4 -
  algebraMap R (ExteriorAlgebra R V) (lambda w3) * blade4 u w1 w2 w4 +
  algebraMap R (ExteriorAlgebra R V) (lambda w4) * blade4 u w1 w2 w3

/-- **Theorem**: Adapted Frame Contraction Formula (λ u = 1, λ w_i = 0 ⟹ contract(K5) = K4). -/
theorem contraction_of_adapted_five_frame
    (lambda : V →ₗ[R] R) (u w1 w2 w3 w4 : V)
    (hu : lambda u = 1) (hw1 : lambda w1 = 0) (hw2 : lambda w2 = 0)
    (hw3 : lambda w3 = 0) (hw4 : lambda w4 = 0) :
    contractFiveBlade lambda u w1 w2 w3 w4 = blade4 w1 w2 w3 w4 := by
  dsimp [contractFiveBlade]
  rw [hu, hw1, hw2, hw3, hw4]
  simp [map_one, map_zero]

/-- Under the adapted-frame hypotheses, the covector contraction equals the
    displayed decomposable 4-vector, whose exterior square vanishes by
    alternation.  This is not itself the Klein/Plücker quadratic equation. -/
theorem contracted_five_blade_nilpotent
    (lambda : V →ₗ[R] R) (u w1 w2 w3 w4 : V)
    (hu : lambda u = 1) (hw1 : lambda w1 = 0) (hw2 : lambda w2 = 0)
    (hw3 : lambda w3 = 0) (hw4 : lambda w4 = 0) :
    let K4 := contractFiveBlade lambda u w1 w2 w3 w4
    K4 * K4 = 0 := by
  intro K4
  have hK4 : K4 = blade4 w1 w2 w3 w4 := contraction_of_adapted_five_frame lambda u w1 w2 w3 w4 hu hw1 hw2 hw3 hw4
  rw [hK4]
  exact decomposable_exterior_blade_square_zero (R := R) 3 ![w1, w2, w3, w4]

/-!
The contraction formula and the square-zero consequence are exposed as
separate reusable theorems above.  A former conjunction merely repackaged
those results and suggested a stronger Grassmannian-boundary interpretation;
the source facts remain available without that wrapper.
-/

end InfoGeometry.Canonical.CovectorContractionBladeBridge
