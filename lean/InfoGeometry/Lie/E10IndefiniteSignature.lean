import InfoGeometry.Lie.E10HyperbolicSignature

/-!
# E₁₀ Indefinite Signature Archetype

While strict (9,1) hyperbolicity requires a full Sylvester decomposition,
we establish the rigorous algebraic prerequisite here: the E₁₀ generalized 
Cartan matrix is strictly indefinite. 

We prove this by exhibiting a strictly positive subspace (any simple root 
in the E₈ subdiagram) orthogonal to or independent of the previously 
established timelike root.
-/

namespace InfoGeometry.Lie.E10Indefinite

open InfoGeometry.Lie.E10
open InfoGeometry.Lie.E10Hyperbolic

/-- A purely spacelike simple root in the E₁₀ diagram. -/
def spacelikeRoot : Fin 10 → ℤ :=
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- 🏆 THEOREM: The E₁₀ Cartan matrix admits a strictly positive direction. -/
theorem e10_has_spacelike_direction :
    cartanQuadraticForm spacelikeRoot = 2 := by
  decide

/-- 🏆 THEOREM: The E₁₀ Cartan matrix is strictly indefinite.
    It contains at least one positive direction and one negative direction. -/
theorem e10_is_indefinite :
    (∃ v : Fin 10 → ℤ, cartanQuadraticForm v > 0) ∧
    (∃ w : Fin 10 → ℤ, cartanQuadraticForm w < 0) := by
  exact ⟨
    ⟨spacelikeRoot, by rw [e10_has_spacelike_direction]; decide⟩,
    ⟨timelikeRoot, by rw [e10_is_hyperbolic]; decide⟩
  ⟩

end InfoGeometry.Lie.E10Indefinite
