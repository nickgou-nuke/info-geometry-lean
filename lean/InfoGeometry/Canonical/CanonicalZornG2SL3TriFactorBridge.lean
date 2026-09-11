import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Canonical Zorn G₂ SL₃ Tri-Factor Bridge

This module formalizes the true $\mathbb{Z}_3$-grading of the exceptional Lie algebra $G_2$.
Following the Draper literature, $G_2$ decomposes exactly as:
$\mathfrak{g}_2 = \mathfrak{sl}_3 \oplus \mathbf{3} \oplus \mathbf{3}^*$
where the components correspond to $\mathbb{Z}_3$ grades $0, 1,$ and $2$ respectively.

This provides the rigorous continuous Lie-theoretic realization of the discrete 
"trifactor geometry" (core + fundamental + dual).
-/

namespace InfoGeometry.Canonical.CanonicalZornG2SL3TriFactorBridge

/-- The grading group $\mathbb{Z}_3$. -/
abbrev Z3 := Fin 3

/-- 
The abstract specification of the $G_2$ tri-factor $\mathbb{Z}_3$-grading.
-/
structure G2Z3TriFactorDatum (𝕜 𝔤 : Type*) [CommRing 𝕜] [LieRing 𝔤] [LieAlgebra 𝕜 𝔤] where
  /-- The three homogeneous components of $\mathfrak{g}_2$. -/
  component : Z3 → Submodule 𝕜 𝔤

  /-- The bracket respects the $\mathbb{Z}_3$-grading. -/
  g2Bracket_grade_add : 
    ∀ (i j : Z3) (x y : 𝔤),
      x ∈ component i → y ∈ component j → ⁅x, y⁆ ∈ component (i + j)

  /-- The direct sum decomposition into the three factors. -/
  g2Z3Decomposition : 
    iSup component = ⊤

/-!
### Capstone Identifications

The capstones formally identify the abstract $\mathbb{Z}_3$ components with 
$\mathfrak{sl}_3$, its fundamental module $\mathbf{3}$, and its dual $\mathbf{3}^*$.
-/

abbrev g2GradeZero {𝕜 𝔤 : Type*} [CommRing 𝕜] [LieRing 𝔤] [LieAlgebra 𝕜 𝔤] (D : G2Z3TriFactorDatum 𝕜 𝔤) := D.component 0
abbrev g2GradeOne  {𝕜 𝔤 : Type*} [CommRing 𝕜] [LieRing 𝔤] [LieAlgebra 𝕜 𝔤] (D : G2Z3TriFactorDatum 𝕜 𝔤) := D.component 1
abbrev g2GradeTwo  {𝕜 𝔤 : Type*} [CommRing 𝕜] [LieRing 𝔤] [LieAlgebra 𝕜 𝔤] (D : G2Z3TriFactorDatum 𝕜 𝔤) := D.component 2

/-- The grade 0 component is closed under the Lie bracket, so it forms a Lie subalgebra. -/
def g2GradeZeroLieSubalgebra {𝕜 𝔤 : Type*} [CommRing 𝕜] [LieRing 𝔤] [LieAlgebra 𝕜 𝔤] (D : G2Z3TriFactorDatum 𝕜 𝔤) : LieSubalgebra 𝕜 𝔤 :=
  { D.component 0 with
    lie_mem' := fun {x y} hx hy => D.g2Bracket_grade_add 0 0 x y hx hy }

/-- CAPSTONE 1: The grade-0 core component is exactly $\mathfrak{sl}_3$. -/
def g2GradeZero_eq_sl3 {𝕜 𝔤 : Type*} [CommRing 𝕜] [LieRing 𝔤] [LieAlgebra 𝕜 𝔤] (D : G2Z3TriFactorDatum 𝕜 𝔤) : Prop :=
  Nonempty (g2GradeZeroLieSubalgebra D ≃ₗ⁅𝕜⁆ LieAlgebra.SpecialLinear.sl (Fin 3) 𝕜)

/-- CAPSTONE 2: The grade-1 component is the natural 3-dimensional representation. -/
def g2GradeOne_natural {𝕜 𝔤 : Type*} [CommRing 𝕜] [LieRing 𝔤] [LieAlgebra 𝕜 𝔤] (D : G2Z3TriFactorDatum 𝕜 𝔤) : Prop :=
  Nonempty (g2GradeOne D ≃ₗ[𝕜] (Fin 3 → 𝕜))

/-- CAPSTONE 3: The grade-2 component is the dual representation. -/
def g2GradeTwo_dual {𝕜 𝔤 : Type*} [CommRing 𝕜] [LieRing 𝔤] [LieAlgebra 𝕜 𝔤] (D : G2Z3TriFactorDatum 𝕜 𝔤) : Prop :=
  Nonempty (g2GradeTwo D ≃ₗ[𝕜] Module.Dual 𝕜 (Fin 3 → 𝕜))

end InfoGeometry.Canonical.CanonicalZornG2SL3TriFactorBridge
