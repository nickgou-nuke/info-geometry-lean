import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# Phase II: Cartan Exterior Symmetry
-/

namespace InfoGeometry.Nuclear.Exterior

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The tetrad 1-forms $e^a$. -/
noncomputable def tetrad (a : ι) : ExteriorAlgebra ℝ (ι →₀ ℝ) :=
  ExteriorAlgebra.ι ℝ (Finsupp.single a (1 : ℝ))

/-- The Spin Connection $\omega^a_b$ -/
abbrev SpinConnection (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  ι → ι → ExteriorAlgebra ℝ (ι →₀ ℝ)

/-- Cartan's First Structural Equation: $T^a = de^a + \omega^a_b \wedge e^b$ -/
noncomputable def torsion2Form 
    (d : ExteriorAlgebra ℝ (ι →₀ ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (ι →₀ ℝ)) 
    (ω : SpinConnection ι) (a : ι) : ExteriorAlgebra ℝ (ι →₀ ℝ) :=
  d (tetrad a) + Finset.sum Finset.univ (fun b => ω a b * tetrad b)

end InfoGeometry.Nuclear.Exterior
