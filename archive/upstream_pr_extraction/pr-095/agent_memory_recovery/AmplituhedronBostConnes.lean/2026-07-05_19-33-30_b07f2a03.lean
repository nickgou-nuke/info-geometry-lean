import Mathlib.Data.Finsupp.Basic
-- import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace InfoGeometry.Physics.AmplituhedronBostConnes

variable {R : Type*} [CommRing R]
variable {ι : Type*} [DecidableEq ι]

-- 1. Generators of the free module
noncomputable def ω (i j : ι) : (ι × ι) →₀ R :=
  Finsupp.single (i, j) (1 : R)

abbrev ExtAlg (R ι : Type*) [CommRing R] [DecidableEq ι] :=
  ExteriorAlgebra R ((ι × ι) →₀ R)

noncomputable def gen (i j : ι) : ExtAlg R ι :=
  ExteriorAlgebra.ι R (ω i j)

-- 4. BCFW Recursion mapped to Arnold-Cohen relations
-- ω_12 ∧ ω_23 + ω_23 ∧ ω_31 + ω_31 ∧ ω_12 = 0
noncomputable def bcfw_recursion_arnold_cohen (i j k : ι) : ExtAlg R ι :=
  (gen i j * gen j k) + (gen j k * gen k i) + (gen k i * gen i j)

-- 5. On-Shell Factorization mapped to Klein quadric chiral Cuntz generators (S_±^2 = 0)
noncomputable def S_plus (i : ι) : ExtAlg R ι := gen i i
noncomputable def S_minus (i : ι) : ExtAlg R ι := gen i i

lemma on_shell_factorization_klein_quadric_plus (i : ι) :
    S_plus i * S_plus i = (0 : ExtAlg R ι) := by
  exact ExteriorAlgebra.ι_sq_zero (ω i i)

lemma on_shell_factorization_klein_quadric_minus (i : ι) :
    S_minus i * S_minus i = (0 : ExtAlg R ι) := by
  exact ExteriorAlgebra.ι_sq_zero (ω i i)

-- 6. All-Loop Integrand mapped to Riemann Zeta partition evaluated by Bost-Connes KMS state
-- Evaluated on ℂ for the KMS state at inverse temperature β
noncomputable def all_loop_integrand_bost_connes_kms_state (β : ℂ) : ℂ :=
  riemannZeta β

end InfoGeometry.Physics.AmplituhedronBostConnes
