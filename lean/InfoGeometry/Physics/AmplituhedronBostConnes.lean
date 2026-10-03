import Mathlib.Data.Finsupp.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

-- The cyclic exterior-algebra expression associated with three indices.
-- Its vanishing requires an Arnold relation; it is not asserted for arbitrary indices.
noncomputable def bcfw_recursion_arnold_cohen (i j k : ι) : ExtAlg R ι :=
  (gen i j * gen j k) + (gen j k * gen k i) + (gen k i * gen i j)

/-
ExteriorAlgebra.ι_sq_zero is the canonical square-zero law for `gen`. This
exterior-algebra fact is not a Klein Plücker equation, a pair of chiral Cuntz
generators, or a physical mass-shell condition; no second alias API is declared.
-/

/- A direct zeta-value readout. This definition alone is not a Bost--Connes
partition function or a KMS-state construction. -/
noncomputable def riemannZetaReadout (β : ℂ) : ℂ :=
  riemannZeta β

end InfoGeometry.Physics.AmplituhedronBostConnes
