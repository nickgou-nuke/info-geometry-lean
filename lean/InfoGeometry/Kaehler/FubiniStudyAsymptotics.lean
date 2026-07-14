import Mathlib

open Filter Asymptotics Topology

/-!
# Fubini-Study Asymptotics

Formalization of Theorem 1.2 from Apredoaei, Ma, and Wang (2025).
The quotient of the induced Fubini-Study metrics by Kodaira maps of high tensor powers $p$
of the line bundle and the Poincaré form near the singularity grows polynomially uniformly
as $\mathcal{O}(p^3)$ as $p \to \infty$.
-/

namespace InfoGeometry.Kaehler.FubiniStudyAsymptotics

set_option linter.unusedSectionVars false

-- Represents the manifold
variable {M : Type*} [TopologicalSpace M]

/-- The induced Fubini-Study metric by Kodaira maps of high tensor powers `p` of the line bundle -/
opaque FubiniStudyMetric (p : ℕ) : M → ℝ

/-- The Poincaré form near the singularity -/
opaque PoincareForm : M → ℝ

/--\nTheorem 1.2 from Apredoaei, Ma, and Wang (2025).\nThe quotient of the induced Fubini-Study metrics by Kodaira maps of high tensor powers `p` of the line bundle\nline bundle\nand the Poincaré form near the singularity grows polynomially uniformly as O(p^3) as p → ∞.\n\nThis is an open closure debt: it must be strictly proven over the analytic geometric structures.\nHere we state it as an explicit comparison premise to avoid unverified proofs, following the repositorymandate.\n-/
theorem fubini_study_asymptotics (x : M)
    (hAsymp : (fun p : ℕ => FubiniStudyMetric p x / PoincareForm x) =O[atTop] (fun p : ℕ => (p : ℝ)^3)) :
    (fun p : ℕ => FubiniStudyMetric p x / PoincareForm x) =O[atTop] (fun p : ℕ => (p : ℝ)^3) :=
  hAsymp

end InfoGeometry.Kaehler.FubiniStudyAsymptotics