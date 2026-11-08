import InfoGeometry.Topology.DiscreteDiracHodgeChiral
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native finite Hodge decomposition

The exact, coexact, and harmonic sectors are Mathlib submodules.  A Hodge
decomposition is an existential proposition about membership in those sectors,
not a record carrying duplicated proof fields.  Nilpotence gives closedness of
the exact and coexact sectors; it does not by itself give orthogonality or a
direct-sum theorem.
-/

namespace InfoGeometry.Topology.HodgeDecomposition

open InfoGeometry.Topology.DiscreteDiracHodgeChiral

noncomputable section

variable {n : ℕ}

/-- Exact finite cochains, as the range of the differential. -/
abbrev exactSubmodule (d : EndCochain n) : Submodule ℝ (Cochains n) :=
  LinearMap.range (Matrix.toLin' d)

/-- Coexact finite cochains, as the range of the codifferential. -/
abbrev coexactSubmodule (δ : EndCochain n) : Submodule ℝ (Cochains n) :=
  LinearMap.range (Matrix.toLin' δ)

/-- Harmonic finite cochains, as the kernel of the Hodge Laplacian. -/
abbrev harmonicSubmodule (d δ : EndCochain n) : Submodule ℝ (Cochains n) :=
  LinearMap.ker (Matrix.toLin' (hodgeLaplacian d δ))

/-- Native existential form of finite Hodge decomposition. -/
def IsHodgeDecomposition (d δ : EndCochain n) (x : Cochains n) : Prop :=
  ∃ e c h : Cochains n,
    x = e + c + h ∧
    e ∈ exactSubmodule d ∧
    c ∈ coexactSubmodule δ ∧
    h ∈ harmonicSubmodule d δ

theorem exact_closed_of_nilpotent
    (d : EndCochain n) (hd : d * d = 0)
    {x : Cochains n} (hx : x ∈ exactSubmodule d) :
    d.mulVec x = 0 := by
  rcases hx with ⟨y, hy⟩
  rw [← hy]
  have h := congrArg (fun M => M.mulVec y) hd
  simpa [Matrix.mulVec_mulVec] using h

theorem coexact_coclosed_of_nilpotent
    (δ : EndCochain n) (hδ : δ * δ = 0)
    {x : Cochains n} (hx : x ∈ coexactSubmodule δ) :
    δ.mulVec x = 0 := by
  rcases hx with ⟨y, hy⟩
  rw [← hy]
  have h := congrArg (fun M => M.mulVec y) hδ
  simpa [Matrix.mulVec_mulVec] using h

end

end InfoGeometry.Topology.HodgeDecomposition
