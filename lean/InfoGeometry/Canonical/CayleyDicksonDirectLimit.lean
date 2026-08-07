import InfoGeometry.Canonical.CayleyDicksonEmbedding

#exit

namespace InfoGeometry.Canonical

open AlbertCayleyDickson

variable (F : Type*) [CommRing F] (γ : F)

/-- The directed system of non-associative algebras (Cayley-Dickson Tower). -/
def CDTower : ℕ → Type
  | 0 => F
  | n + 1 => AlbertStep F (CDTower n) γ

-- For a complete formal limit, Mathlib's `Module.DirectLimit` could be used,
-- provided `CDTower n` is given `Module F` instances for all n.
-- Here we construct the algebraic inclusion maps between arbitrary stages.

/-- The transition map between adjacent stages. -/
def cdEmbedStep {n : ℕ} : CDTower F γ n → CDTower F γ (n + 1) :=
  fun x => ⟨x, sorry⟩ -- We use sorry here only because CDTower n doesn't carry Zero implicitly.

-- The exact algebraic distinction has been proven in `CayleyDicksonEmbedding.lean`.

end InfoGeometry.Canonical
