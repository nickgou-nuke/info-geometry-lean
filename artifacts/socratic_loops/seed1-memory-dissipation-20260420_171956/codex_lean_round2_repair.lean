```lean
import Mathlib.Data.Real.Basic

universe u

/-- An evolution is informationally contractive when it never increases
pairwise distinguishability measured by `D`. -/
def IsInformationalContraction {E : Type u}
    (T : E → E) (D : E → E → ℝ) : Prop :=
  ∀ x y : E, D (T x) (T y) ≤ D x y

/-- The memory sector is the equality case of informational contraction. -/
def MemorySector {E : Type u}
    (T : E → E) (D : E → E → ℝ) : Set (E × E) :=
  {p | D (T p.1) (T p.2) = D p.1 p.2}

/-- The dissipative sector is the strict inequality case of informational contraction. -/
def DissipativeSector {E : Type u}
    (T : E → E) (D : E → E → ℝ) : Set (E × E) :=
  {p | D (T p.1) (T p.2) < D p.1 p.2}

/-- The local MDB surface: under contraction, every pair lies either in the
memory equality sector or in the dissipative strict-loss sector. -/
theorem memory_or_dissipative_of_contraction {E : Type u}
    (T : E → E) (D : E → E → ℝ)
    (hT : IsInformationalContraction T D) :
    ∀ p : E × E, p ∈ MemorySector T D ∨ p ∈ DissipativeSector T D := by
  intro p
  have hle : D (T p.1) (T p.2) ≤ D p.1 p.2 := hT p.1 p.2
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inr hlt
  · exact Or.inl heq

/-- A pair cannot be simultaneously memory and dissipative. -/
theorem memorySector_disjoint_dissipativeSector {E : Type u}
    (T : E → E) (D : E → E → ℝ) :
    Disjoint (MemorySector T D) (DissipativeSector T D) := by
  rw [Set.disjoint_left]
  intro p hp_mem hp_diss
  exact (not_lt_of_eq hp_mem) hp_diss
```
