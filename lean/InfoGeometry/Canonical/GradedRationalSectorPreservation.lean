import InfoGeometry.Canonical.GradedRationalDifferential
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

variable {V : ℕ → Type*}
  [∀ p, AddCommGroup (V p)]
  [∀ p, Module ℚ (V p)]

/-- A degree-indexed family of rational submodules. -/
abbrev GradedSector (V : ℕ → Type*)
    [∀ p, AddCommGroup (V p)] [∀ p, Module ℚ (V p)] :=
  ∀ p, Submodule ℚ (V p)

/-- The graded differential maps each sector into the next degree. -/
def DifferentialPreservesSector
    (D : GradedRationalDifferential V)
    (S : GradedSector V) : Prop :=
  ∀ p (x : V p), x ∈ S p → D.d p x ∈ S (p + 1)

/-- The graded codifferential maps each sector into the previous degree. -/
def CodifferentialPreservesSector
    (C : GradedRationalCodifferential V)
    (S : GradedSector V) : Prop :=
  ∀ p (x : V (p + 1)), x ∈ S (p + 1) → C.cod p x ∈ S p

theorem differential_preserves_sector_add
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    {p : ℕ} {x y : V p}
    (hx : x ∈ S p) (hy : y ∈ S p) :
    D.d p (x + y) ∈ S (p + 1) := by
  rw [map_add]
  exact (S (p + 1)).add_mem (hS p x hx) (hS p y hy)

theorem codifferential_preserves_sector_add
    (C : GradedRationalCodifferential V)
    (S : GradedSector V)
    (hS : CodifferentialPreservesSector C S)
    {p : ℕ} {x y : V (p + 1)}
    (hx : x ∈ S (p + 1)) (hy : y ∈ S (p + 1)) :
    C.cod p (x + y) ∈ S p := by
  rw [map_add]
  exact (S p).add_mem (hS p x hx) (hS p y hy)

theorem differential_preserves_sector_smul
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (p : ℕ) (a : ℚ) (x : V p) (hx : x ∈ S p) :
    D.d p (a • x) ∈ S (p + 1) := by
  rw [map_smul]
  exact (S (p + 1)).smul_mem a (hS p x hx)

theorem codifferential_preserves_sector_smul
    (C : GradedRationalCodifferential V)
    (S : GradedSector V)
    (hS : CodifferentialPreservesSector C S)
    (p : ℕ) (a : ℚ) (x : V (p + 1)) (hx : x ∈ S (p + 1)) :
    C.cod p (a • x) ∈ S p := by
  rw [map_smul]
  exact (S p).smul_mem a (hS p x hx)

end InfoGeometry.Canonical
