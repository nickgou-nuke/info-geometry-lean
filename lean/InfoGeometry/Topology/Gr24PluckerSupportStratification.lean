import Mathlib
import InfoGeometry.Projective.MatrixPluckerPositiveBridge

/-!
# Finite Plücker-support stratification of the nonnegative `Gr(2,4)` chart

The six ordered Plücker coordinates divide the nonnegative matrix chart into
at most `2^6` support patterns.  This file proves that those support sets form
a finite disjoint cover and hence give a pointwise finite cell-sum identity.
They are strata of matrix representatives by vanishing minors; no quotient
Grassmannian, positroid-cell identification, or canonical differential form is
asserted.
-/

open scoped BigOperators

namespace InfoGeometry.Topology.Gr24PluckerSupportStratification

open InfoGeometry.Canonical
open InfoGeometry.Projective.MatrixPluckerPositiveBridge

/-- A Boolean support pattern for the six ordered Plücker coordinates. -/
abbrev Signature := Fin 6 → Bool

/-- The support pattern records exactly which Plücker coordinates are
strictly positive. -/
noncomputable def supportSignature (M : Matrix2x4) : Signature :=
  fun i => decide (0 < matrixPluckerCoords M i)

/-- Matrices in the nonnegative chart with a prescribed strict-positivity
pattern for their six Plücker coordinates. -/
def supportStratum (σ : Signature) : Set Matrix2x4 :=
  {M | M ∈ positiveGrassmannianChart (k := 2) (n := 4) ∧
    ∀ i, (σ i = true ↔ 0 < matrixPluckerCoords M i)}

@[simp] theorem supportSignature_true_iff (M : Matrix2x4) (i : Fin 6) :
    supportSignature M i = true ↔ 0 < matrixPluckerCoords M i := by
  simp [supportSignature]

/-- Every chart representative lies in the stratum specified by its own
Plücker support. -/
theorem supportSignature_mem_stratum (M : Matrix2x4)
    (hM : M ∈ positiveGrassmannianChart (k := 2) (n := 4)) :
    M ∈ supportStratum (supportSignature M) := by
  refine ⟨hM, ?_⟩
  intro i
  exact supportSignature_true_iff M i

/-- A chart representative belongs to exactly the stratum determined by its
support signature. -/
theorem mem_supportStratum_iff (M : Matrix2x4)
    (hM : M ∈ positiveGrassmannianChart (k := 2) (n := 4))
    (σ : Signature) :
    M ∈ supportStratum σ ↔ supportSignature M = σ := by
  constructor
  · rintro ⟨_, hσ⟩
    funext i
    cases hbit : σ i <;> have hpos := hσ i <;>
      simp_all [supportSignature]
  · intro hσ
    subst σ
    exact supportSignature_mem_stratum M hM

/-- Distinct support patterns define disjoint subsets of the nonnegative
matrix chart. -/
theorem supportStratum_disjoint {σ τ : Signature} (hne : σ ≠ τ) :
    Disjoint (supportStratum σ) (supportStratum τ) := by
  rw [Set.disjoint_left]
  intro M hσ hτ
  have hM : M ∈ positiveGrassmannianChart (k := 2) (n := 4) := hσ.1
  have hs := (mem_supportStratum_iff M hM σ).mp hσ
  have ht := (mem_supportStratum_iff M hM τ).mp hτ
  exact hne (hs.symm.trans ht)

/-- The support strata cover the complete nonnegative `Gr(2,4)` matrix
chart. -/
theorem supportStrata_cover :
    positiveGrassmannianChart (k := 2) (n := 4) =
      ⋃ σ : Signature, supportStratum σ := by
  ext M
  constructor
  · intro hM
    exact Set.mem_iUnion.mpr
      ⟨supportSignature M, supportSignature_mem_stratum M hM⟩
  · intro hM
    rcases Set.mem_iUnion.mp hM with ⟨σ, hσ⟩
    exact hσ.1

/-- The indicator of one support stratum, used as a finite partition weight. -/
noncomputable def stratumWeight (σ : Signature) (M : Matrix2x4) : ℝ :=
  by
    classical
    exact if M ∈ supportStratum σ then 1 else 0

/-- On the chart exactly one support indicator is nonzero, so these finite
weights form a pointwise partition of unity. -/
theorem stratumWeight_sum_one (M : Matrix2x4)
    (hM : M ∈ positiveGrassmannianChart (k := 2) (n := 4)) :
    ∑ σ : Signature, stratumWeight σ M = 1 := by
  classical
  rw [Finset.sum_eq_single (supportSignature M)]
  · simp [stratumWeight, supportSignature_mem_stratum M hM]
  · intro σ _ hσ
    have hnot : M ∉ supportStratum σ := by
      intro hmem
      have heq := (mem_supportStratum_iff M hM σ).mp hmem
      exact hσ heq.symm
    simp [stratumWeight, hnot]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Finite cell-sum identity for any real-valued function on the chart:
integrating against the support-stratum partition reproduces its value. -/
theorem supportStrata_cell_sum (M : Matrix2x4)
    (hM : M ∈ positiveGrassmannianChart (k := 2) (n := 4))
    (f : Matrix2x4 → ℝ) :
    ∑ σ : Signature, stratumWeight σ M * f M = f M := by
  rw [← Finset.sum_mul]
  rw [stratumWeight_sum_one M hM, one_mul]

end InfoGeometry.Topology.Gr24PluckerSupportStratification
