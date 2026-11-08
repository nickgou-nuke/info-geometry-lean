import Mathlib.Topology.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.GroupTheory.GroupAction.Quotient
import InfoGeometry.Canonical.ColeFurySpinorProjectiveTopology

noncomputable section

namespace InfoGeometry.Canonical.ColeFurySpinorProjectiveChart

open InfoGeometry.Algebra.ColeFurySpinorBridge
open InfoGeometry.Canonical.ColeFurySpinorProjectiveTopology

/-- The coordinate chart where the `i`-th spinor coordinate is nonzero. -/
def CoordinateChart (i : Fin 32) :=
  {ψ : NonzeroSpinor // ψ.1 i ≠ 0}

instance (i : Fin 32) : TopologicalSpace (CoordinateChart i) := by
  change TopologicalSpace {ψ : NonzeroSpinor // ψ.1 i ≠ 0}
  infer_instance

instance (i : Fin 32) : MulAction ℝˣ (CoordinateChart i) where
  smul u ψ :=
    ⟨u • ψ.1, by
      change (u : ℝ) * ψ.1.1 i ≠ 0
      exact mul_ne_zero (Units.ne_zero u) ψ.2⟩
  one_smul ψ := by
    apply Subtype.ext
    exact one_smul ℝˣ ψ.1
  mul_smul u v ψ := by
    apply Subtype.ext
    exact mul_smul u v ψ.1

/-- Projective quotient of a nonzero-coordinate chart. -/
def chartSetoid (i : Fin 32) : Setoid (CoordinateChart i) :=
  MulAction.orbitRel ℝˣ (CoordinateChart i)

def ProjectiveChart (i : Fin 32) := Quotient (chartSetoid i)

instance (i : Fin 32) : TopologicalSpace (ProjectiveChart i) :=
  instTopologicalSpaceQuotient

def chartMap (i : Fin 32) : CoordinateChart i → ProjectiveChart i :=
  Quotient.mk (chartSetoid i)

theorem continuous_chartMap (i : Fin 32) :
    Continuous (chartMap i) :=
  continuous_quotient_mk'

/-- The affine coordinate `ψ j / ψ i` on the `i`-chart. -/
def coordinateRatio (i j : Fin 32) (ψ : CoordinateChart i) : ℝ :=
  ψ.1.1 j / ψ.1.1 i

theorem continuous_coordinateRatio (i j : Fin 32) :
    Continuous (coordinateRatio i j) := by
  have hval : Continuous (fun ψ : CoordinateChart i => ψ.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  apply Continuous.div
  · exact (continuous_apply j).comp hval
  · exact (continuous_apply i).comp hval
  · intro ψ
    exact ψ.2

theorem coordinateRatio_smul (i j : Fin 32) (u : ℝˣ)
    (ψ : CoordinateChart i) :
    coordinateRatio i j (u • ψ) = coordinateRatio i j ψ := by
  change ((u : ℝ) * ψ.1.1 j) / ((u : ℝ) * ψ.1.1 i) =
    ψ.1.1 j / ψ.1.1 i
  field_simp [Units.ne_zero u, ψ.2]

def coordinateRatioOnProjectiveChart (i j : Fin 32) :
    ProjectiveChart i → ℝ :=
  Quotient.lift (coordinateRatio i j) (by
    intro a b h
    rcases h with ⟨u, hu⟩
    rw [← hu, coordinateRatio_smul])

@[simp]
theorem coordinateRatioOnProjectiveChart_map (i j : Fin 32)
    (ψ : CoordinateChart i) :
    coordinateRatioOnProjectiveChart i j (chartMap i ψ) =
      coordinateRatio i j ψ :=
  rfl

theorem continuous_coordinateRatioOnProjectiveChart (i j : Fin 32) :
    Continuous (coordinateRatioOnProjectiveChart i j) := by
  exact Continuous.quotient_lift (continuous_coordinateRatio i j) _

end InfoGeometry.Canonical.ColeFurySpinorProjectiveChart
