import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Complex

namespace InfoGeometry.Topology

open Complex

/-- 
The punctured unit disk $D^* = \{z \in \mathbb{C} \mid 0 < |z| < 1\}$. 
Used as the standard local model for a puncture on a Riemann surface.
-/
abbrev PuncturedDisk : Type :=
  { z : ℂ // z ≠ 0 ∧ norm z < 1 }

/--
The Poincaré metric form on the punctured disk $D^*$.
The metric is given by $ds^2 = \lambda(z) |dz|^2$, where the conformal factor is:
$$ \lambda(z) = \frac{1}{|z|^2 (\log|z|^2)^2} $$
-/
noncomputable def poincareMetricFactor (z : PuncturedDisk) : ℝ :=
  let r2 := (norm z.val)^2
  1 / (r2 * (Real.log r2)^2)

/--
Structural definition of a punctured Riemann surface.
We abstract it as a topological space `X` which locally behaves as $\mathbb{C}$ everywhere,
except at a distinguished puncture where it is locally isomorphic to the `PuncturedDisk`.
-/
class PuncturedRiemannSurface (X : Type*) [TopologicalSpace X] where
  /-- Local coordinate chart near the puncture mapping into the punctured unit disk $D^*$ -/
  punctureChart : X → PuncturedDisk
  
  /-- The chart is continuous. -/
  continuous_chart : Continuous punctureChart

  /-- The chart has an open range. -/
  isOpen_range : IsOpen (Set.range punctureChart)
  
  /-- The conformal factor of the metric on X -/
  conformalFactor : X → ℝ

  /-- Verification that the geometry locally pulls back the Poincaré metric. -/
  isPoincareMetricNearPuncture : ∀ x, conformalFactor x = poincareMetricFactor (punctureChart x)

lemma PuncturedDisk_range_id : Set.range (id : PuncturedDisk → PuncturedDisk) = Set.univ := by
  exact Set.range_id

lemma PuncturedDisk_isOpen_range : IsOpen (Set.range (id : PuncturedDisk → PuncturedDisk)) := by
  rw [PuncturedDisk_range_id]
  exact isOpen_univ

lemma PuncturedDisk_poincare_pullback (x : PuncturedDisk) : 
    poincareMetricFactor x = poincareMetricFactor (id x) := rfl

/-- The canonical instantiation of a punctured Riemann surface on the punctured disk itself. -/
noncomputable instance : PuncturedRiemannSurface PuncturedDisk where
  punctureChart := id
  continuous_chart := continuous_id
  isOpen_range := PuncturedDisk_isOpen_range
  conformalFactor := poincareMetricFactor
  isPoincareMetricNearPuncture := PuncturedDisk_poincare_pullback

end InfoGeometry.Topology
