import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib

/-!
# Punctured Riemann Surfaces

This file formally defines the topological and geometric structure of a punctured Riemann surface.
In particular, it models the local geometry near a puncture as the punctured unit disk $D^*$ in $\mathbb{C}$.

We explicitly define the Poincaré metric form near the puncture:
$$ ds^2 = \frac{|dz|^2}{|z|^2 (\log|z|^2)^2} $$

## Main Definitions
* `PuncturedDisk`: The punctured unit disk $\{ z \in \mathbb{C} \mid 0 < |z| < 1 \}$.
* `poincareMetricFactor`: The conformal scaling factor of the Poincaré metric.
* `PuncturedRiemannSurface`: A structural class defining the topology of the punctured surface.
-/

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

  /-- The puncture chart is an open embedding, so its image is an open local
  model and the chart is a homeomorphism onto that image. -/
  punctureChart_openEmbedding : Topology.IsOpenEmbedding punctureChart

  /-- Conformal factor of the metric on the surface near the puncture. -/
  metricFactor : X → ℝ

  /-- The metric factor is the pullback of the standard punctured-disk
  Poincaré factor along the puncture chart. -/
  metricFactor_eq_poincare :
    ∀ x : X, metricFactor x = poincareMetricFactor (punctureChart x)

namespace PuncturedRiemannSurface

variable {X : Type*} [TopologicalSpace X] (S : PuncturedRiemannSurface X)

/-- The image of the puncture chart is open in the standard punctured disk. -/
theorem isOpen_range_punctureChart :
    IsOpen (Set.range S.punctureChart) :=
  S.punctureChart_openEmbedding.isOpen_range

/-- Owner theorem for the local Poincaré metric law. -/
theorem isPoincareMetricNearPuncture (x : X) :
    S.metricFactor x = poincareMetricFactor (S.punctureChart x) :=
  S.metricFactor_eq_poincare x

end PuncturedRiemannSurface

end InfoGeometry.Topology
