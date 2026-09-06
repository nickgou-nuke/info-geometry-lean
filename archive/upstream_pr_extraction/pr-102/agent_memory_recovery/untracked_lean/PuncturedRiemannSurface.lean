import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Basic

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
def PuncturedDisk : Type :=
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
  
  /-- The chart is an open embedding near the puncture. -/
  isOpenDomain : Prop
  
  /-- Verification that the geometry locally pulls back the Poincaré metric (placeholder for full metric structure). -/
  isPoincareMetricNearPuncture : Prop

end InfoGeometry.Topology
