import InfoGeometry.Projective.SplitQuaternionMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Projective.LightTorus

This file formalizes the `LightTorus`, the geometric manifold corresponding to the
null cone in the (2,2) signature split-quaternion space.

In Minkowski space (1,3 signature), the locus of light forms a light cone.
However, in split-quaternion spacetime (2,2 signature), the null elements satisfy:
$w^2 + x^2 - y^2 - z^2 = 0$.

In polar division-binarion coordinates, this translates to $|w| = |z| = t$,
parameterizing the null manifold as $\mathbb{R}_{>0} \times S^1 \times S^1$,
which forms a light torus.
-/

namespace InfoGeometry.Projective

/--
The null condition for a split-quaternion.
$N(q) = w^2 + x^2 - y^2 - z^2 = 0$
-/
def IsNullSplitQuaternion (q : SplitQuaternion) : Prop :=
  splitNormSq q.w q.x q.y q.z = 0

/--
The Light Torus geometry in the (2,2) signature space.
This represents the set of all null split-quaternions (excluding the origin).
-/
def LightTorus : Type := { q : SplitQuaternion // q ≠ ⟨0, 0, 0, 0⟩ ∧ IsNullSplitQuaternion q }

/--
A point on the Light Torus parameterized by its topological coordinates:
$(t, \theta, \phi) \in \mathbb{R}_{>0} \times S^1 \times S^1$.

$t$ represents the positive scaling factor.
$\theta$ represents the phase in the positive-definite $(w, x)$ plane.
$\phi$ represents the phase in the negative-definite $(y, z)$ plane.
-/
structure LightTorusCoords where
  t : ℝ
  t_pos : 0 < t
  theta : ℝ -- phase in S^1
  phi : ℝ   -- phase in S^1

/-- An explicit nonzero null split quaternion on the light torus. -/
def lightTorusBasePoint : LightTorus := by
  refine ⟨⟨1, 0, 1, 0⟩, ?_⟩
  constructor
  · intro h
    have hw : ((1 : ℝ)) = 0 := by
      simpa using congrArg SplitQuaternion.w h
    norm_num at hw
  · unfold IsNullSplitQuaternion splitNormSq
    norm_num

/-- The explicit light-torus base point has coordinates `(1,0,1,0)` and is null. -/
theorem lightTorus_basePoint_readout :
    lightTorusBasePoint.val = ⟨1, 0, 1, 0⟩ ∧
      lightTorusBasePoint.val ≠ ⟨0, 0, 0, 0⟩ ∧
      IsNullSplitQuaternion lightTorusBasePoint.val := by
  exact ⟨rfl, lightTorusBasePoint.property.1, lightTorusBasePoint.property.2⟩

end InfoGeometry.Projective
