import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Canonical.SpectralInference

namespace InfoGeometry.Canonical.InformationTorsion

open InfoGeometry.Convex
open InfoGeometry.Canonical.SpectralInference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
A Connection on the information manifold.
Maps two tangent vectors to a third (the directional derivative).
-/
def Connection (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  E → E → E

/--
Dual Connections (∇, ∇*).
Two connections are dual with respect to a metric g if:
u[g(v, w)] = g(∇_u v, w) + g(v, ∇*_u w).
In Info-Geometry, ∇ is the e-connection and ∇* is the m-connection.
-/
structure DualConnections (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  nabla : Connection E
  nablaStar : Connection E

/--
The Information Torsion Tensor.
Measures the non-symmetry of the belief update connection.
T(u, v) = ∇_u v - ∇_v u - [u, v].
For finite-dimensional flat spaces, we assume [u, v] = 0.
-/
def informationTorsion (conn : Connection E) : E → E → E :=
  fun u v => conn u v - conn v u

/-- Definition `IsTorsionFree`. -/
def IsTorsionFree (conn : Connection E) : Prop :=
  informationTorsion conn = 0

/-- Structure `FlatDualConnections`. -/
structure FlatDualConnections (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  dual : DualConnections E
  torsion_free_nabla : IsTorsionFree dual.nabla
  torsion_free_nablaStar : IsTorsionFree dual.nablaStar

omit [FiniteDimensional ℝ E] in
/--
A bridge form for torsion-freeness in the dually-flat setting.
This theorem packages explicit torsion-free hypotheses for both dual connections.
-/
theorem hessian_is_torsion_free (_H : HessianGeometry E) (D : FlatDualConnections E) :
    informationTorsion D.dual.nabla = 0 ∧ informationTorsion D.dual.nablaStar = 0 :=
  ⟨D.torsion_free_nabla, D.torsion_free_nablaStar⟩

/--
A Twisted Information System where the update rule has torsion.
This occurs when the dually-flat structure is broken, leading to path-dependent
belief updates even for identical sets of evidence.
-/
structure TwistedInference (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  dual : DualConnections E
  has_torsion : informationTorsion dual.nabla ≠ 0

end InfoGeometry.Canonical.InformationTorsion
