import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Canonical.SpectralInference

namespace InfoGeometry.Canonical.InformationTorsion

open InfoGeometry.Convex
open SpectralInference

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
structure FlatDualConnectionsData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  dual : DualConnections E

def FlatDualConnectionsLaws
    (D : FlatDualConnectionsData E) : Prop :=
  IsTorsionFree D.dual.nabla ∧ IsTorsionFree D.dual.nablaStar

def FlatDualConnections (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  {D : FlatDualConnectionsData E // FlatDualConnectionsLaws D}

namespace FlatDualConnections

abbrev dual (D : FlatDualConnections E) := D.1.dual
abbrev torsion_free_nabla (D : FlatDualConnections E) : IsTorsionFree D.dual.nabla := D.2.1
abbrev torsion_free_nablaStar (D : FlatDualConnections E) : IsTorsionFree D.dual.nablaStar := D.2.2

end FlatDualConnections

/--
A Twisted Information System where the update rule has torsion.
This occurs when the dually-flat structure is broken, leading to path-dependent
belief updates even for identical sets of evidence.
-/
structure TwistedInferenceData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  dual : DualConnections E

def TwistedInferenceLaws
    (T : TwistedInferenceData E) : Prop :=
  informationTorsion T.dual.nabla ≠ 0

def TwistedInference (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  {T : TwistedInferenceData E // TwistedInferenceLaws T}

namespace TwistedInference

abbrev dual (T : TwistedInference E) := T.1.dual
abbrev has_torsion (T : TwistedInference E) : informationTorsion T.dual.nabla ≠ 0 := T.2

end TwistedInference

end InfoGeometry.Canonical.InformationTorsion
