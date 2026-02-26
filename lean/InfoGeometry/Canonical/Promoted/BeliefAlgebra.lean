import InfoGeometry.Canonical.Promoted.InformationTorsion
import Mathlib.LinearAlgebra.Matrix.Trace

namespace InfoGeometry.Research.BeliefAlgebra

open InfoGeometry.Research.InformationTorsion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
The Non-commutative Algebra of Belief Updates.
In its simplest form, the algebra is represented by linear operators on the state space.
For a twisted inference system, updates do not commute.
-/
structure BeliefSystem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  Twisted : TwistedInference E

namespace BeliefSystem

variable (B : BeliefSystem E)

omit [FiniteDimensional ℝ E] in
/--
Theorem: If the inference system has non-zero torsion, there exist 
belief updates whose composition depends on the order of evidence.
[Update u, Update v] ≠ 0.
-/
theorem non_commutative_updates :
    ∃ (u v : E), B.Twisted.dual.nabla u v ≠ B.Twisted.dual.nabla v u := by
  by_contra h_comm
  push_neg at h_comm
  have h_torsion := B.Twisted.has_torsion
  apply h_torsion
  funext u v
  unfold informationTorsion
  simp [h_comm u v]

/--
The Information Holonomy Lie Algebra.
Defined by the commutation relations of belief updates.
This identifies the algebraic structure of the 'memory' of the learning system.
-/
def InformationLieAlgebra (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  E →L[ℝ] E -- Operators representing belief shifts

end BeliefSystem

end InfoGeometry.Research.BeliefAlgebra
