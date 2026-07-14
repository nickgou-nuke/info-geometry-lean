import InfoGeometry.Clifford.Spacetime
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture

namespace ChiralBasis

open InfoGeometry.Krein
open InfoGeometry.Clifford.Spacetime

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-!
# Chiral Operator Basis (Circularly Polarized)

This module formalizes the null-wave basis $(u_+, u_-, \epsilon)$ which 
organizes the spacetime manifold into lightcone sectors.
-/

/-- The forward lightcone null wave (u_+ = t + z). -/
@[rep_depth projective]
noncomputable def uPlus : Vec13 := (1, 0, 0, 1)

/-- The backward lightcone null wave (u_- = t - z). -/
@[rep_depth projective]
noncomputable def uMinus : Vec13 := (1, 0, 0, -1)

/-- 
The chiral operator induced by a null wave. 
For a 4-vector v, the chiral operator is effectively the matrix $\Sigma(v)$.
-/
@[rep_depth operator]
noncomputable def chiralOperator (v : Vec13) : Biquaternion E :=
  biquaternionSoldering E v

/-- 
Polarized Basis condition: u_+ and u_- are null waves.
Proven by showing their soldered determinant is zero.
-/
theorem uPlus_is_null : (soldering uPlus).det = 0 := by
  unfold uPlus
  simp [det_soldering]

theorem uMinus_is_null : (soldering uMinus).det = 0 := by
  unfold uMinus
  simp [det_soldering]

end ChiralBasis
