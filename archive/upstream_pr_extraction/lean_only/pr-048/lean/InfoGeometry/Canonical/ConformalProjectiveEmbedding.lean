import InfoGeometry.Clifford.ConformalLift55
import InfoGeometry.Clifford.ClNN
import InfoGeometry.Clifford.ConformalProjectiveEmbedding55
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford.ConformalLift55
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.ConformalProjectiveEmbedding55

/--
The projective conformal embedding F: R^{4,4} -> Cl(5,5).

F(x) = x - (x^2) n∞ + n₀

where x is a vector in the (4,4) split space,
and n₀, n∞ are the conformal null pair.

Normalization note: since the repository uses u * v + v * u = 1,
the coefficient of n∞ must be -x^2 to ensure F(x)^2 = 0.
-/
def conformalProjectiveEmbedding
    (P : ConformalNullPair)
    (x : Carrier 4) : Cl55 :=
  gammaTail 4 x - (Quad 4 x) • P.v + P.u

/--
The projective embedding lands on the null cone of Cl(5,5).
In CGA, F(x)² = 0.
-/
theorem conformalProjectiveEmbedding_null
    (P : ConformalNullPair)
    (x : Carrier 4)
    (h_anticomm_u : ∀ v_tail : Carrier 4,
      P.u * gammaTail 4 v_tail + gammaTail 4 v_tail * P.u = 0)
    (h_anticomm_v : ∀ v_tail : Carrier 4,
      P.v * gammaTail 4 v_tail + gammaTail 4 v_tail * P.v = 0) :
    (conformalProjectiveEmbedding P x) ^ 2 = 0 := by
  rw [pow_two]
  let xt : Cl55 := gammaTail 4 x
  have hx_ortho_u : xt * P.u = -P.u * xt := by
    simpa [xt] using eq_neg_of_add_eq_zero_right (h_anticomm_u x)
  have hx_ortho_v : xt * P.v = -P.v * xt := by
    simpa [xt] using eq_neg_of_add_eq_zero_right (h_anticomm_v x)
  have hx_sq : xt * xt = (Quad 4 x) • (1 : Cl55) := by
    dsimp [xt, gammaTail]
    rw [CliffordAlgebra.ι_sq_scalar, quad_tailLift 4 x]
    simp [Algebra.smul_def]
  have hF :
      F P xt (Quad 4 x) =
        conformalProjectiveEmbedding P x := by
    dsimp [F, n_zero, n_infty,
      conformalProjectiveEmbedding, xt]
    rw [smul_smul, sub_eq_add_neg]
    have hs : (1 / 2 * Quad 4 x) * (-2 : ℝ) = -(Quad 4 x) := by ring
    rw [hs]
    simp [neg_smul]
  rw [← hF]
  exact F_sq_zero P xt (Quad 4 x)
    hx_ortho_u hx_ortho_v hx_sq


end InfoGeometry.Canonical
