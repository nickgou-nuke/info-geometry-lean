import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.AlbertCubicTripotent

namespace InfoGeometry.OperatorAlgebra.TKK

/--
  The abstract structural bounds for a 5-graded Super-TKK algebra.
  We isolate g_0 strictly as the operator automorphism group acting over
  the Jordan pairs, mapping the exact boundary of P^3 = P.
-/
structure SuperTKKStructure (M : Type*) [Ring M] where
  -- The Jordan tripotent grading operator in g_0
  P : M

  -- The structural invariant boundary: Tripotency
  tripotent_P : P^3 = P

variable {M : Type*} [Ring M] (sys : SuperTKKStructure M)

/--
  THEOREM: Tripotent Adjoint 5-Grading.
  Proves that if P^3 = P, then the adjoint operator ad_P completely bounds
  the 5-graded Super-TKK spectrum (eigenvalues -2, -1, 0, 1, 2) via the
  characteristic polynomial: ad_P^5(X) - 5 ad_P^3(X) + 4 ad_P(X) = 0.
-/
theorem super_tkk_5_grading (X : M) :
    let adP (Y : M) := sys.P * Y - Y * sys.P
    adP (adP (adP (adP (adP X)))) - 5 • adP (adP (adP X)) + 4 • adP X = 0 := by
  intro adP
  have h3 : sys.P ^ 3 = sys.P := sys.tripotent_P
  have h4 : sys.P ^ 4 = sys.P ^ 2 := by
    calc sys.P ^ 4 = sys.P ^ 3 * sys.P := by noncomm_ring
      _ = sys.P * sys.P := by rw [h3]
      _ = sys.P ^ 2 := by noncomm_ring
  have h5 : sys.P ^ 5 = sys.P := by
    calc sys.P ^ 5 = sys.P ^ 4 * sys.P := by noncomm_ring
      _ = sys.P ^ 2 * sys.P := by rw [h4]
      _ = sys.P ^ 3 := by noncomm_ring
      _ = sys.P := h3
  calc adP (adP (adP (adP (adP X)))) - 5 • adP (adP (adP X)) + 4 • adP X
    = sys.P^5 * X - 5 • (sys.P^4 * X * sys.P) + 10 • (sys.P^3 * X * sys.P^2) - 10 • (sys.P^2 * X * sys.P^3) + 5 • (sys.P * X * sys.P^4) - X * sys.P^5
      - 5 • (sys.P^3 * X - 3 • (sys.P^2 * X * sys.P) + 3 • (sys.P * X * sys.P^2) - X * sys.P^3)
      + 4 • (sys.P * X - X * sys.P) := by
        dsimp [adP]
        noncomm_ring
    _ = sys.P * X - 5 • (sys.P^2 * X * sys.P) + 10 • (sys.P * X * sys.P^2) - 10 • (sys.P^2 * X * sys.P) + 5 • (sys.P * X * sys.P^2) - X * sys.P
      - 5 • (sys.P * X - 3 • (sys.P^2 * X * sys.P) + 3 • (sys.P * X * sys.P^2) - X * sys.P)
      + 4 • (sys.P * X - X * sys.P) := by
        rw [h5, h4, h3]
    _ = 0 := by noncomm_ring

/--
  Wires the Albert algebra's characteristic Freudenthal cubic reduction
  directly into the 5-graded Super-TKK base structure.
-/
def superTKK_of_Freudenthal {K : Type*} [CommRing K] [Algebra K M]
    (sys : Albert.CubicNorm M K)
    (P : M)
    (h_tr1 : sys.trace1 P = 0)
    (h_tr2 : sys.trace2 P = -1)
    (h_nrm : sys.norm P = 0) : SuperTKKStructure M :=
  { P := P
  , tripotent_P := Albert.tripotency_is_cubic_rank2_special sys P h_tr1 h_tr2 h_nrm
  }

end InfoGeometry.OperatorAlgebra.TKK
