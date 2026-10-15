import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.Projective.SplitQuaternionMotivicDPn

/-!
# Additive Grothendieck realization of split-quaternionic projectors

The projective owner supplies the noncommutative matrix projector
`projectorN v : Matrix (Fin (n + 1)) (Fin (n + 1)) (Coquaternion R)` and proves
its trace is the scalar norm of `v`.  This file composes that trace with the
universal additive Grothendieck completion.

The result is an additive Grothendieck-group realization of these projectors.
It is not a construction of Chow motives, algebraic K₀ of projective modules,
or an identification of the Clifford colimit with a category of motives.
-/

namespace InfoGeometry.Projective.SplitQuaternionGrothendieckRealization

open InfoGeometry.Clifford.Coquaternion
open InfoGeometry.Clifford.Coquaternion.Coquaternion
open InfoGeometry.Projective.SplitComposition
open InfoGeometry.Projective.SplitQuaternionMotivicDPn

variable {R : Type*} [CommRing R]

/-- The additive matrix trace on the noncommutative projector carrier. -/
def projectorTraceAddHom (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (Coquaternion R) →+
      Coquaternion R where
  toFun := traceCoq
  map_zero' := by
    simp [traceCoq]
  map_add' A B := by
    simp [traceCoq, Finset.sum_add_distrib, Matrix.add_apply]

/-- The unique additive extension of the projector trace to the Grothendieck
group completion of the underlying additive monoid of the matrix ring. -/
def projectorTraceOnGrothendieck (n : ℕ) :
    Grothendieck (Matrix (Fin (n + 1)) (Fin (n + 1)) (Coquaternion R)) →+
      Coquaternion R :=
  grothendieckLift (projectorTraceAddHom (R := R) n)

/-- On the Grothendieck class of the projective matrix operator, the lifted
trace is exactly the split quadratic norm, embedded as a scalar coquaternion. -/
theorem projectorTraceOnGrothendieck_projectorN {n : ℕ}
    (v : VectorD n R) :
    projectorTraceOnGrothendieck (R := R) n
        (grothendieckMap
          (Matrix (Fin (n + 1)) (Fin (n + 1)) (Coquaternion R))
          (projectorN v)) =
      algebraMap R (Coquaternion R) (normSqN v) := by
  exact grothendieckLift_comp (projectorTraceAddHom (R := R) n)
    (projectorN v) |>.trans (projectorN_trace v)

/-- The Grothendieck trace readout transforms under the coquaternionic gauge
action by multiplication by the reduced norm of the gauge element. -/
theorem projectorTraceOnGrothendieck_action {n : ℕ}
    (v : VectorD n R) (u : Coquaternion R) :
    projectorTraceOnGrothendieck (R := R) n
        (grothendieckMap
          (Matrix (Fin (n + 1)) (Fin (n + 1)) (Coquaternion R))
          (projectorN (actionN v u))) =
      algebraMap R (Coquaternion R) (normSqN v * normSq u) := by
  rw [projectorTraceOnGrothendieck_projectorN]
  rw [normSqN_action]

/-- Unit-norm gauge transformations preserve the trace realization of the
projector's additive Grothendieck class. -/
theorem projectorTraceOnGrothendieck_gauge_invariant {n : ℕ}
    (v : VectorD n R) (u : Coquaternion R) (hu : normSq u = 1) :
    projectorTraceOnGrothendieck (R := R) n
        (grothendieckMap
          (Matrix (Fin (n + 1)) (Fin (n + 1)) (Coquaternion R))
          (projectorN (actionN v u))) =
      projectorTraceOnGrothendieck (R := R) n
        (grothendieckMap
          (Matrix (Fin (n + 1)) (Fin (n + 1)) (Coquaternion R))
          (projectorN v)) := by
  rw [projectorTraceOnGrothendieck_action, hu, mul_one]
  exact (projectorTraceOnGrothendieck_projectorN v).symm

end InfoGeometry.Projective.SplitQuaternionGrothendieckRealization
