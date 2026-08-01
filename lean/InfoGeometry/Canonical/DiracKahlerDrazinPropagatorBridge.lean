import InfoGeometry.Canonical.RealHestenesKreinHomology
import InfoGeometry.Canonical.Drazin

/-!
# InfoGeometry.Canonical.DiracKahlerDrazinPropagatorBridge

Bridging the Hestenes-Krein real substrate with the Dirac-Kahler propagator
using the Drazin generalized inverse.

The Drazin witness supplies a commuting core projector and a generalized
inverse law. This file records those finite algebraic readouts only; it does
not assert a QFT Green's-function, Feynman boundary-condition, or analytic
propagator theorem.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse

variable {C : Type*} [AddCommGroup C] [Module ℝ C]

/-- **1. The Dirac-Kahler Propagator G is the Drazin Inverse** -/
def isDiracKahlerPropagator (D G : Module.End ℝ C) (k : ℕ) : Prop :=
  IsDrazinInverse D G k

/- The Drazin core and complementary readouts decompose the identity. -/
theorem dirac_drazin_projection_decomposition
    (D G : Module.End ℝ C) (k : ℕ)
    (hProp : isDiracKahlerPropagator D G k) :
    D * G + complementaryProjection D G = 1 := by
  simpa [InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection] using
    (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_add_complementaryProjection
      (a := D) (b := G))

/- The Drazin inverse commutes with its operator. -/
theorem dirac_drazin_comm
    (D G : Module.End ℝ C) (k : ℕ)
    (hProp : isDiracKahlerPropagator D G k) :
    D * G = G * D :=
  hProp.comm

/- The generalized inverse law supplied by the Drazin witness. -/
theorem dirac_drazin_idempotent
    (D G : Module.End ℝ C) (k : ℕ)
    (hProp : isDiracKahlerPropagator D G k) :
    G * D * G = G :=
  hProp.idempotent

/-- **4. Option A: Drazin Green's Function Property (D² G D² = D² for index 1)**
    When the Drazin index is 1 (Group Inverse), the propagator satisfies the
    strict operator identity A * G * A = A.
    Setting A = D² represents the Laplacian in QFT. -/
theorem drazin_greens_function
    (A G : Module.End ℝ C)
    (hProp : IsDrazinInverse A G 1) :
    A * G * A = A := by
  have h_comm : G * A = A * G := hProp.comm.symm
  calc
    A * G * A = A * (G * A) := by simp [mul_assoc]
    _ = A * (A * G) := by rw [h_comm]
    _ = A ^ 2 * G := by simp [pow_two, mul_assoc]
    _ = A := by simpa [pow_two] using hProp.power

end InfoGeometry.Canonical
