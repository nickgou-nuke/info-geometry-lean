import InfoGeometry.Canonical.BiQuaternionKahlerFinite
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BiQuaternionKahlerLegendreFinite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Canonical.BiQuaternionKahlerSymplecticNoetherBridge

Finite bridge from the `I4c` symplectic readout to the quadratic
Lagrangian/Hamiltonian lane.

This file does not construct smooth Killing fields, Hamiltonian vector fields,
flows, moment maps, continuum Noether currents, or field dynamics.  It closes
the finite `R^4` algebra that the manuscript uses as the common readout: the
Lagrangian symplectic form is literally the existing `symplecticI = <I4c x,y>`,
the `I4c` generator is skew for `dot4`, the finite Noether derivative vanishes
under an explicit invariant-potential premise, the radial quadratic Hamiltonian
is invariant under the finite `I4c` rotation.

#### BUCKET 1: CLOSED FINITE THEOREMS
`lagrangianSymplecticForm_eq_symplecticI`, `lagrangianSymplecticForm_skew`,
`dot4_comm`, `I4c_skew_adjoint_dot`, `I4c_self_orthogonal`,
`kinetic_I4c_invariant`, `radialQuadraticHamiltonian_I4c_invariant`, and
`finiteNoetherReadback_radial_zero`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`finiteNoetherReadback_zero_of_potential_invariant` depends only on the
explicit premise `dot4 (gradV q) (I4c.mulVec q) = 0`.

#### BUCKET 3: OPEN CLOSURE DEBT
Smooth Kähler manifolds, differentiable potentials, Hamiltonian vector fields,
Killing flows, moment maps, Noether currents, conservation along actual
solutions, gauge fields, and continuum physical dynamics.
-/

namespace InfoGeometry.Canonical.BiQuaternionKahlerSymplecticNoetherBridge

open Matrix
open InfoGeometry.Canonical.BiQuaternionKahlerFinite
open InfoGeometry.Canonical.BiQuaternionKahlerLegendreFinite

/-- The finite symplectic form read by the Lagrangian/Killing lane. -/
def lagrangianSymplecticForm (x y : R4) : ℝ :=
  dot4 (I4c.mulVec x) y

/-- The Lagrangian/Killing symplectic form is exactly the finite `I4c` readout. -/
theorem lagrangianSymplecticForm_eq_symplecticI (x y : R4) :
    lagrangianSymplecticForm x y = symplecticI x y := by
  rfl

/-- The bridged finite symplectic form is skew. -/
theorem lagrangianSymplecticForm_skew (x y : R4) :
    lagrangianSymplecticForm x y = -lagrangianSymplecticForm y x := by
  exact symplecticI_skew x y

/-- The finite Euclidean dot product on `R^4` is symmetric. -/
theorem dot4_comm (x y : R4) : dot4 x y = dot4 y x := by
  dsimp [dot4]
  simp [Fin.sum_univ_succ]
  ring

/-- The concrete `I4c` generator is skew-adjoint for `dot4`. -/
theorem I4c_skew_adjoint_dot (x y : R4) :
    dot4 (I4c.mulVec x) y = -dot4 x (I4c.mulVec y) := by
  dsimp [dot4]
  simp [I4c, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- A skew-adjoint finite generator is self-orthogonal in the `I4c` lane. -/
theorem I4c_self_orthogonal (x : R4) :
    dot4 (I4c.mulVec x) x = 0 := by
  dsimp [dot4]
  simp [I4c, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The `I4c` Noether charge readback for finite position and momentum. -/
def I4cNoetherCharge (q p : R4) : ℝ :=
  lagrangianSymplecticForm q p

/--
Finite derivative packet for `Q(q,p)=<I4c q,p>` along the algebraic equations
`qdot = p`, `pdot = -gradV(q)`.
-/
def finiteNoetherReadback (gradV : R4 → R4) (q p : R4) : ℝ :=
  dot4 (I4c.mulVec p) p - dot4 (gradV q) (I4c.mulVec q)

/--
If the finite potential gradient is invariant in the `I4c` direction, the
finite Noether readback vanishes.
-/
theorem finiteNoetherReadback_zero_of_potential_invariant
    (gradV : R4 → R4) (q p : R4)
    (hV : dot4 (gradV q) (I4c.mulVec q) = 0) :
    finiteNoetherReadback gradV q p = 0 := by
  dsimp [finiteNoetherReadback]
  rw [I4c_self_orthogonal p, hV]
  ring

/-- The radial quadratic potential gradient `gradV(q)=q` is `I4c`-invariant. -/
theorem radialGradient_I4c_invariant (q : R4) :
    dot4 q (I4c.mulVec q) = 0 := by
  rw [dot4_comm q (I4c.mulVec q)]
  exact I4c_self_orthogonal q

/-- Concrete finite Noether readback for the radial quadratic potential. -/
theorem finiteNoetherReadback_radial_zero (q p : R4) :
    finiteNoetherReadback (fun x : R4 => x) q p = 0 := by
  exact finiteNoetherReadback_zero_of_potential_invariant
    (fun x : R4 => x) q p (radialGradient_I4c_invariant q)

/-- The finite `I4c` rotation preserves the quadratic kinetic energy. -/
theorem kinetic_I4c_invariant (v : R4) :
    kinetic (I4c.mulVec v) = kinetic v := by
  dsimp [kinetic, dot4]
  simp [I4c, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/--
The radial quadratic Hamiltonian `H(q,p)=T(p)+T(q)` is invariant under the
finite `I4c` rotation on both position and momentum.
-/
theorem radialQuadraticHamiltonian_I4c_invariant (q p : R4) :
    hamiltonian kinetic (I4c.mulVec q) (I4c.mulVec p) =
      hamiltonian kinetic q p := by
  dsimp [hamiltonian]
  rw [kinetic_I4c_invariant p, kinetic_I4c_invariant q]

end InfoGeometry.Canonical.BiQuaternionKahlerSymplecticNoetherBridge
