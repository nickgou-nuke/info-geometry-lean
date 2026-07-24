import InfoGeometry.Canonical.BiQuaternionKahlerFinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Canonical.BiQuaternionKahlerLegendreFinite

Finite quadratic Legendre owner for the biquaternion/Kähler mechanics language.

This file does not construct a smooth tangent bundle, variational calculus,
Euler-Lagrange equations, Hamiltonian vector fields, Noether currents, canonical
ensembles, or physical field equations.  It closes the finite flat `R^4`
calculation used by the manuscript slogan: for the quadratic kinetic term
`T(v)=1/2 <v,v>` and an arbitrary potential `V(q)`, the canonical momentum is
`p=v`, the Legendre readout is exactly `H(q,p)=T(p)+V(q)`, and this Hamiltonian
is nonnegative when the potential is nonnegative.

#### BUCKET 1: CLOSED FINITE THEOREMS
`legendreReadout_eq_hamiltonian`, `hamiltonian_eq_total_energy`,
`kinetic_nonneg`, and `hamiltonian_nonneg_of_potential_nonneg`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`hamiltonian_nonneg_of_potential_nonneg` depends only on the explicit premise
`0 ≤ V q`.

#### BUCKET 3: OPEN CLOSURE DEBT
Differentiable Legendre transforms, Euler-Lagrange equations, Hamilton's
equations, symplectic flows, Killing/Noether conservation laws, partition
functions, Massieu/Fisher geometry from a genuine finite measure, and continuum
field dynamics.
-/

namespace InfoGeometry.Canonical.BiQuaternionKahlerLegendreFinite

open InfoGeometry.Canonical.BiQuaternionKahlerFinite

/-- Quadratic kinetic energy on the finite `R^4` carrier. -/
noncomputable def kinetic (v : R4) : ℝ :=
  (1 / 2 : ℝ) * dot4 v v

/-- Finite flat Lagrangian `L(q,v)=T(v)-V(q)`. -/
noncomputable def lagrangian (V : R4 → ℝ) (q v : R4) : ℝ :=
  kinetic v - V q

/-- Canonical momentum for the identity metric quadratic kinetic term. -/
def conjugateMomentum (v : R4) : R4 :=
  v

/-- Finite Hamiltonian `H(q,p)=T(p)+V(q)`. -/
noncomputable def hamiltonian (V : R4 → ℝ) (q p : R4) : ℝ :=
  kinetic p + V q

/-- Legendre readout evaluated at the canonical momentum `p=v`. -/
noncomputable def legendreReadout (V : R4 → ℝ) (q v : R4) : ℝ :=
  dot4 (conjugateMomentum v) v - lagrangian V q v

/-- The finite quadratic Legendre readout equals the Hamiltonian. -/
theorem legendreReadout_eq_hamiltonian (V : R4 → ℝ) (q v : R4) :
    legendreReadout V q v = hamiltonian V q (conjugateMomentum v) := by
  dsimp [legendreReadout, hamiltonian, lagrangian, conjugateMomentum, kinetic]
  ring

/-- The Hamiltonian is exactly kinetic plus potential energy. -/
theorem hamiltonian_eq_total_energy (V : R4 → ℝ) (q p : R4) :
    hamiltonian V q p = (1 / 2 : ℝ) * dot4 p p + V q := by
  rfl

/-- The quadratic kinetic energy is nonnegative on the finite carrier. -/
theorem kinetic_nonneg (v : R4) : 0 ≤ kinetic v := by
  dsimp [kinetic, dot4]
  simp [Fin.sum_univ_succ]
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]

/-- Nonnegative potential implies nonnegative finite Hamiltonian. -/
theorem hamiltonian_nonneg_of_potential_nonneg (V : R4 → ℝ) (q p : R4)
    (hV : 0 ≤ V q) : 0 ≤ hamiltonian V q p := by
  dsimp [hamiltonian]
  nlinarith [kinetic_nonneg p, hV]

end InfoGeometry.Canonical.BiQuaternionKahlerLegendreFinite
