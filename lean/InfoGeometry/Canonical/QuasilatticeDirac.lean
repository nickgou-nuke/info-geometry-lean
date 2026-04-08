import InfoGeometry.Canonical.BogoliubovVielbein
import InfoGeometry.Canonical.ChiralAction

/-!
# Quasilattice Dirac Operator

This module formalizes the `QuasilatticeDiracOperator`, the Dirac operator
defined over the curved/deformed informational quasilattice.

In the physical interpretation, the Dirac operator represents the local "mass"
or energy coupling of the Majorana modes. When the quasilattice is stretched
(dilation anomaly), the Dirac operator must be transported via the Bogoliubov
vielbein to maintain local consistency.
-/

namespace InfoGeometry.Canonical.QuasilatticeDirac

open InfoGeometry.Canonical
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Krein
open scoped InnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
The Dirac operator coupled to a Bogoliubov vielbein.
It is the base Dirac operator transported to the local inertial frame at parameter `t`.
-/
noncomputable def quasilatticeDirac
    (V : BogoliubovVielbeinBundle (E := E))
    (D : EndH) (t : ℝ) : EndH :=
  InfoGeometry.Canonical.expTransport (A := EndH)
    V.connectionGenerator D t

/--
**Vielbein Covariance Law**:
The Lie-derivative of the quasilattice Dirac operator is the commutator of the
connection and the operator itself.
-/
theorem deriv_quasilatticeDirac
    (V : BogoliubovVielbeinBundle (E := E))
    (D : EndH) (t : ℝ) :
    deriv (fun s => quasilatticeDirac V D s) t
      =
    V.connectionGenerator * (quasilatticeDirac V D t)
      - (quasilatticeDirac V D t) * V.connectionGenerator := by
  unfold quasilatticeDirac
  simpa using
    (InfoGeometry.Canonical.hasDerivAt_expTransport
      (A := EndH) (X := V.connectionGenerator) (A₀ := D) t).deriv

/--
**Curvature-Dirac Coupling**:
The second derivative of the quasilattice Dirac operator at the reference point
is governed by the Maurer-Cartan curvature.
-/
theorem deriv2_quasilatticeDirac_at_zero
    (V : BogoliubovVielbeinBundle (E := E))
    (D : EndH) :
    let f := fun t => quasilatticeDirac V D t
    deriv (fun t => deriv f t) 0
      =
    V.connectionGenerator * (V.connectionGenerator * D - D * V.connectionGenerator)
      - (V.connectionGenerator * D - D * V.connectionGenerator) * V.connectionGenerator := by
  let f := fun t => quasilatticeDirac V D t
  have h1 : deriv f = fun t => V.connectionGenerator * (f t) - (f t) * V.connectionGenerator := by
    ext t
    exact deriv_quasilatticeDirac V D t
  rw [h1]
  have h_diff : DifferentiableAt ℝ f 0 :=
    (InfoGeometry.Canonical.hasDerivAt_expTransport (A := EndH) (X := V.connectionGenerator) (A₀ := D) 0).differentiableAt
  rw [deriv_sub]
  · rw [deriv_const_mul, deriv_mul_const]
    · unfold f
      simp [quasilatticeDirac, InfoGeometry.Canonical.deriv_expTransport_at_zero]
    · exact h_diff
    · exact h_diff
  · apply DifferentiableAt.const_mul
    exact h_diff
  · apply DifferentiableAt.mul_const
    exact h_diff

end InfoGeometry.Canonical.QuasilatticeDirac
