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

@[simp] theorem quasilatticeDirac_zero
    (V : BogoliubovVielbeinBundle (E := E))
    (D : EndH) :
    quasilatticeDirac V D 0 = D := by
  simp [quasilatticeDirac, InfoGeometry.Canonical.expTransport]

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
  calc
    deriv (fun s => InfoGeometry.Canonical.expTransport (A := EndH) V.connectionGenerator D s) t
      =
        InfoGeometry.Canonical.expTransport (A := EndH)
          V.connectionGenerator
          (InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
            (E := E) V.connectionGenerator D) t := by
            simpa using
              (InfoGeometry.Canonical.hasDerivAt_expTransport
                (A := EndH) (X := V.connectionGenerator) (A₀ := D) t).deriv
    _ =
        InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
          (E := E) V.connectionGenerator
          (InfoGeometry.Canonical.expTransport (A := EndH) V.connectionGenerator D t) := by
            exact (InfoGeometry.Canonical.BogoliubovVielbein.BogoliubovVielbeinBundle.transportCommutator_expTransport
              (E := E) V.connectionGenerator D t).symm
    _ = V.connectionGenerator * (quasilatticeDirac V D t)
          - (quasilatticeDirac V D t) * V.connectionGenerator := by
            rfl

/--
The infinitesimal Dirac transport splits into the phase-linear and
phase-antilinear commutator channels of the connection generator.
-/
theorem deriv_quasilatticeDirac_eq_phaseLinear_add_phaseAntilinear
    (V : BogoliubovVielbeinBundle (E := E))
    (D : EndH) (t : ℝ) :
    deriv (fun s => quasilatticeDirac V D s) t
      =
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
        (E := E)
        (InfoGeometry.Canonical.BogoliubovTransport.phaseLinearPart
          (E := E) V.connectionGenerator)
        (quasilatticeDirac V D t)
      +
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
        (E := E)
        (InfoGeometry.Canonical.BogoliubovTransport.phaseAntilinearPart
          (E := E) V.connectionGenerator)
        (quasilatticeDirac V D t) := by
  rw [deriv_quasilatticeDirac]
  simpa using
    (InfoGeometry.Canonical.BogoliubovTransport.transportCommutator_split_generator
      (E := E) V.connectionGenerator (quasilatticeDirac V D t))

/--
If the transported Dirac operator commutes with the phase-linear part of the
connection generator, its infinitesimal transport is carried purely by the
phase-antilinear source channel.
-/
theorem deriv_quasilatticeDirac_eq_phaseAntilinear_of_commute_phaseLinearPart
    (V : BogoliubovVielbeinBundle (E := E))
    (D : EndH) (t : ℝ)
    (hComm :
      Commute (quasilatticeDirac V D t)
        (InfoGeometry.Canonical.BogoliubovTransport.phaseLinearPart
          (E := E) V.connectionGenerator)) :
    deriv (fun s => quasilatticeDirac V D s) t
      =
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
      (E := E)
      (InfoGeometry.Canonical.BogoliubovTransport.phaseAntilinearPart
        (E := E) V.connectionGenerator)
      (quasilatticeDirac V D t) := by
  rw [deriv_quasilatticeDirac_eq_phaseLinear_add_phaseAntilinear V D t]
  have hZero :
      InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
          (E := E)
          (InfoGeometry.Canonical.BogoliubovTransport.phaseLinearPart
            (E := E) V.connectionGenerator)
          (quasilatticeDirac V D t)
        = 0 := by
    unfold InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
    exact sub_eq_zero.mpr hComm.eq.symm
  simp [hZero]

/--
At the reference point, gauge-commuting Dirac seeds evolve purely through the
phase-antilinear source channel of the connection generator.
-/
theorem deriv_quasilatticeDirac_at_zero_eq_phaseAntilinear_of_commute_phaseLinearPart
    (V : BogoliubovVielbeinBundle (E := E))
    (D : EndH)
    (hComm :
      Commute D
        (InfoGeometry.Canonical.BogoliubovTransport.phaseLinearPart
          (E := E) V.connectionGenerator)) :
    deriv (fun s => quasilatticeDirac V D s) 0
      =
    InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
      (E := E)
      (InfoGeometry.Canonical.BogoliubovTransport.phaseAntilinearPart
        (E := E) V.connectionGenerator) D := by
  rw [deriv_quasilatticeDirac_eq_phaseAntilinear_of_commute_phaseLinearPart
    V D 0]
  · simp
  · simpa [quasilatticeDirac_zero] using hComm

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
  let X : EndH := V.connectionGenerator
  let δD : EndH := InfoGeometry.Canonical.BogoliubovTransport.transportCommutator
    (E := E) X D
  have hDeriv :
      (fun t => deriv (fun s => quasilatticeDirac V D s) t)
        =
      fun t => InfoGeometry.Canonical.expTransport (A := EndH) X δD t := by
    funext t
    simpa [X, δD, quasilatticeDirac] using
      (InfoGeometry.Canonical.hasDerivAt_expTransport
        (A := EndH) (X := X) (A₀ := D) t).deriv
  have hSecond :
      deriv (fun t => InfoGeometry.Canonical.expTransport (A := EndH) X δD t) 0
        =
      X * δD - δD * X := by
    simpa [Ring.lie_def, sub_eq_add_neg] using
      (InfoGeometry.Canonical.deriv_expTransport_at_zero
        (A := EndH) (X := X) (A₀ := δD))
  dsimp
  rw [hDeriv]
  simpa [X, δD, InfoGeometry.Canonical.BogoliubovTransport.transportCommutator]
    using hSecond

end InfoGeometry.Canonical.QuasilatticeDirac
