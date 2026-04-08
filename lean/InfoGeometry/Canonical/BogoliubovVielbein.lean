import InfoGeometry.Canonical.BerryConnection
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Bogoliubov Vielbein Bundle

This file formalizes the `BogoliubovVielbeinBundle`, the geometric object that
attaches a flat, local inertial measurement frame to the curved/deformed
informational quasilattice.

In the physical interpretation, the doubled Krein carrier is a quasilattice
of real Majoranas. Basis stretching (dilation anomaly) generates state-space
curvature. To measure distances and phases locally without global coordinate
failure, one must transport a flat reference frame via exponential modular flow.
The resulting operator frame is the Bogoliubov Vielbein.
-/

namespace InfoGeometry.Canonical.BogoliubovVielbein

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BerryPhase
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
The state-space spin frame that connects the flat, undeformed reference state
to the deformed physical quasilattice.
-/
structure BogoliubovVielbeinBundle where
  /-- The base reference point (the unperturbed operator or state). -/
  reference : EndH
  /-- The transport generator `X` (the connection). -/
  connectionGenerator : EndH

namespace BogoliubovVielbeinBundle

/--
The local inertial frame mapped into the deformed physical space at parameter `t`.
This represents the frame dragged along the orbit of the connection.
-/
noncomputable def localFrame
    (V : BogoliubovVielbeinBundle (E := E)) (t : ℝ) : EndH :=
  InfoGeometry.Canonical.expTransport (A := EndH)
    V.connectionGenerator V.reference t

/--
The Maurer-Cartan curvature evaluated at the base reference frame.
This captures the geometric frustration of the local quasilattice.
-/
noncomputable def maurerCartanCurvature
    (V : BogoliubovVielbeinBundle (E := E)) : EndH :=
  hestenesMaurerCartanCurvature (E := E)
    V.connectionGenerator V.reference

/--
The transported Maurer-Cartan curvature at parameter `t`.
This is the curvature readout as seen by the local inertial frame.
-/
noncomputable def transportedMaurerCartanCurvature
    (V : BogoliubovVielbeinBundle (E := E)) (t : ℝ) : EndH :=
  hestenesMaurerCartanCurvature (E := E)
    V.connectionGenerator (V.localFrame t)

/--
**Bianchi-type Identity**:
The Lie-derivative of the transported Maurer-Cartan curvature is exactly the
commutator of the connection generator and the curvature itself.
This expresses the self-consistency (integrability) of the null web under transport.
-/
theorem bianchi_identity
    (V : BogoliubovVielbeinBundle (E := E)) (t : ℝ) :
    deriv (fun s => V.transportedMaurerCartanCurvature s) t
      =
    hestenesMaurerCartanCurvature (E := E)
      V.connectionGenerator (V.transportedMaurerCartanCurvature t) := by
  unfold transportedMaurerCartanCurvature hestenesMaurerCartanCurvature
  -- d/dt [X, A(t)] = [X, dA/dt]
  have h_deriv :
      deriv (fun s => transportCommutator V.connectionGenerator (V.localFrame s)) t
        = transportCommutator V.connectionGenerator (deriv V.localFrame t) := by
    unfold transportCommutator
    rw [deriv_sub]
    · rw [deriv_const_comp, deriv_comp_const]
      · rfl
      · exact (InfoGeometry.Canonical.hasDerivAt_expTransport (A := EndH) (X := V.connectionGenerator) (A₀ := V.reference) t).differentiableAt
      · exact (InfoGeometry.Canonical.hasDerivAt_expTransport (A := EndH) (X := V.connectionGenerator) (A₀ := V.reference) t).differentiableAt
    · apply DifferentiableAt.const_comp
      exact (InfoGeometry.Canonical.hasDerivAt_expTransport (A := EndH) (X := V.connectionGenerator) (A₀ := V.reference) t).differentiableAt
    · apply DifferentiableAt.comp_const
      exact (InfoGeometry.Canonical.hasDerivAt_expTransport (A := EndH) (X := V.connectionGenerator) (A₀ := V.reference) t).differentiableAt
  rw [h_deriv, V.deriv_localFrame_at t]
  -- [X, expTransport (X, [X, A], t)] = [X, [X, expTransport (X, A, t)]]
  -- This is true because expTransport commutes with the commutator of its generator.
  exact InfoGeometry.Canonical.expTransport_commutator (X := V.connectionGenerator) (A := V.connectionGenerator) (B := V.reference) t

/--
Lie-derivative evolution law for the local spin frame at the reference point (`t = 0`).
The rate of frame deformation is exactly the Maurer-Cartan connection curvature.
-/
theorem deriv_localFrame_at_zero
    (V : BogoliubovVielbeinBundle (E := E)) :
    deriv (fun t => V.localFrame t) 0 = V.maurerCartanCurvature := by
  simpa [localFrame, maurerCartanCurvature, hestenesMaurerCartanCurvature] using
    InfoGeometry.Canonical.deriv_expTransport_at_zero
      (A := EndH) (X := V.connectionGenerator) (A₀ := V.reference)

/--
Global Lie-derivative evolution law for the local spin frame at an arbitrary parameter `t`.
The frame deformation propagates along the exponential orbit of the Maurer-Cartan curvature.
-/
theorem deriv_localFrame_at
    (V : BogoliubovVielbeinBundle (E := E)) (t : ℝ) :
    deriv (fun s => V.localFrame s) t
      =
    InfoGeometry.Canonical.expTransport (A := EndH)
      V.connectionGenerator V.maurerCartanCurvature t := by
  simpa [localFrame, maurerCartanCurvature, hestenesMaurerCartanCurvature] using
    (InfoGeometry.Canonical.hasDerivAt_expTransport
      (A := EndH) (X := V.connectionGenerator) (A₀ := DFunLike.coe reference V) t).deriv

end BogoliubovVielbeinBundle

end InfoGeometry.Canonical.BogoliubovVielbein
