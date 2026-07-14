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

namespace BogoliubovVielbein

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
Commutator transport intertwines with exponential transport for a fixed generator.
-/
lemma transportCommutator_expTransport
    (X A : EndH) (t : ℝ) :
    transportCommutator (E := E) X
        (InfoGeometry.Canonical.expTransport (A := EndH) X A t)
      =
    InfoGeometry.Canonical.expTransport (A := EndH)
      X (transportCommutator (E := E) X A) t := by
  let ePos : EndH := NormedSpace.exp (t • X)
  let eNeg : EndH := NormedSpace.exp (t • (-X))
  have hPos : Commute X ePos := by
    simpa [ePos] using (((Commute.refl X).smul_right t).exp_right)
  have hNeg : Commute X eNeg := by
    simpa [eNeg, smul_neg, neg_smul] using
      (((Commute.refl X).smul_right (-t : ℝ)).exp_right)
  unfold transportCommutator InfoGeometry.Canonical.expTransport
  calc
    X * ((ePos * A) * eNeg) - ((ePos * A) * eNeg) * X
      = ((X * ePos) * A) * eNeg - ePos * (A * (eNeg * X)) := by
          simp [mul_assoc]
    _ = ((ePos * X) * A) * eNeg - ePos * (A * (X * eNeg)) := by
          rw [hPos.eq, hNeg.eq.symm]
    _ = ePos * (X * A) * eNeg - ePos * (A * X) * eNeg := by
          simp [mul_assoc]
    _ = ePos * (X * A - A * X) * eNeg := by
          simp [sub_eq_add_neg, mul_assoc, add_mul, mul_add]
    _ = InfoGeometry.Canonical.expTransport (A := EndH)
          X (transportCommutator (E := E) X A) t := by
          change
              ePos * (X * A - A * X) * eNeg
                =
              InfoGeometry.Canonical.expTransport (A := EndH) X (X * A - A * X) t
          simp [ePos, eNeg, InfoGeometry.Canonical.expTransport, mul_assoc]

/--
The transported Maurer-Cartan curvature is the exponential transport of the
base Maurer-Cartan curvature.
-/
theorem transportedMaurerCartanCurvature_eq_expTransport_maurerCartanCurvature
    (V : BogoliubovVielbeinBundle (E := E)) (t : ℝ) :
    V.transportedMaurerCartanCurvature t
      =
    InfoGeometry.Canonical.expTransport (A := EndH)
      V.connectionGenerator V.maurerCartanCurvature t := by
  unfold transportedMaurerCartanCurvature maurerCartanCurvature localFrame
  simpa [hestenesMaurerCartanCurvature] using
    (transportCommutator_expTransport (E := E) V.connectionGenerator V.reference t)

/--
The derivative of the transported local frame is the commutator with the
connection generator, read at the transported frame itself.
-/
theorem deriv_localFrame_at_eq_transportedMaurerCartanCurvature
    (V : BogoliubovVielbeinBundle (E := E)) (t : ℝ) :
    deriv (fun s => V.localFrame s) t = V.transportedMaurerCartanCurvature t := by
  rw [V.transportedMaurerCartanCurvature_eq_expTransport_maurerCartanCurvature t]
  simpa [localFrame, maurerCartanCurvature, hestenesMaurerCartanCurvature] using
    (InfoGeometry.Canonical.hasDerivAt_expTransport
      (A := EndH) (X := V.connectionGenerator) (A₀ := V.reference) t).deriv

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
  have hTransported :
      (fun s => V.transportedMaurerCartanCurvature s)
        =
      fun s =>
        InfoGeometry.Canonical.expTransport (A := EndH)
          V.connectionGenerator V.maurerCartanCurvature s := by
    funext s
    exact V.transportedMaurerCartanCurvature_eq_expTransport_maurerCartanCurvature s
  rw [hTransported]
  rw [V.transportedMaurerCartanCurvature_eq_expTransport_maurerCartanCurvature t]
  calc
    deriv
        (fun s =>
          InfoGeometry.Canonical.expTransport (A := EndH)
            V.connectionGenerator V.maurerCartanCurvature s)
        t
      =
        InfoGeometry.Canonical.expTransport (A := EndH)
          V.connectionGenerator
          (transportCommutator (E := E) V.connectionGenerator V.maurerCartanCurvature) t := by
            simpa [maurerCartanCurvature, hestenesMaurerCartanCurvature] using
              (InfoGeometry.Canonical.hasDerivAt_expTransport
                (A := EndH) (X := V.connectionGenerator) (A₀ := V.maurerCartanCurvature) t).deriv
    _ =
        transportCommutator (E := E) V.connectionGenerator
          (InfoGeometry.Canonical.expTransport (A := EndH)
            V.connectionGenerator V.maurerCartanCurvature t) := by
              exact (transportCommutator_expTransport
                (E := E) V.connectionGenerator V.maurerCartanCurvature t).symm
    _ =
        hestenesMaurerCartanCurvature (E := E)
          V.connectionGenerator
          (InfoGeometry.Canonical.expTransport (A := EndH)
            V.connectionGenerator V.maurerCartanCurvature t) := by
              rfl

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
  simpa [localFrame, maurerCartanCurvature, hestenesMaurerCartanCurvature, transportCommutator] using
    (InfoGeometry.Canonical.hasDerivAt_expTransport
      (A := EndH) (X := V.connectionGenerator) (A₀ := V.reference) t).deriv

end BogoliubovVielbeinBundle

end BogoliubovVielbein
