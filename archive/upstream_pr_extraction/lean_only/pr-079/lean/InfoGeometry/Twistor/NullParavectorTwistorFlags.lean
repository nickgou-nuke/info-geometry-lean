import InfoGeometry.Geometry.PauliParavectorBridge
import InfoGeometry.Twistor.PenroseIncidence

/-!
# Null paravector/twistor incidence flags

This owner keeps two finite relations separate:

* a kernel-spinor datum `P(v) π = 0` for a null paravector; and
* ordinary Penrose incidence `Z = (i P(v) π, π)`.

Ordinary incidence is not identified with the kernel condition, and no
configuration-space injectivity is asserted here.
-/

noncomputable section

namespace InfoGeometry.Twistor.NullParavectorTwistorFlags

open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Twistor.PenroseIncidence

/-- Ordinary Penrose incidence for the Pauli representative of a paravector. -/
def IncidentTwistor
    (v : Minkowski4) (π : Spinor2) (Z : Twistor4) : Prop :=
  Z = incidenceLinearMap (pauliMatrix v) π

/-- A null paravector together with a nonzero spinor in the Pauli kernel. -/
structure NullParavectorKernelSpinor where
  v : Minkowski4
  hv : v.IsNull
  π : Spinor2
  hπ : π ≠ 0
  hker : Matrix.mulVec (pauliMatrix v) π = 0

/-- A general Penrose incidence flag over a null paravector. -/
structure BoundaryIncidenceFlag where
  v : Minkowski4
  hv : v.IsNull
  π : Spinor2
  hπ : π ≠ 0
  Z : Twistor4
  hInc : IncidentTwistor v π Z

/-- The kernel flags form a special subclass of incidence flags. -/
structure BoundaryKernelFlag extends BoundaryIncidenceFlag where
  hker : Matrix.mulVec (pauliMatrix toBoundaryIncidenceFlag.v) π = 0

theorem BoundaryIncidenceFlag.nonzero_twistor
    (F : BoundaryIncidenceFlag) : F.Z ≠ 0 := by
  intro hZ
  have hmap : incidenceLinearMap (pauliMatrix F.v) F.π = 0 := by
    rw [← F.hInc, hZ]
  have hsecond := congrArg Prod.snd hmap
  have hπzero : F.π = 0 := by
    simpa [incidenceLinearMap] using hsecond
  exact F.hπ hπzero

theorem BoundaryKernelFlag.incidence_zero_first
    (F : BoundaryKernelFlag) :
    F.toBoundaryIncidenceFlag.Z.1 = 0 := by
  rw [F.toBoundaryIncidenceFlag.hInc]
  simp [incidenceLinearMap, omegaLinearMap, F.hker]

theorem BoundaryKernelFlag.incidence_special_form
    (F : BoundaryKernelFlag) :
    F.toBoundaryIncidenceFlag.Z = (0, F.π) := by
  apply Prod.ext
  · exact F.incidence_zero_first
  · rw [F.toBoundaryIncidenceFlag.hInc]
    rfl

end InfoGeometry.Twistor.NullParavectorTwistorFlags
