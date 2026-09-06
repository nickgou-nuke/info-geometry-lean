import InfoGeometry.Canonical.SplitOctonionQuaternionGrassmannian

namespace InfoGeometry.Canonical

/-!
# Split-quaternion associative Grassmannian bridge

This file is a theorem-safe bridge over the algebraic split-quaternion
Grassmannian owner.  It reuses the intrinsic three-plane, its three-dimensional
finrank, the scalar-zero readout, and the restricted volume form already owned
by `SplitOctonionQuaternionGrassmannian`.

It does not assert a homogeneous-space identification or any additional
topological quotient theorem.
-/

/-- Alias for the intrinsic associative Grassmannian carrier. -/
abbrev SplitQuaternionAssociativeGrassmannian := SplitQuaternionGrassmannian

/-- Alias for the intrinsic imaginary associative plane. -/
noncomputable abbrev splitQuaternionAssociativePlane
    (W : SplitQuaternionAssociativeGrassmannian) :
    Submodule ℚ imaginarySplitOctonion :=
  imaginaryAssociativePlane W

/-- The associative plane is three-dimensional. -/
theorem associativePlane_finrank
    (W : SplitQuaternionAssociativeGrassmannian) :
    Module.finrank ℚ (splitQuaternionAssociativePlane W) = 3 := by
  simpa [splitQuaternionAssociativePlane] using imaginaryAssociativePlane_finrank W

/-- The associative plane consists of scalar-zero elements. -/
theorem associativePlane_mem_scalar_zero
    (W : SplitQuaternionAssociativeGrassmannian)
    {x : imaginarySplitOctonion}
    (hx : x ∈ splitQuaternionAssociativePlane W) :
    scalarPart x.1 = 0 := by
  simpa [splitQuaternionAssociativePlane] using
    (imaginaryAssociativePlane_mem_scalar_zero W hx)

/-- Alias for the restricted canonical volume form on the associative plane. -/
noncomputable abbrev associativeVolumeForm
    (W : SplitQuaternionAssociativeGrassmannian) :
    splitQuaternionAssociativePlane W →
      splitQuaternionAssociativePlane W →
      splitQuaternionAssociativePlane W → ℚ :=
  volumeForm W

/-- The volume form on the associative plane is the canonical restriction. -/
theorem associativeVolumeForm_restriction
    (W : SplitQuaternionAssociativeGrassmannian)
    (x y z : splitQuaternionAssociativePlane W) :
    associativeVolumeForm W x y z =
      canonicalSplitG2ThreeFormValue
        (x : imaginarySplitOctonion)
        (y : imaginarySplitOctonion)
        (z : imaginarySplitOctonion) := by
  simpa [associativeVolumeForm, splitQuaternionAssociativePlane] using
    volumeForm_restriction W x y z

end InfoGeometry.Canonical
