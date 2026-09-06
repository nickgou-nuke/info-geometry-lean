import InfoGeometry.Canonical.KZLogarithmicConnection

noncomputable section

namespace InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection

open InfoGeometry.Canonical.KZLogarithmicConnection

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-! The finite coefficient-level frontier for the Arnold--Kohno corridor.
The exterior coefficients are scalars here; a future differential-form owner
must provide the genuine de Rham realization separately. -/

structure Data (R : Type*) (A : Type*) [CommRing R] [Ring A] [Algebra R A] where
  t01 : A
  t12 : A
  t20 : A
  kohno_01_12 : bracket t01 t12 = bracket t12 t20
  kohno_12_20 : bracket t12 t20 = bracket t20 t01

def curvature (C : Data (R := R) (A := A)) (a b c : R) : A :=
  a • bracket C.t01 C.t12 +
    b • bracket C.t12 C.t20 +
    c • bracket C.t20 C.t01

theorem curvature_eq_common_bracket (C : Data (R := R) (A := A))
    (a b c : R) :
    curvature C a b c = (a + b + c) • bracket C.t01 C.t12 := by
  unfold curvature
  rw [C.kohno_01_12, C.kohno_12_20]
  rw [← add_smul, ← add_smul]

theorem curvature_zero (C : Data (R := R) (A := A)) (a b c : R)
    (hArnold : a + b + c = 0) :
    curvature C a b c = 0 := by
  rw [curvature_eq_common_bracket C a b c, hArnold, zero_smul]

end InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection
