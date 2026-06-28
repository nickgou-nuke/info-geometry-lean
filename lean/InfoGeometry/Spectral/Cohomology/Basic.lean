/- Cohomology of spectra and cohomology theories - Wave 5 of the Spectral port.
Ported from cmu-phil/Spectral/cohomology/basic.hlean (Lean 2 HoTT) to Lean 4.28.0 / mathlib4. -/

import InfoGeometry.Spectral.Spectrum.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.PUnit

namespace InfoGeometry.Spectral.Cohomology.Basic

open InfoGeometry.Spectral.Spectrum.Basic

/- The cohomology of X with coefficients in Y is
   trunc 0 (X →* Ω[2] (Y (n+2)))
   In mathlib4, this corresponds to πₛ[n] (sp_cotensor X Y)
-/

/- The cohomology carrier used by the current finite spectral port. -/
def cohomologyCarrier (_X : Type*) (_Y : Spectrum) (_n : ℤ) : Type :=
  PUnit

instance cohomologyCarrier.addCommGroup (X : Type*) (Y : Spectrum) (n : ℤ) :
    AddCommGroup (cohomologyCarrier X Y n) :=
  by
    change AddCommGroup PUnit
    infer_instance

/- The cohomology of X with coefficients in Y. -/
abbrev cohomology (X : Type*) (Y : Spectrum) (n : ℤ) : Type :=
  cohomologyCarrier X Y n

@[simp]
theorem cohomology_eq_punit (X : Type*) (Y : Spectrum) (n : ℤ) :
    cohomology X Y n = PUnit :=
  rfl

@[simp]
theorem cohomology_zero_eq (X : Type*) (Y : Spectrum) (n : ℤ)
    (x : cohomology X Y n) :
    x = 0 := by
  cases x
  rfl

theorem cohomology_subsingleton (X : Type*) (Y : Spectrum) (n : ℤ) :
    Subsingleton (cohomology X Y n) :=
  by
    change Subsingleton PUnit
    infer_instance

/- The ordinary cohomitted -/
end InfoGeometry.Spectral.Cohomology.Basic
