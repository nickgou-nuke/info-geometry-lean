/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.VietaPolynomials
import InfoGeometry.Canonical.QuinticTschirnhausPluckerVietaSynthesis

/-!
# Native elementary-symmetric coefficients in the quintic synthesis

The repository has two concrete presentations of the coefficients of a quintic
with roots indexed by `Fin 5`: Mathlib's multiset elementary-symmetric
functions, and the hand-expanded `vietaE1`–`vietaE5` used by the
Tschirnhaus–Plücker synthesis. This file proves that they agree, by comparing
the coefficient readouts of the two root-product polynomials.

This is a finite algebraic adapter. It does not assert a projective quotient,
Galois classification, or analytic root selection.
-/

noncomputable section

namespace InfoGeometry.Canonical

open Polynomial
open QuinticTschirnhausPluckerVietaSynthesis

variable {R : Type*} [CommRing R]

/-- The native multiset-esymm root product and the synthesis root product are
the same polynomial. -/
theorem monicQuintic_eq_monicRootPoly5 (r : Fin 5 → R) :
    monicQuintic r = monicRootPoly5 r := by
  simp only [monicQuintic, monicRootPoly5,
    Fin.prod_univ_five]

/-- The native first elementary-symmetric coefficient is the synthesis sum. -/
theorem native_e1_eq_vietaE1 (r : Fin 5 → R) :
    e1 r = vietaE1 r := by
  have hpoly := monicQuintic_eq_monicRootPoly5 r
  have hleft := congrArg (fun p : R[X] => p.coeff 4) hpoly
  rw [monicQuintic_eq_Vieta] at hleft
  rw [monicRootPoly5_coeffs r |>.1] at hleft
  simp [Polynomial.coeff_X_pow] at hleft
  exact hleft

/-- The native second elementary-symmetric coefficient is the synthesis sum. -/
theorem native_e2_eq_vietaE2 (r : Fin 5 → R) :
    e2 r = vietaE2 r := by
  have hpoly := monicQuintic_eq_monicRootPoly5 r
  have hleft := congrArg (fun p : R[X] => p.coeff 3) hpoly
  rw [monicQuintic_eq_Vieta] at hleft
  rw [monicRootPoly5_coeffs r |>.2.1] at hleft
  simp [Polynomial.coeff_X_pow] at hleft
  exact hleft

/-- The native third elementary-symmetric coefficient is the synthesis sum. -/
theorem native_e3_eq_vietaE3 (r : Fin 5 → R) :
    e3 r = vietaE3 r := by
  have hpoly := monicQuintic_eq_monicRootPoly5 r
  have hleft := congrArg (fun p : R[X] => p.coeff 2) hpoly
  rw [monicQuintic_eq_Vieta] at hleft
  rw [monicRootPoly5_coeffs r |>.2.2.1] at hleft
  simp [Polynomial.coeff_X_pow] at hleft
  exact hleft

/-- The native fourth elementary-symmetric coefficient is the synthesis sum. -/
theorem native_e4_eq_vietaE4 (r : Fin 5 → R) :
    e4 r = vietaE4 r := by
  have hpoly := monicQuintic_eq_monicRootPoly5 r
  have hleft := congrArg (fun p : R[X] => p.coeff 1) hpoly
  rw [monicQuintic_eq_Vieta] at hleft
  rw [monicRootPoly5_coeffs r |>.2.2.2.1] at hleft
  simp [Polynomial.coeff_X_pow] at hleft
  exact hleft

/-- The native fifth elementary-symmetric coefficient is the synthesis product. -/
theorem native_e5_eq_vietaE5 (r : Fin 5 → R) :
    e5 r = vietaE5 r := by
  have hpoly := monicQuintic_eq_monicRootPoly5 r
  have hleft := congrArg (fun p : R[X] => p.coeff 0) hpoly
  rw [monicQuintic_eq_Vieta] at hleft
  rw [monicRootPoly5_coeffs r |>.2.2.2.2] at hleft
  simp [Polynomial.coeff_X_pow] at hleft
  exact hleft

/-- The entire native Mathlib coefficient tuple agrees with the tuple used by
the weighted Vieta descent. -/
theorem native_vietaTuple_eq_synthesis (r : Fin 5 → R) :
    (e1 r, e2 r, e3 r, e4 r, e5 r) =
    (vietaE1 r, vietaE2 r, vietaE3 r, vietaE4 r, vietaE5 r) := by
  simp only [native_e1_eq_vietaE1, native_e2_eq_vietaE2,
    native_e3_eq_vietaE3, native_e4_eq_vietaE4,
    native_e5_eq_vietaE5]

/-- Root dilation has the expected `(1,2,3,4,5)` multidegree for Mathlib's
native elementary-symmetric coefficient tuple as well. This transports the
already-proved synthesis weights across `native_vietaTuple_eq_synthesis`. -/
theorem native_vieta_smul_weights (c : R) (r : Fin 5 → R) :
    e1 (c • r) = c * e1 r ∧
      e2 (c • r) = c ^ 2 * e2 r ∧
      e3 (c • r) = c ^ 3 * e3 r ∧
      e4 (c • r) = c ^ 4 * e4 r ∧
      e5 (c • r) = c ^ 5 * e5 r := by
  rw [native_e1_eq_vietaE1, native_e1_eq_vietaE1,
    native_e2_eq_vietaE2, native_e2_eq_vietaE2,
    native_e3_eq_vietaE3, native_e3_eq_vietaE3,
    native_e4_eq_vietaE4, native_e4_eq_vietaE4,
    native_e5_eq_vietaE5, native_e5_eq_vietaE5]
  exact vieta_smul_weights c r

end InfoGeometry.Canonical
