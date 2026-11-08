/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# AKNS zero-curvature identity for the coupled cubic Schrödinger system

The fields below are formal jet coordinates.  The theorem is the finite
matrix calculation identifying the zero-curvature components with the two
coupled cubic Schrödinger residuals.  Interpreting these coordinates as jets
of differentiable functions, and imposing the focusing reduction `r = -conj q`,
requires the corresponding analytic/function-space bridge; this file does not
claim that a trapped Gross–Pitaevskii equation has this Lax pair.
-/

namespace InfoGeometry.Physics.CubicNLSAKNSLaxPair

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Spatial part of the AKNS pair, with spectral parameter `λ`. -/
def spatial (spectral q r : ℂ) : Mat2 :=
  !![-Complex.I * spectral, q; r, Complex.I * spectral]

/-- Time part of the AKNS pair, expressed using first spatial jets. -/
def temporal (spectral q r qx rx : ℂ) : Mat2 :=
  !![-2 * Complex.I * spectral ^ 2 - Complex.I * q * r,
     2 * spectral * q + Complex.I * qx;
     2 * spectral * r - Complex.I * rx,
     2 * Complex.I * spectral ^ 2 + Complex.I * q * r]

/-- Formal time derivative of the spatial matrix. -/
def spatialTimeJet (qt rt : ℂ) : Mat2 :=
  !![0, qt; rt, 0]

/-- Formal spatial derivative of the temporal matrix. -/
def temporalSpaceJet (spectral q r qx rx qxx rxx : ℂ) : Mat2 :=
  !![-Complex.I * (qx * r + q * rx),
     2 * spectral * qx + Complex.I * qxx;
     2 * spectral * rx - Complex.I * rxx,
     Complex.I * (qx * r + q * rx)]

/-- Ordered zero-curvature expression `U_t - V_x + [U,V]`. -/
def curvature (spectral q r qx rx qt rt qxx rxx : ℂ) : Mat2 :=
  spatialTimeJet qt rt - temporalSpaceJet spectral q r qx rx qxx rxx +
    (spatial spectral q r * temporal spectral q r qx rx -
      temporal spectral q r qx rx * spatial spectral q r)

/-- The two off-diagonal AKNS equations are exactly the curvature components;
the diagonal components cancel identically. -/
theorem curvature_eq_nls_residuals
    (spectral q r qx rx qt rt qxx rxx : ℂ) :
    curvature spectral q r qx rx qt rt qxx rxx =
      !![(0 : ℂ), qt - Complex.I * qxx + 2 * Complex.I * q ^ 2 * r;
        rt + Complex.I * rxx - 2 * Complex.I * q * r ^ 2, 0] := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    norm_num [pow_two, Complex.I_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [curvature, spatialTimeJet, temporalSpaceJet, spatial, temporal] <;> ring_nf
  all_goals (try rw [hI])
  all_goals ring

/-- Flatness is equivalent to the coupled cubic Schrödinger equations written
as zero residuals.  The reduction relating `r` to the conjugate of `q` is
separate, so the algebraic theorem does not encode a particular physical
reality condition. -/
theorem flat_iff_nls_residuals_zero
    (spectral q r qx rx qt rt qxx rxx : ℂ) :
    curvature spectral q r qx rx qt rt qxx rxx = 0 ↔
      qt - Complex.I * qxx + 2 * Complex.I * q ^ 2 * r = 0 ∧
      rt + Complex.I * rxx - 2 * Complex.I * q * r ^ 2 = 0 := by
  rw [curvature_eq_nls_residuals]
  constructor
  · intro h
    constructor
    · have h01 := congrFun (congrFun h 0) 1
      simpa using h01
    · have h10 := congrFun (congrFun h 1) 0
      simpa using h10
  · rintro ⟨h01, h10⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10]

/-- The scalar focusing NLS residual, with the nonlinear term kept in the
ordered form `(q * q̄) * q`. -/
def focusingResidual (q qt qxx : ℂ) : ℂ :=
  Complex.I * qt + qxx + 2 * (q * star q) * q

/-- Under the focusing reduction `r = -q̄`, the upper-right AKNS residual is
`-i` times the standard scalar focusing NLS residual.  This is an algebraic
identity on jet variables, not an assertion about a trapped GP equation. -/
theorem upper_residual_focusing_reduction (q qt qxx : ℂ) :
    qt - Complex.I * qxx + 2 * Complex.I * q ^ 2 * (-star q) =
      -Complex.I * focusingResidual q qt qxx := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    norm_num [pow_two, Complex.I_mul_I]
  unfold focusingResidual
  calc
    qt - Complex.I * qxx + 2 * Complex.I * q ^ 2 * (-star q) =
        qt - Complex.I * qxx - 2 * Complex.I * (q * star q) * q := by ring
    _ = -Complex.I * (Complex.I * qt + qxx + 2 * (q * star q) * q) := by
      linear_combination hI * qt

/-- Vanishing of the reduced upper AKNS component is equivalent to the scalar
focusing cubic NLS jet equation. -/
theorem upper_residual_zero_iff_focusing_nls
    (q qt qxx : ℂ) :
    qt - Complex.I * qxx + 2 * Complex.I * q ^ 2 * (-star q) = 0 ↔
      focusingResidual q qt qxx = 0 := by
  rw [upper_residual_focusing_reduction]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hI | hN
    · exact (neg_ne_zero.mpr Complex.I_ne_zero hI).elim
    · exact hN
  · intro h
    rw [h, mul_zero]

end InfoGeometry.Physics.CubicNLSAKNSLaxPair
