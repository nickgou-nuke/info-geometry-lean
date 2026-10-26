/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.RindlerCartanFrame
import InfoGeometry.Algebra.MatrixLieCentralDefect

/-!
# Explicit spin-to-vector Cartan torsion in the Rindler chart

The Clifford encoding and its adjoint compatibility are computed explicitly.
A scalar shift of the spin lift disappears through this map. Contorsion is
an independent Lorentz-valued input; it is not inferred from acceleration,
from a central Lie defect, or from a discrete projective multiplier.
The formulas are pointwise in `(t,x)`; a genuine coframe requires `N ≠ 0`.
-/

noncomputable section

namespace InfoGeometry.Geometry.RindlerSpinTorsion

open InfoGeometry.Geometry.RindlerCartanFrame
open InfoGeometry.Geometry.RindlerLapseCalculus
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Algebra.MatrixLieCentralDefect

abbrev Vec := Fin 2 → ℝ

/-- Time has square -1 and space has square +1. -/
def cliffordVector (v : Vec) : Mat2 := v 0 • Eminus + v 1 • Eplus

theorem cliffordVector_injective : Function.Injective cliffordVector := by
  intro v w h
  have ht := congrArg (fun M : Mat2 => M 0 1) h
  have hx := congrArg (fun M : Mat2 => M 0 0) h
  ext i
  fin_cases i
  · simpa [cliffordVector, Eminus, Eplus] using ht
  · simpa [cliffordVector, Eminus, Eplus] using hx

/-- The existing Rindler coframe, with coordinate tangent input. -/
def coframe (a x : ℝ) (v : Tangent) : Vec := ![lapse a x * v.1, v.2]

def exteriorCoframe (a x : ℝ) (v w : Tangent) : Vec :=
  ![dCoframeTime a x v w, 0]

/-- A pointwise Lorentz-valued connection with independent contorsion slots. -/
def lorentzConnection (a kt kx : ℝ) (v : Tangent) : Mat2 :=
  ((a + kt) * v.1 + kx * v.2) • J1

theorem lorentzConnection_zero_contorsion (a : ℝ) (v : Tangent) :
    lorentzConnection a 0 0 v = connectionForm a v := by
  simp [lorentzConnection, connectionForm]

theorem lorentzConnection_lorentz_skew (a kt kx : ℝ) (v : Tangent) :
    (lorentzConnection a kt kx v).transpose * metricMatrix +
      metricMatrix * lorentzConnection a kt kx v = 0 := by
  simpa [lorentzConnection, connectionForm] using
    connection_lorentz_skew ((a + kt) * v.1 + kx * v.2) (1, 0)

/-- Explicit spin lift; the factor and sign are checked by the adjoint theorem. -/
def spinLift (a kt kx : ℝ) (μ : Tangent →ₗ[ℝ] ℝ) (v : Tangent) : Mat2 :=
  (-(((a + kt) * v.1 + kx * v.2) / 2)) • J1 + μ v • 1

/-- In this two-dimensional spin representation the normalized trace is exactly μ. -/
theorem spinLift_trace (a kt kx : ℝ) (μ : Tangent →ₗ[ℝ] ℝ) (v : Tangent) :
    (spinLift a kt kx μ v).trace = 2 * μ v := by
  simp [spinLift, Matrix.trace, J1, Fin.sum_univ_two, two_mul]

theorem spinLift_trace_normalization (a kt kx : ℝ)
    (μ : Tangent →ₗ[ℝ] ℝ) (v : Tangent) :
    spinLift a kt kx μ v - ((spinLift a kt kx μ v).trace / 2) • 1 =
      spinLift a kt kx 0 v := by
  rw [spinLift_trace]
  simp [spinLift]

theorem spinLift_adjoint (a kt kx : ℝ) (μ : Tangent →ₗ[ℝ] ℝ)
    (v : Tangent) (u : Vec) :
    spinLift a kt kx μ v * cliffordVector u -
        cliffordVector u * spinLift a kt kx μ v =
      cliffordVector ((lorentzConnection a kt kx v).mulVec u) := by
  rw [spinLift, commutator_add_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cliffordVector, lorentzConnection, Eminus, Eplus, J1,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- Cartan's first structure expression, with both exterior slots present. -/
def vectorTorsion (a x kt kx : ℝ) (v w : Tangent) : Vec :=
  exteriorCoframe a x v w +
    (lorentzConnection a kt kx v).mulVec (coframe a x w) -
    (lorentzConnection a kt kx w).mulVec (coframe a x v)

def spinTorsion (a x kt kx : ℝ) (μ : Tangent →ₗ[ℝ] ℝ)
    (v w : Tangent) : Mat2 :=
  cliffordVector (exteriorCoframe a x v w) +
    (spinLift a kt kx μ v * cliffordVector (coframe a x w) -
      cliffordVector (coframe a x w) * spinLift a kt kx μ v) -
    (spinLift a kt kx μ w * cliffordVector (coframe a x v) -
      cliffordVector (coframe a x v) * spinLift a kt kx μ w)

/-- The concrete spin and vector Cartan expressions agree under Clifford encoding. -/
theorem spinTorsion_eq_cliffordVector (a x kt kx : ℝ)
    (μ : Tangent →ₗ[ℝ] ℝ) (v w : Tangent) :
    spinTorsion a x kt kx μ v w = cliffordVector (vectorTorsion a x kt kx v w) := by
  unfold spinTorsion
  rw [spinLift_adjoint, spinLift_adjoint]
  simp only [vectorTorsion, cliffordVector, Pi.add_apply, Pi.sub_apply,
    add_smul, sub_smul]
  abel

theorem spinTorsion_scalar_independent (a x kt kx : ℝ)
    (μ ν : Tangent →ₗ[ℝ] ℝ) (v w : Tangent) :
    spinTorsion a x kt kx μ v w = spinTorsion a x kt kx ν v w := by
  rw [spinTorsion_eq_cliffordVector, spinTorsion_eq_cliffordVector]

/-- Both torsion components are calculated, not supplied as assumptions. -/
theorem vectorTorsion_components (a x kt kx : ℝ) (v w : Tangent) :
    vectorTorsion a x kt kx v w =
      ![kt * area v w, -(lapse a x * kx) * area v w] := by
  ext i
  fin_cases i <;>
    simp [vectorTorsion, exteriorCoframe, coframe, lorentzConnection,
      dCoframeTime, (hasDerivAt_lapse a x).deriv, area, J1,
      Matrix.vecHead, Matrix.vecTail] <;> ring

theorem rindler_vectorTorsion_zero (a x : ℝ) (v w : Tangent) :
    vectorTorsion a x 0 0 v w = 0 := by
  rw [vectorTorsion_components]
  ext i
  fin_cases i <;> simp

theorem rindler_spinTorsion_zero (a x : ℝ) (μ : Tangent →ₗ[ℝ] ℝ)
    (v w : Tangent) : spinTorsion a x 0 0 μ v w = 0 := by
  rw [spinTorsion_eq_cliffordVector, rindler_vectorTorsion_zero]
  simp [cliffordVector]

/-- Off the lapse-zero boundary, both independent contorsion slots are detected. -/
theorem vectorTorsion_zero_iff (a x kt kx : ℝ) (hx : lapse a x ≠ 0) :
    (∀ v w, vectorTorsion a x kt kx v w = 0) ↔ kt = 0 ∧ kx = 0 := by
  constructor
  · intro h
    have h0 := congrFun (h (1, 0) (0, 1)) 0
    have h1 := congrFun (h (1, 0) (0, 1)) 1
    simp [vectorTorsion_components, area, hx] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    exact rindler_vectorTorsion_zero a x

theorem spinTorsion_zero_iff (a x kt kx : ℝ) (μ : Tangent →ₗ[ℝ] ℝ)
    (hx : lapse a x ≠ 0) :
    (∀ v w, spinTorsion a x kt kx μ v w = 0) ↔ kt = 0 ∧ kx = 0 := by
  rw [← vectorTorsion_zero_iff a x kt kx hx]
  constructor
  · intro h v w
    apply cliffordVector_injective
    simpa [spinTorsion_eq_cliffordVector, cliffordVector] using h v w
  · intro h v w
    rw [spinTorsion_eq_cliffordVector, h v w]
    simp [cliffordVector]

end InfoGeometry.Geometry.RindlerSpinTorsion
