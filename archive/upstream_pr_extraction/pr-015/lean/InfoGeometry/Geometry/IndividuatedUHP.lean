/-
InfoGeometry/Geometry/IndividuatedUHP.lean

Individuation of the bilingual upper half-plane.

This module replaces the raw `K_positivity` field by a constructive Cartesian
sector:

  τ = X + KY

with

  X† = X,
  K† = -K,
  [X,K] = [Y,K] = 0,
  Y > 0,
  K² = -1.

It proves the exact height identity

  ⟪v, K τ v⟫ = - ⟪v, Y v⟫,

and then derives upper-half-plane positivity.

It also proves the honest real-resolvent consequence available at this level:
real shifted operators have trivial kernel. Full invertibility still requires
an explicit `IsUnit` witness.
-/

import Mathlib
import InfoGeometry.Geometry.BilingualUpperHalfPlane
import InfoGeometry.Geometry.VerifiedCauchyKernel
import InfoGeometry.Quantum.HestenesKahler
import InfoGeometry.Canonical.TomitaTakesaki

noncomputable section

namespace InfoGeometry.Geometry.IndividuatedUHP

open scoped InnerProductSpace

open InfoGeometry.Krein
open InfoGeometry.Quantum
open InfoGeometry.Geometry
open InfoGeometry.Geometry.VerifiedCauchyKernel
open ContinuousLinearMap

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-! ## 1. Phase helpers -/

/-- Pointwise form of phase-linearity. -/
theorem PhaseLinear_apply
    {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}
    {T : EndH}
    (hT : PhaseLinear D T)
    (v : H₂) :
    T (D.K v) = D.K (T v) := by
  exact PhaseLinear.map_K hT v

/-- Pointwise form of `K² = -1`. -/
theorem K_sq_apply
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (v : H₂) :
    D.K (D.K v) = -v := by
  have h :=
    congrArg (fun T : EndH => T v) D.majorana.K_sq
  simpa [ContinuousLinearMap.comp_apply] using h

/-- The canonical doubled phase axis is skew-adjoint. -/
theorem complex_i_skewAdjoint :
    star (complex_i (E := E)) = -(complex_i (E := E)) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [inner_neg_right]

/-- The Hestenes phase axis `K` is skew-adjoint. -/
theorem K_skewAdjoint
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    star D.K = -D.K := by
  rw [D.K_eq_complex_i]
  exact complex_i_skewAdjoint

/--
The real quadratic form of a skew-adjoint continuous endomorphism vanishes.
-/
lemma skew_adjoint_quad_form_zero
    (A : EndH)
    (hA : star A = -A)
    (v : H₂) :
    ⟪v, A v⟫_ℝ = 0 := by
  have hEq : ⟪v, A v⟫_ℝ = -⟪v, A v⟫_ℝ := by
    calc
      ⟪v, A v⟫_ℝ = ⟪(star A) v, v⟫_ℝ := by
        simpa using
          (ContinuousLinearMap.adjoint_inner_left (A := A) (x := v) (y := v)).symm
      _ = ⟪(-A) v, v⟫_ℝ := by
        simp [hA]
      _ = -⟪A v, v⟫_ℝ := by
        simp
      _ = -⟪v, A v⟫_ℝ := by
        simp [real_inner_comm]
  linarith

/--
If `K` is skew-adjoint, `X` is self-adjoint, and `X` commutes with `K`, then
`K ∘ X` is skew-adjoint.
-/
theorem K_comp_selfAdjoint_phaseLinear_skew
    {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}
    {X : EndH}
    (hXstar : star X = X)
    (hXK : PhaseLinear D X) :
    star (D.K.comp X) = -(D.K.comp X) := by
  change star (D.K * X) = -(D.K * X)

  have hKstar : star D.K = -D.K :=
    K_skewAdjoint (E := E) D

  have hcomm : D.K * X = X * D.K := by
    change D.K.comp X = X.comp D.K
    exact hXK.symm

  calc
    star (D.K * X)
        = star X * star D.K := by
          rw [star_mul]
    _ = X * (-D.K) := by
          rw [hXstar, hKstar]
    _ = -(X * D.K) := by
          change X.comp (-D.K) = -(X.comp D.K)
          rw [ContinuousLinearMap.comp_neg]
    _ = -(D.K * X) := by
          rw [← hcomm]

/-! ## 2. Physical Cartesian sector -/

/--
Constructively verified Cartesian sector for an upper-half-plane operator.

`τ = X + K Y`.

`X` is the real part.
`Y` is the positive height operator.

`Y_star_eq` is not needed for the diagonal positivity theorem alone, but it is
part of the intended physical sector: the height operator is an observable.
-/
structure PhysicalSectorDatum
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) where
  X : EndH
  Y : EndH

  /-- `X† = X`. -/
  X_star_eq : star X = X

  /-- `Y† = Y`. -/
  Y_star_eq : star Y = Y

  /-- `X` commutes with the phase axis. -/
  X_phaseLinear : PhaseLinear D X

  /-- `Y` commutes with the phase axis. -/
  Y_phaseLinear : PhaseLinear D Y

  /-- `Y` is strictly positive-definite. -/
  Y_pos : ∀ v : H₂, v ≠ 0 → 0 < ⟪v, Y v⟫_ℝ

namespace PhysicalSectorDatum

variable {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}
variable (P : PhysicalSectorDatum D)

/-- The bilingual operator `τ = X + KY`. -/
def tau : EndH :=
  P.X + D.K.comp P.Y

/-- Real scalar shift of the physical-sector operator. -/
def realShifted
    (ζ : ℝ) : EndH :=
  algebraMap ℝ EndH ζ - P.tau

/--
The operator `τ = X + KY` is phase-linear.
-/
theorem tau_phaseLinear :
    PhaseLinear D P.tau := by
  unfold tau
  apply PhaseLinear.add P.X_phaseLinear
  have hK : PhaseLinear D D.K := by
    unfold PhaseLinear
    rfl
  exact PhaseLinear.comp hK P.Y_phaseLinear

/--
Exact Cartesian height identity:

`⟪v, K τ v⟫ = - ⟪v, Y v⟫`.

This is the constructive replacement for a raw `K_positivity` hypothesis.
-/
theorem K_tau_quadratic_eq_neg_Y
    (v : H₂) :
    ⟪v, D.K (P.tau v)⟫_ℝ =
      -⟪v, P.Y v⟫_ℝ := by
  have hsplit :
      D.K (P.tau v) =
        D.K (P.X v) + D.K (D.K (P.Y v)) := by
    simp [tau, ContinuousLinearMap.comp_apply, ContinuousLinearMap.map_add]
  rw [hsplit]
  rw [inner_add_right]

  have hKXskew :
      star (D.K.comp P.X) = -(D.K.comp P.X) :=
    K_comp_selfAdjoint_phaseLinear_skew
      (E := E) P.X_star_eq P.X_phaseLinear

  have hKXzero :
      ⟪v, D.K (P.X v)⟫_ℝ = 0 := by
    simpa [ContinuousLinearMap.comp_apply] using
      skew_adjoint_quad_form_zero
        (E := E)
        (D.K.comp P.X)
        hKXskew
        v

  have hK2Y :
      D.K (D.K (P.Y v)) = -P.Y v :=
    K_sq_apply (E := E) D (P.Y v)

  calc
    ⟪v, D.K (P.X v)⟫_ℝ +
        ⟪v, D.K (D.K (P.Y v))⟫_ℝ
        =
      0 + ⟪v, D.K (D.K (P.Y v))⟫_ℝ := by
        rw [hKXzero]
    _ = ⟪v, -P.Y v⟫_ℝ := by
        rw [hK2Y, zero_add]
    _ = -⟪v, P.Y v⟫_ℝ := by
        rw [inner_neg_right]

/--
Native UHP height equals the positive `Y` quadratic form.
-/
theorem neg_K_tau_quadratic_eq_Y
    (v : H₂) :
    -⟪v, D.K (P.tau v)⟫_ℝ =
      ⟪v, P.Y v⟫_ℝ := by
  rw [P.K_tau_quadratic_eq_neg_Y v]
  simp

/--
The native positive height form is strictly positive on nonzero vectors.
-/
theorem positive_height
    (v : H₂)
    (hv : v ≠ 0) :
    0 < -⟪v, D.K (P.tau v)⟫_ℝ := by
  rw [P.neg_K_tau_quadratic_eq_Y v]
  exact P.Y_pos v hv

/--
The Cartesian decomposition forces UHP positivity.
-/
theorem tau_K_positivity
    (v : H₂)
    (hv : v ≠ 0) :
    ⟪v, D.K (P.tau v)⟫_ℝ < 0 := by
  rw [P.K_tau_quadratic_eq_neg_Y v]
  exact neg_lt_zero.mpr (P.Y_pos v hv)

/--
A real scalar cannot be an eigenvalue of `τ`.

This is the strongest resolvent-type statement available from positivity alone
in infinite dimension: it proves trivial kernel, not full invertibility.
-/
theorem no_real_eigenvector
    (ζ : ℝ)
    {v : H₂}
    (hEig : P.tau v = ζ • v) :
    v = 0 := by
  by_contra hv

  have hneg :
      ⟪v, D.K (P.tau v)⟫_ℝ < 0 :=
    P.tau_K_positivity v hv

  have hKzero :
      ⟪v, D.K v⟫_ℝ = 0 :=
    skew_adjoint_quad_form_zero
      (E := E)
      D.K
      (K_skewAdjoint (E := E) D)
      v

  have hheightZero :
      ⟪v, D.K (P.tau v)⟫_ℝ = 0 := by
    rw [hEig]
    calc
      ⟪v, D.K (ζ • v)⟫_ℝ
          = ⟪v, ζ • D.K v⟫_ℝ := by
            simp
      _ = 0 := by
            rw [inner_smul_right, hKzero, mul_zero]

  linarith

/--
The real shifted operator `ζ - τ` has trivial kernel.
-/
theorem realShifted_kernel_trivial
    (ζ : ℝ)
    {v : H₂}
    (hker : P.realShifted ζ v = 0) :
    v = 0 := by
  have hsub :
      ζ • v - P.tau v = 0 := by
    simpa [realShifted, ContinuousLinearMap.sub_apply] using hker

  have htau :
      P.tau v = ζ • v :=
    (eq_of_sub_eq_zero hsub).symm

  exact P.no_real_eigenvector ζ htau

/--
Alias for the real shifted operator's trivial kernel theorem.

The name emphasizes that this is resolvent-domain hygiene, not a proof that
the shifted operator is a unit in infinite dimension.
-/
theorem realShifted_resolvent_kernel_trivial
    (ζ : ℝ)
    {v : H₂}
    (hker : P.realShifted ζ v = 0) :
    v = 0 :=
  P.realShifted_kernel_trivial ζ hker

/--
The real shifted operator is injective.

This is still not invertibility in infinite dimension.
-/
theorem realShifted_injective
    (ζ : ℝ) :
    Function.Injective (P.realShifted ζ) := by
  intro v w hvw
  have hker :
      P.realShifted ζ (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hzero :
      v - w = 0 :=
    P.realShifted_kernel_trivial ζ hker
  exact sub_eq_zero.mp hzero

/--
The physical sector datum induces a genuine point in the bilingual upper
half-plane.
-/
def toUHP :
    BilingualUpperHalfPlane D where
  tau := P.tau
  phase_linear := P.tau_phaseLinear
  K_positivity := P.tau_K_positivity

end PhysicalSectorDatum

/-! ## 3. Cauchy kernel from an explicit unit witness -/

/--
In the physical sector, a real Cauchy kernel can be built once an invertibility
witness for `(ζ - τ)` is supplied.

This definition does not prove the real resolvent theorem. The Cartesian
positivity proves trivial kernel for real `ζ`; full invertibility still needs
a unit/surjectivity/Fredholm witness.
-/
def kernelInPhysicalSector
    {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}
    (P : PhysicalSectorDatum D)
    (ζ : ℝ)
    (h_invertible : IsUnit (P.realShifted ζ)) :
    VerifiedKernel (D.K : EndH) P.tau ζ :=
  let U := h_invertible.unit
  { kernelVal := ↑U⁻¹
    inv_right := by
      change P.realShifted ζ * ↑U⁻¹ = 1
      rw [← h_invertible.unit_spec]
      exact U.mul_inv
    inv_left := by
      change ↑U⁻¹ * P.realShifted ζ = 1
      rw [← h_invertible.unit_spec]
      exact U.inv_mul }

end InfoGeometry.Geometry.IndividuatedUHP
