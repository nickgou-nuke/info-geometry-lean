import Mathlib.LinearAlgebra.QuadraticForm.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Algebra.Module.Basic

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55ProjectiveBoundary

open Projectivization

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable (Q : QuadraticMap K V K)

/--
A point in projective space is a Null Point if any of its representatives
lie on the null cone of the quadratic form. We use `Quotient.liftOn'`
to rigorously prove this property is well-defined across the 1D ray.
-/
def IsProjectiveNull (p : Projectivization K V) : Prop :=
  Quotient.liftOn' p
    (fun v : {x : V // x ≠ 0} => Q v.val = 0)
    (by
      rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨c, hc_ne, rfl⟩
      dsimp
      apply propext
      have h_smul : Q ((c : K) • w) = (c : K) * (c : K) * Q w := QuadraticMap.map_smul Q (c : K) w
      constructor
      · intro h
        change Q ((c : K) • w) = 0 at h
        rw [h_smul] at h
        cases mul_eq_zero.mp h with
        | inl h_c2 =>
          cases mul_eq_zero.mp h_c2 with
          | inl h_c => exact False.elim (Units.ne_zero c h_c)
          | inr h_c => exact False.elim (Units.ne_zero c h_c)
        | inr h_Qw => exact h_Qw
      · intro h
        change Q ((c : K) • w) = 0
        rw [h_smul, h, mul_zero]
    )

/-- The Projective Null Quadric (The Lightcone at Infinity / Twistor Space Boundary). -/
def ProjectiveNullQuadric : Set (Projectivization K V) :=
  { p | IsProjectiveNull Q p }

variable (v_inf : V) (hv_inf : Q v_inf = 0) (hv_inf_ne : v_inf ≠ 0)
include hv_inf

/-- The distinct point at infinity, acting as the pole for the affine projection. -/
def pointAtInfinity : Projectivization K V :=
  Projectivization.mk K v_inf hv_inf_ne

/--
THEOREM: The point at infinity strictly lies on the Projective Null Quadric.
No assumptions needed; it inherits the null property intrinsically.
-/
theorem pointAtInfinity_is_null :
    pointAtInfinity v_inf hv_inf_ne ∈ ProjectiveNullQuadric Q := by
  dsimp [ProjectiveNullQuadric, IsProjectiveNull, pointAtInfinity, Projectivization.mk]
  exact hv_inf

/--
The Projective Boundary defined by the isotropic vector v_inf.
We use the native `QuadraticMap.polar` (the associated bilinear form)
to define orthogonality to infinity independently of the representative vector.
-/
def IsOnProjectiveBoundary (p : Projectivization K V) : Prop :=
  Quotient.liftOn' p
    (fun v : {x : V // x ≠ 0} => QuadraticMap.polar Q v.val v_inf = 0)
    (by
      rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨c, hc_ne, rfl⟩
      dsimp
      apply propext
      -- polar Q (c • w) v_inf = c * polar Q w v_inf
      have H : (QuadraticMap.polarBilin Q) ((c : K) • w) v_inf = (c : K) * QuadraticMap.polar Q w v_inf := by
        change (QuadraticMap.polarBilin Q) ((c : K) • w) v_inf = (c : K) * (QuadraticMap.polarBilin Q) w v_inf
        rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
      constructor
      · intro h
        change (QuadraticMap.polarBilin Q) ((c : K) • w) v_inf = 0 at h
        rw [H] at h
        exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero c)
      · intro h
        change (QuadraticMap.polarBilin Q) ((c : K) • w) v_inf = 0
        rw [H, h, mul_zero]
    )

/-- The Projective Boundary Set (The Horizon). -/
def ProjectiveBoundary : Set (Projectivization K V) :=
  { p | IsOnProjectiveBoundary Q v_inf p }

/-- The Affine Patch (Spacetime interior) is the strict complement of the boundary. -/
def AffinePatch : Set (Projectivization K V) :=
  { p | ¬ IsOnProjectiveBoundary Q v_inf p }

/--
THEOREM: The chosen point at infinity is strictly part of its own boundary.
This fundamentally prevents the affine patch from containing the pole,
guaranteeing the geometric consistency of the Conformal mapping.
-/
theorem pointAtInfinity_mem_boundary :
    pointAtInfinity v_inf hv_inf_ne ∈ ProjectiveBoundary Q v_inf := by
  dsimp [ProjectiveBoundary, IsOnProjectiveBoundary, pointAtInfinity, Projectivization.mk]
  -- Native Mathlib property: polar Q x x = 2 * Q x
  have h_polar : QuadraticMap.polar Q v_inf v_inf = 2 • Q v_inf := by
    exact QuadraticMap.polar_self Q v_inf
  rw [h_polar, hv_inf, smul_zero]

omit hv_inf in
/-- A point in the affine patch has a non-zero polar inner product with infinity. -/
theorem affinePatch_polar_ne_zero (p : Projectivization K V) (hp : p ∈ AffinePatch Q v_inf) :
    ¬ IsOnProjectiveBoundary Q v_inf p := hp

end InfoGeometry.Canonical.Cl55ProjectiveBoundary
