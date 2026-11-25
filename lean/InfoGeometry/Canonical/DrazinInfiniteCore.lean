/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Algebra.Spectrum
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.DrazinExistenceBridge
import InfoGeometry.Algebraic.Fitting
import InfoGeometry.Meta.Architecture
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# InfoGeometry.Canonical.DrazinInfiniteCore

Infinite-dimensional operator core for the canonical Drazin lane.

This file separates:
- algebraic owner predicate: `InfoGeometry.Canonical.Drazin.IsDrazinInverse`,
- spectral/ascent-descent/Riesz interfaces (assumption surfaces),
- constructive finite-dimensional bridge into a Riesz-style package.
-/

namespace InfoGeometry.Canonical.DrazinInfiniteCore

open InfoGeometry.Canonical

section ResolventStability

variable {𝕂 A : Type*}
variable [NormedField 𝕂] [NormedRing A] [NormedAlgebra 𝕂 A]

/-- Pointwise resolvent stability from the second resolvent identity. The
estimate keeps the noncommutative operator order and requires both resolvents
to exist at the parameter. -/
@[rep_depth operator]
theorem norm_resolvent_sub_resolvent_le
    (a b : A) (z : 𝕂)
    (ha : z ∈ resolventSet 𝕂 a) (hb : z ∈ resolventSet 𝕂 b) :
    ‖resolvent a z - resolvent b z‖ ≤
      ‖resolvent a z‖ * ‖a - b‖ * ‖resolvent b z‖ := by
  rw [spectrum.resolvent_sub_resolvent ha hb]
  calc
    ‖resolvent a z * (a - b) * resolvent b z‖ ≤
        ‖resolvent a z * (a - b)‖ * ‖resolvent b z‖ := norm_mul_le _ _
    _ ≤ (‖resolvent a z‖ * ‖a - b‖) * ‖resolvent b z‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)

/-- A point remains in the resolvent set under a perturbation smaller than the
inverse-resolvent radius. This is the local spectral-stability step supplied
by the Neumann-series unit neighborhood; no spectral-separation conclusion is
asserted for parameters outside this radius. -/
@[rep_depth operator]
theorem mem_resolventSet_of_norm_perturbation
    [HasSummableGeomSeries A]
    (a b : A) (z : 𝕂)
    (ha : z ∈ resolventSet 𝕂 a)
    (hsmall : ‖a - b‖ < ‖resolvent a z‖⁻¹) :
    z ∈ resolventSet 𝕂 b := by
  have haUnit : IsUnit (z • (1 : A) - a) := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      (spectrum.mem_resolventSet_iff (R := 𝕂) (a := a) (r := z)).mp ha
  have hres : resolvent a z = ((haUnit.unit⁻¹ : Aˣ) : A) := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      (spectrum.resolvent_eq (R := 𝕂) (a := a) (r := z) ha)
  have hnear :
      ‖(z • (1 : A) - b) - (z • (1 : A) - a)‖ <
        ‖((haUnit.unit⁻¹ : Aˣ) : A)‖⁻¹ := by
    rw [show (z • (1 : A) - b) - (z • (1 : A) - a) = a - b by noncomm_ring,
      ← hres]
    exact hsmall
  have hbUnit : IsUnit (z • (1 : A) - b) :=
    (Units.ofNearby haUnit.unit (z • (1 : A) - b) hnear).isUnit
  have hbUnit' : IsUnit ((algebraMap 𝕂 A) z - b) := by
    convert hbUnit using 1
    rw [Algebra.algebraMap_eq_smul_one]
  exact (spectrum.mem_resolventSet_iff (R := 𝕂) (a := b) (r := z)).mpr hbUnit'

/-- Uniform Neumann-radius control transports a resolvent bound across a
perturbation. If the original resolvent is bounded by `M` on `K` and
`‖a-b‖ * M < 1`, then every point of `K` remains in the perturbed resolvent
set and the new resolvent norm is bounded by the geometric-series factor
`M / (1 - ‖a-b‖ * M)`. -/
@[rep_depth operator]
theorem resolvent_norm_bound_of_uniform_perturbation
    [HasSummableGeomSeries A] [Nontrivial A]
    (a b : A) (K : Set 𝕂) (M : ℝ)
    (ha : ∀ z ∈ K, z ∈ resolventSet 𝕂 a)
    (hboundA : ∀ z ∈ K, ‖resolvent a z‖ ≤ M)
    (hperturb : ‖a - b‖ * M < 1) :
    ∀ z ∈ K, z ∈ resolventSet 𝕂 b ∧
      ‖resolvent b z‖ ≤ M / (1 - ‖a - b‖ * M) := by
  intro z hz
  have hAz := ha z hz
  have hRpositive : 0 < ‖resolvent a z‖ := by
    have hunit : IsUnit (z • (1 : A) - a) := by
      simpa [Algebra.algebraMap_eq_smul_one] using
        (spectrum.mem_resolventSet_iff (R := 𝕂) (a := a) (r := z)).mp hAz
    have hres : resolvent a z = ((hunit.unit⁻¹ : Aˣ) : A) := by
      simpa [Algebra.algebraMap_eq_smul_one] using
        (spectrum.resolvent_eq (R := 𝕂) (a := a) (r := z) hAz)
    rw [hres]
    exact Units.norm_pos _
  have hmul : ‖a - b‖ * ‖resolvent a z‖ < 1 := by
    calc
      ‖a - b‖ * ‖resolvent a z‖ ≤ ‖a - b‖ * M :=
        mul_le_mul_of_nonneg_left (hboundA z hz) (norm_nonneg _)
      _ < 1 := by simpa [mul_comm] using hperturb
  have hsmall : ‖a - b‖ < ‖resolvent a z‖⁻¹ := by
    simpa [one_div] using (lt_div_iff₀ hRpositive).2 hmul
  have hBz : z ∈ resolventSet 𝕂 b :=
    mem_resolventSet_of_norm_perturbation a b z hAz hsmall
  have hdiff := norm_resolvent_sub_resolvent_le a b z hAz hBz
  have hnorm : ‖resolvent b z‖ ≤
      M + (M * ‖a - b‖) * ‖resolvent b z‖ := by
    calc
      ‖resolvent b z‖ =
          ‖resolvent a z - (resolvent a z - resolvent b z)‖ := by congr 1; abel
      _ ≤ ‖resolvent a z‖ + ‖resolvent a z - resolvent b z‖ := norm_sub_le _ _
      _ ≤ M + (‖resolvent a z‖ * ‖a - b‖) * ‖resolvent b z‖ := by
        exact add_le_add (hboundA z hz) hdiff
      _ ≤ M + (M * ‖a - b‖) * ‖resolvent b z‖ := by
        simpa [add_comm] using add_le_add_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hboundA z hz) (norm_nonneg (a - b)))
            (norm_nonneg (resolvent b z))) M
  have hden : 0 < 1 - ‖a - b‖ * M := by linarith
  refine ⟨hBz, ?_⟩
  rw [le_div_iff₀ hden]
  nlinarith [hnorm]

/-- Uniform resolvent bounds on a common parameter set give a uniform
Lipschitz estimate for the resolvent map as the operator varies. This is the
norm-control input needed before integrating along a separating contour. -/
@[rep_depth operator]
theorem norm_resolvent_sub_resolvent_le_of_uniform_bound
    (a b : A) (K : Set 𝕂) (M : ℝ)
    (ha : ∀ z ∈ K, z ∈ resolventSet 𝕂 a)
    (hb : ∀ z ∈ K, z ∈ resolventSet 𝕂 b)
    (hboundA : ∀ z ∈ K, ‖resolvent a z‖ ≤ M)
    (hboundB : ∀ z ∈ K, ‖resolvent b z‖ ≤ M) :
    ∀ z ∈ K, ‖resolvent a z - resolvent b z‖ ≤ M ^ 2 * ‖a - b‖ := by
  intro z hz
  have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg _) (hboundB z hz)
  calc
    ‖resolvent a z - resolvent b z‖ ≤
        ‖resolvent a z‖ * ‖a - b‖ * ‖resolvent b z‖ :=
      norm_resolvent_sub_resolvent_le a b z (ha z hz) (hb z hz)
    _ ≤ M * ‖a - b‖ * M := by
      calc
        ‖resolvent a z‖ * ‖a - b‖ * ‖resolvent b z‖ ≤
            (M * ‖a - b‖) * ‖resolvent b z‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hboundA z hz) (norm_nonneg _)) (norm_nonneg _)
        _ ≤ (M * ‖a - b‖) * M :=
          mul_le_mul_of_nonneg_left (hboundB z hz)
            (mul_nonneg hM_nonneg (norm_nonneg _))
    _ = M ^ 2 * ‖a - b‖ := by ring

end ResolventStability

section AscentDescent

variable {K V : Type*}
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Kernel stabilization at index `k` (ascent interface). -/
@[rep_depth operator]
def AscentAtZero (T : Module.End K V) (k : ℕ) : Prop :=
  InfoGeometry.Algebraic.Fitting.AscentStabilized T k

/-- Range stabilization at index `k` (descent interface). -/
@[rep_depth operator]
def DescentAtZero (T : Module.End K V) (k : ℕ) : Prop :=
  InfoGeometry.Algebraic.Fitting.DescentStabilized T k

/-- Finite ascent/descent witness at the spectral point `0`. -/
@[rep_depth operator]
structure HasFiniteAscentDescentAtZero (T : Module.End K V) where
  k : ℕ
  ascent : AscentAtZero T k
  descent : DescentAtZero T k
  D : Module.End K V
  hIsDrazin : InfoGeometry.Canonical.Drazin.IsDrazinInverse T D k

variable {T TD : Module.End K V} {k m : ℕ}

/--
Descent stabilization from a canonical Drazin witness at any step `m ≥ k`.
-/
@[rep_depth operator]
theorem descentAtZero_of_isDrazinInverse_le
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD k)
    (hm : k ≤ m) :
    DescentAtZero T m := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨TD x, ?_⟩
    have hPow : T ^ (m + 1) * TD = T ^ m :=
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.power_le hD hm
    simpa using congrArg (fun f : Module.End K V => f x) hPow
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨T x, ?_⟩
    simp [pow_succ]

/--
Ascent stabilization from a canonical Drazin witness at any step `m ≥ k`.
-/
@[rep_depth operator]
theorem ascentAtZero_of_isDrazinInverse_le
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD k)
    (hm : k ≤ m) :
    AscentAtZero T m := by
  apply le_antisymm
  · intro x hx
    change (T ^ (m + 1)) x = 0
    have hx0 : (T ^ m) x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    calc
      (T ^ (m + 1)) x = (T * T ^ m) x := by simp [pow_succ']
      _ = T ((T ^ m) x) := rfl
      _ = T 0 := by rw [hx0]
      _ = 0 := by simp
  · intro x hx
    change (T ^ m) x = 0
    have hx0 : (T ^ (m + 1)) x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    have hPow : T ^ (m + 1) * TD = T ^ m :=
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.power_le hD hm
    have hCommute : Commute T TD := InfoGeometry.Canonical.Drazin.IsDrazinInverse.comm hD
    have hPowComm : T ^ (m + 1) * TD = TD * T ^ (m + 1) :=
      (hCommute.pow_left (m + 1)).eq
    have hLeft : TD * T ^ (m + 1) = T ^ m := by
      calc
        TD * T ^ (m + 1) = T ^ (m + 1) * TD := hPowComm.symm
        _ = T ^ m := hPow
    calc
      (T ^ m) x = (TD * T ^ (m + 1)) x := by
        simpa using congrArg (fun f : Module.End K V => f x) hLeft.symm
      _ = TD ((T ^ (m + 1)) x) := rfl
      _ = TD 0 := by rw [hx0]
      _ = 0 := by simp

/-- Descent stabilization at the canonical Drazin index. -/
@[rep_depth operator]
theorem descentAtZero_of_isDrazinInverse
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD k) :
    DescentAtZero T k :=
  descentAtZero_of_isDrazinInverse_le (T := T) (TD := TD) (k := k) (m := k) hD le_rfl

/-- Ascent stabilization at the canonical Drazin index. -/
@[rep_depth operator]
theorem ascentAtZero_of_isDrazinInverse
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD k) :
    AscentAtZero T k :=
  ascentAtZero_of_isDrazinInverse_le (T := T) (TD := TD) (k := k) (m := k) hD le_rfl

/--
Canonical Drazin witness induces a finite ascent/descent witness at zero.
-/
@[rep_depth operator]
def finiteAscentDescentAtZero_of_isDrazinInverse
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD k) :
    HasFiniteAscentDescentAtZero T where
  k := k
  ascent := ascentAtZero_of_isDrazinInverse (T := T) (TD := TD) (k := k) hD
  descent := descentAtZero_of_isDrazinInverse (T := T) (TD := TD) (k := k) hD
  D := TD
  hIsDrazin := hD

/--
Finite ascent/descent interface yields a canonical Drazin witness.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_finiteAscentDescent
    (h : HasFiniteAscentDescentAtZero T) :
    ∃ k' TD', InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD' k' :=
  ⟨h.k, h.D, h.hIsDrazin⟩

/--
Compatibility readback theorem for finite ascent/descent packages that already
store a witness.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_finiteAscentDescent_readback
    (h : HasFiniteAscentDescentAtZero T) :
    ∃ k' TD', InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD' k' :=
  ⟨h.k, h.D, h.hIsDrazin⟩

/--
**The InfoGeometry.Algebraic.Fitting Transition:**
Algebraically construct the Drazin inverse from stabilized ascent and descent.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_fitting {T : Module.End K V} {k : ℕ}
    (ha : AscentAtZero T k) (hd : DescentAtZero T k) :
    ∃ TD, InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD k := by
  let Ker : Submodule K V := (T ^ k).ker
  let Ran : Submodule K V := (T ^ k).range

  have hk : IsCompl Ker Ran :=
    InfoGeometry.Algebraic.Fitting.isCompl_ker_pow_range_pow (T := T) (k := k) ha hd

  let πRan : V →ₗ[K] Ran := Ran.projectionOnto Ker hk.symm

  have hT_map_Ran : ∀ x : Ran, T x.1 ∈ Ran := by
    intro x
    rcases x.2 with ⟨y, hy⟩
    refine ⟨T y, ?_⟩
    calc
      (T ^ k) (T y) = T ((T ^ k) y) := by
        calc
          (T ^ k) (T y) = (T ^ k * T) y := by rfl
          _ = (T ^ (k + 1)) y := by simp [pow_succ]
          _ = (T * T ^ k) y := by simp [pow_succ']
          _ = T ((T ^ k) y) := by rfl
      _ = T x.1 := by simp [hy]

  let TR : Ran →ₗ[K] Ran := LinearMap.codRestrict Ran (T ∘ₗ Ran.subtype) hT_map_Ran

  have hTR_surj : Function.Surjective TR := by
    intro y
    rcases InfoGeometry.Algebraic.Fitting.surjective_on_range (T := T) (k := k) hd y.1 y.2 with
      ⟨x, hx, hTx⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    change T x = (y : V)
    exact hTx

  have hTR_inj : Function.Injective TR := by
    intro x y hxy
    apply Subtype.ext
    have hxy_val : T x.1 = T y.1 := by
      exact congrArg Subtype.val hxy
    have hT_sub : T (x.1 - y.1) = 0 := by
      calc
        T (x.1 - y.1) = T x.1 - T y.1 := by simp [map_sub]
        _ = 0 := by simp [hxy_val]
    have h_sub_eq_zero : x.1 - y.1 = 0 :=
      InfoGeometry.Algebraic.Fitting.injective_on_range (T := T) (k := k) ha hd
        (x.1 - y.1) (Submodule.sub_mem Ran x.2 y.2) hT_sub
    exact sub_eq_zero.mp h_sub_eq_zero

  let eRan : Ran ≃ₗ[K] Ran := LinearEquiv.ofBijective TR ⟨hTR_inj, hTR_surj⟩

  let D : Module.End K V := Ran.subtype ∘ₗ (eRan.symm : Ran →ₗ[K] Ran) ∘ₗ πRan
  let P : Module.End K V := Ran.subtype ∘ₗ πRan

  have hT_mul_D : T * D = P := by
    ext x
    have hright : TR (eRan.symm (πRan x)) = πRan x := by
      exact eRan.apply_symm_apply (πRan x)
    calc
      (T * D) x = T (Ran.subtype (eRan.symm (πRan x))) := by rfl
      _ = Ran.subtype (TR (eRan.symm (πRan x))) := by rfl
      _ = Ran.subtype (πRan x) := by rw [hright]
      _ = P x := by rfl

  have hpowT_apply : ∀ z : V, (T ^ k) (T z) = T ((T ^ k) z) := by
    intro z
    calc
      (T ^ k) (T z) = (T ^ k * T) z := by rfl
      _ = (T ^ (k + 1)) z := by simp [pow_succ]
      _ = (T * T ^ k) z := by simp [pow_succ']
      _ = T ((T ^ k) z) := by rfl

  have hT_map_Ker : ∀ x ∈ Ker, T x ∈ Ker := by
    intro x hx
    have hx0 : (T ^ k) x = 0 := by
      simpa [Ker, LinearMap.mem_ker] using hx
    change (T ^ k) (T x) = 0
    calc
      (T ^ k) (T x) = T ((T ^ k) x) := hpowT_apply x
      _ = 0 := by simp [hx0]

  have hD_mul_T : D * T = P := by
    ext x
    rcases Submodule.existsUnique_add_of_isCompl hk x with ⟨xK, xR, hsum, huniq⟩
    have hπK : πRan xK = 0 := by
      exact Submodule.linearProjOfIsCompl_apply_right hk.symm xK
    have hπR : πRan xR = xR := by
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm xR
    have hTK : T (xK : V) ∈ Ker := hT_map_Ker xK xK.2
    have hπTK : πRan (T (xK : V)) = 0 := by
      exact Submodule.projectionOnto_apply_of_mem_right hk.symm hTK
    have hTRxR : T (xR : V) ∈ Ran := hT_map_Ran xR
    have hπTRxR : πRan (T (xR : V)) = ⟨T xR, hTRxR⟩ := by
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm ⟨T xR, hTRxR⟩
    have hTRxR_eq : (⟨T xR, hTRxR⟩ : Ran) = TR xR := by
      apply Subtype.ext
      rfl
    have hleftInv : eRan.symm (TR xR) = xR := by
      exact eRan.symm_apply_apply xR
    have hP_on_sum : P ((xK : V) + xR) = (xR : V) := by
      unfold P
      simp [map_add, hπK, hπR]
    calc
      (D * T) x = D (T ((xK : V) + xR)) := by simp [hsum]
      _ = D (T (xK : V) + T xR) := by simp [map_add]
      _ = Ran.subtype (eRan.symm (πRan (T (xK : V) + T xR))) := by rfl
      _ = Ran.subtype (eRan.symm (πRan (T (xK : V)) + πRan (T xR))) := by
        simp [map_add]
      _ = Ran.subtype (eRan.symm (0 + ⟨T xR, hTRxR⟩)) := by rw [hπTK, hπTRxR]
      _ = Ran.subtype (eRan.symm (TR xR)) := by
        rw [hTRxR_eq]
        simp
      _ = (xR : V) := by simp [hleftInv]
      _ = P ((xK : V) + xR) := by symm; exact hP_on_sum
      _ = P x := by simp [hsum]

  have hD_mem_Ran : ∀ x : V, D x ∈ Ran := by
    intro x
    unfold D
    exact (eRan.symm (πRan x)).2

  have hD_mul_P : D * P = D := by
    ext x
    have hπPx : πRan (P x) = πRan x := by
      unfold P
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm (πRan x)
    calc
      (D * P) x = Ran.subtype (eRan.symm (πRan (P x))) := by rfl
      _ = Ran.subtype (eRan.symm (πRan x)) := by rw [hπPx]
      _ = D x := by rfl

  have hP_mul_D : P * D = D := by
    ext x
    have hπDx : πRan (D x) = ⟨D x, hD_mem_Ran x⟩ := by
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm ⟨D x, hD_mem_Ran x⟩
    calc
      (P * D) x = Ran.subtype (πRan (D x)) := by rfl
      _ = Ran.subtype ⟨D x, hD_mem_Ran x⟩ := by rw [hπDx]
      _ = D x := by rfl

  have hTk_mul_P : (T ^ k) * P = T ^ k := by
    ext x
    rcases Submodule.existsUnique_add_of_isCompl hk x with ⟨xK, xR, hsum, huniq⟩
    have hπK : πRan xK = 0 := by
      exact Submodule.linearProjOfIsCompl_apply_right hk.symm xK
    have hπR : πRan xR = xR := by
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm xR
    have hP_on_sum : P ((xK : V) + xR) = (xR : V) := by
      unfold P
      simp [map_add, hπK, hπR]
    have hTk_xK : (T ^ k) (xK : V) = 0 := xK.2
    calc
      ((T ^ k) * P) x = (T ^ k) (P ((xK : V) + xR)) := by simp [hsum]
      _ = (T ^ k) (xR : V) := by rw [hP_on_sum]
      _ = (T ^ k) ((xK : V) + xR) := by simp [map_add, hTk_xK]
      _ = (T ^ k) x := by simp [hsum]

  have hIdem : D * T * D = D := by
    calc
      D * T * D = (D * T) * D := by simp [mul_assoc]
      _ = P * D := by rw [hD_mul_T]
      _ = D := hP_mul_D

  have hComm : T * D = D * T := by
    exact hT_mul_D.trans hD_mul_T.symm

  have hPow : T ^ (k + 1) * D = T ^ k := by
    calc
      T ^ (k + 1) * D = (T ^ k) * (T * D) := by simp [pow_succ, mul_assoc]
      _ = (T ^ k) * P := by rw [hT_mul_D]
      _ = T ^ k := hTk_mul_P

  exact ⟨D, InfoGeometry.Canonical.Drazin.IsDrazinInverse.mk hComm hIdem hPow⟩

/--
Constructive finite ascent/descent bridge:
recover a Drazin witness from stabilization fields only (without using any
stored witness field from the interface package).
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_finiteAscentDescent_constructive
    (h : HasFiniteAscentDescentAtZero T) :
    ∃ k' TD', InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD' k' := by
  rcases exists_drazinInverse_of_fitting (T := T) (k := h.k) h.ascent h.descent with
    ⟨TD, hD⟩
  exact ⟨h.k, TD, hD⟩

end AscentDescent

section PolynomialPrimaryProjection

variable {𝕂 E : Type*}
variable [NormedField 𝕂]
variable [NormedAddCommGroup E] [NormedSpace 𝕂 E]

/-- The polynomially constructed projector for the `p`-primary part, given a
coprime factorization of an annihilating polynomial. -/
@[rep_depth operator]
noncomputable def primaryClusterProjector
    (T : E →L[𝕂] E) (q v : Polynomial 𝕂) : E →L[𝕂] E :=
  Polynomial.aeval T (v * q)

/-- Bézout's identity constructs a commuting idempotent separating the two
polynomially annihilated subspaces. No simplicity assumption on roots within
either factor is required. -/
@[rep_depth operator]
theorem primaryClusterProjector_laws
    (T : E →L[𝕂] E) (p q u v : Polynomial 𝕂)
    (hBezout : u * p + v * q = 1)
    (hAnnihilate : Polynomial.aeval T (p * q) = 0) :
    (primaryClusterProjector T q v) * primaryClusterProjector T q v =
        primaryClusterProjector T q v ∧
      T * primaryClusterProjector T q v = primaryClusterProjector T q v * T ∧
      Polynomial.aeval T p * primaryClusterProjector T q v = 0 ∧
      Polynomial.aeval T q * (1 - primaryClusterProjector T q v) = 0 ∧
      (∀ x : E, Polynomial.aeval T p x = 0 → primaryClusterProjector T q v x = x) ∧
      (∀ x : E, Polynomial.aeval T q x = 0 → primaryClusterProjector T q v x = 0) := by
  let f : E →L[𝕂] E := Polynomial.aeval T p
  let g : E →L[𝕂] E := Polynomial.aeval T q
  let a : E →L[𝕂] E := Polynomial.aeval T u
  let b : E →L[𝕂] E := Polynomial.aeval T v
  let P : E →L[𝕂] E := b * g
  have hB : a * f + b * g = 1 := by
    have h := congrArg (Polynomial.aeval T) hBezout
    simpa [map_add, map_mul] using h
  have hFG : f * g = 0 := by
    simpa [map_mul, f, g] using hAnnihilate
  have hComm (r s : Polynomial 𝕂) :
      Polynomial.aeval T r * Polynomial.aeval T s =
        Polynomial.aeval T s * Polynomial.aeval T r := by
    rw [← map_mul, ← map_mul]
    exact congrArg (Polynomial.aeval T) (mul_comm r s)
  have hGF : g * f = 0 := by
    calc
      g * f = f * g := hComm q p
      _ = 0 := hFG
  have hPCommF : P * f = f * P := by
    dsimp [P, f, b, g]
    simpa [map_mul] using hComm (v * q) p
  have hPCommG : P * g = g * P := by
    dsimp [P, g, b]
    simpa [map_mul] using hComm (v * q) q
  have hfp : f * P = 0 := by
    calc
      f * P = f * (b * g) := rfl
      _ = (f * b) * g := by noncomm_ring
      _ = (b * f) * g := by rw [hComm p v]
      _ = b * (f * g) := by noncomm_ring
      _ = 0 := by rw [hFG]; simp
  have hPexpr : P = 1 - a * f := by
    dsimp [P]
    rw [← hB]
    noncomm_ring
  have hafP : (a * f) * P = 0 := by
    calc
      (a * f) * P = a * (f * P) := by noncomm_ring
      _ = 0 := by rw [hfp]; simp
  have hIdem : P * P = P := by
    calc
      P * P = (1 - a * f) * P := by rw [hPexpr]
      _ = P := by noncomm_ring [hafP]
  have hTf : T * P = P * T := by
    have h := hComm Polynomial.X (v * q)
    simpa [P, Polynomial.aeval_X, map_mul] using h
  have hgcomp : g * (1 - P) = 0 := by
    calc
      g * (1 - P) = g * (a * f) := by rw [hPexpr]; noncomm_ring
      _ = 0 := by
        calc
          g * (a * f) = (g * a) * f := by noncomm_ring
          _ = (a * g) * f := by rw [hComm q u]
          _ = a * (g * f) := by noncomm_ring
          _ = 0 := by rw [hGF]; simp
  have hFix : ∀ x : E, f x = 0 → P x = x := by
    intro x hx
    rw [hPexpr]
    simp [hx]
  have hKill : ∀ x : E, g x = 0 → P x = 0 := by
    intro x hx
    have hBezoutX := congrArg (fun L : E →L[𝕂] E => L x) hB
    have haxf : a (f x) = x := by simpa [hx] using hBezoutX
    rw [hPexpr]
    change x - a (f x) = 0
    rw [haxf]
    simp
  simpa [P, primaryClusterProjector, f, g] using
    (show P * P = P ∧ T * P = P * T ∧ f * P = 0 ∧ g * (1 - P) = 0 ∧
      (∀ x : E, f x = 0 → P x = x) ∧ (∀ x : E, g x = 0 → P x = 0) from
      ⟨hIdem, hTf, hfp, hgcomp, hFix, hKill⟩)

/-- The polynomial primary projector has range exactly the `p(T)`-annihilated
subspace. This identifies the primary component itself, including generalized
eigenvectors when `p` has repeated roots. -/
@[rep_depth operator]
theorem primaryClusterProjector_range_eq_ker
    (T : E →L[𝕂] E) (p q u v : Polynomial 𝕂)
    (hBezout : u * p + v * q = 1)
    (hAnnihilate : Polynomial.aeval T (p * q) = 0) :
    LinearMap.range (primaryClusterProjector T q v).toLinearMap =
      LinearMap.ker (Polynomial.aeval T p).toLinearMap := by
  obtain ⟨_, _, hpP, _, hpFix, _⟩ :=
    primaryClusterProjector_laws T p q u v hBezout hAnnihilate
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, rfl⟩
    change (Polynomial.aeval T p) ((primaryClusterProjector T q v) y) = 0
    exact congrArg (fun L : E →L[𝕂] E => L y) hpP
  · intro x hx
    change (Polynomial.aeval T p) x = 0 at hx
    refine ⟨x, ?_⟩
    change (primaryClusterProjector T q v) x = x
    exact hpFix x hx

/-- The complementary primary projector has range exactly the `q(T)`-annihilated
subspace. No diagonalizability assumption is used. -/
@[rep_depth operator]
theorem primaryClusterComplement_range_eq_ker
    (T : E →L[𝕂] E) (p q u v : Polynomial 𝕂)
    (hBezout : u * p + v * q = 1)
    (hAnnihilate : Polynomial.aeval T (p * q) = 0) :
    LinearMap.range (1 - primaryClusterProjector T q v).toLinearMap =
      LinearMap.ker (Polynomial.aeval T q).toLinearMap := by
  obtain ⟨_, _, _, hqComp, _, hqKill⟩ :=
    primaryClusterProjector_laws T p q u v hBezout hAnnihilate
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, rfl⟩
    change (Polynomial.aeval T q) ((1 - primaryClusterProjector T q v) y) = 0
    exact congrArg (fun L : E →L[𝕂] E => L y) hqComp
  · intro x hx
    change (Polynomial.aeval T q) x = 0 at hx
    have hPx : (primaryClusterProjector T q v) x = 0 := hqKill x hx
    refine ⟨x, ?_⟩
    change x - (primaryClusterProjector T q v) x = x
    rw [hPx, sub_zero]

/-- In finite dimension, the two coprime polynomial primary components split
the full dimension. Repeated roots and their generalized eigenvectors remain
inside the corresponding kernel; no eigenbasis or semisimplicity hypothesis
is used. -/
@[rep_depth operator]
theorem primaryCluster_finrank_add
    [FiniteDimensional 𝕂 E]
    (T : E →L[𝕂] E) (p q u v : Polynomial 𝕂)
    (hBezout : u * p + v * q = 1)
    (hAnnihilate : Polynomial.aeval T (p * q) = 0) :
    Module.finrank 𝕂 (Polynomial.aeval T p).ker +
      Module.finrank 𝕂 (Polynomial.aeval T q).ker = Module.finrank 𝕂 E := by
  let P := primaryClusterProjector T q v
  let Q : E →L[𝕂] E := 1 - P
  let U : Submodule 𝕂 E := LinearMap.range P.toLinearMap
  let W : Submodule 𝕂 E := LinearMap.range Q.toLinearMap
  have hIdem : P * P = P :=
    (primaryClusterProjector_laws T p q u v hBezout hAnnihilate).1
  have hPQ : P * Q = 0 := by
    dsimp [Q]
    noncomm_ring [hIdem]
  have hDisjoint : Disjoint U W := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    rcases hx with ⟨hxU, hxW⟩
    rcases hxU with ⟨y, rfl⟩
    rcases hxW with ⟨z, hz⟩
    have hPy : P (P y) = P y := by
      have h := congrArg (fun L : E →L[𝕂] E => L y) hIdem
      simpa using h
    have hPzero : P (Q z) = 0 := by
      have h := congrArg (fun L : E →L[𝕂] E => L z) hPQ
      simpa using h
    have hEq : P y = Q z := hz.symm
    have : P y = 0 := by
      calc
        P y = P (P y) := hPy.symm
        _ = P (Q z) := by rw [hEq]
        _ = 0 := hPzero
    simp [this]
  have hsum : U ⊔ W = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨P x, ?_, Q x, ?_, ?_⟩
    · exact ⟨x, rfl⟩
    · exact ⟨x, rfl⟩
    · simp [Q]
  have hCompl : IsCompl U W := ⟨hDisjoint, codisjoint_iff.mpr hsum⟩
  rw [← primaryClusterProjector_range_eq_ker T p q u v hBezout hAnnihilate,
    ← primaryClusterComplement_range_eq_ker T p q u v hBezout hAnnihilate]
  change Module.finrank 𝕂 U + Module.finrank 𝕂 W = Module.finrank 𝕂 E
  exact Submodule.finrank_add_eq_of_isCompl hCompl

/-- The Bézout projector gives the unique primary decomposition of every vector:
the first component is killed by `p(T)`, and the second by `q(T)`. -/
@[rep_depth operator]
theorem primaryClusterProjector_unique_decomposition
    (T : E →L[𝕂] E) (p q u v : Polynomial 𝕂)
    (hBezout : u * p + v * q = 1)
    (hAnnihilate : Polynomial.aeval T (p * q) = 0) (x : E) :
    ∃! yz : E × E,
      Polynomial.aeval T p yz.1 = 0 ∧
      Polynomial.aeval T q yz.2 = 0 ∧
      x = yz.1 + yz.2 := by
  let P := primaryClusterProjector T q v
  obtain ⟨_, _, hpP, hqComp, hpFix, hqKill⟩ :=
    primaryClusterProjector_laws T p q u v hBezout hAnnihilate
  refine ⟨(P x, (1 - P) x), ?_, ?_⟩
  · constructor
    · have h := congrArg (fun L : E →L[𝕂] E => L x) hpP
      simpa [P, primaryClusterProjector] using h
    · constructor
      · have h := congrArg (fun L : E →L[𝕂] E => L x) hqComp
        simpa [P, primaryClusterProjector] using h
      · simp
  · intro yz hyz
    rcases yz with ⟨y, z⟩
    rcases hyz with ⟨hy, hz, hsum⟩
    have hPy : P y = y := hpFix y (by simpa [P, primaryClusterProjector] using hy)
    have hPz : P z = 0 := hqKill z (by simpa [P, primaryClusterProjector] using hz)
    have hPx : P x = y := by
      rw [hsum]
      simp [hPy, hPz]
    have hCompX : (1 - P) x = z := by
      rw [hsum]
      simp [hPy, hPz]
    apply Prod.ext
    · exact hPx.symm
    · exact hCompX.symm

end PolynomialPrimaryProjection

section SpectralInterfaces

variable {𝕂 E : Type*}
variable [NormedField 𝕂]
variable [NormedAddCommGroup E] [NormedSpace 𝕂 E]

/--
Topological isolation interface for the spectral point `0`.

This is intentionally stated as neighborhood isolation to stay lightweight.
-/
@[rep_depth operator]
def ZeroIsolatedInSpectrum (T : E →L[𝕂] E) : Prop :=
  ∃ U : Set 𝕂, IsOpen U ∧ (0 : 𝕂) ∈ U ∧
    ∀ z : 𝕂, z ∈ U → z ∈ spectrum 𝕂 T → z = 0

/--
Riesz-style decomposition interface at `0` for a bounded operator.
-/
@[rep_depth operator]
structure HasClassicalRieszDecompositionAtZero (T : E →L[𝕂] E) where
  P : E →L[𝕂] E
  P_idempotent : P * P = P
  PT_comm : T * P = P * T
  k : ℕ
  D : E →L[𝕂] E
  hIsDrazin : InfoGeometry.Canonical.Drazin.IsDrazinInverse T D k
  hP : P = InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection T D

/--
Generalized Riesz-style interface at `0` for a bounded operator.

This is the generalized Drazin-style lane: the regular part is invertible on
`P`, while the complementary operator has spectral radius zero.  The separate
`ConstructiveRieszDecompositionAtZero` below retains its finite-nilpotence
condition, which is stronger and belongs to the classical finite-index lane.
-/
@[rep_depth operator]
def QuasinilpotentOnDefect
    (T P : E →L[𝕂] E) : Prop :=
  spectralRadius 𝕂 (T * (1 - P)) = 0

/-- Finite-index nilpotence of the complementary operator. -/
@[rep_depth operator]
def NilpotentOnDefect
    (T P : E →L[𝕂] E) : Prop :=
  ∃ k : ℕ, T ^ k * (1 - P) = 0

/-- A finite-nilpotent defect has spectral radius zero when the projector commutes with `T`. -/
@[rep_depth operator]
theorem quasinilpotentOnDefect_of_nilpotentOnDefect
    {T P : E →L[𝕂] E}
    (hP : P * P = P) (hTP : T * P = P * T)
    (hNil : NilpotentOnDefect T P) :
    QuasinilpotentOnDefect T P := by
  rcases hNil with ⟨k, hk⟩
  let Q : E →L[𝕂] E := 1 - P
  let A : E →L[𝕂] E := T * Q
  have hQid : Q * Q = Q := by
    dsimp [Q]
    noncomm_ring [hP]
  have hQT : Q * T = T * Q := by
    dsimp [Q]
    noncomm_ring [hTP]
  have hpow (n : ℕ) : A ^ (n + 1) = T ^ (n + 1) * Q := by
    induction n with
    | zero => simp [A, Q]
    | succ n ih =>
        calc
          A ^ (Nat.succ n + 1) = A ^ (n + 1) * A := by
            rw [show Nat.succ n + 1 = (n + 1) + 1 by omega, pow_succ]
          _ = (T ^ (n + 1) * Q) * A := by rw [ih]
          _ = T ^ (n + 1) * (Q * T) * Q := by
            dsimp [A]
            noncomm_ring
          _ = T ^ (n + 1) * (T * Q) * Q := by rw [hQT]
          _ = (T ^ (n + 1) * T) * (Q * Q) := by noncomm_ring
          _ = T ^ (n + 2) * Q := by
            rw [hQid]
            have hpowT : T ^ (n + 2) = T ^ (n + 1) * T := by
              rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
            rw [hpowT]
  have hAzero : A ^ (k + 1) = 0 := by
    rw [hpow k]
    have hkQ : T ^ k * Q = 0 := by simpa [Q] using hk
    calc
      T ^ (k + 1) * Q = T * (T ^ k * Q) := by
        rw [show k + 1 = Nat.succ k by omega, pow_succ']
        noncomm_ring
      _ = 0 := by rw [hkQ]; simp
  have hRadius :
      (spectralRadius 𝕂 A) ^ (k + 1) ≤ spectralRadius 𝕂 (A ^ (k + 1)) :=
    spectrum.spectralRadius_pow_le A (k + 1) (by omega)
  rw [hAzero, spectrum.spectralRadius_zero] at hRadius
  have hRadiusPow : (spectralRadius 𝕂 A) ^ (k + 1) = 0 :=
    le_antisymm hRadius bot_le
  exact (pow_eq_zero_iff (by omega : k + 1 ≠ 0)).mp hRadiusPow

@[rep_depth operator]
structure HasGeneralizedRieszDecompositionAtZero (T : E →L[𝕂] E) where
  P : E →L[𝕂] E
  P_idempotent : P * P = P
  PT_comm : T * P = P * T
  S : E →L[𝕂] E
  left_inverse_on_regular :
    (T * P) * S = P
  right_inverse_on_regular :
    S * (T * P) = P
  inverse_supported_on_regular_left : S * P = S
  inverse_supported_on_regular_right : P * S = S
  quasinilpotent_on_defect : QuasinilpotentOnDefect T P

/-- A quasinilpotent operator is the pure-defect case of generalized Riesz
decomposition: the regular projector and its supported inverse are zero. -/
@[rep_depth operator]
def generalizedRiesz_of_quasinilpotent
    {T : E →L[𝕂] E} (hT : spectralRadius 𝕂 T = 0) :
    HasGeneralizedRieszDecompositionAtZero (𝕂 := 𝕂) T where
  P := 0
  P_idempotent := by simp
  PT_comm := by simp
  S := 0
  left_inverse_on_regular := by simp
  right_inverse_on_regular := by simp
  inverse_supported_on_regular_left := by simp
  inverse_supported_on_regular_right := by simp
  quasinilpotent_on_defect := by
    simpa [QuasinilpotentOnDefect] using hT

/-- The generalized Riesz data determine the usual generalized-Drazin laws:
the regular inverse is two-sided on the regular corner, while the residual
`T - T²S` is quasinilpotent on the whole operator space. -/
@[rep_depth operator]
theorem generalizedDrazin_relations_of_riesz
    {T : E →L[𝕂] E} (h : HasGeneralizedRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    T * h.S = h.P ∧ h.S * T = h.P ∧ h.S * T * h.S = h.S ∧
      spectralRadius 𝕂 (T - T * T * h.S) = 0 := by
  have hTS : T * h.S = h.P := by
    calc
      T * h.S = T * (h.P * h.S) := by rw [h.inverse_supported_on_regular_right]
      _ = (T * h.P) * h.S := by noncomm_ring
      _ = h.P := h.left_inverse_on_regular
  have hST : h.S * T = h.P := by
    calc
      h.S * T = (h.S * h.P) * T := by rw [h.inverse_supported_on_regular_left]
      _ = h.S * (h.P * T) := by noncomm_ring
      _ = h.S * (T * h.P) := by rw [h.PT_comm]
      _ = h.P := h.right_inverse_on_regular
  have hSTS : h.S * T * h.S = h.S := by
    calc
      h.S * T * h.S = h.P * h.S := by rw [hST]
      _ = h.S := h.inverse_supported_on_regular_right
  have hResidual : T - T * T * h.S = T * (1 - h.P) := by
    calc
      T - T * T * h.S = T - T * (T * h.S) := by noncomm_ring
      _ = T - T * h.P := by rw [hTS]
      _ = T * (1 - h.P) := by noncomm_ring
  exact ⟨hTS, hST, hSTS, by rw [hResidual]; exact h.quasinilpotent_on_defect⟩

/--
Witness-free constructive Riesz decomposition surface at `0`.

This owner carries only projector/splitting data and does not store a
preconstructed Drazin witness.
-/
@[rep_depth operator]
structure ConstructiveRieszDecompositionAtZero (T : E →L[𝕂] E) where
  k : ℕ
  P : E →L[𝕂] E
  P_idempotent : P * P = P
  PT_comm : T * P = P * T
  S : E →L[𝕂] E
  left_inverse_on_regular : S * T = P
  right_inverse_on_regular : T * S = P
  S_supported_on_regular_left : S * P = S
  S_supported_on_regular_right : P * S = S
  nilpotent_on_complement : T ^ k * (1 - P) = 0

/-- A polynomial primary split with complementary factor `X^k` constructs a
finite Drazin/Riesz decomposition. The inverse on the regular primary part is
the polynomial `c(T)` supplied by `c * X + d * p = 1`; the complementary part
is annihilated by `T^k`. -/
@[rep_depth operator]
noncomputable def constructiveRiesz_of_polynomial_primary
    (T : E →L[𝕂] E) (k : ℕ) (p u v c d : Polynomial 𝕂)
    (hSplit : u * p + v * (Polynomial.X : Polynomial 𝕂) ^ k = 1)
    (hAnnihilate : Polynomial.aeval T (p * (Polynomial.X : Polynomial 𝕂) ^ k) = 0)
    (hInverse : c * (Polynomial.X : Polynomial 𝕂) + d * p = 1) :
    ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T := by
  let P := primaryClusterProjector T ((Polynomial.X : Polynomial 𝕂) ^ k) v
  let C : E →L[𝕂] E := Polynomial.aeval T c
  let F : E →L[𝕂] E := Polynomial.aeval T p
  obtain ⟨hPid, hPT, hFP, hQComp, _, _⟩ :=
    primaryClusterProjector_laws T p ((Polynomial.X : Polynomial 𝕂) ^ k) u v hSplit hAnnihilate
  have hXpow : Polynomial.aeval T ((Polynomial.X : Polynomial 𝕂) ^ k) = T ^ k := by
    simp [Polynomial.aeval_X_pow]
  have hInverseEval : C * T + Polynomial.aeval T d * F = 1 := by
    have h := congrArg (Polynomial.aeval T) hInverse
    simpa [C, F, map_add, map_mul, Polynomial.aeval_X] using h
  have hLocalInverse : (C * T) * P = P := by
    have h := congrArg (fun L : E →L[𝕂] E => L * P) hInverseEval
    have hCross : (Polynomial.aeval T d * F) * P = 0 := by
      calc
        (Polynomial.aeval T d * F) * P = Polynomial.aeval T d * (F * P) := by
          noncomm_ring
        _ = 0 := by rw [hFP]; simp
    simpa [add_mul, hCross] using h
  have hTC : T * C = C * T := by
    have h := congrArg (Polynomial.aeval T)
      (mul_comm (Polynomial.X : Polynomial 𝕂) c)
    simpa [C, map_mul, Polynomial.aeval_X] using h
  have hPC : P * C = C * P := by
    have h := congrArg (Polynomial.aeval T)
      (mul_comm (v * Polynomial.X ^ k) c)
    simpa [P, C, primaryClusterProjector, map_mul] using h
  have hPidem : P * P = P := by simpa [P] using hPid
  refine
    { k := k
      P := P
      P_idempotent := ?_
      PT_comm := ?_
      S := C * P
      left_inverse_on_regular := ?_
      right_inverse_on_regular := ?_
      S_supported_on_regular_left := ?_
      S_supported_on_regular_right := ?_
      nilpotent_on_complement := ?_ }
  · exact hPidem
  · exact hPT
  · calc
      (C * P) * T = C * (P * T) := by noncomm_ring
      _ = C * (T * P) := by rw [hPT]
      _ = (C * T) * P := by noncomm_ring
      _ = P := hLocalInverse
  · calc
      T * (C * P) = (T * C) * P := by noncomm_ring
      _ = (C * T) * P := by rw [hTC]
      _ = P := hLocalInverse
  · calc
      (C * P) * P = C * (P * P) := by noncomm_ring
      _ = C * P := by rw [hPidem]
  · calc
      P * (C * P) = (P * C) * P := by noncomm_ring
      _ = (C * P) * P := by rw [hPC]
      _ = C * (P * P) := by noncomm_ring
      _ = C * P := by rw [hPidem]
  · simpa [hXpow] using hQComp

/-- A finite-nilpotent constructive split is a special case of the generalized split. -/
@[rep_depth operator]
def generalizedRiesz_of_constructiveRiesz
    {T : E →L[𝕂] E}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    HasGeneralizedRieszDecompositionAtZero (𝕂 := 𝕂) T where
  P := hR.P
  P_idempotent := hR.P_idempotent
  PT_comm := hR.PT_comm
  S := hR.S
  left_inverse_on_regular := by
    calc
      (T * hR.P) * hR.S = T * (hR.P * hR.S) := by noncomm_ring
      _ = T * hR.S := by rw [hR.S_supported_on_regular_right]
      _ = hR.P := hR.right_inverse_on_regular
  right_inverse_on_regular := by
    calc
      hR.S * (T * hR.P) = hR.S * (hR.P * T) := by rw [hR.PT_comm]
      _ = (hR.S * hR.P) * T := by rw [← mul_assoc]
      _ = hR.S * T := by rw [hR.S_supported_on_regular_left]
      _ = hR.P := hR.left_inverse_on_regular
  inverse_supported_on_regular_left := hR.S_supported_on_regular_left
  inverse_supported_on_regular_right := hR.S_supported_on_regular_right
  quasinilpotent_on_defect :=
    quasinilpotentOnDefect_of_nilpotentOnDefect hR.P_idempotent hR.PT_comm
      ⟨hR.k, hR.nilpotent_on_complement⟩
/--
Foundational Drazin data: the inverse is not primitive, but is carried together
with the projector and defect-annihilation laws that define it.
-/
@[rep_depth operator]
structure ConstructiveDrazinData (T : E →L[𝕂] E) where
  k : ℕ
  projector : E →L[𝕂] E
  inverse : E →L[𝕂] E
  projector_idempotent : projector * projector = projector
  projector_comm : T * projector = projector * T
  left_inverse_on_regular : inverse * T = projector
  right_inverse_on_regular : T * inverse = projector
  inverse_supported_on_regular_left : inverse * projector = inverse
  inverse_supported_on_regular_right : projector * inverse = inverse
  nilpotent_on_defect : T ^ k * (1 - projector) = 0

/--
A constructive Riesz decomposition canonically induces the foundational Drazin
package.
-/
@[rep_depth operator]
def constructiveDrazinData_of_constructiveRieszDecompositionAtZero
    {T : E →L[𝕂] E}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    ConstructiveDrazinData (𝕂 := 𝕂) T where
  k := hR.k
  projector := hR.P
  inverse := hR.S
  projector_idempotent := hR.P_idempotent
  projector_comm := hR.PT_comm
  left_inverse_on_regular := hR.left_inverse_on_regular
  right_inverse_on_regular := hR.right_inverse_on_regular
  inverse_supported_on_regular_left := hR.S_supported_on_regular_left
  inverse_supported_on_regular_right := hR.S_supported_on_regular_right
  nilpotent_on_defect := hR.nilpotent_on_complement

/-- Recover constructive Riesz data from the foundational Drazin package. -/
@[rep_depth operator]
def constructiveRieszDecompositionAtZero_of_constructiveDrazinData
    {T : E →L[𝕂] E}
    (h : ConstructiveDrazinData (𝕂 := 𝕂) T) :
    ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T where
  k := h.k
  P := h.projector
  P_idempotent := h.projector_idempotent
  PT_comm := h.projector_comm
  S := h.inverse
  left_inverse_on_regular := h.left_inverse_on_regular
  right_inverse_on_regular := h.right_inverse_on_regular
  S_supported_on_regular_left := h.inverse_supported_on_regular_left
  S_supported_on_regular_right := h.inverse_supported_on_regular_right
  nilpotent_on_complement := h.nilpotent_on_defect

/-- Candidate Drazin inverse extracted from constructive Riesz data. -/
@[rep_depth operator]
def constructiveDrazinCandidate
    {T : E →L[𝕂] E}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    E →L[𝕂] E :=
  hR.S

/-- Candidate commutes with the base operator. -/
@[rep_depth operator]
theorem constructiveDrazinCandidate_comm
    {T : E →L[𝕂] E}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    T * constructiveDrazinCandidate hR = constructiveDrazinCandidate hR * T := by
  calc
    T * constructiveDrazinCandidate hR = T * hR.S := rfl
    _ = hR.P := hR.right_inverse_on_regular
    _ = hR.S * T := hR.left_inverse_on_regular.symm
    _ = constructiveDrazinCandidate hR * T := rfl

/-- Candidate satisfies the inner Drazin law `D * T * D = D`. -/
@[rep_depth operator]
theorem constructiveDrazinCandidate_inner
    {T : E →L[𝕂] E}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    constructiveDrazinCandidate hR * T * constructiveDrazinCandidate hR
      = constructiveDrazinCandidate hR := by
  calc
    constructiveDrazinCandidate hR * T * constructiveDrazinCandidate hR
        = (hR.S * T) * hR.S := by
            simp [constructiveDrazinCandidate, mul_assoc]
    _ = hR.P * hR.S := by rw [hR.left_inverse_on_regular]
    _ = hR.S := hR.S_supported_on_regular_right
    _ = constructiveDrazinCandidate hR := rfl

/-- Candidate satisfies the finite-index Drazin power law. -/
@[rep_depth operator]
theorem constructiveDrazinCandidate_power
    {T : E →L[𝕂] E}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    T ^ (hR.k + 1) * constructiveDrazinCandidate hR = T ^ hR.k := by
  calc
    T ^ (hR.k + 1) * constructiveDrazinCandidate hR
        = T ^ hR.k * (T * hR.S) := by
            simp [constructiveDrazinCandidate, pow_succ, mul_assoc]
    _ = T ^ hR.k * hR.P := by rw [hR.right_inverse_on_regular]
    _ = T ^ hR.k * (1 - (1 - hR.P)) := by simp
    _ = T ^ hR.k * 1 - T ^ hR.k * (1 - hR.P) := by rw [mul_sub]
    _ = T ^ hR.k - 0 := by rw [mul_one, hR.nilpotent_on_complement]
    _ = T ^ hR.k := by simp

/--
Foundational constructive Drazin data already carries a canonical Drazin witness
for its stored inverse, without first re-expanding through the Riesz package.
-/
@[rep_depth operator]
theorem isDrazinInverse_of_constructiveDrazinData
    {T : E →L[𝕂] E}
    (h : ConstructiveDrazinData (𝕂 := 𝕂) T) :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse T h.inverse h.k := by
  refine InfoGeometry.Canonical.Drazin.IsDrazinInverse.mk ?_ ?_ ?_
  · calc
      T * h.inverse = h.projector := h.right_inverse_on_regular
      _ = h.inverse * T := h.left_inverse_on_regular.symm
  · calc
      h.inverse * T * h.inverse = h.projector * h.inverse := by
          rw [h.left_inverse_on_regular]
      _ = h.inverse := h.inverse_supported_on_regular_right
  · calc
      T ^ (h.k + 1) * h.inverse = T ^ h.k * (T * h.inverse) := by
          simp [pow_succ, mul_assoc]
      _ = T ^ h.k * h.projector := by rw [h.right_inverse_on_regular]
      _ = T ^ h.k * (1 - (1 - h.projector)) := by simp
      _ = T ^ h.k * 1 - T ^ h.k * (1 - h.projector) := by rw [mul_sub]
      _ = T ^ h.k - 0 := by rw [mul_one, h.nilpotent_on_defect]
      _ = T ^ h.k := by simp

/--
Foundational constructive Drazin data yields a canonical existential Drazin
witness without first converting to a constructive Riesz package.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_constructiveDrazinData
    {T : E →L[𝕂] E}
    (h : ConstructiveDrazinData (𝕂 := 𝕂) T) :
    ∃ k TD, InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD k :=
  ⟨h.k, h.inverse, isDrazinInverse_of_constructiveDrazinData (𝕂 := 𝕂) h⟩

/--
Constructive Riesz decomposition at `0` yields a canonical Drazin witness.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_constructiveRieszDecompositionAtZero
    {T : E →L[𝕂] E}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    ∃ k TD, InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD k := by
  refine ⟨hR.k, constructiveDrazinCandidate hR, ?_⟩
  exact InfoGeometry.Canonical.Drazin.IsDrazinInverse.mk
    (constructiveDrazinCandidate_comm (hR := hR))
    (constructiveDrazinCandidate_inner (hR := hR))
    (constructiveDrazinCandidate_power (hR := hR))

/--
Compatibility adapter: recover constructive Riesz data from the legacy
classical witness-bearing interface.
-/
@[rep_depth operator]
def constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
    {T : E →L[𝕂] E}
    (h : HasClassicalRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T where
  k := h.k
  P := h.P
  P_idempotent := h.P_idempotent
  PT_comm := h.PT_comm
  S := h.D
  left_inverse_on_regular := by
    calc
      h.D * T = T * h.D := h.hIsDrazin.comm.symm
      _ = InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection T h.D := by rfl
      _ = h.P := h.hP.symm
  right_inverse_on_regular := by
    calc
      T * h.D = InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection T h.D := by rfl
      _ = h.P := h.hP.symm
  S_supported_on_regular_left := by
    calc
      h.D * h.P = h.D * InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection T h.D := by rw [h.hP]
      _ = h.D := by
            simpa [InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection, mul_assoc] using
              h.hIsDrazin.idempotent
  S_supported_on_regular_right := by
    calc
      h.P * h.D = InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection T h.D * h.D := by rw [h.hP]
      _ = h.D * InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection T h.D := by
            simpa using InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_comm (h := h.hIsDrazin)
      _ = h.D := by
            simpa [InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection, mul_assoc] using
              h.hIsDrazin.idempotent
  nilpotent_on_complement := by
    calc
      T ^ h.k * (1 - h.P)
          = T ^ h.k * (1 - InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection T h.D) := by rw [h.hP]
      _ = T ^ h.k * (1 - T * h.D) := by rfl
      _ = T ^ h.k - T ^ h.k * (T * h.D) := by rw [mul_sub, mul_one]
      _ = T ^ h.k - T ^ (h.k + 1) * h.D := by rw [pow_succ, mul_assoc]
      _ = T ^ h.k - T ^ h.k := by rw [h.hIsDrazin.power]
      _ = 0 := by simp

/--
Bundle of spectral interfaces commonly used for infinite-dimensional Drazin
existence statements.
-/
@[rep_depth operator]
structure DrazinInfiniteAssumptions (T : E →L[𝕂] E) where
  finite_ascent_descent : HasFiniteAscentDescentAtZero (K := 𝕂) (V := E) T.toLinearMap
  zero_isolated_spectrum : ZeroIsolatedInSpectrum (𝕂 := 𝕂) T
  classical_riesz : HasClassicalRieszDecompositionAtZero (𝕂 := 𝕂) T
  generalized_riesz : HasGeneralizedRieszDecompositionAtZero (𝕂 := 𝕂) T

/--
The bundled infinite-dimensional Drazin assumptions already carry a classical
Riesz packet, so they recover the witness-free constructive Riesz surface
without reintroducing a separate `HasClassicalRieszDecompositionAtZero`
hypothesis.
-/
@[rep_depth operator]
def constructiveRieszDecompositionAtZero_of_drazinInfiniteAssumptions
    {T : E →L[𝕂] E}
    (h : DrazinInfiniteAssumptions (𝕂 := 𝕂) T) :
    ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T :=
  constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
    (𝕂 := 𝕂) h.classical_riesz

/--
The bundled infinite-dimensional Drazin assumptions already determine the
canonical Drazin witness attached to their classical Riesz field.
-/
@[rep_depth operator]
theorem isDrazinInverse_of_drazinInfiniteAssumptions
    {T : E →L[𝕂] E}
    (h : DrazinInfiniteAssumptions (𝕂 := 𝕂) T) :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse T h.classical_riesz.D h.classical_riesz.k :=
  h.classical_riesz.hIsDrazin

/--
Bundled infinite-dimensional Drazin assumptions yield a Drazin inverse through
their owned classical Riesz component, removing the need to thread that packet
as a separate theorem argument.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_drazinInfiniteAssumptions
    {T : E →L[𝕂] E}
    (h : DrazinInfiniteAssumptions (𝕂 := 𝕂) T) :
    ∃ k TD, InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD k :=
  exists_drazinInverse_of_constructiveRieszDecompositionAtZero
    (hR := constructiveRieszDecompositionAtZero_of_drazinInfiniteAssumptions
      (𝕂 := 𝕂) h)

/--
Classical Riesz decomposition immediately yields the canonical Drazin witness.
-/
@[rep_depth operator]
theorem isDrazinInverse_of_hasClassicalRieszDecompositionAtZero
    {T : E →L[𝕂] E}
    (h : HasClassicalRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse T h.D h.k :=
  h.hIsDrazin

/--
Classical Riesz decomposition interface yields a canonical Drazin witness.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_rieszDecomposition
    {T : E →L[𝕂] E}
    (h : HasClassicalRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    ∃ k TD, InfoGeometry.Canonical.Drazin.IsDrazinInverse T TD k :=
  exists_drazinInverse_of_constructiveRieszDecompositionAtZero
    (hR := constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero h)

/--
Constructive Riesz decomposition at `0` for an invertible operator (`S * T = 1`, `T * S = 1`):
the regular spectral projector is `P = 1`, the Drazin index is `k = 0`, and the regular inverse is `S`.
-/
@[rep_depth operator]
def constructiveRieszDecompositionAtZero_of_invertible
    {T : E →L[𝕂] E} (S : E →L[𝕂] E)
    (hLeft : S * T = 1) (hRight : T * S = 1) :
    ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T where
  k := 0
  P := 1
  P_idempotent := mul_one 1
  PT_comm := by rw [mul_one, one_mul]
  S := S
  left_inverse_on_regular := hLeft
  right_inverse_on_regular := hRight
  S_supported_on_regular_left := mul_one S
  S_supported_on_regular_right := one_mul S
  nilpotent_on_complement := by simp

/--
Constructive Riesz decomposition at `0` for a nilpotent operator (`T ^ k = 0`):
the regular spectral projector is `P = 0` and the regular inverse is `S = 0`.
-/
@[rep_depth operator]
def constructiveRieszDecompositionAtZero_of_nilpotent
    {T : E →L[𝕂] E} (k : ℕ) (hNil : T ^ k = 0) :
    ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T where
  k := k
  P := 0
  P_idempotent := mul_zero 0
  PT_comm := by rw [mul_zero, zero_mul]
  S := 0
  left_inverse_on_regular := zero_mul T
  right_inverse_on_regular := mul_zero T
  S_supported_on_regular_left := mul_zero 0
  S_supported_on_regular_right := zero_mul 0
  nilpotent_on_complement := by rw [sub_zero, mul_one, hNil]

/--
Constructive Riesz decomposition at `0` from an idempotent `T`-commuting projector `P`,
a two-sided inverse `U` of the regular part (`U * T * P = P`, `T * U * P = P`), and nilpotency
of `T` on the defect complement (`(T * (1 - P)) ^ k = 0`).
Notice the regular inverse `S := P * U * P` and its two-sided support laws are constructed
automatically rather than assumed as independent fields.
-/
@[rep_depth operator]
def constructiveRieszDecompositionAtZero_of_regularInverseAndNilpotentDefect
    {T : E →L[𝕂] E} (k : ℕ) (P U : E →L[𝕂] E)
    (hP : P * P = P) (hComm : T * P = P * T)
    (hLeft : U * T * P = P) (hRight : T * U * P = P)
    (hNil : T ^ k * (1 - P) = 0) :
    ConstructiveRieszDecompositionAtZero (𝕂 := 𝕂) T where
  k := k
  P := P
  P_idempotent := hP
  PT_comm := hComm
  S := P * U * P
  left_inverse_on_regular := by
    calc
      (P * U * P) * T = P * U * (P * T) := by simp [mul_assoc]
      _ = P * U * (T * P) := by rw [← hComm]
      _ = P * (U * T * P) := by simp [mul_assoc]
      _ = P * P := by rw [hLeft]
      _ = P := hP
  right_inverse_on_regular := by
    calc
      T * (P * U * P) = (T * P) * U * P := by simp [mul_assoc]
      _ = (P * T) * U * P := by rw [hComm]
      _ = P * (T * U * P) := by simp [mul_assoc]
      _ = P * P := by rw [hRight]
      _ = P := hP
  S_supported_on_regular_left := by
    calc
      (P * U * P) * P = P * U * (P * P) := by simp [mul_assoc]
      _ = P * U * P := by rw [hP]
  S_supported_on_regular_right := by
    calc
      P * (P * U * P) = (P * P) * U * P := by simp [mul_assoc]
      _ = P * U * P := by rw [hP]
  nilpotent_on_complement := hNil

end SpectralInterfaces

section RieszData

variable {R : Type*} [Ring R]

/--
Riesz-style Drazin package on an operator ring.

The load-bearing field remains the canonical algebraic witness.
-/
@[rep_depth operator]
structure RieszDrazinData (T : R) where
  k : ℕ
  D : R
  P : R
  hIsDrazin : InfoGeometry.Canonical.Drazin.IsDrazinInverse T D k
  hP : P = InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection T D

variable {T : R}

/-- Extract canonical Drazin witness from a Riesz package. -/
@[rep_depth operator]
theorem isDrazinInverse_of_riesz
    (h : RieszDrazinData T) :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse T h.D h.k :=
  h.hIsDrazin

/-- The regular projector in a Riesz package is idempotent. -/
@[rep_depth operator]
theorem projector_idempotent_of_riesz
    (h : RieszDrazinData T) :
    h.P * h.P = h.P := by
  rw [h.hP]
  exact InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_is_idempotent h.hIsDrazin

/-- Complementary projector attached to a Riesz package. -/
@[rep_depth operator]
def complementaryProjector (h : RieszDrazinData T) : R :=
  InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection T h.D

/-- Complementary projector in a Riesz package is idempotent. -/
@[rep_depth operator]
theorem complementaryProjector_idempotent_of_riesz
    (h : RieszDrazinData T) :
    complementaryProjector h * complementaryProjector h = complementaryProjector h := by
  unfold complementaryProjector
  exact InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_is_idempotent h.hIsDrazin

/-- Regular/complementary projectors are left-orthogonal. -/
@[rep_depth operator]
theorem projector_mul_complementaryProjector_of_riesz
    (h : RieszDrazinData T) :
    h.P * complementaryProjector h = 0 := by
  rw [h.hP]
  unfold complementaryProjector
  exact InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_mul_complementaryProjection h.hIsDrazin

/-- Regular/complementary projectors are right-orthogonal. -/
@[rep_depth operator]
theorem complementaryProjector_mul_projector_of_riesz
    (h : RieszDrazinData T) :
    complementaryProjector h * h.P = 0 := by
  rw [h.hP]
  unfold complementaryProjector
  exact InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_mul_projection h.hIsDrazin

/-- The complementary Riesz projector is annihilated by the Drazin index power
on both sides. -/
@[rep_depth operator]
theorem drazin_complementaryProjector_annihilates_index_power
    (h : RieszDrazinData T) :
    T ^ h.k * complementaryProjector h = 0 ∧
      complementaryProjector h * T ^ h.k = 0 := by
  constructor
  · unfold complementaryProjector
    exact InfoGeometry.Canonical.Drazin.IsDrazinInverse.power_mul_complementaryProjection_eq_zero
      h.hIsDrazin
  · unfold complementaryProjector
    exact InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_mul_power_eq_zero
      h.hIsDrazin

end RieszData

section FiniteDimensionalBridge

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/--
Finite-dimensional continuous-operator bridge into the Riesz-style package.
The finite-dimensional Drazin existence theorem supplies the package
existentially; this file does not choose a canonical inverse or index.
-/
@[rep_depth operator]
theorem exists_rieszDrazinData_endCLM (T : E →L[ℝ] E) :
    ∃ h : RieszDrazinData T, InfoGeometry.Canonical.Drazin.IsDrazinInverse T h.D h.k := by
  rcases DrazinExistenceBridge.exists_canonicalDrazinInverse_global_endCLM
      (E := E) T with ⟨k, D, hD⟩
  let hpack : RieszDrazinData T :=
    { k := k
      D := D
      P := InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection T D
      hIsDrazin := hD
      hP := rfl }
  refine ⟨hpack, ?_⟩
  simpa [hpack] using hD

end FiniteDimensionalBridge

end InfoGeometry.Canonical.DrazinInfiniteCore
