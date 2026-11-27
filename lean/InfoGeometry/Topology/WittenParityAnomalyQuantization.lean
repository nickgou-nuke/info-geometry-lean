/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.LipschitzWittRieszPrimary
import InfoGeometry.Clifford.LipschitzVectorAction
import InfoGeometry.Clifford.RealLipschitzPin
import InfoGeometry.Clifford.CoordinateLessCliffordInvariance
import InfoGeometry.Clifford.Cl55PinPlusMinusNative
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Witten (2016) §2: General `Pin±` Double Covers and Stiefel–Whitney Quantization

This module formalizes the Clifford double-cover and Stiefel–Whitney anomaly-quantization
theorems of Edward Witten, *"The 'Parity' Anomaly on an Unorientable Manifold"* (2016), §2:

1. **General `Pin^+(V, Q)` and `Pin^-(V, Q)` double covers onto `O(V, Q)`**:
   - Reuses `InfoGeometry.Clifford.LipschitzWittRieszPrimary` (`lipschitzGroupToIsometryHom`,
     `lipschitzSpinorNormHom`, `pinGroupToIsometryHom`, `lipschitz_pin_spin_doubleCover_witness`),
     `RealLipschitzPin`, `RealQuadraticReflectionCartanDieudonne`, and
     `CoordinateLessCliffordInvariance`.
   - **Sign convention** (Witten 2016 §2.2, fn. 11; generalizing `Cl55PinPlusMinusNative`):
     Mathlib's `_root_.pinGroup Q` enforces `star g * g = 1`. Since `star (ι Q v) = -ι Q v`,
     `star (ι Q v) * ι Q v = -Q v`. Thus on a positive-definite Riemannian space `(V, Q)`,
     `PinPlusGroup Q := (lipschitzSpinorNormHom Q).ker` houses reflections `Q v = 1` with
     `R^2 = +1`, whereas `PinMinusGroup Q := _root_.pinGroup (-Q)` houses reflections
     `(-Q) v = -1` (i.e. `Q v = 1`) with `R^2 = -1`. In indefinite signature `(5,5)`
     (`Clifford55PinPlusMinusNative`), `PinMinus55 := pinGroup (-Q55)` already matches
     `PinMinusGroup Q55` definitionally.
   - Proves exact double-cover theorems (`pinPlus_doubleCover`, `pinMinus_doubleCover`) for
     every nontrivial finite-dimensional positive-definite `(V, Q)`: surjectivity onto
     `OrthogonalGroup Q := Q.IsometryEquiv Q` and exact kernel `{1, -1}` (`-1 ≠ 1`).

2. **Truncated Stiefel–Whitney algebra `SW4Ring A := A[X] ⧸ Ideal.span {X^5}` (Witten §2.4–2.5)**:
   - **Mod-8 `ℤ/2` theorem** (`sw_z2_mod_eight_iff`, Eq. 2.17):
     `(1 + swT : SW4Ring (ZMod 2)) ^ k = 1 ↔ 8 ∣ k`.
   - **4-copy `SO(p)` theorem** (`sw_so_four_copy_trivial` & `sw_oriented_pow_four_eq_one`, Eq. 2.18):
     over `[CharP A 2]`, any oriented Stiefel–Whitney class (`w₁ = 0`) satisfies `w^4 = 1`.
   - **Mod-4 `U(1)` theorem** (`sw_u1_stably_trivial_iff_four_dvd`, Eqs. 2.10–2.15):
     for `y = #{odd n_i}`, `∏ (1 + n_i c₁ t^2) = 1` in `SW4Ring A` iff `4 ∣ y` (when `c₁^2 ≠ 0`),
     accompanied by the `ℝℙ⁴` `η`-phase matching formula (`rp4_u1_eta_phase_trivial_iff_four_dvd`,
     Eq. 2.16) and the 2-copy `U(2) → U(1)` obstruction vs. 4-copy cancellation (Eq. 2.19).

Long-term Mathlib frontier: smooth unorientable 4-manifold `Pin±` structures, topological
vector bundle Stiefel–Whitney classes `w_k(V)` over manifolds, Atiyah–Patodi–Singer
`η`-invariants, and cobordism groups `Ω_4^{Pin^+} ≅ ℤ/16` lie beyond current Mathlib `v4.34.1`
and are scoped here to algebraic Clifford double covers and the truncated Stiefel–Whitney ring
`A[t]/(t^5)`.
-/

noncomputable section

set_option autoImplicit false

namespace InfoGeometry.Topology.WittenParityAnomalyQuantization

open InfoGeometry.Clifford
open InfoGeometry.Clifford.LipschitzWittRieszPrimary
open InfoGeometry.Clifford.LipschitzVectorAction
open InfoGeometry.Clifford.RealLipschitzPin
open InfoGeometry.Clifford.CoordinateLessCliffordInvariance
open InfoGeometry.Clifford.Clifford55PinPlusMinusNative

/-! ## Section 1: General `Pin^+(V, Q)` and `Pin^-(V, Q)` Double Covers onto `O(V, Q)` -/

section PinPlusMinus

/-- Orthogonal group `O(V, Q)` as `Q.IsometryEquiv Q`, reusing
`InfoGeometry.Clifford.quadraticIsometryEquivGroup Q`. -/
abbrev OrthogonalGroup {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : QuadraticForm ℝ V) : Type _ :=
  Q.IsometryEquiv Q

/-- `Pin^+(V, Q)` as the spinor-norm-`+1` kernel of `lipschitzSpinorNormHom Q` inside
`_root_.lipschitzGroup Q`. Positive-unit vectors `Q v = 1` lie here and square to `+1`. -/
def PinPlusGroup {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : QuadraticForm ℝ V) :
    Subgroup (_root_.lipschitzGroup Q) :=
  (lipschitzSpinorNormHom Q).ker

/-- `Pin^-(V, Q)` as Mathlib's `_root_.pinGroup (-Q)`. Unit vectors `Q v = 1` have
`(-Q) v = -1`, satisfy `star (ι (-Q) v) * ι (-Q) v = 1`, and square to `-1`. -/
abbrev PinMinusGroup {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : QuadraticForm ℝ V) : Type _ :=
  _root_.pinGroup (-Q)

/-- Convention alignment with `Cl55PinPlusMinusNative`: `PinMinusGroup Q55` coincides
definitionally with `Clifford55PinPlusMinusNative.PinMinus55`. -/
theorem cl55_pinMinus_sign_convention :
    PinMinusGroup InfoGeometry.Clifford.Clifford55.Q55 = PinMinus55 :=
  rfl

/-- Canonical group isomorphism `(-Q).IsometryEquiv (-Q) ≃* Q.IsometryEquiv Q`. -/
def negQuadraticIsometryMulEquiv {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) :
    (-Q).IsometryEquiv (-Q) ≃* OrthogonalGroup Q where
  toFun f :=
    { toLinearEquiv := f.toLinearEquiv
      map_app' v := neg_inj.mp (f.map_app v) }
  invFun f :=
    { toLinearEquiv := f.toLinearEquiv
      map_app' v := by
        change -Q (f v) = -Q v
        rw [f.map_app] }
  left_inv f := by
    apply DFunLike.ext
    intro v
    rfl
  right_inv f := by
    apply DFunLike.ext
    intro v
    rfl
  map_mul' f g := by
    apply DFunLike.ext
    intro v
    rfl

@[simp]
theorem negQuadraticIsometryMulEquiv_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (f : (-Q).IsometryEquiv (-Q)) (v : V) :
    negQuadraticIsometryMulEquiv Q f v = f v :=
  rfl

/-- Double-cover homomorphism `Pin^+(V, Q) →* O(V, Q)`. -/
def pinPlusToIsometryHom {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : QuadraticForm ℝ V) :
    PinPlusGroup Q →* OrthogonalGroup Q :=
  (lipschitzGroupToIsometryHom Q).comp (PinPlusGroup Q).subtype

/-- Double-cover homomorphism `Pin^-(V, Q) →* O(V, Q)`. -/
def pinMinusToIsometryHom {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : QuadraticForm ℝ V) :
    PinMinusGroup Q →* OrthogonalGroup Q :=
  (negQuadraticIsometryMulEquiv Q).toMonoidHom.comp (pinGroupToIsometryHom (-Q))

/-- Reflection lift in `Pin^+(V, Q)` for a unit vector `Q v = 1`. -/
def pinPlusReflection {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (hv : Q v = 1) : PinPlusGroup Q :=
  letI : Invertible (Q v) := ⟨1, by rw [hv]; norm_num, by rw [hv]; norm_num⟩
  ⟨vectorLipschitz Q v, by
    change lipschitzSpinorNormHom Q (vectorLipschitz Q v) = 1
    apply Units.ext
    change (lipschitzSpinorNormHom Q (vectorLipschitz Q v) : ℝ) = 1
    rw [vectorLipschitz_spinorNorm, hv]⟩

/-- Reflection lift in `Pin^-(V, Q)` for a unit vector `Q v = 1` (`(-Q) v = -1`). -/
def pinMinusReflection {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (hv : Q v = 1) : PinMinusGroup Q :=
  pinNegativeUnitVector (-Q) v (by change -Q v = -1; rw [hv])

/-- Euclidean reflection in `Pin^+(V, Q)` squares to `+1` (`R^2 = +1`, Witten 2016 fn. 11). -/
theorem pinPlusReflection_sq_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (hv : Q v = 1) :
    ((↑((pinPlusReflection Q v hv : _root_.lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q) ^ 2) = 1 := by
  change CliffordAlgebra.ι Q v ^ 2 = 1
  rw [pow_two, CliffordAlgebra.ι_sq_scalar, hv, map_one]

/-- Euclidean reflection in `Pin^-(V, Q)` squares to `-1` (`R^2 = -1`, Witten 2016 fn. 11). -/
theorem pinMinusReflection_sq_neg_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (hv : Q v = 1) :
    ((pinMinusReflection Q v hv : PinMinusGroup Q) : CliffordAlgebra (-Q)) ^ 2 = -1 := by
  change CliffordAlgebra.ι (-Q) v ^ 2 = -1
  rw [pow_two, CliffordAlgebra.ι_sq_scalar]
  change algebraMap ℝ (CliffordAlgebra (-Q)) (-Q v) = -1
  rw [hv, map_neg, map_one]

/-- `pinPlusReflection` projects to the orthogonal hyperplane reflection in `O(V, Q)`. -/
theorem pinPlusReflection_action {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (hv : Q v = 1) :
    pinPlusToIsometryHom Q (pinPlusReflection Q v hv) =
      realQuadraticReflectionIsometry Q v (by rw [hv]; norm_num) := by
  let _ : Invertible (Q v) := ⟨1, by rw [hv]; norm_num, by rw [hv]; norm_num⟩
  apply DFunLike.ext
  intro x
  change lipschitzGroupToIsometryHom Q (vectorLipschitz Q v) x =
    realQuadraticReflection Q v (by rw [hv]; norm_num) x
  have hact := (lipschitzGroupToIsometryHom_ι_eq_reflection Q v).1 x
  have hcoef : ⅟(Q v) * QuadraticMap.polar (⇑Q) v x =
      QuadraticMap.polar (⇑Q) x v / Q v := by
    rw [QuadraticMap.polar_comm, invOf_eq_inv, div_eq_mul_inv, mul_comm]
  rw [hcoef] at hact
  simpa [vectorLipschitz, realQuadraticReflection_apply] using hact

/-- `pinMinusReflection` projects to the orthogonal hyperplane reflection in `O(V, Q)`. -/
theorem pinMinusReflection_action {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (hv : Q v = 1) :
    pinMinusToIsometryHom Q (pinMinusReflection Q v hv) =
      realQuadraticReflectionIsometry Q v (by rw [hv]; norm_num) := by
  have hnegv : (-Q) v = -1 := by change -Q v = -1; rw [hv]
  let _ : Invertible ((-Q) v) :=
    ⟨-1, by rw [hnegv]; norm_num, by rw [hnegv]; norm_num⟩
  apply DFunLike.ext
  intro x
  change pinGroupToIsometryHom (-Q) (pinNegativeUnitVector (-Q) v hnegv) x =
    realQuadraticReflection Q v (by rw [hv]; norm_num) x
  have hpin :
      (⟨_root_.pinGroup.toUnits (pinNegativeUnitVector (-Q) v hnegv),
          _root_.pinGroup.units_mem_lipschitzGroup (pinNegativeUnitVector (-Q) v hnegv).2⟩ :
          _root_.lipschitzGroup (-Q)) =
        ⟨⟨CliffordAlgebra.ι (-Q) v, CliffordAlgebra.ι (-Q) (⅟((-Q) v) • v),
            by
              rw [map_smul, mul_smul_comm, CliffordAlgebra.ι_sq_scalar,
                Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, _root_.one_smul],
            by
              rw [map_smul, smul_mul_assoc, CliffordAlgebra.ι_sq_scalar,
                Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, _root_.one_smul]⟩,
          Subgroup.subset_closure ⟨v, rfl⟩⟩ := by
    apply Subtype.ext
    apply Units.ext
    rfl
  change lipschitzGroupToIsometryHom (-Q) _ x = _
  rw [hpin]
  have hact := (lipschitzGroupToIsometryHom_ι_eq_reflection (-Q) v).1 x
  rw [hact]
  have hpol : QuadraticMap.polar (⇑(-Q)) v x = -QuadraticMap.polar (⇑Q) x v := by
    change (-Q) (v + x) - (-Q) v - (-Q) x = -(Q (x + v) - Q x - Q v)
    change -(Q (v + x)) - (-Q v) - (-Q x) = -(Q (x + v) - Q x - Q v)
    rw [add_comm v x]
    ring
  have hinv : ⅟((-Q) v) = -1 := by
    have hmul : (-1 : ℝ) * ⅟((-Q) v) = 1 := by
      rw [← hnegv]
      exact mul_invOf_self ((-Q) v)
    linarith
  rw [hpol, hinv]
  simp only [neg_mul, _root_.one_mul]
  rw [realQuadraticReflection_apply, hv, div_one]
  ring_nf

private theorem clifford_algebraMap_injective_of_Q {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) :
    Function.Injective (algebraMap ℝ (CliffordAlgebra Q)) := by
  intro r₁ r₂ h
  have ht := congrArg (InfoGeometry.Riemannian.hTrace_cl Q) h
  have hlocal : ∀ r : ℝ, InfoGeometry.Riemannian.hTrace_cl Q
      (algebraMap ℝ (CliffordAlgebra Q) r) = r := by
    intro r
    change ExteriorAlgebra.algebraMapInv
        (CliffordAlgebra.equivExterior Q (algebraMap ℝ (CliffordAlgebra Q) r)) = r
    rw [InfoGeometry.Clifford.GradedGraceContraction.equivExterior_algebraMap]
    exact AlgHom.commutes (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra ℝ V →ₐ[ℝ] ℝ) r
  rwa [hlocal r₁, hlocal r₂] at ht

private theorem clifford_ι_conj_eq_equivOfIsometry {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (hv : Q v ≠ 0) (x : CliffordAlgebra Q) :
    let _ : Invertible (Q v) := invertibleOfNonzero hv
    let _ : Invertible (CliffordAlgebra.ι Q v) := CliffordAlgebra.invertibleιOfInvertible Q v
    CliffordAlgebra.ι Q v * x * ⅟(CliffordAlgebra.ι Q v) =
      CliffordAlgebra.equivOfIsometry
        (negIsometryEquiv Q * realQuadraticReflectionIsometry Q v hv) x := by
  let _ : Invertible (Q v) := invertibleOfNonzero hv
  let _ : Invertible (CliffordAlgebra.ι Q v) := CliffordAlgebra.invertibleιOfInvertible Q v
  let conjHom : CliffordAlgebra Q →ₐ[ℝ] CliffordAlgebra Q :=
    { toFun := fun z => CliffordAlgebra.ι Q v * z * ⅟(CliffordAlgebra.ι Q v)
      map_one' := by rw [_root_.mul_one, mul_invOf_self]
      map_mul' := fun a b => by
        calc
          CliffordAlgebra.ι Q v * (a * b) * ⅟(CliffordAlgebra.ι Q v)
              = CliffordAlgebra.ι Q v * a * 1 * b * ⅟(CliffordAlgebra.ι Q v) := by
                noncomm_ring
          _ = CliffordAlgebra.ι Q v * a * (⅟(CliffordAlgebra.ι Q v) * CliffordAlgebra.ι Q v) *
                b * ⅟(CliffordAlgebra.ι Q v) := by rw [invOf_mul_self]
          _ = (CliffordAlgebra.ι Q v * a * ⅟(CliffordAlgebra.ι Q v)) *
                (CliffordAlgebra.ι Q v * b * ⅟(CliffordAlgebra.ι Q v)) := by noncomm_ring
      map_zero' := by rw [mul_zero, zero_mul]
      map_add' := fun a b => by noncomm_ring
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, _root_.mul_one,
          mul_invOf_self] }
  have hhom :
      conjHom =
        (CliffordAlgebra.equivOfIsometry
          (negIsometryEquiv Q * realQuadraticReflectionIsometry Q v hv)).toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro y
    change CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q y * ⅟(CliffordAlgebra.ι Q v) =
      CliffordAlgebra.equivOfIsometry
        (negIsometryEquiv Q * realQuadraticReflectionIsometry Q v hv) (CliffordAlgebra.ι Q y)
    rw [CliffordAlgebra.ι_mul_ι_mul_invOf_ι Q v y]
    change CliffordAlgebra.ι Q ((⅟(Q v) * QuadraticMap.polar (⇑Q) v y) • v - y) =
      CliffordAlgebra.equivOfIsometry
        ((realQuadraticReflectionIsometry Q v hv).trans (negIsometryEquiv Q))
        (CliffordAlgebra.ι Q y)
    rw [CliffordAlgebra.equivOfIsometry_apply]
    have hvect : (⅟(Q v) * QuadraticMap.polar (⇑Q) v y) • v - y =
        (negIsometryEquiv Q) ((realQuadraticReflectionIsometry Q v hv) y) := by
      change _ = -(realQuadraticReflection Q v hv y)
      rw [realQuadraticReflection_apply, QuadraticMap.polar_comm, invOf_eq_inv, div_eq_mul_inv,
        mul_comm]
      module
    change CliffordAlgebra.ι Q ((⅟(Q v) * QuadraticMap.polar (⇑Q) v y) • v - y) =
      CliffordAlgebra.map
        ((realQuadraticReflectionIsometry Q v hv).trans (negIsometryEquiv Q)).toIsometry
        (CliffordAlgebra.ι Q y)
    rw [CliffordAlgebra.map_apply_ι, hvect]
    rfl
  exact congrArg (fun f : CliffordAlgebra Q →ₐ[ℝ] CliffordAlgebra Q => f x) hhom

/-- Any element in the kernel of `lipschitzGroupToIsometryHom Q` for a finite-dimensional
nondegenerate real quadratic space `(V, Q)` is a scalar in `range (algebraMap ℝ _)`. -/
theorem lipschitzGroupToIsometryHom_ker_subset_scalars
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (hnondeg : Q.Nondegenerate)
    (g : _root_.lipschitzGroup Q) (hg : g ∈ (lipschitzGroupToIsometryHom Q).ker) :
    (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      (algebraMap ℝ (CliffordAlgebra Q)).range := by
  let x : CliffordAlgebra Q := (↑(g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  have hact : ∀ v : V, CliffordAlgebra.involute (Q := Q) x * CliffordAlgebra.ι Q v =
      CliffordAlgebra.ι Q v * x := by
    intro v
    have hv1 : lipschitzGroupToIsometryHom Q g v = v := by
      rw [MonoidHom.mem_ker] at hg
      rw [hg]
      rfl
    have hcl := congrArg (CliffordAlgebra.ι Q) hv1
    rw [ι_lipschitzGroupToIsometryHom] at hcl
    have hmul := congrArg (fun z => z * x) hcl
    have hinv : (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) * x = 1 := by
      exact Units.inv_mul (g : (CliffordAlgebra Q)ˣ)
    calc
      CliffordAlgebra.involute (Q := Q) x * CliffordAlgebra.ι Q v
          = CliffordAlgebra.involute (Q := Q) x * CliffordAlgebra.ι Q v * 1 := (_root_.mul_one _).symm
      _ = CliffordAlgebra.involute (Q := Q) x * CliffordAlgebra.ι Q v *
            ((↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) * x) := by rw [hinv]
      _ = (CliffordAlgebra.involute (Q := Q) x * CliffordAlgebra.ι Q v *
            (↑((g : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q)) * x := by noncomm_ring
      _ = CliffordAlgebra.ι Q v * x := hmul
  have hreflFix : ∀ v : V, (hv : Q v ≠ 0) →
      CliffordAlgebra.equivOfIsometry (realQuadraticReflectionIsometry Q v hv) x = x := by
    intro v hv
    let _ : Invertible (Q v) := invertibleOfNonzero hv
    let _ : Invertible (CliffordAlgebra.ι Q v) := CliffordAlgebra.invertibleιOfInvertible Q v
    have hconj := clifford_ι_conj_eq_equivOfIsometry Q v hv x
    change CliffordAlgebra.ι Q v * x * ⅟(CliffordAlgebra.ι Q v) =
      CliffordAlgebra.equivOfIsometry
        (negIsometryEquiv Q * realQuadraticReflectionIsometry Q v hv) x at hconj
    have hcomp :
        CliffordAlgebra.equivOfIsometry
            (negIsometryEquiv Q * realQuadraticReflectionIsometry Q v hv) x =
          CliffordAlgebra.involute (Q := Q)
            (CliffordAlgebra.equivOfIsometry (realQuadraticReflectionIsometry Q v hv) x) := by
      change CliffordAlgebra.equivOfIsometry
          ((realQuadraticReflectionIsometry Q v hv).trans (negIsometryEquiv Q)) x = _
      rw [← CliffordAlgebra.equivOfIsometry_trans]
      change CliffordAlgebra.equivOfIsometry (negIsometryEquiv Q)
          (CliffordAlgebra.equivOfIsometry (realQuadraticReflectionIsometry Q v hv) x) = _
      rw [equivOfIsometry_negIsometryEquiv]
      rfl
    rcases lipschitz_involute_eq_self_or_neg Q g.property with heven | hodd
    · have hcomm : CliffordAlgebra.ι Q v * x = x * CliffordAlgebra.ι Q v := by
        rw [← hact v, heven]
      have hlhs : CliffordAlgebra.ι Q v * x * ⅟(CliffordAlgebra.ι Q v) = x := by
        rw [hcomm, _root_.mul_assoc, mul_invOf_self, _root_.mul_one]
      rw [hlhs, hcomp] at hconj
      have hinv := congrArg (CliffordAlgebra.involute (Q := Q)) hconj.symm
      rw [CliffordAlgebra.involute_involute, heven] at hinv
      exact hinv
    · have hanticomm : CliffordAlgebra.ι Q v * x = -(x * CliffordAlgebra.ι Q v) := by
        have ha := hact v
        rw [hodd, neg_mul] at ha
        have ha' : CliffordAlgebra.ι Q v * x = -x * CliffordAlgebra.ι Q v := by
          simpa [x] using ha.symm
        calc
          CliffordAlgebra.ι Q v * x = -x * CliffordAlgebra.ι Q v := ha'
          _ = -(x * CliffordAlgebra.ι Q v) := by noncomm_ring
      have hlhs : CliffordAlgebra.ι Q v * x * ⅟(CliffordAlgebra.ι Q v) = -x := by
        rw [hanticomm, neg_mul, _root_.mul_assoc, mul_invOf_self, _root_.mul_one]
      rw [hlhs, hcomp] at hconj
      have hinv := congrArg (CliffordAlgebra.involute (Q := Q)) hconj.symm
      rw [CliffordAlgebra.involute_involute, map_neg, hodd, neg_neg] at hinv
      exact hinv
  let B : LinearMap.BilinForm ℝ V := QuadraticMap.associatedHom ℝ Q
  have hBsymm : LinearMap.IsSymm B := ⟨fun a b => QuadraticMap.associated_isSymm ℝ Q a b⟩
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B) hBsymm
  have hBnondeg : B.Nondegenerate := (QuadraticMap.nondegenerate_associated_iff).mpr hnondeg
  have hQ : ∀ i : Fin (Module.finrank ℝ V), Q (b i) ≠ 0 := by
    intro i hi
    apply b.ne_zero i
    apply hBnondeg.1 (b i)
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range b) := by rw [b.span_eq]; trivial
    induction hy using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨j, rfl⟩
        by_cases hij : j = i
        · subst hij
          change (QuadraticMap.associated Q) (b j) (b j) = 0
          rw [QuadraticMap.associated_apply, ← two_smul ℝ (b j), QuadraticMap.map_smul, hi]
          simp
        · exact hb (Ne.symm hij)
    | zero => simp
    | add u w _ _ hu hw => simp [hu, hw]
    | smul c u _ hu => simp [hu]
  have horth : ∀ {i j : Fin (Module.finrank ℝ V)}, i ≠ j →
      QuadraticMap.polar (⇑Q) (b i) (b j) = 0 := by
    intro i j hij
    have hzero : B (b i) (b j) = 0 := hb hij
    have htwo := congrArg (fun C : LinearMap.BilinForm ℝ V => C (b i) (b j))
      (QuadraticMap.two_nsmul_associated ℝ Q)
    have htwo' : 2 * B (b i) (b j) = QuadraticMap.polar (⇑Q) (b i) (b j) := by
      simpa only [B, two_nsmul, LinearMap.add_apply, QuadraticMap.polarBilin_apply_apply,
        two_mul] using htwo
    rw [hzero, mul_zero] at htwo'
    exact htwo'.symm
  have htop : realQuadraticReflectionSubgroup Q = ⊤ :=
    realQuadraticReflectionSubgroup_eq_top_of_orthogonal_spanning Q b b.span_eq hQ horth
  have hInv : InfoGeometry.OperatorAlgebra.IsInvariant (cliffordSymmetryAction Q) x := by
    intro f
    have hf : f ∈ realQuadraticReflectionSubgroup Q := by rw [htop]; trivial
    change f ∈ Subgroup.closure (realQuadraticReflectionSet Q) at hf
    induction hf using Subgroup.closure_induction with
    | mem k hk =>
        rcases hk with ⟨v, hv, rfl⟩
        exact hreflFix v hv
    | one =>
        change CliffordAlgebra.equivOfIsometry (QuadraticMap.IsometryEquiv.refl Q) x = x
        rw [CliffordAlgebra.equivOfIsometry_refl]
        rfl
    | mul f₁ f₂ _ _ hf₁ hf₂ =>
        change CliffordAlgebra.equivOfIsometry f₁ x = x at hf₁
        change CliffordAlgebra.equivOfIsometry f₂ x = x at hf₂
        change CliffordAlgebra.equivOfIsometry (f₁ * f₂) x = x
        change CliffordAlgebra.equivOfIsometry (f₂.trans f₁) x = x
        rw [← CliffordAlgebra.equivOfIsometry_trans]
        change CliffordAlgebra.equivOfIsometry f₁ (CliffordAlgebra.equivOfIsometry f₂ x) = x
        rw [hf₂, hf₁]
    | inv f₁ _ hf₁ =>
        change CliffordAlgebra.equivOfIsometry f₁ x = x at hf₁
        have hinj : Function.Injective (CliffordAlgebra.equivOfIsometry f₁) :=
          (CliffordAlgebra.equivOfIsometry f₁).injective
        apply hinj
        change CliffordAlgebra.equivOfIsometry f₁ (CliffordAlgebra.equivOfIsometry f₁.symm x) =
          CliffordAlgebra.equivOfIsometry f₁ x
        have hid : CliffordAlgebra.equivOfIsometry f₁
            (CliffordAlgebra.equivOfIsometry f₁.symm x) = x := by
          change CliffordAlgebra.equivOfIsometry f₁
              ((CliffordAlgebra.equivOfIsometry f₁).symm x) = x
          exact (CliffordAlgebra.equivOfIsometry f₁).apply_symm_apply x
        rw [hid, hf₁]
  obtain ⟨c, hc⟩ := (isInvariant_cliffordSymmetryAction_iff_mem_range Q x).mp hInv
  exact ⟨c, hc.symm⟩

private theorem nondegenerate_of_posDef {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (hpos : ∀ v : V, v ≠ 0 → 0 < Q v) : Q.Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticMap.radical_eq_ker_polarBilin,
    Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  by_contra hv0
  have hpol : QuadraticMap.polar (⇑Q) v v = 0 := congrArg (fun f : V →ₗ[ℝ] ℝ => f v) hv
  have hQ0 : Q v = 0 := by
    have h2 : (2 : ℝ) * Q v = 0 := by
      calc
        (2 : ℝ) * Q v = QuadraticMap.polar (⇑Q) v v := by
          rw [QuadraticMap.polar_self, two_nsmul, two_mul]
        _ = 0 := hpol
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  exact (ne_of_gt (hpos v hv0)) hQ0

/-- General finite-dimensional `Pin^+(V, Q) →* O(V, Q)` double cover theorem for any
nontrivial positive-definite real quadratic space `(V, Q)`: surjectivity and exact kernel
`{1, -1}` (`-1 ≠ 1`). -/
theorem pinPlus_doubleCover
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
    (Q : QuadraticForm ℝ V) (hpos : ∀ v : V, v ≠ 0 → 0 < Q v) :
    Function.Surjective (pinPlusToIsometryHom Q) ∧
      ∃ negOne : PinPlusGroup Q,
        (↑(negOne : _root_.lipschitzGroup Q) : (CliffordAlgebra Q)ˣ).1 = -1 ∧
        negOne ≠ 1 ∧
        ∀ g : PinPlusGroup Q, g ∈ (pinPlusToIsometryHom Q).ker ↔ g = 1 ∨ g = negOne := by
  let B : LinearMap.BilinForm ℝ V := QuadraticMap.associatedHom ℝ Q
  have hBsymm : LinearMap.IsSymm B := ⟨fun a b => QuadraticMap.associated_isSymm ℝ Q a b⟩
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B) hBsymm
  have hQ : ∀ i : Fin (Module.finrank ℝ V), Q (b i) ≠ 0 :=
    fun i => ne_of_gt (hpos (b i) (b.ne_zero i))
  have horth : ∀ {i j : Fin (Module.finrank ℝ V)}, i ≠ j →
      QuadraticMap.polar (⇑Q) (b i) (b j) = 0 := by
    intro i j hij
    have hzero : B (b i) (b j) = 0 := hb hij
    have htwo := congrArg (fun C : LinearMap.BilinForm ℝ V => C (b i) (b j))
      (QuadraticMap.two_nsmul_associated ℝ Q)
    have htwo' : 2 * B (b i) (b j) = QuadraticMap.polar (⇑Q) (b i) (b j) := by
      simpa only [B, two_nsmul, LinearMap.add_apply, QuadraticMap.polarBilin_apply_apply,
        two_mul] using htwo
    rw [hzero, mul_zero] at htwo'
    exact htwo'.symm
  have htop : realQuadraticReflectionSubgroup Q = ⊤ :=
    realQuadraticReflectionSubgroup_eq_top_of_orthogonal_spanning Q b b.span_eq hQ horth
  have hsurj : Function.Surjective (pinPlusToIsometryHom Q) := by
    have hgen : realQuadraticReflectionSubgroup Q ≤ (pinPlusToIsometryHom Q).range := by
      change Subgroup.closure (realQuadraticReflectionSet Q) ≤ _
      rw [Subgroup.closure_le]
      intro f hf
      rcases hf with ⟨v, hv, rfl⟩
      have hv0 : v ≠ 0 := by
        rintro rfl
        exact hv (by simp)
      have hQvpos : 0 < Q v := hpos v hv0
      let c : ℝ := (Real.sqrt (Q v))⁻¹
      have hc : c ≠ 0 := inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hQvpos))
      let w : V := c • v
      have hw : Q w = 1 := by
        change Q (c • v) = 1
        rw [QuadraticMap.map_smul, smul_eq_mul]
        dsimp [c]
        have hsq : Real.sqrt (Q v) ^ 2 = Q v := Real.sq_sqrt (le_of_lt hQvpos)
        field_simp [ne_of_gt (Real.sqrt_pos.mpr hQvpos)]
        rw [hsq]
      refine ⟨pinPlusReflection Q w hw, ?_⟩
      rw [pinPlusReflection_action]
      apply DFunLike.ext
      intro x
      exact congrArg (fun e : V ≃ₗ[ℝ] V => e x)
        (InfoGeometry.Clifford.LipschitzVectorAction.realQuadraticReflection_smul Q c v hv hc)
    have hrange : (pinPlusToIsometryHom Q).range = ⊤ := top_unique (htop ▸ hgen)
    intro f
    have hf : f ∈ (pinPlusToIsometryHom Q).range := by rw [hrange]; trivial
    rcases hf with ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨a, ha0⟩ := exists_ne (0 : V)
  have hQa : IsUnit (Q a) := IsUnit.mk0 (Q a) (ne_of_gt (hpos a ha0))
  have hdw := lipschitz_pin_spin_doubleCover_witness Q ⟨a, hQa⟩
  have hneg_mem_lip : (-1 : (CliffordAlgebra Q)ˣ) ∈ _root_.lipschitzGroup Q := hdw.1
  let negLip : _root_.lipschitzGroup Q := ⟨-1, hneg_mem_lip⟩
  have hneg_mem_plus : negLip ∈ PinPlusGroup Q := by
    change lipschitzSpinorNormHom Q negLip = 1
    apply Units.ext
    apply clifford_algebraMap_injective_of_Q Q
    change algebraMap ℝ (CliffordAlgebra Q) (lipschitzSpinorNormVal Q negLip) =
      algebraMap ℝ (CliffordAlgebra Q) ((1 : ℝˣ) : ℝ)
    rw [algebraMap_lipschitzSpinorNormVal, Units.val_one, map_one]
    change CliffordAlgebra.reverse (Q := Q) (-1 : CliffordAlgebra Q) * (-1 : CliffordAlgebra Q) = 1
    rw [map_neg, ← map_one (algebraMap ℝ (CliffordAlgebra Q)), CliffordAlgebra.reverse.commutes,
      map_one, neg_mul_neg, _root_.one_mul]
  let negOne : PinPlusGroup Q := ⟨negLip, hneg_mem_plus⟩
  have hneg_val : (↑(negOne : _root_.lipschitzGroup Q) : (CliffordAlgebra Q)ˣ).1 = -1 := rfl
  have hneg_ne : negOne ≠ 1 := by
    intro h
    have h' := congrArg (fun g : PinPlusGroup Q =>
      (↑(g : _root_.lipschitzGroup Q) : (CliffordAlgebra Q)ˣ).1) h
    change (-1 : CliffordAlgebra Q) = 1 at h'
    exact hdw.2.2.2.1 h'
  refine ⟨hsurj, negOne, hneg_val, hneg_ne, ?_⟩
  intro g
  constructor
  · intro hg
    have hker : (g : _root_.lipschitzGroup Q) ∈ (lipschitzGroupToIsometryHom Q).ker := hg
    obtain ⟨c, hc⟩ := lipschitzGroupToIsometryHom_ker_subset_scalars Q
      (nondegenerate_of_posDef Q hpos) g.1 hker
    have hnorm : CliffordAlgebra.reverse (Q := Q)
        (↑(g.1 : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        (↑(g.1 : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = 1 := by
      have hgker : lipschitzSpinorNormHom Q g.1 = 1 := g.2
      have hval := congrArg (fun u : ℝˣ => algebraMap ℝ (CliffordAlgebra Q) (u : ℝ)) hgker
      rw [show (lipschitzSpinorNormHom Q g.1 : ℝ) = lipschitzSpinorNormVal Q g.1 from rfl] at hval
      rw [algebraMap_lipschitzSpinorNormVal, Units.val_one, map_one] at hval
      exact hval
    rw [← hc, CliffordAlgebra.reverse.commutes, ← map_mul, ← map_one (algebraMap ℝ (CliffordAlgebra Q))]
      at hnorm
    have hcsq : c * c = 1 := clifford_algebraMap_injective_of_Q Q hnorm
    rcases mul_self_eq_one_iff.mp hcsq with rfl | rfl
    · left
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      change (↑(g.1 : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = 1
      simpa using hc.symm
    · right
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      change (↑(g.1 : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = -1
      simpa [negOne, negLip] using hc.symm
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact hdw.2.2.2.2 hneg_mem_lip

/-- General finite-dimensional `Pin^-(V, Q) →* O(V, Q)` double cover theorem for any
nontrivial positive-definite real quadratic space `(V, Q)`: surjectivity and exact kernel
`{1, -1}` (`-1 ≠ 1`). -/
theorem pinMinus_doubleCover
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
    (Q : QuadraticForm ℝ V) (hpos : ∀ v : V, v ≠ 0 → 0 < Q v) :
    Function.Surjective (pinMinusToIsometryHom Q) ∧
      ∃ negOne : PinMinusGroup Q,
        (negOne : CliffordAlgebra (-Q)) = -1 ∧
        negOne ≠ 1 ∧
        ∀ g : PinMinusGroup Q, g ∈ (pinMinusToIsometryHom Q).ker ↔ g = 1 ∨ g = negOne := by
  let B : LinearMap.BilinForm ℝ V := QuadraticMap.associatedHom ℝ Q
  have hBsymm : LinearMap.IsSymm B := ⟨fun a b => QuadraticMap.associated_isSymm ℝ Q a b⟩
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B) hBsymm
  have hQ : ∀ i : Fin (Module.finrank ℝ V), Q (b i) ≠ 0 :=
    fun i => ne_of_gt (hpos (b i) (b.ne_zero i))
  have horth : ∀ {i j : Fin (Module.finrank ℝ V)}, i ≠ j →
      QuadraticMap.polar (⇑Q) (b i) (b j) = 0 := by
    intro i j hij
    have hzero : B (b i) (b j) = 0 := hb hij
    have htwo := congrArg (fun C : LinearMap.BilinForm ℝ V => C (b i) (b j))
      (QuadraticMap.two_nsmul_associated ℝ Q)
    have htwo' : 2 * B (b i) (b j) = QuadraticMap.polar (⇑Q) (b i) (b j) := by
      simpa only [B, two_nsmul, LinearMap.add_apply, QuadraticMap.polarBilin_apply_apply,
        two_mul] using htwo
    rw [hzero, mul_zero] at htwo'
    exact htwo'.symm
  have htop : realQuadraticReflectionSubgroup Q = ⊤ :=
    realQuadraticReflectionSubgroup_eq_top_of_orthogonal_spanning Q b b.span_eq hQ horth
  have hsurj : Function.Surjective (pinMinusToIsometryHom Q) := by
    have hgen : realQuadraticReflectionSubgroup Q ≤ (pinMinusToIsometryHom Q).range := by
      change Subgroup.closure (realQuadraticReflectionSet Q) ≤ _
      rw [Subgroup.closure_le]
      intro f hf
      rcases hf with ⟨v, hv, rfl⟩
      have hv0 : v ≠ 0 := by
        rintro rfl
        exact hv (by simp)
      have hQvpos : 0 < Q v := hpos v hv0
      let c : ℝ := (Real.sqrt (Q v))⁻¹
      have hc : c ≠ 0 := inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hQvpos))
      let w : V := c • v
      have hw : Q w = 1 := by
        change Q (c • v) = 1
        rw [QuadraticMap.map_smul, smul_eq_mul]
        dsimp [c]
        have hsq : Real.sqrt (Q v) ^ 2 = Q v := Real.sq_sqrt (le_of_lt hQvpos)
        field_simp [ne_of_gt (Real.sqrt_pos.mpr hQvpos)]
        rw [hsq]
      refine ⟨pinMinusReflection Q w hw, ?_⟩
      rw [pinMinusReflection_action]
      apply DFunLike.ext
      intro x
      exact congrArg (fun e : V ≃ₗ[ℝ] V => e x)
        (InfoGeometry.Clifford.LipschitzVectorAction.realQuadraticReflection_smul Q c v hv hc)
    have hrange : (pinMinusToIsometryHom Q).range = ⊤ := top_unique (htop ▸ hgen)
    intro f
    have hf : f ∈ (pinMinusToIsometryHom Q).range := by rw [hrange]; trivial
    rcases hf with ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨a, ha0⟩ := exists_ne (0 : V)
  have hnegQa : IsUnit ((-Q) a) := by
    change IsUnit (-Q a)
    exact (IsUnit.mk0 (Q a) (ne_of_gt (hpos a ha0))).neg
  have hdw := lipschitz_pin_spin_doubleCover_witness (-Q) ⟨a, hnegQa⟩
  let negOne : PinMinusGroup Q := ⟨-1, hdw.2.1⟩
  have hneg_val : (negOne : CliffordAlgebra (-Q)) = -1 := rfl
  have hneg_ne : negOne ≠ 1 := by
    intro h
    have h' := congrArg (fun g : PinMinusGroup Q => (g : CliffordAlgebra (-Q))) h
    change (-1 : CliffordAlgebra (-Q)) = 1 at h'
    exact hdw.2.2.2.1 h'
  have hnondegNeg : (-Q).Nondegenerate := by
    rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticMap.radical_eq_ker_polarBilin,
      Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    by_contra hv0
    have hpol : QuadraticMap.polar (⇑(-Q)) v v = 0 := congrArg (fun f : V →ₗ[ℝ] ℝ => f v) hv
    have hpol' : QuadraticMap.polar (⇑Q) v v = 0 := by
      have hneg : QuadraticMap.polar (⇑(-Q)) v v = -QuadraticMap.polar (⇑Q) v v := by
        change (-Q) (v + v) - (-Q) v - (-Q) v = -(Q (v + v) - Q v - Q v)
        change -(Q (v + v)) - (-Q v) - (-Q v) = -(Q (v + v) - Q v - Q v)
        ring
      rw [hneg, neg_eq_zero] at hpol
      exact hpol
    have hQ0 : Q v = 0 := by
      have h2 : (2 : ℝ) * Q v = 0 := by
        calc
          (2 : ℝ) * Q v = QuadraticMap.polar (⇑Q) v v := by
            rw [QuadraticMap.polar_self, two_nsmul, two_mul]
          _ = 0 := hpol'
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    exact (ne_of_gt (hpos v hv0)) hQ0
  refine ⟨hsurj, negOne, hneg_val, hneg_ne, ?_⟩
  intro g
  constructor
  · intro hg
    have hkerPin : g ∈ (pinGroupToIsometryHom (-Q)).ker := by
      rw [MonoidHom.mem_ker] at hg ⊢
      exact (negQuadraticIsometryMulEquiv Q).injective (by simpa [pinMinusToIsometryHom] using hg)
    let gLip : _root_.lipschitzGroup (-Q) :=
      ⟨_root_.pinGroup.toUnits g, _root_.pinGroup.units_mem_lipschitzGroup g.2⟩
    have hkerLip : gLip ∈ (lipschitzGroupToIsometryHom (-Q)).ker := hkerPin
    obtain ⟨c, hc⟩ := lipschitzGroupToIsometryHom_ker_subset_scalars (-Q) hnondegNeg gLip hkerLip
    have hstar : star (g : CliffordAlgebra (-Q)) * (g : CliffordAlgebra (-Q)) = 1 :=
      _root_.pinGroup.coe_star_mul_self g
    have hgcoe : (↑(gLip : (CliffordAlgebra (-Q))ˣ) : CliffordAlgebra (-Q)) =
        (g : CliffordAlgebra (-Q)) := rfl
    rw [hgcoe] at hc
    have hstarc : star (algebraMap ℝ (CliffordAlgebra (-Q)) c) =
        algebraMap ℝ (CliffordAlgebra (-Q)) c := by
      rw [CliffordAlgebra.star_def, CliffordAlgebra.involute.commutes,
        CliffordAlgebra.reverse.commutes]
    rw [← hc, hstarc, ← map_mul, ← map_one (algebraMap ℝ (CliffordAlgebra (-Q)))] at hstar
    have hcsq : c * c = 1 := clifford_algebraMap_injective_of_Q (-Q) hstar
    rcases mul_self_eq_one_iff.mp hcsq with rfl | rfl
    · left
      apply Subtype.ext
      simpa using hc.symm
    · right
      apply Subtype.ext
      simpa [negOne] using hc.symm
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · rw [MonoidHom.mem_ker]
      change negQuadraticIsometryMulEquiv Q (pinGroupToIsometryHom (-Q) negOne) = 1
      have hlip : pinGroupToIsometryHom (-Q) negOne = 1 := by
        have hmem : (-1 : (CliffordAlgebra (-Q))ˣ) ∈ _root_.lipschitzGroup (-Q) := hdw.1
        have heq : (⟨_root_.pinGroup.toUnits negOne,
            _root_.pinGroup.units_mem_lipschitzGroup negOne.2⟩ : _root_.lipschitzGroup (-Q)) =
            ⟨-1, hmem⟩ := by
          apply Subtype.ext
          apply Units.ext
          rfl
        change lipschitzGroupToIsometryHom (-Q) _ = 1
        rw [heq]
        exact hdw.2.2.2.2 hmem
      rw [hlip, map_one]

section NoncommWitness

/-- Standard 2D Euclidean quadratic form `x₀² + x₁²` on `Fin 2 → ℝ`. -/
def euc2Q : QuadraticForm ℝ (Fin 2 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (fun _ : Fin 2 => (1 : ℝ))

/-- Closed `T16` non-commutativity witness for `CliffordAlgebra` on a positive-definite
Euclidean space (`e₀ * e₁ = -(e₁ * e₀)` and `e₀ * e₁ ≠ e₁ * e₀`). -/
theorem clifford_euc2_anticomm_witness :
    let e0 : CliffordAlgebra euc2Q := CliffordAlgebra.ι euc2Q (fun i => if i = 0 then 1 else 0)
    let e1 : CliffordAlgebra euc2Q := CliffordAlgebra.ι euc2Q (fun i => if i = 1 then 1 else 0)
    e0 * e1 = -(e1 * e0) ∧ e0 * e1 ≠ e1 * e0 := by
  let v0 : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
  let v1 : Fin 2 → ℝ := fun i => if i = 1 then 1 else 0
  let e0 : CliffordAlgebra euc2Q := CliffordAlgebra.ι euc2Q v0
  let e1 : CliffordAlgebra euc2Q := CliffordAlgebra.ι euc2Q v1
  have hQ0 : euc2Q v0 = 1 := by
    simp [euc2Q, v0, QuadraticMap.weightedSumSquares_apply]
  have hQ1 : euc2Q v1 = 1 := by
    simp [euc2Q, v1, QuadraticMap.weightedSumSquares_apply]
  have hpol : QuadraticMap.polar (⇑euc2Q) v0 v1 = 0 := by
    change euc2Q (v0 + v1) - euc2Q v0 - euc2Q v1 = 0
    simp [euc2Q, v0, v1, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two]
  have hanti : e0 * e1 = -(e1 * e0) := by
    have hadd := CliffordAlgebra.ι_mul_ι_add_swap (Q := euc2Q) v0 v1
    rw [hpol, map_zero] at hadd
    exact eq_neg_of_add_eq_zero_left hadd
  refine ⟨hanti, ?_⟩
  intro hcomm
  have h2 : (2 : ℝ) • (e0 * e1) = 0 := by
    rw [two_smul]
    calc
      e0 * e1 + e0 * e1 = e0 * e1 + e1 * e0 := by rw [← hcomm]
      _ = 0 := by rw [hanti, neg_add_cancel]
  have he01 : e0 * e1 = 0 := by
    have h' := congrArg (fun z : CliffordAlgebra euc2Q => (2⁻¹ : ℝ) • z) h2
    simpa [smul_smul] using h'
  have hsq0 : e0 * e0 = 1 := by
    change CliffordAlgebra.ι euc2Q v0 * CliffordAlgebra.ι euc2Q v0 = 1
    rw [CliffordAlgebra.ι_sq_scalar, hQ0, map_one]
  have hsq1 : e1 * e1 = 1 := by
    change CliffordAlgebra.ι euc2Q v1 * CliffordAlgebra.ι euc2Q v1 = 1
    rw [CliffordAlgebra.ι_sq_scalar, hQ1, map_one]
  have h10 : (1 : CliffordAlgebra euc2Q) = 0 := by
    calc
      (1 : CliffordAlgebra euc2Q) = (e0 * e0) * (e1 * e1) := by rw [hsq0, hsq1, _root_.mul_one]
      _ = e0 * (e0 * e1) * e1 := by noncomm_ring
      _ = 0 := by rw [he01, mul_zero, zero_mul]
  have h01r : (1 : ℝ) = 0 := clifford_algebraMap_injective_of_Q euc2Q (by simp at h10)
  norm_num at h01r

end NoncommWitness

end PinPlusMinus

/-! ## Section 2: Truncated Stiefel–Whitney Polynomial Ring `A[t]/(t^5)` (Witten §2.4–2.5) -/

section StiefelWhitneyAlgebra

open Polynomial

/-- Truncated Stiefel–Whitney cohomology ring `A[t] ⧸ (t⁵)` for a 4-manifold. -/
abbrev SW4Ring (A : Type*) [CommRing A] :=
  A[X] ⧸ Ideal.span {(Polynomial.X : A[X]) ^ 5}

/-- Canonical quotient map `A[X] →+* SW4Ring A`. -/
def swMk {A : Type*} [CommRing A] : A[X] →+* SW4Ring A :=
  Ideal.Quotient.mk (Ideal.span {(Polynomial.X : A[X]) ^ 5})

/-- Degree-1 Stiefel–Whitney generator `t : SW4Ring A` satisfying `t⁵ = 0`. -/
def swT {A : Type*} [CommRing A] : SW4Ring A :=
  swMk Polynomial.X

@[simp]
theorem swT_pow_five {A : Type*} [CommRing A] : (swT : SW4Ring A) ^ 5 = 0 := by
  change swMk ((Polynomial.X : A[X]) ^ 5) = 0
  rw [swMk, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- In `SW4Ring A`, two polynomials are equal modulo `t⁵` iff their coefficients agree
in all degrees `d < 5`. -/
theorem swMk_eq_iff {A : Type*} [CommRing A] (p q : A[X]) :
    swMk p = swMk q ↔ ∀ d < 5, p.coeff d = q.coeff d := by
  rw [swMk, Ideal.Quotient.eq, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  simp only [Polynomial.coeff_sub, sub_eq_zero]

private theorem swT_pow_eq_zero_of_le {A : Type*} [CommRing A] {n : ℕ} (hn : 5 ≤ n) :
    (swT : SW4Ring A) ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, swT_pow_five, zero_mul]

instance sw4Ring_charP {A : Type*} [CommRing A] [CharP A 2] : CharP (SW4Ring A) 2 := by
  refine ⟨fun n => ?_⟩
  have h0 : ((n : SW4Ring A) = 0) ↔ swMk (Polynomial.C (n : A)) = swMk 0 := by
    simp [swMk]
  rw [h0, swMk_eq_iff]
  constructor
  · intro h
    have h0' := h 0 (by norm_num)
    simp only [Polynomial.coeff_C_zero, Polynomial.coeff_zero] at h0'
    exact (CharP.cast_eq_zero_iff A 2 n).mp h0'
  · intro hn d _
    have hnA : (n : A) = 0 := (CharP.cast_eq_zero_iff A 2 n).mpr hn
    simp [hnA]

/-! ### 2.1 Mod-8 `ℤ/2` Anomaly Theorem (Witten 2016 Eq. 2.17) -/

/-- **Mod-8 `ℤ/2` Theorem (Witten 2016 §2.5, Eq. 2.17)**:
For `k` copies of a real line bundle `α` with `w(α) = 1 + t`, the total Stiefel–Whitney
class `(1 + t)^k` is trivial in `H^*(X; ℤ/2)` modulo `t⁵` if and only if `8 ∣ k`. -/
theorem sw_z2_mod_eight_iff (k : ℕ) :
    ((1 + swT : SW4Ring (ZMod 2)) ^ k = 1) ↔ 8 ∣ k := by
  have h8 : ((1 + swT : SW4Ring (ZMod 2)) ^ 8) = 1 := by
    have hpow8 : (1 + swT : SW4Ring (ZMod 2)) ^ (2 ^ 3) =
        1 ^ (2 ^ 3) + swT ^ (2 ^ 3) :=
      add_pow_char_pow (R := SW4Ring (ZMod 2)) (p := 2) 1 swT 3
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, hpow8, one_pow,
      show (2 ^ 3 : ℕ) = 8 by norm_num, swT_pow_eq_zero_of_le (by norm_num), add_zero]
  have hmod : (1 + swT : SW4Ring (ZMod 2)) ^ k = (1 + swT : SW4Ring (ZMod 2)) ^ (k % 8) := by
    conv_lhs => rw [← Nat.div_add_mod k 8]
    rw [pow_add, pow_mul, h8, one_pow, _root_.one_mul]
  rw [hmod, Nat.dvd_iff_mod_eq_zero]
  have hklt : k % 8 < 8 := Nat.mod_lt k (by norm_num)
  generalize k % 8 = r at hklt ⊢
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · constructor
    · intro h
      have heq : swMk ((1 + Polynomial.X : (ZMod 2)[X]) ^ 1) = swMk 1 := by simpa [swT] using h
      rw [swMk_eq_iff] at heq
      have h1 := heq 1 (by norm_num)
      simp [Polynomial.coeff_one] at h1
    · intro h; omega
  · constructor
    · intro h
      have heq : swMk ((1 + Polynomial.X : (ZMod 2)[X]) ^ 2) = swMk 1 := by simpa [swT] using h
      rw [swMk_eq_iff] at heq
      have h2 := heq 2 (by norm_num)
      rw [add_pow_char, one_pow] at h2
      simp [Polynomial.coeff_one, Polynomial.coeff_X_pow] at h2
    · intro h; omega
  · constructor
    · intro h
      have heq : swMk ((1 + Polynomial.X : (ZMod 2)[X]) ^ 3) = swMk 1 := by simpa [swT] using h
      rw [swMk_eq_iff] at heq
      have h1 := heq 1 (by norm_num)
      have h3 : (1 + Polynomial.X : (ZMod 2)[X]) ^ 3 =
          1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 := by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_one, add_pow_char, one_pow]
        ring
      rw [h3] at h1
      simp [Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow] at h1
    · intro h; omega
  · constructor
    · intro h
      have heq : swMk ((1 + Polynomial.X : (ZMod 2)[X]) ^ 4) = swMk 1 := by simpa [swT] using h
      rw [swMk_eq_iff] at heq
      have h4 := heq 4 (by norm_num)
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, add_pow_char_pow (p := 2), one_pow] at h4
      simp [Polynomial.coeff_one, Polynomial.coeff_X_pow] at h4
    · intro h; omega
  · constructor
    · intro h
      have heq : swMk ((1 + Polynomial.X : (ZMod 2)[X]) ^ 5) = swMk 1 := by simpa [swT] using h
      rw [swMk_eq_iff] at heq
      have h1 := heq 1 (by norm_num)
      have h5 : (1 + Polynomial.X : (ZMod 2)[X]) ^ 5 =
          1 + Polynomial.X + Polynomial.X ^ 4 + Polynomial.X ^ 5 := by
        rw [show (5 : ℕ) = 2 ^ 2 + 1 by norm_num, pow_add, pow_one,
          add_pow_char_pow (p := 2), one_pow]
        ring
      rw [h5] at h1
      simp [Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow] at h1
    · intro h; omega
  · constructor
    · intro h
      have heq : swMk ((1 + Polynomial.X : (ZMod 2)[X]) ^ 6) = swMk 1 := by simpa [swT] using h
      rw [swMk_eq_iff] at heq
      have h2 := heq 2 (by norm_num)
      have h6 : (1 + Polynomial.X : (ZMod 2)[X]) ^ 6 =
          1 + Polynomial.X ^ 2 + Polynomial.X ^ 4 + Polynomial.X ^ 6 := by
        rw [show (6 : ℕ) = 2 ^ 2 + 2 by norm_num, pow_add,
          add_pow_char_pow (p := 2), add_pow_char, one_pow]
        ring
      rw [h6] at h2
      simp [Polynomial.coeff_one, Polynomial.coeff_X_pow] at h2
    · intro h; omega
  · constructor
    · intro h
      have heq : swMk ((1 + Polynomial.X : (ZMod 2)[X]) ^ 7) = swMk 1 := by simpa [swT] using h
      rw [swMk_eq_iff] at heq
      have h1 := heq 1 (by norm_num)
      have h7 : (1 + Polynomial.X : (ZMod 2)[X]) ^ 7 =
          1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 +
            Polynomial.X ^ 4 + Polynomial.X ^ 5 + Polynomial.X ^ 6 + Polynomial.X ^ 7 := by
        rw [show (7 : ℕ) = 2 ^ 2 + 2 + 1 by norm_num, pow_add, pow_add, pow_one,
          add_pow_char_pow (p := 2), add_pow_char, one_pow]
        ring
      rw [h7] at h1
      simp [Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow] at h1
    · intro h; omega

/-! ### 2.2 4-Copy `SO(p)` Theorem (Witten 2016 Eq. 2.18) -/

/-- General oriented 4-copy theorem over any characteristic-2 ring `A`: any polynomial `p : A[X]`
with `w₀ = 1` and `w₁ = 0` satisfies `(swMk p) ^ 4 = 1` in `SW4Ring A`. -/
theorem sw_oriented_pow_four_eq_one {A : Type*} [CommRing A] [CharP A 2]
    (p : A[X]) (hp0 : p.coeff 0 = 1) (hp1 : p.coeff 1 = 0) :
    (swMk p) ^ 4 = 1 := by
  let q : A[X] := p - 1
  have hq0 : q.coeff 0 = 0 := by simp [q, hp0]
  have hq1 : q.coeff 1 = 0 := by simp [q, hp1, Polynomial.coeff_one]
  have hdvd : (Polynomial.X : A[X]) ^ 2 ∣ q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · exact hq0
    · exact hq1
  rcases hdvd with ⟨r, hr⟩
  have hp_eq : p = 1 + Polynomial.X ^ 2 * r := by
    have : p = 1 + q := by simp [q]
    rw [this, hr]
  have hsw : swMk p = 1 + swT ^ 2 * swMk r := by
    rw [hp_eq]
    simp [swMk, swT]
  rw [hsw, show (4 : ℕ) = 2 ^ 2 by norm_num,
    add_pow_char_pow (R := SW4Ring A) 1 (swT ^ 2 * swMk r) 2, one_pow, mul_pow, ← pow_mul,
    show (2 : ℕ) * 2 ^ 2 = 8 by norm_num, swT_pow_eq_zero_of_le (by norm_num), zero_mul,
    add_zero]

/-- **4-copy `SO(p)` Theorem (Witten 2016 §2.5, Eq. 2.18)**:
Any 4 copies of an oriented bundle with `w = 1 + w₂ t² + w₃ t³ + w₄ t⁴` have trivial total
Stiefel–Whitney class `w⁴ = 1` modulo `t⁵`. -/
theorem sw_so_four_copy_trivial {A : Type*} [CommRing A] [CharP A 2] (w₂ w₃ w₄ : A) :
    (1 + swMk (Polynomial.C w₂) * swT ^ 2 + swMk (Polynomial.C w₃) * swT ^ 3 +
      swMk (Polynomial.C w₄) * swT ^ 4) ^ 4 = 1 := by
  let p : A[X] := 1 + Polynomial.C w₂ * Polynomial.X ^ 2 + Polynomial.C w₃ * Polynomial.X ^ 3 +
    Polynomial.C w₄ * Polynomial.X ^ 4
  have hp0 : p.coeff 0 = 1 := by simp [p]
  have hp1 : p.coeff 1 = 0 := by simp [p, Polynomial.coeff_one]
  simpa [p, swT] using sw_oriented_pow_four_eq_one p hp0 hp1

/-! ### 2.3 Mod-4 `U(1)` Theorem, `ℝℙ⁴` Phase Check, and `U(2)` Comparison (Eqs. 2.10–2.19) -/

/-- Number of odd charges `#{i | Odd (n i)}` in a `U(1)` charge tuple `n : Fin k → ℤ`. -/
def oddChargeCount {k : ℕ} (n : Fin k → ℤ) : ℕ :=
  (Finset.univ.filter fun i => Odd (n i)).card

/-- Canonical ring homomorphism `ZMod 2 →+* A` for any characteristic-2 ring `A`. -/
def zmod2CastHom (A : Type*) [CommRing A] [CharP A 2] : ZMod 2 →+* A :=
  ZMod.castHom (dvd_refl 2) A

/-- Total Stiefel–Whitney class `∏ i, (1 + (n_i mod 2) c₁ t²)` in `SW4Ring A` for a direct
sum `⨁_{i=1}^k V_{n_i}` of `U(1)` charge-`n_i` complex line bundles (Witten Eqs. 2.10–2.13). -/
def u1TotalSW {A : Type*} [CommRing A] [CharP A 2] (c₁ : A) {k : ℕ} (n : Fin k → ℤ) :
    SW4Ring A :=
  ∏ i : Fin k, (1 + swMk (Polynomial.C (zmod2CastHom A (n i : ZMod 2) * c₁)) * swT ^ 2)

private theorem u1TotalSW_finset_expand {A : Type*} [CommRing A] [CharP A 2] (c₁ : A)
    {k : ℕ} (n : Fin k → ℤ) (s : Finset (Fin k)) :
    (∏ i ∈ s, (1 + swMk (Polynomial.C (zmod2CastHom A (n i : ZMod 2) * c₁)) * swT ^ 2)) =
      1 +
        swMk (Polynomial.C (zmod2CastHom A (∑ i ∈ s, (n i : ZMod 2)) * c₁)) * swT ^ 2 +
        swMk (Polynomial.C (zmod2CastHom A
          (∑ p ∈ (s ×ˢ s).filter (fun p : Fin k × Fin k => p.1 < p.2),
            (n p.1 * n p.2 : ZMod 2)) * c₁ ^ 2)) * swT ^ 4 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, ih]
      have hsum : ∑ i ∈ insert a s, (n i : ZMod 2) = (n a : ZMod 2) + ∑ i ∈ s, (n i : ZMod 2) :=
        Finset.sum_insert ha
      have hpair :
          ((insert a s) ×ˢ (insert a s)).filter (fun p : Fin k × Fin k => p.1 < p.2) =
            (s ×ˢ s).filter (fun p : Fin k × Fin k => p.1 < p.2) ∪
              (s.filter fun i => a < i).map ⟨fun i => (a, i), fun _ _ h => (Prod.ext_iff.mp h).2⟩ ∪
              (s.filter fun i => i < a).map ⟨fun i => (i, a), fun _ _ h => (Prod.ext_iff.mp h).1⟩ := by
        ext ⟨u, v⟩
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
          Finset.mem_map]
        constructor
        · rintro ⟨⟨rfl | hu, rfl | hv⟩, huv⟩
          · exact False.elim (lt_irrefl _ huv)
          · left; right; exact ⟨v, ⟨hv, huv⟩, rfl⟩
          · right; exact ⟨u, ⟨hu, huv⟩, rfl⟩
          · left; left; exact ⟨⟨hu, hv⟩, huv⟩
        · rintro ((⟨⟨hu, hv⟩, huv⟩ | ⟨i, ⟨hi, hai⟩, h⟩) | ⟨i, ⟨hi, hia⟩, h⟩)
          · exact ⟨⟨Or.inr hu, Or.inr hv⟩, huv⟩
          · rcases Prod.ext_iff.mp h with ⟨rfl, rfl⟩
            exact ⟨⟨Or.inl rfl, Or.inr hi⟩, hai⟩
          · rcases Prod.ext_iff.mp h with ⟨rfl, rfl⟩
            exact ⟨⟨Or.inr hi, Or.inl rfl⟩, hia⟩
      have hd1 : Disjoint
          ((s ×ˢ s).filter (fun p : Fin k × Fin k => p.1 < p.2))
          ((s.filter fun i => a < i).map
            ⟨fun i => (a, i), fun _ _ h => (Prod.ext_iff.mp h).2⟩) := by
        rw [Finset.disjoint_left]
        rintro ⟨u, v⟩ huv hmap
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_map] at huv hmap
        rcases hmap with ⟨i, _, h⟩
        rcases Prod.ext_iff.mp h with ⟨rfl, _⟩
        exact ha huv.1.1
      have hd2 : Disjoint
          ((s ×ˢ s).filter (fun p : Fin k × Fin k => p.1 < p.2) ∪
            (s.filter fun i => a < i).map
              ⟨fun i => (a, i), fun _ _ h => (Prod.ext_iff.mp h).2⟩)
          ((s.filter fun i => i < a).map
            ⟨fun i => (i, a), fun _ _ h => (Prod.ext_iff.mp h).1⟩) := by
        rw [Finset.disjoint_left]
        rintro ⟨u, v⟩ huv hmap
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product,
          Finset.mem_map] at huv hmap
        rcases hmap with ⟨i, ⟨hi, hia⟩, h⟩
        rcases Prod.ext_iff.mp h with ⟨rfl, rfl⟩
        rcases huv with huv | ⟨j, _, hj⟩
        · exact ha huv.1.2
        · rcases Prod.ext_iff.mp hj with ⟨rfl, _⟩
          exact lt_asymm hia hia
      have hpairSum :
          (∑ p ∈ ((insert a s) ×ˢ (insert a s)).filter (fun p : Fin k × Fin k => p.1 < p.2),
            (n p.1 * n p.2 : ZMod 2)) =
          (∑ p ∈ (s ×ˢ s).filter (fun p : Fin k × Fin k => p.1 < p.2), (n p.1 * n p.2 : ZMod 2)) +
            (n a : ZMod 2) * (∑ i ∈ s, (n i : ZMod 2)) := by
        rw [hpair, Finset.sum_union hd2, Finset.sum_union hd1, Finset.sum_map, Finset.sum_map]
        have hpart : s = s.filter (fun i => a < i) ∪ s.filter (fun i => i < a) := by
          ext i
          simp only [Finset.mem_union, Finset.mem_filter]
          constructor
          · intro hi
            rcases lt_trichotomy a i with hlt | rfl | hgt
            · exact Or.inl ⟨hi, hlt⟩
            · exact False.elim (ha hi)
            · exact Or.inr ⟨hi, hgt⟩
          · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
        have hdlt : Disjoint (s.filter fun i => a < i) (s.filter fun i => i < a) := by
          rw [Finset.disjoint_left]
          intro i h1 h2
          simp only [Finset.mem_filter] at h1 h2
          exact lt_asymm h1.2 h2.2
        have hsSum : ∑ i ∈ s, (n i : ZMod 2) =
            (∑ i ∈ s.filter (fun i => a < i), (n i : ZMod 2)) +
              (∑ i ∈ s.filter (fun i => i < a), (n i : ZMod 2)) := by
          conv_lhs => rw [hpart, Finset.sum_union hdlt]
        rw [hsSum, mul_add]
        simp only [Finset.mul_sum]
        have he1 :
            (∑ x ∈ s.filter (fun i => a < i),
              (n ((⟨fun i => (a, i), fun _ _ h => (Prod.ext_iff.mp h).2⟩ :
                Fin k ↪ Fin k × Fin k) x).1 : ZMod 2) *
              (n ((⟨fun i => (a, i), fun _ _ h => (Prod.ext_iff.mp h).2⟩ :
                Fin k ↪ Fin k × Fin k) x).2 : ZMod 2)) =
              ∑ i ∈ s.filter (fun i => a < i), (n a : ZMod 2) * (n i : ZMod 2) :=
          Finset.sum_congr rfl fun _ _ => rfl
        have he2 :
            (∑ x ∈ s.filter (fun i => i < a),
              (n ((⟨fun i => (i, a), fun _ _ h => (Prod.ext_iff.mp h).1⟩ :
                Fin k ↪ Fin k × Fin k) x).1 : ZMod 2) *
              (n ((⟨fun i => (i, a), fun _ _ h => (Prod.ext_iff.mp h).1⟩ :
                Fin k ↪ Fin k × Fin k) x).2 : ZMod 2)) =
              ∑ i ∈ s.filter (fun i => i < a), (n a : ZMod 2) * (n i : ZMod 2) :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
        rw [he1, he2]
        ring
      rw [hsum, hpairSum]
      set α : A := zmod2CastHom A (n a : ZMod 2)
      set σ : A := zmod2CastHom A (∑ i ∈ s, (n i : ZMod 2))
      set π : A := zmod2CastHom A
        (∑ p ∈ (s ×ˢ s).filter (fun p : Fin k × Fin k => p.1 < p.2), (n p.1 * n p.2 : ZMod 2))
      have ht6 : (swT : SW4Ring A) ^ 2 * (swT : SW4Ring A) ^ 4 = 0 := by
        rw [← pow_add]
        exact swT_pow_eq_zero_of_le (by norm_num)
      have ht4 : (swT : SW4Ring A) ^ 2 * (swT : SW4Ring A) ^ 2 = swT ^ 4 := by
        rw [← pow_add]
      have hαc : zmod2CastHom A ((n a : ZMod 2) + ∑ i ∈ s, (n i : ZMod 2)) = α + σ :=
        map_add _ _ _
      have hπc : zmod2CastHom A
          ((∑ p ∈ (s ×ˢ s).filter (fun p : Fin k × Fin k => p.1 < p.2),
            (n p.1 * n p.2 : ZMod 2)) + (n a : ZMod 2) * ∑ i ∈ s, (n i : ZMod 2)) =
          π + α * σ := by
        rw [map_add, map_mul]
      rw [hαc, hπc]
      calc
        (1 + swMk (Polynomial.C (α * c₁)) * swT ^ 2) *
            (1 + swMk (Polynomial.C (σ * c₁)) * swT ^ 2 +
              swMk (Polynomial.C (π * c₁ ^ 2)) * swT ^ 4)
            = 1 + (swMk (Polynomial.C (α * c₁)) + swMk (Polynomial.C (σ * c₁))) * swT ^ 2 +
                (swMk (Polynomial.C (π * c₁ ^ 2)) * swT ^ 4 +
                  swMk (Polynomial.C (α * c₁)) * swMk (Polynomial.C (σ * c₁)) *
                    (swT ^ 2 * swT ^ 2)) +
                swMk (Polynomial.C (α * c₁)) * swMk (Polynomial.C (π * c₁ ^ 2)) *
                  (swT ^ 2 * swT ^ 4) := by ring
        _ = 1 + swMk (Polynomial.C ((α + σ) * c₁)) * swT ^ 2 +
              swMk (Polynomial.C ((π + α * σ) * c₁ ^ 2)) * swT ^ 4 := by
            rw [ht4, ht6, mul_zero, add_zero]
            have h1 : swMk (Polynomial.C (α * c₁)) + swMk (Polynomial.C (σ * c₁)) =
                swMk (Polynomial.C ((α + σ) * c₁)) := by
              rw [← map_add, ← Polynomial.C_add, add_mul]
            have h2 : swMk (Polynomial.C (π * c₁ ^ 2)) * swT ^ 4 +
                swMk (Polynomial.C (α * c₁)) * swMk (Polynomial.C (σ * c₁)) * swT ^ 4 =
                swMk (Polynomial.C ((π + α * σ) * c₁ ^ 2)) * swT ^ 4 := by
              rw [← add_mul, ← map_mul, ← map_add, ← Polynomial.C_mul, ← Polynomial.C_add]
              congr 2
              ring
            rw [h1, h2]

private theorem zmod2_sum_eq_oddChargeCount {k : ℕ} (n : Fin k → ℤ) :
    (∑ i : Fin k, (n i : ZMod 2)) = (oddChargeCount n : ZMod 2) := by
  have hite : ∀ i : Fin k, (n i : ZMod 2) = if Odd (n i) then 1 else 0 := by
    intro i
    rcases Int.even_or_odd (n i) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hne : ¬ Odd (n i) := by
        rw [hm, ← two_mul]
        exact Int.not_odd_iff_even.mpr (even_two_mul m)
      simp only [hne, ↓reduceIte]
      rw [hm, ← two_mul]
      push_cast
      have : (2 : ZMod 2) = 0 := by decide
      rw [this, zero_mul]
    · have hod : Odd (n i) := ⟨m, hm⟩
      simp only [hod, ↓reduceIte]
      rw [hm]
      push_cast
      have : (2 : ZMod 2) = 0 := by decide
      rw [this, zero_mul, zero_add]
  simp_rw [hite, Finset.sum_boole, oddChargeCount]

private theorem zmod2_pair_sum_eq_choose_two {k : ℕ} (n : Fin k → ℤ) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
      (n p.1 * n p.2 : ZMod 2)) = ((oddChargeCount n).choose 2 : ZMod 2) := by
  let S := Finset.univ.filter (fun i : Fin k => Odd (n i))
  have hfilt :
      (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)).filter
        (fun p : Fin k × Fin k => Odd (n p.1) ∧ Odd (n p.2)) =
      (S ×ˢ S).filter (fun p : Fin k × Fin k => p.1 < p.2) := by
    ext ⟨i, j⟩
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    tauto
  have hprod : ∀ p : Fin k × Fin k,
      (n p.1 * n p.2 : ZMod 2) = if Odd (n p.1) ∧ Odd (n p.2) then 1 else 0 := by
    intro p
    have hi : (n p.1 : ZMod 2) = if Odd (n p.1) then 1 else 0 := by
      rcases Int.even_or_odd (n p.1) with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hne : ¬ Odd (n p.1) := by
          rw [hm, ← two_mul]; exact Int.not_odd_iff_even.mpr (even_two_mul m)
        simp only [hne, ↓reduceIte]; rw [hm, ← two_mul]; push_cast
        have : (2 : ZMod 2) = 0 := by decide
        rw [this, zero_mul]
      · have hod : Odd (n p.1) := ⟨m, hm⟩
        simp only [hod, ↓reduceIte]; rw [hm]; push_cast
        have : (2 : ZMod 2) = 0 := by decide
        rw [this, zero_mul, zero_add]
    have hj : (n p.2 : ZMod 2) = if Odd (n p.2) then 1 else 0 := by
      rcases Int.even_or_odd (n p.2) with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hne : ¬ Odd (n p.2) := by
          rw [hm, ← two_mul]; exact Int.not_odd_iff_even.mpr (even_two_mul m)
        simp only [hne, ↓reduceIte]; rw [hm, ← two_mul]; push_cast
        have : (2 : ZMod 2) = 0 := by decide
        rw [this, zero_mul]
      · have hod : Odd (n p.2) := ⟨m, hm⟩
        simp only [hod, ↓reduceIte]; rw [hm]; push_cast
        have : (2 : ZMod 2) = 0 := by decide
        rw [this, zero_mul, zero_add]
    rw [hi, hj]
    by_cases h1 : Odd (n p.1) <;> by_cases h2 : Odd (n p.2) <;> simp [h1, h2]
  simp_rw [hprod, Finset.sum_boole, hfilt]
  have hcard : ((S ×ˢ S).filter (fun p : Fin k × Fin k => p.1 < p.2)).card = S.card.choose 2 := by
    have hbij : ((S ×ˢ S).filter (fun p : Fin k × Fin k => p.1 < p.2)).card =
        (S.powersetCard 2).card := by
      refine Finset.card_bij (fun p _ => ({p.1, p.2} : Finset (Fin k))) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product] at hp
        rw [Finset.mem_powersetCard]
        refine ⟨?_, Finset.card_pair (ne_of_lt hp.2)⟩
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> [exact hp.1.1; exact hp.1.2]
      · intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
        simp only [Finset.mem_filter, Finset.mem_product] at h₁ h₂
        have ha₁ : a₁ ∈ ({a₂, b₂} : Finset (Fin k)) := heq ▸ Finset.mem_insert_self a₁ {b₁}
        have hb₁ : b₁ ∈ ({a₂, b₂} : Finset (Fin k)) :=
          heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b₁)
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha₁ hb₁
        rcases ha₁ with rfl | rfl <;> rcases hb₁ with rfl | rfl
        · exact False.elim (lt_irrefl _ h₁.2)
        · rfl
        · exact False.elim (lt_asymm h₁.2 h₂.2)
        · exact False.elim (lt_irrefl _ h₁.2)
      · intro t ht
        rw [Finset.mem_powersetCard] at ht
        rcases Finset.card_eq_two.mp ht.2 with ⟨x, y, hxy, rfl⟩
        rcases lt_or_gt_of_ne hxy with hlt | hgt
        · refine ⟨(x, y), ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨ht.1 (Finset.mem_insert_self x {y}),
            ht.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))⟩, hlt⟩
        · refine ⟨(y, x), ?_, Finset.pair_comm y x⟩
          simp only [Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨ht.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)),
            ht.1 (Finset.mem_insert_self x {y})⟩, hgt⟩
    rw [hbij, Finset.card_powersetCard]
  rw [hcard]
  rfl

/-- Explicit Whitney-sum expansion of `u1TotalSW c₁ n` (Witten 2016 Eq. 2.13–2.14). -/
theorem u1TotalSW_eq_expand {A : Type*} [CommRing A] [CharP A 2] (c₁ : A) {k : ℕ}
    (n : Fin k → ℤ) :
    u1TotalSW c₁ n =
      1 +
        swMk (Polynomial.C (zmod2CastHom A (oddChargeCount n : ZMod 2) * c₁)) * swT ^ 2 +
        swMk (Polynomial.C (zmod2CastHom A ((oddChargeCount n).choose 2 : ZMod 2) * c₁ ^ 2)) *
          swT ^ 4 := by
  unfold u1TotalSW
  rw [u1TotalSW_finset_expand c₁ n Finset.univ, Finset.univ_product_univ,
    zmod2_sum_eq_oddChargeCount n, zmod2_pair_sum_eq_choose_two n]

private theorem zmod2_self_and_choose_two_eq_zero_iff_four_dvd (y : ℕ) :
    ((y : ZMod 2) = 0 ∧ ((y.choose 2 : ℕ) : ZMod 2) = 0) ↔ 4 ∣ y := by
  have hy : y = 4 * (y / 4) + y % 4 := (Nat.div_add_mod y 4).symm
  have h1 : (y : ZMod 2) = ((y % 4 : ℕ) : ZMod 2) := by
    conv_lhs => rw [hy]
    push_cast
    have h4 : (4 : ZMod 2) = 0 := by decide
    rw [h4, zero_mul, zero_add]
  have h2 : ((y.choose 2 : ℕ) : ZMod 2) = (((y % 4).choose 2 : ℕ) : ZMod 2) := by
    have hch : ∀ m : ℕ, m.choose 2 * 2 = m * (m - 1) := by
      intro m
      rw [Nat.choose_two_right, Nat.div_mul_cancel]
      exact Nat.even_mul_pred_self m |>.two_dvd
    have hmod4 : y * (y - 1) % 4 = (y % 4) * ((y % 4) - 1) % 4 := by
      set q := y / 4
      set r := y % 4
      have hr : r < 4 := Nat.mod_lt y (by norm_num)
      rcases r with _ | r'
      · simp only [add_zero] at hy
        rw [hy]
        rcases q with _ | q'
        · simp
        · rw [show 4 * (q' + 1) * (4 * (q' + 1) - 1) = 4 * ((q' + 1) * (4 * (q' + 1) - 1)) by ring]
          simp
      · have hsub : 4 * q + (r' + 1) - 1 = 4 * q + r' := by omega
        rw [hy, hsub]
        rw [show (4 * q + (r' + 1)) * (4 * q + r') =
          4 * (4 * q * q + q * (2 * r' + 1)) + (r' + 1) * r' by ring]
        simp [show r' + 1 - 1 = r' by omega]
    have hmul2 : y.choose 2 % 2 = (y % 4).choose 2 % 2 := by
      have hm1 := hch y
      have hm2 := hch (y % 4)
      have hm1' : y.choose 2 * 2 % 4 = y * (y - 1) % 4 := by rw [hm1]
      have hm2' : (y % 4).choose 2 * 2 % 4 = (y % 4) * ((y % 4) - 1) % 4 := by rw [hm2]
      omega
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, hmul2]
  rw [h1, h2, Nat.dvd_iff_mod_eq_zero]
  have hrlt : y % 4 < 4 := Nat.mod_lt y (by norm_num)
  generalize y % 4 = r at hrlt ⊢
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr with rfl | rfl | rfl | rfl <;> decide

/-- Sufficient direction of the mod-4 `U(1)` theorem for any characteristic-2 ring `A` and
any `c₁ : A`. -/
theorem sw_u1_stably_trivial_of_four_dvd {A : Type*} [CommRing A] [CharP A 2] (c₁ : A)
    {k : ℕ} (n : Fin k → ℤ) (hdvd : 4 ∣ oddChargeCount n) :
    u1TotalSW c₁ n = 1 := by
  have hpair := (zmod2_self_and_choose_two_eq_zero_iff_four_dvd (oddChargeCount n)).mpr hdvd
  rw [u1TotalSW_eq_expand, hpair.1, hpair.2]
  simp

/-- **Mod-4 `U(1)` Theorem (Witten 2016 §2.5, Eqs. 2.10–2.15)**:
For `y = #{odd n_i}` and any `c₁ : A` with `c₁² ≠ 0` (e.g. `c₁ = 1 : ZMod 2` on `ℝℙ⁴`),
the total Stiefel–Whitney class `u1TotalSW c₁ n` is trivial modulo `t⁵` iff `4 ∣ y`. -/
theorem sw_u1_stably_trivial_iff_four_dvd {A : Type*} [CommRing A] [CharP A 2] (c₁ : A)
    (hc₁ : c₁ ^ 2 ≠ 0) {k : ℕ} (n : Fin k → ℤ) :
    u1TotalSW c₁ n = 1 ↔ 4 ∣ oddChargeCount n := by
  constructor
  · intro h
    rw [u1TotalSW_eq_expand] at h
    have hpoly :
        swMk (1 + Polynomial.C (zmod2CastHom A (oddChargeCount n : ZMod 2) * c₁) * Polynomial.X ^ 2 +
          Polynomial.C (zmod2CastHom A ((oddChargeCount n).choose 2 : ZMod 2) * c₁ ^ 2) *
            Polynomial.X ^ 4) = swMk 1 := by
      simpa [swT] using h
    rw [swMk_eq_iff] at hpoly
    have hd2 := hpoly 2 (by norm_num)
    have hd4 := hpoly 4 (by norm_num)
    simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X_pow] at hd2 hd4
    have hA1 : zmod2CastHom A (oddChargeCount n : ZMod 2) * c₁ = 0 := by
      simpa using hd2
    have hA2 : zmod2CastHom A ((oddChargeCount n).choose 2 : ZMod 2) * c₁ ^ 2 = 0 := by
      simpa using hd4
    have hc1_ne : c₁ ≠ 0 := fun hz => hc₁ (by rw [hz]; simp)
    have hzmod2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by
      intro z
      rw [← ZMod.natCast_zmod_val z]
      have hv : z.val = 0 ∨ z.val = 1 := by have := ZMod.val_lt z; omega
      rcases hv with h0 | h1
      · left; simp [h0]
      · right; simp [h1]
    have hz1 : (oddChargeCount n : ZMod 2) = 0 := by
      rcases hzmod2 (oddChargeCount n : ZMod 2) with h0 | h1
      · exact h0
      · exfalso
        rw [h1, map_one, _root_.one_mul] at hA1
        exact hc1_ne hA1
    have hz2 : ((oddChargeCount n).choose 2 : ZMod 2) = 0 := by
      rcases hzmod2 ((oddChargeCount n).choose 2 : ZMod 2) with h0 | h1
      · exact h0
      · exfalso
        rw [h1, map_one, _root_.one_mul] at hA2
        exact hc₁ hA2
    exact (zmod2_self_and_choose_two_eq_zero_iff_four_dvd (oddChargeCount n)).mp ⟨hz1, hz2⟩
  · exact sw_u1_stably_trivial_of_four_dvd c₁ n

/-- **`ℝℙ⁴` `η`-Phase Quantization (Witten 2016 §2.5, Eq. 2.16)**:
For `k` Dirac fermions on `ℝℙ⁴` with `y` odd-charge fermions under a flat `ℤ/2 ⊂ U(1)` bundle,
the `η`-phase `exp(-iπ η_R / 2)` matches the trivial-bundle phase iff `4 ∣ y`. -/
theorem rp4_u1_eta_phase_trivial_iff_four_dvd (k y : ℕ) :
    Circle.exp (-(((2 * (k : ℤ) - 4 * (y : ℤ) : ℤ) : ℝ) * (2 * Real.pi) / 16)) =
      Circle.exp (-(((2 * (k : ℤ) : ℤ) : ℝ) * (2 * Real.pi) / 16)) ↔
      4 ∣ y := by
  rw [Circle.exp_eq_exp]
  constructor
  · rintro ⟨m, hm⟩
    push_cast at hm
    have hdiff : (4 * (y : ℝ)) / 16 * (2 * Real.pi) = (m : ℝ) * (2 * Real.pi) := by
      linarith
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    have hq : (4 * (y : ℝ)) / 16 = (m : ℝ) := mul_right_cancel₀ hpi hdiff
    have hz : (y : ℤ) = 4 * m := by
      have hr : (y : ℝ) = (4 : ℝ) * (m : ℝ) := by linarith
      exact_mod_cast hr
    refine ⟨m.toNat, ?_⟩
    omega
  · rintro ⟨q, hq⟩
    refine ⟨(q : ℤ), ?_⟩
    have hq' : (y : ℝ) = 4 * (q : ℝ) := by exact_mod_cast hq
    push_cast
    rw [hq']
    ring

/-- **2-copy `U(2) → U(1)` Obstruction vs. 4-copy Cancellation (Witten 2016 Eq. 2.19)**:
Two copies of the fundamental `2` of `U(2)` restrict along `diag(e^{iθ}, 1)` to charges
`(1, 1, 0, 0)` with `y = 2`, which fails `4 ∣ y`; four copies `(1, 1, 1, 1, 0, 0, 0, 0)` have
`y = 4` and are anomaly-free. -/
theorem u2_two_copy_vs_four_copy :
    let twoCopy : Fin 4 → ℤ := ![1, 1, 0, 0]
    let fourCopy : Fin 8 → ℤ := ![1, 1, 1, 1, 0, 0, 0, 0]
    oddChargeCount twoCopy = 2 ∧
      u1TotalSW (1 : ZMod 2) twoCopy ≠ 1 ∧
      oddChargeCount fourCopy = 4 ∧
      u1TotalSW (1 : ZMod 2) fourCopy = 1 := by
  intro twoCopy fourCopy
  have hc2 : oddChargeCount twoCopy = 2 := by
    simp [oddChargeCount, twoCopy]
    decide
  have hc4 : oddChargeCount fourCopy = 4 := by
    simp [oddChargeCount, fourCopy]
    decide
  have h1sq : (1 : ZMod 2) ^ 2 ≠ 0 := by decide
  refine ⟨hc2, ?_, hc4, ?_⟩
  · rw [ne_eq, sw_u1_stably_trivial_iff_four_dvd (1 : ZMod 2) h1sq twoCopy, hc2]
    decide
  · exact sw_u1_stably_trivial_of_four_dvd (1 : ZMod 2) fourCopy (by rw [hc4])

end StiefelWhitneyAlgebra

end InfoGeometry.Topology.WittenParityAnomalyQuantization
