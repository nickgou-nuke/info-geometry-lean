/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.WittenParityAnomalyQuantization
import InfoGeometry.CondensedMatter.DIIISuperfluid
import InfoGeometry.Canonical.WittenParityAnomalyBridge
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Witten (2016) §3: Boundary Symmetry Extensions, `ν mod 16`, Monopoles, and SPT Pullback

This module formalizes the 3+1D topological superconductor boundary and SPT pullback theorems
of Edward Witten, *"The 'Parity' Anomaly on an Unorientable Manifold"* (2016), §3:

1. **Boundary symmetry group extension `1 → K → H → ℤ₄ᵀ → 1` (Witten §3.1, Eqs. 3.1–3.6)**:
   - `BoundarySymmetryExtension K H` models `T'² = (-1)^F K` (`tPrime ^ 2 = fermionParity * incl kUnbroken`)
     and proves the splitting obstruction (`boundaryExtension_no_fermionParity_preserving_lift` and
     `boundaryExtension_no_splitting`), inhabited by the non-split extension
     `1 → ℤ/4 → ℤ/8 × ℤ/2 → ℤ/4 → 1` (`canonicalZ4Extension`).
   - `MajoranaYukawaBoundaryDatum` and `boundary_trivial_K_forces_sixteen_dvd` prove that when
     `K = 1`, a nondegenerate `K_{1/2}`-odd Yukawa pairing pairs `ℤ/2`-even and `ℤ/2`-odd
     Majorana modes (`ν = 2 n_odd`), and `sw_z2_mod_eight_iff` forces `8 ∣ n_odd`, hence
     `16 ∣ ν` (`WittenParityAnomalyBridge.AnomalyFree ν`, linked to
     `DIIISuperfluid.DIIITopologicalRegime.threeDimensionalInteractingZ16`), inhabited by
     `canonicalNu16YukawaModel`.

2. **`S²` monopole spin / Kramers-singlet quantization (Witten §3.2.2, Eqs. 3.13–3.16)**:
   - `monopole_lowest_charge_integral_iff_even` (`2 ∣ 2q ↔ Even y`),
     `monopole_tPrime_exponent_mod_two`, and `monopole_kramers_singlet_iff_four_dvd` prove that
     monopole spin-statistics compatibility holds iff `4 ∣ y`, matching `u1TotalSW` in
     `WittenParityAnomalyQuantization`.

3. **Bosonic SPT group-cohomology pullback trivialization (Witten §3.3, Eqs. 3.19–3.24)**:
   - Using Mathlib's `groupCohomology (Rep.trivial ℤ G UnitAddCircle) D` and
     `groupCohomology.map`, proves the fiber-restriction vanishing `pullback_restrict_fiber_eq_zero`,
     the boundary-lift trivialization law `boundary_lift_pullback_trivial` (Eq. 3.24),
     the `H^{D-1}(H, U(1))` trivialization torsor & boundary `K`-cocycle lemmas, and the
     explicit nontrivial `D = 3` pullback trivialization on `0 → ℤ/2 → ℤ/4 → ℤ/2 → 0`
     (`z2CubicClass_ne_zero`, `z2_to_z4_spt_pullback_trivial`, Eq. 3.22).

Long-term Mathlib frontier: smooth 2+1D boundary Chern–Simons / topological quantum field
theories, `S²` radial-quantization Dirac operator zero-mode indices, and the full cobordism
classification `Ω_4^{Pin^+} ≅ ℤ/16` lie beyond current Mathlib `v4.34.1` and are scoped here
to exact group extensions, bilinear Yukawa pairings, monopole zero-mode arithmetic, and
Mathlib `groupCohomology` functoriality.
-/

noncomputable section

set_option autoImplicit false

namespace InfoGeometry.CondensedMatter.WittenBoundaryExtension16

open InfoGeometry.Topology.WittenParityAnomalyQuantization
open InfoGeometry.CondensedMatter.DIIISuperfluid
open InfoGeometry.Canonical.WittenParityAnomalyBridge

/-! ## Section 1: Boundary Symmetry Extension & `K = 1 → 16 ∣ ν` (Witten §3.1) -/

section BoundaryExtension

/-- Bulk fermionic time-reversal group `ℤ₄ᵀ = {1, T, (-1)^F, T(-1)^F}`. -/
abbrev BulkTimeReversalGroup : Type := Multiplicative (ZMod 4)

/-- Boundary symmetry group extension `1 → K → H → ℤ₄ᵀ → 1` with `T'² = (-1)^F K`
(Witten 2016 §3.1, Eqs. 3.4–3.6). -/
structure BoundarySymmetryExtension (K H : Type*) [Group K] [Group H] where
  incl : K →* H
  proj : H →* BulkTimeReversalGroup
  incl_injective : Function.Injective incl
  proj_surjective : Function.Surjective proj
  exact_ker : incl.range = proj.ker
  fermionParity : H
  fermionParity_proj : proj fermionParity = Multiplicative.ofAdd (2 : ZMod 4)
  fermionParity_sq : fermionParity ^ 2 = 1
  tPrime : H
  tPrime_proj : proj tPrime = Multiplicative.ofAdd (1 : ZMod 4)
  kUnbroken : K
  tPrime_sq : tPrime ^ 2 = fermionParity * incl kUnbroken

/-- If `E.kUnbroken * k² ≠ 1` for every `k : K` in an abelian boundary extension `H`,
no lift `T̃` of `T` satisfies `T̃² = (-1)^F` (Witten 2016 Eq. 3.6). -/
theorem boundaryExtension_no_fermionParity_preserving_lift
    {K H : Type*} [Group K] [CommGroup H]
    (E : BoundarySymmetryExtension K H)
    (hobs : ∀ k : K, E.kUnbroken * k ^ 2 ≠ 1) :
    ∀ Ttilde : H, E.proj Ttilde = Multiplicative.ofAdd (1 : ZMod 4) →
      Ttilde ^ 2 ≠ E.fermionParity := by
  intro Ttilde hproj hsq
  have hker : Ttilde * E.tPrime⁻¹ ∈ E.proj.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hproj, E.tPrime_proj, mul_inv_cancel]
  rw [← E.exact_ker] at hker
  rcases hker with ⟨k, hk⟩
  have hT : Ttilde = E.tPrime * E.incl k := by
    have hT' : Ttilde = E.incl k * E.tPrime := eq_mul_of_mul_inv_eq hk.symm
    rw [hT', mul_comm]
  have hcalc : Ttilde ^ 2 = E.fermionParity * E.incl (E.kUnbroken * k ^ 2) := by
    rw [hT, mul_pow, E.tPrime_sq, map_mul, map_pow]
    ac_rfl
  rw [hsq] at hcalc
  have hincl1 : E.incl (E.kUnbroken * k ^ 2) = 1 := by
    have hmul := congrArg (fun x => E.fermionParity⁻¹ * x) hcalc
    simpa [← mul_assoc] using hmul.symm
  have hk1 : E.kUnbroken * k ^ 2 = 1 := E.incl_injective (by simpa [map_one] using hincl1)
  exact hobs k hk1

/-- Strong splitting obstruction: if `(E.kUnbroken * k²)² ≠ 1` for every `k : K` in an abelian
boundary extension `H`, then no lift `T̃` of `T` has order dividing `4`, so `1 → K → H → ℤ₄ᵀ → 1`
has no group-homomorphism splitting whatsoever. -/
theorem boundaryExtension_no_splitting
    {K H : Type*} [Group K] [CommGroup H]
    (E : BoundarySymmetryExtension K H)
    (hobs : ∀ k : K, (E.kUnbroken * k ^ 2) ^ 2 ≠ 1) :
    ¬ ∃ s : BulkTimeReversalGroup →* H, E.proj.comp s = MonoidHom.id BulkTimeReversalGroup := by
  rintro ⟨s, hs⟩
  let Ttilde : H := s (Multiplicative.ofAdd (1 : ZMod 4))
  have hproj : E.proj Ttilde = Multiplicative.ofAdd (1 : ZMod 4) := by
    change (E.proj.comp s) (Multiplicative.ofAdd (1 : ZMod 4)) = _
    rw [hs]
    rfl
  have h4 : Ttilde ^ 4 = 1 := by
    dsimp [Ttilde]
    rw [← map_pow]
    have hpow4 : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 4 = 1 := by decide
    rw [hpow4, map_one]
  have hker : Ttilde * E.tPrime⁻¹ ∈ E.proj.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hproj, E.tPrime_proj, mul_inv_cancel]
  rw [← E.exact_ker] at hker
  rcases hker with ⟨k, hk⟩
  have hT : Ttilde = E.tPrime * E.incl k := by
    have hT' : Ttilde = E.incl k * E.tPrime := eq_mul_of_mul_inv_eq hk.symm
    rw [hT', mul_comm]
  have hsq : Ttilde ^ 2 = E.fermionParity * E.incl (E.kUnbroken * k ^ 2) := by
    rw [hT, mul_pow, E.tPrime_sq, map_mul, map_pow]
    ac_rfl
  have h4' : Ttilde ^ 4 = E.incl ((E.kUnbroken * k ^ 2) ^ 2) := by
    calc
      Ttilde ^ 4 = (Ttilde ^ 2) ^ 2 := by
            rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      _ = (E.fermionParity * E.incl (E.kUnbroken * k ^ 2)) ^ 2 := by rw [hsq]
      _ = E.fermionParity ^ 2 * (E.incl (E.kUnbroken * k ^ 2)) ^ 2 := by rw [mul_pow]
      _ = E.incl ((E.kUnbroken * k ^ 2) ^ 2) := by
            rw [E.fermionParity_sq, one_mul, ← map_pow]
  rw [h4] at h4'
  have hk1 : (E.kUnbroken * k ^ 2) ^ 2 = 1 := E.incl_injective (by simpa [map_one] using h4'.symm)
  exact hobs k hk1

/-- Majorana boundary Yukawa datum with trivial residual extension (`K = 1`, Witten §3.1 Eq. 3.5):
`kHalf` satisfies `kHalf² = 1`, `yukawaForm` is nondegenerate and `kHalf`-odd, and the
`ℤ/2`-odd sector is `ℤ/2`-anomaly-free (`(1 + swT) ^ dim V_- = 1` in `SW4Ring (ZMod 2)`). -/
structure MajoranaYukawaBoundaryDatum where
  V : Type*
  [addCommGroup : AddCommGroup V]
  [module : Module ℝ V]
  [finiteDim : FiniteDimensional ℝ V]
  kHalf : V →ₗ[ℝ] V
  kHalf_sq : kHalf ^ 2 = 1
  yukawaForm : LinearMap.BilinForm ℝ V
  yukawa_nondegenerate : yukawaForm.Nondegenerate
  yukawa_kHalf_odd : ∀ u v : V, yukawaForm (kHalf u) (kHalf v) = -yukawaForm u v
  z2_anomaly_free :
    (1 + swT : SW4Ring (ZMod 2)) ^
      Module.finrank ℝ (LinearMap.ker (kHalf + LinearMap.id)) = 1

attribute [instance] MajoranaYukawaBoundaryDatum.addCommGroup
attribute [instance] MajoranaYukawaBoundaryDatum.module
attribute [instance] MajoranaYukawaBoundaryDatum.finiteDim

/-- **Witten (2016) §3.1 Eq. (3.5)**: When `K = 1` (`kHalf² = 1`), the `kHalf`-odd Yukawa
pairing forces `dim V_+ = dim V_-` (`ν = 2 n_odd`), and the mod-8 `ℤ/2` anomaly theorem
(`sw_z2_mod_eight_iff`) forces `8 ∣ n_odd`, hence `16 ∣ ν`. -/
theorem boundary_trivial_K_forces_sixteen_dvd (D : MajoranaYukawaBoundaryDatum) :
    16 ∣ Module.finrank ℝ D.V := by
  let Vplus : Submodule ℝ D.V := LinearMap.ker (D.kHalf - LinearMap.id)
  let Vminus : Submodule ℝ D.V := LinearMap.ker (D.kHalf + LinearMap.id)
  have hk_apply : ∀ v : D.V, D.kHalf (D.kHalf v) = v := by
    intro v
    have h := congrArg (fun f : D.V →ₗ[ℝ] D.V => f v) D.kHalf_sq
    simpa [pow_two] using h
  have hcomp : IsCompl Vplus Vminus := by
    rw [isCompl_iff]
    constructor
    · rw [disjoint_iff, Submodule.eq_bot_iff]
      intro v hv
      rcases hv with ⟨hvp, hvm⟩
      change v ∈ LinearMap.ker (D.kHalf - LinearMap.id) at hvp
      change v ∈ LinearMap.ker (D.kHalf + LinearMap.id) at hvm
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hvp
      rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg] at hvm
      have h2v : (2 : ℝ) • v = 0 := by
        rw [two_smul]
        calc
          v + v = D.kHalf v + v := by rw [hvp]
          _ = -v + v := by rw [hvm]
          _ = 0 := neg_add_cancel v
      exact (smul_eq_zero.mp h2v).resolve_left (by norm_num)
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      let vp : D.V := (1 / 2 : ℝ) • (v + D.kHalf v)
      let vm : D.V := (1 / 2 : ℝ) • (v - D.kHalf v)
      have hvp : vp ∈ Vplus := by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
        dsimp [vp]
        rw [map_smul, map_add, hk_apply, add_comm]
      have hvm : vm ∈ Vminus := by
        rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]
        dsimp [vm]
        rw [map_smul, map_sub, hk_apply, ← smul_neg, neg_sub]
      have hsum : vp + vm = v := by
        dsimp [vp, vm]
        module
      rw [← hsum]
      exact Submodule.add_mem_sup hvp hvm
  have hplus_vanish : ∀ u ∈ Vplus, ∀ v ∈ Vplus, D.yukawaForm u v = 0 := by
    intro u hu v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hu hv
    have hodd := D.yukawa_kHalf_odd u v
    rw [hu, hv] at hodd
    linarith
  have hminus_vanish : ∀ u ∈ Vminus, ∀ v ∈ Vminus, D.yukawaForm u v = 0 := by
    intro u hu v hv
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg] at hu hv
    have hodd := D.yukawa_kHalf_odd u v
    rw [hu, hv] at hodd
    simp only [map_neg, LinearMap.neg_apply, neg_neg] at hodd
    linarith
  let toDualPlus : Vplus →ₗ[ℝ] Module.Dual ℝ Vminus :=
    { toFun := fun u =>
        { toFun := fun v => D.yukawaForm u.1 v.1
          map_add' := fun v₁ v₂ => map_add (D.yukawaForm u.1) v₁.1 v₂.1
          map_smul' := fun r v => map_smul (D.yukawaForm u.1) r v.1 }
      map_add' := fun u₁ u₂ => by
        ext v
        simp [map_add]
      map_smul' := fun r u => by
        ext v
        simp [map_smul] }
  let toDualMinus : Vminus →ₗ[ℝ] Module.Dual ℝ Vplus :=
    { toFun := fun u =>
        { toFun := fun v => D.yukawaForm u.1 v.1
          map_add' := fun v₁ v₂ => map_add (D.yukawaForm u.1) v₁.1 v₂.1
          map_smul' := fun r v => map_smul (D.yukawaForm u.1) r v.1 }
      map_add' := fun u₁ u₂ => by
        ext v
        simp [map_add]
      map_smul' := fun r u => by
        ext v
        simp [map_smul] }
  have hinjPlus : Function.Injective toDualPlus := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    apply Subtype.ext
    apply D.yukawa_nondegenerate.1 u.1
    intro w
    have hw : w ∈ Vplus ⊔ Vminus := by rw [hcomp.sup_eq_top]; trivial
    rw [Submodule.mem_sup] at hw
    rcases hw with ⟨wp, hwp, wm, hwm, rfl⟩
    rw [map_add]
    have h1 : D.yukawaForm u.1 wp = 0 := hplus_vanish u.1 u.2 wp hwp
    have h2 : D.yukawaForm u.1 wm = 0 := by
      have hm := congrArg (fun f : Module.Dual ℝ Vminus => f ⟨wm, hwm⟩) hu
      simpa [toDualPlus] using hm
    rw [h1, h2, add_zero]
  have hinjMinus : Function.Injective toDualMinus := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    apply Subtype.ext
    apply D.yukawa_nondegenerate.1 u.1
    intro w
    have hw : w ∈ Vplus ⊔ Vminus := by rw [hcomp.sup_eq_top]; trivial
    rw [Submodule.mem_sup] at hw
    rcases hw with ⟨wp, hwp, wm, hwm, rfl⟩
    rw [map_add]
    have h1 : D.yukawaForm u.1 wp = 0 := by
      have hp := congrArg (fun f : Module.Dual ℝ Vplus => f ⟨wp, hwp⟩) hu
      simpa [toDualMinus] using hp
    have h2 : D.yukawaForm u.1 wm = 0 := hminus_vanish u.1 u.2 wm hwm
    rw [h1, h2, add_zero]
  have hle1 : Module.finrank ℝ Vplus ≤ Module.finrank ℝ Vminus := by
    calc
      Module.finrank ℝ Vplus ≤ Module.finrank ℝ (Module.Dual ℝ Vminus) :=
        LinearMap.finrank_le_finrank_of_injective hinjPlus
      _ = Module.finrank ℝ Vminus := Subspace.dual_finrank_eq
  have hle2 : Module.finrank ℝ Vminus ≤ Module.finrank ℝ Vplus := by
    calc
      Module.finrank ℝ Vminus ≤ Module.finrank ℝ (Module.Dual ℝ Vplus) :=
        LinearMap.finrank_le_finrank_of_injective hinjMinus
      _ = Module.finrank ℝ Vplus := Subspace.dual_finrank_eq
  have heqdim : Module.finrank ℝ Vplus = Module.finrank ℝ Vminus := le_antisymm hle1 hle2
  have htot : Module.finrank ℝ D.V = Module.finrank ℝ Vplus + Module.finrank ℝ Vminus := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq Vplus Vminus
    rw [hcomp.sup_eq_top, hcomp.inf_eq_bot, finrank_top, finrank_bot, add_zero] at hsum
    exact hsum
  have h8 : 8 ∣ Module.finrank ℝ Vminus :=
    (sw_z2_mod_eight_iff (Module.finrank ℝ Vminus)).mp D.z2_anomaly_free
  rcases h8 with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  rw [htot, heqdim, hm]
  ring

/-- Equivalence with `WittenParityAnomalyBridge.AnomalyFree` and `ZMod 16` triviality. -/
theorem boundary_trivial_K_anomaly_free_and_diii (D : MajoranaYukawaBoundaryDatum) :
    AnomalyFree (Module.finrank ℝ D.V) ∧ (Module.finrank ℝ D.V : ZMod 16) = 0 := by
  have hdvd : 16 ∣ Module.finrank ℝ D.V := boundary_trivial_K_forces_sixteen_dvd D
  have hmod : Module.finrank ℝ D.V % 16 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  refine ⟨hmod, ?_⟩
  exact (ZMod.natCast_eq_zero_iff (Module.finrank ℝ D.V) 16).mpr hdvd

/-- Contrapositive: if `¬ 16 ∣ ν`, then no `MajoranaYukawaBoundaryDatum` (`K = 1`) can have
dimension `ν`, forcing a nontrivial boundary extension `K ≠ 1`. -/
theorem nontrivial_K_of_not_sixteen_dvd {ν : ℕ} (hnot : ¬ 16 ∣ ν)
    (D : MajoranaYukawaBoundaryDatum) : Module.finrank ℝ D.V ≠ ν := by
  intro heq
  apply hnot
  rw [← heq]
  exact boundary_trivial_K_forces_sixteen_dvd D

/-- Canonical DIII interacting `ℤ/16` readout linking a `MajoranaYukawaBoundaryDatum`
to `InfoGeometry.CondensedMatter.DIIISuperfluid.DIIITopologicalRegime.threeDimensionalInteractingZ16`. -/
def boundaryDIIIReadout {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (D_op : DIIISuperfluidDatum Op) (D_yuk : MajoranaYukawaBoundaryDatum) :
    DIIITopologicalReadout D_op :=
  DIIITopologicalReadout.mk .threeDimensionalInteractingZ16 (Module.finrank ℝ D_yuk.V : ZMod 16)

theorem boundaryDIIIReadout_invariant_eq_zero {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (D_op : DIIISuperfluidDatum Op) (D_yuk : MajoranaYukawaBoundaryDatum) :
    (boundaryDIIIReadout D_op D_yuk).regime = .threeDimensionalInteractingZ16 ∧
      (Module.finrank ℝ D_yuk.V : ZMod 16) = 0 := by
  refine ⟨rfl, ?_⟩
  exact (ZMod.natCast_eq_zero_iff (Module.finrank ℝ D_yuk.V) 16).mpr
    (boundary_trivial_K_forces_sixteen_dvd D_yuk)

end BoundaryExtension

/-! ## Section 1B: Closed Constructive `T17` Inhabitants (No Ambient Variables) -/

section BoundaryExtensionWitnesses

/-- Additive-to-multiplicative `ZMod 4`. -/
abbrev Z4Mul : Type := Multiplicative (ZMod 4)

/-- Additive-to-multiplicative `ZMod 8 × ZMod 2`. -/
abbrev Z8xZ2Mul : Type := Multiplicative (ZMod 8 × ZMod 2)

private def z4ToZ8xZ2AddHom : ZMod 4 →+ ZMod 8 × ZMod 2 where
  toFun k := ((2 * k.val : ZMod 8), (k.val : ZMod 2))
  map_zero' := by simp
  map_add' a b := by
    ext
    · change (2 * ((a + b).val : ℕ) : ZMod 8) = (2 * a.val : ZMod 8) + (2 * b.val : ZMod 8)
      rw [ZMod.val_add]
      have hmod : (2 * ((a.val + b.val) % 4)) % 8 = (2 * a.val + 2 * b.val) % 8 := by omega
      have hmul : (2 : ZMod 8) * (((a.val + b.val) % 4 : ℕ) : ZMod 8) =
          ((2 * ((a.val + b.val) % 4) : ℕ) : ZMod 8) := by push_cast; rfl
      rw [hmul, ← ZMod.natCast_mod (2 * ((a.val + b.val) % 4)) 8, hmod, ZMod.natCast_mod]
      push_cast
      rfl
    · change (((a + b).val : ℕ) : ZMod 2) = (a.val : ZMod 2) + (b.val : ZMod 2)
      rw [ZMod.val_add]
      have hmod : ((a.val + b.val) % 4) % 2 = (a.val + b.val) % 2 := by omega
      rw [← ZMod.natCast_mod ((a.val + b.val) % 4) 2, hmod, ZMod.natCast_mod]
      push_cast
      rfl

private def z8xZ2ToZ4AddHom : ZMod 8 × ZMod 2 →+ ZMod 4 where
  toFun x := (x.1.val : ZMod 4) + 2 * (x.2.val : ZMod 4)
  map_zero' := by simp
  map_add' a b := by
    have h1 : ((a.1 + b.1).val : ZMod 4) = (a.1.val : ZMod 4) + (b.1.val : ZMod 4) := by
      rw [ZMod.val_add]
      have hmod : ((a.1.val + b.1.val) % 8) % 4 = (a.1.val + b.1.val) % 4 := by omega
      rw [← ZMod.natCast_mod ((a.1.val + b.1.val) % 8) 4, hmod, ZMod.natCast_mod]
      push_cast
      rfl
    have h2 : (2 : ZMod 4) * ((a.2 + b.2).val : ZMod 4) =
        2 * (a.2.val : ZMod 4) + 2 * (b.2.val : ZMod 4) := by
      rw [ZMod.val_add]
      have hmod : (2 * ((a.2.val + b.2.val) % 2)) % 4 = (2 * a.2.val + 2 * b.2.val) % 4 := by omega
      have : (2 : ZMod 4) * (((a.2.val + b.2.val) % 2 : ℕ) : ZMod 4) =
          ((2 * ((a.2.val + b.2.val) % 2) : ℕ) : ZMod 4) := by push_cast; rfl
      rw [this, ← ZMod.natCast_mod (2 * ((a.2.val + b.2.val) % 2)) 4, hmod, ZMod.natCast_mod]
      push_cast
      ring
    rw [Prod.fst_add, Prod.snd_add, h1, h2]
    ring

/-- Closed `T17` constructive inhabitant of `BoundarySymmetryExtension`: the genuinely non-split
abelian extension `1 → ℤ/4 → ℤ/8 × ℤ/2 → ℤ/4 → 1` with `T'² = (-1)^F K`. -/
def canonicalZ4Extension : BoundarySymmetryExtension Z4Mul Z8xZ2Mul where
  incl := z4ToZ8xZ2AddHom.toMultiplicative
  proj := z8xZ2ToZ4AddHom.toMultiplicative
  incl_injective := by
    intro a b hab
    have hadd : z4ToZ8xZ2AddHom a.toAdd = z4ToZ8xZ2AddHom b.toAdd := by
      simpa using congrArg Multiplicative.toAdd hab
    have hval : ∀ x y : ZMod 4, z4ToZ8xZ2AddHom x = z4ToZ8xZ2AddHom y → x = y := by
      decide
    exact Multiplicative.toAdd.injective (hval a.toAdd b.toAdd hadd)
  proj_surjective := by
    intro y
    refine ⟨Multiplicative.ofAdd ((y.toAdd.val : ZMod 8), (0 : ZMod 2)), ?_⟩
    apply Multiplicative.toAdd.injective
    change z8xZ2ToZ4AddHom ((y.toAdd.val : ZMod 8), 0) = y.toAdd
    have hcheck : ∀ z : ZMod 4, z8xZ2ToZ4AddHom ((z.val : ZMod 8), 0) = z := by decide
    exact hcheck y.toAdd
  exact_ker := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      change z8xZ2ToZ4AddHom (z4ToZ8xZ2AddHom k.toAdd) = 0
      have hcheck : ∀ z : ZMod 4, z8xZ2ToZ4AddHom (z4ToZ8xZ2AddHom z) = 0 := by decide
      exact hcheck k.toAdd
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hx0 : z8xZ2ToZ4AddHom x.toAdd = 0 := by
        simpa using congrArg Multiplicative.toAdd hx
      have hlift : ∀ u : ZMod 8 × ZMod 2,
          z8xZ2ToZ4AddHom u = 0 → ∃ k : ZMod 4, z4ToZ8xZ2AddHom k = u := by
        decide
      rcases hlift x.toAdd hx0 with ⟨k, hk⟩
      exact ⟨Multiplicative.ofAdd k, Multiplicative.toAdd.injective hk⟩
  fermionParity := Multiplicative.ofAdd ((0 : ZMod 8), (1 : ZMod 2))
  fermionParity_proj := by decide
  fermionParity_sq := by decide
  tPrime := Multiplicative.ofAdd ((1 : ZMod 8), (0 : ZMod 2))
  tPrime_proj := by decide
  kUnbroken := Multiplicative.ofAdd (1 : ZMod 4)
  tPrime_sq := by decide

/-- `canonicalZ4Extension` has NO group-homomorphism splitting `ℤ₄ᵀ → ℤ/8 × ℤ/2`. -/
theorem canonicalZ4Extension_non_split :
    ¬ ∃ s : BulkTimeReversalGroup →* Z8xZ2Mul,
      canonicalZ4Extension.proj.comp s = MonoidHom.id BulkTimeReversalGroup := by
  apply boundaryExtension_no_splitting canonicalZ4Extension
  intro k
  have hcheck : ∀ x : ZMod 4, 2 * (1 + 2 * x) ≠ 0 := by decide
  intro hk
  have hk' := congrArg Multiplicative.toAdd hk
  have hne := hcheck k.toAdd
  apply hne
  simpa [canonicalZ4Extension, mul_add] using hk'

private def canonicalNu16KHalf : (Fin 16 → ℝ) →ₗ[ℝ] (Fin 16 → ℝ) where
  toFun v i := if i.1 < 8 then v i else -v i
  map_add' u v := by
    ext i
    simp only [Pi.add_apply]
    split_ifs <;> abel
  map_smul' r v := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [mul_neg]

private theorem canonicalNu16KHalf_sq : canonicalNu16KHalf ^ 2 = 1 := by
  apply LinearMap.ext
  intro v
  ext i
  change canonicalNu16KHalf (canonicalNu16KHalf v) i = v i
  dsimp [canonicalNu16KHalf]
  split_ifs <;> simp

private def canonicalNu16YukawaForm : LinearMap.BilinForm ℝ (Fin 16 → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun u v => ∑ i : Fin 8,
      (u ⟨i.1, by omega⟩ * v ⟨i.1 + 8, by omega⟩ -
       u ⟨i.1 + 8, by omega⟩ * v ⟨i.1, by omega⟩))
    (fun u₁ u₂ v => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, add_mul]
      exact add_sub_add_comm _ _ _ _)
    (fun r u v => by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, mul_sub, mul_assoc])
    (fun u v₁ v₂ => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, mul_add]
      exact add_sub_add_comm _ _ _ _)
    (fun r u v => by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, mul_sub, mul_left_comm])

private theorem canonicalNu16YukawaForm_nondegenerate : canonicalNu16YukawaForm.Nondegenerate := by
  constructor
  · intro u hu
    ext j
    by_cases hj : j.1 < 8
    · let k : Fin 8 := ⟨j.1, hj⟩
      have htest := hu (Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ))
      have hsum : canonicalNu16YukawaForm u
          (Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ)) = u j := by
        change ∑ i : Fin 8,
            (u ⟨i.1, by omega⟩ * Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ) ⟨i.1 + 8, by omega⟩ -
             u ⟨i.1 + 8, by omega⟩ * Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ) ⟨i.1, by omega⟩) = u j
        have hzero2 : ∀ i : Fin 8,
            Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ) ⟨i.1, by omega⟩ = 0 := by
          intro i
          apply Pi.single_eq_of_ne
          intro h
          have hv := congrArg Fin.val h
          dsimp at hv
          omega
        simp_rw [hzero2, mul_zero, sub_zero]
        have hdelta : ∀ i : Fin 8,
            u ⟨i.1, by omega⟩ *
              Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ) ⟨i.1 + 8, by omega⟩ =
              if i = k then u j else 0 := by
          intro i
          by_cases hik : i = k
          · subst hik
            rw [if_pos rfl]
            have h1 : Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ) ⟨k.1 + 8, by omega⟩ = 1 :=
              Pi.single_eq_same _ _
            rw [h1, mul_one]
          · rw [if_neg hik]
            have hne : (⟨i.1 + 8, by omega⟩ : Fin 16) ≠ ⟨k.1 + 8, by omega⟩ := by
              intro h
              apply hik
              exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
            rw [Pi.single_eq_of_ne hne, mul_zero]
        simp_rw [hdelta]
        simp
      rw [hsum] at htest
      simpa using htest
    · let k : Fin 8 := ⟨j.1 - 8, by omega⟩
      have htest := hu (Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ))
      have hsum : canonicalNu16YukawaForm u
          (Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ)) = -u j := by
        change ∑ i : Fin 8,
            (u ⟨i.1, by omega⟩ * Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ) ⟨i.1 + 8, by omega⟩ -
             u ⟨i.1 + 8, by omega⟩ * Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ) ⟨i.1, by omega⟩) = -u j
        have hzero1 : ∀ i : Fin 8,
            Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ) ⟨i.1 + 8, by omega⟩ = 0 := by
          intro i
          apply Pi.single_eq_of_ne
          intro h
          have hv := congrArg Fin.val h
          dsimp at hv
          omega
        simp_rw [hzero1, mul_zero, zero_sub]
        have hdelta : ∀ i : Fin 8,
            -(u ⟨i.1 + 8, by omega⟩ *
              Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ) ⟨i.1, by omega⟩) =
              if i = k then -u j else 0 := by
          intro i
          by_cases hik : i = k
          · subst hik
            rw [if_pos rfl]
            have h1 : Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ) ⟨k.1, by omega⟩ = 1 :=
              Pi.single_eq_same _ _
            rw [h1, mul_one]
            congr 2
            exact Fin.ext (by dsimp [k]; omega)
          · rw [if_neg hik]
            have hne : (⟨i.1, by omega⟩ : Fin 16) ≠ ⟨k.1, by omega⟩ := by
              intro h
              apply hik
              exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
            rw [Pi.single_eq_of_ne hne, mul_zero, neg_zero]
        simp_rw [hdelta]
        simp
      rw [hsum, neg_eq_zero] at htest
      simpa using htest
  · intro v hv
    ext j
    by_cases hj : j.1 < 8
    · let k : Fin 8 := ⟨j.1, hj⟩
      have htest := hv (Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ))
      have hsum : canonicalNu16YukawaForm
          (Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ)) v = -v j := by
        change ∑ i : Fin 8,
            (Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ) ⟨i.1, by omega⟩ * v ⟨i.1 + 8, by omega⟩ -
             Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ) ⟨i.1 + 8, by omega⟩ * v ⟨i.1, by omega⟩) = -v j
        have hzero1 : ∀ i : Fin 8,
            Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ) ⟨i.1, by omega⟩ = 0 := by
          intro i
          apply Pi.single_eq_of_ne
          intro h
          have hv := congrArg Fin.val h
          dsimp at hv
          omega
        simp_rw [hzero1, zero_mul, zero_sub]
        have hdelta : ∀ i : Fin 8,
            -(Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ) ⟨i.1 + 8, by omega⟩ *
              v ⟨i.1, by omega⟩) =
              if i = k then -v j else 0 := by
          intro i
          by_cases hik : i = k
          · subst hik
            rw [if_pos rfl]
            have h1 : Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1 + 8, by omega⟩ (1 : ℝ) ⟨k.1 + 8, by omega⟩ = 1 :=
              Pi.single_eq_same _ _
            rw [h1, one_mul]
          · rw [if_neg hik]
            have hne : (⟨i.1 + 8, by omega⟩ : Fin 16) ≠ ⟨k.1 + 8, by omega⟩ := by
              intro h
              apply hik
              exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
            rw [Pi.single_eq_of_ne hne, zero_mul, neg_zero]
        simp_rw [hdelta]
        simp
      rw [hsum, neg_eq_zero] at htest
      simpa using htest
    · let k : Fin 8 := ⟨j.1 - 8, by omega⟩
      have htest := hv (Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ))
      have hsum : canonicalNu16YukawaForm
          (Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ)) v = v j := by
        change ∑ i : Fin 8,
            (Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ) ⟨i.1, by omega⟩ * v ⟨i.1 + 8, by omega⟩ -
             Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ) ⟨i.1 + 8, by omega⟩ * v ⟨i.1, by omega⟩) = v j
        have hzero2 : ∀ i : Fin 8,
            Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ) ⟨i.1 + 8, by omega⟩ = 0 := by
          intro i
          apply Pi.single_eq_of_ne
          intro h
          have hv := congrArg Fin.val h
          dsimp at hv
          omega
        simp_rw [hzero2, zero_mul, sub_zero]
        have hdelta : ∀ i : Fin 8,
            Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ) ⟨i.1, by omega⟩ *
              v ⟨i.1 + 8, by omega⟩ =
              if i = k then v j else 0 := by
          intro i
          by_cases hik : i = k
          · subst hik
            rw [if_pos rfl]
            have h1 : Pi.single (M := fun _ : Fin 16 => ℝ) ⟨k.1, by omega⟩ (1 : ℝ) ⟨k.1, by omega⟩ = 1 :=
              Pi.single_eq_same _ _
            rw [h1, one_mul]
            congr 1
            exact Fin.ext (by dsimp [k]; omega)
          · rw [if_neg hik]
            have hne : (⟨i.1, by omega⟩ : Fin 16) ≠ ⟨k.1, by omega⟩ := by
              intro h
              apply hik
              exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
            rw [Pi.single_eq_of_ne hne, zero_mul]
        simp_rw [hdelta]
        simp
      rw [hsum] at htest
      simpa using htest

private theorem canonicalNu16YukawaForm_kHalf_odd (u v : Fin 16 → ℝ) :
    canonicalNu16YukawaForm (canonicalNu16KHalf u) (canonicalNu16KHalf v) =
      -canonicalNu16YukawaForm u v := by
  change (∑ i : Fin 8,
      (canonicalNu16KHalf u ⟨i.1, by omega⟩ * canonicalNu16KHalf v ⟨i.1 + 8, by omega⟩ -
       canonicalNu16KHalf u ⟨i.1 + 8, by omega⟩ * canonicalNu16KHalf v ⟨i.1, by omega⟩)) =
    -(∑ i : Fin 8,
      (u ⟨i.1, by omega⟩ * v ⟨i.1 + 8, by omega⟩ - u ⟨i.1 + 8, by omega⟩ * v ⟨i.1, by omega⟩))
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp [canonicalNu16KHalf]
  have h1 : i.1 < 8 := i.2
  have h2 : ¬ (i.1 + 8 < 8) := by omega
  simp only [h1, ↓reduceIte]
  ring

private theorem canonicalNu16_finrank_odd :
    Module.finrank ℝ (LinearMap.ker (canonicalNu16KHalf + LinearMap.id)) = 8 := by
  let e : (Fin 8 → ℝ) ≃ₗ[ℝ] LinearMap.ker (canonicalNu16KHalf + LinearMap.id) :=
    { toFun := fun w =>
        ⟨fun i => if h : i.1 < 8 then 0 else w ⟨i.1 - 8, by omega⟩, by
          rw [LinearMap.mem_ker]
          ext i
          simp only [LinearMap.add_apply, LinearMap.id_apply, Pi.zero_apply]
          dsimp [canonicalNu16KHalf]
          by_cases h : i.1 < 8
          · simp [h]
          · simp [h]⟩
      invFun := fun v k => v.1 ⟨k.1 + 8, by omega⟩
      left_inv := fun w => by
        ext k
        have h : ¬ (k.1 + 8 < 8) := by omega
        simp [h]
      right_inv := fun v => by
        apply Subtype.ext
        ext i
        have hv : canonicalNu16KHalf v.1 i + v.1 i = 0 := by
          have hker := LinearMap.mem_ker.mp v.2
          exact congrArg (fun f : Fin 16 → ℝ => f i) hker
        dsimp [canonicalNu16KHalf] at hv
        by_cases h : i.1 < 8
        · simp only [h, ↓reduceDIte, ↓reduceIte] at hv ⊢
          linarith
        · simp only [h, ↓reduceDIte]
          exact congrArg v.1 (Fin.ext (by dsimp; omega))
      map_add' := fun w₁ w₂ => by
        apply Subtype.ext
        ext i
        by_cases h : i.1 < 8
        · simp [h]
        · simp [h]
      map_smul' := fun r w => by
        apply Subtype.ext
        ext i
        by_cases h : i.1 < 8 <;> simp [h] }
  rw [← LinearEquiv.finrank_eq e]
  simp

/-- Closed `T17` constructive inhabitant of `MajoranaYukawaBoundaryDatum` realizing `ν = 16`
Majorana modes (`8` even + `8` odd under `kHalf`) with nondegenerate skew Yukawa pairing. -/
def canonicalNu16YukawaModel : MajoranaYukawaBoundaryDatum where
  V := Fin 16 → ℝ
  kHalf := canonicalNu16KHalf
  kHalf_sq := canonicalNu16KHalf_sq
  yukawaForm := canonicalNu16YukawaForm
  yukawa_nondegenerate := canonicalNu16YukawaForm_nondegenerate
  yukawa_kHalf_odd := canonicalNu16YukawaForm_kHalf_odd
  z2_anomaly_free := by
    rw [canonicalNu16_finrank_odd]
    exact (sw_z2_mod_eight_iff 8).mpr (dvd_refl 8)

theorem canonicalNu16YukawaModel_finrank :
    Module.finrank ℝ canonicalNu16YukawaModel.V = 16 := by
  change Module.finrank ℝ (Fin 16 → ℝ) = 16
  simp

end BoundaryExtensionWitnesses

/-! ## Section 2: `S²` Monopole Spin & Kramers-Singlet Quantization (Witten §3.2.2) -/

section MonopoleQuantization

/-- Number of odd-charge Dirac fermions `y = #{i | Odd (n i)}`. -/
def monopoleOddChargeCount {k : ℕ} (n : Fin k → ℕ) : ℕ :=
  (Finset.univ.filter fun i => Odd (n i)).card

/-- Twice the lowest monopole electric charge `2q = -∑_{odd n_i} n_i²` (Witten Eq. 3.13). -/
def monopoleLowestChargeTwice {k : ℕ} (n : Fin k → ℕ) : ℤ :=
  -(∑ i : Fin k, if Odd (n i) then (n i : ℤ) ^ 2 else 0)

/-- Twice the `T'`-sign exponent `2t = (a_+ - a_-)/2 = ∑_{n_i ≡ 1(4)} n_i - ∑_{n_i ≡ 3(4)} n_i`
(Witten Eq. 3.15). -/
def monopoleTPrimeSignTwice {k : ℕ} (n : Fin k → ℕ) : ℤ :=
  ∑ i : Fin k, if n i % 4 = 1 then (n i : ℤ) else if n i % 4 = 3 then -(n i : ℤ) else 0

/-- Lowest monopole electric charge `q = ⌊(2q)/2⌋` (exact integer when `2 ∣ 2q`). -/
def monopoleLowestCharge {k : ℕ} (n : Fin k → ℕ) : ℤ :=
  monopoleLowestChargeTwice n / 2

/-- Monopole `T'`-sign exponent `t = ⌊(2t)/2⌋` (exact integer when `2 ∣ 2t`). -/
def monopoleTPrimeExponent {k : ℕ} (n : Fin k → ℕ) : ℤ :=
  monopoleTPrimeSignTwice n / 2

/-- Spin-statistics / Kramers-singlet compatibility of the monopole state `|Ψ⟩ = w^{-q}|↓⟩`
(Witten 2016 §3.2.2, Eq. 3.16): `T^2 |Ψ⟩ = (-1)^{t - q} |Ψ⟩`, so `|Ψ⟩` is either a
Kramers-singlet boson (`Even q ∧ (-1)^(t-q) = 1`) or a Kramers-doublet fermion
(`Odd q ∧ (-1)^(t-q) = -1`, which combines with an odd-charge fermion `w^{n_i} χ_i` to form a
Kramers-singlet boson). -/
def IsMonopoleSpinStatisticsCompatible (q t : ℤ) : Prop :=
  (Even q ∧ (-1 : ℝ) ^ (t - q) = 1) ∨ (Odd q ∧ (-1 : ℝ) ^ (t - q) = -1)

/-- `q ∈ ℤ` (i.e. `2 ∣ monopoleLowestChargeTwice n`, Eq. 3.13) iff `y` is even. -/
theorem monopole_lowest_charge_integral_iff_even {k : ℕ} (n : Fin k → ℕ) :
    2 ∣ monopoleLowestChargeTwice n ↔ Even (monopoleOddChargeCount n) := by
  unfold monopoleLowestChargeTwice monopoleOddChargeCount
  rw [dvd_neg]
  have hmod2 : ∀ i : Fin k, (if Odd (n i) then (n i : ℤ) ^ 2 else 0) % 2 =
      if Odd (n i) then 1 else 0 := by
    intro i
    by_cases hi : Odd (n i)
    · simp only [hi, ↓reduceIte]
      rcases hi with ⟨m, hm⟩
      rw [hm]
      push_cast
      have hsq : ((2 * (m : ℤ) + 1) ^ 2) = 2 * (2 * (m : ℤ) ^ 2 + 2 * m) + 1 := by ring
      rw [hsq]
      omega
    · simp [hi]
  have hsum : (∑ i : Fin k, if Odd (n i) then (n i : ℤ) ^ 2 else 0) % 2 =
      ((Finset.univ.filter fun i => Odd (n i)).card : ℤ) % 2 := by
    have hs : ∀ s : Finset (Fin k),
        (∑ i ∈ s, if Odd (n i) then (n i : ℤ) ^ 2 else 0) % 2 =
          (∑ i ∈ s, (if Odd (n i) then (1 : ℤ) else 0)) % 2 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          have ha2 : (if Odd (n a) then (1 : ℤ) else 0) % 2 = if Odd (n a) then 1 else 0 := by
            split_ifs <;> decide
          rw [Int.add_emod, hmod2 a, ih]
          symm
          rw [Int.add_emod, ha2]
    rw [hs Finset.univ, Finset.sum_boole]
  rw [Int.dvd_iff_emod_eq_zero, hsum, Nat.even_iff]
  omega

/-- When `y` is even, `2 ∣ 2t` and `2 ∣ t` iff `4 ∣ y` (Witten 2016 Eq. 3.15). -/
theorem monopole_tPrime_exponent_mod_two {k : ℕ} (n : Fin k → ℕ)
    (heven : Even (monopoleOddChargeCount n)) :
    2 ∣ monopoleTPrimeSignTwice n ∧ (Even (monopoleTPrimeExponent n) ↔ 4 ∣ monopoleOddChargeCount n) := by
  have hmod4 : ∀ i : Fin k,
      (if n i % 4 = 1 then (n i : ℤ) else if n i % 4 = 3 then -(n i : ℤ) else 0) % 4 =
        if Odd (n i) then 1 else 0 := by
    intro i
    have h4 : n i % 4 = 0 ∨ n i % 4 = 1 ∨ n i % 4 = 2 ∨ n i % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · have hne : ¬ Odd (n i) := by rw [Nat.not_odd_iff_even, Nat.even_iff]; omega
      simp [h, hne]
    · have hod : Odd (n i) := by rw [Nat.odd_iff]; omega
      simp only [h, ↓reduceIte, hod]
      omega
    · have hne : ¬ Odd (n i) := by rw [Nat.not_odd_iff_even, Nat.even_iff]; omega
      simp [h, hne]
    · have hod : Odd (n i) := by rw [Nat.odd_iff]; omega
      have hne1 : n i % 4 ≠ 1 := by omega
      simp only [h, hne1, ↓reduceIte, hod]
      omega
  have hsum4 : monopoleTPrimeSignTwice n % 4 = (monopoleOddChargeCount n : ℤ) % 4 := by
    unfold monopoleTPrimeSignTwice monopoleOddChargeCount
    have hs : ∀ s : Finset (Fin k),
        (∑ i ∈ s, if n i % 4 = 1 then (n i : ℤ) else if n i % 4 = 3 then -(n i : ℤ) else 0) % 4 =
          (∑ i ∈ s, (if Odd (n i) then (1 : ℤ) else 0)) % 4 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          have ha4 : (if Odd (n a) then (1 : ℤ) else 0) % 4 = if Odd (n a) then 1 else 0 := by
            split_ifs <;> decide
          rw [Int.add_emod, hmod4 a, ih]
          symm
          rw [Int.add_emod, ha4]
    rw [hs Finset.univ, Finset.sum_boole]
  have h2y : (2 : ℤ) ∣ (monopoleOddChargeCount n : ℤ) := by
    rcases heven with ⟨m, hm⟩
    exact ⟨m, by omega⟩
  have hdvd2 : 2 ∣ monopoleTPrimeSignTwice n := by
    rw [Int.dvd_iff_emod_eq_zero]
    omega
  refine ⟨hdvd2, ?_⟩
  unfold monopoleTPrimeExponent
  rw [Int.even_iff, Nat.dvd_iff_mod_eq_zero]
  omega

/-- **Monopole Kramers-Singlet Quantization Theorem (Witten 2016 §3.2.2, Eqs. 3.13–3.16)**:
The lowest-charge monopole on `S²` has integral charge `q ∈ ℤ` and satisfies spin-statistics /
Kramers-singlet compatibility iff `4 ∣ y`, matching the `ℤ/2`-valued Stiefel–Whitney mod-4
criterion (`u1TotalSW (1 : ZMod 2) ... = 1`). -/
theorem monopole_kramers_singlet_iff_four_dvd {k : ℕ} (n : Fin k → ℕ) :
    (2 ∣ monopoleLowestChargeTwice n ∧
        IsMonopoleSpinStatisticsCompatible (monopoleLowestCharge n) (monopoleTPrimeExponent n)) ↔
      4 ∣ monopoleOddChargeCount n := by
  have hcompat : ∀ q t : ℤ, IsMonopoleSpinStatisticsCompatible q t ↔ Even t := by
    intro q t
    have hpow : ∀ z : ℤ, (-1 : ℝ) ^ z = 1 ↔ Even z := by
      intro z
      rcases Int.even_or_odd z with hz | hz
      · simpa [hz.neg_one_zpow] using hz
      · simp [hz.neg_one_zpow, Int.not_even_iff_odd.mpr hz]
        norm_num
    have hpow_neg : ∀ z : ℤ, (-1 : ℝ) ^ z = -1 ↔ Odd z := by
      intro z
      rcases Int.even_or_odd z with hz | hz
      · simp [hz.neg_one_zpow, Int.not_odd_iff_even.mpr hz]
        norm_num
      · simpa [hz.neg_one_zpow] using hz
    unfold IsMonopoleSpinStatisticsCompatible
    rw [hpow, hpow_neg]
    rcases Int.even_or_odd q with hq | hq
    · have hnot : ¬ Odd q := Int.not_odd_iff_even.mpr hq
      simp only [hq, hnot, true_and, false_and, or_false]
      constructor
      · intro hsub
        rw [Int.even_iff] at hsub hq ⊢; omega
      · intro ht
        rw [Int.even_iff] at ht hq ⊢; omega
    · have hnot : ¬ Even q := Int.not_even_iff_odd.mpr hq
      simp only [hq, hnot, false_and, true_and, false_or]
      constructor
      · intro hsub
        rw [Int.odd_iff] at hsub hq; rw [Int.even_iff]; omega
      · intro ht
        rw [Int.even_iff] at ht; rw [Int.odd_iff] at hq ⊢; omega
  rw [monopole_lowest_charge_integral_iff_even, hcompat]
  constructor
  · rintro ⟨heven, ht⟩
    exact (monopole_tPrime_exponent_mod_two n heven).2.mp ht
  · intro h4
    have heven : Even (monopoleOddChargeCount n) := by
      rcases h4 with ⟨m, hm⟩
      exact ⟨2 * m, by omega⟩
    exact ⟨heven, (monopole_tPrime_exponent_mod_two n heven).2.mpr h4⟩

/-- Equivalence between `S²` monopole Kramers-singlet compatibility and `u1TotalSW = 1`
from `WittenParityAnomalyQuantization`. -/
theorem monopole_kramers_singlet_iff_u1_stably_trivial {k : ℕ} (n : Fin k → ℕ) :
    (2 ∣ monopoleLowestChargeTwice n ∧
        IsMonopoleSpinStatisticsCompatible (monopoleLowestCharge n) (monopoleTPrimeExponent n)) ↔
      u1TotalSW (1 : ZMod 2) (fun i => (n i : ℤ)) = 1 := by
  have hcount : oddChargeCount (fun i => (n i : ℤ)) = monopoleOddChargeCount n := by
    unfold oddChargeCount monopoleOddChargeCount
    congr 1
    ext i
    simp [Int.odd_coe_nat]
  have h1sq : (1 : ZMod 2) ^ 2 ≠ 0 := by decide
  rw [monopole_kramers_singlet_iff_four_dvd, sw_u1_stably_trivial_iff_four_dvd (1 : ZMod 2) h1sq,
    hcount]

end MonopoleQuantization

/-! ## Section 3: Bosonic SPT Group-Cohomology Pullback Trivialization (Witten §3.3) -/

section BosonicSPTPullback

open CategoryTheory

/-- `U(1) = ℝ / ℤ` coefficient group as `UnitAddCircle : Type 0`. -/
abbrev U1Coeff : Type := UnitAddCircle

/-- Trivial `G`-representation on `U(1) = UnitAddCircle` over `ℤ`. -/
abbrev trivialU1Rep (G : Type) [Group G] : Rep ℤ G :=
  Rep.trivial ℤ G U1Coeff

/-- Canonical representation morphism `Res(π)(U(1)) ⟶ U(1)` for trivial `U(1)`-modules. -/
def resPullbackHom {H F : Type} [Group H] [Group F] (π : H →* F) :
    Rep.res π (trivialU1Rep F) ⟶ trivialU1Rep H :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- Arbitrary-degree group-cohomology pullback `H^D(F, U(1)) ⟶ H^D(H, U(1))` along `π : H →* F`. -/
noncomputable def pullbackCohomology {H F : Type} [Group H] [Group F]
    (π : H →* F) (D : ℕ) :
    groupCohomology (trivialU1Rep F) D ⟶ groupCohomology (trivialU1Rep H) D :=
  groupCohomology.map π (resPullbackHom π) D

/-- **Fiber-restriction vanishing (Witten 2016 §3.3, Eq. 3.21)**:
For `1 → K → H → F → 1` (`π.comp ι = 1`), pulling back along `π` and restricting to the
fiber `K` along `ι` is identically zero in every positive degree `D ≥ 1`. -/
theorem pullback_restrict_fiber_eq_zero {K H F : Type} [Group K] [Group H] [Group F]
    (ι : K →* H) (π : H →* F) (hcomp : π.comp ι = 1) (D : ℕ) [NeZero D] :
    pullbackCohomology π D ≫ pullbackCohomology ι D = 0 := by
  unfold pullbackCohomology
  have hres : (Rep.resFunctor ι).map (resPullbackHom π) ≫ resPullbackHom ι =
      resPullbackHom (π.comp ι) := rfl
  rw [← groupCohomology.map_comp π ι (resPullbackHom π) (resPullbackHom ι) D, hres]
  exact groupCohomology.map_eq_zero (π.comp ι) (resPullbackHom (π.comp ι)) D hcomp

/-- **Boundary-lift trivialization law (Witten 2016 §3.3.4, Eq. 3.24)**:
Given `j : ΓW →* ΓX`, `Φ : ΓX →* F`, and a boundary lift `Φhat : ΓW →* H` satisfying
`π.comp Φhat = Φ.comp j`, if `π^* γ = 0` in `H^D(H, U(1))`, then `j^* (Φ^* γ) = 0` in
`H^D(ΓW, U(1))`. -/
theorem boundary_lift_pullback_trivial {H F ΓW ΓX : Type}
    [Group H] [Group F] [Group ΓW] [Group ΓX]
    (π : H →* F) (j : ΓW →* ΓX) (Φ : ΓX →* F) (Φhat : ΓW →* H)
    (hcomm : π.comp Φhat = Φ.comp j) (D : ℕ)
    (γ : groupCohomology (trivialU1Rep F) D)
    (htriv : pullbackCohomology π D γ = 0) :
    pullbackCohomology j D (pullbackCohomology Φ D γ) = 0 := by
  unfold pullbackCohomology at htriv ⊢
  have h1 :
      groupCohomology.map Φ (resPullbackHom Φ) D ≫
          groupCohomology.map j (resPullbackHom j) D =
        groupCohomology.map (Φ.comp j) (resPullbackHom (Φ.comp j)) D := by
    rw [← groupCohomology.map_comp Φ j (resPullbackHom Φ) (resPullbackHom j) D]
    rfl
  have h2 :
      groupCohomology.map π (resPullbackHom π) D ≫
          groupCohomology.map Φhat (resPullbackHom Φhat) D =
        groupCohomology.map (π.comp Φhat) (resPullbackHom (π.comp Φhat)) D := by
    rw [← groupCohomology.map_comp π Φhat (resPullbackHom π) (resPullbackHom Φhat) D]
    rfl
  have hlhs : groupCohomology.map j (resPullbackHom j) D
      (groupCohomology.map Φ (resPullbackHom Φ) D γ) =
      (groupCohomology.map (Φ.comp j) (resPullbackHom (Φ.comp j)) D) γ :=
    congrArg (fun f => f γ) h1
  have hrhs : groupCohomology.map Φhat (resPullbackHom Φhat) D
      (groupCohomology.map π (resPullbackHom π) D γ) =
      (groupCohomology.map (π.comp Φhat) (resPullbackHom (π.comp Φhat)) D) γ :=
    congrArg (fun f => f γ) h2
  have hcongr : groupCohomology.map (Φ.comp j) (resPullbackHom (Φ.comp j)) D =
      groupCohomology.map (π.comp Φhat) (resPullbackHom (π.comp Φhat)) D := by
    exact groupCohomology.map_congr hcomm.symm rfl D
  rw [hlhs, hcongr, ← hrhs, htriv, map_zero]

/-- Any coboundary `f = d b` represents the zero cohomology class in `groupCohomology A (d + 1)`. -/
theorem groupCohomology_pi_eq_zero_of_coboundary {G : Type} [Group G] (A : Rep ℤ G) {d : ℕ}
    (f : (Fin (d + 1) → G) → A)
    (hf : _root_.inhomogeneousCochains.d A (d + 1) f = 0)
    (b : (Fin d → G) → A)
    (hb : _root_.inhomogeneousCochains.d A d b = f) :
    groupCohomology.π A (d + 1) (groupCohomology.cocyclesMk f hf) = 0 := by
  have hcyc : groupCohomology.toCocycles A d (d + 1) b = groupCohomology.cocyclesMk f hf := by
    apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles A (d + 1))).1 inferInstance
    change ((groupCohomology.toCocycles A d (d + 1) ≫
      groupCohomology.iCocycles A (d + 1)) b) = groupCohomology.iCocycles A (d + 1) _
    rw [HomologicalComplex.toCycles_i, groupCohomology.iCocycles_mk]
    simpa [groupCohomology.inhomogeneousCochains] using hb
  rw [← hcyc]
  exact congrArg (fun φ => φ b)
    ((groupCohomology.inhomogeneousCochains A).toCycles_comp_homologyπ d (d + 1))

set_option backward.isDefEq.respectTransparency false in
/-- Exact coboundary characterization in arbitrary degree `d + 1`:
`groupCohomology.π A (d + 1) (cocyclesMk f hf) = 0 ↔ ∃ b, d b = f`. -/
theorem groupCohomology_pi_eq_zero_iff_exists_coboundary {G : Type} [Group G] (A : Rep ℤ G)
    {d : ℕ} (f : (Fin (d + 1) → G) → A)
    (hf : _root_.inhomogeneousCochains.d A (d + 1) f = 0) :
    groupCohomology.π A (d + 1) (groupCohomology.cocyclesMk f hf) = 0 ↔
      ∃ b : (Fin d → G) → A, _root_.inhomogeneousCochains.d A d b = f := by
  constructor
  · intro hpi
    let K := groupCohomology.inhomogeneousCochains A
    let S := K.sc (d + 1)
    let x : S.cycles := groupCohomology.cocyclesMk f hf
    have hx0 : S.homologyπ x = 0 := hpi
    have hop : S.pOpcycles (S.iCycles x) = 0 := by
      have h1 : (S.iCycles ≫ S.pOpcycles) x = (S.homologyπ ≫ S.homologyι) x :=
        congrArg (fun φ => φ x) S.homology_π_ι.symm
      change S.pOpcycles (S.iCycles x) = S.homologyι (S.homologyπ x) at h1
      rw [h1, hx0, map_zero]
    have hmem : S.iCycles x ∈ LinearMap.range S.f.hom :=
      (S.moduleCat_pOpcycles_eq_zero_iff (S.iCycles x)).1 hop
    rcases LinearMap.mem_range.mp hmem with ⟨y, hy'⟩
    have hprev : (ComplexShape.up ℕ).prev (d + 1) = d :=
      (ComplexShape.up ℕ).prev_eq' (rfl : d + 1 = d + 1)
    let b : (Fin d → G) → A := (K.XIsoOfEq hprev).hom y
    refine ⟨b, ?_⟩
    have hcomm : (K.XIsoOfEq hprev).inv ≫ S.f = K.d d (d + 1) := by
      change (K.XIsoOfEq hprev).inv ≫ K.d ((ComplexShape.up ℕ).prev (d + 1)) (d + 1) =
        K.d d (d + 1)
      simp
    have hdb : K.d d (d + 1) b = S.f y := by
      have happ := congrArg (fun φ => φ b) hcomm
      have hb_inv : (K.XIsoOfEq hprev).inv b = y := by
        change ((K.XIsoOfEq hprev).hom ≫ (K.XIsoOfEq hprev).inv) y = y
        rw [Iso.hom_inv_id]
        rfl
      change S.f ((K.XIsoOfEq hprev).inv b) = K.d d (d + 1) b at happ
      rw [hb_inv] at happ
      exact happ.symm
    have hd_def : _root_.inhomogeneousCochains.d A d b = K.d d (d + 1) b :=
      congrArg (fun φ => φ b) (groupCohomology.inhomogeneousCochains.d_def A d).symm
    rw [hd_def, hdb, hy']
    exact groupCohomology.iCocycles_mk f hf
  · rintro ⟨b, hb⟩
    exact groupCohomology_pi_eq_zero_of_coboundary A f hf b hb

/-- **Trivialization torsor (Witten 2016 §3.3.3)**: Any two `d`-cochain trivializations
`α₁, α₂` of the same `(d+1)`-cocycle `f` differ by a `d`-cocycle `α₁ - α₂ ∈ Z^d(H, A)`. -/
theorem cocycle_trivialization_diff_is_cocycle {H : Type} [Group H] (A : Rep ℤ H) {d : ℕ}
    (f : (Fin (d + 1) → H) → A) (α₁ α₂ : (Fin d → H) → A)
    (h₁ : _root_.inhomogeneousCochains.d A d α₁ = f)
    (h₂ : _root_.inhomogeneousCochains.d A d α₂ = f) :
    _root_.inhomogeneousCochains.d A d (α₁ - α₂) = 0 := by
  rw [map_sub, h₁, h₂, sub_self]

/-- **Boundary `K`-gauge cocycle (Witten 2016 §3.3.3–3.3.4)**:
If `α` trivializes `π^* γ` on `H` and `γ` is normalized (`γ (fun _ => 1) = 0`), then
restricting `α` along `ι : K →* H` (`π.comp ι = 1`) yields a `d`-cocycle `α ∘ ι ∈ Z^d(K, U(1))`. -/
theorem trivialization_restrict_to_fiber_is_cocycle {K H F : Type}
    [Group K] [Group H] [Group F]
    (ι : K →* H) (π : H →* F) (hcomp : π.comp ι = 1) {d : ℕ}
    (γ : (Fin (d + 1) → F) → U1Coeff) (hnorm : γ (fun _ => 1) = 0)
    (α : (Fin d → H) → U1Coeff)
    (htriv : _root_.inhomogeneousCochains.d (trivialU1Rep H) d α =
      (groupCohomology.cochainsMap π (resPullbackHom π)).f (d + 1) γ) :
    _root_.inhomogeneousCochains.d (trivialU1Rep K) d (fun g => α (ι ∘ g)) = 0 := by
  have hcomm := (groupCohomology.cochainsMap ι (resPullbackHom ι)).comm' d (d + 1) rfl
  rw [groupCohomology.inhomogeneousCochains.d_def, groupCohomology.inhomogeneousCochains.d_def] at hcomm
  have happ := congrArg (fun φ => φ α) hcomm
  simp only [CategoryTheory.comp_apply] at happ
  have hlhs :
      ((groupCohomology.cochainsMap ι (resPullbackHom ι)).f (d + 1))
        ((_root_.inhomogeneousCochains.d (trivialU1Rep H) d) α) =
      (_root_.inhomogeneousCochains.d (trivialU1Rep K) d) (fun g => α (ι ∘ g)) := by
    change _ = (_root_.inhomogeneousCochains.d (trivialU1Rep K) d)
      (((groupCohomology.cochainsMap ι (resPullbackHom ι)).f d) α)
    exact happ.symm
  rw [← hlhs, htriv]
  ext g
  change γ (fun i => π (ι (g i))) = 0
  have hpi1 : (fun i => π (ι (g i))) = (fun _ => 1) := by
    funext i
    exact congrArg (fun f : K →* F => f (g i)) hcomp
  rw [hpi1, hnorm]

/-! ### 3.1 Concrete `D = 3` Witness: `0 → ℤ/2 → ℤ/4 → ℤ/2 → 0` (Witten 2016 Eq. 3.22) -/

/-- Multiplicative `ℤ/2`. -/
abbrev Z2Mul : Type := Multiplicative (ZMod 2)

/-- Inclusion `2 : ℤ/2 →* ℤ/4`. -/
def z2ToZ4 : Z2Mul →* Z4Mul :=
  (AddMonoidHom.mk' (fun x : ZMod 2 => (2 * x.val : ZMod 4)) (by
    intro a b
    rw [ZMod.val_add]
    have hmod : (2 * ((a.val + b.val) % 2)) % 4 = (2 * a.val + 2 * b.val) % 4 := by omega
    have hmul : (2 : ZMod 4) * (((a.val + b.val) % 2 : ℕ) : ZMod 4) =
        ((2 * ((a.val + b.val) % 2) : ℕ) : ZMod 4) := by push_cast; rfl
    rw [hmul, ← ZMod.natCast_mod (2 * ((a.val + b.val) % 2)) 4, hmod, ZMod.natCast_mod]
    push_cast
    rfl)).toMultiplicative

/-- Projection `mod 2 : ℤ/4 →* ℤ/2`. -/
def z4ToZ2 : Z4Mul →* Z2Mul :=
  (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)).toMultiplicative

theorem z2ToZ4_injective : Function.Injective z2ToZ4 := by
  intro a b hab
  have hadd : z2ToZ4 a = z2ToZ4 b := hab
  have hval : ∀ x y : ZMod 2, (2 * x.val : ZMod 4) = (2 * y.val : ZMod 4) → x = y := by decide
  exact Multiplicative.toAdd.injective (hval a.toAdd b.toAdd (congrArg Multiplicative.toAdd hadd))

theorem z4ToZ2_surjective : Function.Surjective z4ToZ2 := by
  intro y
  refine ⟨Multiplicative.ofAdd (y.toAdd.val : ZMod 4), ?_⟩
  apply Multiplicative.toAdd.injective
  have hcheck : ∀ z : ZMod 2, ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) (z.val : ZMod 4) = z := by
    decide
  exact hcheck y.toAdd

theorem z2ToZ4_range_eq_ker : z2ToZ4.range = z4ToZ2.ker := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    have hcheck : ∀ z : ZMod 2,
        ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) (2 * z.val : ZMod 4) = 0 := by decide
    exact hcheck k.toAdd
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    have hx0 := congrArg Multiplicative.toAdd hx
    have hlift : ∀ u : ZMod 4,
        ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) u = 0 →
          ∃ k : ZMod 2, (2 * k.val : ZMod 4) = u := by decide
    rcases hlift x.toAdd hx0 with ⟨k, hk⟩
    exact ⟨Multiplicative.ofAdd k, Multiplicative.toAdd.injective hk⟩

/-- Explicit nontrivial `D = 3` bosonic `ℤ/2`-SPT cocycle `γ(a, b, c) = (a*b*c)/2 mod 1`. -/
def z2CubicCochain : (Fin 3 → Z2Mul) → U1Coeff := fun g =>
  if (g 0).toAdd = 1 ∧ (g 1).toAdd = 1 ∧ (g 2).toAdd = 1 then ZMod.toAddCircle (1 : ZMod 2) else 0

private theorem toAddCircle_two_smul (x : ZMod 2) : (2 : ℤ) • ZMod.toAddCircle x = 0 := by
  rw [← map_zsmul]
  have h2 : (2 : ℤ) • x = 0 := by
    fin_cases x <;> decide
  rw [h2, map_zero]

theorem z2CubicCochain_is_cocycle :
    _root_.inhomogeneousCochains.d (trivialU1Rep Z2Mul) 3 z2CubicCochain = 0 := by
  funext g
  change (z2CubicCochain (fun i : Fin 3 => g i.succ) +
      ∑ j : Fin 4, (-1 : ℤ) ^ ((j : ℕ) + 1) •
        z2CubicCochain (Fin.contractNth j (· * ·) g)) = 0
  rw [Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
    show ((3 : Fin 4) : ℕ) = 3 from rfl,
    Nat.zero_add, Nat.reduceAdd, pow_one, neg_one_sq,
    show (-1 : ℤ) ^ 3 = -1 by norm_num,
    show (-1 : ℤ) ^ 4 = 1 by norm_num,
    neg_smul, one_smul]
  have hs : (fun i : Fin 3 => g i.succ) = ![g 1, g 2, g 3] := by
    ext i; fin_cases i <;> rfl
  have hc0 : Fin.contractNth 0 (· * ·) g = ![g 0 * g 1, g 2, g 3] := by
    ext i; fin_cases i <;>
      simp [Fin.contractNth_apply_of_eq, Fin.contractNth_apply_of_gt]
  have hc1 : Fin.contractNth 1 (· * ·) g = ![g 0, g 1 * g 2, g 3] := by
    ext i; fin_cases i <;>
      simp [Fin.contractNth_apply_of_lt, Fin.contractNth_apply_of_eq, Fin.contractNth_apply_of_gt]
  have hc2 : Fin.contractNth 2 (· * ·) g = ![g 0, g 1, g 2 * g 3] := by
    ext i; fin_cases i <;>
      simp [Fin.contractNth_apply_of_lt, Fin.contractNth_apply_of_eq]
  have hc3 : Fin.contractNth 3 (· * ·) g = ![g 0, g 1, g 2] := by
    ext i; fin_cases i <;>
      simp [Fin.contractNth_apply_of_lt]
  rw [hs, hc0, hc1, hc2, hc3]
  have hcheck : ∀ a b c d : ZMod 2,
      z2CubicCochain ![Multiplicative.ofAdd b, Multiplicative.ofAdd c, Multiplicative.ofAdd d] +
        (-z2CubicCochain ![Multiplicative.ofAdd (a + b), Multiplicative.ofAdd c, Multiplicative.ofAdd d] +
         z2CubicCochain ![Multiplicative.ofAdd a, Multiplicative.ofAdd (b + c), Multiplicative.ofAdd d] +
         -z2CubicCochain ![Multiplicative.ofAdd a, Multiplicative.ofAdd b, Multiplicative.ofAdd (c + d)] +
         z2CubicCochain ![Multiplicative.ofAdd a, Multiplicative.ofAdd b, Multiplicative.ofAdd c]) = 0 := by
    intro a b c d
    let c2 : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 := fun x y z =>
      if x = 1 ∧ y = 1 ∧ z = 1 then 1 else 0
    have hc2 : ∀ x y z : ZMod 2,
        z2CubicCochain ![Multiplicative.ofAdd x, Multiplicative.ofAdd y, Multiplicative.ofAdd z] =
          ZMod.toAddCircle (c2 x y z) := by
      intro x y z
      simp only [z2CubicCochain, c2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        toAdd_ofAdd]
      split_ifs with h <;> simp [h]
    rw [hc2, hc2, hc2, hc2, hc2]
    have hlin : ZMod.toAddCircle (c2 b c d) +
        (-ZMod.toAddCircle (c2 (a + b) c d) + ZMod.toAddCircle (c2 a (b + c) d) +
          -ZMod.toAddCircle (c2 a b (c + d)) + ZMod.toAddCircle (c2 a b c)) =
        ZMod.toAddCircle (c2 b c d - c2 (a + b) c d + c2 a (b + c) d - c2 a b (c + d) + c2 a b c) := by
      simp only [sub_eq_add_neg, map_add, map_neg]
      abel
    rw [hlin]
    have h0 : c2 b c d - c2 (a + b) c d + c2 a (b + c) d - c2 a b (c + d) + c2 a b c = 0 := by
      clear hlin; revert a b c d; decide
    rw [h0, map_zero]
  have hmul : ∀ u v : Z2Mul, u * v = Multiplicative.ofAdd (u.toAdd + v.toAdd) := fun _ _ => rfl
  rw [hmul, hmul, hmul]
  have hres := hcheck (g 0).toAdd (g 1).toAdd (g 2).toAdd (g 3).toAdd
  simp only [ofAdd_toAdd] at hres
  exact hres

/-- The nontrivial `D = 3` bosonic `ℤ/2`-SPT cohomology class `[γ] ∈ H³(ℤ/2, U(1))`. -/
noncomputable def z2CubicClass : groupCohomology (trivialU1Rep Z2Mul) 3 :=
  groupCohomology.π (trivialU1Rep Z2Mul) 3
    (groupCohomology.cocyclesMk z2CubicCochain z2CubicCochain_is_cocycle)

/-- `z2CubicClass` is nonzero in `H³(ℤ/2, U(1))`. -/
theorem z2CubicClass_ne_zero : z2CubicClass ≠ 0 := by
  intro h0
  rw [z2CubicClass, groupCohomology_pi_eq_zero_iff_exists_coboundary] at h0
  rcases h0 with ⟨β, hβ⟩
  let u1 : Z2Mul := Multiplicative.ofAdd (1 : ZMod 2)
  let u0 : Z2Mul := Multiplicative.ofAdd (0 : ZMod 2)
  have hd : ∀ x y z : Z2Mul,
      β ![y, z] - β ![x * y, z] + β ![x, y * z] - β ![x, y] = z2CubicCochain ![x, y, z] := by
    intro x y z
    have hpt := congrArg (fun f : (Fin 3 → Z2Mul) → U1Coeff => f ![x, y, z]) hβ
    change (β (fun i : Fin 2 => (![x, y, z] : Fin 3 → Z2Mul) i.succ) +
        ∑ j : Fin 3, (-1 : ℤ) ^ ((j : ℕ) + 1) •
          β (Fin.contractNth j (· * ·) ![x, y, z])) = z2CubicCochain ![x, y, z] at hpt
    rw [Fin.sum_univ_three] at hpt
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_one, pow_two, pow_three,
      neg_one_sq, show (-1 : ℤ) ^ 3 = -1 by norm_num, neg_smul, one_smul] at hpt
    have hs : (fun i : Fin 2 => (![x, y, z] : Fin 3 → Z2Mul) i.succ) = ![y, z] := by
      ext i; fin_cases i <;> rfl
    have hc0 : Fin.contractNth 0 (· * ·) ![x, y, z] = ![x * y, z] := by
      ext i; fin_cases i <;>
        simp [Fin.contractNth_apply_of_eq, Fin.contractNth_apply_of_gt]
    have hc1 : Fin.contractNth 1 (· * ·) ![x, y, z] = ![x, y * z] := by
      ext i; fin_cases i <;>
        simp [Fin.contractNth_apply_of_lt, Fin.contractNth_apply_of_eq]
    have hc2 : Fin.contractNth 2 (· * ·) ![x, y, z] = ![x, y] := by
      ext i; fin_cases i <;>
        simp [Fin.contractNth_apply_of_lt]
    rw [hs, hc0, hc1, hc2] at hpt
    abel_nf at hpt ⊢
    exact hpt
  have h101 := hd u1 u0 u1
  have h111 := hd u1 u1 u1
  have hu10 : u1 * u0 = u1 := by decide
  have hu01 : u0 * u1 = u1 := by decide
  have hu11 : u1 * u1 = u0 := by decide
  have hc101 : z2CubicCochain ![u1, u0, u1] = 0 := by simp [z2CubicCochain, u1, u0]
  have hc111 : z2CubicCochain ![u1, u1, u1] = ZMod.toAddCircle (1 : ZMod 2) := by
    simp [z2CubicCochain, u1]
  rw [hu10, hu01, hc101] at h101
  rw [hu11, hc111] at h111
  have hadd := congrArg₂ (· + ·) h101 h111
  have hsum0 : (β ![u0, u1] - β ![u1, u1] + β ![u1, u1] - β ![u1, u0]) +
      (β ![u1, u1] - β ![u0, u1] + β ![u1, u0] - β ![u1, u1]) = 0 := by abel
  rw [hsum0, zero_add] at hadd
  have hne : ZMod.toAddCircle (1 : ZMod 2) ≠ 0 := by
    rw [ne_eq, ZMod.toAddCircle_eq_zero]
    decide
  exact hne hadd.symm

/-- Explicit 2-cochain `α : (Fin 2 → ℤ/4) → U(1)` trivializing `z4ToZ2^* γ`
(Witten 2016 Eq. 3.22). -/
def z4TrivializingCochain : (Fin 2 → Z4Mul) → U1Coeff := fun g =>
  ZMod.toAddCircle (((((g 0).toAdd.val % 2 : ℕ) : ZMod 4) * (g 1).toAdd))

private theorem toAddCircle_two_zmod4 :
    ZMod.toAddCircle (2 : ZMod 4) = ZMod.toAddCircle (1 : ZMod 2) := by
  rw [show (2 : ZMod 4) = ((2 : ℤ) : ZMod 4) by rfl,
    show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by rfl,
    ZMod.toAddCircle_intCast, ZMod.toAddCircle_intCast]
  congr 1
  norm_num

theorem d_z4TrivializingCochain_eq_pullback :
    _root_.inhomogeneousCochains.d (trivialU1Rep Z4Mul) 2 z4TrivializingCochain =
      (groupCohomology.cochainsMap z4ToZ2 (resPullbackHom z4ToZ2)).f 3 z2CubicCochain := by
  funext g
  change (z4TrivializingCochain (fun i : Fin 2 => g i.succ) +
      ∑ j : Fin 3, (-1 : ℤ) ^ ((j : ℕ) + 1) •
        z4TrivializingCochain (Fin.contractNth j (· * ·) g)) =
    z2CubicCochain (z4ToZ2 ∘ g)
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.zero_add, Nat.reduceAdd,
    pow_one, neg_one_sq, show (-1 : ℤ) ^ 3 = -1 by norm_num, neg_smul, one_smul]
  have hs : (fun i : Fin 2 => g i.succ) = ![g 1, g 2] := by
    ext i; fin_cases i <;> rfl
  have hc0 : Fin.contractNth 0 (· * ·) g = ![g 0 * g 1, g 2] := by
    ext i; fin_cases i <;> simp [Fin.contractNth_apply_of_eq, Fin.contractNth_apply_of_gt]
  have hc1 : Fin.contractNth 1 (· * ·) g = ![g 0, g 1 * g 2] := by
    ext i; fin_cases i <;> simp [Fin.contractNth_apply_of_lt, Fin.contractNth_apply_of_eq]
  have hc2 : Fin.contractNth 2 (· * ·) g = ![g 0, g 1] := by
    ext i; fin_cases i <;> simp [Fin.contractNth_apply_of_lt]
  rw [hs, hc0, hc1, hc2]
  have hcheck : ∀ a b c : ZMod 4,
      z4TrivializingCochain ![Multiplicative.ofAdd b, Multiplicative.ofAdd c] +
        (-z4TrivializingCochain ![Multiplicative.ofAdd (a + b), Multiplicative.ofAdd c] +
         z4TrivializingCochain ![Multiplicative.ofAdd a, Multiplicative.ofAdd (b + c)] +
         -z4TrivializingCochain ![Multiplicative.ofAdd a, Multiplicative.ofAdd b]) =
      z2CubicCochain (z4ToZ2 ∘ ![Multiplicative.ofAdd a, Multiplicative.ofAdd b,
        Multiplicative.ofAdd c]) := by
    intro a b c
    have hz4 : ∀ x y : ZMod 4,
        z4TrivializingCochain ![Multiplicative.ofAdd x, Multiplicative.ofAdd y] =
          ZMod.toAddCircle (((x.val % 2 : ℕ) : ZMod 4) * y) := fun _ _ => rfl
    rw [hz4, hz4, hz4, hz4]
    have hlin : ∀ u v w t : ZMod 4,
        ZMod.toAddCircle u + (-ZMod.toAddCircle v + ZMod.toAddCircle w + -ZMod.toAddCircle t) =
          ZMod.toAddCircle (u - v + w - t) := by
      intro u v w t
      simp only [sub_eq_add_neg, map_add, map_neg]
      abel
    rw [hlin]
    have hz : (((b.val % 2 : ℕ) : ZMod 4) * c - (((a + b).val % 2 : ℕ) : ZMod 4) * c +
        ((a.val % 2 : ℕ) : ZMod 4) * (b + c) - ((a.val % 2 : ℕ) : ZMod 4) * b) =
        if ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) a = 1 ∧
           ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) b = 1 ∧
           ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) c = 1 then (2 : ZMod 4) else 0 := by
      revert a b c; decide
    rw [hz]
    have hcast (x : ZMod 4) : (z4ToZ2 (Multiplicative.ofAdd x)).toAdd =
        ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) x := rfl
    simp only [z2CubicCochain, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, hcast, ZMod.castHom_apply] at ⊢
    by_cases hcond : (ZMod.cast a : ZMod 2) = 1 ∧ (ZMod.cast b : ZMod 2) = 1 ∧
        (ZMod.cast c : ZMod 2) = 1
    · simp [hcond, toAddCircle_two_zmod4]
    · simp [hcond]
  have hg : g = ![g 0, g 1, g 2] := by
    ext i; fin_cases i <;> rfl
  have hmul : ∀ u v : Z4Mul, u * v = Multiplicative.ofAdd (u.toAdd + v.toAdd) := fun _ _ => rfl
  rw [hmul, hmul]
  conv_rhs => rw [hg]
  have hres := hcheck (g 0).toAdd (g 1).toAdd (g 2).toAdd
  simp only [ofAdd_toAdd] at hres
  exact hres

/-- **Concrete `D = 3` Bosonic SPT Pullback Trivialization (Witten 2016 §3.3.2, Eq. 3.22)**:
The nontrivial bulk `H³(ℤ/2, U(1))` class `z2CubicClass` pulls back to `0` in `H³(ℤ/4, U(1))`
along `z4ToZ2 : ℤ/4 →* ℤ/2`. -/
theorem z2_to_z4_spt_pullback_trivial :
    pullbackCohomology z4ToZ2 3 z2CubicClass = 0 := by
  unfold z2CubicClass pullbackCohomology
  have hπ := congrArg (fun φ => φ (groupCohomology.cocyclesMk z2CubicCochain z2CubicCochain_is_cocycle))
    (groupCohomology.π_map z4ToZ2 (resPullbackHom z4ToZ2) 3)
  simp only [CategoryTheory.comp_apply] at hπ
  erw [hπ]
  have hcyc :
      (groupCohomology.cocyclesMap z4ToZ2 (resPullbackHom z4ToZ2) 3)
        (groupCohomology.cocyclesMk z2CubicCochain z2CubicCochain_is_cocycle) =
      groupCohomology.cocyclesMk
        ((groupCohomology.cochainsMap z4ToZ2 (resPullbackHom z4ToZ2)).f 3 z2CubicCochain)
        (by
          have hc := (groupCohomology.cochainsMap z4ToZ2 (resPullbackHom z4ToZ2)).comm' 3 4 rfl
          rw [groupCohomology.inhomogeneousCochains.d_def,
            groupCohomology.inhomogeneousCochains.d_def] at hc
          have hc' := congrArg (fun φ => φ z2CubicCochain) hc
          simp only [CategoryTheory.comp_apply] at hc'
          change (_root_.inhomogeneousCochains.d (trivialU1Rep Z4Mul) 3)
            (((groupCohomology.cochainsMap z4ToZ2 (resPullbackHom z4ToZ2)).f 3) z2CubicCochain) = 0
          rw [show ((_root_.inhomogeneousCochains.d (trivialU1Rep Z4Mul) 3)
            (((groupCohomology.cochainsMap z4ToZ2 (resPullbackHom z4ToZ2)).f 3) z2CubicCochain)) =
            (((groupCohomology.cochainsMap z4ToZ2 (resPullbackHom z4ToZ2)).f 4)
              ((_root_.inhomogeneousCochains.d (trivialU1Rep Z2Mul) 3) z2CubicCochain)) from hc']
          rw [z2CubicCochain_is_cocycle, map_zero]) := by
    apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles (trivialU1Rep Z4Mul) 3)).1
      inferInstance
    change (groupCohomology.cocyclesMap z4ToZ2 (resPullbackHom z4ToZ2) 3 ≫
      groupCohomology.iCocycles (trivialU1Rep Z4Mul) 3) _ =
      groupCohomology.iCocycles (trivialU1Rep Z4Mul) 3 _
    rw [HomologicalComplex.cyclesMap_i, groupCohomology.iCocycles_mk]
    change ((groupCohomology.cochainsMap z4ToZ2 (resPullbackHom z4ToZ2)).f 3)
      (groupCohomology.iCocycles (trivialU1Rep Z2Mul) 3
        (groupCohomology.cocyclesMk z2CubicCochain z2CubicCochain_is_cocycle)) = _
    rw [groupCohomology.iCocycles_mk]
  rw [hcyc]
  exact groupCohomology_pi_eq_zero_of_coboundary (trivialU1Rep Z4Mul)
    ((groupCohomology.cochainsMap z4ToZ2 (resPullbackHom z4ToZ2)).f 3 z2CubicCochain)
    _ z4TrivializingCochain d_z4TrivializingCochain_eq_pullback

/-- Restricting `z4TrivializingCochain` along `z2ToZ4 : ℤ/2 →* ℤ/4` vanishes identically,
so the resulting boundary `ℤ/2` 2-cocycle class in `H²(ℤ/2, U(1))` is trivial. -/
theorem z4TrivializingCochain_restrict_z2_eq_zero (g : Fin 2 → Z2Mul) :
    z4TrivializingCochain (z2ToZ4 ∘ g) = 0 := by
  dsimp [z4TrivializingCochain, z2ToZ4]
  have h0 : ((2 * ((g 0).toAdd.val : ZMod 4)).val % 2) = 0 := by
    have hcheck : ∀ x : ZMod 2, (2 * (x.val : ZMod 4)).val % 2 = 0 := by decide
    exact hcheck (g 0).toAdd
  change ZMod.toAddCircle (((((2 * ((g 0).toAdd.val : ZMod 4)).val % 2 : ℕ) : ZMod 4) * _)) = 0
  rw [h0]
  simp

end BosonicSPTPullback

end InfoGeometry.CondensedMatter.WittenBoundaryExtension16

