/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.BRSTExactClassZeroBridge
import InfoGeometry.Canonical.PhysicalGhostZeroBRSTCohomologyBridge
import InfoGeometry.Canonical.KreinSpaceBRSTUnitarityBridge
import InfoGeometry.Canonical.BRSTQuotientPairingWellDefinedBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.BRSTQuotientInnerProductLiftBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
open InfoGeometry.Canonical.BRSTExactClassZeroBridge
open InfoGeometry.Canonical.PhysicalGhostZeroBRSTCohomologyBridge
open InfoGeometry.Canonical.KreinSpaceBRSTUnitarityBridge
open InfoGeometry.Canonical.BRSTQuotientPairingWellDefinedBridge

variable {R H : Type*} [Ring R] [AddCommGroup H] [Module R H]

/-- The boundary map with codomain restricted to cycles. Nilpotency supplies
the proof that every value of `Q` is closed. -/
def brstBoundaryMap (q : Module.End R H) (hq2 : q.comp q = 0) :
    H →ₗ[R] LinearMap.ker q where
  toFun x := ⟨q x, by
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun hq2 x⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- A cycle is a boundary in the restricted complex exactly when its
underlying vector belongs to the ordinary operator range. -/
theorem mem_brstBoundaryMap_range_iff
    (q : Module.End R H) (hq2 : q.comp q = 0) (x : LinearMap.ker q) :
    x ∈ LinearMap.range (brstBoundaryMap q hq2) ↔
      (x : H) ∈ LinearMap.range q := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact hy

/-- **Theorem**: Well-definedness condition for Quotient Pairing on BRST Cohomology Module H_Q = Ker Q / Im Q. -/
theorem brst_quotient_pairing_well_defined_lift
    (inner : H → H → R)
    (q : Module.End R H)
    (hq2 : q.comp q = 0)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    (h_zero2 : ∀ x, inner x 0 = 0)
    (h_add1 : ∀ x y z, inner (x + y) z = inner x z + inner y z)
    (h_add2 : ∀ x y z, inner x (y + z) = inner x y + inner x z)
    (u v u' v' : LinearMap.ker q)
    (hu : u - u' ∈ LinearMap.range (brstBoundaryMap q hq2))
    (hv : v - v' ∈ LinearMap.range (brstBoundaryMap q hq2)) :
    inner u.1 v.1 = inner u'.1 v'.1 := by
  obtain ⟨chi, hchi⟩ := hu
  obtain ⟨eta, heta⟩ := hv
  have h_u : u.1 = u'.1 + q chi := by
    have h := congrArg Subtype.val hchi
    change q chi = u.1 - u'.1 at h
    calc
      u.1 = (u.1 - u'.1) + u'.1 := by abel
      _ = q chi + u'.1 := by rw [h]
      _ = u'.1 + q chi := by abel
  have h_v : v.1 = v'.1 + q eta := by
    have h := congrArg Subtype.val heta
    change q eta = v.1 - v'.1 at h
    calc
      v.1 = (v.1 - v'.1) + v'.1 := by abel
      _ = q eta + v'.1 := by rw [h]
      _ = v'.1 + q eta := by abel
  rw [h_u, h_v]
  have h_phys_u : isPhysicalState q u'.1 := u'.2
  have h_phys_v : isPhysicalState q v'.1 := v'.2
  exact brst_quotient_pairing_gauge_invariant inner q hq2 h_adj h_zero1 h_zero2 h_add1 h_add2 u'.1 v'.1 chi eta h_phys_u h_phys_v

/-- **Definition**: General BRST Cohomology Quotient Module H_Q = Ker Q / Im Q for Module H. -/
abbrev brstCohomologyQuotientModule (q : Module.End R H) (hq2 : q.comp q = 0) :=
  LinearMap.ker q ⧸ LinearMap.range (brstBoundaryMap q hq2)

/-- **Definition**: Literal Physical Inner Product Lift on the BRST Cohomology Quotient Module H_Q = Ker Q / Im Q. -/
def brstQuotientPairing
    (inner : H → H → R)
    (q : Module.End R H)
    (hq2 : q.comp q = 0)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    (h_zero2 : ∀ x, inner x 0 = 0)
    (h_add1 : ∀ x y z, inner (x + y) z = inner x z + inner y z)
    (h_add2 : ∀ x y z, inner x (y + z) = inner x y + inner x z)
    (u v : brstCohomologyQuotientModule q hq2) : R :=
  Quotient.liftOn₂ u v (fun u_val v_val => inner u_val.1 v_val.1) (by
    intro u1 v1 u2 v2 hu hv
    have h_eq1 : Submodule.Quotient.mk u1 =
        (Submodule.Quotient.mk u2 : brstCohomologyQuotientModule q hq2) := Quotient.sound hu
    have h_eq2 : Submodule.Quotient.mk v1 =
        (Submodule.Quotient.mk v2 : brstCohomologyQuotientModule q hq2) := Quotient.sound hv
    rw [Submodule.Quotient.eq] at h_eq1 h_eq2
    exact brst_quotient_pairing_well_defined_lift inner q hq2 h_adj h_zero1 h_zero2 h_add1 h_add2 u1 v1 u2 v2 h_eq1 h_eq2)

/-- **Theorem**: Literal Evaluation of Physical BRST Quotient Pairing ⟨[ψ], [φ]⟩ = ⟨ψ, φ⟩ for Closed Physical States. -/
theorem brst_quotient_pairing_eval
    (inner : H → H → R)
    (q : Module.End R H)
    (hq2 : q.comp q = 0)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    (h_zero2 : ∀ x, inner x 0 = 0)
    (h_add1 : ∀ x y z, inner (x + y) z = inner x z + inner y z)
    (h_add2 : ∀ x y z, inner x (y + z) = inner x y + inner x z)
    (u v : LinearMap.ker q) :
    brstQuotientPairing inner q hq2 h_adj h_zero1 h_zero2 h_add1 h_add2 (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      inner u.1 v.1 := rfl

theorem master_brst_quotient_inner_product_lift_synthesis
    (inner : H → H → R)
    (q : Module.End R H)
    (hq2 : q.comp q = 0)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    (h_zero2 : ∀ x, inner x 0 = 0)
    (h_add1 : ∀ x y z, inner (x + y) z = inner x z + inner y z)
    (h_add2 : ∀ x y z, inner x (y + z) = inner x y + inner x z)
    (u v : LinearMap.ker q) :
    (brstQuotientPairing inner q hq2 h_adj h_zero1 h_zero2 h_add1 h_add2 (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      inner u.1 v.1) :=
  rfl

end InfoGeometry.Canonical.BRSTQuotientInnerProductLiftBridge
