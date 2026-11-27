/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Colimit.Module
import Mathlib.Data.Dyadic
import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.Algebra.FiniteProjectiveModuleGrothendieck
import InfoGeometry.Algebra.CuntzQuotientDiracBridge
import InfoGeometry.OperatorAlgebra.RealProjectionMurrayVonNeumann
import InfoGeometry.Canonical.CantorCuntzRangeProjectionMurrayVonNeumann
import InfoGeometry.Canonical.PrimitiveCuntzIsometry
import InfoGeometry.Canonical.PrimitiveCuntzCohomology
import InfoGeometry.Canonical.UHFCohomologyColimit
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.DyadicDimensionGroup
import InfoGeometry.Canonical.RealUHFProjectionRankSystem

/-!
# Cuntz `K₀(O₂) = 0` and the UHF Dimension Group `K₀(M_{2^∞}) ≃+ ℤ[1/2]`

This module proves two foundational K-theoretic results using the repository's
canonical Grothendieck, Cuntz, Murray–von Neumann, and dyadic-limit owners:

1. **Cuntz `K₀(O₂)` unit vanishing**: In the genuine algebraic Grothendieck group
   `FiniteProjectiveModuleGrothendieck.K0 A` of finitely generated projective
   left `A`-modules under direct sum, an orthogonal idempotent partition
   `P_L + P_R = 1` with Murray–von Neumann equivalences `P_L ~ 1 ~ P_R` yields
   `[1] = [P_L] + [P_R] = [1] + [1]` and hence `[1] = 0`. This is established
   uniformly for every `CuntzO2Carrier A`, every `[UHFAlgebra A]`, and the
   concrete nontrivial tensor-quotient algebra `CuntzAlg 2`.
2. **UHF dimension group**: Mathlib's `AddCommGroup.DirectLimit` of `ℤ` under the
   stage-doubling bonding maps `z ↦ 2 * z` (`UHFDimensionGroup`) is proved
   additively isomorphic (`≃+`) to both Mathlib's native `Dyadic` rationals and
   the repository's `DyadicRational` / `DyadicDirectLimit`, with
   `uhfDimensionGroup_unit_ne_zero : uhfStageInclusion 0 1 ≠ 0` contrasting
   `K₀(M_{2^∞}) ≃+ ℤ[1/2]` against `K₀(O₂)`.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzK0AndUHFDimensionGroup

open InfoGeometry.Algebra.FiniteProjectiveModuleGrothendieck
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzQuotientDiracBridge
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Topology
open InfoGeometry.GrandUnification.UHF
open InfoGeometry.Canonical.PrimitiveCuntzIsometry
open InfoGeometry.Canonical.PrimitiveCuntzCohomology
open InfoGeometry.Canonical.UHFCohomology
open InfoGeometry.Canonical.UHFBoundaryExactSequence

/-! ## Part A: Genuine `K₀(O₂)` Unit Vanishing -/

section CuntzK0

universe u

/-- `K₀(R)` inherits its abelian group structure from `Grothendieck (ProjectiveModuleClass R)`. -/
instance instAddCommGroupK0 (R : Type u) [Ring R] : AddCommGroup (K0 R) :=
  inferInstanceAs (AddCommGroup (Grothendieck (ProjectiveModuleClass R)))

/-- The free rank-1 left `A`-module `A` as a finitely generated projective module. -/
def unitProjModule (A : Type u) [Ring A] : FiniteProjectiveModule A := by
  letI : Module.Finite A A := Module.Finite.self A
  letI : Module.Projective A A :=
    Module.Projective.of_equiv (LinearEquiv.funUnique (Fin 1) A A)
  exact ⟨ModuleCat.of A A, inferInstance, inferInstance⟩

/-- The class `[1] = [A]` in `K₀(A)`. -/
def unitK0Class (A : Type u) [Ring A] : K0 A :=
  k0Class A (unitProjModule A)

/-- The cyclic left `A`-submodule `A * p` associated with an idempotent `p * p = p`. -/
def leftIdealOfIdempotent {A : Type u} [Ring A] (p : A) (hp : p * p = p) :
    FiniteProjectiveModule A := by
  let r : A →ₗ[A] LinearMap.range (LinearMap.mulRight A p) :=
    (LinearMap.mulRight A p).rangeRestrict
  let i : LinearMap.range (LinearMap.mulRight A p) →ₗ[A] A := Submodule.subtype _
  have hfin : Module.Finite A (LinearMap.range (LinearMap.mulRight A p)) :=
    Module.Finite.of_surjective r (LinearMap.surjective_rangeRestrict _)
  have hsplit : r.comp i = LinearMap.id := by
    ext x
    rcases x with ⟨_, a, rfl⟩
    change (a * p) * p = a * p
    rw [mul_assoc, hp]
  haveI : Module.Projective A A :=
    Module.Projective.of_equiv (LinearEquiv.funUnique (Fin 1) A A)
  have hproj : Module.Projective A (LinearMap.range (LinearMap.mulRight A p)) :=
    Module.Projective.of_split i r hsplit
  exact ⟨ModuleCat.of A (LinearMap.range (LinearMap.mulRight A p)), hfin, hproj⟩

/-- The class `[A * p]` in `K₀(A)` for an idempotent `p`. -/
def k0ClassOfIdempotent {A : Type u} [Ring A] (p : A) (hp : p * p = p) : K0 A :=
  k0Class A (leftIdealOfIdempotent p hp)

/-- `[A * 1] = [1]` in `K₀(A)`. -/
theorem k0ClassOfIdempotent_one_eq_unit (A : Type u) [Ring A] :
    k0ClassOfIdempotent (1 : A) (mul_one 1) = unitK0Class A := by
  have hrange : LinearMap.range (LinearMap.mulRight A (1 : A)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact ⟨x, mul_one x⟩
  let e : LinearMap.range (LinearMap.mulRight A (1 : A)) ≃ₗ[A] A :=
    LinearEquiv.ofTop _ hrange
  refine congrArg (grothendieckMap (ProjectiveModuleClass A)) ?_
  apply Quotient.sound
  exact ⟨e.toModuleIso⟩

/-- Murray–von Neumann equivalent idempotents determine equal classes in `K₀(A)`. -/
theorem k0ClassOfIdempotent_eq_of_mvn {A : Type u} [Ring A] [StarRing A]
    {p q : A} (hp : p * p = p) (hq : q * q = q)
    (hmvn : MurrayVonNeumannEquivalent p q) :
    k0ClassOfIdempotent p hp = k0ClassOfIdempotent q hq := by
  rcases hmvn with ⟨v, hvp, hvq⟩
  have hpv : p * star v = star v * q := by
    calc
      p * star v = (star v * v) * star v := by rw [← hvp]
      _ = star v * (v * star v) := by rw [mul_assoc]
      _ = star v * q := by rw [hvq]
  have hqv : q * v = v * p := by
    calc
      q * v = (v * star v) * v := by rw [← hvq]
      _ = v * (star v * v) := by rw [mul_assoc]
      _ = v * p := by rw [hvp]
  let e : LinearMap.range (LinearMap.mulRight A p) ≃ₗ[A]
      LinearMap.range (LinearMap.mulRight A q) :=
    { toFun := fun x => ⟨x.1 * star v, by
        rcases x.2 with ⟨a, ha⟩
        refine ⟨a * star v, ?_⟩
        change (a * star v) * q = x.1 * star v
        rw [← ha]
        change (a * star v) * q = (a * p) * star v
        rw [mul_assoc, ← hpv, ← mul_assoc]⟩
      invFun := fun y => ⟨y.1 * v, by
        rcases y.2 with ⟨b, hb⟩
        refine ⟨b * v, ?_⟩
        change (b * v) * p = y.1 * v
        rw [← hb]
        change (b * v) * p = (b * q) * v
        rw [mul_assoc, ← hqv, ← mul_assoc]⟩
      map_add' := fun x y => by
        apply Subtype.ext
        exact add_mul x.1 y.1 (star v)
      map_smul' := fun a x => by
        apply Subtype.ext
        change (a * x.1) * star v = a * (x.1 * star v)
        rw [mul_assoc]
      left_inv := fun x => by
        rcases x with ⟨_, a, rfl⟩
        apply Subtype.ext
        change ((a * p) * star v) * v = a * p
        rw [mul_assoc (a * p) (star v) v, hvp, mul_assoc, hp]
      right_inv := fun y => by
        rcases y with ⟨_, b, rfl⟩
        apply Subtype.ext
        change ((b * q) * v) * star v = b * q
        rw [mul_assoc (b * q) v (star v), hvq, mul_assoc, hq] }
  refine congrArg (grothendieckMap (ProjectiveModuleClass A)) ?_
  apply Quotient.sound
  exact ⟨e.toModuleIso⟩

/-- An orthogonal idempotent decomposition `p + q = 1` splits `[1] = [p] + [q]` in `K₀(A)`. -/
theorem k0ClassOfIdempotent_add_of_orthogonal {A : Type u} [Ring A]
    {p q : A} (hp : p * p = p) (hq : q * q = q)
    (hpq : p * q = 0) (hqp : q * p = 0) (hsum : p + q = 1) :
    unitK0Class A = k0ClassOfIdempotent p hp + k0ClassOfIdempotent q hq := by
  let e : A ≃ₗ[A]
      (LinearMap.range (LinearMap.mulRight A p) ×
       LinearMap.range (LinearMap.mulRight A q)) :=
    { toFun := fun x => (⟨x * p, x, rfl⟩, ⟨x * q, x, rfl⟩)
      invFun := fun yz => yz.1.1 + yz.2.1
      map_add' := fun x y => by
        ext <;> simp [add_mul]
      map_smul' := fun a x => by
        ext <;> simp [smul_eq_mul, mul_assoc]
      left_inv := fun x => by
        change x * p + x * q = x
        rw [← mul_add, hsum, mul_one]
      right_inv := fun yz => by
        rcases yz with ⟨⟨_, a, rfl⟩, ⟨_, b, rfl⟩⟩
        ext
        · change (a * p + b * q) * p = a * p
          rw [add_mul, mul_assoc, hp, mul_assoc, hqp, mul_zero, add_zero]
        · change (a * p + b * q) * q = b * q
          rw [add_mul, mul_assoc, hpq, mul_zero, zero_add, mul_assoc, hq] }
  let uCls : ProjectiveModuleClass A := Quotient.mk (moduleIsoSetoid A) (unitProjModule A)
  let pCls : ProjectiveModuleClass A :=
    Quotient.mk (moduleIsoSetoid A) (leftIdealOfIdempotent p hp)
  let qCls : ProjectiveModuleClass A :=
    Quotient.mk (moduleIsoSetoid A) (leftIdealOfIdempotent q hq)
  have hclass : uCls = pCls + qCls := by
    apply Quotient.sound
    exact ⟨e.toModuleIso⟩
  have hmap :
      grothendieckMap (ProjectiveModuleClass A) uCls =
        grothendieckMap (ProjectiveModuleClass A) pCls +
          grothendieckMap (ProjectiveModuleClass A) qCls := by
    rw [hclass, (grothendieckMap (ProjectiveModuleClass A)).map_add]
  exact hmap

/-- Splitting `[1] = [P_L] + [P_R]` in `K₀(A)` for any `CuntzO2Carrier A`. -/
theorem cuntz_unit_k0_eq_split {A : Type u} [Ring A] [StarRing A] (C : CuntzO2Carrier A) :
    unitK0Class A =
      k0ClassOfIdempotent (CuntzO2Carrier.leftRangeProjection C)
        (CuntzO2Carrier.leftRangeProjection_idempotent_murrayVonNeumann C) +
      k0ClassOfIdempotent (CuntzO2Carrier.rightRangeProjection C)
        (CuntzO2Carrier.rightRangeProjection_idempotent_murrayVonNeumann C) :=
  k0ClassOfIdempotent_add_of_orthogonal
    (CuntzO2Carrier.leftRangeProjection_idempotent_murrayVonNeumann C)
    (CuntzO2Carrier.rightRangeProjection_idempotent_murrayVonNeumann C)
    (CuntzO2Carrier.leftRangeProjection_mul_rightRangeProjection_eq_zero_murrayVonNeumann C)
    (CuntzO2Carrier.rightRangeProjection_mul_leftRangeProjection_eq_zero_murrayVonNeumann C)
    (CuntzO2Carrier.rangeProjection_sum_one C)

/-- `[P_L] = [1]` in `K₀(A)` via Murray–von Neumann equivalence. -/
theorem cuntz_leftProj_k0_eq_unit {A : Type u} [Ring A] [StarRing A] (C : CuntzO2Carrier A) :
    k0ClassOfIdempotent (CuntzO2Carrier.leftRangeProjection C)
      (CuntzO2Carrier.leftRangeProjection_idempotent_murrayVonNeumann C) = unitK0Class A := by
  rw [k0ClassOfIdempotent_eq_of_mvn
    (CuntzO2Carrier.leftRangeProjection_idempotent_murrayVonNeumann C)
    (mul_one (1 : A))
    (CuntzO2Carrier.leftRangeProjection_murrayVonNeumannEquivalent_unit C)]
  exact k0ClassOfIdempotent_one_eq_unit A

/-- `[P_R] = [1]` in `K₀(A)` via Murray–von Neumann equivalence. -/
theorem cuntz_rightProj_k0_eq_unit {A : Type u} [Ring A] [StarRing A] (C : CuntzO2Carrier A) :
    k0ClassOfIdempotent (CuntzO2Carrier.rightRangeProjection C)
      (CuntzO2Carrier.rightRangeProjection_idempotent_murrayVonNeumann C) = unitK0Class A := by
  rw [k0ClassOfIdempotent_eq_of_mvn
    (CuntzO2Carrier.rightRangeProjection_idempotent_murrayVonNeumann C)
    (mul_one (1 : A))
    (CuntzO2Carrier.rightRangeProjection_murrayVonNeumannEquivalent_unit C)]
  exact k0ClassOfIdempotent_one_eq_unit A

/-- `[1] = [1] + [1]` in `K₀(A)` for any `CuntzO2Carrier A`. -/
theorem cuntz_O2_unit_k0_eq_two_mul {A : Type u} [Ring A] [StarRing A] (C : CuntzO2Carrier A) :
    unitK0Class A = unitK0Class A + unitK0Class A := by
  calc
    unitK0Class A
        = k0ClassOfIdempotent (CuntzO2Carrier.leftRangeProjection C)
            (CuntzO2Carrier.leftRangeProjection_idempotent_murrayVonNeumann C) +
          k0ClassOfIdempotent (CuntzO2Carrier.rightRangeProjection C)
            (CuntzO2Carrier.rightRangeProjection_idempotent_murrayVonNeumann C) :=
          cuntz_unit_k0_eq_split C
    _ = unitK0Class A + unitK0Class A := by
          rw [cuntz_leftProj_k0_eq_unit C, cuntz_rightProj_k0_eq_unit C]

/-- Main Cuntz `K₀(O₂)` vanishing theorem: `[1] = 0` in `K₀(A)`. -/
theorem cuntz_O2_k0_unit_eq_zero {A : Type u} [Ring A] [StarRing A] (C : CuntzO2Carrier A) :
    unitK0Class A = 0 := by
  have h := cuntz_O2_unit_k0_eq_two_mul C
  have h' : unitK0Class A + 0 = unitK0Class A + unitK0Class A := by
    simpa [add_zero] using h
  exact (add_left_cancel h').symm

/-- Every `UHFAlgebra A` carries a `CuntzO2Carrier A` structure via `(S_L, S_R)`. -/
def uhfToCuntzO2Carrier (A : Type u) [NormedRing A] [StarRing A] [CompleteSpace A]
    [UHFAlgebra A] : CuntzO2Carrier A where
  S := ![UHFAlgebra.S_L, UHFAlgebra.S_R]
  isometry := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using UHFAlgebra.isometry_L (A := A)
    · simpa using cuntz_orthogonality (A := A)
    · simpa using cuntz_dual_orthogonality (A := A)
    · simpa using UHFAlgebra.isometry_R (A := A)
  range_sum := by
    simp [Fin.sum_univ_two]
    exact cuntz_partition_exactness (A := A)

/-- For any `[UHFAlgebra A]`, `[1] = [P_L] + [P_R] = [1] + [1]` and `[1] = 0` in `K₀(A)`. -/
theorem uhfAlgebra_k0_unit_eq_zero (A : Type u) [NormedRing A] [StarRing A] [CompleteSpace A]
    [UHFAlgebra A] : unitK0Class A = 0 :=
  cuntz_O2_k0_unit_eq_zero (uhfToCuntzO2Carrier A)

/-- `[UHF_transition S_L S_R 1] = 0` in `K₀(A)` because `UHF_transition` fixes `1`. -/
theorem uhfTransition_one_k0_eq_zero (A : Type u) [NormedRing A] [StarRing A] [CompleteSpace A]
    [UHFAlgebra A] :
    k0ClassOfIdempotent
        (UHF_transition (UHFAlgebra.S_L (A := A)) (UHFAlgebra.S_R (A := A)) 1)
        (UHF_transition_one_is_projection _ _ (cuntz_partition_exactness (A := A))) = 0 := by
  have h_id : UHF_transition (UHFAlgebra.S_L (A := A)) (UHFAlgebra.S_R (A := A)) 1 = 1 :=
    UHF_transition_one_eq_one _ _ (cuntz_partition_exactness (A := A))
  have h_cls :
      k0ClassOfIdempotent
          (UHF_transition (UHFAlgebra.S_L (A := A)) (UHFAlgebra.S_R (A := A)) 1)
          (UHF_transition_one_is_projection _ _ (cuntz_partition_exactness (A := A))) =
        k0ClassOfIdempotent (1 : A) (mul_one 1) := by
    refine k0ClassOfIdempotent_eq_of_mvn _ (mul_one 1) ?_
    refine ⟨1, ?_, ?_⟩ <;> simp [h_id]
  rw [h_cls, k0ClassOfIdempotent_one_eq_unit]
  exact uhfAlgebra_k0_unit_eq_zero A

end CuntzK0

/-! ## Concrete Nontrivial Witness: `CuntzAlg 2` & `T16` Non-Commutativity -/

section ConcreteCuntzO2

/-- Constructive `CuntzO2Carrier` inhabitant on the tensor-quotient algebra `CuntzAlg 2`. -/
def cuntzAlg2Carrier : CuntzO2Carrier (CuntzAlg 2) :=
  quotientCuntzNAlgebra 2

private theorem boundary_ops_orth (i j : Fin 2) :
    (![star_S_L_op_linear, star_S_R_op_linear] i : Module.End ℂ ((ℕ → Bool) → ℂ)) *
      ![S_L_op_linear, S_R_op_linear] j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> ext f x
  · exact congrFun (star_S_L_op_S_L_op f) x
  · exact congrFun (star_S_L_op_S_R_op f) x
  · exact congrFun (star_S_R_op_S_L_op f) x
  · exact congrFun (star_S_R_op_S_R_op f) x

private theorem boundary_ops_partition :
    (∑ i : Fin 2,
      (![S_L_op_linear, S_R_op_linear] i : Module.End ℂ ((ℕ → Bool) → ℂ)) *
        ![star_S_L_op_linear, star_S_R_op_linear] i) = 1 := by
  rw [Fin.sum_univ_two]
  ext f x
  exact congrFun (cuntz_partition_op f) x

/-- Representation of `CuntzAlg 2` on Cantor boundary functions `(ℕ → Bool) → ℂ`. -/
def cuntzAlg2BoundaryRep : CuntzAlg 2 →ₐ[ℂ] Module.End ℂ ((ℕ → Bool) → ℂ) :=
  InfoGeometry.Algebra.CuntzTensorQuotient.lift 2
    ![S_L_op_linear, S_R_op_linear]
    ![star_S_L_op_linear, star_S_R_op_linear]
    boundary_ops_orth
    boundary_ops_partition

/-- Closed `T16` non-commutativity witness on the concrete Cantor shift operators. -/
theorem uhfBoundary_shift_noncomm :
    S_L_op_linear * S_R_op_linear ≠ S_R_op_linear * S_L_op_linear := by
  intro h
  have hval := congrArg (fun T : Module.End ℂ ((ℕ → Bool) → ℂ) =>
    T (fun _ => (1 : ℂ)) (fun n => decide (n = 1))) h
  simp [S_L_op_linear, S_R_op_linear, S_L_op, S_R_op,
    InfoGeometry.Canonical.CuntzCantorBoundaryShift.tail] at hval

/-- Closed `T16` non-commutativity witness for the concrete `CuntzAlg 2` generators. -/
theorem cuntzAlg2_generators_noncomm :
    cuntzS 2 0 * cuntzS 2 1 ≠ cuntzS 2 1 * cuntzS 2 0 := by
  intro h
  apply uhfBoundary_shift_noncomm
  have hrep := congrArg cuntzAlg2BoundaryRep h
  simpa [cuntzAlg2BoundaryRep, map_mul] using hrep

/-- `CuntzAlg 2` is genuinely nontrivial (no `0 = 1` collapse). -/
theorem cuntzAlg2_nontrivial : Nontrivial (CuntzAlg 2) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h01
  have hrep := congrArg cuntzAlg2BoundaryRep h01
  rw [map_zero, map_one] at hrep
  have hval := congrArg (fun T : Module.End ℂ ((ℕ → Bool) → ℂ) =>
    T (fun _ => (1 : ℂ)) (fun _ => false)) hrep
  simp at hval

/-- General `T16` non-commutativity of generators for any nontrivial `CuntzO2Carrier Op`. -/
theorem cuntzO2_generators_noncomm {Op : Type u} [Ring Op] [StarRing Op] [Nontrivial Op]
    (C : CuntzO2Carrier Op) :
    CuntzO2Carrier.S_left C * CuntzO2Carrier.S_right C ≠
      CuntzO2Carrier.S_right C * CuntzO2Carrier.S_left C := by
  intro h
  have hmul : star (CuntzO2Carrier.S_left C) *
      (CuntzO2Carrier.S_left C * CuntzO2Carrier.S_right C) =
      star (CuntzO2Carrier.S_left C) *
        (CuntzO2Carrier.S_right C * CuntzO2Carrier.S_left C) := by
    rw [h]
  rw [← mul_assoc, CuntzO2Carrier.left_isometry C, one_mul,
    ← mul_assoc, (CuntzO2Carrier.orthogonal_ranges C).1, zero_mul] at hmul
  have h1 : (1 : Op) = 0 := by
    calc
      (1 : Op) = star (CuntzO2Carrier.S_right C) * CuntzO2Carrier.S_right C :=
        (CuntzO2Carrier.right_isometry C).symm
      _ = star (CuntzO2Carrier.S_right C) * 0 := by rw [hmul]
      _ = 0 := mul_zero _
  exact one_ne_zero h1

/-- General `T16` non-commutativity of `S_left` and `star S_left` in `CuntzO2Carrier Op`. -/
theorem cuntzO2_isometry_noncomm {Op : Type u} [Ring Op] [StarRing Op] [Nontrivial Op]
    (C : CuntzO2Carrier Op) :
    CuntzO2Carrier.S_left C * star (CuntzO2Carrier.S_left C) ≠
      star (CuntzO2Carrier.S_left C) * CuntzO2Carrier.S_left C := by
  rw [CuntzO2Carrier.left_isometry C]
  exact CuntzO2Carrier.leftRangeProjection_ne_one C

/-- `[1] = 0` in `K₀(CuntzAlg 2)` on the concrete nontrivial `O₂` carrier. -/
theorem cuntzAlg2_k0_unit_eq_zero : unitK0Class (CuntzAlg 2) = 0 :=
  cuntz_O2_k0_unit_eq_zero cuntzAlg2Carrier

end ConcreteCuntzO2

/-! ## Part B: UHF Dimension Group `K₀(M_{2^∞}) ≃+ ℤ[1/2]` via `AddCommGroup.DirectLimit` -/

section UHFDimensionGroup

/-- Stage-transition bonding map `z ↦ 2^(j - i) * z` on `ℤ` for `i ≤ j`. -/
def uhfK0Bond (i j : ℕ) (_ : i ≤ j) : ℤ →+ ℤ where
  toFun z := (2 : ℤ) ^ (j - i) * z
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

/-- The stage-doubling bonds form a `DirectedSystem` over `(ℕ, ≤)`. -/
instance uhfK0DirectedSystem :
    DirectedSystem (fun _ : ℕ => ℤ) (fun i j h => uhfK0Bond i j h) where
  map_self i z := by simp [uhfK0Bond]
  map_map i j k hij hjk z := by
    simp only [uhfK0Bond, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    have hexp : i - j + (j - k) = i - k := by omega
    rw [← mul_assoc, ← pow_add, hexp]

/-- One-step specialization coincides with `DyadicDimensionGroup.dyadicBond`. -/
theorem uhfK0Bond_succ (n : ℕ) :
    uhfK0Bond n (n + 1) (Nat.le_succ n) = dyadicBond n := by
  apply AddMonoidHom.ext
  intro z
  simp [uhfK0Bond, dyadicBond]

/-- The UHF dimension group `K₀(M_{2^∞})` defined as `AddCommGroup.DirectLimit`
of `ℤ` along the `x ↦ 2 * x` bonding maps. -/
abbrev UHFDimensionGroup : Type :=
  AddCommGroup.DirectLimit (fun _ : ℕ => ℤ) uhfK0Bond

/-- Canonical stage inclusion `ℤ →+ UHFDimensionGroup` from stage `n`. -/
def uhfStageInclusion (n : ℕ) : ℤ →+ UHFDimensionGroup :=
  AddCommGroup.DirectLimit.of (fun _ : ℕ => ℤ) uhfK0Bond n

/-- Constructive unit inhabitant of `UHFDimensionGroup` at stage `0`. -/
def uhfDimensionGroupUnit : UHFDimensionGroup :=
  uhfStageInclusion 0 1

theorem uhfStageInclusion_succ (n : ℕ) (z : ℤ) :
    uhfStageInclusion (n + 1) (2 * z) = uhfStageInclusion n z := by
  have h := AddCommGroup.DirectLimit.of_f (G := fun _ : ℕ => ℤ) (f := uhfK0Bond)
    (i := n) (j := n + 1) (Nat.le_succ n) z
  simpa [uhfStageInclusion, uhfK0Bond] using h

theorem uhfDimensionGroup_halving (n : ℕ) :
    (2 : ℤ) • uhfStageInclusion (n + 1) 1 = uhfStageInclusion n 1 := by
  rw [← map_zsmul]
  simpa using uhfStageInclusion_succ n 1

/-- Embedding of the `n`-th stage `ℤ` into Mathlib's `Dyadic` rationals via `z ↦ z / 2^n`. -/
def uhfStageToDyadic (n : ℕ) : ℤ →+ Dyadic where
  toFun z := Dyadic.ofIntWithPrec z (n : ℤ)
  map_zero' := by
    rw [← Dyadic.toRat_inj, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Dyadic.toRat_zero]
    simp
  map_add' x y := by
    rw [← Dyadic.toRat_inj, Dyadic.toRat_add,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow,
      Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
    push_cast
    ring

theorem uhfStageToDyadic_compat (i j : ℕ) (h : i ≤ j) (z : ℤ) :
    uhfStageToDyadic j (uhfK0Bond i j h z) = uhfStageToDyadic i z := by
  rw [← Dyadic.toRat_inj]
  simp only [uhfStageToDyadic, uhfK0Bond, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  push_cast
  rw [mul_comm ((2 : ℚ) ^ (j - i)) (z : ℚ), mul_assoc,
    ← zpow_natCast (2 : ℚ) (j - i), ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 2
  omega

/-- Canonical homomorphism `UHFDimensionGroup →+ Dyadic` induced by the universal property. -/
def uhfToDyadic : UHFDimensionGroup →+ Dyadic :=
  AddCommGroup.DirectLimit.lift (fun _ : ℕ => ℤ) uhfK0Bond Dyadic
    uhfStageToDyadic uhfStageToDyadic_compat

theorem uhfStageToDyadic_injective (n : ℕ) : Function.Injective (uhfStageToDyadic n) := by
  intro x y hxy
  have hrat := congrArg Dyadic.toRat hxy
  simp only [uhfStageToDyadic, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow] at hrat
  have hpow : (2 : ℚ) ^ (-(n : ℤ)) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hq : (x : ℚ) = (y : ℚ) := mul_right_cancel₀ hpow hrat
  exact Int.cast_injective hq

theorem uhfToDyadic_bijective : Function.Bijective uhfToDyadic := by
  refine ⟨AddCommGroup.DirectLimit.lift_injective Dyadic uhfStageToDyadic
    uhfStageToDyadic_compat uhfStageToDyadic_injective, ?_⟩
  intro d
  cases d with
  | zero =>
      refine ⟨uhfStageInclusion 0 0, ?_⟩
      simp [uhfToDyadic, uhfStageInclusion]
  | ofOdd m k _ =>
      by_cases hk : k < 0
      · refine ⟨uhfStageInclusion 0 (m * (2 : ℤ) ^ (-k).toNat), ?_⟩
        rw [uhfStageInclusion, uhfToDyadic, AddCommGroup.DirectLimit.lift_of]
        rw [← Dyadic.toRat_inj]
        simp only [uhfStageToDyadic, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Dyadic.toRat_ofOdd_eq_mul_two_pow]
        push_cast
        rw [mul_one, ← zpow_natCast (2 : ℚ) (-k).toNat, show ((-k).toNat : ℤ) = -k by omega]
      · refine ⟨uhfStageInclusion k.toNat m, ?_⟩
        rw [uhfStageInclusion, uhfToDyadic, AddCommGroup.DirectLimit.lift_of]
        rw [← Dyadic.toRat_inj]
        simp only [uhfStageToDyadic, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Dyadic.toRat_ofOdd_eq_mul_two_pow]
        rw [show (k.toNat : ℤ) = k by omega]

/-- Additive equivalence between `UHFDimensionGroup` and Mathlib's `Dyadic` (`ℤ[1/2]`). -/
def uhfDimensionGroupEquivDyadic : UHFDimensionGroup ≃+ Dyadic :=
  AddEquiv.ofBijective uhfToDyadic uhfToDyadic_bijective

@[simp]
theorem uhfDimensionGroupEquivDyadic_stage (n : ℕ) (z : ℤ) :
    uhfDimensionGroupEquivDyadic (uhfStageInclusion n z) = Dyadic.ofIntWithPrec z (n : ℤ) :=
  AddCommGroup.DirectLimit.lift_of Dyadic uhfStageToDyadic uhfStageToDyadic_compat n z

theorem dyadicStageMap_compat (i j : ℕ) (h : i ≤ j) (z : ℤ) :
    dyadicStageMap j (uhfK0Bond i j h z) = dyadicStageMap i z := by
  induction h with
  | refl =>
      simp [uhfK0Bond]
  | @step m h_im ih =>
      have hbond : uhfK0Bond i (m + 1) (Nat.le_succ_of_le h_im) z =
          dyadicBond m (uhfK0Bond i m h_im z) := by
        simp only [uhfK0Bond, dyadicBond, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        rw [Nat.sub_add_comm h_im, pow_succ', mul_assoc]
      rw [hbond, dyadicStageMap_succ, ih]

/-- Canonical homomorphism `UHFDimensionGroup →+ DyadicRational`. -/
def uhfToDyadicRational : UHFDimensionGroup →+ DyadicRational :=
  AddCommGroup.DirectLimit.lift (fun _ : ℕ => ℤ) uhfK0Bond DyadicRational
    dyadicStageMap dyadicStageMap_compat

theorem dyadicStageMap_injective (n : ℕ) : Function.Injective (dyadicStageMap n) := by
  intro x y hxy
  have hq : ((dyadicStageMap n x : DyadicRational) : ℚ) =
      ((dyadicStageMap n y : DyadicRational) : ℚ) := congrArg Subtype.val hxy
  simp only [dyadicStageMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hq
  have hpow : (2 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  exact Int.cast_injective ((div_left_inj' hpow).mp hq)

theorem uhfToDyadicRational_bijective : Function.Bijective uhfToDyadicRational := by
  refine ⟨AddCommGroup.DirectLimit.lift_injective DyadicRational dyadicStageMap
    dyadicStageMap_compat dyadicStageMap_injective, ?_⟩
  intro q
  rcases q.property with ⟨z, n, hq⟩
  refine ⟨uhfStageInclusion n z, ?_⟩
  apply Subtype.ext
  rw [uhfStageInclusion, uhfToDyadicRational, AddCommGroup.DirectLimit.lift_of]
  exact hq.symm

/-- Additive equivalence `K₀(M_{2^∞}) ≃+ DyadicRational` (`ℤ[1/2] ⊂ ℚ`). -/
def uhfDimensionGroupEquivDyadicRational : UHFDimensionGroup ≃+ DyadicRational :=
  AddEquiv.ofBijective uhfToDyadicRational uhfToDyadicRational_bijective

@[simp]
theorem uhfDimensionGroupEquivDyadicRational_stage (n : ℕ) (z : ℤ) :
    uhfDimensionGroupEquivDyadicRational (uhfStageInclusion n z) = dyadicStageMap n z :=
  AddCommGroup.DirectLimit.lift_of DyadicRational dyadicStageMap dyadicStageMap_compat n z

/-- Additive equivalence between `AddCommGroup.DirectLimit` (`UHFDimensionGroup`) and
the repository's `DyadicDirectLimit`. -/
def uhfDimensionGroupEquivDyadicDirectLimit : UHFDimensionGroup ≃+ DyadicDirectLimit :=
  uhfDimensionGroupEquivDyadicRational.trans dyadicDirectLimitEquiv.symm

/-- Unlike `K₀(O₂)` where `[1] = 0`, the unit `[1]` in `K₀(M_{2^∞})` is strictly nonzero. -/
theorem uhfDimensionGroup_unit_ne_zero : uhfStageInclusion 0 1 ≠ 0 := by
  intro h0
  have hq := congrArg (fun x => ((uhfDimensionGroupEquivDyadicRational x : DyadicRational) : ℚ)) h0
  simp [dyadicStageMap] at hq

/-- Embed a coherent finite-stage projection readout from `RealUHFProjectionRankSystem`
into `UHFDimensionGroup`. -/
def realProjectionRankDimensionClass (S : RealUHFProjectionRankSystem) (n : ℕ) :
    UHFDimensionGroup :=
  uhfDimensionGroupEquivDyadicRational.symm (S.normalizedReadout n)

theorem realProjectionRankDimensionClass_add (S : RealUHFProjectionRankSystem) (n k : ℕ) :
    realProjectionRankDimensionClass S (n + k) = realProjectionRankDimensionClass S n := by
  unfold realProjectionRankDimensionClass
  rw [S.normalizedReadout_add]

end UHFDimensionGroup

end InfoGeometry.Canonical.CuntzK0AndUHFDimensionGroup
