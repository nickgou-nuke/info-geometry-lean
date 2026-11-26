/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornE6RootSystem
import InfoGeometry.Algebra.H3ZornStructureGroup

/-!
# Full Chevalley Generation and Bruhat Decomposition of `Str₀(H₃(𝕆_s)) = E₆(6)`

Proves constructively (without `sorry`, `admit`, custom axioms, or unsigned
`CFSGPort.Chevalley.xOp`) that the 72 signed root subgroups of `h3zornCubicStabilizer`
generate the entire reduced structure group `h3zornReducedStructureGroup` (`Str₀(H₃(𝕆_s))`):

1. **Part A (Cubic-Norm-1 Transitivity & `U(X)` membership)**: `e6ChevalleySubgroup` acts
   transitively on `{X : H3Zorn ℝ | normCubic X = 1}`, contains `h3zornULinearEquiv X`
   for `normCubic X = ±1`, and reduces any `g ∈ Str₀(H₃(𝕆_s))` to `h3zornReducedStructureFixOne`.
2. **Part B (`F₄(4) ⊆ E₆(6)` & Full Generation)**: using `f4PeirceExp`, idempotent swaps
   `w₁₂, w₂₃, w₃₁`, `D₄` Witt reduction, triality `A₂₃ = A₃₁ = ±id`, `G₂(2)` / `SL₃(ℝ)`
   reduction, and `e6TorusElt 2 (-1) * e6TorusElt 4 (-1)`, proves
   `h3zornReducedStructureFixOne ≤ e6ChevalleySubgroup` and **`e6ChevalleySubgroup = ⊤`**.
3. **Part C (Native Signed Borel / Weyl / Torus & Bruhat Decomposition)**: establishes
   faithfulness of the adjoint action, `T ⊓ U⁺ = ⊥`, `B ⊓ U⁻ = ⊥`, `U⁺ ⊓ U⁻ = ⊥`,
   `B = T * U⁺`, simple-root generation, Weyl root conjugation, the Rank-1 `SL₂` Bruhat
   identity, and full Bruhat cell decomposition `G = B W B`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit
open InfoGeometry.Exceptional.CFSGPort.Chevalley

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private local instance : One (ZornVectorMatrix ℝ) := ⟨ZornVectorMatrix.one⟩

section RootExponentials

private theorem sqZero_cubic_scalar_kill {a b c : ℝ}
    (h1 : a + b + c = 0) (hm1 : a - b + c = 0) (ha : a = 0) :
    b = 0 ∧ c = 0 := by
  have hsum : a + c = 0 := by linarith [h1, hm1]
  have hc : c = 0 := by linarith [hsum, ha]
  have hb : b = 0 := by linarith [h1, hc, ha]
  exact ⟨hb, hc⟩

/-- Endomorphism `1 + c • X` for `X ∈ h3zornCubicStabilizer`. -/
def e6RootExpEnd (X : h3zornCubicStabilizer) (c : ℝ) : Module.End ℝ (H3Zorn ℝ) :=
  (1 : Module.End ℝ (H3Zorn ℝ)) + c • (X.1 : Module.End ℝ (H3Zorn ℝ))

theorem e6RootExpEnd_apply (X : h3zornCubicStabilizer) (c : ℝ) (x : H3Zorn ℝ) :
    e6RootExpEnd X c x = x + c • X.1 x := by
  simp [e6RootExpEnd]

theorem e6RootExpEnd_zero (X : h3zornCubicStabilizer) :
    e6RootExpEnd X 0 = (1 : Module.End ℝ (H3Zorn ℝ)) := by
  simp [e6RootExpEnd]

theorem e6RootExpEnd_mul (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (a b : ℝ) :
    e6RootExpEnd X a * e6RootExpEnd X b = e6RootExpEnd X (a + b) := by
  dsimp [e6RootExpEnd]
  have hxx : (X.1 : Module.End ℝ (H3Zorn ℝ)) * (X.1 : Module.End ℝ (H3Zorn ℝ)) = 0 := by
    simpa [sq] using hsq
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    hxx, smul_zero, add_zero]
  rw [add_smul, add_assoc]

/-- Linear equivalence `1 + c • X` on `H3Zorn ℝ` for square-zero `X ∈ h3zornCubicStabilizer`. -/
def e6RootExpEquiv (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ :=
  LinearEquiv.ofLinearMap
    (e6RootExpEnd X c)
    (e6RootExpEnd X (-c))
    (by
      change e6RootExpEnd X c * e6RootExpEnd X (-c) = 1
      rw [e6RootExpEnd_mul X hsq, add_neg_cancel, e6RootExpEnd_zero])
    (by
      change e6RootExpEnd X (-c) * e6RootExpEnd X c = 1
      rw [e6RootExpEnd_mul X hsq, neg_add_cancel, e6RootExpEnd_zero])

@[simp] theorem e6RootExpEquiv_toLinearMap (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    (e6RootExpEquiv X hsq c).toLinearMap = e6RootExpEnd X c := rfl

@[simp] theorem e6RootExpEquiv_symm_toLinearMap (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    (e6RootExpEquiv X hsq c).symm.toLinearMap = e6RootExpEnd X (-c) := rfl

@[simp] theorem e6RootExpEquiv_apply (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) (x : H3Zorn ℝ) :
    e6RootExpEquiv X hsq c x = x + c • X.1 x :=
  e6RootExpEnd_apply X c x

private theorem normCubic_line_coeffs_zero_gen (n c : ℝ) :
    n + c * 0 + c ^ 2 * 0 + c ^ 3 * 0 = n := by ring

theorem e6RootExp_mem_reducedStructureGroup (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    e6RootExpEquiv X hsq c ∈ h3zornReducedStructureGroup := by
  intro x
  have htr : ∀ w : H3Zorn ℝ, traceBilin (adjointQuad w) (X.1 w) = 0 :=
    (mem_h3zornCubicStabilizer_iff_traceBilin_adjointQuad X.1).mp X.2
  let y : H3Zorn ℝ := X.1 x
  have hTy : X.1 y = 0 := by
    have h0 := LinearMap.ext_iff.mp hsq x
    simpa [sq, Module.End.mul_apply, y] using h0
  have hp : traceBilin (adjointQuad (x + y)) y = 0 := by
    have h := htr (x + y)
    rwa [map_add, show X.1 y = 0 from hTy, add_zero] at h
  have hm : traceBilin (adjointQuad (x - y)) y = 0 := by
    have h := htr (x - y)
    rwa [map_sub, show X.1 y = 0 from hTy, sub_zero] at h
  have hp_exp : traceBilin (adjointQuad x) y + traceBilin (crossProduct x y) y +
      traceBilin (adjointQuad y) y = 0 := by
    rwa [adjointQuad_add, traceBilin_add_left, traceBilin_add_left] at hp
  have hm_exp : traceBilin (adjointQuad x) y - traceBilin (crossProduct x y) y +
      traceBilin (adjointQuad y) y = 0 := by
    have hsub : adjointQuad (x - y) = adjointQuad x - crossProduct x y + adjointQuad y := by
      rw [sub_eq_add_neg, show -y = (-1 : ℝ) • y by module, adjointQuad_add,
        crossProduct_smul_right, adjointQuad_smul]
      module
    rwa [hsub, traceBilin_add_left, traceBilin_sub_left] at hm
  have hkill := sqZero_cubic_scalar_kill hp_exp hm_exp (htr x)
  have hnorm_y : normCubic y = 0 := by
    have h13 := mccrimmon_identity_13 y
    rw [hkill.2] at h13
    linarith
  have hcross_zero : traceBilin (adjointQuad y) x = 0 := by
    have hassoc := traceBilin_crossProduct_assoc x y y
    rw [hkill.1, crossProduct_self, traceBilin_smul_right] at hassoc
    rw [traceBilin_symm]
    linarith
  rw [e6RootExpEquiv_apply, normCubic_line, htr x, hcross_zero, hnorm_y]
  exact normCubic_line_coeffs_zero_gen (normCubic x) c

/-- Square-zero exponential inside `h3zornReducedStructureGroup`. -/
def e6SqZeroExp (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    h3zornReducedStructureGroup :=
  ⟨e6RootExpEquiv X hsq c, e6RootExp_mem_reducedStructureGroup X hsq c⟩

@[simp] theorem e6SqZeroExp_coe (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    ((e6SqZeroExp X hsq c).1 : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) = e6RootExpEquiv X hsq c := rfl

theorem e6SqZeroExp_zero (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) :
    e6SqZeroExp X hsq 0 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact e6RootExpEnd_zero X

theorem e6SqZeroExp_mul (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (a b : ℝ) :
    e6SqZeroExp X hsq a * e6SqZeroExp X hsq b = e6SqZeroExp X hsq (a + b) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact e6RootExpEnd_mul X hsq a b

/-- Root exponential `exp(c • e6RootVec r)` inside `h3zornReducedStructureGroup`. -/
def e6RootExp (r : Fin 72) (c : ℝ) : h3zornReducedStructureGroup :=
  e6SqZeroExp (e6RootVec r) (e6RootVec_sq_zero r) c

@[simp] theorem e6RootExp_coe_toLinearMap (r : Fin 72) (c : ℝ) :
    (e6RootExp r c).1.toLinearMap =
      (1 : Module.End ℝ (H3Zorn ℝ)) + c • (e6RootVec r).1 := rfl

@[simp] theorem e6RootExp_apply (r : Fin 72) (c : ℝ) (x : H3Zorn ℝ) :
    (e6RootExp r c).1 x = x + c • (e6RootVec r).1 x := rfl

theorem e6RootExp_zero (r : Fin 72) : e6RootExp r 0 = 1 :=
  e6SqZeroExp_zero (e6RootVec r) (e6RootVec_sq_zero r)

theorem e6RootExp_mul (r : Fin 72) (a b : ℝ) :
    e6RootExp r a * e6RootExp r b = e6RootExp r (a + b) :=
  e6SqZeroExp_mul (e6RootVec r) (e6RootVec_sq_zero r) a b

/-- Canonical generating set of all 72 root exponentials in `h3zornReducedStructureGroup`. -/
def e6RootExpSet : Set h3zornReducedStructureGroup :=
  Set.range fun p : Fin 72 × ℝ => e6RootExp p.1 p.2

/-- Native root-subgroup homomorphism `Multiplicative ℝ →* h3zornReducedStructureGroup`. -/
def e6RootSubgroupHom (r : Fin 72) :
    Multiplicative ℝ →* h3zornReducedStructureGroup where
  toFun x := e6RootExp r (Multiplicative.toAdd x)
  map_one' := e6RootExp_zero r
  map_mul' x y := by
    simp only [toAdd_mul]
    exact (e6RootExp_mul r _ _).symm

/-- Subgroup of `h3zornReducedStructureGroup` generated by the 72 signed root subgroups. -/
def e6ChevalleySubgroup : Subgroup h3zornReducedStructureGroup :=
  Subgroup.closure e6RootExpSet

theorem e6RootExp_mem_chevalley (r : Fin 72) (c : ℝ) :
    e6RootExp r c ∈ e6ChevalleySubgroup :=
  Subgroup.subset_closure ⟨(r, c), rfl⟩

theorem e6SimpleF_sq_zero_gen (i : Fin 6) :
    ((e6SimpleF i).1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0 := by
  have hsq := e6RootVec_sq_zero (fSimpleIdx i)
  rw [sq] at hsq
  change ((fSimpleSign i : ℝ) • (e6RootVec (fSimpleIdx i)).1) ^ 2 = 0
  rw [sq, smul_mul_assoc, mul_smul_comm, smul_smul, hsq, smul_zero]

/-- Simple positive root element `x_i(c)`. -/
def e6SimpleX (i : Fin 6) (c : ℝ) : h3zornReducedStructureGroup :=
  e6SqZeroExp (e6RootVec (eSimpleIdx i)) (e6RootVec_sq_zero (eSimpleIdx i)) c

/-- Simple negative root element `y_i(c)`. -/
def e6SimpleY (i : Fin 6) (c : ℝ) : h3zornReducedStructureGroup :=
  e6SqZeroExp (e6SimpleF i) (e6SimpleF_sq_zero_gen i) c

theorem e6SimpleX_eq_rootExp (i : Fin 6) (c : ℝ) :
    e6SimpleX i c = e6RootExp (eSimpleIdx i) c := rfl

theorem e6SimpleY_eq_rootExp (i : Fin 6) (c : ℝ) :
    e6SimpleY i c = e6RootExp (fSimpleIdx i) ((fSimpleSign i : ℝ) * c) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  change (1 : Module.End ℝ (H3Zorn ℝ)) + c • ((fSimpleSign i : ℝ) • (e6RootVec (fSimpleIdx i)).1) =
    (1 : Module.End ℝ (H3Zorn ℝ)) + ((fSimpleSign i : ℝ) * c) • (e6RootVec (fSimpleIdx i)).1
  rw [smul_smul, mul_comm]

theorem e6SimpleX_mem_chevalley (i : Fin 6) (c : ℝ) :
    e6SimpleX i c ∈ e6ChevalleySubgroup :=
  e6RootExp_mem_chevalley (eSimpleIdx i) c

theorem e6SimpleY_mem_chevalley (i : Fin 6) (c : ℝ) :
    e6SimpleY i c ∈ e6ChevalleySubgroup := by
  rw [e6SimpleY_eq_rootExp]
  exact e6RootExp_mem_chevalley (fSimpleIdx i) ((fSimpleSign i : ℝ) * c)

/-- Weyl element `w_i(t) = x_i(t) y_i(-t⁻¹) x_i(t)`. -/
def e6WeylElt (i : Fin 6) (t : ℝˣ) : h3zornReducedStructureGroup :=
  e6SimpleX i t * e6SimpleY i (-(t⁻¹ : ℝˣ)) * e6SimpleX i t

theorem e6WeylElt_mem_chevalley (i : Fin 6) (t : ℝˣ) :
    e6WeylElt i t ∈ e6ChevalleySubgroup :=
  Subgroup.mul_mem _
    (Subgroup.mul_mem _ (e6SimpleX_mem_chevalley i t) (e6SimpleY_mem_chevalley i _))
    (e6SimpleX_mem_chevalley i t)

/-- Torus element `h_i(t) = w_i(t) w_i(-1)`. -/
def e6TorusElt (i : Fin 6) (t : ℝˣ) : h3zornReducedStructureGroup :=
  e6WeylElt i t * e6WeylElt i (-1)

theorem e6TorusElt_mem_chevalley (i : Fin 6) (t : ℝˣ) :
    e6TorusElt i t ∈ e6ChevalleySubgroup :=
  Subgroup.mul_mem _ (e6WeylElt_mem_chevalley i t) (e6WeylElt_mem_chevalley i (-1))

end RootExponentials

section SparseWeylAndTorus

private theorem zpow_neg_mul_self_gen (t : ℝˣ) (a : ℤ) :
    ((t : ℝ) ^ (-a)) * ((t : ℝ) ^ a) = 1 := by
  have ht : (t : ℝ) ≠ 0 := t.ne_zero
  rw [← zpow_add₀ ht, neg_add_cancel, zpow_zero]

private theorem neg_inv_val_neg_one_gen : (-(((-1 : ℝˣ)⁻¹ : ℝˣ) : ℝ)) = 1 := by norm_num

private theorem minuscule_weight_dichotomy_gen (i : Fin 6) (k : Fin 27) :
    h3zornWeight k i = -1 ∨ h3zornWeight k i = 0 ∨ h3zornWeight k i = 1 := by
  have h : (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      decide (h3zornWeight k i = -1 ∨ h3zornWeight k i = 0 ∨ h3zornWeight k i = 1))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at h
  exact h i k

private theorem simpleE_kill_of_weight_nonneg_gen (i : Fin 6) (k : Fin 27)
    (hw : h3zornWeight k i = 0 ∨ h3zornWeight k i = 1) :
    (e6SimpleE i).1 (h3ZornBasis k) = 0 := by
  have hchk : (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      if h3zornWeight k i == 0 || h3zornWeight k i == 1 then
        (List.finRange 27).all (fun r => sparseVal (e6SimpleESparse i) r k == 0)
      else true)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hi := hchk i k
  have hcond : (h3zornWeight k i == 0 || h3zornWeight k i == 1) = true := by
    rcases hw with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [hcond] at hi
  simp only [ite_true, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hi
  have hrep : (e6SimpleE i).1 (h3ZornBasis k) =
      ∑ r : Fin 27, ((h3zornToMatrix (e6SimpleE i).1) r k) • h3ZornBasis r := by
    have hsum := h3ZornBasis.sum_repr ((e6SimpleE i).1 (h3ZornBasis k))
    rw [← hsum]
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1
    exact (h3zornToMatrix_apply (e6SimpleE i).1 r k).symm
  have hzero : ∀ r : Fin 27, (h3zornToMatrix (e6SimpleE i).1) r k = 0 := by
    intro r
    rw [h3zornToMatrix_e6SimpleE]
    change ((sparseVal (e6SimpleESparse i) r k : ℤ) : ℝ) = 0
    rw [hi r, Int.cast_zero]
  rw [hrep]
  exact Finset.sum_eq_zero fun r _ => by rw [hzero r, zero_smul]

private theorem simpleF_kill_of_weight_nonpos_gen (i : Fin 6) (k : Fin 27)
    (hw : h3zornWeight k i = 0 ∨ h3zornWeight k i = -1) :
    (e6SimpleF i).1 (h3ZornBasis k) = 0 := by
  have hchk : (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      if h3zornWeight k i == 0 || h3zornWeight k i == -1 then
        (List.finRange 27).all (fun r => sparseVal (e6SimpleFSparse i) r k == 0)
      else true)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hi := hchk i k
  have hcond : (h3zornWeight k i == 0 || h3zornWeight k i == -1) = true := by
    rcases hw with h0 | hm1
    · simp [h0]
    · simp [hm1]
  rw [hcond] at hi
  simp only [ite_true, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hi
  have hrep : (e6SimpleF i).1 (h3ZornBasis k) =
      ∑ r : Fin 27, ((h3zornToMatrix (e6SimpleF i).1) r k) • h3ZornBasis r := by
    have hsum := h3ZornBasis.sum_repr ((e6SimpleF i).1 (h3ZornBasis k))
    rw [← hsum]
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1
    exact (h3zornToMatrix_apply (e6SimpleF i).1 r k).symm
  have hzero : ∀ r : Fin 27, (h3zornToMatrix (e6SimpleF i).1) r k = 0 := by
    intro r
    rw [h3zornToMatrix_e6SimpleF]
    change ((sparseVal (e6SimpleFSparse i) r k : ℤ) : ℝ) = 0
    rw [hi r, Int.cast_zero]
  rw [hrep]
  exact Finset.sum_eq_zero fun r _ => by rw [hzero r, zero_smul]

private theorem e6SimpleE_sq_apply_gen (i : Fin 6) (v : H3Zorn ℝ) :
    (e6SimpleE i).1 ((e6SimpleE i).1 v) = 0 := by
  have h0 := LinearMap.ext_iff.mp (e6RootVec_sq_zero (eSimpleIdx i)) v
  change (e6RootVec (eSimpleIdx i)).1 ((e6RootVec (eSimpleIdx i)).1 v) = 0
  simpa [sq, Module.End.mul_apply] using h0

private theorem e6SimpleF_sq_apply_gen (i : Fin 6) (v : H3Zorn ℝ) :
    (e6SimpleF i).1 ((e6SimpleF i).1 v) = 0 := by
  have h0 := LinearMap.ext_iff.mp (e6SimpleF_sq_zero_gen i) v
  simpa [sq, Module.End.mul_apply] using h0

private theorem e6Simple_comm_apply_gen (i : Fin 6) (v : H3Zorn ℝ) :
    (e6SimpleE i).1 ((e6SimpleF i).1 v) - (e6SimpleF i).1 ((e6SimpleE i).1 v) =
      (e6SimpleH i).1 v :=
  congrArg (fun x : h3zornCubicStabilizer => x.1 v) (e6Simple_bracket_EF_same i)

private theorem weyl_on_highest_like_gen (i : Fin 6) (s : ℝ) (hs : s ≠ 0) (v : H3Zorn ℝ)
    (hE : (e6SimpleE i).1 v = 0)
    (hEF : (e6SimpleE i).1 ((e6SimpleF i).1 v) = v) :
    ((e6SimpleX i s).1 * (e6SimpleY i (-s⁻¹)).1 * (e6SimpleX i s).1) v =
      (-s⁻¹) • (e6SimpleF i).1 v := by
  change (e6SimpleX i s).1 ((e6SimpleY i (-s⁻¹)).1 ((e6SimpleX i s).1 v)) = _
  have hEE : (e6RootVec (eSimpleIdx i)).1 = (e6SimpleE i).1 := rfl
  have h1 : (e6SimpleX i s).1 v = v := by
    change v + s • (e6RootVec (eSimpleIdx i)).1 v = v
    rw [hEE, hE, smul_zero, add_zero]
  have h2 : (e6SimpleY i (-s⁻¹)).1 v = v + (-s⁻¹) • (e6SimpleF i).1 v := rfl
  have h3 : (e6SimpleX i s).1 (v + (-s⁻¹) • (e6SimpleF i).1 v) = (-s⁻¹) • (e6SimpleF i).1 v := by
    change v + (-s⁻¹) • (e6SimpleF i).1 v +
      s • (e6RootVec (eSimpleIdx i)).1 (v + (-s⁻¹) • (e6SimpleF i).1 v) = _
    rw [hEE, map_add, map_smul, hE, hEF, zero_add, smul_smul,
      show s * (-s⁻¹) = -1 by rw [mul_neg, mul_inv_cancel₀ hs], neg_one_smul]
    module
  rw [h1, h2, h3]

private theorem weyl_on_lowest_like_gen (i : Fin 6) (s : ℝ) (hs : s ≠ 0) (v : H3Zorn ℝ)
    (hF : (e6SimpleF i).1 v = 0)
    (hFE : (e6SimpleF i).1 ((e6SimpleE i).1 v) = v) :
    ((e6SimpleX i s).1 * (e6SimpleY i (-s⁻¹)).1 * (e6SimpleX i s).1) v =
      s • (e6SimpleE i).1 v := by
  change (e6SimpleX i s).1 ((e6SimpleY i (-s⁻¹)).1 ((e6SimpleX i s).1 v)) = _
  have hEE : (e6RootVec (eSimpleIdx i)).1 = (e6SimpleE i).1 := rfl
  have h1 : (e6SimpleX i s).1 v = v + s • (e6SimpleE i).1 v := rfl
  have h2 : (e6SimpleY i (-s⁻¹)).1 (v + s • (e6SimpleE i).1 v) = s • (e6SimpleE i).1 v := by
    change v + s • (e6SimpleE i).1 v + (-s⁻¹) • (e6SimpleF i).1 (v + s • (e6SimpleE i).1 v) = _
    rw [map_add, map_smul, hF, hFE, zero_add, smul_smul,
      show (-s⁻¹) * s = -1 by rw [neg_mul, inv_mul_cancel₀ hs], neg_one_smul]
    module
  have h3 : (e6SimpleX i s).1 (s • (e6SimpleE i).1 v) = s • (e6SimpleE i).1 v := by
    change s • (e6SimpleE i).1 v + s • (e6RootVec (eSimpleIdx i)).1 (s • (e6SimpleE i).1 v) = _
    rw [hEE, map_smul, e6SimpleE_sq_apply_gen, smul_zero, smul_zero, add_zero]
  rw [h1, h2, h3]

theorem e6TorusElt_apply_basis (i : Fin 6) (t : ℝˣ) (k : Fin 27) :
    (e6TorusElt i t).1 (h3ZornBasis k) = ((t ^ h3zornWeight k i : ℝˣ) : ℝ) • h3ZornBasis k := by
  change ((e6WeylElt i t).1 ((e6WeylElt i (-1)).1 (h3ZornBasis k))) = _
  have hw_unfold : ∀ (s : ℝˣ) (v : H3Zorn ℝ),
      (e6WeylElt i s).1 v =
        ((e6SimpleX i s).1 * (e6SimpleY i (-((s⁻¹ : ℝˣ) : ℝ))).1 *
          (e6SimpleX i s).1) v := fun _ _ => rfl
  rcases minuscule_weight_dichotomy_gen i k with hm1 | h0 | h1
  · have hF : (e6SimpleF i).1 (h3ZornBasis k) = 0 :=
      simpleF_kill_of_weight_nonpos_gen i k (Or.inr hm1)
    have hFE : (e6SimpleF i).1 ((e6SimpleE i).1 (h3ZornBasis k)) = h3ZornBasis k := by
      have hc := e6Simple_comm_apply_gen i (h3ZornBasis k)
      rw [hF, map_zero, zero_sub, e6SimpleH_apply_basis, hm1, Int.cast_neg, Int.cast_one] at hc
      change -((e6SimpleF i).1 ((e6SimpleE i).1 (h3ZornBasis k))) = (-1 : ℝ) • h3ZornBasis k at hc
      simpa using congrArg Neg.neg hc
    have h1_res : (e6WeylElt i (-1)).1 (h3ZornBasis k) = -(e6SimpleE i).1 (h3ZornBasis k) := by
      rw [hw_unfold]
      have hs : ((-1 : ℝˣ) : ℝ) ≠ 0 := by norm_num
      have hloc := weyl_on_lowest_like_gen i (-1) hs (h3ZornBasis k) hF hFE
      simpa [neg_inv_val_neg_one_gen] using hloc
    let u := (e6SimpleE i).1 (h3ZornBasis k)
    have hEu : (e6SimpleE i).1 u = 0 := e6SimpleE_sq_apply_gen i (h3ZornBasis k)
    have hEFu : (e6SimpleE i).1 ((e6SimpleF i).1 u) = u := by dsimp [u]; rw [hFE]
    have ht_res : (e6WeylElt i t).1 u = (-((t⁻¹ : ℝˣ) : ℝ)) • (h3ZornBasis k) := by
      rw [hw_unfold]
      have hloc := weyl_on_highest_like_gen i (t : ℝ) t.ne_zero u hEu hEFu
      rw [Units.val_inv_eq_inv_val]
      simpa [u, hFE] using hloc
    rw [h1_res, map_neg, ht_res, hm1, zpow_neg_one, Units.val_inv_eq_inv_val]
    module
  · have hE : (e6SimpleE i).1 (h3ZornBasis k) = 0 :=
      simpleE_kill_of_weight_nonneg_gen i k (Or.inl h0)
    have hF : (e6SimpleF i).1 (h3ZornBasis k) = 0 :=
      simpleF_kill_of_weight_nonpos_gen i k (Or.inl h0)
    have hfix : ∀ (s : ℝˣ), (e6WeylElt i s).1 (h3ZornBasis k) = h3ZornBasis k := by
      intro s
      rw [hw_unfold]
      change (e6SimpleX i s).1 ((e6SimpleY i (-((s⁻¹ : ℝˣ) : ℝ))).1
        ((e6SimpleX i s).1 (h3ZornBasis k))) = h3ZornBasis k
      simp only [e6SimpleX, e6SimpleY, e6SqZeroExp_coe, e6RootExpEquiv_apply]
      have hEE : (e6RootVec (eSimpleIdx i)).1 (h3ZornBasis k) = 0 := hE
      rw [hEE, smul_zero, add_zero, hF, smul_zero, add_zero, hEE, smul_zero, add_zero]
    rw [hfix (-1), hfix t, h0, zpow_zero, Units.val_one, one_smul]
  · have hE : (e6SimpleE i).1 (h3ZornBasis k) = 0 :=
      simpleE_kill_of_weight_nonneg_gen i k (Or.inr h1)
    have hEF : (e6SimpleE i).1 ((e6SimpleF i).1 (h3ZornBasis k)) = h3ZornBasis k := by
      have hc := e6Simple_comm_apply_gen i (h3ZornBasis k)
      rw [hE, map_zero, sub_zero, e6SimpleH_apply_basis, h1] at hc
      simpa using hc
    have h1_res : (e6WeylElt i (-1)).1 (h3ZornBasis k) = (e6SimpleF i).1 (h3ZornBasis k) := by
      rw [hw_unfold]
      have hs : ((-1 : ℝˣ) : ℝ) ≠ 0 := by norm_num
      have hloc := weyl_on_highest_like_gen i (-1) hs (h3ZornBasis k) hE hEF
      simpa [neg_inv_val_neg_one_gen] using hloc
    let u := (e6SimpleF i).1 (h3ZornBasis k)
    have hFu : (e6SimpleF i).1 u = 0 := e6SimpleF_sq_apply_gen i (h3ZornBasis k)
    have hFEu : (e6SimpleF i).1 ((e6SimpleE i).1 u) = u := by dsimp [u]; rw [hEF]
    have ht_res : (e6WeylElt i t).1 u = (t : ℝ) • h3ZornBasis k := by
      rw [hw_unfold]
      have hloc := weyl_on_lowest_like_gen i (t : ℝ) t.ne_zero u hFu hFEu
      simpa [u, hEF] using hloc
    rw [h1_res, ht_res, h1, zpow_one]

theorem e6TorusElt_symm_apply_basis (i : Fin 6) (t : ℝˣ) (k : Fin 27) :
    (e6TorusElt i t).1.symm (h3ZornBasis k) =
      ((t : ℝ) ^ (-h3zornWeight k i)) • h3ZornBasis k := by
  rw [LinearEquiv.symm_apply_eq, map_smul, e6TorusElt_apply_basis, smul_smul,
    Units.val_zpow_eq_zpow_val, zpow_neg_mul_self_gen, one_smul]

/-- Explicit non-commutativity witness for 27×27 integer root matrices. -/
theorem e6GroupGen_matrix27_int_noncomm_witness :
    ∃ A B : Matrix (Fin 27) (Fin 27) ℤ, A * B ≠ B * A :=
  ⟨sparseToMat (e6RootSparse 71), sparseToMat (e6RootSparse 56), by
    intro h
    have h00 := congrFun (congrFun h 0) 0
    have h1 : sparseVal (sparseMul (e6RootSparse 71) (e6RootSparse 56)) 0 0 = 1 := by decide
    have h2 : sparseVal (sparseMul (e6RootSparse 56) (e6RootSparse 71)) 0 0 = 0 := by decide
    change (∑ k : Fin 27, sparseVal (e6RootSparse 71) 0 k * sparseVal (e6RootSparse 56) k 0) =
      (∑ k : Fin 27, sparseVal (e6RootSparse 56) 0 k * sparseVal (e6RootSparse 71) k 0) at h00
    rw [← sparseVal_mul, ← sparseVal_mul, h1, h2] at h00
    omega⟩

end SparseWeylAndTorus

section CoordinateReadout

/-- The 8 standard coordinates of a `ZornVectorMatrix ℝ` matching `zorn_basis`. -/
def zornCoord (u : ZornVectorMatrix ℝ) (i : Fin 8) : ℝ :=
  match i.val with
  | 0 => u.a
  | 1 => u.v 0
  | 2 => u.v 1
  | 3 => u.v 2
  | 4 => u.w 0
  | 5 => u.w 1
  | 6 => u.w 2
  | _ => u.b

theorem zorn_eq_of_zornCoord_eq {u v : ZornVectorMatrix ℝ}
    (h : ∀ i : Fin 8, zornCoord u i = zornCoord v i) : u = v := by
  apply ZornVectorMatrix.ext
  · exact h 0
  · funext k; fin_cases k
    · exact h 1
    · exact h 2
    · exact h 3
  · funext k; fin_cases k
    · exact h 4
    · exact h 5
    · exact h 6
  · exact h 7

theorem zornCoord_eq_zero_iff (u : ZornVectorMatrix ℝ) :
    (∀ i : Fin 8, zornCoord u i = 0) ↔ u = 0 := by
  constructor
  · intro h
    exact zorn_eq_of_zornCoord_eq fun i => (h i).trans (by fin_cases i <;> rfl)
  · rintro rfl i
    fin_cases i <;> rfl

theorem zornCoord_add (u v : ZornVectorMatrix ℝ) (i : Fin 8) :
    zornCoord (u + v) i = zornCoord u i + zornCoord v i := by
  fin_cases i <;> rfl

theorem zornCoord_smul (c : ℝ) (u : ZornVectorMatrix ℝ) (i : Fin 8) :
    zornCoord (c • u) i = c * zornCoord u i := by
  fin_cases i <;> rfl

theorem zornBilin_eq_sum_zornCoord (u : ZornVectorMatrix ℝ) (i : Fin 8) :
    zornBilin u (zorn_basis i) =
      ∑ j : Fin 8, (zornBilinInt i j : ℝ) * zornCoord u j := by
  rw [Fin.sum_univ_eight]
  fin_cases i <;>
    simp [zornBilin, zornBilinInt, zornCoord, zorn_basis, ZornVectorMatrix.trace,
      ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVec3.dot]

theorem h3ZornCoord_zero_eq (X : H3Zorn ℝ) : h3ZornCoordinate X 0 = X.α₁ := rfl
theorem h3ZornCoord_one_eq (X : H3Zorn ℝ) : h3ZornCoordinate X 1 = X.α₂ := rfl
theorem h3ZornCoord_two_eq (X : H3Zorn ℝ) : h3ZornCoordinate X 2 = X.α₃ := rfl

theorem h3ZornCoord_a_eq (X : H3Zorn ℝ) (j : Fin 8) :
    h3ZornCoordinate X ⟨3 + j.val, by omega⟩ = zornCoord X.a j := by
  fin_cases j <;> rfl

theorem h3ZornCoord_b_eq (X : H3Zorn ℝ) (j : Fin 8) :
    h3ZornCoordinate X ⟨11 + j.val, by omega⟩ = zornCoord X.b j := by
  fin_cases j <;> rfl

theorem h3ZornCoord_c_eq (X : H3Zorn ℝ) (j : Fin 8) :
    h3ZornCoordinate X ⟨19 + j.val, by omega⟩ = zornCoord X.c j := by
  fin_cases j <;> rfl

theorem h3Zorn_ext_coord {X Y : H3Zorn ℝ}
    (h : ∀ m : Fin 27, h3ZornCoordinate X m = h3ZornCoordinate Y m) : X = Y := by
  apply h3ZornCoordEquiv.injective
  ext m
  exact h m

theorem h3ZornCoordinate_e6RootVec (r : Fin 72) (X : H3Zorn ℝ) (m : Fin 27) :
    h3ZornCoordinate ((e6RootVec r).1 X) m =
      ∑ k : Fin 27, (sparseVal (e6RootSparse r) m k : ℝ) * h3ZornCoordinate X k := by
  have hrep : X = ∑ k : Fin 27, h3ZornCoordinate X k • h3ZornBasis k :=
    (h3ZornBasis.sum_repr X).symm
  conv_lhs => rw [hrep, map_sum]
  change h3ZornCoordinateLM (∑ k : Fin 27, (e6RootVec r).1 (h3ZornCoordinate X k • h3ZornBasis k)) m = _
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  change h3ZornCoordinate (h3ZornCoordinate X k • (e6RootVec r).1 (h3ZornBasis k)) m = _
  rw [h3ZornCoordinate_smul, mul_comm]
  congr 1
  have hm : h3ZornCoordinate ((e6RootVec r).1 (h3ZornBasis k)) m =
      h3zornToMatrix (e6RootVec r : Module.End ℝ (H3Zorn ℝ)) m k :=
    (h3zornToMatrix_apply (e6RootVec r).1 m k).symm
  rw [hm, h3zornToMatrix_e6RootVec r, Matrix.map_apply, sparseToMat]

theorem h3ZornCoordinate_e6RootExp (r : Fin 72) (t : ℝ) (X : H3Zorn ℝ) (m : Fin 27) :
    h3ZornCoordinate ((e6RootExp r t).1 X) m =
      h3ZornCoordinate X m +
        t * ∑ k : Fin 27, (sparseVal (e6RootSparse r) m k : ℝ) * h3ZornCoordinate X k := by
  rw [e6RootExp_apply, h3ZornCoordinate_add, h3ZornCoordinate_smul, h3ZornCoordinate_e6RootVec]

private theorem sum_fin27_eq_sum_fin8_of_support (g : Fin 27 → ℝ) (base : ℕ) (hb : base + 8 ≤ 27)
    (hg : ∀ k : Fin 27, ¬(base ≤ k.val ∧ k.val < base + 8) → g k = 0) :
    (∑ k : Fin 27, g k) =
      ∑ j : Fin 8, g ⟨base + j.val, lt_of_lt_of_le (Nat.add_lt_add_left j.isLt base) hb⟩ := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun k : Fin 27 => base ≤ k.val ∧ k.val < base + 8)]
  have hz : ∑ k ∈ Finset.univ.filter (fun k : Fin 27 => ¬(base ≤ k.val ∧ k.val < base + 8)), g k = 0 :=
    Finset.sum_eq_zero fun k hk => hg k (Finset.mem_filter.mp hk).2
  rw [hz, add_zero]
  refine (Finset.sum_bij (fun j _ => (⟨base + j.val, by omega⟩ : Fin 27)) ?_ ?_ ?_ ?_).symm
  · intro j _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Nat.le_add_right _ _, by omega⟩
  · intro j₁ _ j₂ _ h
    have hval := congrArg Fin.val h
    exact Fin.ext (by dsimp at hval; omega)
  · intro k hk
    have hkp := (Finset.mem_filter.mp hk).2
    refine ⟨⟨k.val - base, by omega⟩, Finset.mem_univ _, ?_⟩
    ext; dsimp; omega
  · intro _ _; rfl

private theorem sum_fin27_eq_three_of_support (g : Fin 27 → ℝ)
    (hg : ∀ k : Fin 27, ¬(k.val < 3) → g k = 0) :
    (∑ k : Fin 27, g k) = g 0 + g 1 + g 2 := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun k : Fin 27 => k.val < 3)]
  have hz : ∑ k ∈ Finset.univ.filter (fun k : Fin 27 => ¬(k.val < 3)), g k = 0 :=
    Finset.sum_eq_zero fun k hk => hg k (Finset.mem_filter.mp hk).2
  rw [hz, add_zero]
  have hflt : Finset.univ.filter (fun k : Fin 27 => k.val < 3) = {0, 1, 2} := by decide
  rw [hflt, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private def slot0Pos (i : Fin 8) : Fin 72 := ⟨24 + 2 * i.val, by omega⟩
private def slot0Neg (i : Fin 8) : Fin 72 := ⟨25 + 2 * i.val, by omega⟩
private def slot1Pos (i : Fin 8) : Fin 72 := ⟨40 + 2 * i.val, by omega⟩
private def slot1Neg (i : Fin 8) : Fin 72 := ⟨41 + 2 * i.val, by omega⟩
private def slot2Pos (i : Fin 8) : Fin 72 := ⟨56 + 2 * i.val, by omega⟩
private def slot2Neg (i : Fin 8) : Fin 72 := ⟨57 + 2 * i.val, by omega⟩

private theorem slot0Pos_row0 (i : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot0Pos i)) 0 k =
      if h : 3 ≤ k.val ∧ k.val < 11 then zornBilinInt i ⟨k.val - 3, by omega⟩ else 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot0Pos i)) 0 k ==
        if h : 3 ≤ k.val ∧ k.val < 11 then zornBilinInt i ⟨k.val - 3, by omega⟩ else 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i k

private theorem slot0Pos_row1 (i : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot0Pos i)) 1 k = 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot0Pos i)) 1 k == 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i k

private theorem slot0Pos_row2 (i : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot0Pos i)) 2 k = 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot0Pos i)) 2 k == 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i k

private theorem slot0Pos_rowA (i j : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot0Pos i)) ⟨3 + j.val, by omega⟩ k =
      if i = j ∧ k.val = 1 then 1 else 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      (List.finRange 27).all (fun k =>
        sparseVal (e6RootSparse (slot0Pos i)) ⟨3 + j.val, by omega⟩ k ==
          if i = j ∧ k.val = 1 then 1 else 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i j k

private theorem slot0Pos_rowB (i j : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot0Pos i)) ⟨11 + j.val, by omega⟩ k = 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      (List.finRange 27).all (fun k =>
        sparseVal (e6RootSparse (slot0Pos i)) ⟨11 + j.val, by omega⟩ k == 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i j k

private theorem slot0Neg_row0 (i : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot0Neg i)) 0 k = 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot0Neg i)) 0 k == 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i k

private theorem slot0Neg_rowA (i j : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot0Neg i)) ⟨3 + j.val, by omega⟩ k =
      if i = j ∧ k.val = 0 then 1 else 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      (List.finRange 27).all (fun k =>
        sparseVal (e6RootSparse (slot0Neg i)) ⟨3 + j.val, by omega⟩ k ==
          if i = j ∧ k.val = 0 then 1 else 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i j k

private theorem slot0Neg_rowC (i j : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot0Neg i)) ⟨19 + j.val, by omega⟩ k = 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      (List.finRange 27).all (fun k =>
        sparseVal (e6RootSparse (slot0Neg i)) ⟨19 + j.val, by omega⟩ k == 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i j k

private theorem slot1Pos_row0 (i : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot1Pos i)) 0 k = 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot1Pos i)) 0 k == 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i k

private theorem slot1Pos_row1 (i : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot1Pos i)) 1 k =
      if h : 11 ≤ k.val ∧ k.val < 19 then zornBilinInt i ⟨k.val - 11, by omega⟩ else 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot1Pos i)) 1 k ==
        if h : 11 ≤ k.val ∧ k.val < 19 then zornBilinInt i ⟨k.val - 11, by omega⟩ else 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i k

private theorem slot1Pos_rowA_cols_check :
    (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      (List.finRange 27).all (fun k =>
        if k.val < 19 then sparseVal (e6RootSparse (slot1Pos i)) ⟨3 + j.val, by omega⟩ k == 0
        else true))) = true := by
  decide

private theorem slot1Pos_rowA_cols (i j : Fin 8) (k : Fin 27) (hk : k.val < 19) :
    sparseVal (e6RootSparse (slot1Pos i)) ⟨3 + j.val, by omega⟩ k = 0 := by
  have hc := slot1Pos_rowA_cols_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc
  have hij := hc i j k
  simp [hk] at hij
  exact hij

private theorem slot1Pos_rowC (i j : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot1Pos i)) ⟨19 + j.val, by omega⟩ k = 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      (List.finRange 27).all (fun k =>
        sparseVal (e6RootSparse (slot1Pos i)) ⟨19 + j.val, by omega⟩ k == 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i j k

private theorem slot1Neg_row0 (i : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot1Neg i)) 0 k = 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot1Neg i)) 0 k == 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i k

private theorem slot1Neg_row1 (i : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot1Neg i)) 1 k = 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot1Neg i)) 1 k == 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i k

private theorem slot1Neg_rowA (i j : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot1Neg i)) ⟨3 + j.val, by omega⟩ k = 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      (List.finRange 27).all (fun k =>
        sparseVal (e6RootSparse (slot1Neg i)) ⟨3 + j.val, by omega⟩ k == 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i j k

private theorem slot1Neg_rowB (i j : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot1Neg i)) ⟨11 + j.val, by omega⟩ k =
      if i = j ∧ k.val = 1 then 1 else 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      (List.finRange 27).all (fun k =>
        sparseVal (e6RootSparse (slot1Neg i)) ⟨11 + j.val, by omega⟩ k ==
          if i = j ∧ k.val = 1 then 1 else 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i j k

private theorem slot1Neg_rowC_cols_check :
    (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      (List.finRange 27).all (fun k =>
        if !(3 ≤ k.val && k.val < 11) then
          sparseVal (e6RootSparse (slot1Neg i)) ⟨19 + j.val, by omega⟩ k == 0
        else true))) = true := by
  decide

private theorem slot1Neg_rowC_cols (i j : Fin 8) (k : Fin 27) (hk : ¬(3 ≤ k.val ∧ k.val < 11)) :
    sparseVal (e6RootSparse (slot1Neg i)) ⟨19 + j.val, by omega⟩ k = 0 := by
  have hc := slot1Neg_rowC_cols_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc
  have hij := hc i j k
  have hcond : (!(3 ≤ k.val && k.val < 11)) = true := by
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases h3 : 3 ≤ k.val
    · right; intro h11; exact hk ⟨h3, h11⟩
    · left; exact h3
  simp only [hcond, ↓reduceIte, beq_iff_eq] at hij
  exact hij

private theorem slot2Pos_row0 (i : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot2Pos i)) 0 k = 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot2Pos i)) 0 k == 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i k

private theorem slot2Pos_rowA (i j : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot2Pos i)) ⟨3 + j.val, by omega⟩ k = 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      (List.finRange 27).all (fun k =>
        sparseVal (e6RootSparse (slot2Pos i)) ⟨3 + j.val, by omega⟩ k == 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i j k

private theorem slot2Pos_rowC (i j : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot2Pos i)) ⟨19 + j.val, by omega⟩ k =
      if i = j ∧ k.val = 0 then 1 else 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      (List.finRange 27).all (fun k =>
        sparseVal (e6RootSparse (slot2Pos i)) ⟨19 + j.val, by omega⟩ k ==
          if i = j ∧ k.val = 0 then 1 else 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i j k

private theorem slot2Neg_row0 (i : Fin 8) (k : Fin 27) :
    sparseVal (e6RootSparse (slot2Neg i)) 0 k =
      if h : 19 ≤ k.val ∧ k.val < 27 then zornBilinInt i ⟨k.val - 19, by omega⟩ else 0 := by
  have hc : (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot2Neg i)) 0 k ==
        if h : 19 ≤ k.val ∧ k.val < 27 then zornBilinInt i ⟨k.val - 19, by omega⟩ else 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  exact hc i k

/-- Torus scaling on diagonal `diagCartan α₁ α₂ α₃`. -/
theorem e6TorusElt_apply_diag (i : Fin 6) (t : ℝˣ) (α₁ α₂ α₃ : ℝ) :
    (e6TorusElt i t).1 (diagCartan α₁ α₂ α₃) =
      diagCartan
        (((t ^ h3zornWeight 0 i : ℝˣ) : ℝ) * α₁)
        (((t ^ h3zornWeight 1 i : ℝˣ) : ℝ) * α₂)
        (((t ^ h3zornWeight 2 i : ℝˣ) : ℝ) * α₃) := by
  have hdec : diagCartan α₁ α₂ α₃ = α₁ • h3ZornBasis 0 + α₂ • h3ZornBasis 1 + α₃ • h3ZornBasis 2 := by
    rw [h3ZornBasis_zero, h3ZornBasis_one, h3ZornBasis_two]
    apply ext_h3 <;> simp [diagCartan, h3_diag₁, h3_diag₂, h3_diag₃, add_readback, smul_readback,
      ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]
  have hdiag : ∀ β₁ β₂ β₃ : ℝ,
      diagCartan β₁ β₂ β₃ = β₁ • h3ZornBasis 0 + β₂ • h3ZornBasis 1 + β₃ • h3ZornBasis 2 := by
    intro β₁ β₂ β₃
    rw [h3ZornBasis_zero, h3ZornBasis_one, h3ZornBasis_two]
    apply ext_h3 <;> simp [diagCartan, h3_diag₁, h3_diag₂, h3_diag₃, add_readback, smul_readback,
      ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]
  rw [hdec, map_add, map_add, map_smul, map_smul, map_smul,
    e6TorusElt_apply_basis, e6TorusElt_apply_basis, e6TorusElt_apply_basis,
    smul_smul, smul_smul, smul_smul, mul_comm α₁, mul_comm α₂, mul_comm α₃, ← hdiag]

end CoordinateReadout

section PartATransitivity

private theorem slot0Pos_alpha1 (i : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot0Pos i) t).1 X).α₁ = X.α₁ + t * zornBilin X.a (zorn_basis i) := by
  change h3ZornCoordinate ((e6RootExp (slot0Pos i) t).1 X) 0 = _
  rw [h3ZornCoordinate_e6RootExp, h3ZornCoord_zero_eq]
  have hsum : (∑ k : Fin 27, (sparseVal (e6RootSparse (slot0Pos i)) 0 k : ℝ) *
      h3ZornCoordinate X k) = zornBilin X.a (zorn_basis i) := by
    rw [sum_fin27_eq_sum_fin8_of_support _ 3 (by omega) (fun k hk => by
      rw [slot0Pos_row0]; split_ifs with hk'
      · exact False.elim (hk hk')
      · simp)]
    rw [zornBilin_eq_sum_zornCoord]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [slot0Pos_row0]; split_ifs with hj'
    · rw [h3ZornCoord_a_eq]
      have hidx : (⟨(⟨3 + j.val, lt_of_lt_of_le (Nat.add_lt_add_left j.isLt 3) (by omega)⟩ : Fin 27).val - 3,
          by dsimp; omega⟩ : Fin 8) = j := Fin.ext (by dsimp; omega)
      rw [hidx]
    · exact False.elim (hj' ⟨Nat.le_add_right 3 j.val, by dsimp; omega⟩)
  rw [hsum]

private theorem slot2Neg_alpha1 (i : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot2Neg i) t).1 X).α₁ = X.α₁ + t * zornBilin X.c (zorn_basis i) := by
  change h3ZornCoordinate ((e6RootExp (slot2Neg i) t).1 X) 0 = _
  rw [h3ZornCoordinate_e6RootExp, h3ZornCoord_zero_eq]
  have hsum : (∑ k : Fin 27, (sparseVal (e6RootSparse (slot2Neg i)) 0 k : ℝ) *
      h3ZornCoordinate X k) = zornBilin X.c (zorn_basis i) := by
    rw [sum_fin27_eq_sum_fin8_of_support _ 19 (by omega) (fun k hk => by
      rw [slot2Neg_row0]; split_ifs with hk'
      · exact False.elim (hk hk')
      · simp)]
    rw [zornBilin_eq_sum_zornCoord]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [slot2Neg_row0]; split_ifs with hj'
    · rw [h3ZornCoord_c_eq]
      have hidx : (⟨(⟨19 + j.val, lt_of_lt_of_le (Nat.add_lt_add_left j.isLt 19) (by omega)⟩ : Fin 27).val - 19,
          by dsimp; omega⟩ : Fin 8) = j := Fin.ext (by dsimp; omega)
      rw [hidx]
    · exact False.elim (hj' ⟨Nat.le_add_right 19 j.val, by dsimp; omega⟩)
  rw [hsum]

private theorem slot0Neg_alpha1 (i : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot0Neg i) t).1 X).α₁ = X.α₁ := by
  change h3ZornCoordinate ((e6RootExp (slot0Neg i) t).1 X) 0 = X.α₁
  rw [h3ZornCoordinate_e6RootExp, h3ZornCoord_zero_eq]
  simp [slot0Neg_row0]

private theorem slot0Neg_a (i j : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    zornCoord ((e6RootExp (slot0Neg i) t).1 X).a j =
      zornCoord X.a j + (if i = j then t * X.α₁ else 0) := by
  rw [← h3ZornCoord_a_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_a_eq]
  have hsum : (∑ k : Fin 27, (sparseVal (e6RootSparse (slot0Neg i)) ⟨3 + j.val, by omega⟩ k : ℝ) *
      h3ZornCoordinate X k) = if i = j then X.α₁ else 0 := by
    rw [Finset.sum_eq_single 0]
    · simp [slot0Neg_rowA, h3ZornCoord_zero_eq]
    · intro k _ hk0
      have hk : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
      simp [slot0Neg_rowA, hk]
    · intro h0; exact absurd (Finset.mem_univ 0) h0
  rw [hsum]
  split_ifs <;> ring

private theorem slot2Pos_alpha1 (i : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot2Pos i) t).1 X).α₁ = X.α₁ := by
  change h3ZornCoordinate ((e6RootExp (slot2Pos i) t).1 X) 0 = X.α₁
  rw [h3ZornCoordinate_e6RootExp, h3ZornCoord_zero_eq]
  simp [slot2Pos_row0]

private theorem slot2Pos_a (i : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot2Pos i) t).1 X).a = X.a := by
  apply zorn_eq_of_zornCoord_eq
  intro j
  rw [← h3ZornCoord_a_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_a_eq]
  simp [slot2Pos_rowA]

private theorem slot2Pos_c (i j : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    zornCoord ((e6RootExp (slot2Pos i) t).1 X).c j =
      zornCoord X.c j + (if i = j then t * X.α₁ else 0) := by
  rw [← h3ZornCoord_c_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_c_eq]
  have hsum : (∑ k : Fin 27, (sparseVal (e6RootSparse (slot2Pos i)) ⟨19 + j.val, by omega⟩ k : ℝ) *
      h3ZornCoordinate X k) = if i = j then X.α₁ else 0 := by
    rw [Finset.sum_eq_single 0]
    · simp [slot2Pos_rowC, h3ZornCoord_zero_eq]
    · intro k _ hk0
      have hk : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
      simp [slot2Pos_rowC, hk]
    · intro h0; exact absurd (Finset.mem_univ 0) h0
  rw [hsum]
  split_ifs <;> ring

private theorem slot1Pos_alpha1 (i : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot1Pos i) t).1 X).α₁ = X.α₁ := by
  change h3ZornCoordinate ((e6RootExp (slot1Pos i) t).1 X) 0 = X.α₁
  rw [h3ZornCoordinate_e6RootExp, h3ZornCoord_zero_eq]
  simp [slot1Pos_row0]

private theorem slot1Pos_alpha2 (i : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot1Pos i) t).1 X).α₂ = X.α₂ + t * zornBilin X.b (zorn_basis i) := by
  change h3ZornCoordinate ((e6RootExp (slot1Pos i) t).1 X) 1 = _
  rw [h3ZornCoordinate_e6RootExp, h3ZornCoord_one_eq]
  have hsum : (∑ k : Fin 27, (sparseVal (e6RootSparse (slot1Pos i)) 1 k : ℝ) *
      h3ZornCoordinate X k) = zornBilin X.b (zorn_basis i) := by
    rw [sum_fin27_eq_sum_fin8_of_support _ 11 (by omega) (fun k hk => by
      rw [slot1Pos_row1]; split_ifs with hk'
      · exact False.elim (hk hk')
      · simp)]
    rw [zornBilin_eq_sum_zornCoord]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [slot1Pos_row1]; split_ifs with hj'
    · rw [h3ZornCoord_b_eq]
      have hidx : (⟨(⟨11 + j.val, lt_of_lt_of_le (Nat.add_lt_add_left j.isLt 11) (by omega)⟩ : Fin 27).val - 11,
          by dsimp; omega⟩ : Fin 8) = j := Fin.ext (by dsimp; omega)
      rw [hidx]
    · exact False.elim (hj' ⟨Nat.le_add_right 11 j.val, by dsimp; omega⟩)
  rw [hsum]

private theorem slot1Pos_a_of_c_zero (i : Fin 8) (t : ℝ) {X : H3Zorn ℝ} (hc : X.c = 0) :
    ((e6RootExp (slot1Pos i) t).1 X).a = X.a := by
  apply zorn_eq_of_zornCoord_eq
  intro j
  rw [← h3ZornCoord_a_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_a_eq]
  have hsum : (∑ k : Fin 27, (sparseVal (e6RootSparse (slot1Pos i)) ⟨3 + j.val, by omega⟩ k : ℝ) *
      h3ZornCoordinate X k) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k.val < 19
    · rw [slot1Pos_rowA_cols i j k hk, Int.cast_zero, zero_mul]
    · have hk_eq : k = ⟨19 + (⟨k.val - 19, by omega⟩ : Fin 8).val, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      have hcz : h3ZornCoordinate X k = 0 := by
        rw [hk_eq, h3ZornCoord_c_eq, hc]
        exact (zornCoord_eq_zero_iff 0).mpr rfl ⟨k.val - 19, by omega⟩
      rw [hcz, mul_zero]
  rw [hsum, mul_zero, add_zero]

private theorem slot1Pos_c (i : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot1Pos i) t).1 X).c = X.c := by
  apply zorn_eq_of_zornCoord_eq
  intro j
  rw [← h3ZornCoord_c_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_c_eq]
  simp [slot1Pos_rowC]

private theorem slot1Neg_alpha1 (i : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot1Neg i) t).1 X).α₁ = X.α₁ := by
  change h3ZornCoordinate ((e6RootExp (slot1Neg i) t).1 X) 0 = X.α₁
  rw [h3ZornCoordinate_e6RootExp, h3ZornCoord_zero_eq]
  simp [slot1Neg_row0]

private theorem slot1Neg_alpha2 (i : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot1Neg i) t).1 X).α₂ = X.α₂ := by
  change h3ZornCoordinate ((e6RootExp (slot1Neg i) t).1 X) 1 = X.α₂
  rw [h3ZornCoordinate_e6RootExp, h3ZornCoord_one_eq]
  simp [slot1Neg_row1]

private theorem slot1Neg_a (i : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot1Neg i) t).1 X).a = X.a := by
  apply zorn_eq_of_zornCoord_eq
  intro j
  rw [← h3ZornCoord_a_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_a_eq]
  simp [slot1Neg_rowA]

private theorem slot1Neg_b (i j : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    zornCoord ((e6RootExp (slot1Neg i) t).1 X).b j =
      zornCoord X.b j + (if i = j then t * X.α₂ else 0) := by
  rw [← h3ZornCoord_b_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_b_eq]
  have hsum : (∑ k : Fin 27, (sparseVal (e6RootSparse (slot1Neg i)) ⟨11 + j.val, by omega⟩ k : ℝ) *
      h3ZornCoordinate X k) = if i = j then X.α₂ else 0 := by
    rw [Finset.sum_eq_single 1]
    · simp [slot1Neg_rowB, h3ZornCoord_one_eq]
    · intro k _ hk1
      have hk : k.val ≠ 1 := fun h => hk1 (Fin.ext h)
      simp [slot1Neg_rowB, hk]
    · intro h1; exact absurd (Finset.mem_univ 1) h1
  rw [hsum]
  split_ifs <;> ring

private theorem slot1Neg_c_of_a_zero (i : Fin 8) (t : ℝ) {X : H3Zorn ℝ} (ha : X.a = 0) :
    ((e6RootExp (slot1Neg i) t).1 X).c = X.c := by
  apply zorn_eq_of_zornCoord_eq
  intro j
  rw [← h3ZornCoord_c_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_c_eq]
  have hsum : (∑ k : Fin 27, (sparseVal (e6RootSparse (slot1Neg i)) ⟨19 + j.val, by omega⟩ k : ℝ) *
      h3ZornCoordinate X k) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : 3 ≤ k.val ∧ k.val < 11
    · have hk_eq : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      have haz : h3ZornCoordinate X k = 0 := by
        rw [hk_eq, h3ZornCoord_a_eq, ha]
        exact (zornCoord_eq_zero_iff 0).mpr rfl ⟨k.val - 3, by omega⟩
      rw [haz, mul_zero]
    · rw [slot1Neg_rowC_cols i j k hk, Int.cast_zero, zero_mul]
  rw [hsum, mul_zero, add_zero]

private theorem normCubic_eq_diag_of_zero {X : H3Zorn ℝ}
    (ha : X.a = 0) (hb : X.b = 0) (hc : X.c = 0) :
    normCubic X = X.α₁ * X.α₂ * X.α₃ := by
  simp [normCubic, ha, hb, hc, ZornVectorMatrix.norm_zero, ZornVectorMatrix.mul_zero,
    ZornVectorMatrix.trace_zero]

private theorem eq_diagCartan_of_abc_zero {X : H3Zorn ℝ}
    (ha : X.a = 0) (hb : X.b = 0) (hc : X.c = 0) :
    X = diagCartan X.α₁ X.α₂ X.α₃ := by
  apply ext_h3 <;> simp [diagCartan, ha, hb, hc]

private theorem clear_a_prefix :
    ∀ n : ℕ, n ≤ 8 → ∀ X : H3Zorn ℝ, X.α₁ ≠ 0 →
      ∃ h ∈ e6ChevalleySubgroup,
        (h.1 X).α₁ = X.α₁ ∧ ∀ j : Fin 8, j.val < n → zornCoord (h.1 X).a j = 0 := by
  intro n
  induction n with
  | zero =>
    intro _ X _
    exact ⟨1, e6ChevalleySubgroup.one_mem, rfl, fun j hj => by omega⟩
  | succ n ih =>
    intro hn X hα
    obtain ⟨h₀, hh₀, hα₀, hj₀⟩ := ih (by omega) X hα
    let X₀ := h₀.1 X
    let i : Fin 8 := ⟨n, by omega⟩
    let g := e6RootExp (slot0Neg i) (-zornCoord X₀.a i / X.α₁)
    refine ⟨g * h₀, e6ChevalleySubgroup.mul_mem (e6RootExp_mem_chevalley _ _) hh₀, ?_, ?_⟩
    · change (g.1 X₀).α₁ = X.α₁
      rw [slot0Neg_alpha1, hα₀]
    · intro j hj
      change zornCoord (g.1 X₀).a j = 0
      rw [slot0Neg_a, hα₀]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        field_simp [hα]
        ring
      · simp only [hij, ↓reduceIte, add_zero]
        have hjlt : j.val < n := by
          have hne : n ≠ j.val := fun heq => hij (Fin.ext heq)
          omega
        exact hj₀ j hjlt

private theorem clear_c_prefix :
    ∀ n : ℕ, n ≤ 8 → ∀ X : H3Zorn ℝ, X.α₁ ≠ 0 → X.a = 0 →
      ∃ h ∈ e6ChevalleySubgroup,
        (h.1 X).α₁ = X.α₁ ∧ (h.1 X).a = 0 ∧
          ∀ j : Fin 8, j.val < n → zornCoord (h.1 X).c j = 0 := by
  intro n
  induction n with
  | zero =>
    intro _ X _ ha
    exact ⟨1, e6ChevalleySubgroup.one_mem, rfl, ha, fun j hj => by omega⟩
  | succ n ih =>
    intro hn X hα ha
    obtain ⟨h₀, hh₀, hα₀, ha₀, hj₀⟩ := ih (by omega) X hα ha
    let X₀ := h₀.1 X
    let i : Fin 8 := ⟨n, by omega⟩
    let g := e6RootExp (slot2Pos i) (-zornCoord X₀.c i / X.α₁)
    refine ⟨g * h₀, e6ChevalleySubgroup.mul_mem (e6RootExp_mem_chevalley _ _) hh₀, ?_, ?_, ?_⟩
    · change (g.1 X₀).α₁ = X.α₁
      rw [slot2Pos_alpha1, hα₀]
    · change (g.1 X₀).a = 0
      rw [slot2Pos_a, ha₀]
    · intro j hj
      change zornCoord (g.1 X₀).c j = 0
      rw [slot2Pos_c, hα₀]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        field_simp [hα]
        ring
      · simp only [hij, ↓reduceIte, add_zero]
        have hjlt : j.val < n := by
          have hne : n ≠ j.val := fun heq => hij (Fin.ext heq)
          omega
        exact hj₀ j hjlt

private theorem clear_b_prefix :
    ∀ n : ℕ, n ≤ 8 → ∀ X : H3Zorn ℝ, X.α₂ ≠ 0 → X.a = 0 → X.c = 0 →
      ∃ h ∈ e6ChevalleySubgroup,
        (h.1 X).α₁ = X.α₁ ∧ (h.1 X).α₂ = X.α₂ ∧ (h.1 X).a = 0 ∧ (h.1 X).c = 0 ∧
          ∀ j : Fin 8, j.val < n → zornCoord (h.1 X).b j = 0 := by
  intro n
  induction n with
  | zero =>
    intro _ X _ ha hc
    exact ⟨1, e6ChevalleySubgroup.one_mem, rfl, rfl, ha, hc, fun j hj => by omega⟩
  | succ n ih =>
    intro hn X hα₂ ha hc
    obtain ⟨h₀, hh₀, hα₁₀, hα₂₀, ha₀, hc₀, hj₀⟩ := ih (by omega) X hα₂ ha hc
    let X₀ := h₀.1 X
    let i : Fin 8 := ⟨n, by omega⟩
    let g := e6RootExp (slot1Neg i) (-zornCoord X₀.b i / X.α₂)
    refine ⟨g * h₀, e6ChevalleySubgroup.mul_mem (e6RootExp_mem_chevalley _ _) hh₀, ?_, ?_, ?_, ?_, ?_⟩
    · change (g.1 X₀).α₁ = X.α₁; rw [slot1Neg_alpha1, hα₁₀]
    · change (g.1 X₀).α₂ = X.α₂; rw [slot1Neg_alpha2, hα₂₀]
    · change (g.1 X₀).a = 0; rw [slot1Neg_a, ha₀]
    · change (g.1 X₀).c = 0; rw [slot1Neg_c_of_a_zero i _ ha₀, hc₀]
    · intro j hj
      change zornCoord (g.1 X₀).b j = 0
      rw [slot1Neg_b, hα₂₀]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        field_simp [hα₂]
        ring
      · simp only [hij, ↓reduceIte, add_zero]
        have hjlt : j.val < n := by
          have hne : n ≠ j.val := fun heq => hij (Fin.ext heq)
          omega
        exact hj₀ j hjlt

/-- Any cubic-norm-1 element of `H3Zorn ℝ` can be moved to `1` by `e6ChevalleySubgroup`. -/
theorem e6ChevalleySubgroup_move_normCubic_one_to_one (X : H3Zorn ℝ) (hN : normCubic X = 1) :
    ∃ h ∈ e6ChevalleySubgroup, h.1 X = 1 := by
  -- Step 1: Make α₁ ≠ 0
  have hStep1 : ∃ h₁ ∈ e6ChevalleySubgroup, (h₁.1 X).α₁ ≠ 0 := by
    by_cases hα₁ : X.α₁ ≠ 0
    · exact ⟨1, e6ChevalleySubgroup.one_mem, hα₁⟩
    · have hα₁0 : X.α₁ = 0 := not_not.mp hα₁
      by_cases ha : X.a ≠ 0
      · have hex : ∃ i : Fin 8, zornBilin X.a (zorn_basis i) ≠ 0 := by
          by_contra hall
          push Not at hall
          exact ha (eq_zero_of_zornBilin_basis X.a hall)
        obtain ⟨i, hi⟩ := hex
        refine ⟨e6RootExp (slot0Pos i) 1, e6RootExp_mem_chevalley _ _, ?_⟩
        rw [slot0Pos_alpha1, hα₁0, zero_add, one_mul]
        exact hi
      · have ha0 : X.a = 0 := not_not.mp ha
        have hc : X.c ≠ 0 := by
          intro hc0
          have hn0 : normCubic X = 0 := by
            simp [normCubic, hα₁0, ha0, hc0, ZornVectorMatrix.norm_zero,
              ZornVectorMatrix.mul_zero, ZornVectorMatrix.trace_zero]
          linarith [hN, hn0]
        have hex : ∃ i : Fin 8, zornBilin X.c (zorn_basis i) ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hc (eq_zero_of_zornBilin_basis X.c hall)
        obtain ⟨i, hi⟩ := hex
        refine ⟨e6RootExp (slot2Neg i) 1, e6RootExp_mem_chevalley _ _, ?_⟩
        rw [slot2Neg_alpha1, hα₁0, zero_add, one_mul]
        exact hi
  obtain ⟨h₁, hh₁, hα₁⟩ := hStep1
  obtain ⟨X₁, hX₁⟩ : ∃ X₁, h₁.1 X = X₁ := ⟨_, rfl⟩
  rw [hX₁] at hα₁
  -- Step 2: Clear a = 0 preserving α₁ ≠ 0
  obtain ⟨h₂, hh₂, hα₁₂, ha₂⟩ := clear_a_prefix 8 (le_refl 8) X₁ hα₁
  have ha₂' : (h₂.1 X₁).a = 0 := (zornCoord_eq_zero_iff _).mp fun j => ha₂ j j.isLt
  -- Step 3: Clear c = 0 preserving α₁ ≠ 0 and a = 0
  obtain ⟨h₃, hh₃, hα₁₃, ha₃, hc₃⟩ := clear_c_prefix 8 (le_refl 8) (h₂.1 X₁) (by rw [hα₁₂]; exact hα₁) ha₂'
  have hc₃' : (h₃.1 (h₂.1 X₁)).c = 0 := (zornCoord_eq_zero_iff _).mp fun j => hc₃ j j.isLt
  obtain ⟨X₃, hX₃⟩ : ∃ X₃, h₃.1 (h₂.1 X₁) = X₃ := ⟨_, rfl⟩
  rw [hX₃] at hα₁₃ ha₃ hc₃'
  have hX₃_eq : (h₃ * h₂ * h₁).1 X = X₃ := by
    change h₃.1 (h₂.1 (h₁.1 X)) = X₃; rw [hX₁, hX₃]
  have hX₃N : normCubic X₃ = 1 := by rw [← hX₃_eq, (h₃ * h₂ * h₁).2 X, hN]
  have hα₁₃' : X₃.α₁ ≠ 0 := by rw [hα₁₃, hα₁₂]; exact hα₁
  -- Step 4: Make α₂ ≠ 0 preserving α₁ ≠ 0, a = 0, c = 0
  have hStep4 : ∃ h₄ ∈ e6ChevalleySubgroup,
      (h₄.1 X₃).α₁ = X₃.α₁ ∧ (h₄.1 X₃).α₂ ≠ 0 ∧ (h₄.1 X₃).a = 0 ∧ (h₄.1 X₃).c = 0 := by
    by_cases hα₂ : X₃.α₂ ≠ 0
    · exact ⟨1, e6ChevalleySubgroup.one_mem, rfl, hα₂, ha₃, hc₃'⟩
    · have hα₂0 : X₃.α₂ = 0 := not_not.mp hα₂
      have hb : X₃.b ≠ 0 := by
        intro hb0
        have hn0 : normCubic X₃ = 0 := by
          rw [normCubic_eq_diag_of_zero ha₃ hb0 hc₃', hα₂0, mul_zero, zero_mul]
        linarith [hX₃N, hn0]
      have hex : ∃ i : Fin 8, zornBilin X₃.b (zorn_basis i) ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hb (eq_zero_of_zornBilin_basis X₃.b hall)
      obtain ⟨i, hi⟩ := hex
      refine ⟨e6RootExp (slot1Pos i) 1, e6RootExp_mem_chevalley _ _, ?_, ?_, ?_, ?_⟩
      · exact slot1Pos_alpha1 i 1 X₃
      · rw [slot1Pos_alpha2, hα₂0, zero_add, one_mul]
        exact hi
      · rw [slot1Pos_a_of_c_zero i 1 hc₃', ha₃]
      · exact (slot1Pos_c i 1 X₃).trans hc₃'
  obtain ⟨h₄, hh₄, hα₁₄, hα₂₄, ha₄, hc₄⟩ := hStep4
  obtain ⟨X₄, hX₄⟩ : ∃ X₄, h₄.1 X₃ = X₄ := ⟨_, rfl⟩
  rw [hX₄] at hα₁₄ hα₂₄ ha₄ hc₄
  -- Step 5: Clear b = 0
  obtain ⟨h₅, hh₅, hα₁₅, hα₂₅, ha₅, hc₅, hb₅⟩ :=
    clear_b_prefix 8 (le_refl 8) X₄ hα₂₄ ha₄ hc₄
  have hb₅' : (h₅.1 X₄).b = 0 := (zornCoord_eq_zero_iff _).mp fun j => hb₅ j j.isLt
  obtain ⟨X₅, hX₅⟩ : ∃ X₅, h₅.1 X₄ = X₅ := ⟨_, rfl⟩
  rw [hX₅] at hα₁₅ hα₂₅ ha₅ hc₅ hb₅'
  have hX₅_eq : (h₅ * h₄ * h₃ * h₂ * h₁).1 X = X₅ := by
    change h₅.1 (h₄.1 (h₃.1 (h₂.1 (h₁.1 X)))) = X₅; rw [hX₁, hX₃, hX₄, hX₅]
  have hX₅_diag : X₅ = diagCartan X₅.α₁ X₅.α₂ X₅.α₃ :=
    eq_diagCartan_of_abc_zero ha₅ hb₅' hc₅
  have hα₁₅' : X₅.α₁ ≠ 0 := by rw [hα₁₅, hα₁₄]; exact hα₁₃'
  have hα₂₅' : X₅.α₂ ≠ 0 := by rw [hα₂₅]; exact hα₂₄
  have hX₅N : X₅.α₁ * X₅.α₂ * X₅.α₃ = 1 := by
    rw [← normCubic_eq_diag_of_zero ha₅ hb₅' hc₅, ← hX₅_eq, (h₅ * h₄ * h₃ * h₂ * h₁).2 X, hN]
  -- Step 6: Scale diagCartan X₅.α₁ X₅.α₂ X₅.α₃ to 1 via torus elements 0 and 2
  let u₁ : ℝˣ := Units.mk0 X₅.α₁ hα₁₅'
  let u₂ : ℝˣ := Units.mk0 X₅.α₂ hα₂₅'
  let t := (e6TorusElt 0 u₂⁻¹ * e6TorusElt 2 u₂⁻¹) * e6TorusElt 0 u₁⁻¹
  have ht_mem : t ∈ e6ChevalleySubgroup :=
    e6ChevalleySubgroup.mul_mem
      (e6ChevalleySubgroup.mul_mem (e6TorusElt_mem_chevalley 0 _) (e6TorusElt_mem_chevalley 2 _))
      (e6TorusElt_mem_chevalley 0 _)
  have ht_apply : t.1 X₅ = 1 := by
    have hmul : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Y : H3Zorn ℝ),
        (g₁ * g₂).1 Y = g₁.1 (g₂.1 Y) := fun _ _ _ => rfl
    rw [hX₅_diag]
    dsimp only [t]
    rw [hmul, hmul, e6TorusElt_apply_diag, e6TorusElt_apply_diag, e6TorusElt_apply_diag]
    have hw00 : h3zornWeight 0 0 = 1 := rfl
    have hw10 : h3zornWeight 1 0 = 0 := rfl
    have hw20 : h3zornWeight 2 0 = -1 := rfl
    have hw02 : h3zornWeight 0 2 = -1 := rfl
    have hw12 : h3zornWeight 1 2 = 1 := rfl
    have hw22 : h3zornWeight 2 2 = 0 := rfl
    rw [hw00, hw10, hw20, hw02, hw12, hw22]
    simp only [zpow_one, zpow_zero, zpow_neg_one, inv_inv, Units.val_one, Units.val_inv_eq_inv_val]
    have hu₁ : (u₁ : ℝ) = X₅.α₁ := rfl
    have hu₂ : (u₂ : ℝ) = X₅.α₂ := rfl
    rw [hu₁, hu₂]
    simp only [one_mul, mul_one, inv_mul_cancel₀ hα₁₅', inv_mul_cancel₀ hα₂₅']
    have hprod3 : X₅.α₂ * (X₅.α₁ * X₅.α₃) = 1 := by
      have : X₅.α₂ * (X₅.α₁ * X₅.α₃) = X₅.α₁ * X₅.α₂ * X₅.α₃ := by ring
      rw [this, hX₅N]
    rw [hprod3]
    rfl
  have hmul : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Y : H3Zorn ℝ),
      (g₁ * g₂).1 Y = g₁.1 (g₂.1 Y) := fun _ _ _ => rfl
  refine ⟨t * (h₅ * h₄ * h₃ * h₂ * h₁), ?_, ?_⟩
  · exact e6ChevalleySubgroup.mul_mem ht_mem
      (e6ChevalleySubgroup.mul_mem
        (e6ChevalleySubgroup.mul_mem
          (e6ChevalleySubgroup.mul_mem (e6ChevalleySubgroup.mul_mem hh₅ hh₄) hh₃) hh₂) hh₁)
  · rw [hmul, hX₅_eq, ht_apply]

/-- **Part A (Cubic-Norm-1 Transitivity)**: `e6ChevalleySubgroup` acts transitively on
`{X : H3Zorn ℝ | normCubic X = 1}`. -/
theorem e6ChevalleySubgroup_transitive_normCubic_one (X : H3Zorn ℝ) (hN : normCubic X = 1) :
    ∃ h ∈ e6ChevalleySubgroup, h.1 1 = X := by
  obtain ⟨g, hg, hgX⟩ := e6ChevalleySubgroup_move_normCubic_one_to_one X hN
  refine ⟨g⁻¹, e6ChevalleySubgroup.inv_mem hg, ?_⟩
  change g.1.symm 1 = X
  rw [← hgX, g.1.symm_apply_apply]

/-- Every element of `Str₀(H₃(𝕆_s))` can be multiplied on the left by `e6ChevalleySubgroup`
into the unit stabilizer `h3zornReducedStructureFixOne`. -/
theorem e6ChevalleySubgroup_reduce_to_fixOne (g : h3zornReducedStructureGroup) :
    ∃ h ∈ e6ChevalleySubgroup, (h * g).1 1 = 1 := by
  have hN : normCubic (g.1 1) = 1 := by simpa [normCubic_one] using g.2 1
  obtain ⟨h, hh, h1⟩ := e6ChevalleySubgroup_move_normCubic_one_to_one (g.1 1) hN
  exact ⟨h, hh, h1⟩

end PartATransitivity

section PartBF4AndFullGeneration

/-- Subgroup of `e6ChevalleySubgroup` fixing the Jordan unit `1`. -/
def e6F4InChevalley : Subgroup h3zornReducedStructureGroup :=
  e6ChevalleySubgroup ⊓ h3zornReducedStructureFixOne

theorem e6F4InChevalley_mem_iff (g : h3zornReducedStructureGroup) :
    g ∈ e6F4InChevalley ↔ g ∈ e6ChevalleySubgroup ∧ g.1 1 = 1 :=
  Iff.rfl

/-- Rank-1 primitive idempotent predicate in `H3Zorn ℝ`. -/
def isRankOneIdem (e : H3Zorn ℝ) : Prop :=
  e * e = e ∧ linearTrace e = 1 ∧ adjointQuad e = 0

theorem h3_diag₁_isRankOneIdem : isRankOneIdem h3_diag₁ := by
  refine ⟨h3_diag₁_mul_h3_diag₁, ?_, ?_⟩
  · change (1 : ℝ) + 0 + 0 = 1; norm_num
  · apply ext_h3 <;>
      simp [adjointQuad, h3_diag₁, ZornVectorMatrix.norm_zero,
        ZornVectorMatrix.conj_zero, ZornVectorMatrix.mul_zero,
        ZornVectorMatrix.smul_zero]

private theorem jordanAut_adjointQuad (A : H3ZornJordanAut) (X : H3Zorn ℝ) :
    A (adjointQuad X) = adjointQuad (A X) := by
  have htr : ∀ x y z : H3Zorn ℝ,
      h3zornNormTrilin (A.toLinearEquiv x) (A.toLinearEquiv y) (A.toLinearEquiv z) =
        h3zornNormTrilin x y z :=
    h3zornNormTrilin_preserved_of_normCubic_preserved A.toLinearEquiv.toLinearMap
      (H3ZornJordanAut.mem_reducedStructureGroup A)
  have hcp := h3zorn_crossProduct_eq_of_cubic_and_unit A.toLinearEquiv htr A.map_one X X
  rw [crossProduct_self, crossProduct_self, map_smul] at hcp
  have h2 : (2 : ℝ) • A (adjointQuad X) = (2 : ℝ) • adjointQuad (A X) := hcp
  exact smul_right_injective _ (two_ne_zero : (2 : ℝ) ≠ 0) h2

theorem jordanAut_preserves_isRankOneIdem (A : H3ZornJordanAut) {e : H3Zorn ℝ}
    (he : isRankOneIdem e) : isRankOneIdem (A e) := by
  have htr : ∀ x y z : H3Zorn ℝ,
      h3zornNormTrilin (A.toLinearEquiv x) (A.toLinearEquiv y) (A.toLinearEquiv z) =
        h3zornNormTrilin x y z :=
    h3zornNormTrilin_preserved_of_normCubic_preserved A.toLinearEquiv.toLinearMap
      (H3ZornJordanAut.mem_reducedStructureGroup A)
  refine ⟨?_, ?_, ?_⟩
  · rw [← A.map_mul, he.1]
  · change linearTrace (A.toLinearEquiv.toLinearMap e) = 1
    rw [h3zorn_trace_eq_of_cubic_and_unit A.toLinearEquiv.toLinearMap htr A.map_one, he.2.1]
  · rw [← jordanAut_adjointQuad, he.2.2]
    exact A.toLinearEquiv.map_zero

private theorem h3ZornCoordinate_e6RootExp_mul (r₁ r₂ : Fin 72) (t₁ t₂ : ℝ)
    (X : H3Zorn ℝ) (m : Fin 27) :
    h3ZornCoordinate (((e6RootExp r₁ t₁ * e6RootExp r₂ t₂).1) X) m =
      h3ZornCoordinate X m +
        t₁ * (∑ k : Fin 27, (sparseVal (e6RootSparse r₁) m k : ℝ) * h3ZornCoordinate X k) +
        t₂ * (∑ k : Fin 27, (sparseVal (e6RootSparse r₂) m k : ℝ) * h3ZornCoordinate X k) +
        (t₁ * t₂) * (∑ k : Fin 27,
          (sparseVal (sparseMul (e6RootSparse r₁) (e6RootSparse r₂)) m k : ℝ) *
            h3ZornCoordinate X k) := by
  change h3ZornCoordinate ((e6RootExp r₁ t₁).1 ((e6RootExp r₂ t₂).1 X)) m = _
  rw [h3ZornCoordinate_e6RootExp]
  have hr2 : ∀ k : Fin 27,
      h3ZornCoordinate ((e6RootExp r₂ t₂).1 X) k =
        h3ZornCoordinate X k +
          t₂ * ∑ l : Fin 27, (sparseVal (e6RootSparse r₂) k l : ℝ) * h3ZornCoordinate X l :=
    fun k => h3ZornCoordinate_e6RootExp r₂ t₂ X k
  have hmul : ∑ k : Fin 27, (sparseVal (e6RootSparse r₁) m k : ℝ) *
      (∑ l : Fin 27, (sparseVal (e6RootSparse r₂) k l : ℝ) * h3ZornCoordinate X l) =
      ∑ l : Fin 27, (sparseVal (sparseMul (e6RootSparse r₁) (e6RootSparse r₂)) m l : ℝ) *
        h3ZornCoordinate X l := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [sparseVal_mul, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Int.cast_mul]
    ring
  simp_rw [hr2, mul_add, Finset.sum_add_distrib]
  have hm2 : (∑ k : Fin 27, (sparseVal (e6RootSparse r₁) m k : ℝ) *
      (t₂ * ∑ l : Fin 27, (sparseVal (e6RootSparse r₂) k l : ℝ) * h3ZornCoordinate X l)) =
      t₂ * ∑ k : Fin 27, (sparseVal (e6RootSparse r₁) m k : ℝ) *
        (∑ l : Fin 27, (sparseVal (e6RootSparse r₂) k l : ℝ) * h3ZornCoordinate X l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hm2, hmul]
  ring

private theorem h3ZornCoordinate_one (m : Fin 27) :
    h3ZornCoordinate (1 : H3Zorn ℝ) m = if m.val < 3 then 1 else 0 := by
  fin_cases m <;> rfl

/-- The `D₄ = so(4,4)` subgroup generated by `r < 24`. -/
def d4Subgroup : Subgroup h3zornReducedStructureGroup :=
  Subgroup.closure
    (Set.range fun p : {r : Fin 72 // r.val < 24} × ℝ => e6RootExp p.1.1 p.2)

private theorem d4_sparse_block_diag_check :
    (List.finRange 72).all (fun r =>
      if r.val < 24 then (List.finRange 27).all (fun m => (List.finRange 27).all (fun k =>
        (!decide (m.val < 3) || sparseVal (e6RootSparse r) m k == 0) &&
        (!decide (k.val < 3) || sparseVal (e6RootSparse r) m k == 0) &&
        (!(decide (3 ≤ m.val ∧ m.val < 11) && !decide (3 ≤ k.val ∧ k.val < 11)) ||
          sparseVal (e6RootSparse r) m k == 0) &&
        (!(decide (11 ≤ m.val ∧ m.val < 19) && !decide (11 ≤ k.val ∧ k.val < 19)) ||
          sparseVal (e6RootSparse r) m k == 0) &&
        (!(decide (19 ≤ m.val) && !decide (19 ≤ k.val)) ||
          sparseVal (e6RootSparse r) m k == 0)))
      else true) = true := by
  decide

private theorem d4_sparse_block_diag (r : Fin 72) (hr : r.val < 24) (m k : Fin 27) :
    (m.val < 3 → sparseVal (e6RootSparse r) m k = 0) ∧
    (k.val < 3 → sparseVal (e6RootSparse r) m k = 0) ∧
    (3 ≤ m.val ∧ m.val < 11 → ¬(3 ≤ k.val ∧ k.val < 11) → sparseVal (e6RootSparse r) m k = 0) ∧
    (11 ≤ m.val ∧ m.val < 19 → ¬(11 ≤ k.val ∧ k.val < 19) → sparseVal (e6RootSparse r) m k = 0) ∧
    (19 ≤ m.val → ¬(19 ≤ k.val) → sparseVal (e6RootSparse r) m k = 0) := by
  have hc := d4_sparse_block_diag_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc
  have hr' := hc r
  simp only [hr, ↓reduceIte, List.all_eq_true, List.mem_finRange, true_implies] at hr'
  have hmk := hr' m k
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    beq_iff_eq] at hmk
  rcases hmk with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  refine ⟨fun hm => h1.resolve_left (by simp [hm]),
    fun hk => h2.resolve_left (by simp [hk]),
    fun hm hk => h3.resolve_left (by simp [hm, hk]),
    fun hm hk => h4.resolve_left (by simp [hm, hk]),
    fun hm hk => h5.resolve_left (by simp [hm, hk])⟩

theorem d4Subgroup_mem_chevalley {g : h3zornReducedStructureGroup} (hg : g ∈ d4Subgroup) :
    g ∈ e6ChevalleySubgroup := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨⟨r, _⟩, c⟩, rfl⟩
    exact e6RootExp_mem_chevalley r c
  | one => exact e6ChevalleySubgroup.one_mem
  | mul _ _ _ _ ha hb => exact e6ChevalleySubgroup.mul_mem ha hb
  | inv _ _ ha => exact e6ChevalleySubgroup.inv_mem ha

theorem d4Subgroup_preserves_blocks {g : h3zornReducedStructureGroup} (hg : g ∈ d4Subgroup) :
    ∀ X : H3Zorn ℝ,
      (g.1 X).α₁ = X.α₁ ∧ (g.1 X).α₂ = X.α₂ ∧ (g.1 X).α₃ = X.α₃ ∧
      (X.a = 0 → (g.1 X).a = 0) ∧ (X.b = 0 → (g.1 X).b = 0) ∧ (X.c = 0 → (g.1 X).c = 0) := by
  have hgen : ∀ (r : Fin 72) (_hr : r.val < 24) (t : ℝ) (X : H3Zorn ℝ),
      ((e6RootExp r t).1 X).α₁ = X.α₁ ∧ ((e6RootExp r t).1 X).α₂ = X.α₂ ∧
      ((e6RootExp r t).1 X).α₃ = X.α₃ ∧
      (X.a = 0 → ((e6RootExp r t).1 X).a = 0) ∧
      (X.b = 0 → ((e6RootExp r t).1 X).b = 0) ∧
      (X.c = 0 → ((e6RootExp r t).1 X).c = 0) := by
    intro r hr t X
    have hdiag : ∀ (m : Fin 27) (hm : m.val < 3),
        h3ZornCoordinate ((e6RootExp r t).1 X) m = h3ZornCoordinate X m := by
      intro m hm
      rw [h3ZornCoordinate_e6RootExp]
      have hz : ∑ k : Fin 27, (sparseVal (e6RootSparse r) m k : ℝ) * h3ZornCoordinate X k = 0 :=
        Finset.sum_eq_zero fun k _ => by
          rw [(d4_sparse_block_diag r hr m k).1 hm, Int.cast_zero, zero_mul]
      rw [hz, mul_zero, add_zero]
    refine ⟨hdiag 0 (by decide), hdiag 1 (by decide), hdiag 2 (by decide), ?_, ?_, ?_⟩
    · intro ha
      apply zorn_eq_of_zornCoord_eq
      intro j
      rw [← h3ZornCoord_a_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_a_eq, ha]
      have ha0 : zornCoord (0 : ZornVectorMatrix ℝ) j = 0 := by fin_cases j <;> rfl
      have hsum : ∑ k : Fin 27, (sparseVal (e6RootSparse r) ⟨3 + j.val, by omega⟩ k : ℝ) *
          h3ZornCoordinate X k = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : 3 ≤ k.val ∧ k.val < 11
        · have hkq : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          have hck : h3ZornCoordinate X k = 0 := by
            rw [hkq, h3ZornCoord_a_eq, ha]
            exact (zornCoord_eq_zero_iff 0).mpr rfl ⟨k.val - 3, by omega⟩
          rw [hck, mul_zero]
        · rw [(d4_sparse_block_diag r hr ⟨3 + j.val, by omega⟩ k).2.2.1 (by dsimp; omega) hk,
            Int.cast_zero, zero_mul]
      rw [ha0, hsum, mul_zero, add_zero]
    · intro hb
      apply zorn_eq_of_zornCoord_eq
      intro j
      rw [← h3ZornCoord_b_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_b_eq, hb]
      have hb0 : zornCoord (0 : ZornVectorMatrix ℝ) j = 0 := by fin_cases j <;> rfl
      have hsum : ∑ k : Fin 27, (sparseVal (e6RootSparse r) ⟨11 + j.val, by omega⟩ k : ℝ) *
          h3ZornCoordinate X k = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : 11 ≤ k.val ∧ k.val < 19
        · have hkq : k = ⟨11 + (⟨k.val - 11, by omega⟩ : Fin 8).val, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          have hck : h3ZornCoordinate X k = 0 := by
            rw [hkq, h3ZornCoord_b_eq, hb]
            exact (zornCoord_eq_zero_iff 0).mpr rfl ⟨k.val - 11, by omega⟩
          rw [hck, mul_zero]
        · rw [(d4_sparse_block_diag r hr ⟨11 + j.val, by omega⟩ k).2.2.2.1 (by dsimp; omega) hk,
            Int.cast_zero, zero_mul]
      rw [hb0, hsum, mul_zero, add_zero]
    · intro hc
      apply zorn_eq_of_zornCoord_eq
      intro j
      rw [← h3ZornCoord_c_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_c_eq, hc]
      have hc0 : zornCoord (0 : ZornVectorMatrix ℝ) j = 0 := by fin_cases j <;> rfl
      have hsum : ∑ k : Fin 27, (sparseVal (e6RootSparse r) ⟨19 + j.val, by omega⟩ k : ℝ) *
          h3ZornCoordinate X k = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : 19 ≤ k.val
        · have hkq : k = ⟨19 + (⟨k.val - 19, by omega⟩ : Fin 8).val, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          have hck : h3ZornCoordinate X k = 0 := by
            rw [hkq, h3ZornCoord_c_eq, hc]
            exact (zornCoord_eq_zero_iff 0).mpr rfl ⟨k.val - 19, by omega⟩
          rw [hck, mul_zero]
        · rw [(d4_sparse_block_diag r hr ⟨19 + j.val, by omega⟩ k).2.2.2.2 (by dsimp; omega) hk,
            Int.cast_zero, zero_mul]
      rw [hc0, hsum, mul_zero, add_zero]
  have hmain : ∀ g ∈ d4Subgroup,
      (∀ X : H3Zorn ℝ,
        (g.1 X).α₁ = X.α₁ ∧ (g.1 X).α₂ = X.α₂ ∧ (g.1 X).α₃ = X.α₃ ∧
        (X.a = 0 → (g.1 X).a = 0) ∧ (X.b = 0 → (g.1 X).b = 0) ∧ (X.c = 0 → (g.1 X).c = 0)) ∧
      (∀ X : H3Zorn ℝ,
        (g⁻¹.1 X).α₁ = X.α₁ ∧ (g⁻¹.1 X).α₂ = X.α₂ ∧ (g⁻¹.1 X).α₃ = X.α₃ ∧
        (X.a = 0 → (g⁻¹.1 X).a = 0) ∧ (X.b = 0 → (g⁻¹.1 X).b = 0) ∧ (X.c = 0 → (g⁻¹.1 X).c = 0)) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨⟨r, t⟩, rfl⟩
      have hinv : (e6RootExp r.1 t)⁻¹ = e6RootExp r.1 (-t) := by
        rw [inv_eq_iff_mul_eq_one, e6RootExp_mul, add_neg_cancel, e6RootExp_zero]
      refine ⟨hgen r.1 r.2 t, ?_⟩
      rw [hinv]
      exact hgen r.1 r.2 (-t)
    | one =>
      have hone : ∀ X : H3Zorn ℝ,
          ((1 : h3zornReducedStructureGroup).1 X).α₁ = X.α₁ ∧
          ((1 : h3zornReducedStructureGroup).1 X).α₂ = X.α₂ ∧
          ((1 : h3zornReducedStructureGroup).1 X).α₃ = X.α₃ ∧
          (X.a = 0 → ((1 : h3zornReducedStructureGroup).1 X).a = 0) ∧
          (X.b = 0 → ((1 : h3zornReducedStructureGroup).1 X).b = 0) ∧
          (X.c = 0 → ((1 : h3zornReducedStructureGroup).1 X).c = 0) :=
        fun _ => ⟨rfl, rfl, rfl, id, id, id⟩
      exact ⟨hone, hone⟩
    | mul a b _ _ iha ihb =>
      refine ⟨?_, ?_⟩
      · intro X
        obtain ⟨h1b, h2b, h3b, hab, hbb, hcb⟩ := ihb.1 X
        obtain ⟨h1a, h2a, h3a, haa, hba, hca⟩ := iha.1 (b.1 X)
        exact ⟨h1a.trans h1b, h2a.trans h2b, h3a.trans h3b,
          fun ha => haa (hab ha), fun hb => hba (hbb hb), fun hc => hca (hcb hc)⟩
      · intro X
        rw [mul_inv_rev]
        obtain ⟨h1a, h2a, h3a, haa, hba, hca⟩ := iha.2 X
        obtain ⟨h1b, h2b, h3b, hab, hbb, hcb⟩ := ihb.2 (a⁻¹.1 X)
        exact ⟨h1b.trans h1a, h2b.trans h2a, h3b.trans h3a,
          fun ha => hab (haa ha), fun hb => hbb (hba hb), fun hc => hcb (hca hc)⟩
    | inv x _ ih =>
      exact ⟨ih.2, fun X => by simpa only [inv_inv] using ih.1 X⟩
  exact (hmain g hg).1

theorem d4Subgroup_fix_one {g : h3zornReducedStructureGroup} (hg : g ∈ d4Subgroup) :
    g.1 1 = 1 := by
  obtain ⟨h1, h2, h3, ha, hb, hc⟩ := d4Subgroup_preserves_blocks hg (1 : H3Zorn ℝ)
  apply ext_h3
  · exact h1
  · exact h2
  · exact h3
  · exact ha rfl
  · exact hb rfl
  · exact hc rfl

theorem d4Subgroup_le_f4InChevalley : d4Subgroup ≤ e6F4InChevalley :=
  fun _ hg => ⟨d4Subgroup_mem_chevalley hg, d4Subgroup_fix_one hg⟩

/-- The 24 `F₄` Peirce-shift exponentials fixing `1`. -/
def f4PeirceExp (s : Fin 3) (i : Fin 8) (t : ℝ) : h3zornReducedStructureGroup :=
  e6RootExp ⟨24 + 16 * s.val + 2 * i.val, by omega⟩ t *
    e6RootExp ⟨25 + 16 * s.val + 2 * i.val, by omega⟩ (-t)

private theorem f4PeirceExp_fix_one_check1 :
    (List.finRange 3).all (fun s => (List.finRange 8).all (fun i =>
      (List.finRange 27).all (fun m =>
        (sparseVal (e6RootSparse ⟨24 + 16 * s.val + 2 * i.val, by omega⟩) m 0 +
         sparseVal (e6RootSparse ⟨24 + 16 * s.val + 2 * i.val, by omega⟩) m 1 +
         sparseVal (e6RootSparse ⟨24 + 16 * s.val + 2 * i.val, by omega⟩) m 2) ==
        (sparseVal (e6RootSparse ⟨25 + 16 * s.val + 2 * i.val, by omega⟩) m 0 +
         sparseVal (e6RootSparse ⟨25 + 16 * s.val + 2 * i.val, by omega⟩) m 1 +
         sparseVal (e6RootSparse ⟨25 + 16 * s.val + 2 * i.val, by omega⟩) m 2)))) = true := by
  decide

private theorem f4PeirceExp_fix_one_check2 :
    (List.finRange 3).all (fun s => (List.finRange 8).all (fun i =>
      (List.finRange 27).all (fun m =>
        (sparseVal (sparseMul (e6RootSparse ⟨24 + 16 * s.val + 2 * i.val, by omega⟩)
          (e6RootSparse ⟨25 + 16 * s.val + 2 * i.val, by omega⟩)) m 0 +
         sparseVal (sparseMul (e6RootSparse ⟨24 + 16 * s.val + 2 * i.val, by omega⟩)
          (e6RootSparse ⟨25 + 16 * s.val + 2 * i.val, by omega⟩)) m 1 +
         sparseVal (sparseMul (e6RootSparse ⟨24 + 16 * s.val + 2 * i.val, by omega⟩)
          (e6RootSparse ⟨25 + 16 * s.val + 2 * i.val, by omega⟩)) m 2) == 0))) = true := by
  decide

private theorem f4PeirceExp_fix_one (s : Fin 3) (i : Fin 8) (t : ℝ) :
    (f4PeirceExp s i t).1 1 = 1 := by
  have h1 := f4PeirceExp_fix_one_check1
  have h2 := f4PeirceExp_fix_one_check2
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h1 h2
  apply h3Zorn_ext_coord
  intro m
  rw [show f4PeirceExp s i t =
      e6RootExp ⟨24 + 16 * s.val + 2 * i.val, by omega⟩ t *
        e6RootExp ⟨25 + 16 * s.val + 2 * i.val, by omega⟩ (-t) from rfl,
    h3ZornCoordinate_e6RootExp_mul]
  have hsum1 : ∀ (sp : SparseMat27),
      (∑ k : Fin 27, (sparseVal sp m k : ℝ) * h3ZornCoordinate (1 : H3Zorn ℝ) k) =
        ((sparseVal sp m 0 + sparseVal sp m 1 + sparseVal sp m 2 : ℤ) : ℝ) := by
    intro sp
    rw [sum_fin27_eq_three_of_support _ (fun k hk => by
      rw [h3ZornCoordinate_one]; simp [hk])]
    simp only [h3ZornCoordinate_one, show (0 : Fin 27).val < 3 by decide,
      show (1 : Fin 27).val < 3 by decide, show (2 : Fin 27).val < 3 by decide,
      ↓reduceIte, mul_one, Int.cast_add]
  rw [hsum1, hsum1, hsum1, h1 s i m, h2 s i m, Int.cast_zero]
  ring

theorem f4PeirceExp_mem_f4 (s : Fin 3) (i : Fin 8) (t : ℝ) :
    f4PeirceExp s i t ∈ e6F4InChevalley :=
  ⟨e6ChevalleySubgroup.mul_mem (e6RootExp_mem_chevalley _ _) (e6RootExp_mem_chevalley _ _),
    f4PeirceExp_fix_one s i t⟩

/-- Idempotent swap `E₁ ↔ E₂` inside `F₄(4)`. -/
def w12 : h3zornReducedStructureGroup :=
  f4PeirceExp 0 0 1 * f4PeirceExp 0 7 1 * f4PeirceExp 0 0 1

/-- Idempotent swap `E₂ ↔ E₃` inside `F₄(4)`. -/
def w23 : h3zornReducedStructureGroup :=
  f4PeirceExp 1 0 1 * f4PeirceExp 1 7 1 * f4PeirceExp 1 0 1

/-- Idempotent swap `E₃ ↔ E₁` inside `F₄(4)`. -/
def w31 : h3zornReducedStructureGroup :=
  f4PeirceExp 2 0 1 * f4PeirceExp 2 7 1 * f4PeirceExp 2 0 1

theorem w12_mem_f4 : w12 ∈ e6F4InChevalley :=
  e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 0 0 1) (f4PeirceExp_mem_f4 0 7 1))
    (f4PeirceExp_mem_f4 0 0 1)

theorem w23_mem_f4 : w23 ∈ e6F4InChevalley :=
  e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 1 0 1) (f4PeirceExp_mem_f4 1 7 1))
    (f4PeirceExp_mem_f4 1 0 1)

theorem w31_mem_f4 : w31 ∈ e6F4InChevalley :=
  e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 2 0 1) (f4PeirceExp_mem_f4 2 7 1))
    (f4PeirceExp_mem_f4 2 0 1)

/-- Sparse integer matrix of `f4PeirceExp s i 1`. -/
private def f4PeirceOneSparse (s : Fin 3) (i : Fin 8) : SparseMat27 :=
  let rp := e6RootSparse ⟨24 + 16 * s.val + 2 * i.val, by omega⟩
  let rm := e6RootSparse ⟨25 + 16 * s.val + 2 * i.val, by omega⟩
  sparseSub (sparseSub rp rm) (sparseMul rp rm)

private theorem h3zornToMatrix_f4PeirceOne (s : Fin 3) (i : Fin 8) :
    h3zornToMatrix (f4PeirceExp s i 1).1.toLinearMap =
      (1 : Matrix (Fin 27) (Fin 27) ℝ) + (sparseToMat (f4PeirceOneSparse s i)).map Int.cast := by
  let rp : Fin 72 := ⟨24 + 16 * s.val + 2 * i.val, by omega⟩
  let rm : Fin 72 := ⟨25 + 16 * s.val + 2 * i.val, by omega⟩
  have hm : (f4PeirceExp s i 1).1.toLinearMap =
      ((1 : Module.End ℝ (H3Zorn ℝ)) + (e6RootVec rp).1) *
        ((1 : Module.End ℝ (H3Zorn ℝ)) - (e6RootVec rm).1) := by
    change ((e6RootExp rp 1).1.toLinearMap * (e6RootExp rm (-1)).1.toLinearMap) = _
    simp only [e6RootExp_coe_toLinearMap, one_smul, neg_one_smul, sub_eq_add_neg]
  rw [hm, map_mul, map_add, map_sub, _root_.map_one h3zornToMatrix,
    h3zornToMatrix_e6RootVec, h3zornToMatrix_e6RootVec]
  dsimp [f4PeirceOneSparse]
  simp only [sparseToMat_sub, sparseToMat_mul, add_mul, mul_sub, one_mul, mul_one]
  ext r c
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply,
    Matrix.mul_apply, Int.cast_sub, Int.cast_sum, Int.cast_mul]
  ring

private def f4P0Lit : Fin 3 → SparseMat27
  | 0 => [(0, 10, 1), (1, 10, -1), (3, 0, -1), (3, 1, 1), (3, 10, -1), (15, 23, 1),
          (16, 24, 1), (17, 25, 1), (18, 19, -1), (20, 12, -1), (21, 13, -1), (22, 14, -1), (26, 11, 1)]
  | 1 => [(1, 18, 1), (2, 18, -1), (4, 20, -1), (5, 21, -1), (6, 22, -1), (10, 19, 1),
          (11, 1, -1), (11, 2, 1), (11, 18, -1), (23, 7, 1), (24, 8, 1), (25, 9, 1), (26, 3, -1)]
  | 2 => [(0, 26, -1), (2, 26, 1), (7, 15, 1), (8, 16, 1), (9, 17, 1), (10, 11, -1),
          (12, 4, -1), (13, 5, -1), (14, 6, -1), (18, 3, 1), (19, 0, 1), (19, 2, -1), (19, 26, -1)]

private def f4P7Lit : Fin 3 → SparseMat27
  | 0 => [(0, 3, 1), (1, 3, -1), (10, 0, -1), (10, 1, 1), (10, 3, -1), (11, 26, -1),
          (12, 20, 1), (13, 21, 1), (14, 22, 1), (19, 18, 1), (23, 15, -1), (24, 16, -1), (25, 17, -1)]
  | 1 => [(1, 11, 1), (2, 11, -1), (3, 26, 1), (7, 23, -1), (8, 24, -1), (9, 25, -1),
          (18, 1, -1), (18, 2, 1), (18, 11, -1), (19, 10, -1), (20, 4, 1), (21, 5, 1), (22, 6, 1)]
  | 2 => [(0, 19, -1), (2, 19, 1), (3, 18, -1), (4, 12, 1), (5, 13, 1), (6, 14, 1),
          (11, 10, 1), (15, 7, -1), (16, 8, -1), (17, 9, -1), (26, 0, 1), (26, 2, -1), (26, 19, -1)]

private theorem f4P0Lit_check :
    (List.finRange 3).all (fun s => sparseEq (f4PeirceOneSparse s 0) (f4P0Lit s)) = true := by
  decide

private theorem f4P7Lit_check :
    (List.finRange 3).all (fun s => sparseEq (f4PeirceOneSparse s 7) (f4P7Lit s)) = true := by
  decide

private theorem sparseToMat_f4P0Lit (s : Fin 3) :
    sparseToMat (f4PeirceOneSparse s 0) = sparseToMat (f4P0Lit s) := by
  have hc := f4P0Lit_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc
  exact sparseToMat_eq_of_sparseEq (hc s)

private theorem sparseToMat_f4P7Lit (s : Fin 3) :
    sparseToMat (f4PeirceOneSparse s 7) = sparseToMat (f4P7Lit s) := by
  have hc := f4P7Lit_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc
  exact sparseToMat_eq_of_sparseEq (hc s)

private def w12Sparse : SparseMat27 :=
  [(0, 1, 1), (1, 0, 1), (2, 2, 1), (3, 10, -1), (4, 4, 1), (5, 5, 1), (6, 6, 1), (7, 7, 1), (8, 8, 1), (9, 9, 1), (10, 3, -1), (11, 26, -1), (12, 20, 1), (13, 21, 1), (14, 22, 1), (15, 23, 1), (16, 24, 1), (17, 25, 1), (18, 19, -1), (19, 18, 1), (20, 12, -1), (21, 13, -1), (22, 14, -1), (23, 15, -1), (24, 16, -1), (25, 17, -1), (26, 11, 1)]

private def w23Sparse : SparseMat27 :=
  [(0, 0, 1), (1, 2, 1), (2, 1, 1), (3, 26, 1), (4, 20, -1), (5, 21, -1), (6, 22, -1), (7, 23, -1), (8, 24, -1), (9, 25, -1), (10, 19, 1), (11, 18, -1), (12, 12, 1), (13, 13, 1), (14, 14, 1), (15, 15, 1), (16, 16, 1), (17, 17, 1), (18, 11, -1), (19, 10, -1), (20, 4, 1), (21, 5, 1), (22, 6, 1), (23, 7, 1), (24, 8, 1), (25, 9, 1), (26, 3, -1)]

private def w31Sparse : SparseMat27 :=
  [(0, 2, 1), (1, 1, 1), (2, 0, 1), (3, 18, -1), (4, 12, 1), (5, 13, 1), (6, 14, 1), (7, 15, 1), (8, 16, 1), (9, 17, 1), (10, 11, -1), (11, 10, 1), (12, 4, -1), (13, 5, -1), (14, 6, -1), (15, 7, -1), (16, 8, -1), (17, 9, -1), (18, 3, 1), (19, 26, -1), (20, 20, 1), (21, 21, 1), (22, 22, 1), (23, 23, 1), (24, 24, 1), (25, 25, 1), (26, 19, -1)]

private def f4P07Lit : Fin 3 → SparseMat27
  | 0 => [(0, 0, -1), (0, 1, 1), (0, 3, -1), (1, 0, 1), (1, 1, -1), (1, 3, 1), (3, 0, 1), (3, 1, -1), (3, 3, -1), (15, 15, -1), (16, 16, -1), (17, 17, -1), (18, 18, -1), (20, 20, -1), (21, 21, -1), (22, 22, -1), (26, 26, -1)]
  | 1 => [(1, 1, -1), (1, 2, 1), (1, 11, -1), (2, 1, 1), (2, 2, -1), (2, 11, 1), (4, 4, -1), (5, 5, -1), (6, 6, -1), (10, 10, -1), (11, 1, 1), (11, 2, -1), (11, 11, -1), (23, 23, -1), (24, 24, -1), (25, 25, -1), (26, 26, -1)]
  | 2 => [(0, 0, -1), (0, 2, 1), (0, 19, 1), (2, 0, 1), (2, 2, -1), (2, 19, -1), (7, 7, -1), (8, 8, -1), (9, 9, -1), (10, 10, -1), (12, 12, -1), (13, 13, -1), (14, 14, -1), (18, 18, -1), (19, 0, -1), (19, 2, 1), (19, 19, -1)]

private def f4D07Lit : Fin 3 → SparseMat27
  | 0 => [(0, 0, -1), (0, 1, 1), (0, 10, 1), (1, 0, 1), (1, 1, -1), (1, 10, -1), (3, 3, -1), (3, 10, -1), (10, 0, -1), (10, 1, 1), (10, 3, -1), (11, 26, -1), (12, 20, 1), (13, 21, 1), (14, 22, 1), (15, 15, -1), (15, 23, 1), (16, 16, -1), (16, 24, 1), (17, 17, -1), (17, 25, 1), (18, 18, -1), (18, 19, -1), (19, 18, 1), (20, 12, -1), (20, 20, -1), (21, 13, -1), (21, 21, -1), (22, 14, -1), (22, 22, -1), (23, 15, -1), (24, 16, -1), (25, 17, -1), (26, 11, 1), (26, 26, -1)]
  | 1 => [(1, 1, -1), (1, 2, 1), (1, 18, 1), (2, 1, 1), (2, 2, -1), (2, 18, -1), (3, 26, 1), (4, 4, -1), (4, 20, -1), (5, 5, -1), (5, 21, -1), (6, 6, -1), (6, 22, -1), (7, 23, -1), (8, 24, -1), (9, 25, -1), (10, 10, -1), (10, 19, 1), (11, 11, -1), (11, 18, -1), (18, 1, -1), (18, 2, 1), (18, 11, -1), (19, 10, -1), (20, 4, 1), (21, 5, 1), (22, 6, 1), (23, 7, 1), (23, 23, -1), (24, 8, 1), (24, 24, -1), (25, 9, 1), (25, 25, -1), (26, 3, -1), (26, 26, -1)]
  | 2 => [(0, 0, -1), (0, 2, 1), (0, 26, -1), (2, 0, 1), (2, 2, -1), (2, 26, 1), (3, 18, -1), (4, 12, 1), (5, 13, 1), (6, 14, 1), (7, 7, -1), (7, 15, 1), (8, 8, -1), (8, 16, 1), (9, 9, -1), (9, 17, 1), (10, 10, -1), (10, 11, -1), (11, 10, 1), (12, 4, -1), (12, 12, -1), (13, 5, -1), (13, 13, -1), (14, 6, -1), (14, 14, -1), (15, 7, -1), (16, 8, -1), (17, 9, -1), (18, 3, 1), (18, 18, -1), (19, 19, -1), (19, 26, -1), (26, 0, 1), (26, 2, -1), (26, 19, -1)]

private def f4D07P0Lit : Fin 3 → SparseMat27
  | 0 => [(0, 10, -2), (1, 10, 2), (3, 0, 1), (3, 1, -1), (3, 10, 1), (10, 0, 1), (10, 1, -1), (10, 10, -1), (11, 11, -1), (12, 12, -1), (13, 13, -1), (14, 14, -1), (15, 23, -1), (16, 24, -1), (17, 25, -1), (18, 19, 1), (19, 19, -1), (20, 12, 1), (21, 13, 1), (22, 14, 1), (23, 23, -1), (24, 24, -1), (25, 25, -1), (26, 11, -1)]
  | 1 => [(1, 18, -2), (2, 18, 2), (3, 3, -1), (4, 20, 1), (5, 21, 1), (6, 22, 1), (7, 7, -1), (8, 8, -1), (9, 9, -1), (10, 19, -1), (11, 1, 1), (11, 2, -1), (11, 18, 1), (18, 1, 1), (18, 2, -1), (18, 18, -1), (19, 19, -1), (20, 20, -1), (21, 21, -1), (22, 22, -1), (23, 7, -1), (24, 8, -1), (25, 9, -1), (26, 3, 1)]
  | 2 => [(0, 26, 2), (2, 26, -2), (3, 3, -1), (4, 4, -1), (5, 5, -1), (6, 6, -1), (7, 15, -1), (8, 16, -1), (9, 17, -1), (10, 11, 1), (11, 11, -1), (12, 4, 1), (13, 5, 1), (14, 6, 1), (15, 15, -1), (16, 16, -1), (17, 17, -1), (18, 3, -1), (19, 0, -1), (19, 2, 1), (19, 26, 1), (26, 0, -1), (26, 2, 1), (26, 26, -1)]

private theorem sparseToMat_eq_of_pointwise (a b : SparseMat27)
    (h : (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal a r c == sparseVal b r c)) = true) :
    sparseToMat a = sparseToMat b := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  ext r c
  exact h r c

private theorem sparseToMat_eq_sum3_of_pointwise (w a b c : SparseMat27)
    (h : (List.finRange 27).all (fun r => (List.finRange 27).all (fun col =>
      sparseVal w r col == sparseVal a r col + sparseVal b r col + sparseVal c r col)) = true) :
    sparseToMat w = sparseToMat a + sparseToMat b + sparseToMat c := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  ext r col
  exact h r col

private theorem sparseToMat_eq_one_add3_of_pointwise (w a b c : SparseMat27)
    (h : (List.finRange 27).all (fun r => (List.finRange 27).all (fun col =>
      sparseVal w r col ==
        (if r == col then 1 else 0) + sparseVal a r col + sparseVal b r col + sparseVal c r col)) = true) :
    sparseToMat w = (1 : Matrix (Fin 27) (Fin 27) ℤ) + (sparseToMat a + sparseToMat b + sparseToMat c) := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  ext r col
  simpa [sparseToMat, Matrix.one_apply, add_assoc] using h r col

private theorem f4P07Lit_check0 :
    (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal (sparseMul (f4P0Lit 0) (f4P7Lit 0)) r c == sparseVal (f4P07Lit 0) r c)) = true := by decide
private theorem f4P07Lit_check1 :
    (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal (sparseMul (f4P0Lit 1) (f4P7Lit 1)) r c == sparseVal (f4P07Lit 1) r c)) = true := by decide
private theorem f4P07Lit_check2 :
    (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal (sparseMul (f4P0Lit 2) (f4P7Lit 2)) r c == sparseVal (f4P07Lit 2) r c)) = true := by decide

private theorem sparseToMat_f4P07Lit (s : Fin 3) :
    sparseToMat (f4P07Lit s) = sparseToMat (f4P0Lit s) * sparseToMat (f4P7Lit s) := by
  rw [← sparseToMat_mul]
  fin_cases s
  · exact (sparseToMat_eq_of_pointwise _ _ f4P07Lit_check0).symm
  · exact (sparseToMat_eq_of_pointwise _ _ f4P07Lit_check1).symm
  · exact (sparseToMat_eq_of_pointwise _ _ f4P07Lit_check2).symm

private theorem f4D07Lit_check0 :
    (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal (f4D07Lit 0) r c ==
        sparseVal (f4P0Lit 0) r c + sparseVal (f4P7Lit 0) r c + sparseVal (f4P07Lit 0) r c)) = true := by decide
private theorem f4D07Lit_check1 :
    (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal (f4D07Lit 1) r c ==
        sparseVal (f4P0Lit 1) r c + sparseVal (f4P7Lit 1) r c + sparseVal (f4P07Lit 1) r c)) = true := by decide
private theorem f4D07Lit_check2 :
    (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal (f4D07Lit 2) r c ==
        sparseVal (f4P0Lit 2) r c + sparseVal (f4P7Lit 2) r c + sparseVal (f4P07Lit 2) r c)) = true := by decide

private theorem sparseToMat_f4D07Lit (s : Fin 3) :
    sparseToMat (f4D07Lit s) =
      sparseToMat (f4P0Lit s) + sparseToMat (f4P7Lit s) +
        sparseToMat (f4P0Lit s) * sparseToMat (f4P7Lit s) := by
  rw [← sparseToMat_f4P07Lit s]
  fin_cases s
  · exact sparseToMat_eq_sum3_of_pointwise _ _ _ _ f4D07Lit_check0
  · exact sparseToMat_eq_sum3_of_pointwise _ _ _ _ f4D07Lit_check1
  · exact sparseToMat_eq_sum3_of_pointwise _ _ _ _ f4D07Lit_check2

private theorem f4D07P0Lit_check0 :
    (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal (sparseMul (f4D07Lit 0) (f4P0Lit 0)) r c == sparseVal (f4D07P0Lit 0) r c)) = true := by decide
private theorem f4D07P0Lit_check1 :
    (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal (sparseMul (f4D07Lit 1) (f4P0Lit 1)) r c == sparseVal (f4D07P0Lit 1) r c)) = true := by decide
private theorem f4D07P0Lit_check2 :
    (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal (sparseMul (f4D07Lit 2) (f4P0Lit 2)) r c == sparseVal (f4D07P0Lit 2) r c)) = true := by decide

private theorem sparseToMat_f4D07P0Lit (s : Fin 3) :
    sparseToMat (f4D07P0Lit s) = sparseToMat (f4D07Lit s) * sparseToMat (f4P0Lit s) := by
  rw [← sparseToMat_mul]
  fin_cases s
  · exact (sparseToMat_eq_of_pointwise _ _ f4D07P0Lit_check0).symm
  · exact (sparseToMat_eq_of_pointwise _ _ f4D07P0Lit_check1).symm
  · exact (sparseToMat_eq_of_pointwise _ _ f4D07P0Lit_check2).symm

private theorem f4_swap_expand_mat_two (P0 D07 : Matrix (Fin 27) (Fin 27) ℝ) :
    (1 + D07) * (1 + P0) = 1 + (D07 + P0 + D07 * P0) := by
  simp only [mul_add, add_mul, one_mul, mul_one]
  abel

private theorem h3zornToMatrix_f4Swap_aux (s : Fin 3) (ws : SparseMat27)
    (hchk : sparseToMat ws =
      (1 : Matrix (Fin 27) (Fin 27) ℤ) +
        (sparseToMat (f4D07Lit s) + sparseToMat (f4P0Lit s) + sparseToMat (f4D07P0Lit s))) :
    ((1 : Matrix (Fin 27) (Fin 27) ℝ) + (sparseToMat (f4PeirceOneSparse s 0)).map Int.cast) *
      ((1 : Matrix (Fin 27) (Fin 27) ℝ) + (sparseToMat (f4PeirceOneSparse s 7)).map Int.cast) *
      ((1 : Matrix (Fin 27) (Fin 27) ℝ) + (sparseToMat (f4PeirceOneSparse s 0)).map Int.cast) =
      (sparseToMat ws).map Int.cast := by
  have hd07 : ((1 : Matrix (Fin 27) (Fin 27) ℝ) + (sparseToMat (f4PeirceOneSparse s 0)).map Int.cast) *
      ((1 : Matrix (Fin 27) (Fin 27) ℝ) + (sparseToMat (f4PeirceOneSparse s 7)).map Int.cast) =
      (1 : Matrix (Fin 27) (Fin 27) ℝ) + (sparseToMat (f4D07Lit s)).map Int.cast := by
    rw [sparseToMat_f4P0Lit s, sparseToMat_f4P7Lit s, sparseToMat_f4D07Lit s]
    ext r c
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, Matrix.one_apply,
      Int.cast_add, Int.cast_sum, Int.cast_mul]
    have hsplit : (∑ x : Fin 27, ((if r = x then (1 : ℝ) else 0) + (sparseToMat (f4P0Lit s) r x : ℝ)) *
        ((if x = c then (1 : ℝ) else 0) + (sparseToMat (f4P7Lit s) x c : ℝ))) =
        (if r = c then (1 : ℝ) else 0) + (sparseToMat (f4P0Lit s) r c : ℝ) +
          (sparseToMat (f4P7Lit s) r c : ℝ) +
          ∑ x : Fin 27, (sparseToMat (f4P0Lit s) r x : ℝ) * (sparseToMat (f4P7Lit s) x c : ℝ) := by
      simp only [add_mul, mul_add, Finset.sum_add_distrib]
      simp [Finset.sum_ite_eq, Finset.sum_ite_eq', add_assoc]
    rw [hsplit]
    ring
  rw [hd07, sparseToMat_f4P0Lit s, f4_swap_expand_mat_two]
  have hm' := congrArg (Matrix.map · (Int.cast : ℤ → ℝ)) hchk
  rw [hm']
  have hdp := congrArg (Matrix.map · (Int.cast : ℤ → ℝ)) (sparseToMat_f4D07P0Lit s)
  ext r c
  have hdp_rc := congrFun (congrFun hdp r) c
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.one_apply, Matrix.mul_apply,
    Int.cast_add, Int.cast_sum, Int.cast_mul] at hdp_rc ⊢
  rw [← hdp_rc]
  split_ifs <;> simp

private theorem w12_check :
    (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal w12Sparse r c ==
        (if r == c then 1 else 0) + sparseVal (f4D07Lit 0) r c + sparseVal (f4P0Lit 0) r c +
          sparseVal (f4D07P0Lit 0) r c)) = true := by decide

private theorem w23_check :
    (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal w23Sparse r c ==
        (if r == c then 1 else 0) + sparseVal (f4D07Lit 1) r c + sparseVal (f4P0Lit 1) r c +
          sparseVal (f4D07P0Lit 1) r c)) = true := by decide

private theorem w31_check :
    (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
      sparseVal w31Sparse r c ==
        (if r == c then 1 else 0) + sparseVal (f4D07Lit 2) r c + sparseVal (f4P0Lit 2) r c +
          sparseVal (f4D07P0Lit 2) r c)) = true := by decide

private theorem h3zornToMatrix_w12_sparse :
    h3zornToMatrix w12.1.toLinearMap = (sparseToMat w12Sparse).map Int.cast := by
  have hm : w12.1.toLinearMap =
      (f4PeirceExp 0 0 1).1.toLinearMap * (f4PeirceExp 0 7 1).1.toLinearMap *
        (f4PeirceExp 0 0 1).1.toLinearMap := rfl
  rw [hm, map_mul, map_mul, h3zornToMatrix_f4PeirceOne, h3zornToMatrix_f4PeirceOne]
  exact h3zornToMatrix_f4Swap_aux 0 w12Sparse (sparseToMat_eq_one_add3_of_pointwise _ _ _ _ w12_check)

private theorem h3zornToMatrix_w23_sparse :
    h3zornToMatrix w23.1.toLinearMap = (sparseToMat w23Sparse).map Int.cast := by
  have hm : w23.1.toLinearMap =
      (f4PeirceExp 1 0 1).1.toLinearMap * (f4PeirceExp 1 7 1).1.toLinearMap *
        (f4PeirceExp 1 0 1).1.toLinearMap := rfl
  rw [hm, map_mul, map_mul, h3zornToMatrix_f4PeirceOne, h3zornToMatrix_f4PeirceOne]
  exact h3zornToMatrix_f4Swap_aux 1 w23Sparse (sparseToMat_eq_one_add3_of_pointwise _ _ _ _ w23_check)

private theorem h3zornToMatrix_w31_sparse :
    h3zornToMatrix w31.1.toLinearMap = (sparseToMat w31Sparse).map Int.cast := by
  have hm : w31.1.toLinearMap =
      (f4PeirceExp 2 0 1).1.toLinearMap * (f4PeirceExp 2 7 1).1.toLinearMap *
        (f4PeirceExp 2 0 1).1.toLinearMap := rfl
  rw [hm, map_mul, map_mul, h3zornToMatrix_f4PeirceOne, h3zornToMatrix_f4PeirceOne]
  exact h3zornToMatrix_f4Swap_aux 2 w31Sparse (sparseToMat_eq_one_add3_of_pointwise _ _ _ _ w31_check)

private theorem h3ZornCoordinate_of_matrix_equiv (T : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (s : SparseMat27)
    (hs : h3zornToMatrix T.toLinearMap = (sparseToMat s).map Int.cast) (X : H3Zorn ℝ) (m : Fin 27) :
    h3ZornCoordinate (T X) m =
      ∑ k : Fin 27, (sparseVal s m k : ℝ) * h3ZornCoordinate X k := by
  have hrep : X = ∑ k : Fin 27, h3ZornCoordinate X k • h3ZornBasis k :=
    (h3ZornBasis.sum_repr X).symm
  conv_lhs => rw [hrep, map_sum]
  change h3ZornCoordinateLM (∑ k : Fin 27, T (h3ZornCoordinate X k • h3ZornBasis k)) m = _
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  change h3ZornCoordinate (h3ZornCoordinate X k • T (h3ZornBasis k)) m = _
  rw [h3ZornCoordinate_smul, mul_comm]
  congr 1
  have hm : h3ZornCoordinate (T (h3ZornBasis k)) m = h3zornToMatrix T.toLinearMap m k :=
    (h3zornToMatrix_apply T.toLinearMap m k).symm
  rw [hm, hs, Matrix.map_apply, sparseToMat]

private theorem w12_diag_coords (X : H3Zorn ℝ) :
    (w12.1 X).α₁ = X.α₂ ∧ (w12.1 X).α₂ = X.α₁ ∧ (w12.1 X).α₃ = X.α₃ := by
  have hc : (List.finRange 27).all (fun k =>
      (sparseVal w12Sparse 0 k == if k.val = 1 then 1 else 0) &&
      (sparseVal w12Sparse 1 k == if k.val = 0 then 1 else 0) &&
      (sparseVal w12Sparse 2 k == if k.val = 2 then 1 else 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc
  refine ⟨?_, ?_, ?_⟩
  · change h3ZornCoordinate (w12.1 X) 0 = h3ZornCoordinate X 1
    rw [h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w12_sparse]
    rw [Finset.sum_eq_single 1]
    · simp [(hc 1).1.1]
    · intro k _ hk
      have hne : k.val ≠ 1 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1, hne]
    · intro h; exact absurd (Finset.mem_univ 1) h
  · change h3ZornCoordinate (w12.1 X) 1 = h3ZornCoordinate X 0
    rw [h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w12_sparse]
    rw [Finset.sum_eq_single 0]
    · simp [(hc 0).1.2]
    · intro k _ hk
      have hne : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [(hc k).1.2, hne]
    · intro h; exact absurd (Finset.mem_univ 0) h
  · change h3ZornCoordinate (w12.1 X) 2 = h3ZornCoordinate X 2
    rw [h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w12_sparse]
    rw [Finset.sum_eq_single 2]
    · simp [(hc 2).2]
    · intro k _ hk
      have hne : k.val ≠ 2 := fun h => hk (Fin.ext h)
      simp [(hc k).2, hne]
    · intro h; exact absurd (Finset.mem_univ 2) h

private theorem w23_diag_coords (X : H3Zorn ℝ) :
    (w23.1 X).α₁ = X.α₁ ∧ (w23.1 X).α₂ = X.α₃ ∧ (w23.1 X).α₃ = X.α₂ := by
  have hc : (List.finRange 27).all (fun k =>
      (sparseVal w23Sparse 0 k == if k.val = 0 then 1 else 0) &&
      (sparseVal w23Sparse 1 k == if k.val = 2 then 1 else 0) &&
      (sparseVal w23Sparse 2 k == if k.val = 1 then 1 else 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc
  refine ⟨?_, ?_, ?_⟩
  · change h3ZornCoordinate (w23.1 X) 0 = h3ZornCoordinate X 0
    rw [h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w23_sparse]
    rw [Finset.sum_eq_single 0]
    · simp [(hc 0).1.1]
    · intro k _ hk
      have hne : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1, hne]
    · intro h; exact absurd (Finset.mem_univ 0) h
  · change h3ZornCoordinate (w23.1 X) 1 = h3ZornCoordinate X 2
    rw [h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w23_sparse]
    rw [Finset.sum_eq_single 2]
    · simp [(hc 2).1.2]
    · intro k _ hk
      have hne : k.val ≠ 2 := fun h => hk (Fin.ext h)
      simp [(hc k).1.2, hne]
    · intro h; exact absurd (Finset.mem_univ 2) h
  · change h3ZornCoordinate (w23.1 X) 2 = h3ZornCoordinate X 1
    rw [h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w23_sparse]
    rw [Finset.sum_eq_single 1]
    · simp [(hc 1).2]
    · intro k _ hk
      have hne : k.val ≠ 1 := fun h => hk (Fin.ext h)
      simp [(hc k).2, hne]
    · intro h; exact absurd (Finset.mem_univ 1) h

private theorem w31_diag_coords (X : H3Zorn ℝ) :
    (w31.1 X).α₁ = X.α₃ ∧ (w31.1 X).α₂ = X.α₂ ∧ (w31.1 X).α₃ = X.α₁ := by
  have hc : (List.finRange 27).all (fun k =>
      (sparseVal w31Sparse 0 k == if k.val = 2 then 1 else 0) &&
      (sparseVal w31Sparse 1 k == if k.val = 1 then 1 else 0) &&
      (sparseVal w31Sparse 2 k == if k.val = 0 then 1 else 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc
  refine ⟨?_, ?_, ?_⟩
  · change h3ZornCoordinate (w31.1 X) 0 = h3ZornCoordinate X 2
    rw [h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w31_sparse]
    rw [Finset.sum_eq_single 2]
    · simp [(hc 2).1.1]
    · intro k _ hk
      have hne : k.val ≠ 2 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1, hne]
    · intro h; exact absurd (Finset.mem_univ 2) h
  · change h3ZornCoordinate (w31.1 X) 1 = h3ZornCoordinate X 1
    rw [h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w31_sparse]
    rw [Finset.sum_eq_single 1]
    · simp [(hc 1).1.2]
    · intro k _ hk
      have hne : k.val ≠ 1 := fun h => hk (Fin.ext h)
      simp [(hc k).1.2, hne]
    · intro h; exact absurd (Finset.mem_univ 1) h
  · change h3ZornCoordinate (w31.1 X) 2 = h3ZornCoordinate X 0
    rw [h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w31_sparse]
    rw [Finset.sum_eq_single 0]
    · simp [(hc 0).2]
    · intro k _ hk
      have hne : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [(hc k).2, hne]
    · intro h; exact absurd (Finset.mem_univ 0) h

private theorem w23_fix_diag1 : w23.1 h3_diag₁ = h3_diag₁ := by
  have hc : (List.finRange 27).all (fun m =>
      sparseVal w23Sparse m 0 == if m.val = 0 then 1 else 0) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  apply h3Zorn_ext_coord
  intro m
  rw [h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w23_sparse]
  rw [Finset.sum_eq_single 0]
  · have hd : h3ZornCoordinate h3_diag₁ 0 = 1 := rfl
    have hm : h3ZornCoordinate h3_diag₁ m = if m.val = 0 then 1 else 0 := by fin_cases m <;> rfl
    rw [hd, hm, hc m, mul_one]
    split_ifs <;> simp
  · intro k _ hk
    have hkz : h3ZornCoordinate h3_diag₁ k = 0 := by fin_cases k <;> simp_all [h3_diag₁, h3ZornCoordinate]
    rw [hkz, mul_zero]
  · intro h; exact absurd (Finset.mem_univ 0) h

private theorem w23_zero_b_of_zero_ac_check :
    (List.finRange 27).all (fun m => (List.finRange 27).all (fun k =>
      if (m.val = 2 || (11 ≤ m.val && m.val < 27)) then
        if (k.val = 0 || k.val = 2 || (19 ≤ k.val && k.val < 27)) then
          sparseVal w23Sparse m k == 0
        else true
      else true)) = true := by decide

private theorem w23_zero_b_of_zero_ac {X : H3Zorn ℝ} (h2 : X.α₂ = 0) (ha : X.a = 0) (hb : X.b = 0) :
    (w23.1 X).α₃ = 0 ∧ (w23.1 X).b = 0 ∧ (w23.1 X).c = 0 := by
  have hc := w23_zero_b_of_zero_ac_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc
  have hzero_m : ∀ m : Fin 27, m.val = 2 ∨ (11 ≤ m.val ∧ m.val < 27) →
      h3ZornCoordinate (w23.1 X) m = 0 := by
    intro m hm
    rw [h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w23_sparse]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k.val = 0 ∨ k.val = 2 ∨ (19 ≤ k.val ∧ k.val < 27)
    · have hcc := hc m k
      have hm_b : (m.val = 2 || (11 ≤ m.val && m.val < 27)) = true := by
        rcases hm with hm2 | ⟨h11, h27⟩
        · simp [hm2]
        · simp [h11, h27]
      have hk_b : (k.val = 0 || k.val = 2 || (19 ≤ k.val && k.val < 27)) = true := by
        rcases hk with hk0 | hk2 | ⟨h19, h27⟩
        · simp [hk0]
        · simp [hk2]
        · simp [h19, h27]
      rw [hm_b, hk_b] at hcc
      simp only [↓reduceIte, beq_iff_eq] at hcc
      rw [hcc, Int.cast_zero, zero_mul]
    · have hk1 : k.val = 1 ∨ (3 ≤ k.val ∧ k.val < 11) ∨ (11 ≤ k.val ∧ k.val < 19) := by omega
      have hxk : h3ZornCoordinate X k = 0 := by
        rcases hk1 with h1 | ⟨h3, h11⟩ | ⟨h11, h19⟩
        · have hk_eq : k = 1 := Fin.ext h1
          rw [hk_eq, h3ZornCoord_one_eq, h2]
        · have hk_eq : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [hk_eq, h3ZornCoord_a_eq, ha]
          exact (zornCoord_eq_zero_iff 0).mpr rfl ⟨k.val - 3, by omega⟩
        · have hk_eq : k = ⟨11 + (⟨k.val - 11, by omega⟩ : Fin 8).val, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [hk_eq, h3ZornCoord_b_eq, hb]
          exact (zornCoord_eq_zero_iff 0).mpr rfl ⟨k.val - 11, by omega⟩
      rw [hxk, mul_zero]
  refine ⟨hzero_m 2 (Or.inl rfl), ?_, ?_⟩
  · apply zorn_eq_of_zornCoord_eq
    intro j
    rw [← h3ZornCoord_b_eq, hzero_m ⟨11 + j.val, by omega⟩ (Or.inr ⟨by dsimp; omega, by dsimp; omega⟩)]
    fin_cases j <;> rfl
  · apply zorn_eq_of_zornCoord_eq
    intro j
    rw [← h3ZornCoord_c_eq, hzero_m ⟨19 + j.val, by omega⟩ (Or.inr ⟨by dsimp; omega, by dsimp; omega⟩)]
    fin_cases j <;> rfl

/-! ### Step B1 & B2: Idempotent Reduction in `F₄(4)` -/

private theorem rootExp_coord_unchanged (r : Fin 72) (m : Fin 27) (t : ℝ) (X : H3Zorn ℝ)
    (hz : ∀ k : Fin 27, sparseVal (e6RootSparse r) m k = 0) :
    h3ZornCoordinate ((e6RootExp r t).1 X) m = h3ZornCoordinate X m := by
  rw [h3ZornCoordinate_e6RootExp]
  have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse r) m k : ℝ) * h3ZornCoordinate X k) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hz k, Int.cast_zero, zero_mul]
  rw [hs, mul_zero, add_zero]

private theorem rootExp_coord_add_single (r : Fin 72) (m k₀ : Fin 27) (v : ℤ) (t : ℝ) (X : H3Zorn ℝ)
    (hs : ∀ k : Fin 27, sparseVal (e6RootSparse r) m k = if k = k₀ then v else 0) :
    h3ZornCoordinate ((e6RootExp r t).1 X) m =
      h3ZornCoordinate X m + t * ((v : ℝ) * h3ZornCoordinate X k₀) := by
  rw [h3ZornCoordinate_e6RootExp]
  have hsum : (∑ k : Fin 27, (sparseVal (e6RootSparse r) m k : ℝ) * h3ZornCoordinate X k) =
      (v : ℝ) * h3ZornCoordinate X k₀ := by
    rw [Finset.sum_eq_single k₀]
    · simp [hs k₀]
    · intro k _ hk
      simp [hs k, hk]
    · intro h; exact absurd (Finset.mem_univ k₀) h
  rw [hsum]

private def clearARoot : Fin 6 → Fin 72
  | 0 => 10
  | 1 => 14
  | 2 => 17
  | 3 => 20
  | 4 => 22
  | 5 => 23

private def bumpARoot : Fin 6 → Fin 72
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2

private theorem clearARoot_lt_check :
    (List.finRange 6).all (fun i => decide ((clearARoot i).val < 24) && decide ((bumpARoot i).val < 24)) = true := by
  decide

private theorem clearARoot_row_check :
    (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (clearARoot i)) 3 k == 0) &&
      (sparseVal (e6RootSparse (clearARoot i)) ⟨4 + i.val, by omega⟩ k == if k.val = 3 then 1 else 0))) = true := by
  decide

private theorem clearARoot_prev_check :
    (List.finRange 6).all (fun i => (List.finRange 6).all (fun j =>
      if j.val < i.val then
        (List.finRange 27).all (fun k =>
          sparseVal (e6RootSparse (clearARoot i)) ⟨4 + j.val, by omega⟩ k == 0)
      else true)) = true := by
  decide

private theorem bumpARoot_row3_check :
    (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (bumpARoot i)) 3 k == if k.val = 4 + i.val then -1 else 0)) = true := by
  decide

private theorem d4_clear_a_mid_prefix :
    ∀ n : ℕ, n ≤ 6 → ∀ X : H3Zorn ℝ, zornCoord X.a 0 ≠ 0 →
      ∃ h ∈ d4Subgroup,
        zornCoord (h.1 X).a 0 = zornCoord X.a 0 ∧
        ∀ j : Fin 6, j.val < n → zornCoord (h.1 X).a ⟨1 + j.val, by omega⟩ = 0 := by
  intro n hn
  induction n with
  | zero =>
    intro X _
    exact ⟨1, d4Subgroup.one_mem, rfl, fun j hj => False.elim (Nat.not_lt_zero _ hj)⟩
  | succ m ih =>
    intro X ha0
    obtain ⟨h₁, hh₁, h0₁, hm₁⟩ := ih (Nat.le_of_succ_le hn) X ha0
    obtain ⟨X₁, hX₁⟩ : ∃ X₁, h₁.1 X = X₁ := ⟨_, rfl⟩
    rw [hX₁] at h0₁ hm₁
    have hX₁_a0 : zornCoord X₁.a 0 ≠ 0 := by rw [h0₁]; exact ha0
    let idx : Fin 6 := ⟨m, by omega⟩
    let r := clearARoot idx
    have hr24 : r.val < 24 := by
      have hc := clearARoot_lt_check
      simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
        decide_eq_true_eq] at hc
      exact (hc idx).1
    let t : ℝ := -(zornCoord X₁.a ⟨1 + m, by omega⟩) / zornCoord X₁.a 0
    have hg_mem : e6RootExp r t ∈ d4Subgroup := Subgroup.subset_closure ⟨(⟨r, hr24⟩, t), rfl⟩
    have hc_rows := clearARoot_row_check
    simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc_rows
    have hc_prev := clearARoot_prev_check
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc_prev
    have h0' : zornCoord ((e6RootExp r t).1 X₁).a 0 = zornCoord X₁.a 0 := by
      rw [← h3ZornCoord_a_eq]
      change h3ZornCoordinate ((e6RootExp r t).1 X₁) 3 = zornCoord X₁.a 0
      rw [rootExp_coord_unchanged r 3 t X₁ (fun k => (hc_rows idx k).1),
        show h3ZornCoordinate X₁ 3 = zornCoord X₁.a 0 from h3ZornCoord_a_eq X₁ 0]
    have hidx' : zornCoord ((e6RootExp r t).1 X₁).a ⟨1 + m, by omega⟩ = 0 := by
      rw [← h3ZornCoord_a_eq]
      have hs : ∀ k : Fin 27, sparseVal (e6RootSparse r) ⟨4 + idx.val, by omega⟩ k =
          if k = 3 then (1 : ℤ) else 0 := by
        intro k
        have h := (hc_rows idx k).2
        dsimp only [r]
        rw [h]; simp [Fin.ext_iff]
      have hcoord := rootExp_coord_add_single r ⟨4 + idx.val, by omega⟩ 3 1 t X₁ hs
      have hm_eq : (⟨3 + (⟨1 + m, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
          ⟨4 + idx.val, by omega⟩ := Fin.ext (by dsimp [idx]; omega)
      rw [hm_eq, hcoord, ← hm_eq, h3ZornCoord_a_eq,
        show h3ZornCoordinate X₁ 3 = zornCoord X₁.a 0 from h3ZornCoord_a_eq X₁ 0]
      simp only [Int.cast_one, one_mul, t]
      field_simp [hX₁_a0]
      ring
    refine ⟨e6RootExp r t * h₁, d4Subgroup.mul_mem hg_mem hh₁, ?_, ?_⟩
    · change zornCoord ((e6RootExp r t).1 (h₁.1 X)).a 0 = zornCoord X.a 0
      rw [hX₁, h0', h0₁]
    · intro j hj
      change zornCoord ((e6RootExp r t).1 (h₁.1 X)).a ⟨1 + j.val, by omega⟩ = 0
      rw [hX₁]
      by_cases hjm : j.val = m
      · have hjeq : (⟨1 + j.val, by omega⟩ : Fin 8) = ⟨1 + m, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hjeq, hidx']
      · have hjlt : j.val < m := by omega
        have hp := hc_prev idx j
        simp only [show j.val < idx.val from hjlt, ↓reduceIte] at hp
        simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hp
        have hj0 : zornCoord ((e6RootExp r t).1 X₁).a ⟨1 + j.val, by omega⟩ =
            zornCoord X₁.a ⟨1 + j.val, by omega⟩ := by
          let j' : Fin 8 := ⟨1 + j.val, by omega⟩
          have hm_eq : (⟨3 + j'.val, by omega⟩ : Fin 27) = ⟨4 + j.val, by omega⟩ :=
            Fin.ext (by dsimp [j']; omega)
          change zornCoord ((e6RootExp r t).1 X₁).a j' = zornCoord X₁.a j'
          rw [← h3ZornCoord_a_eq, hm_eq,
            rootExp_coord_unchanged r ⟨4 + j.val, by omega⟩ t X₁ hp,
            ← hm_eq, h3ZornCoord_a_eq]
        rw [hj0, hm₁ j hjlt]

private theorem d4_clear_a_mid (X : H3Zorn ℝ) :
    ∃ h ∈ d4Subgroup,
      (h.1 X).α₁ = X.α₁ ∧ (h.1 X).α₂ = X.α₂ ∧ (h.1 X).α₃ = X.α₃ ∧
      (∀ j : Fin 6, zornCoord (h.1 X).a ⟨1 + j.val, by omega⟩ = 0) ∧
      (X.a = 0 → (h.1 X).a = 0) := by
  by_cases ha0 : zornCoord X.a 0 ≠ 0
  · obtain ⟨h, hh, _, hj⟩ := d4_clear_a_mid_prefix 6 (le_refl 6) X ha0
    obtain ⟨h1, h2, h3, ha, _, _⟩ := d4Subgroup_preserves_blocks hh X
    exact ⟨h, hh, h1, h2, h3, fun j => hj j j.isLt, ha⟩
  · have ha00 : zornCoord X.a 0 = 0 := not_not.mp ha0
    by_cases hex : ∃ i : Fin 6, zornCoord X.a ⟨1 + i.val, by omega⟩ ≠ 0
    · obtain ⟨i, hi⟩ := hex
      let rb := bumpARoot i
      have hrb24 : rb.val < 24 := by
        have hc := clearARoot_lt_check
        simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
          decide_eq_true_eq] at hc
        exact (hc i).2
      have hgb : e6RootExp rb 1 ∈ d4Subgroup := Subgroup.subset_closure ⟨(⟨rb, hrb24⟩, 1), rfl⟩
      have hbrow := bumpARoot_row3_check
      simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hbrow
      have ha0' : zornCoord ((e6RootExp rb 1).1 X).a 0 ≠ 0 := by
        rw [← h3ZornCoord_a_eq]
        have hs : ∀ k : Fin 27, sparseVal (e6RootSparse rb) 3 k =
            if k = ⟨4 + i.val, by omega⟩ then (-1 : ℤ) else 0 := by
          intro k
          have h := hbrow i k
          dsimp only [rb]
          rw [h]; simp [Fin.ext_iff]
        change h3ZornCoordinate ((e6RootExp rb 1).1 X) 3 ≠ 0
        rw [rootExp_coord_add_single rb 3 ⟨4 + i.val, by omega⟩ (-1) 1 X hs]
        have h4eq : (⟨4 + i.val, by omega⟩ : Fin 27) =
            ⟨3 + (⟨1 + i.val, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [show h3ZornCoordinate X 3 = zornCoord X.a 0 from h3ZornCoord_a_eq X 0,
          h4eq, h3ZornCoord_a_eq, ha00]
        simpa using hi
      obtain ⟨X₁, hX₁⟩ : ∃ X₁, (e6RootExp rb 1).1 X = X₁ := ⟨_, rfl⟩
      rw [hX₁] at ha0'
      obtain ⟨h, hh, _, hj⟩ := d4_clear_a_mid_prefix 6 (le_refl 6) X₁ ha0'
      have hmul_mem := d4Subgroup.mul_mem hh hgb
      obtain ⟨h1, h2, h3, ha, _, _⟩ := d4Subgroup_preserves_blocks hmul_mem X
      refine ⟨h * e6RootExp rb 1, hmul_mem, h1, h2, h3, ?_, ha⟩
      intro j
      change zornCoord (h.1 ((e6RootExp rb 1).1 X)).a ⟨1 + j.val, by omega⟩ = 0
      rw [hX₁]
      exact hj j j.isLt
    · push Not at hex
      exact ⟨1, d4Subgroup.one_mem, rfl, rfl, rfl, hex, id⟩

private theorem w12_a_coords (X : H3Zorn ℝ) :
    zornCoord (w12.1 X).a 0 = -zornCoord X.a 7 ∧
    zornCoord (w12.1 X).a 7 = -zornCoord X.a 0 ∧
    (∀ j : Fin 6, zornCoord (w12.1 X).a ⟨1 + j.val, by omega⟩ = zornCoord X.a ⟨1 + j.val, by omega⟩) := by
  have hc0 : (List.finRange 27).all (fun k =>
      (sparseVal w12Sparse 3 k == if k.val = 10 then -1 else 0) &&
      (sparseVal w12Sparse 10 k == if k.val = 3 then -1 else 0)) = true := by decide
  have hcmid : (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      sparseVal w12Sparse ⟨4 + j.val, by omega⟩ k == if k.val = 4 + j.val then 1 else 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc0 hcmid
  refine ⟨?_, ?_, ?_⟩
  · rw [← h3ZornCoord_a_eq, h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w12_sparse]
    rw [Finset.sum_eq_single 10]
    · have h10 : h3ZornCoordinate X 10 = zornCoord X.a 7 := h3ZornCoord_a_eq X 7
      simp [(hc0 10).1, h10]
    · intro k _ hk
      have hne : k.val ≠ 10 := fun h => hk (Fin.ext h)
      simp [(hc0 k).1, hne]
    · intro h; exact absurd (Finset.mem_univ 10) h
  · rw [← h3ZornCoord_a_eq, h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w12_sparse]
    rw [Finset.sum_eq_single 3]
    · have h3 : h3ZornCoordinate X 3 = zornCoord X.a 0 := h3ZornCoord_a_eq X 0
      simp [(hc0 3).2, h3]
    · intro k _ hk
      have hne : k.val ≠ 3 := fun h => hk (Fin.ext h)
      simp [(hc0 k).2, hne]
    · intro h; exact absurd (Finset.mem_univ 3) h
  · intro j
    rw [← h3ZornCoord_a_eq]
    have hm_eq : (⟨3 + (⟨1 + j.val, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
        ⟨4 + j.val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hm_eq, h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w12_sparse]
    rw [Finset.sum_eq_single ⟨4 + j.val, by omega⟩]
    · have hjv := hcmid j ⟨4 + j.val, by omega⟩
      simp only [↓reduceIte] at hjv
      rw [hjv, Int.cast_one, one_mul, ← hm_eq, h3ZornCoord_a_eq]
    · intro k _ hk
      have hne : k.val ≠ 4 + j.val := fun h => hk (Fin.ext h)
      simp [hcmid j k, hne]
    · intro h; exact absurd (Finset.mem_univ _) h

private theorem f4Peirce_0_0_mul_eq :
    sparseToMat (sparseMul (e6RootSparse 24) (e6RootSparse 25)) = sparseToMat [(3, 10, 1)] := by
  exact sparseToMat_eq_of_sparseEq (by decide)

private theorem f4Peirce_0_0_check :
    (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 24) 0 k == if k.val = 10 then 1 else 0) &&
      (sparseVal (e6RootSparse 25) 0 k == 0) &&
      (sparseVal (e6RootSparse 24) 1 k == 0) &&
      (sparseVal (e6RootSparse 25) 1 k == if k.val = 10 then 1 else 0) &&
      (sparseVal (e6RootSparse 24) 2 k == 0) &&
      (sparseVal (e6RootSparse 25) 2 k == 0) &&
      (sparseVal (e6RootSparse 24) 3 k == if k.val = 1 then 1 else 0) &&
      (sparseVal (e6RootSparse 25) 3 k == if k.val = 0 then 1 else 0) &&
      (sparseVal (e6RootSparse 24) 10 k == 0) &&
      (sparseVal (e6RootSparse 25) 10 k == 0)) = true := by decide

private theorem f4Peirce_0_0_mid_check :
    (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 24) ⟨4 + j.val, by omega⟩ k == 0) &&
      (sparseVal (e6RootSparse 25) ⟨4 + j.val, by omega⟩ k == 0))) = true := by decide

private theorem f4Peirce_0_0_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((f4PeirceExp 0 0 t).1 X).α₁ = X.α₁ + t * zornCoord X.a 7 ∧
    ((f4PeirceExp 0 0 t).1 X).α₂ = X.α₂ - t * zornCoord X.a 7 ∧
    ((f4PeirceExp 0 0 t).1 X).α₃ = X.α₃ ∧
    zornCoord ((f4PeirceExp 0 0 t).1 X).a 0 =
      zornCoord X.a 0 + t * (X.α₂ - X.α₁) - t ^ 2 * zornCoord X.a 7 ∧
    zornCoord ((f4PeirceExp 0 0 t).1 X).a 7 = zornCoord X.a 7 ∧
    (∀ j : Fin 6, zornCoord ((f4PeirceExp 0 0 t).1 X).a ⟨1 + j.val, by omega⟩ =
      zornCoord X.a ⟨1 + j.val, by omega⟩) := by
  have hc := f4Peirce_0_0_check
  have hcm := f4Peirce_0_0_mid_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc hcm
  have hpm : ∀ m k : Fin 27, sparseVal (sparseMul (e6RootSparse 24) (e6RootSparse 25)) m k =
      if m = 3 ∧ k = 10 then 1 else 0 := by
    intro m k
    have hm := congrFun (congrFun f4Peirce_0_0_mul_eq m) k
    change sparseVal (sparseMul (e6RootSparse 24) (e6RootSparse 25)) m k =
      sparseVal [(3, 10, 1)] m k at hm
    rw [hm]
    by_cases hmk : m = 3 ∧ k = 10
    · rcases hmk with ⟨rfl, rfl⟩; decide
    · simp only [hmk, ↓reduceIte, sparseVal_cons, sparseVal_nil, add_zero]
      have hb : ((3 : Fin 27) == m && (10 : Fin 27) == k) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        exact not_and_or.mp fun ⟨h1, h2⟩ => hmk ⟨h1.symm, h2.symm⟩
      simp [hb]
  have hf : f4PeirceExp 0 0 t = e6RootExp 24 t * e6RootExp 25 (-t) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((f4PeirceExp 0 0 t).1 X) 0 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_zero_eq]
    rw [Finset.sum_eq_single 10 (fun k _ hk => by
      have hne : k.val ≠ 10 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.1.1.1.1.1.1, hne]) (fun h => absurd (Finset.mem_univ 10) h)]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 25) 0 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 24) (e6RootSparse 25)) 0 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 0 k]
    rw [hs2, hs3, (hc 10).1.1.1.1.1.1.1.1.1, show h3ZornCoordinate X 10 = zornCoord X.a 7 from h3ZornCoord_a_eq X 7]
    simp
  · change h3ZornCoordinate ((f4PeirceExp 0 0 t).1 X) 1 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_one_eq]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 24) 1 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 24) (e6RootSparse 25)) 1 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 1 k]
    rw [hs1, hs3, Finset.sum_eq_single 10 (fun k _ hk => by
      have hne : k.val ≠ 10 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.1.1.1.2, hne]) (fun h => absurd (Finset.mem_univ 10) h)]
    rw [(hc 10).1.1.1.1.1.1.2, show h3ZornCoordinate X 10 = zornCoord X.a 7 from h3ZornCoord_a_eq X 7]
    simp; ring
  · change h3ZornCoordinate ((f4PeirceExp 0 0 t).1 X) 2 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_two_eq]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 24) 2 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.2]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 25) 2 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 24) (e6RootSparse 25)) 2 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 2 k]
    rw [hs1, hs2, hs3]; ring
  · rw [← h3ZornCoord_a_eq]
    change h3ZornCoordinate ((f4PeirceExp 0 0 t).1 X) 3 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul]
    rw [Finset.sum_eq_single 1 (fun k _ hk => by
      have hne : k.val ≠ 1 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.2, hne]) (fun h => absurd (Finset.mem_univ 1) h)]
    rw [Finset.sum_eq_single 0 (fun k _ hk => by
      have hne : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.2, hne]) (fun h => absurd (Finset.mem_univ 0) h)]
    rw [Finset.sum_eq_single 10 (fun k _ hk => by simp [hpm 3 k, hk])
      (fun h => absurd (Finset.mem_univ 10) h)]
    rw [(hc 1).1.1.1.2, (hc 0).1.1.2, hpm 3 10]
    rw [show h3ZornCoordinate X 3 = zornCoord X.a 0 from h3ZornCoord_a_eq X 0,
      show h3ZornCoordinate X 1 = X.α₂ from rfl, show h3ZornCoordinate X 0 = X.α₁ from rfl,
      show h3ZornCoordinate X 10 = zornCoord X.a 7 from h3ZornCoord_a_eq X 7]
    simp; ring
  · rw [← h3ZornCoord_a_eq]
    change h3ZornCoordinate ((f4PeirceExp 0 0 t).1 X) 10 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 24) 10 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.2]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 25) 10 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 24) (e6RootSparse 25)) 10 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 10 k]
    rw [hs1, hs2, hs3, show h3ZornCoordinate X 10 = zornCoord X.a 7 from h3ZornCoord_a_eq X 7]
    ring
  · intro j
    let j' : Fin 8 := ⟨1 + j.val, by omega⟩
    have hm_eq : (⟨3 + j'.val, by omega⟩ : Fin 27) = ⟨4 + j.val, by omega⟩ :=
      Fin.ext (by dsimp [j']; omega)
    change zornCoord ((f4PeirceExp 0 0 t).1 X).a j' = zornCoord X.a j'
    rw [← h3ZornCoord_a_eq, hm_eq, hf, h3ZornCoordinate_e6RootExp_mul]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 24) ⟨4 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hcm j k).1]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 25) ⟨4 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hcm j k).2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 24) (e6RootSparse 25)) ⟨4 + j.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        have hne : (⟨4 + j.val, by omega⟩ : Fin 27) ≠ 3 := fun h => by
          have := congrArg Fin.val h; dsimp at this; omega
        simp [hpm ⟨4 + j.val, by omega⟩ k, hne]
    rw [hs1, hs2, hs3, ← hm_eq, h3ZornCoord_a_eq]; ring

private theorem f4Peirce_0_7_mul_eq :
    sparseToMat (sparseMul (e6RootSparse 38) (e6RootSparse 39)) = sparseToMat [(10, 3, 1)] := by
  exact sparseToMat_eq_of_sparseEq (by decide)

private theorem f4Peirce_0_7_check :
    (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 38) 0 k == if k.val = 3 then 1 else 0) &&
      (sparseVal (e6RootSparse 39) 0 k == 0) &&
      (sparseVal (e6RootSparse 38) 1 k == 0) &&
      (sparseVal (e6RootSparse 39) 1 k == if k.val = 3 then 1 else 0) &&
      (sparseVal (e6RootSparse 38) 2 k == 0) &&
      (sparseVal (e6RootSparse 39) 2 k == 0) &&
      (sparseVal (e6RootSparse 38) 3 k == 0) &&
      (sparseVal (e6RootSparse 39) 3 k == 0) &&
      (sparseVal (e6RootSparse 38) 10 k == if k.val = 1 then 1 else 0) &&
      (sparseVal (e6RootSparse 39) 10 k == if k.val = 0 then 1 else 0)) = true := by decide

private theorem f4Peirce_0_7_mid_check :
    (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 38) ⟨4 + j.val, by omega⟩ k == 0) &&
      (sparseVal (e6RootSparse 39) ⟨4 + j.val, by omega⟩ k == 0))) = true := by decide

private theorem f4Peirce_0_7_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((f4PeirceExp 0 7 t).1 X).α₁ = X.α₁ + t * zornCoord X.a 0 ∧
    ((f4PeirceExp 0 7 t).1 X).α₂ = X.α₂ - t * zornCoord X.a 0 ∧
    ((f4PeirceExp 0 7 t).1 X).α₃ = X.α₃ ∧
    zornCoord ((f4PeirceExp 0 7 t).1 X).a 0 = zornCoord X.a 0 ∧
    zornCoord ((f4PeirceExp 0 7 t).1 X).a 7 =
      zornCoord X.a 7 + t * (X.α₂ - X.α₁) - t ^ 2 * zornCoord X.a 0 ∧
    (∀ j : Fin 6, zornCoord ((f4PeirceExp 0 7 t).1 X).a ⟨1 + j.val, by omega⟩ =
      zornCoord X.a ⟨1 + j.val, by omega⟩) := by
  have hc := f4Peirce_0_7_check
  have hcm := f4Peirce_0_7_mid_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc hcm
  have hpm : ∀ m k : Fin 27, sparseVal (sparseMul (e6RootSparse 38) (e6RootSparse 39)) m k =
      if m = 10 ∧ k = 3 then 1 else 0 := by
    intro m k
    have hm := congrFun (congrFun f4Peirce_0_7_mul_eq m) k
    change sparseVal (sparseMul (e6RootSparse 38) (e6RootSparse 39)) m k =
      sparseVal [(10, 3, 1)] m k at hm
    rw [hm]
    by_cases hmk : m = 10 ∧ k = 3
    · rcases hmk with ⟨rfl, rfl⟩; decide
    · simp only [hmk, ↓reduceIte, sparseVal_cons, sparseVal_nil, add_zero]
      have hb : ((10 : Fin 27) == m && (3 : Fin 27) == k) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        exact not_and_or.mp fun ⟨h1, h2⟩ => hmk ⟨h1.symm, h2.symm⟩
      simp [hb]
  have hf : f4PeirceExp 0 7 t = e6RootExp 38 t * e6RootExp 39 (-t) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((f4PeirceExp 0 7 t).1 X) 0 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_zero_eq]
    rw [Finset.sum_eq_single 3 (fun k _ hk => by
      have hne : k.val ≠ 3 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.1.1.1.1.1.1, hne]) (fun h => absurd (Finset.mem_univ 3) h)]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 39) 0 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 38) (e6RootSparse 39)) 0 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 0 k]
    rw [hs2, hs3, (hc 3).1.1.1.1.1.1.1.1.1, show h3ZornCoordinate X 3 = zornCoord X.a 0 from h3ZornCoord_a_eq X 0]
    simp
  · change h3ZornCoordinate ((f4PeirceExp 0 7 t).1 X) 1 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_one_eq]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 38) 1 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 38) (e6RootSparse 39)) 1 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 1 k]
    rw [hs1, hs3, Finset.sum_eq_single 3 (fun k _ hk => by
      have hne : k.val ≠ 3 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.1.1.1.2, hne]) (fun h => absurd (Finset.mem_univ 3) h)]
    rw [(hc 3).1.1.1.1.1.1.2, show h3ZornCoordinate X 3 = zornCoord X.a 0 from h3ZornCoord_a_eq X 0]
    simp; ring
  · change h3ZornCoordinate ((f4PeirceExp 0 7 t).1 X) 2 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_two_eq]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 38) 2 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.2]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 39) 2 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 38) (e6RootSparse 39)) 2 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 2 k]
    rw [hs1, hs2, hs3]; ring
  · rw [← h3ZornCoord_a_eq]
    change h3ZornCoordinate ((f4PeirceExp 0 7 t).1 X) 3 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 38) 3 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.2]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 39) 3 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 38) (e6RootSparse 39)) 3 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 3 k]
    rw [hs1, hs2, hs3, show h3ZornCoordinate X 3 = zornCoord X.a 0 from h3ZornCoord_a_eq X 0]
    ring
  · rw [← h3ZornCoord_a_eq]
    change h3ZornCoordinate ((f4PeirceExp 0 7 t).1 X) 10 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul]
    rw [Finset.sum_eq_single 1 (fun k _ hk => by
      have hne : k.val ≠ 1 := fun h => hk (Fin.ext h)
      simp [(hc k).1.2, hne]) (fun h => absurd (Finset.mem_univ 1) h)]
    rw [Finset.sum_eq_single 0 (fun k _ hk => by
      have hne : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [(hc k).2, hne]) (fun h => absurd (Finset.mem_univ 0) h)]
    rw [Finset.sum_eq_single 3 (fun k _ hk => by simp [hpm 10 k, hk])
      (fun h => absurd (Finset.mem_univ 3) h)]
    rw [(hc 1).1.2, (hc 0).2, hpm 10 3]
    rw [show h3ZornCoordinate X 10 = zornCoord X.a 7 from h3ZornCoord_a_eq X 7,
      show h3ZornCoordinate X 1 = X.α₂ from rfl, show h3ZornCoordinate X 0 = X.α₁ from rfl,
      show h3ZornCoordinate X 3 = zornCoord X.a 0 from h3ZornCoord_a_eq X 0]
    simp; ring
  · intro j
    let j' : Fin 8 := ⟨1 + j.val, by omega⟩
    have hm_eq : (⟨3 + j'.val, by omega⟩ : Fin 27) = ⟨4 + j.val, by omega⟩ :=
      Fin.ext (by dsimp [j']; omega)
    change zornCoord ((f4PeirceExp 0 7 t).1 X).a j' = zornCoord X.a j'
    rw [← h3ZornCoord_a_eq, hm_eq, hf, h3ZornCoordinate_e6RootExp_mul]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 38) ⟨4 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hcm j k).1]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 39) ⟨4 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hcm j k).2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 38) (e6RootSparse 39)) ⟨4 + j.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        have hne : (⟨4 + j.val, by omega⟩ : Fin 27) ≠ 10 := fun h => by
          have := congrArg Fin.val h; dsimp at this; omega
        simp [hpm ⟨4 + j.val, by omega⟩ k, hne]
    rw [hs1, hs2, hs3, ← hm_eq, h3ZornCoord_a_eq]; ring

private theorem zorn_norm_of_mid_zero {u : ZornVectorMatrix ℝ}
    (hu : ∀ j : Fin 6, zornCoord u ⟨1 + j.val, by omega⟩ = 0) :
    ZornVectorMatrix.norm u = zornCoord u 0 * zornCoord u 7 := by
  have h1 : u.v 0 = 0 := hu 0
  have h2 : u.v 1 = 0 := hu 1
  have h3 : u.v 2 = 0 := hu 2
  have h4 : u.w 0 = 0 := hu 3
  have h5 : u.w 1 = 0 := hu 4
  have h6 : u.w 2 = 0 := hu 5
  simp [ZornVectorMatrix.norm, ZornVec3.dot, Fin.sum_univ_three, zornCoord, h1, h2, h3, h4, h5, h6]

private theorem f4InChevalley_preserves_isRankOneIdem {h : h3zornReducedStructureGroup}
    (hh : h ∈ e6F4InChevalley) {e : H3Zorn ℝ} (he : isRankOneIdem e) :
    isRankOneIdem (h.1 e) := by
  let A : H3ZornJordanAut := h3zornJordanAutOfReducedStructure h hh.2
  have hA : ∀ X : H3Zorn ℝ, A X = h.1 X := fun _ => rfl
  rw [← hA e]
  exact jordanAut_preserves_isRankOneIdem A he

private theorem isRankOneIdem_norm_eq {e : H3Zorn ℝ} (he : isRankOneIdem e) :
    e.α₁ + e.α₂ + e.α₃ = 1 ∧
    e.α₂ * e.α₃ = ZornVectorMatrix.norm e.b ∧
    e.α₁ * e.α₃ = ZornVectorMatrix.norm e.c ∧
    e.α₁ * e.α₂ = ZornVectorMatrix.norm e.a := by
  have htr : e.α₁ + e.α₂ + e.α₃ = 1 := he.2.1
  have haq := he.2.2
  have h1 := congrArg H3Zorn.α₁ haq
  have h2 := congrArg H3Zorn.α₂ haq
  have h3 := congrArg H3Zorn.α₃ haq
  change e.α₂ * e.α₃ - ZornVectorMatrix.norm e.b = 0 at h1
  change e.α₁ * e.α₃ - ZornVectorMatrix.norm e.c = 0 at h2
  change e.α₁ * e.α₂ - ZornVectorMatrix.norm e.a = 0 at h3
  exact ⟨htr, sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3⟩

private theorem isRankOneIdem_b_zero_of_a_zero {e : H3Zorn ℝ} (he : isRankOneIdem e)
    (ha : e.a = 0) (hα₁ : e.α₁ ≠ 0) : e.b = 0 := by
  have hb0 := congrArg H3Zorn.b he.2.2
  change ZornVectorMatrix.sub (ZornVectorMatrix.mul (ZornVectorMatrix.conj e.a) (ZornVectorMatrix.conj e.c))
      (ZornVectorMatrix.smul e.α₁ e.b) = 0 at hb0
  have hcz : ZornVectorMatrix.conj (0 : ZornVectorMatrix ℝ) = 0 := by
    ext i <;> simp [ZornVectorMatrix.conj, ZornVectorMatrix.zero]
  have hmz : ∀ y : ZornVectorMatrix ℝ, ZornVectorMatrix.mul (0 : ZornVectorMatrix ℝ) y = 0 := fun y => by
    ext i <;> simp [ZornVectorMatrix.mul, ZornVectorMatrix.zero]
  rw [ha, hcz, hmz] at hb0
  have hsb : ∀ i : Fin 8, zornCoord (ZornVectorMatrix.sub (0 : ZornVectorMatrix ℝ)
      (ZornVectorMatrix.smul e.α₁ e.b)) i = -(e.α₁ * zornCoord e.b i) := by
    intro i; fin_cases i <;> simp [ZornVectorMatrix.sub, ZornVectorMatrix.smul,
      ZornVectorMatrix.zero, ZornVectorMatrix.neg, zornCoord]
  apply zorn_eq_of_zornCoord_eq
  intro i
  have hci := congrArg (fun u => zornCoord u i) hb0
  change zornCoord (ZornVectorMatrix.sub (0 : ZornVectorMatrix ℝ) (ZornVectorMatrix.smul e.α₁ e.b)) i =
    zornCoord (0 : ZornVectorMatrix ℝ) i at hci
  rw [hsb i] at hci
  have hz0 : zornCoord (0 : ZornVectorMatrix ℝ) i = 0 := by fin_cases i <;> rfl
  rw [hz0] at hci
  have hmul0 : e.α₁ * zornCoord e.b i = 0 := neg_eq_zero.mp hci
  have hi0 := (mul_eq_zero.mp hmul0).resolve_left hα₁
  rw [hi0, hz0]

private theorem scalar_peirce_kill_a7 (α₁ α₂ a₀ a₇ : ℝ) (ha₀ : a₀ ≠ 0) (hn : α₁ * α₂ = a₀ * a₇) :
    α₁ + (α₂ / a₀) * a₀ = α₁ + α₂ ∧
    α₂ - (α₂ / a₀) * a₀ = 0 ∧
    a₇ + (α₂ / a₀) * (α₂ - α₁) - (α₂ / a₀) ^ 2 * a₀ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · field_simp [ha₀]
  · field_simp [ha₀]; ring
  · have hn' : a₇ = α₁ * α₂ / a₀ := by
      field_simp [ha₀]
      linarith [hn]
    rw [hn']
    field_simp [ha₀]
    ring

private theorem scalar_peirce_kill_a0 (a₀ d : ℝ) (hd : d ≠ 0) :
    a₀ + (-a₀ / d) * d = 0 := by
  field_simp [hd]
  ring

private theorem f4_clear_a_of_mid_zero_a0_ne_zero {e : H3Zorn ℝ} (he : isRankOneIdem e)
    (hmid : ∀ j : Fin 6, zornCoord e.a ⟨1 + j.val, by omega⟩ = 0) (ha₀ : zornCoord e.a 0 ≠ 0)
    (hsum : e.α₁ + e.α₂ ≠ 0) :
    ∃ h ∈ e6F4InChevalley, (h.1 e).a = 0 ∧ (h.1 e).α₁ = e.α₁ + e.α₂ ∧ (h.1 e).α₂ = 0 := by
  let t₁ : ℝ := e.α₂ / zornCoord e.a 0
  let h₁ := f4PeirceExp 0 7 t₁
  have hh₁ : h₁ ∈ e6F4InChevalley := f4PeirceExp_mem_f4 0 7 t₁
  obtain ⟨h1a, h2a, _, h0a, h7a, hmida⟩ := f4Peirce_0_7_coords t₁ e
  have hn : e.α₁ * e.α₂ = zornCoord e.a 0 * zornCoord e.a 7 := by
    rw [(isRankOneIdem_norm_eq he).2.2.2, zorn_norm_of_mid_zero hmid]
  obtain ⟨hs1, hs2, hs7⟩ := scalar_peirce_kill_a7 e.α₁ e.α₂ (zornCoord e.a 0) (zornCoord e.a 7) ha₀ hn
  obtain ⟨e₁, he₁⟩ : ∃ e₁, h₁.1 e = e₁ := ⟨_, rfl⟩
  rw [he₁] at h1a h2a h0a h7a hmida
  have he₁_1 : e₁.α₁ = e.α₁ + e.α₂ := h1a.trans hs1
  have he₁_2 : e₁.α₂ = 0 := h2a.trans hs2
  have he₁_7 : zornCoord e₁.a 7 = 0 := h7a.trans hs7
  have hd : e₁.α₂ - e₁.α₁ ≠ 0 := by
    rw [he₁_2, he₁_1, zero_sub]
    exact neg_ne_zero.mpr hsum
  let t₂ : ℝ := -(zornCoord e₁.a 0) / (e₁.α₂ - e₁.α₁)
  let h₂ := f4PeirceExp 0 0 t₂
  have hh₂ : h₂ ∈ e6F4InChevalley := f4PeirceExp_mem_f4 0 0 t₂
  obtain ⟨h1b, h2b, _, h0b, h7b, hmidb⟩ := f4Peirce_0_0_coords (-(zornCoord e₁.a 0) / (e₁.α₂ - e₁.α₁)) e₁
  simp only [he₁_7, mul_zero, add_zero, sub_zero] at h1b h2b h0b h7b
  have ha0'' : zornCoord ((f4PeirceExp 0 0 (-(zornCoord e₁.a 0) / (e₁.α₂ - e₁.α₁))).1 e₁).a 0 = 0 :=
    h0b.trans (scalar_peirce_kill_a0 (zornCoord e₁.a 0) _ hd)
  have ha'' : ((f4PeirceExp 0 0 (-(zornCoord e₁.a 0) / (e₁.α₂ - e₁.α₁))).1 e₁).a = 0 := by
    rw [← zornCoord_eq_zero_iff]
    intro j
    fin_cases j <;> dsimp
    · exact ha0''
    · exact (hmidb 0).trans ((hmida 0).trans (hmid 0))
    · exact (hmidb 1).trans ((hmida 1).trans (hmid 1))
    · exact (hmidb 2).trans ((hmida 2).trans (hmid 2))
    · exact (hmidb 3).trans ((hmida 3).trans (hmid 3))
    · exact (hmidb 4).trans ((hmida 4).trans (hmid 4))
    · exact (hmidb 5).trans ((hmida 5).trans (hmid 5))
    · exact h7b
  have hmul : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Y : H3Zorn ℝ),
      (g₁ * g₂).1 Y = g₁.1 (g₂.1 Y) := fun _ _ _ => rfl
  refine ⟨f4PeirceExp 0 0 (-(zornCoord e₁.a 0) / (e₁.α₂ - e₁.α₁)) * f4PeirceExp 0 7 t₁,
    e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 0 0 _) hh₁, ?_, ?_, ?_⟩
  · rw [hmul, he₁]; exact ha''
  · rw [hmul, he₁, h1b, he₁_1]
  · rw [hmul, he₁, h2b, he₁_2]

private theorem f4_clear_a_of_alpha1_one_alpha2_zero {e : H3Zorn ℝ} (he : isRankOneIdem e)
    (h1 : e.α₁ = 1) (h2 : e.α₂ = 0) :
    ∃ h ∈ e6F4InChevalley, (h.1 e).a = 0 ∧ (h.1 e).α₁ = 1 ∧ (h.1 e).α₂ = 0 := by
  obtain ⟨hd, hhd, hd1, hd2, _, hmid, _⟩ := d4_clear_a_mid e
  have hhd_f4 : hd ∈ e6F4InChevalley := d4Subgroup_le_f4InChevalley hhd
  obtain ⟨e₁, he₁⟩ : ∃ e₁, hd.1 e = e₁ := ⟨_, rfl⟩
  rw [he₁] at hd1 hd2 hmid
  have he₁_1 : e₁.α₁ = 1 := hd1.trans h1
  have he₁_2 : e₁.α₂ = 0 := hd2.trans h2
  have he₁_idem : isRankOneIdem e₁ := he₁ ▸ f4InChevalley_preserves_isRankOneIdem hhd_f4 he
  have hprod0 : zornCoord e₁.a 0 * zornCoord e₁.a 7 = 0 := by
    rw [← zorn_norm_of_mid_zero hmid, ← (isRankOneIdem_norm_eq he₁_idem).2.2.2, he₁_1, he₁_2, mul_zero]
  have hmul : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Y : H3Zorn ℝ),
      (g₁ * g₂).1 Y = g₁.1 (g₂.1 Y) := fun _ _ _ => rfl
  by_cases ha0 : zornCoord e₁.a 0 = 0
  · by_cases ha7 : zornCoord e₁.a 7 = 0
    · refine ⟨hd, hhd_f4, ?_, ?_, ?_⟩
      · rw [he₁, ← zornCoord_eq_zero_iff]; intro j
        fin_cases j <;> dsimp
        · exact ha0
        · exact hmid 0
        · exact hmid 1
        · exact hmid 2
        · exact hmid 3
        · exact hmid 4
        · exact hmid 5
        · exact ha7
      · rw [he₁]; exact he₁_1
      · rw [he₁]; exact he₁_2
    · obtain ⟨w1, w2, _⟩ := w12_diag_coords e₁
      obtain ⟨wa0, wa7, wamid⟩ := w12_a_coords e₁
      obtain ⟨e₂, he₂⟩ : ∃ e₂, w12.1 e₁ = e₂ := ⟨_, rfl⟩
      rw [he₂] at w1 w2 wa0 wa7 wamid
      have he₂_1 : e₂.α₁ = 0 := w1.trans he₁_2
      have he₂_2 : e₂.α₂ = 1 := w2.trans he₁_1
      have he₂_7 : zornCoord e₂.a 7 = 0 := by rw [wa7, ha0, neg_zero]
      obtain ⟨h1b, h2b, _, h0b, h7b, hmidb⟩ := f4Peirce_0_0_coords (-(zornCoord e₂.a 0)) e₂
      simp only [he₂_7, mul_zero, add_zero, sub_zero, he₂_2, he₂_1] at h1b h2b h0b h7b
      have he₃_a : ((f4PeirceExp 0 0 (-(zornCoord e₂.a 0))).1 e₂).a = 0 := by
        rw [← zornCoord_eq_zero_iff]; intro j
        fin_cases j <;> dsimp
        · rw [h0b]; ring
        · exact (hmidb 0).trans ((wamid 0).trans (hmid 0))
        · exact (hmidb 1).trans ((wamid 1).trans (hmid 1))
        · exact (hmidb 2).trans ((wamid 2).trans (hmid 2))
        · exact (hmidb 3).trans ((wamid 3).trans (hmid 3))
        · exact (hmidb 4).trans ((wamid 4).trans (hmid 4))
        · exact (hmidb 5).trans ((wamid 5).trans (hmid 5))
        · exact h7b
      obtain ⟨e₃, he₃⟩ : ∃ e₃, (f4PeirceExp 0 0 (-(zornCoord e₂.a 0))).1 e₂ = e₃ := ⟨_, rfl⟩
      rw [he₃] at h1b h2b he₃_a
      obtain ⟨w1', w2', _⟩ := w12_diag_coords e₃
      obtain ⟨wa0', wa7', wamid'⟩ := w12_a_coords e₃
      have hfin_a : (w12.1 e₃).a = 0 := by
        have hcz := (zornCoord_eq_zero_iff e₃.a).mpr he₃_a
        rw [← zornCoord_eq_zero_iff]; intro j
        fin_cases j <;> dsimp
        · rw [wa0', hcz 7, neg_zero]
        · exact (wamid' 0).trans (hcz 1)
        · exact (wamid' 1).trans (hcz 2)
        · exact (wamid' 2).trans (hcz 3)
        · exact (wamid' 3).trans (hcz 4)
        · exact (wamid' 4).trans (hcz 5)
        · exact (wamid' 5).trans (hcz 6)
        · rw [wa7', hcz 0, neg_zero]
      refine ⟨w12 * f4PeirceExp 0 0 (-(zornCoord e₂.a 0)) * w12 * hd,
        e6F4InChevalley.mul_mem
          (e6F4InChevalley.mul_mem
            (e6F4InChevalley.mul_mem w12_mem_f4 (f4PeirceExp_mem_f4 0 0 _)) w12_mem_f4) hhd_f4, ?_, ?_, ?_⟩
      · rw [hmul, hmul, hmul, he₁, he₂, he₃]; exact hfin_a
      · rw [hmul, hmul, hmul, he₁, he₂, he₃, w1', h2b]
      · rw [hmul, hmul, hmul, he₁, he₂, he₃, w2', h1b]
  · have ha7 : zornCoord e₁.a 7 = 0 := (mul_eq_zero.mp hprod0).resolve_left ha0
    obtain ⟨h1b, h2b, _, h0b, h7b, hmidb⟩ := f4Peirce_0_0_coords (zornCoord e₁.a 0) e₁
    simp only [ha7, mul_zero, add_zero, sub_zero, he₁_2, he₁_1] at h1b h2b h0b h7b
    have ha'' : ((f4PeirceExp 0 0 (zornCoord e₁.a 0)).1 e₁).a = 0 := by
      rw [← zornCoord_eq_zero_iff]; intro j
      fin_cases j <;> dsimp
      · rw [h0b]; ring
      · exact (hmidb 0).trans (hmid 0)
      · exact (hmidb 1).trans (hmid 1)
      · exact (hmidb 2).trans (hmid 2)
      · exact (hmidb 3).trans (hmid 3)
      · exact (hmidb 4).trans (hmid 4)
      · exact (hmidb 5).trans (hmid 5)
      · exact h7b
    refine ⟨f4PeirceExp 0 0 (zornCoord e₁.a 0) * hd,
      e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 0 0 _) hhd_f4, ?_, ?_, ?_⟩
    · rw [hmul, he₁]; exact ha''
    · rw [hmul, he₁]; exact h1b
    · rw [hmul, he₁]; exact h2b

private theorem f4_clear_a_and_alpha2_nonzero_alpha1 {e : H3Zorn ℝ} (he : isRankOneIdem e) :
    ∃ h ∈ e6F4InChevalley, (h.1 e).a = 0 ∧ (h.1 e).α₂ = 0 ∧ (h.1 e).α₁ ≠ 0 := by
  obtain ⟨hd, hhd, _, _, _, hmid, _⟩ := d4_clear_a_mid e
  have hhd_f4 : hd ∈ e6F4InChevalley := d4Subgroup_le_f4InChevalley hhd
  obtain ⟨e₁, he₁⟩ : ∃ e₁, hd.1 e = e₁ := ⟨_, rfl⟩
  rw [he₁] at hmid
  have he₁_idem : isRankOneIdem e₁ := he₁ ▸ f4InChevalley_preserves_isRankOneIdem hhd_f4 he
  have hmul : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Y : H3Zorn ℝ),
      (g₁ * g₂).1 Y = g₁.1 (g₂.1 Y) := fun _ _ _ => rfl
  have hStepA : ∃ g ∈ e6F4InChevalley, (g.1 e₁).a = 0 := by
    by_cases ha0 : zornCoord e₁.a 0 = 0
    · by_cases ha7 : zornCoord e₁.a 7 = 0
      · refine ⟨1, e6F4InChevalley.one_mem, ?_⟩
        change e₁.a = 0
        rw [← zornCoord_eq_zero_iff]; intro j
        fin_cases j <;> dsimp
        · exact ha0
        · exact hmid 0
        · exact hmid 1
        · exact hmid 2
        · exact hmid 3
        · exact hmid 4
        · exact hmid 5
        · exact ha7
      · obtain ⟨_, _, _⟩ := w12_diag_coords e₁
        obtain ⟨wa0, _, wamid⟩ := w12_a_coords e₁
        obtain ⟨e₂, he₂⟩ : ∃ e₂, w12.1 e₁ = e₂ := ⟨_, rfl⟩
        rw [he₂] at wa0 wamid
        have he₂_idem : isRankOneIdem e₂ := he₂ ▸ f4InChevalley_preserves_isRankOneIdem w12_mem_f4 he₁_idem
        have he₂_mid : ∀ j : Fin 6, zornCoord e₂.a ⟨1 + j.val, by omega⟩ = 0 :=
          fun j => (wamid j).trans (hmid j)
        have he₂_a0 : zornCoord e₂.a 0 ≠ 0 := by rw [wa0]; exact neg_ne_zero.mpr ha7
        by_cases hsum : e₂.α₁ + e₂.α₂ ≠ 0
        · obtain ⟨h', hh', ha', _, _⟩ := f4_clear_a_of_mid_zero_a0_ne_zero he₂_idem he₂_mid he₂_a0 hsum
          exact ⟨h' * w12, e6F4InChevalley.mul_mem hh' w12_mem_f4, by rw [hmul, he₂]; exact ha'⟩
        · have hsum0 : e₂.α₁ + e₂.α₂ = 0 := not_not.mp hsum
          obtain ⟨h1a, h2a, h3a, _, _, _⟩ := f4Peirce_0_7_coords (e₂.α₂ / zornCoord e₂.a 0) e₂
          obtain ⟨e₃, he₃⟩ : ∃ e₃, (f4PeirceExp 0 7 (e₂.α₂ / zornCoord e₂.a 0)).1 e₂ = e₃ := ⟨_, rfl⟩
          rw [he₃] at h1a h2a h3a
          have he₃_idem : isRankOneIdem e₃ :=
            he₃ ▸ f4InChevalley_preserves_isRankOneIdem (f4PeirceExp_mem_f4 0 7 _) he₂_idem
          have he₃_3 : e₃.α₃ = 1 := by
            have htr := (isRankOneIdem_norm_eq he₃_idem).1
            have hsum3 : e₃.α₁ + e₃.α₂ = 0 := by
              rw [h1a, h2a]; field_simp [he₂_a0]; linarith [hsum0]
            linarith [htr, hsum3]
          obtain ⟨w21, w22, _⟩ := w23_diag_coords e₃
          obtain ⟨e₄, he₄⟩ : ∃ e₄, w23.1 e₃ = e₄ := ⟨_, rfl⟩
          rw [he₄] at w21 w22
          have he₄_idem : isRankOneIdem e₄ := he₄ ▸ f4InChevalley_preserves_isRankOneIdem w23_mem_f4 he₃_idem
          have he₄_2 : e₄.α₂ = 1 := w22.trans he₃_3
          have he₄_1 : e₄.α₁ = 0 := by
            rw [w21, h1a]; field_simp [he₂_a0]; exact hsum0
          obtain ⟨w31d, w32d, _⟩ := w12_diag_coords e₄
          obtain ⟨e₅, he₅⟩ : ∃ e₅, w12.1 e₄ = e₅ := ⟨_, rfl⟩
          rw [he₅] at w31d w32d
          have he₅_idem : isRankOneIdem e₅ := he₅ ▸ f4InChevalley_preserves_isRankOneIdem w12_mem_f4 he₄_idem
          obtain ⟨hc, hhc, hac, _, _⟩ :=
            f4_clear_a_of_alpha1_one_alpha2_zero he₅_idem (w31d.trans he₄_2) (w32d.trans he₄_1)
          refine ⟨hc * w12 * w23 * f4PeirceExp 0 7 (e₂.α₂ / zornCoord e₂.a 0) * w12,
            e6F4InChevalley.mul_mem
              (e6F4InChevalley.mul_mem
                (e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem hhc w12_mem_f4) w23_mem_f4)
                (f4PeirceExp_mem_f4 0 7 _)) w12_mem_f4, ?_⟩
          rw [hmul, hmul, hmul, hmul, he₂, he₃, he₄, he₅]; exact hac
    · by_cases hsum : e₁.α₁ + e₁.α₂ ≠ 0
      · obtain ⟨h', hh', ha', _, _⟩ := f4_clear_a_of_mid_zero_a0_ne_zero he₁_idem hmid ha0 hsum
        exact ⟨h', hh', ha'⟩
      · have hsum0 : e₁.α₁ + e₁.α₂ = 0 := not_not.mp hsum
        obtain ⟨h1a, h2a, h3a, _, _, _⟩ := f4Peirce_0_7_coords (e₁.α₂ / zornCoord e₁.a 0) e₁
        obtain ⟨e₃, he₃⟩ : ∃ e₃, (f4PeirceExp 0 7 (e₁.α₂ / zornCoord e₁.a 0)).1 e₁ = e₃ := ⟨_, rfl⟩
        rw [he₃] at h1a h2a h3a
        have he₃_idem : isRankOneIdem e₃ :=
          he₃ ▸ f4InChevalley_preserves_isRankOneIdem (f4PeirceExp_mem_f4 0 7 _) he₁_idem
        have he₃_3 : e₃.α₃ = 1 := by
          have htr := (isRankOneIdem_norm_eq he₃_idem).1
          have hsum3 : e₃.α₁ + e₃.α₂ = 0 := by
            rw [h1a, h2a]; field_simp [ha0]; linarith [hsum0]
          linarith [htr, hsum3]
        obtain ⟨w21, w22, _⟩ := w23_diag_coords e₃
        obtain ⟨e₄, he₄⟩ : ∃ e₄, w23.1 e₃ = e₄ := ⟨_, rfl⟩
        rw [he₄] at w21 w22
        have he₄_idem : isRankOneIdem e₄ := he₄ ▸ f4InChevalley_preserves_isRankOneIdem w23_mem_f4 he₃_idem
        have he₄_2 : e₄.α₂ = 1 := w22.trans he₃_3
        have he₄_1 : e₄.α₁ = 0 := by
          rw [w21, h1a]; field_simp [ha0]; exact hsum0
        obtain ⟨w31d, w32d, _⟩ := w12_diag_coords e₄
        obtain ⟨e₅, he₅⟩ : ∃ e₅, w12.1 e₄ = e₅ := ⟨_, rfl⟩
        rw [he₅] at w31d w32d
        have he₅_idem : isRankOneIdem e₅ := he₅ ▸ f4InChevalley_preserves_isRankOneIdem w12_mem_f4 he₄_idem
        obtain ⟨hc, hhc, hac, _, _⟩ :=
          f4_clear_a_of_alpha1_one_alpha2_zero he₅_idem (w31d.trans he₄_2) (w32d.trans he₄_1)
        refine ⟨hc * w12 * w23 * f4PeirceExp 0 7 (e₁.α₂ / zornCoord e₁.a 0),
          e6F4InChevalley.mul_mem
            (e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem hhc w12_mem_f4) w23_mem_f4)
            (f4PeirceExp_mem_f4 0 7 _), ?_⟩
        rw [hmul, hmul, hmul, he₃, he₄, he₅]; exact hac
  obtain ⟨ga, hga, ha_zero⟩ := hStepA
  obtain ⟨ea, hea⟩ : ∃ ea, ga.1 e₁ = ea := ⟨_, rfl⟩
  rw [hea] at ha_zero
  have hea_idem : isRankOneIdem ea := hea ▸ f4InChevalley_preserves_isRankOneIdem hga he₁_idem
  have hnorm0 : ZornVectorMatrix.norm (0 : ZornVectorMatrix ℝ) = 0 := by
    simp [ZornVectorMatrix.norm, ZornVectorMatrix.zero, ZornVec3.dot]
  have hprod : ea.α₁ * ea.α₂ = 0 := by
    rw [(isRankOneIdem_norm_eq hea_idem).2.2.2, ha_zero, hnorm0]
  by_cases hα₂ : ea.α₂ = 0
  · by_cases hα₁ : ea.α₁ ≠ 0
    · refine ⟨ga * hd, e6F4InChevalley.mul_mem hga hhd_f4, ?_, ?_, ?_⟩
      · rw [hmul, he₁, hea]; exact ha_zero
      · rw [hmul, he₁, hea]; exact hα₂
      · rw [hmul, he₁, hea]; exact hα₁
    · have hα₁0 : ea.α₁ = 0 := not_not.mp hα₁
      have hα₃ : ea.α₃ = 1 := by linarith [(isRankOneIdem_norm_eq hea_idem).1, hα₁0, hα₂]
      obtain ⟨w21, w22, _⟩ := w23_diag_coords ea
      obtain ⟨eb, heb⟩ : ∃ eb, w23.1 ea = eb := ⟨_, rfl⟩
      rw [heb] at w21 w22
      have heb_idem : isRankOneIdem eb := heb ▸ f4InChevalley_preserves_isRankOneIdem w23_mem_f4 hea_idem
      obtain ⟨w31d, w32d, _⟩ := w12_diag_coords eb
      obtain ⟨ec, hec⟩ : ∃ ec, w12.1 eb = ec := ⟨_, rfl⟩
      rw [hec] at w31d w32d
      have hec_idem : isRankOneIdem ec := hec ▸ f4InChevalley_preserves_isRankOneIdem w12_mem_f4 heb_idem
      obtain ⟨hc, hhc, hac, h1c, h2c⟩ :=
        f4_clear_a_of_alpha1_one_alpha2_zero hec_idem (w31d.trans (w22.trans hα₃)) (w32d.trans (w21.trans hα₁0))
      refine ⟨hc * w12 * w23 * ga * hd,
        e6F4InChevalley.mul_mem
          (e6F4InChevalley.mul_mem
            (e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem hhc w12_mem_f4) w23_mem_f4) hga) hhd_f4,
        ?_, ?_, ?_⟩
      · rw [hmul, hmul, hmul, hmul, he₁, hea, heb, hec]; exact hac
      · rw [hmul, hmul, hmul, hmul, he₁, hea, heb, hec]; exact h2c
      · rw [hmul, hmul, hmul, hmul, he₁, hea, heb, hec, h1c]; exact one_ne_zero
  · have hα₁0 : ea.α₁ = 0 := (mul_eq_zero.mp hprod).resolve_right hα₂
    obtain ⟨w1, w2, _⟩ := w12_diag_coords ea
    obtain ⟨wa0, wa7, wamid⟩ := w12_a_coords ea
    have heaw_a : (w12.1 ea).a = 0 := by
      have hcz := (zornCoord_eq_zero_iff ea.a).mpr ha_zero
      rw [← zornCoord_eq_zero_iff]; intro j
      fin_cases j <;> dsimp
      · rw [wa0, hcz 7, neg_zero]
      · exact (wamid 0).trans (hcz 1)
      · exact (wamid 1).trans (hcz 2)
      · exact (wamid 2).trans (hcz 3)
      · exact (wamid 3).trans (hcz 4)
      · exact (wamid 4).trans (hcz 5)
      · exact (wamid 5).trans (hcz 6)
      · rw [wa7, hcz 0, neg_zero]
    refine ⟨w12 * ga * hd,
      e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem w12_mem_f4 hga) hhd_f4, ?_, ?_, ?_⟩
    · rw [hmul, hmul, he₁, hea]; exact heaw_a
    · rw [hmul, hmul, he₁, hea, w2, hα₁0]
    · rw [hmul, hmul, he₁, hea, w1]; exact hα₂

private def clearCRoot : Fin 6 → Fin 72
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 11
  | 4 => 7
  | 5 => 6

private def clearCSign : Fin 6 → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => -1
  | 5 => 1

private def bumpCRoot : Fin 6 → Fin 72
  | 0 => 20
  | 1 => 22
  | 2 => 23
  | 3 => 21
  | 4 => 19
  | 5 => 18

private def bumpCSign : Fin 6 → ℤ
  | 0 => -1
  | 1 => -1
  | 2 => -1
  | 3 => -1
  | 4 => 1
  | 5 => -1

private theorem clearCRoot_lt_check :
    (List.finRange 6).all (fun i => decide ((clearCRoot i).val < 24) && decide ((bumpCRoot i).val < 24)) = true := by
  decide

private theorem clearCRoot_row_check :
    (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (clearCRoot i)) 19 k == 0) &&
      (sparseVal (e6RootSparse (clearCRoot i)) ⟨20 + i.val, by omega⟩ k ==
        if k.val = 19 then clearCSign i else 0))) = true := by
  decide

private theorem clearCRoot_prev_check :
    (List.finRange 6).all (fun i => (List.finRange 6).all (fun j =>
      if j.val < i.val then
        (List.finRange 27).all (fun k =>
          sparseVal (e6RootSparse (clearCRoot i)) ⟨20 + j.val, by omega⟩ k == 0)
      else true)) = true := by
  decide

private theorem bumpCRoot_row19_check :
    (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (bumpCRoot i)) 19 k ==
        if k.val = 20 + i.val then bumpCSign i else 0)) = true := by
  decide

private theorem d4_clear_c_mid_prefix :
    ∀ n : ℕ, n ≤ 6 → ∀ X : H3Zorn ℝ, zornCoord X.c 0 ≠ 0 →
      ∃ h ∈ d4Subgroup,
        zornCoord (h.1 X).c 0 = zornCoord X.c 0 ∧
        ∀ j : Fin 6, j.val < n → zornCoord (h.1 X).c ⟨1 + j.val, by omega⟩ = 0 := by
  intro n hn
  induction n with
  | zero =>
    intro X _
    exact ⟨1, d4Subgroup.one_mem, rfl, fun j hj => False.elim (Nat.not_lt_zero _ hj)⟩
  | succ m ih =>
    intro X hc0
    obtain ⟨h₁, hh₁, h0₁, hm₁⟩ := ih (Nat.le_of_succ_le hn) X hc0
    obtain ⟨X₁, hX₁⟩ : ∃ X₁, h₁.1 X = X₁ := ⟨_, rfl⟩
    rw [hX₁] at h0₁ hm₁
    have hX₁_c0 : zornCoord X₁.c 0 ≠ 0 := by rw [h0₁]; exact hc0
    let idx : Fin 6 := ⟨m, by omega⟩
    let r := clearCRoot idx
    have hr24 : r.val < 24 := by
      have hc := clearCRoot_lt_check
      simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
        decide_eq_true_eq] at hc
      exact (hc idx).1
    let t : ℝ := -(zornCoord X₁.c ⟨1 + m, by omega⟩) / ((clearCSign idx : ℝ) * zornCoord X₁.c 0)
    have hcs_ne : (clearCSign idx : ℝ) ≠ 0 := by
      have hall : ∀ i : Fin 6, (clearCSign i : ℝ) ≠ 0 := fun i => by
        fin_cases i <;> norm_num [clearCSign]
      exact hall idx
    have hg_mem : e6RootExp r t ∈ d4Subgroup := Subgroup.subset_closure ⟨(⟨r, hr24⟩, t), rfl⟩
    have hc_rows := clearCRoot_row_check
    simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc_rows
    have hc_prev := clearCRoot_prev_check
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc_prev
    have h0' : zornCoord ((e6RootExp r t).1 X₁).c 0 = zornCoord X₁.c 0 := by
      rw [← h3ZornCoord_c_eq]
      change h3ZornCoordinate ((e6RootExp r t).1 X₁) 19 = zornCoord X₁.c 0
      rw [rootExp_coord_unchanged r 19 t X₁ (fun k => (hc_rows idx k).1),
        show h3ZornCoordinate X₁ 19 = zornCoord X₁.c 0 from h3ZornCoord_c_eq X₁ 0]
    have hidx' : zornCoord ((e6RootExp r t).1 X₁).c ⟨1 + m, by omega⟩ = 0 := by
      rw [← h3ZornCoord_c_eq]
      have hs : ∀ k : Fin 27, sparseVal (e6RootSparse r) ⟨20 + idx.val, by omega⟩ k =
          if k = 19 then clearCSign idx else 0 := by
        intro k
        have h := (hc_rows idx k).2
        dsimp only [r]
        rw [h]; simp [Fin.ext_iff]
      have hcoord := rootExp_coord_add_single r ⟨20 + idx.val, by omega⟩ 19 (clearCSign idx) t X₁ hs
      have hm_eq : (⟨19 + (⟨1 + m, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
          ⟨20 + idx.val, by omega⟩ := Fin.ext (by dsimp [idx]; omega)
      rw [hm_eq, hcoord, ← hm_eq, h3ZornCoord_c_eq,
        show h3ZornCoordinate X₁ 19 = zornCoord X₁.c 0 from h3ZornCoord_c_eq X₁ 0]
      simp only [t]
      field_simp [hcs_ne, hX₁_c0]
      ring
    refine ⟨e6RootExp r t * h₁, d4Subgroup.mul_mem hg_mem hh₁, ?_, ?_⟩
    · change zornCoord ((e6RootExp r t).1 (h₁.1 X)).c 0 = zornCoord X.c 0
      rw [hX₁, h0', h0₁]
    · intro j hj
      change zornCoord ((e6RootExp r t).1 (h₁.1 X)).c ⟨1 + j.val, by omega⟩ = 0
      rw [hX₁]
      by_cases hjm : j.val = m
      · have hjeq : (⟨1 + j.val, by omega⟩ : Fin 8) = ⟨1 + m, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hjeq, hidx']
      · have hjlt : j.val < m := by omega
        have hp := hc_prev idx j
        simp only [show j.val < idx.val from hjlt, ↓reduceIte] at hp
        simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hp
        have hj0 : zornCoord ((e6RootExp r t).1 X₁).c ⟨1 + j.val, by omega⟩ =
            zornCoord X₁.c ⟨1 + j.val, by omega⟩ := by
          let j' : Fin 8 := ⟨1 + j.val, by omega⟩
          have hm_eq : (⟨19 + j'.val, by omega⟩ : Fin 27) = ⟨20 + j.val, by omega⟩ :=
            Fin.ext (by dsimp [j']; omega)
          change zornCoord ((e6RootExp r t).1 X₁).c j' = zornCoord X₁.c j'
          rw [← h3ZornCoord_c_eq, hm_eq,
            rootExp_coord_unchanged r ⟨20 + j.val, by omega⟩ t X₁ hp,
            ← hm_eq, h3ZornCoord_c_eq]
        rw [hj0, hm₁ j hjlt]

private theorem d4_clear_c_mid (X : H3Zorn ℝ) :
    ∃ h ∈ d4Subgroup,
      (h.1 X).α₁ = X.α₁ ∧ (h.1 X).α₂ = X.α₂ ∧ (h.1 X).α₃ = X.α₃ ∧
      (X.a = 0 → (h.1 X).a = 0) ∧ (X.b = 0 → (h.1 X).b = 0) ∧
      (∀ j : Fin 6, zornCoord (h.1 X).c ⟨1 + j.val, by omega⟩ = 0) := by
  by_cases hc0 : zornCoord X.c 0 ≠ 0
  · obtain ⟨h, hh, _, hj⟩ := d4_clear_c_mid_prefix 6 (le_refl 6) X hc0
    obtain ⟨h1, h2, h3, ha, hb, _⟩ := d4Subgroup_preserves_blocks hh X
    exact ⟨h, hh, h1, h2, h3, ha, hb, fun j => hj j j.isLt⟩
  · have hc00 : zornCoord X.c 0 = 0 := not_not.mp hc0
    by_cases hex : ∃ i : Fin 6, zornCoord X.c ⟨1 + i.val, by omega⟩ ≠ 0
    · obtain ⟨i, hi⟩ := hex
      let rb := bumpCRoot i
      have hrb24 : rb.val < 24 := by
        have hc := clearCRoot_lt_check
        simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
          decide_eq_true_eq] at hc
        exact (hc i).2
      have hgb : e6RootExp rb 1 ∈ d4Subgroup := Subgroup.subset_closure ⟨(⟨rb, hrb24⟩, 1), rfl⟩
      have hbrow := bumpCRoot_row19_check
      simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hbrow
      have hbs_ne : (bumpCSign i : ℝ) ≠ 0 := by
        fin_cases i <;> norm_num [bumpCSign]
      have hc0' : zornCoord ((e6RootExp rb 1).1 X).c 0 ≠ 0 := by
        rw [← h3ZornCoord_c_eq]
        have hs : ∀ k : Fin 27, sparseVal (e6RootSparse rb) 19 k =
            if k = ⟨20 + i.val, by omega⟩ then bumpCSign i else 0 := by
          intro k
          have h := hbrow i k
          dsimp only [rb]
          rw [h]; simp [Fin.ext_iff]
        change h3ZornCoordinate ((e6RootExp rb 1).1 X) 19 ≠ 0
        rw [rootExp_coord_add_single rb 19 ⟨20 + i.val, by omega⟩ (bumpCSign i) 1 X hs]
        have h4eq : (⟨20 + i.val, by omega⟩ : Fin 27) =
            ⟨19 + (⟨1 + i.val, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [show h3ZornCoordinate X 19 = zornCoord X.c 0 from h3ZornCoord_c_eq X 0,
          h4eq, h3ZornCoord_c_eq, hc00, zero_add, one_mul]
        exact mul_ne_zero hbs_ne hi
      obtain ⟨X₁, hX₁⟩ : ∃ X₁, (e6RootExp rb 1).1 X = X₁ := ⟨_, rfl⟩
      rw [hX₁] at hc0'
      obtain ⟨h, hh, _, hj⟩ := d4_clear_c_mid_prefix 6 (le_refl 6) X₁ hc0'
      have hmul_mem := d4Subgroup.mul_mem hh hgb
      obtain ⟨h1, h2, h3, ha, hb, _⟩ := d4Subgroup_preserves_blocks hmul_mem X
      refine ⟨h * e6RootExp rb 1, hmul_mem, h1, h2, h3, ha, hb, ?_⟩
      intro j
      change zornCoord (h.1 ((e6RootExp rb 1).1 X)).c ⟨1 + j.val, by omega⟩ = 0
      rw [hX₁]
      exact hj j j.isLt
    · push Not at hex
      exact ⟨1, d4Subgroup.one_mem, rfl, rfl, rfl, id, id, hex⟩

private theorem w31_c_and_ab_check :
    (List.finRange 27).all (fun k =>
      (sparseVal w31Sparse 19 k == if k.val = 26 then -1 else 0) &&
      (sparseVal w31Sparse 26 k == if k.val = 19 then -1 else 0)) = true ∧
    (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      sparseVal w31Sparse ⟨20 + j.val, by omega⟩ k == if k.val = 20 + j.val then 1 else 0)) = true ∧
    (List.finRange 27).all (fun m => (List.finRange 27).all (fun k =>
      if 3 ≤ m.val ∧ m.val < 19 then
        if k.val = 0 ∨ k.val = 2 ∨ (19 ≤ k.val ∧ k.val < 27) then
          sparseVal w31Sparse m k == 0
        else true
      else true)) = true := by
  decide

private theorem w31_c_coords (X : H3Zorn ℝ) :
    zornCoord (w31.1 X).c 0 = -zornCoord X.c 7 ∧
    zornCoord (w31.1 X).c 7 = -zornCoord X.c 0 ∧
    (∀ j : Fin 6, zornCoord (w31.1 X).c ⟨1 + j.val, by omega⟩ = zornCoord X.c ⟨1 + j.val, by omega⟩) := by
  have hc0 := w31_c_and_ab_check.1
  have hcmid := w31_c_and_ab_check.2.1
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc0 hcmid
  refine ⟨?_, ?_, ?_⟩
  · rw [← h3ZornCoord_c_eq, h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w31_sparse]
    rw [Finset.sum_eq_single 26]
    · have h26 : h3ZornCoordinate X 26 = zornCoord X.c 7 := h3ZornCoord_c_eq X 7
      simp [(hc0 26).1, h26]
    · intro k _ hk
      have hne : k.val ≠ 26 := fun h => hk (Fin.ext h)
      simp [(hc0 k).1, hne]
    · intro h; exact absurd (Finset.mem_univ 26) h
  · rw [← h3ZornCoord_c_eq, h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w31_sparse]
    rw [Finset.sum_eq_single 19]
    · have h19 : h3ZornCoordinate X 19 = zornCoord X.c 0 := h3ZornCoord_c_eq X 0
      simp [(hc0 19).2, h19]
    · intro k _ hk
      have hne : k.val ≠ 19 := fun h => hk (Fin.ext h)
      simp [(hc0 k).2, hne]
    · intro h; exact absurd (Finset.mem_univ 19) h
  · intro j
    rw [← h3ZornCoord_c_eq]
    have hm_eq : (⟨19 + (⟨1 + j.val, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
        ⟨20 + j.val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hm_eq, h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w31_sparse]
    rw [Finset.sum_eq_single ⟨20 + j.val, by omega⟩]
    · have hjv := hcmid j ⟨20 + j.val, by omega⟩
      simp only [↓reduceIte] at hjv
      rw [hjv, Int.cast_one, one_mul, ← hm_eq, h3ZornCoord_c_eq]
    · intro k _ hk
      have hne : k.val ≠ 20 + j.val := fun h => hk (Fin.ext h)
      simp [hcmid j k, hne]
    · intro h; exact absurd (Finset.mem_univ _) h

private theorem w31_preserves_zero_ab {X : H3Zorn ℝ} (ha : X.a = 0) (hb : X.b = 0) :
    (w31.1 X).a = 0 ∧ (w31.1 X).b = 0 := by
  have hc := w31_c_and_ab_check.2.2
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc
  have hzm : ∀ m : Fin 27, 3 ≤ m.val ∧ m.val < 19 → h3ZornCoordinate (w31.1 X) m = 0 := by
    intro m hm
    rw [h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w31_sparse]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k.val = 0 ∨ k.val = 2 ∨ (19 ≤ k.val ∧ k.val < 27)
    · have hcc := hc m k
      rw [ite_eq_left_of_eq_true _ _ (eq_true hm), ite_eq_left_of_eq_true _ _ (eq_true hk), beq_iff_eq] at hcc
      rw [hcc, Int.cast_zero, zero_mul]
    · have hk1 : k.val = 1 ∨ (3 ≤ k.val ∧ k.val < 11) ∨ (11 ≤ k.val ∧ k.val < 19) := by omega
      rcases hk1 with hk1 | ⟨h3, h11⟩ | ⟨h11, h19⟩
      · have hw1 : sparseVal w31Sparse m k = 0 := by
          have : (List.finRange 27).all (fun m => if 3 ≤ m.val ∧ m.val < 19 then
              sparseVal w31Sparse m 1 == 0 else true) = true := by decide
          simp only [List.all_eq_true, List.mem_finRange, true_implies] at this
          have h1 := this m
          rw [ite_eq_left_of_eq_true _ _ (eq_true hm), beq_iff_eq] at h1
          have hkeq : k = 1 := Fin.ext hk1
          rw [hkeq, h1]
        rw [hw1, Int.cast_zero, zero_mul]
      · have hkeq : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        have haz : h3ZornCoordinate X k = 0 := by
          rw [hkeq, h3ZornCoord_a_eq, ha]
          exact (zornCoord_eq_zero_iff 0).mpr rfl _
        rw [haz, mul_zero]
      · have hkeq : k = ⟨11 + (⟨k.val - 11, by omega⟩ : Fin 8).val, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        have hbz : h3ZornCoordinate X k = 0 := by
          rw [hkeq, h3ZornCoord_b_eq, hb]
          exact (zornCoord_eq_zero_iff 0).mpr rfl _
        rw [hbz, mul_zero]
  refine ⟨?_, ?_⟩
  · rw [← zornCoord_eq_zero_iff]; intro j
    rw [← h3ZornCoord_a_eq, hzm ⟨3 + j.val, by omega⟩ ⟨by dsimp; omega, by have := j.isLt; dsimp; omega⟩]
  · rw [← zornCoord_eq_zero_iff]; intro j
    rw [← h3ZornCoord_b_eq, hzm ⟨11 + j.val, by omega⟩ ⟨by dsimp; omega, by have := j.isLt; dsimp; omega⟩]

private theorem f4Peirce_2_0_mul_eq :
    sparseToMat (sparseMul (e6RootSparse 56) (e6RootSparse 57)) = sparseToMat [(19, 26, 1)] := by
  exact sparseToMat_eq_of_sparseEq (by decide)

private theorem f4Peirce_2_7_mul_eq :
    sparseToMat (sparseMul (e6RootSparse 70) (e6RootSparse 71)) = sparseToMat [(26, 19, 1)] := by
  exact sparseToMat_eq_of_sparseEq (by decide)

private theorem f4Peirce_2_0_check :
    (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 56) 0 k == 0) &&
      (sparseVal (e6RootSparse 57) 0 k == if k.val = 26 then 1 else 0) &&
      (sparseVal (e6RootSparse 56) 1 k == 0) &&
      (sparseVal (e6RootSparse 57) 1 k == 0) &&
      (sparseVal (e6RootSparse 56) 2 k == if k.val = 26 then 1 else 0) &&
      (sparseVal (e6RootSparse 57) 2 k == 0) &&
      (sparseVal (e6RootSparse 56) 19 k == if k.val = 0 then 1 else 0) &&
      (sparseVal (e6RootSparse 57) 19 k == if k.val = 2 then 1 else 0) &&
      (sparseVal (e6RootSparse 56) 26 k == 0) &&
      (sparseVal (e6RootSparse 57) 26 k == 0)) = true := by decide

private theorem f4Peirce_2_0_mid_ab_check :
    (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 56) ⟨20 + j.val, by omega⟩ k == 0) &&
      (sparseVal (e6RootSparse 57) ⟨20 + j.val, by omega⟩ k == 0))) = true ∧
    (List.finRange 16).all (fun m => (List.finRange 27).all (fun k =>
      if k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ (19 ≤ k.val ∧ k.val < 27) then
        (sparseVal (e6RootSparse 56) ⟨3 + m.val, by omega⟩ k == 0) &&
        (sparseVal (e6RootSparse 57) ⟨3 + m.val, by omega⟩ k == 0)
      else true)) = true := by decide

private theorem f4Peirce_2_7_check :
    (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 70) 0 k == 0) &&
      (sparseVal (e6RootSparse 71) 0 k == if k.val = 19 then 1 else 0) &&
      (sparseVal (e6RootSparse 70) 1 k == 0) &&
      (sparseVal (e6RootSparse 71) 1 k == 0) &&
      (sparseVal (e6RootSparse 70) 2 k == if k.val = 19 then 1 else 0) &&
      (sparseVal (e6RootSparse 71) 2 k == 0) &&
      (sparseVal (e6RootSparse 70) 19 k == 0) &&
      (sparseVal (e6RootSparse 71) 19 k == 0) &&
      (sparseVal (e6RootSparse 70) 26 k == if k.val = 0 then 1 else 0) &&
      (sparseVal (e6RootSparse 71) 26 k == if k.val = 2 then 1 else 0)) = true := by decide

private theorem f4Peirce_2_7_mid_ab_check :
    (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 70) ⟨20 + j.val, by omega⟩ k == 0) &&
      (sparseVal (e6RootSparse 71) ⟨20 + j.val, by omega⟩ k == 0))) = true ∧
    (List.finRange 16).all (fun m => (List.finRange 27).all (fun k =>
      if k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ (19 ≤ k.val ∧ k.val < 27) then
        (sparseVal (e6RootSparse 70) ⟨3 + m.val, by omega⟩ k == 0) &&
        (sparseVal (e6RootSparse 71) ⟨3 + m.val, by omega⟩ k == 0)
      else true)) = true := by decide

private theorem f4Peirce_2_0_coords (t : ℝ) {X : H3Zorn ℝ} (ha : X.a = 0) (hb : X.b = 0) :
    ((f4PeirceExp 2 0 t).1 X).α₁ = X.α₁ - t * zornCoord X.c 7 ∧
    ((f4PeirceExp 2 0 t).1 X).α₂ = X.α₂ ∧
    ((f4PeirceExp 2 0 t).1 X).α₃ = X.α₃ + t * zornCoord X.c 7 ∧
    ((f4PeirceExp 2 0 t).1 X).a = 0 ∧
    ((f4PeirceExp 2 0 t).1 X).b = 0 ∧
    zornCoord ((f4PeirceExp 2 0 t).1 X).c 0 =
      zornCoord X.c 0 + t * (X.α₁ - X.α₃) - t ^ 2 * zornCoord X.c 7 ∧
    zornCoord ((f4PeirceExp 2 0 t).1 X).c 7 = zornCoord X.c 7 ∧
    (∀ j : Fin 6, zornCoord ((f4PeirceExp 2 0 t).1 X).c ⟨1 + j.val, by omega⟩ =
      zornCoord X.c ⟨1 + j.val, by omega⟩) := by
  have hc := f4Peirce_2_0_check
  have hcm := f4Peirce_2_0_mid_ab_check.1
  have hab := f4Peirce_2_0_mid_ab_check.2
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc hcm hab
  have hpm : ∀ m k : Fin 27, sparseVal (sparseMul (e6RootSparse 56) (e6RootSparse 57)) m k =
      if m = 19 ∧ k = 26 then 1 else 0 := by
    intro m k
    have hm := congrFun (congrFun f4Peirce_2_0_mul_eq m) k
    change sparseVal (sparseMul (e6RootSparse 56) (e6RootSparse 57)) m k =
      sparseVal [(19, 26, 1)] m k at hm
    rw [hm]
    by_cases hmk : m = 19 ∧ k = 26
    · rcases hmk with ⟨rfl, rfl⟩; decide
    · simp only [hmk, ↓reduceIte, sparseVal_cons, sparseVal_nil, add_zero]
      have hb' : ((19 : Fin 27) == m && (26 : Fin 27) == k) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        exact not_and_or.mp fun ⟨h1, h2⟩ => hmk ⟨h1.symm, h2.symm⟩
      simp [hb']
  have hab_zero : ∀ m : Fin 16,
      h3ZornCoordinate ((e6RootExp 56 t).1 ((e6RootExp 57 (-t)).1 X)) ⟨3 + m.val, by omega⟩ = 0 := by
    intro m
    have hstep1 : ∀ n : Fin 16,
        h3ZornCoordinate ((e6RootExp 57 (-t)).1 X) ⟨3 + n.val, by omega⟩ = 0 := by
      intro n
      rw [h3ZornCoordinate_e6RootExp]
      have hxn : h3ZornCoordinate X ⟨3 + n.val, by omega⟩ = 0 := by
        by_cases hn8 : n.val < 8
        · have hne : (⟨3 + n.val, by omega⟩ : Fin 27) =
              ⟨3 + (⟨n.val, hn8⟩ : Fin 8).val, by omega⟩ := Fin.ext rfl
          rw [hne, h3ZornCoord_a_eq, ha]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
        · have hne : (⟨3 + n.val, by omega⟩ : Fin 27) =
              ⟨11 + (⟨n.val - 8, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [hne, h3ZornCoord_b_eq, hb]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
      have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse 57) ⟨3 + n.val, by omega⟩ k : ℝ) *
          h3ZornCoordinate X k) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ (19 ≤ k.val ∧ k.val < 27)
        · have hnn := hab n k
          rw [ite_eq_left_of_eq_true _ _ (eq_true hk)] at hnn
          simp only [Bool.and_eq_true, beq_iff_eq] at hnn
          rw [hnn.2, Int.cast_zero, zero_mul]
        · have hxk : h3ZornCoordinate X k = 0 := by
            by_cases hk11 : k.val < 11
            · have hk3 : 3 ≤ k.val := by omega
              have hne : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ :=
                Fin.ext (by dsimp; omega)
              rw [hne, h3ZornCoord_a_eq, ha]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
            · have hk19 : k.val < 19 := by omega
              have hne : k = ⟨11 + (⟨k.val - 11, by omega⟩ : Fin 8).val, by omega⟩ :=
                Fin.ext (by dsimp; omega)
              rw [hne, h3ZornCoord_b_eq, hb]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
          rw [hxk, mul_zero]
      rw [hxn, hs, mul_zero, add_zero]
    rw [h3ZornCoordinate_e6RootExp, hstep1 m, zero_add]
    have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse 56) ⟨3 + m.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate ((e6RootExp 57 (-t)).1 X) k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ (19 ≤ k.val ∧ k.val < 27)
      · have hmm := hab m k
        rw [ite_eq_left_of_eq_true _ _ (eq_true hk)] at hmm
        simp only [Bool.and_eq_true, beq_iff_eq] at hmm
        rw [hmm.1, Int.cast_zero, zero_mul]
      · have hkn : ∃ n : Fin 16, k = ⟨3 + n.val, by omega⟩ := ⟨⟨k.val - 3, by omega⟩, Fin.ext (by dsimp; omega)⟩
        obtain ⟨n, rfl⟩ := hkn
        rw [hstep1 n, mul_zero]
    rw [hs, mul_zero]
  have hf : f4PeirceExp 2 0 t = e6RootExp 56 t * e6RootExp 57 (-t) := rfl
  have hmul_app : (f4PeirceExp 2 0 t).1 X = (e6RootExp 56 t).1 ((e6RootExp 57 (-t)).1 X) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((f4PeirceExp 2 0 t).1 X) 0 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_zero_eq]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 56) 0 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.1.1.1]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 56) (e6RootSparse 57)) 0 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 0 k]
    rw [hs1, hs3, Finset.sum_eq_single 26 (fun k _ hk => by
      have hne : k.val ≠ 26 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.1.1.1.1.1.2, hne]) (fun h => absurd (Finset.mem_univ 26) h)]
    rw [(hc 26).1.1.1.1.1.1.1.1.2, show h3ZornCoordinate X 26 = zornCoord X.c 7 from h3ZornCoord_c_eq X 7]
    simp; ring
  · change h3ZornCoordinate ((f4PeirceExp 2 0 t).1 X) 1 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_one_eq]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 56) 1 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.1.2]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 57) 1 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 56) (e6RootSparse 57)) 1 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 1 k]
    rw [hs1, hs2, hs3]; ring
  · change h3ZornCoordinate ((f4PeirceExp 2 0 t).1 X) 2 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_two_eq]
    rw [Finset.sum_eq_single 26 (fun k _ hk => by
      have hne : k.val ≠ 26 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.1.1.2, hne]) (fun h => absurd (Finset.mem_univ 26) h)]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 57) 2 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 56) (e6RootSparse 57)) 2 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 2 k]
    rw [hs2, hs3, (hc 26).1.1.1.1.1.2, show h3ZornCoordinate X 26 = zornCoord X.c 7 from h3ZornCoord_c_eq X 7]
    simp
  · rw [← zornCoord_eq_zero_iff]; intro j
    rw [← h3ZornCoord_a_eq, hmul_app]
    exact hab_zero ⟨j.val, by omega⟩
  · rw [← zornCoord_eq_zero_iff]; intro j
    rw [← h3ZornCoord_b_eq, hmul_app]
    have hb_eq : (⟨11 + j.val, by omega⟩ : Fin 27) =
        ⟨3 + (⟨8 + j.val, by omega⟩ : Fin 16).val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hb_eq]
    exact hab_zero ⟨8 + j.val, by omega⟩
  · rw [← h3ZornCoord_c_eq]
    change h3ZornCoordinate ((f4PeirceExp 2 0 t).1 X) 19 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul]
    rw [Finset.sum_eq_single 0 (fun k _ hk => by
      have hne : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.2, hne]) (fun h => absurd (Finset.mem_univ 0) h)]
    rw [Finset.sum_eq_single 2 (fun k _ hk => by
      have hne : k.val ≠ 2 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.2, hne]) (fun h => absurd (Finset.mem_univ 2) h)]
    rw [Finset.sum_eq_single 26 (fun k _ hk => by simp [hpm 19 k, hk])
      (fun h => absurd (Finset.mem_univ 26) h)]
    rw [(hc 0).1.1.1.2, (hc 2).1.1.2, hpm 19 26]
    rw [show h3ZornCoordinate X 19 = zornCoord X.c 0 from h3ZornCoord_c_eq X 0,
      show h3ZornCoordinate X 0 = X.α₁ from rfl, show h3ZornCoordinate X 2 = X.α₃ from rfl,
      show h3ZornCoordinate X 26 = zornCoord X.c 7 from h3ZornCoord_c_eq X 7]
    simp; ring
  · rw [← h3ZornCoord_c_eq]
    change h3ZornCoordinate ((f4PeirceExp 2 0 t).1 X) 26 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 56) 26 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.2]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 57) 26 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 56) (e6RootSparse 57)) 26 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 26 k]
    rw [hs1, hs2, hs3, show h3ZornCoordinate X 26 = zornCoord X.c 7 from h3ZornCoord_c_eq X 7]; ring
  · intro j
    let j' : Fin 8 := ⟨1 + j.val, by omega⟩
    have hm_eq : (⟨19 + j'.val, by omega⟩ : Fin 27) = ⟨20 + j.val, by omega⟩ :=
      Fin.ext (by dsimp [j']; omega)
    change zornCoord ((f4PeirceExp 2 0 t).1 X).c j' = zornCoord X.c j'
    rw [← h3ZornCoord_c_eq, hm_eq, hf, h3ZornCoordinate_e6RootExp_mul]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 56) ⟨20 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hcm j k).1]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 57) ⟨20 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hcm j k).2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 56) (e6RootSparse 57)) ⟨20 + j.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        have hne : (⟨20 + j.val, by omega⟩ : Fin 27) ≠ 19 := fun h => by
          have := congrArg Fin.val h; dsimp at this; omega
        simp [hpm ⟨20 + j.val, by omega⟩ k, hne]
    rw [hs1, hs2, hs3, ← hm_eq, h3ZornCoord_c_eq]; ring

private theorem f4Peirce_2_7_coords (t : ℝ) {X : H3Zorn ℝ} (ha : X.a = 0) (hb : X.b = 0) :
    ((f4PeirceExp 2 7 t).1 X).α₁ = X.α₁ - t * zornCoord X.c 0 ∧
    ((f4PeirceExp 2 7 t).1 X).α₂ = X.α₂ ∧
    ((f4PeirceExp 2 7 t).1 X).α₃ = X.α₃ + t * zornCoord X.c 0 ∧
    ((f4PeirceExp 2 7 t).1 X).a = 0 ∧
    ((f4PeirceExp 2 7 t).1 X).b = 0 ∧
    zornCoord ((f4PeirceExp 2 7 t).1 X).c 0 = zornCoord X.c 0 ∧
    zornCoord ((f4PeirceExp 2 7 t).1 X).c 7 =
      zornCoord X.c 7 + t * (X.α₁ - X.α₃) - t ^ 2 * zornCoord X.c 0 ∧
    (∀ j : Fin 6, zornCoord ((f4PeirceExp 2 7 t).1 X).c ⟨1 + j.val, by omega⟩ =
      zornCoord X.c ⟨1 + j.val, by omega⟩) := by
  have hc := f4Peirce_2_7_check
  have hcm := f4Peirce_2_7_mid_ab_check.1
  have hab := f4Peirce_2_7_mid_ab_check.2
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc hcm hab
  have hpm : ∀ m k : Fin 27, sparseVal (sparseMul (e6RootSparse 70) (e6RootSparse 71)) m k =
      if m = 26 ∧ k = 19 then 1 else 0 := by
    intro m k
    have hm := congrFun (congrFun f4Peirce_2_7_mul_eq m) k
    change sparseVal (sparseMul (e6RootSparse 70) (e6RootSparse 71)) m k =
      sparseVal [(26, 19, 1)] m k at hm
    rw [hm]
    by_cases hmk : m = 26 ∧ k = 19
    · rcases hmk with ⟨rfl, rfl⟩; decide
    · simp only [hmk, ↓reduceIte, sparseVal_cons, sparseVal_nil, add_zero]
      have hb' : ((26 : Fin 27) == m && (19 : Fin 27) == k) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        exact not_and_or.mp fun ⟨h1, h2⟩ => hmk ⟨h1.symm, h2.symm⟩
      simp [hb']
  have hab_zero : ∀ m : Fin 16,
      h3ZornCoordinate ((e6RootExp 70 t).1 ((e6RootExp 71 (-t)).1 X)) ⟨3 + m.val, by omega⟩ = 0 := by
    intro m
    have hstep1 : ∀ n : Fin 16,
        h3ZornCoordinate ((e6RootExp 71 (-t)).1 X) ⟨3 + n.val, by omega⟩ = 0 := by
      intro n
      rw [h3ZornCoordinate_e6RootExp]
      have hxn : h3ZornCoordinate X ⟨3 + n.val, by omega⟩ = 0 := by
        by_cases hn8 : n.val < 8
        · have hne : (⟨3 + n.val, by omega⟩ : Fin 27) =
              ⟨3 + (⟨n.val, hn8⟩ : Fin 8).val, by omega⟩ := Fin.ext rfl
          rw [hne, h3ZornCoord_a_eq, ha]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
        · have hne : (⟨3 + n.val, by omega⟩ : Fin 27) =
              ⟨11 + (⟨n.val - 8, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [hne, h3ZornCoord_b_eq, hb]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
      have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse 71) ⟨3 + n.val, by omega⟩ k : ℝ) *
          h3ZornCoordinate X k) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ (19 ≤ k.val ∧ k.val < 27)
        · have hnn := hab n k
          rw [ite_eq_left_of_eq_true _ _ (eq_true hk)] at hnn
          simp only [Bool.and_eq_true, beq_iff_eq] at hnn
          rw [hnn.2, Int.cast_zero, zero_mul]
        · have hxk : h3ZornCoordinate X k = 0 := by
            by_cases hk11 : k.val < 11
            · have hk3 : 3 ≤ k.val := by omega
              have hne : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ :=
                Fin.ext (by dsimp; omega)
              rw [hne, h3ZornCoord_a_eq, ha]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
            · have hk19 : k.val < 19 := by omega
              have hne : k = ⟨11 + (⟨k.val - 11, by omega⟩ : Fin 8).val, by omega⟩ :=
                Fin.ext (by dsimp; omega)
              rw [hne, h3ZornCoord_b_eq, hb]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
          rw [hxk, mul_zero]
      rw [hxn, hs, mul_zero, add_zero]
    rw [h3ZornCoordinate_e6RootExp, hstep1 m, zero_add]
    have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse 70) ⟨3 + m.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate ((e6RootExp 71 (-t)).1 X) k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ (19 ≤ k.val ∧ k.val < 27)
      · have hmm := hab m k
        rw [ite_eq_left_of_eq_true _ _ (eq_true hk)] at hmm
        simp only [Bool.and_eq_true, beq_iff_eq] at hmm
        rw [hmm.1, Int.cast_zero, zero_mul]
      · have hkn : ∃ n : Fin 16, k = ⟨3 + n.val, by omega⟩ := ⟨⟨k.val - 3, by omega⟩, Fin.ext (by dsimp; omega)⟩
        obtain ⟨n, rfl⟩ := hkn
        rw [hstep1 n, mul_zero]
    rw [hs, mul_zero]
  have hf : f4PeirceExp 2 7 t = e6RootExp 70 t * e6RootExp 71 (-t) := rfl
  have hmul_app : (f4PeirceExp 2 7 t).1 X = (e6RootExp 70 t).1 ((e6RootExp 71 (-t)).1 X) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((f4PeirceExp 2 7 t).1 X) 0 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_zero_eq]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 70) 0 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.1.1.1]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 70) (e6RootSparse 71)) 0 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 0 k]
    rw [hs1, hs3, Finset.sum_eq_single 19 (fun k _ hk => by
      have hne : k.val ≠ 19 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.1.1.1.1.1.2, hne]) (fun h => absurd (Finset.mem_univ 19) h)]
    rw [(hc 19).1.1.1.1.1.1.1.1.2, show h3ZornCoordinate X 19 = zornCoord X.c 0 from h3ZornCoord_c_eq X 0]
    simp; ring
  · change h3ZornCoordinate ((f4PeirceExp 2 7 t).1 X) 1 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_one_eq]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 70) 1 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.1.2]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 71) 1 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 70) (e6RootSparse 71)) 1 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 1 k]
    rw [hs1, hs2, hs3]; ring
  · change h3ZornCoordinate ((f4PeirceExp 2 7 t).1 X) 2 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_two_eq]
    rw [Finset.sum_eq_single 19 (fun k _ hk => by
      have hne : k.val ≠ 19 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.1.1.2, hne]) (fun h => absurd (Finset.mem_univ 19) h)]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 71) 2 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 70) (e6RootSparse 71)) 2 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 2 k]
    rw [hs2, hs3, (hc 19).1.1.1.1.1.2, show h3ZornCoordinate X 19 = zornCoord X.c 0 from h3ZornCoord_c_eq X 0]
    simp
  · rw [← zornCoord_eq_zero_iff]; intro j
    rw [← h3ZornCoord_a_eq, hmul_app]
    exact hab_zero ⟨j.val, by omega⟩
  · rw [← zornCoord_eq_zero_iff]; intro j
    rw [← h3ZornCoord_b_eq, hmul_app]
    have hb_eq : (⟨11 + j.val, by omega⟩ : Fin 27) =
        ⟨3 + (⟨8 + j.val, by omega⟩ : Fin 16).val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hb_eq]
    exact hab_zero ⟨8 + j.val, by omega⟩
  · rw [← h3ZornCoord_c_eq]
    change h3ZornCoordinate ((f4PeirceExp 2 7 t).1 X) 19 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 70) 19 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.2]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 71) 19 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 70) (e6RootSparse 71)) 19 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 19 k]
    rw [hs1, hs2, hs3, show h3ZornCoordinate X 19 = zornCoord X.c 0 from h3ZornCoord_c_eq X 0]; ring
  · rw [← h3ZornCoord_c_eq]
    change h3ZornCoordinate ((f4PeirceExp 2 7 t).1 X) 26 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul]
    rw [Finset.sum_eq_single 0 (fun k _ hk => by
      have hne : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [(hc k).1.2, hne]) (fun h => absurd (Finset.mem_univ 0) h)]
    rw [Finset.sum_eq_single 2 (fun k _ hk => by
      have hne : k.val ≠ 2 := fun h => hk (Fin.ext h)
      simp [(hc k).2, hne]) (fun h => absurd (Finset.mem_univ 2) h)]
    rw [Finset.sum_eq_single 19 (fun k _ hk => by simp [hpm 26 k, hk])
      (fun h => absurd (Finset.mem_univ 19) h)]
    rw [(hc 0).1.2, (hc 2).2, hpm 26 19]
    rw [show h3ZornCoordinate X 26 = zornCoord X.c 7 from h3ZornCoord_c_eq X 7,
      show h3ZornCoordinate X 0 = X.α₁ from rfl, show h3ZornCoordinate X 2 = X.α₃ from rfl,
      show h3ZornCoordinate X 19 = zornCoord X.c 0 from h3ZornCoord_c_eq X 0]
    simp; ring
  · intro j
    let j' : Fin 8 := ⟨1 + j.val, by omega⟩
    have hm_eq : (⟨19 + j'.val, by omega⟩ : Fin 27) = ⟨20 + j.val, by omega⟩ :=
      Fin.ext (by dsimp [j']; omega)
    change zornCoord ((f4PeirceExp 2 7 t).1 X).c j' = zornCoord X.c j'
    rw [← h3ZornCoord_c_eq, hm_eq, hf, h3ZornCoordinate_e6RootExp_mul]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 70) ⟨20 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hcm j k).1]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 71) ⟨20 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hcm j k).2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 70) (e6RootSparse 71)) ⟨20 + j.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        have hne : (⟨20 + j.val, by omega⟩ : Fin 27) ≠ 26 := fun h => by
          have := congrArg Fin.val h; dsimp at this; omega
        simp [hpm ⟨20 + j.val, by omega⟩ k, hne]
    rw [hs1, hs2, hs3, ← hm_eq, h3ZornCoord_c_eq]; ring

private theorem scalar_peirce_kill_c7 (α₁ α₃ c₀ c₇ : ℝ) (hc₀ : c₀ ≠ 0) (hn : α₁ * α₃ = c₀ * c₇)
    (hsum : α₁ + α₃ = 1) :
    α₁ - (-α₃ / c₀) * c₀ = 1 ∧
    α₃ + (-α₃ / c₀) * c₀ = 0 ∧
    c₇ + (-α₃ / c₀) * (α₁ - α₃) - (-α₃ / c₀) ^ 2 * c₀ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · field_simp [hc₀]; linarith [hsum]
  · field_simp [hc₀]; ring
  · have hn' : c₇ = α₁ * α₃ / c₀ := by field_simp [hc₀]; linarith [hn]
    rw [hn']; field_simp [hc₀]; ring

private theorem f4_reduce_idempotent_to_diag1 (e : H3Zorn ℝ) (he : isRankOneIdem e) :
    ∃ h ∈ e6F4InChevalley, h.1 e = h3_diag₁ := by
  have hmul : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Y : H3Zorn ℝ),
      (g₁ * g₂).1 Y = g₁.1 (g₂.1 Y) := fun _ _ _ => rfl
  obtain ⟨h₁, hh₁, ha₁, hα₂, hα₁⟩ := f4_clear_a_and_alpha2_nonzero_alpha1 he
  obtain ⟨e₁, he₁⟩ : ∃ e₁, h₁.1 e = e₁ := ⟨_, rfl⟩
  rw [he₁] at ha₁ hα₂ hα₁
  have he₁_idem : isRankOneIdem e₁ := he₁ ▸ f4InChevalley_preserves_isRankOneIdem hh₁ he
  have hb₁ : e₁.b = 0 := isRankOneIdem_b_zero_of_a_zero he₁_idem ha₁ hα₁
  obtain ⟨hd, hhd, hd1, hd2, hd3, hda, hdb, hmid⟩ := d4_clear_c_mid e₁
  have hhd_f4 : hd ∈ e6F4InChevalley := d4Subgroup_le_f4InChevalley hhd
  obtain ⟨e₂, he₂⟩ : ∃ e₂, hd.1 e₁ = e₂ := ⟨_, rfl⟩
  rw [he₂] at hd1 hd2 hd3 hda hdb hmid
  have he₂_idem : isRankOneIdem e₂ := he₂ ▸ f4InChevalley_preserves_isRankOneIdem hhd_f4 he₁_idem
  have he₂_2 : e₂.α₂ = 0 := hd2.trans hα₂
  have he₂_a : e₂.a = 0 := hda ha₁
  have he₂_b : e₂.b = 0 := hdb hb₁
  have hstepC : ∃ gc ∈ e6F4InChevalley,
      (gc.1 e₂).a = 0 ∧ (gc.1 e₂).b = 0 ∧ (gc.1 e₂).c = 0 ∧ (gc.1 e₂).α₂ = 0 := by
    by_cases hc0 : zornCoord e₂.c 0 = 0
    · by_cases hc7 : zornCoord e₂.c 7 = 0
      · refine ⟨1, e6F4InChevalley.one_mem, he₂_a, he₂_b, ?_, he₂_2⟩
        change e₂.c = 0
        rw [← zornCoord_eq_zero_iff]; intro j
        fin_cases j <;> dsimp
        · exact hc0
        · exact hmid 0
        · exact hmid 1
        · exact hmid 2
        · exact hmid 3
        · exact hmid 4
        · exact hmid 5
        · exact hc7
      · obtain ⟨w1, w2, w3⟩ := w31_diag_coords e₂
        obtain ⟨wa3, wb3⟩ := w31_preserves_zero_ab he₂_a he₂_b
        obtain ⟨wc0, wc7, wcmid⟩ := w31_c_coords e₂
        obtain ⟨e₃, he₃⟩ : ∃ e₃, w31.1 e₂ = e₃ := ⟨_, rfl⟩
        rw [he₃] at w1 w2 w3 wa3 wb3 wc0 wc7 wcmid
        have he₃_idem : isRankOneIdem e₃ := he₃ ▸ f4InChevalley_preserves_isRankOneIdem w31_mem_f4 he₂_idem
        have he₃_2 : e₃.α₂ = 0 := w2.trans he₂_2
        have he₃_sum : e₃.α₁ + e₃.α₃ = 1 := by linarith [(isRankOneIdem_norm_eq he₃_idem).1, he₃_2]
        have he₃_c0 : zornCoord e₃.c 0 ≠ 0 := by rw [wc0]; exact neg_ne_zero.mpr hc7
        have he₃_mid : ∀ j : Fin 6, zornCoord e₃.c ⟨1 + j.val, by omega⟩ = 0 :=
          fun j => (wcmid j).trans (hmid j)
        have he₃_hn : e₃.α₁ * e₃.α₃ = zornCoord e₃.c 0 * zornCoord e₃.c 7 := by
          rw [(isRankOneIdem_norm_eq he₃_idem).2.2.1, zorn_norm_of_mid_zero he₃_mid]
        obtain ⟨hs1, hs3, hs7⟩ := scalar_peirce_kill_c7 e₃.α₁ e₃.α₃ (zornCoord e₃.c 0) (zornCoord e₃.c 7)
          he₃_c0 he₃_hn he₃_sum
        let t₁ : ℝ := -e₃.α₃ / zornCoord e₃.c 0
        obtain ⟨p1, p2, p3, pa, pb, pc0, pc7, pcmid⟩ := f4Peirce_2_7_coords t₁ wa3 wb3
        obtain ⟨e₄, he₄⟩ : ∃ e₄, (f4PeirceExp 2 7 t₁).1 e₃ = e₄ := ⟨_, rfl⟩
        rw [he₄] at p1 p2 p3 pa pb pc0 pc7 pcmid
        have he₄_1 : e₄.α₁ = 1 := p1.trans hs1
        have he₄_2 : e₄.α₂ = 0 := p2.trans he₃_2
        have he₄_3 : e₄.α₃ = 0 := p3.trans hs3
        have he₄_7 : zornCoord e₄.c 7 = 0 := pc7.trans hs7
        obtain ⟨q1, q2, q3, qa, qb, qc0, qc7, qcmid⟩ :=
          f4Peirce_2_0_coords (-(zornCoord e₄.c 0)) pa pb
        simp only [he₄_7, mul_zero, sub_zero, add_zero, he₄_1, he₄_3] at q1 q2 q3 qc0 qc7
        have hc_fin : ((f4PeirceExp 2 0 (-(zornCoord e₄.c 0))).1 e₄).c = 0 := by
          rw [← zornCoord_eq_zero_iff]; intro j
          fin_cases j <;> dsimp
          · rw [qc0]; ring
          · exact (qcmid 0).trans ((pcmid 0).trans (he₃_mid 0))
          · exact (qcmid 1).trans ((pcmid 1).trans (he₃_mid 1))
          · exact (qcmid 2).trans ((pcmid 2).trans (he₃_mid 2))
          · exact (qcmid 3).trans ((pcmid 3).trans (he₃_mid 3))
          · exact (qcmid 4).trans ((pcmid 4).trans (he₃_mid 4))
          · exact (qcmid 5).trans ((pcmid 5).trans (he₃_mid 5))
          · exact qc7
        refine ⟨f4PeirceExp 2 0 (-(zornCoord e₄.c 0)) * f4PeirceExp 2 7 t₁ * w31,
          e6F4InChevalley.mul_mem
            (e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 2 0 _) (f4PeirceExp_mem_f4 2 7 _)) w31_mem_f4,
          ?_, ?_, ?_, ?_⟩
        · rw [hmul, hmul, he₃, he₄]; exact qa
        · rw [hmul, hmul, he₃, he₄]; exact qb
        · rw [hmul, hmul, he₃, he₄]; exact hc_fin
        · rw [hmul, hmul, he₃, he₄, q2, he₄_2]
    · have he₂_sum : e₂.α₁ + e₂.α₃ = 1 := by linarith [(isRankOneIdem_norm_eq he₂_idem).1, he₂_2]
      have he₂_hn : e₂.α₁ * e₂.α₃ = zornCoord e₂.c 0 * zornCoord e₂.c 7 := by
        rw [(isRankOneIdem_norm_eq he₂_idem).2.2.1, zorn_norm_of_mid_zero hmid]
      obtain ⟨hs1, hs3, hs7⟩ := scalar_peirce_kill_c7 e₂.α₁ e₂.α₃ (zornCoord e₂.c 0) (zornCoord e₂.c 7)
        hc0 he₂_hn he₂_sum
      let t₁ : ℝ := -e₂.α₃ / zornCoord e₂.c 0
      obtain ⟨p1, p2, p3, pa, pb, pc0, pc7, pcmid⟩ := f4Peirce_2_7_coords t₁ he₂_a he₂_b
      obtain ⟨e₄, he₄⟩ : ∃ e₄, (f4PeirceExp 2 7 t₁).1 e₂ = e₄ := ⟨_, rfl⟩
      rw [he₄] at p1 p2 p3 pa pb pc0 pc7 pcmid
      have he₄_1 : e₄.α₁ = 1 := p1.trans hs1
      have he₄_2 : e₄.α₂ = 0 := p2.trans he₂_2
      have he₄_3 : e₄.α₃ = 0 := p3.trans hs3
      have he₄_7 : zornCoord e₄.c 7 = 0 := pc7.trans hs7
      obtain ⟨q1, q2, q3, qa, qb, qc0, qc7, qcmid⟩ :=
        f4Peirce_2_0_coords (-(zornCoord e₄.c 0)) pa pb
      simp only [he₄_7, mul_zero, sub_zero, add_zero, he₄_1, he₄_3] at q1 q2 q3 qc0 qc7
      have hc_fin : ((f4PeirceExp 2 0 (-(zornCoord e₄.c 0))).1 e₄).c = 0 := by
        rw [← zornCoord_eq_zero_iff]; intro j
        fin_cases j <;> dsimp
        · rw [qc0]; ring
        · exact (qcmid 0).trans ((pcmid 0).trans (hmid 0))
        · exact (qcmid 1).trans ((pcmid 1).trans (hmid 1))
        · exact (qcmid 2).trans ((pcmid 2).trans (hmid 2))
        · exact (qcmid 3).trans ((pcmid 3).trans (hmid 3))
        · exact (qcmid 4).trans ((pcmid 4).trans (hmid 4))
        · exact (qcmid 5).trans ((pcmid 5).trans (hmid 5))
        · exact qc7
      refine ⟨f4PeirceExp 2 0 (-(zornCoord e₄.c 0)) * f4PeirceExp 2 7 t₁,
        e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 2 0 _) (f4PeirceExp_mem_f4 2 7 _),
        ?_, ?_, ?_, ?_⟩
      · rw [hmul, he₄]; exact qa
      · rw [hmul, he₄]; exact qb
      · rw [hmul, he₄]; exact hc_fin
      · rw [hmul, he₄, q2, he₄_2]
  obtain ⟨gc, hgc, gca, gcb, gcc, gc2⟩ := hstepC
  obtain ⟨ef, hef⟩ : ∃ ef, gc.1 e₂ = ef := ⟨_, rfl⟩
  rw [hef] at gca gcb gcc gc2
  have hef_idem : isRankOneIdem ef := hef ▸ f4InChevalley_preserves_isRankOneIdem hgc he₂_idem
  have hnorm0 : ZornVectorMatrix.norm (0 : ZornVectorMatrix ℝ) = 0 := by
    simp [ZornVectorMatrix.norm, ZornVectorMatrix.zero, ZornVec3.dot]
  have hprod : ef.α₁ * ef.α₃ = 0 := by
    rw [(isRankOneIdem_norm_eq hef_idem).2.2.1, gcc, hnorm0]
  have hsum : ef.α₁ + ef.α₃ = 1 := by linarith [(isRankOneIdem_norm_eq hef_idem).1, gc2]
  rcases mul_eq_zero.mp hprod with h10 | h30
  · have h31 : ef.α₃ = 1 := by linarith [h10, hsum]
    obtain ⟨w1, w2, w3⟩ := w31_diag_coords ef
    obtain ⟨wa3, wb3⟩ := w31_preserves_zero_ab gca gcb
    obtain ⟨wc0, wc7, wcmid⟩ := w31_c_coords ef
    have hcf : (w31.1 ef).c = 0 := by
      have hcz := (zornCoord_eq_zero_iff ef.c).mpr gcc
      rw [← zornCoord_eq_zero_iff]; intro j
      fin_cases j <;> dsimp
      · rw [wc0, hcz 7, neg_zero]
      · exact (wcmid 0).trans (hcz 1)
      · exact (wcmid 1).trans (hcz 2)
      · exact (wcmid 2).trans (hcz 3)
      · exact (wcmid 3).trans (hcz 4)
      · exact (wcmid 4).trans (hcz 5)
      · exact (wcmid 5).trans (hcz 6)
      · rw [wc7, hcz 0, neg_zero]
    refine ⟨w31 * gc * hd * h₁,
      e6F4InChevalley.mul_mem
        (e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem w31_mem_f4 hgc) hhd_f4) hh₁, ?_⟩
    rw [hmul, hmul, hmul, he₁, he₂, hef]
    apply ext_h3
    · exact w1.trans h31
    · exact w2.trans gc2
    · exact w3.trans h10
    · exact wa3
    · exact wb3
    · exact hcf
  · have h11 : ef.α₁ = 1 := by linarith [h30, hsum]
    refine ⟨gc * hd * h₁,
      e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem hgc hhd_f4) hh₁, ?_⟩
    rw [hmul, hmul, he₁, he₂, hef]
    apply ext_h3
    · exact h11
    · exact gc2
    · exact h30
    · exact gca
    · exact gcb
    · exact gcc

/-- Transitivity of `e6ChevalleySubgroup` on rank-1 primitive idempotents. -/
theorem e6ChevalleySubgroup_transitive_rankOneIdempotent (e : H3Zorn ℝ) (he : isRankOneIdem e) :
    ∃ h ∈ e6ChevalleySubgroup, h.1 h3_diag₁ = e := by
  obtain ⟨g, hg, hge⟩ := f4_reduce_idempotent_to_diag1 e he
  refine ⟨g⁻¹, e6ChevalleySubgroup.inv_mem hg.1, ?_⟩
  change g.1.symm h3_diag₁ = e
  rw [← hge, g.1.symm_apply_apply]

/-! ### Step B2: Fixing `h3_diag₁` and Reducing `A h3_diag₂` to `h3_diag₂` -/

private theorem h3_diag₂_isRankOneIdem : isRankOneIdem h3_diag₂ := by
  refine ⟨h3_diag₂_mul_h3_diag₂, ?_, ?_⟩
  · change (0 : ℝ) + 1 + 0 = 1; norm_num
  · apply ext_h3 <;>
      simp [adjointQuad, h3_diag₂, ZornVectorMatrix.norm_zero,
        ZornVectorMatrix.conj_zero, ZornVectorMatrix.mul_zero,
        ZornVectorMatrix.smul_zero]

private theorem eq_J23_of_diag1_mul_zero {X : H3Zorn ℝ} (h : h3_diag₁ * X = 0) :
    X.α₁ = 0 ∧ X.a = 0 ∧ X.c = 0 := by
  have hdec : X = X.α₁ • h3_diag₁ + X.α₂ • h3_diag₂ + X.α₃ • h3_diag₃ +
      embedJ12 X.a + embedJ23 X.b + embedJ31 X.c := by
    apply ext_h3 <;> simp [h3_diag₁, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31,
      add_readback, smul_readback, ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]
  have hmul : h3_diag₁ * X = X.α₁ • h3_diag₁ + (1 / 2 : ℝ) • embedJ12 X.a + (1 / 2 : ℝ) • embedJ31 X.c := by
    conv_lhs => rw [hdec]
    simp only [mul_add, mul_smul_comm, h3_diag₁_mul_h3_diag₁, h3_diag₁_mul_h3_diag₂,
      h3_diag₁_mul_h3_diag₃, h3_diag₁_mul_embedJ12, h3_diag₁_mul_embedJ23, h3_diag₁_mul_embedJ31,
      smul_zero, add_zero]
  rw [hmul] at h
  have hα₁ : X.α₁ = 0 := by
    have h0 := congrArg H3Zorn.α₁ h
    simpa [h3_diag₁, embedJ12, embedJ31, add_readback, smul_readback] using h0
  have ha : X.a = 0 := by
    have h0 := congrArg H3Zorn.a h
    have h0' : ZornVectorMatrix.smul (1 / 2 : ℝ) X.a = 0 := by
      simpa [h3_diag₁, embedJ12, embedJ31, add_readback, smul_readback, ZornVectorMatrix.smul_zero,
        ZornVectorMatrix.add_zero] using h0
    rw [← zornCoord_eq_zero_iff]; intro i
    have hi := congrArg (fun u => zornCoord u i) h0'
    have hsm : zornCoord (ZornVectorMatrix.smul (1 / 2 : ℝ) X.a) i = (1 / 2 : ℝ) * zornCoord X.a i := by
      fin_cases i <;> rfl
    rw [hsm] at hi
    have hz : zornCoord (0 : ZornVectorMatrix ℝ) i = 0 := by fin_cases i <;> rfl
    rw [hz] at hi
    have hi0 : zornCoord X.a i = 0 := (mul_eq_zero.mp hi).resolve_left (by norm_num)
    simp [hi0]
  have hc : X.c = 0 := by
    have h0 := congrArg H3Zorn.c h
    have h0' : ZornVectorMatrix.smul (1 / 2 : ℝ) X.c = 0 := by
      simpa [h3_diag₁, embedJ12, embedJ31, add_readback, smul_readback, ZornVectorMatrix.smul_zero,
        ZornVectorMatrix.add_zero] using h0
    rw [← zornCoord_eq_zero_iff]; intro i
    have hi := congrArg (fun u => zornCoord u i) h0'
    have hsm : zornCoord (ZornVectorMatrix.smul (1 / 2 : ℝ) X.c) i = (1 / 2 : ℝ) * zornCoord X.c i := by
      fin_cases i <;> rfl
    rw [hsm] at hi
    have hz : zornCoord (0 : ZornVectorMatrix ℝ) i = 0 := by fin_cases i <;> rfl
    rw [hz] at hi
    have hi0 : zornCoord X.c i = 0 := (mul_eq_zero.mp hi).resolve_left (by norm_num)
    simp [hi0]
  exact ⟨hα₁, ha, hc⟩

private def clearBRoot : Fin 6 → Fin 72
  | 0 => 21
  | 1 => 19
  | 2 => 18
  | 3 => 3
  | 4 => 4
  | 5 => 5

private def clearBSign : Fin 6 → ℤ
  | 0 => 1
  | 1 => -1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1

private def bumpBRoot : Fin 6 → Fin 72
  | 0 => 11
  | 1 => 7
  | 2 => 6
  | 3 => 10
  | 4 => 14
  | 5 => 17

private def bumpBSign : Fin 6 → ℤ
  | 0 => -1
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => -1
  | 5 => -1

private theorem clearBRoot_lt_check :
    (List.finRange 6).all (fun i => decide ((clearBRoot i).val < 24) && decide ((bumpBRoot i).val < 24)) = true := by
  decide

private theorem clearBRoot_row_check :
    (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (clearBRoot i)) 11 k == 0) &&
      (sparseVal (e6RootSparse (clearBRoot i)) ⟨12 + i.val, by omega⟩ k ==
        if k.val = 11 then clearBSign i else 0))) = true := by
  decide

private theorem clearBRoot_prev_check :
    (List.finRange 6).all (fun i => (List.finRange 6).all (fun j =>
      if j.val < i.val then
        (List.finRange 27).all (fun k =>
          sparseVal (e6RootSparse (clearBRoot i)) ⟨12 + j.val, by omega⟩ k == 0)
      else true)) = true := by
  decide

private theorem bumpBRoot_row11_check :
    (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (bumpBRoot i)) 11 k ==
        if k.val = 12 + i.val then bumpBSign i else 0)) = true := by
  decide

private theorem d4_clear_b_mid_prefix :
    ∀ n : ℕ, n ≤ 6 → ∀ X : H3Zorn ℝ, zornCoord X.b 0 ≠ 0 →
      ∃ h ∈ d4Subgroup,
        zornCoord (h.1 X).b 0 = zornCoord X.b 0 ∧
        ∀ j : Fin 6, j.val < n → zornCoord (h.1 X).b ⟨1 + j.val, by omega⟩ = 0 := by
  intro n hn
  induction n with
  | zero =>
    intro X _
    exact ⟨1, d4Subgroup.one_mem, rfl, fun j hj => False.elim (Nat.not_lt_zero _ hj)⟩
  | succ m ih =>
    intro X hb0
    obtain ⟨h₁, hh₁, h0₁, hm₁⟩ := ih (Nat.le_of_succ_le hn) X hb0
    obtain ⟨X₁, hX₁⟩ : ∃ X₁, h₁.1 X = X₁ := ⟨_, rfl⟩
    rw [hX₁] at h0₁ hm₁
    have hX₁_b0 : zornCoord X₁.b 0 ≠ 0 := by rw [h0₁]; exact hb0
    let idx : Fin 6 := ⟨m, by omega⟩
    let r := clearBRoot idx
    have hr24 : r.val < 24 := by
      have hc := clearBRoot_lt_check
      simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
        decide_eq_true_eq] at hc
      exact (hc idx).1
    let t : ℝ := -(zornCoord X₁.b ⟨1 + m, by omega⟩) / ((clearBSign idx : ℝ) * zornCoord X₁.b 0)
    have hbs_ne : (clearBSign idx : ℝ) ≠ 0 := by
      have hall : ∀ i : Fin 6, (clearBSign i : ℝ) ≠ 0 := fun i => by
        fin_cases i <;> norm_num [clearBSign]
      exact hall idx
    have hg_mem : e6RootExp r t ∈ d4Subgroup := Subgroup.subset_closure ⟨(⟨r, hr24⟩, t), rfl⟩
    have hc_rows := clearBRoot_row_check
    simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc_rows
    have hc_prev := clearBRoot_prev_check
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc_prev
    have h0' : zornCoord ((e6RootExp r t).1 X₁).b 0 = zornCoord X₁.b 0 := by
      rw [← h3ZornCoord_b_eq]
      change h3ZornCoordinate ((e6RootExp r t).1 X₁) 11 = zornCoord X₁.b 0
      rw [rootExp_coord_unchanged r 11 t X₁ (fun k => (hc_rows idx k).1),
        show h3ZornCoordinate X₁ 11 = zornCoord X₁.b 0 from h3ZornCoord_b_eq X₁ 0]
    have hidx' : zornCoord ((e6RootExp r t).1 X₁).b ⟨1 + m, by omega⟩ = 0 := by
      rw [← h3ZornCoord_b_eq]
      have hs : ∀ k : Fin 27, sparseVal (e6RootSparse r) ⟨12 + idx.val, by omega⟩ k =
          if k = 11 then clearBSign idx else 0 := by
        intro k
        have h := (hc_rows idx k).2
        dsimp only [r]
        rw [h]; simp [Fin.ext_iff]
      have hcoord := rootExp_coord_add_single r ⟨12 + idx.val, by omega⟩ 11 (clearBSign idx) t X₁ hs
      have hm_eq : (⟨11 + (⟨1 + m, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
          ⟨12 + idx.val, by omega⟩ := Fin.ext (by dsimp [idx]; omega)
      rw [hm_eq, hcoord, ← hm_eq, h3ZornCoord_b_eq,
        show h3ZornCoordinate X₁ 11 = zornCoord X₁.b 0 from h3ZornCoord_b_eq X₁ 0]
      simp only [t]
      field_simp [hbs_ne, hX₁_b0]
      ring
    refine ⟨e6RootExp r t * h₁, d4Subgroup.mul_mem hg_mem hh₁, ?_, ?_⟩
    · change zornCoord ((e6RootExp r t).1 (h₁.1 X)).b 0 = zornCoord X.b 0
      rw [hX₁, h0', h0₁]
    · intro j hj
      change zornCoord ((e6RootExp r t).1 (h₁.1 X)).b ⟨1 + j.val, by omega⟩ = 0
      rw [hX₁]
      by_cases hjm : j.val = m
      · have hjeq : (⟨1 + j.val, by omega⟩ : Fin 8) = ⟨1 + m, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hjeq, hidx']
      · have hjlt : j.val < m := by omega
        have hp := hc_prev idx j
        simp only [show j.val < idx.val from hjlt, ↓reduceIte] at hp
        simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hp
        have hj0 : zornCoord ((e6RootExp r t).1 X₁).b ⟨1 + j.val, by omega⟩ =
            zornCoord X₁.b ⟨1 + j.val, by omega⟩ := by
          let j' : Fin 8 := ⟨1 + j.val, by omega⟩
          have hm_eq : (⟨11 + j'.val, by omega⟩ : Fin 27) = ⟨12 + j.val, by omega⟩ :=
            Fin.ext (by dsimp [j']; omega)
          change zornCoord ((e6RootExp r t).1 X₁).b j' = zornCoord X₁.b j'
          rw [← h3ZornCoord_b_eq, hm_eq,
            rootExp_coord_unchanged r ⟨12 + j.val, by omega⟩ t X₁ hp,
            ← hm_eq, h3ZornCoord_b_eq]
        rw [hj0, hm₁ j hjlt]

private theorem d4_clear_b_mid (X : H3Zorn ℝ) :
    ∃ h ∈ d4Subgroup,
      (h.1 X).α₁ = X.α₁ ∧ (h.1 X).α₂ = X.α₂ ∧ (h.1 X).α₃ = X.α₃ ∧
      (X.a = 0 → (h.1 X).a = 0) ∧ (X.c = 0 → (h.1 X).c = 0) ∧
      (∀ j : Fin 6, zornCoord (h.1 X).b ⟨1 + j.val, by omega⟩ = 0) := by
  by_cases hb0 : zornCoord X.b 0 ≠ 0
  · obtain ⟨h, hh, _, hj⟩ := d4_clear_b_mid_prefix 6 (le_refl 6) X hb0
    obtain ⟨h1, h2, h3, ha, _, hc⟩ := d4Subgroup_preserves_blocks hh X
    exact ⟨h, hh, h1, h2, h3, ha, hc, fun j => hj j j.isLt⟩
  · have hb00 : zornCoord X.b 0 = 0 := not_not.mp hb0
    by_cases hex : ∃ i : Fin 6, zornCoord X.b ⟨1 + i.val, by omega⟩ ≠ 0
    · obtain ⟨i, hi⟩ := hex
      let rb := bumpBRoot i
      have hrb24 : rb.val < 24 := by
        have hc := clearBRoot_lt_check
        simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
          decide_eq_true_eq] at hc
        exact (hc i).2
      have hgb : e6RootExp rb 1 ∈ d4Subgroup := Subgroup.subset_closure ⟨(⟨rb, hrb24⟩, 1), rfl⟩
      have hbrow := bumpBRoot_row11_check
      simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hbrow
      have hbs_ne : (bumpBSign i : ℝ) ≠ 0 := by
        fin_cases i <;> norm_num [bumpBSign]
      have hb0' : zornCoord ((e6RootExp rb 1).1 X).b 0 ≠ 0 := by
        rw [← h3ZornCoord_b_eq]
        have hs : ∀ k : Fin 27, sparseVal (e6RootSparse rb) 11 k =
            if k = ⟨12 + i.val, by omega⟩ then bumpBSign i else 0 := by
          intro k
          have h := hbrow i k
          dsimp only [rb]
          rw [h]; simp [Fin.ext_iff]
        change h3ZornCoordinate ((e6RootExp rb 1).1 X) 11 ≠ 0
        rw [rootExp_coord_add_single rb 11 ⟨12 + i.val, by omega⟩ (bumpBSign i) 1 X hs]
        have h4eq : (⟨12 + i.val, by omega⟩ : Fin 27) =
            ⟨11 + (⟨1 + i.val, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [show h3ZornCoordinate X 11 = zornCoord X.b 0 from h3ZornCoord_b_eq X 0,
          h4eq, h3ZornCoord_b_eq, hb00, zero_add, one_mul]
        exact mul_ne_zero hbs_ne hi
      obtain ⟨X₁, hX₁⟩ : ∃ X₁, (e6RootExp rb 1).1 X = X₁ := ⟨_, rfl⟩
      rw [hX₁] at hb0'
      obtain ⟨h, hh, _, hj⟩ := d4_clear_b_mid_prefix 6 (le_refl 6) X₁ hb0'
      have hmul_mem := d4Subgroup.mul_mem hh hgb
      obtain ⟨h1, h2, h3, ha, _, hc⟩ := d4Subgroup_preserves_blocks hmul_mem X
      refine ⟨h * e6RootExp rb 1, hmul_mem, h1, h2, h3, ha, hc, ?_⟩
      intro j
      change zornCoord (h.1 ((e6RootExp rb 1).1 X)).b ⟨1 + j.val, by omega⟩ = 0
      rw [hX₁]
      exact hj j j.isLt
    · push Not at hex
      exact ⟨1, d4Subgroup.one_mem, rfl, rfl, rfl, id, id, hex⟩

private theorem w23_b_and_ac_check :
    (List.finRange 27).all (fun k =>
      (sparseVal w23Sparse 11 k == if k.val = 18 then -1 else 0) &&
      (sparseVal w23Sparse 18 k == if k.val = 11 then -1 else 0)) = true ∧
    (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      sparseVal w23Sparse ⟨12 + j.val, by omega⟩ k == if k.val = 12 + j.val then 1 else 0)) = true ∧
    (List.finRange 27).all (fun m => (List.finRange 27).all (fun k =>
      if (3 ≤ m.val ∧ m.val < 11) ∨ (19 ≤ m.val ∧ m.val < 27) then
        if k.val = 1 ∨ k.val = 2 ∨ (11 ≤ k.val ∧ k.val < 19) then
          sparseVal w23Sparse m k == 0
        else true
      else true)) = true ∧
    (List.finRange 27).all (fun m =>
      if (3 ≤ m.val ∧ m.val < 11) ∨ (19 ≤ m.val ∧ m.val < 27) then
        sparseVal w23Sparse m 0 == 0
      else true) = true := by
  decide

private theorem w23_b_coords (X : H3Zorn ℝ) :
    zornCoord (w23.1 X).b 0 = -zornCoord X.b 7 ∧
    zornCoord (w23.1 X).b 7 = -zornCoord X.b 0 ∧
    (∀ j : Fin 6, zornCoord (w23.1 X).b ⟨1 + j.val, by omega⟩ = zornCoord X.b ⟨1 + j.val, by omega⟩) := by
  have hc0 := w23_b_and_ac_check.1
  have hcmid := w23_b_and_ac_check.2.1
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc0 hcmid
  refine ⟨?_, ?_, ?_⟩
  · rw [← h3ZornCoord_b_eq, h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w23_sparse]
    rw [Finset.sum_eq_single 18]
    · have h18 : h3ZornCoordinate X 18 = zornCoord X.b 7 := h3ZornCoord_b_eq X 7
      simp [(hc0 18).1, h18]
    · intro k _ hk
      have hne : k.val ≠ 18 := fun h => hk (Fin.ext h)
      simp [(hc0 k).1, hne]
    · intro h; exact absurd (Finset.mem_univ 18) h
  · rw [← h3ZornCoord_b_eq, h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w23_sparse]
    rw [Finset.sum_eq_single 11]
    · have h11 : h3ZornCoordinate X 11 = zornCoord X.b 0 := h3ZornCoord_b_eq X 0
      simp [(hc0 11).2, h11]
    · intro k _ hk
      have hne : k.val ≠ 11 := fun h => hk (Fin.ext h)
      simp [(hc0 k).2, hne]
    · intro h; exact absurd (Finset.mem_univ 11) h
  · intro j
    rw [← h3ZornCoord_b_eq]
    have hm_eq : (⟨11 + (⟨1 + j.val, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
        ⟨12 + j.val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hm_eq, h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w23_sparse]
    rw [Finset.sum_eq_single ⟨12 + j.val, by omega⟩]
    · have hjv := hcmid j ⟨12 + j.val, by omega⟩
      simp only [↓reduceIte] at hjv
      rw [hjv, Int.cast_one, one_mul, ← hm_eq, h3ZornCoord_b_eq]
    · intro k _ hk
      have hne : k.val ≠ 12 + j.val := fun h => hk (Fin.ext h)
      simp [hcmid j k, hne]
    · intro h; exact absurd (Finset.mem_univ _) h

private theorem w23_preserves_zero_ac {X : H3Zorn ℝ} (ha : X.a = 0) (hc_zero : X.c = 0) :
    (w23.1 X).a = 0 ∧ (w23.1 X).c = 0 := by
  have hc := w23_b_and_ac_check.2.2.1
  have hc0 := w23_b_and_ac_check.2.2.2
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc hc0
  have hzm : ∀ m : Fin 27, (3 ≤ m.val ∧ m.val < 11) ∨ (19 ≤ m.val ∧ m.val < 27) →
      h3ZornCoordinate (w23.1 X) m = 0 := by
    intro m hm
    rw [h3ZornCoordinate_of_matrix_equiv _ _ h3zornToMatrix_w23_sparse]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k.val = 1 ∨ k.val = 2 ∨ (11 ≤ k.val ∧ k.val < 19)
    · have hcc := hc m k
      rw [ite_eq_left_of_eq_true _ _ (eq_true hm), ite_eq_left_of_eq_true _ _ (eq_true hk), beq_iff_eq] at hcc
      rw [hcc, Int.cast_zero, zero_mul]
    · have hk1 : k.val = 0 ∨ (3 ≤ k.val ∧ k.val < 11) ∨ (19 ≤ k.val ∧ k.val < 27) := by omega
      rcases hk1 with hk0 | ⟨h3, h11⟩ | ⟨h19, h27⟩
      · have hw0 := hc0 m
        rw [ite_eq_left_of_eq_true _ _ (eq_true hm), beq_iff_eq] at hw0
        have hkeq : k = 0 := Fin.ext hk0
        rw [hkeq, hw0, Int.cast_zero, zero_mul]
      · have hkeq : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        have haz : h3ZornCoordinate X k = 0 := by
          rw [hkeq, h3ZornCoord_a_eq, ha]
          exact (zornCoord_eq_zero_iff 0).mpr rfl _
        rw [haz, mul_zero]
      · have hkeq : k = ⟨19 + (⟨k.val - 19, by omega⟩ : Fin 8).val, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        have hcz : h3ZornCoordinate X k = 0 := by
          rw [hkeq, h3ZornCoord_c_eq, hc_zero]
          exact (zornCoord_eq_zero_iff 0).mpr rfl _
        rw [hcz, mul_zero]
  refine ⟨?_, ?_⟩
  · rw [← zornCoord_eq_zero_iff]; intro j
    rw [← h3ZornCoord_a_eq, hzm ⟨3 + j.val, by omega⟩ (Or.inl ⟨by dsimp; omega, by have := j.isLt; dsimp; omega⟩)]
  · rw [← zornCoord_eq_zero_iff]; intro j
    rw [← h3ZornCoord_c_eq, hzm ⟨19 + j.val, by omega⟩ (Or.inr ⟨by dsimp; omega, by have := j.isLt; dsimp; omega⟩)]

private theorem f4Peirce_1_0_mul_eq :
    sparseToMat (sparseMul (e6RootSparse 40) (e6RootSparse 41)) = sparseToMat [(11, 18, 1)] := by
  exact sparseToMat_eq_of_sparseEq (by decide)

private theorem f4Peirce_1_7_mul_eq :
    sparseToMat (sparseMul (e6RootSparse 54) (e6RootSparse 55)) = sparseToMat [(18, 11, 1)] := by
  exact sparseToMat_eq_of_sparseEq (by decide)

private theorem f4Peirce_1_0_check :
    (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 40) 0 k == 0) &&
      (sparseVal (e6RootSparse 41) 0 k == 0) &&
      (sparseVal (e6RootSparse 40) 1 k == if k.val = 18 then 1 else 0) &&
      (sparseVal (e6RootSparse 41) 1 k == 0) &&
      (sparseVal (e6RootSparse 40) 2 k == 0) &&
      (sparseVal (e6RootSparse 41) 2 k == if k.val = 18 then 1 else 0) &&
      (sparseVal (e6RootSparse 40) 11 k == if k.val = 2 then 1 else 0) &&
      (sparseVal (e6RootSparse 41) 11 k == if k.val = 1 then 1 else 0) &&
      (sparseVal (e6RootSparse 40) 18 k == 0) &&
      (sparseVal (e6RootSparse 41) 18 k == 0)) = true := by decide

private theorem f4Peirce_1_0_mid_ac_fix1_check :
    (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 40) ⟨12 + j.val, by omega⟩ k == 0) &&
      (sparseVal (e6RootSparse 41) ⟨12 + j.val, by omega⟩ k == 0))) = true ∧
    (List.finRange 27).all (fun m => (List.finRange 27).all (fun k =>
      if (3 ≤ m.val ∧ m.val < 11) ∨ (19 ≤ m.val ∧ m.val < 27) then
        if k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ (11 ≤ k.val ∧ k.val < 19) then
          (sparseVal (e6RootSparse 40) m k == 0) && (sparseVal (e6RootSparse 41) m k == 0)
        else true
      else true)) = true ∧
    (List.finRange 27).all (fun m =>
      (sparseVal (e6RootSparse 40) m 0 == 0) && (sparseVal (e6RootSparse 41) m 0 == 0)) = true := by
  decide

private theorem f4Peirce_1_7_check :
    (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 54) 0 k == 0) &&
      (sparseVal (e6RootSparse 55) 0 k == 0) &&
      (sparseVal (e6RootSparse 54) 1 k == if k.val = 11 then 1 else 0) &&
      (sparseVal (e6RootSparse 55) 1 k == 0) &&
      (sparseVal (e6RootSparse 54) 2 k == 0) &&
      (sparseVal (e6RootSparse 55) 2 k == if k.val = 11 then 1 else 0) &&
      (sparseVal (e6RootSparse 54) 11 k == 0) &&
      (sparseVal (e6RootSparse 55) 11 k == 0) &&
      (sparseVal (e6RootSparse 54) 18 k == if k.val = 2 then 1 else 0) &&
      (sparseVal (e6RootSparse 55) 18 k == if k.val = 1 then 1 else 0)) = true := by decide

private theorem f4Peirce_1_7_mid_ac_fix1_check :
    (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 54) ⟨12 + j.val, by omega⟩ k == 0) &&
      (sparseVal (e6RootSparse 55) ⟨12 + j.val, by omega⟩ k == 0))) = true ∧
    (List.finRange 27).all (fun m => (List.finRange 27).all (fun k =>
      if (3 ≤ m.val ∧ m.val < 11) ∨ (19 ≤ m.val ∧ m.val < 27) then
        if k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ (11 ≤ k.val ∧ k.val < 19) then
          (sparseVal (e6RootSparse 54) m k == 0) && (sparseVal (e6RootSparse 55) m k == 0)
        else true
      else true)) = true ∧
    (List.finRange 27).all (fun m =>
      (sparseVal (e6RootSparse 54) m 0 == 0) && (sparseVal (e6RootSparse 55) m 0 == 0)) = true := by
  decide

private theorem f4Peirce_1_0_fix_diag1 (t : ℝ) : (f4PeirceExp 1 0 t).1 h3_diag₁ = h3_diag₁ := by
  have hcol := f4Peirce_1_0_mid_ac_fix1_check.2.2
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hcol
  have hf : f4PeirceExp 1 0 t = e6RootExp 40 t * e6RootExp 41 (-t) := rfl
  have h1 : ∀ (r : Fin 72) (s : ℝ), (∀ m : Fin 27, sparseVal (e6RootSparse r) m 0 = 0) →
      (e6RootExp r s).1 h3_diag₁ = h3_diag₁ := by
    intro r s hr0
    apply h3Zorn_ext_coord
    intro m
    rw [h3ZornCoordinate_e6RootExp]
    have hsum : (∑ k : Fin 27, (sparseVal (e6RootSparse r) m k : ℝ) * h3ZornCoordinate h3_diag₁ k) = 0 := by
      rw [Finset.sum_eq_single 0]
      · rw [hr0 m, Int.cast_zero, zero_mul]
      · intro k _ hk
        have hkz : h3ZornCoordinate h3_diag₁ k = 0 := by
          fin_cases k <;> simp_all [h3_diag₁, h3ZornCoordinate]
        rw [hkz, mul_zero]
      · intro h; exact absurd (Finset.mem_univ 0) h
    rw [hsum, mul_zero, add_zero]
  have hmul : (f4PeirceExp 1 0 t).1 h3_diag₁ = (e6RootExp 40 t).1 ((e6RootExp 41 (-t)).1 h3_diag₁) := rfl
  rw [hmul, h1 41 (-t) (fun m => (hcol m).2), h1 40 t (fun m => (hcol m).1)]

private theorem f4Peirce_1_7_fix_diag1 (t : ℝ) : (f4PeirceExp 1 7 t).1 h3_diag₁ = h3_diag₁ := by
  have hcol := f4Peirce_1_7_mid_ac_fix1_check.2.2
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hcol
  have h1 : ∀ (r : Fin 72) (s : ℝ), (∀ m : Fin 27, sparseVal (e6RootSparse r) m 0 = 0) →
      (e6RootExp r s).1 h3_diag₁ = h3_diag₁ := by
    intro r s hr0
    apply h3Zorn_ext_coord
    intro m
    rw [h3ZornCoordinate_e6RootExp]
    have hsum : (∑ k : Fin 27, (sparseVal (e6RootSparse r) m k : ℝ) * h3ZornCoordinate h3_diag₁ k) = 0 := by
      rw [Finset.sum_eq_single 0]
      · rw [hr0 m, Int.cast_zero, zero_mul]
      · intro k _ hk
        have hkz : h3ZornCoordinate h3_diag₁ k = 0 := by
          fin_cases k <;> simp_all [h3_diag₁, h3ZornCoordinate]
        rw [hkz, mul_zero]
      · intro h; exact absurd (Finset.mem_univ 0) h
    rw [hsum, mul_zero, add_zero]
  have hmul : (f4PeirceExp 1 7 t).1 h3_diag₁ = (e6RootExp 54 t).1 ((e6RootExp 55 (-t)).1 h3_diag₁) := rfl
  rw [hmul, h1 55 (-t) (fun m => (hcol m).2), h1 54 t (fun m => (hcol m).1)]

private theorem d4Subgroup_fix_diag1 {g : h3zornReducedStructureGroup} (hg : g ∈ d4Subgroup) :
    g.1 h3_diag₁ = h3_diag₁ := by
  obtain ⟨h1, h2, h3, ha, hb, hc⟩ := d4Subgroup_preserves_blocks hg h3_diag₁
  apply ext_h3
  · exact h1
  · exact h2
  · exact h3
  · exact ha rfl
  · exact hb rfl
  · exact hc rfl

private theorem f4Peirce_1_0_coords (t : ℝ) {X : H3Zorn ℝ} (ha : X.a = 0) (hc_zero : X.c = 0) :
    ((f4PeirceExp 1 0 t).1 X).α₁ = X.α₁ ∧
    ((f4PeirceExp 1 0 t).1 X).α₂ = X.α₂ + t * zornCoord X.b 7 ∧
    ((f4PeirceExp 1 0 t).1 X).α₃ = X.α₃ - t * zornCoord X.b 7 ∧
    ((f4PeirceExp 1 0 t).1 X).a = 0 ∧
    ((f4PeirceExp 1 0 t).1 X).c = 0 ∧
    zornCoord ((f4PeirceExp 1 0 t).1 X).b 0 =
      zornCoord X.b 0 + t * (X.α₃ - X.α₂) - t ^ 2 * zornCoord X.b 7 ∧
    zornCoord ((f4PeirceExp 1 0 t).1 X).b 7 = zornCoord X.b 7 ∧
    (∀ j : Fin 6, zornCoord ((f4PeirceExp 1 0 t).1 X).b ⟨1 + j.val, by omega⟩ =
      zornCoord X.b ⟨1 + j.val, by omega⟩) := by
  have hc := f4Peirce_1_0_check
  have hcm := f4Peirce_1_0_mid_ac_fix1_check.1
  have hac := f4Peirce_1_0_mid_ac_fix1_check.2.1
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc hcm hac
  have hpm : ∀ m k : Fin 27, sparseVal (sparseMul (e6RootSparse 40) (e6RootSparse 41)) m k =
      if m = 11 ∧ k = 18 then 1 else 0 := by
    intro m k
    have hm := congrFun (congrFun f4Peirce_1_0_mul_eq m) k
    change sparseVal (sparseMul (e6RootSparse 40) (e6RootSparse 41)) m k =
      sparseVal [(11, 18, 1)] m k at hm
    rw [hm]
    by_cases hmk : m = 11 ∧ k = 18
    · rcases hmk with ⟨rfl, rfl⟩; decide
    · simp only [hmk, ↓reduceIte, sparseVal_cons, sparseVal_nil, add_zero]
      have hb' : ((11 : Fin 27) == m && (18 : Fin 27) == k) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        exact not_and_or.mp fun ⟨h1, h2⟩ => hmk ⟨h1.symm, h2.symm⟩
      simp [hb']
  have hac_zero : ∀ m : Fin 27, (3 ≤ m.val ∧ m.val < 11) ∨ (19 ≤ m.val ∧ m.val < 27) →
      h3ZornCoordinate ((e6RootExp 40 t).1 ((e6RootExp 41 (-t)).1 X)) m = 0 := by
    intro m hm
    have hstep1 : ∀ n : Fin 27, (3 ≤ n.val ∧ n.val < 11) ∨ (19 ≤ n.val ∧ n.val < 27) →
        h3ZornCoordinate ((e6RootExp 41 (-t)).1 X) n = 0 := by
      intro n hn
      rw [h3ZornCoordinate_e6RootExp]
      have hxn : h3ZornCoordinate X n = 0 := by
        rcases hn with ⟨h3, h11⟩ | ⟨h19, h27⟩
        · have hne : n = ⟨3 + (⟨n.val - 3, by omega⟩ : Fin 8).val, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [hne, h3ZornCoord_a_eq, ha]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
        · have hne : n = ⟨19 + (⟨n.val - 19, by omega⟩ : Fin 8).val, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [hne, h3ZornCoord_c_eq, hc_zero]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
      have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse 41) n k : ℝ) *
          h3ZornCoordinate X k) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ (11 ≤ k.val ∧ k.val < 19)
        · have hnn := hac n k
          rw [ite_eq_left_of_eq_true _ _ (eq_true hn), ite_eq_left_of_eq_true _ _ (eq_true hk)] at hnn
          simp only [Bool.and_eq_true, beq_iff_eq] at hnn
          rw [hnn.2, Int.cast_zero, zero_mul]
        · have hxk : h3ZornCoordinate X k = 0 := by
            by_cases hk11 : k.val < 11
            · have hne : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ :=
                Fin.ext (by dsimp; omega)
              rw [hne, h3ZornCoord_a_eq, ha]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
            · have hne : k = ⟨19 + (⟨k.val - 19, by omega⟩ : Fin 8).val, by omega⟩ :=
                Fin.ext (by dsimp; omega)
              rw [hne, h3ZornCoord_c_eq, hc_zero]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
          rw [hxk, mul_zero]
      rw [hxn, hs, mul_zero, add_zero]
    rw [h3ZornCoordinate_e6RootExp, hstep1 m hm, zero_add]
    have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse 40) m k : ℝ) *
        h3ZornCoordinate ((e6RootExp 41 (-t)).1 X) k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ (11 ≤ k.val ∧ k.val < 19)
      · have hmm := hac m k
        rw [ite_eq_left_of_eq_true _ _ (eq_true hm), ite_eq_left_of_eq_true _ _ (eq_true hk)] at hmm
        simp only [Bool.and_eq_true, beq_iff_eq] at hmm
        rw [hmm.1, Int.cast_zero, zero_mul]
      · have hkn : (3 ≤ k.val ∧ k.val < 11) ∨ (19 ≤ k.val ∧ k.val < 27) := by omega
        rw [hstep1 k hkn, mul_zero]
    rw [hs, mul_zero]
  have hf : f4PeirceExp 1 0 t = e6RootExp 40 t * e6RootExp 41 (-t) := rfl
  have hmul_app : (f4PeirceExp 1 0 t).1 X = (e6RootExp 40 t).1 ((e6RootExp 41 (-t)).1 X) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((f4PeirceExp 1 0 t).1 X) 0 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_zero_eq]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 40) 0 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.1.1.1]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 41) 0 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 40) (e6RootSparse 41)) 0 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 0 k]
    rw [hs1, hs2, hs3]; ring
  · change h3ZornCoordinate ((f4PeirceExp 1 0 t).1 X) 1 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_one_eq]
    rw [Finset.sum_eq_single 18 (fun k _ hk => by
      have hne : k.val ≠ 18 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.1.1.1.1.2, hne]) (fun h => absurd (Finset.mem_univ 18) h)]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 41) 1 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 40) (e6RootSparse 41)) 1 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 1 k]
    rw [hs2, hs3, (hc 18).1.1.1.1.1.1.1.2, show h3ZornCoordinate X 18 = zornCoord X.b 7 from h3ZornCoord_b_eq X 7]
    simp
  · change h3ZornCoordinate ((f4PeirceExp 1 0 t).1 X) 2 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_two_eq]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 40) 2 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 40) (e6RootSparse 41)) 2 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 2 k]
    rw [hs1, hs3, Finset.sum_eq_single 18 (fun k _ hk => by
      have hne : k.val ≠ 18 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.1.2, hne]) (fun h => absurd (Finset.mem_univ 18) h)]
    rw [(hc 18).1.1.1.1.2, show h3ZornCoordinate X 18 = zornCoord X.b 7 from h3ZornCoord_b_eq X 7]
    simp; ring
  · rw [← zornCoord_eq_zero_iff]; intro j
    rw [← h3ZornCoord_a_eq, hmul_app]
    exact hac_zero ⟨3 + j.val, by omega⟩ (Or.inl ⟨by dsimp; omega, by have := j.isLt; dsimp; omega⟩)
  · rw [← zornCoord_eq_zero_iff]; intro j
    rw [← h3ZornCoord_c_eq, hmul_app]
    exact hac_zero ⟨19 + j.val, by omega⟩ (Or.inr ⟨by dsimp; omega, by have := j.isLt; dsimp; omega⟩)
  · rw [← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((f4PeirceExp 1 0 t).1 X) 11 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul]
    rw [Finset.sum_eq_single 2 (fun k _ hk => by
      have hne : k.val ≠ 2 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.2, hne]) (fun h => absurd (Finset.mem_univ 2) h)]
    rw [Finset.sum_eq_single 1 (fun k _ hk => by
      have hne : k.val ≠ 1 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.2, hne]) (fun h => absurd (Finset.mem_univ 1) h)]
    rw [Finset.sum_eq_single 18 (fun k _ hk => by simp [hpm 11 k, hk])
      (fun h => absurd (Finset.mem_univ 18) h)]
    rw [(hc 2).1.1.1.2, (hc 1).1.1.2, hpm 11 18]
    rw [show h3ZornCoordinate X 11 = zornCoord X.b 0 from h3ZornCoord_b_eq X 0,
      show h3ZornCoordinate X 2 = X.α₃ from rfl, show h3ZornCoordinate X 1 = X.α₂ from rfl,
      show h3ZornCoordinate X 18 = zornCoord X.b 7 from h3ZornCoord_b_eq X 7]
    simp; ring
  · rw [← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((f4PeirceExp 1 0 t).1 X) 18 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 40) 18 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.2]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 41) 18 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 40) (e6RootSparse 41)) 18 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 18 k]
    rw [hs1, hs2, hs3, show h3ZornCoordinate X 18 = zornCoord X.b 7 from h3ZornCoord_b_eq X 7]; ring
  · intro j
    let j' : Fin 8 := ⟨1 + j.val, by omega⟩
    have hm_eq : (⟨11 + j'.val, by omega⟩ : Fin 27) = ⟨12 + j.val, by omega⟩ :=
      Fin.ext (by dsimp [j']; omega)
    change zornCoord ((f4PeirceExp 1 0 t).1 X).b j' = zornCoord X.b j'
    rw [← h3ZornCoord_b_eq, hm_eq, hf, h3ZornCoordinate_e6RootExp_mul]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 40) ⟨12 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hcm j k).1]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 41) ⟨12 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hcm j k).2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 40) (e6RootSparse 41)) ⟨12 + j.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        have hne : (⟨12 + j.val, by omega⟩ : Fin 27) ≠ 11 := fun h => by
          have := congrArg Fin.val h; dsimp at this; omega
        simp [hpm ⟨12 + j.val, by omega⟩ k, hne]
    rw [hs1, hs2, hs3, ← hm_eq, h3ZornCoord_b_eq]; ring

private theorem f4Peirce_1_7_coords (t : ℝ) {X : H3Zorn ℝ} (ha : X.a = 0) (hc_zero : X.c = 0) :
    ((f4PeirceExp 1 7 t).1 X).α₁ = X.α₁ ∧
    ((f4PeirceExp 1 7 t).1 X).α₂ = X.α₂ + t * zornCoord X.b 0 ∧
    ((f4PeirceExp 1 7 t).1 X).α₃ = X.α₃ - t * zornCoord X.b 0 ∧
    ((f4PeirceExp 1 7 t).1 X).a = 0 ∧
    ((f4PeirceExp 1 7 t).1 X).c = 0 ∧
    zornCoord ((f4PeirceExp 1 7 t).1 X).b 0 = zornCoord X.b 0 ∧
    zornCoord ((f4PeirceExp 1 7 t).1 X).b 7 =
      zornCoord X.b 7 + t * (X.α₃ - X.α₂) - t ^ 2 * zornCoord X.b 0 ∧
    (∀ j : Fin 6, zornCoord ((f4PeirceExp 1 7 t).1 X).b ⟨1 + j.val, by omega⟩ =
      zornCoord X.b ⟨1 + j.val, by omega⟩) := by
  have hc := f4Peirce_1_7_check
  have hcm := f4Peirce_1_7_mid_ac_fix1_check.1
  have hac := f4Peirce_1_7_mid_ac_fix1_check.2.1
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc hcm hac
  have hpm : ∀ m k : Fin 27, sparseVal (sparseMul (e6RootSparse 54) (e6RootSparse 55)) m k =
      if m = 18 ∧ k = 11 then 1 else 0 := by
    intro m k
    have hm := congrFun (congrFun f4Peirce_1_7_mul_eq m) k
    change sparseVal (sparseMul (e6RootSparse 54) (e6RootSparse 55)) m k =
      sparseVal [(18, 11, 1)] m k at hm
    rw [hm]
    by_cases hmk : m = 18 ∧ k = 11
    · rcases hmk with ⟨rfl, rfl⟩; decide
    · simp only [hmk, ↓reduceIte, sparseVal_cons, sparseVal_nil, add_zero]
      have hb' : ((18 : Fin 27) == m && (11 : Fin 27) == k) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        exact not_and_or.mp fun ⟨h1, h2⟩ => hmk ⟨h1.symm, h2.symm⟩
      simp [hb']
  have hac_zero : ∀ m : Fin 27, (3 ≤ m.val ∧ m.val < 11) ∨ (19 ≤ m.val ∧ m.val < 27) →
      h3ZornCoordinate ((e6RootExp 54 t).1 ((e6RootExp 55 (-t)).1 X)) m = 0 := by
    intro m hm
    have hstep1 : ∀ n : Fin 27, (3 ≤ n.val ∧ n.val < 11) ∨ (19 ≤ n.val ∧ n.val < 27) →
        h3ZornCoordinate ((e6RootExp 55 (-t)).1 X) n = 0 := by
      intro n hn
      rw [h3ZornCoordinate_e6RootExp]
      have hxn : h3ZornCoordinate X n = 0 := by
        rcases hn with ⟨h3, h11⟩ | ⟨h19, h27⟩
        · have hne : n = ⟨3 + (⟨n.val - 3, by omega⟩ : Fin 8).val, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [hne, h3ZornCoord_a_eq, ha]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
        · have hne : n = ⟨19 + (⟨n.val - 19, by omega⟩ : Fin 8).val, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [hne, h3ZornCoord_c_eq, hc_zero]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
      have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse 55) n k : ℝ) *
          h3ZornCoordinate X k) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ (11 ≤ k.val ∧ k.val < 19)
        · have hnn := hac n k
          rw [ite_eq_left_of_eq_true _ _ (eq_true hn), ite_eq_left_of_eq_true _ _ (eq_true hk)] at hnn
          simp only [Bool.and_eq_true, beq_iff_eq] at hnn
          rw [hnn.2, Int.cast_zero, zero_mul]
        · have hxk : h3ZornCoordinate X k = 0 := by
            by_cases hk11 : k.val < 11
            · have hne : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ :=
                Fin.ext (by dsimp; omega)
              rw [hne, h3ZornCoord_a_eq, ha]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
            · have hne : k = ⟨19 + (⟨k.val - 19, by omega⟩ : Fin 8).val, by omega⟩ :=
                Fin.ext (by dsimp; omega)
              rw [hne, h3ZornCoord_c_eq, hc_zero]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
          rw [hxk, mul_zero]
      rw [hxn, hs, mul_zero, add_zero]
    rw [h3ZornCoordinate_e6RootExp, hstep1 m hm, zero_add]
    have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse 54) m k : ℝ) *
        h3ZornCoordinate ((e6RootExp 55 (-t)).1 X) k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ (11 ≤ k.val ∧ k.val < 19)
      · have hmm := hac m k
        rw [ite_eq_left_of_eq_true _ _ (eq_true hm), ite_eq_left_of_eq_true _ _ (eq_true hk)] at hmm
        simp only [Bool.and_eq_true, beq_iff_eq] at hmm
        rw [hmm.1, Int.cast_zero, zero_mul]
      · have hkn : (3 ≤ k.val ∧ k.val < 11) ∨ (19 ≤ k.val ∧ k.val < 27) := by omega
        rw [hstep1 k hkn, mul_zero]
    rw [hs, mul_zero]
  have hf : f4PeirceExp 1 7 t = e6RootExp 54 t * e6RootExp 55 (-t) := rfl
  have hmul_app : (f4PeirceExp 1 7 t).1 X = (e6RootExp 54 t).1 ((e6RootExp 55 (-t)).1 X) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((f4PeirceExp 1 7 t).1 X) 0 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_zero_eq]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 54) 0 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.1.1.1]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 55) 0 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 54) (e6RootSparse 55)) 0 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 0 k]
    rw [hs1, hs2, hs3]; ring
  · change h3ZornCoordinate ((f4PeirceExp 1 7 t).1 X) 1 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_one_eq]
    rw [Finset.sum_eq_single 11 (fun k _ hk => by
      have hne : k.val ≠ 11 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.1.1.1.1.2, hne]) (fun h => absurd (Finset.mem_univ 11) h)]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 55) 1 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 54) (e6RootSparse 55)) 1 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 1 k]
    rw [hs2, hs3, (hc 11).1.1.1.1.1.1.1.2, show h3ZornCoordinate X 11 = zornCoord X.b 0 from h3ZornCoord_b_eq X 0]
    simp
  · change h3ZornCoordinate ((f4PeirceExp 1 7 t).1 X) 2 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul, h3ZornCoord_two_eq]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 54) 2 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 54) (e6RootSparse 55)) 2 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 2 k]
    rw [hs1, hs3, Finset.sum_eq_single 11 (fun k _ hk => by
      have hne : k.val ≠ 11 := fun h => hk (Fin.ext h)
      simp [(hc k).1.1.1.1.2, hne]) (fun h => absurd (Finset.mem_univ 11) h)]
    rw [(hc 11).1.1.1.1.2, show h3ZornCoordinate X 11 = zornCoord X.b 0 from h3ZornCoord_b_eq X 0]
    simp; ring
  · rw [← zornCoord_eq_zero_iff]; intro j
    rw [← h3ZornCoord_a_eq, hmul_app]
    exact hac_zero ⟨3 + j.val, by omega⟩ (Or.inl ⟨by dsimp; omega, by have := j.isLt; dsimp; omega⟩)
  · rw [← zornCoord_eq_zero_iff]; intro j
    rw [← h3ZornCoord_c_eq, hmul_app]
    exact hac_zero ⟨19 + j.val, by omega⟩ (Or.inr ⟨by dsimp; omega, by have := j.isLt; dsimp; omega⟩)
  · rw [← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((f4PeirceExp 1 7 t).1 X) 11 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 54) 11 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.1.2]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 55) 11 k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hc k).1.1.2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 54) (e6RootSparse 55)) 11 k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hpm 11 k]
    rw [hs1, hs2, hs3, show h3ZornCoordinate X 11 = zornCoord X.b 0 from h3ZornCoord_b_eq X 0]; ring
  · rw [← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((f4PeirceExp 1 7 t).1 X) 18 = _
    rw [hf, h3ZornCoordinate_e6RootExp_mul]
    rw [Finset.sum_eq_single 2 (fun k _ hk => by
      have hne : k.val ≠ 2 := fun h => hk (Fin.ext h)
      simp [(hc k).1.2, hne]) (fun h => absurd (Finset.mem_univ 2) h)]
    rw [Finset.sum_eq_single 1 (fun k _ hk => by
      have hne : k.val ≠ 1 := fun h => hk (Fin.ext h)
      simp [(hc k).2, hne]) (fun h => absurd (Finset.mem_univ 1) h)]
    rw [Finset.sum_eq_single 11 (fun k _ hk => by simp [hpm 18 k, hk])
      (fun h => absurd (Finset.mem_univ 11) h)]
    rw [(hc 2).1.2, (hc 1).2, hpm 18 11]
    rw [show h3ZornCoordinate X 18 = zornCoord X.b 7 from h3ZornCoord_b_eq X 7,
      show h3ZornCoordinate X 2 = X.α₃ from rfl, show h3ZornCoordinate X 1 = X.α₂ from rfl,
      show h3ZornCoordinate X 11 = zornCoord X.b 0 from h3ZornCoord_b_eq X 0]
    simp; ring
  · intro j
    let j' : Fin 8 := ⟨1 + j.val, by omega⟩
    have hm_eq : (⟨11 + j'.val, by omega⟩ : Fin 27) = ⟨12 + j.val, by omega⟩ :=
      Fin.ext (by dsimp [j']; omega)
    change zornCoord ((f4PeirceExp 1 7 t).1 X).b j' = zornCoord X.b j'
    rw [← h3ZornCoord_b_eq, hm_eq, hf, h3ZornCoordinate_e6RootExp_mul]
    have hs1 : (∑ k : Fin 27, (sparseVal (e6RootSparse 54) ⟨12 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hcm j k).1]
    have hs2 : (∑ k : Fin 27, (sparseVal (e6RootSparse 55) ⟨12 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [(hcm j k).2]
    have hs3 : (∑ k : Fin 27, (sparseVal (sparseMul (e6RootSparse 54) (e6RootSparse 55)) ⟨12 + j.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate X k) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        have hne : (⟨12 + j.val, by omega⟩ : Fin 27) ≠ 18 := fun h => by
          have := congrArg Fin.val h; dsimp at this; omega
        simp [hpm ⟨12 + j.val, by omega⟩ k, hne]
    rw [hs1, hs2, hs3, ← hm_eq, h3ZornCoord_b_eq]; ring

private theorem scalar_peirce_kill_b7 (α₂ α₃ b₀ b₇ : ℝ) (hb₀ : b₀ ≠ 0) (hn : α₂ * α₃ = b₀ * b₇)
    (hsum : α₂ + α₃ = 1) :
    α₂ + (α₃ / b₀) * b₀ = 1 ∧
    α₃ - (α₃ / b₀) * b₀ = 0 ∧
    b₇ + (α₃ / b₀) * (α₃ - α₂) - (α₃ / b₀) ^ 2 * b₀ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · field_simp [hb₀]; exact hsum
  · field_simp [hb₀]; ring
  · have hn' : b₇ = α₂ * α₃ / b₀ := by field_simp [hb₀]; linarith [hn]
    rw [hn']; field_simp [hb₀]; ring

private theorem h3_diag₂_mul_h3_diag₁ : h3_diag₂ * h3_diag₁ = 0 := by
  rw [mul_comm]; exact h3_diag₁_mul_h3_diag₂

private theorem h3_diag₃_mul_h3_diag₁ : h3_diag₃ * h3_diag₁ = 0 := by
  rw [mul_comm]; exact h3_diag₁_mul_h3_diag₃

private theorem h3_diag₃_mul_h3_diag₂ : h3_diag₃ * h3_diag₂ = 0 := by
  rw [mul_comm]; exact h3_diag₂_mul_h3_diag₃

private theorem f4_reduce_diag2_fixing_diag1 (A : H3ZornJordanAut) (h1 : A h3_diag₁ = h3_diag₁) :
    ∃ h ∈ e6F4InChevalley, h.1 h3_diag₁ = h3_diag₁ ∧ h.1 (A h3_diag₂) = h3_diag₂ := by
  have hmul : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Y : H3Zorn ℝ),
      (g₁ * g₂).1 Y = g₁.1 (g₂.1 Y) := fun _ _ _ => rfl
  let e := A h3_diag₂
  have he : isRankOneIdem e := jordanAut_preserves_isRankOneIdem A h3_diag₂_isRankOneIdem
  have he_mul : h3_diag₁ * e = 0 := by
    have hz : A (h3_diag₁ * h3_diag₂) = 0 := by
      rw [h3_diag₁_mul_h3_diag₂]
      change A.toLinearEquiv 0 = 0
      exact map_zero A.toLinearEquiv
    rw [A.map_mul, h1] at hz
    exact hz
  obtain ⟨eα₁, ea, ec⟩ := eq_J23_of_diag1_mul_zero he_mul
  obtain ⟨hd, hhd, hd1, _, _, hda, hdc, hmid⟩ := d4_clear_b_mid e
  have hhd_f4 : hd ∈ e6F4InChevalley := d4Subgroup_le_f4InChevalley hhd
  have hhd_d1 : hd.1 h3_diag₁ = h3_diag₁ := d4Subgroup_fix_diag1 hhd
  obtain ⟨e₁, he₁⟩ : ∃ e₁, hd.1 e = e₁ := ⟨_, rfl⟩
  rw [he₁] at hd1 hda hdc hmid
  have he₁_idem : isRankOneIdem e₁ := he₁ ▸ f4InChevalley_preserves_isRankOneIdem hhd_f4 he
  have he₁_1 : e₁.α₁ = 0 := hd1.trans eα₁
  have he₁_a : e₁.a = 0 := hda ea
  have he₁_c : e₁.c = 0 := hdc ec
  have hstepB : ∃ gb ∈ e6F4InChevalley, gb.1 h3_diag₁ = h3_diag₁ ∧
      (gb.1 e₁).a = 0 ∧ (gb.1 e₁).b = 0 ∧ (gb.1 e₁).c = 0 ∧ (gb.1 e₁).α₁ = 0 := by
    by_cases hb0 : zornCoord e₁.b 0 = 0
    · by_cases hb7 : zornCoord e₁.b 7 = 0
      · refine ⟨1, e6F4InChevalley.one_mem, rfl, he₁_a, ?_, he₁_c, he₁_1⟩
        change e₁.b = 0
        rw [← zornCoord_eq_zero_iff]; intro j
        fin_cases j <;> dsimp
        · exact hb0
        · exact hmid 0
        · exact hmid 1
        · exact hmid 2
        · exact hmid 3
        · exact hmid 4
        · exact hmid 5
        · exact hb7
      · obtain ⟨w1, _, _⟩ := w23_diag_coords e₁
        obtain ⟨wa2, wc2⟩ := w23_preserves_zero_ac he₁_a he₁_c
        obtain ⟨wb0, wb7, wbmid⟩ := w23_b_coords e₁
        obtain ⟨e₂, he₂⟩ : ∃ e₂, w23.1 e₁ = e₂ := ⟨_, rfl⟩
        rw [he₂] at w1 wa2 wc2 wb0 wb7 wbmid
        have he₂_idem : isRankOneIdem e₂ := he₂ ▸ f4InChevalley_preserves_isRankOneIdem w23_mem_f4 he₁_idem
        have he₂_1 : e₂.α₁ = 0 := w1.trans he₁_1
        have he₂_sum : e₂.α₂ + e₂.α₃ = 1 := by linarith [(isRankOneIdem_norm_eq he₂_idem).1, he₂_1]
        have he₂_b0 : zornCoord e₂.b 0 ≠ 0 := by rw [wb0]; exact neg_ne_zero.mpr hb7
        have he₂_mid : ∀ j : Fin 6, zornCoord e₂.b ⟨1 + j.val, by omega⟩ = 0 :=
          fun j => (wbmid j).trans (hmid j)
        have he₂_hn : e₂.α₂ * e₂.α₃ = zornCoord e₂.b 0 * zornCoord e₂.b 7 := by
          rw [(isRankOneIdem_norm_eq he₂_idem).2.1, zorn_norm_of_mid_zero he₂_mid]
        obtain ⟨hs2, hs3, hs7⟩ := scalar_peirce_kill_b7 e₂.α₂ e₂.α₃ (zornCoord e₂.b 0) (zornCoord e₂.b 7)
          he₂_b0 he₂_hn he₂_sum
        let t₁ : ℝ := e₂.α₃ / zornCoord e₂.b 0
        obtain ⟨p1, p2, p3, pa, pc, pb0, pb7, pbmid⟩ := f4Peirce_1_7_coords t₁ wa2 wc2
        obtain ⟨e₃, he₃⟩ : ∃ e₃, (f4PeirceExp 1 7 t₁).1 e₂ = e₃ := ⟨_, rfl⟩
        rw [he₃] at p1 p2 p3 pa pc pb0 pb7 pbmid
        have he₃_1 : e₃.α₁ = 0 := p1.trans he₂_1
        have he₃_2 : e₃.α₂ = 1 := p2.trans hs2
        have he₃_3 : e₃.α₃ = 0 := p3.trans hs3
        have he₃_7 : zornCoord e₃.b 7 = 0 := pb7.trans hs7
        obtain ⟨q1, q2, q3, qa, qc, qb0, qb7, qbmid⟩ :=
          f4Peirce_1_0_coords (zornCoord e₃.b 0) pa pc
        simp only [he₃_7, mul_zero, sub_zero, add_zero, he₃_2, he₃_3] at q1 q2 q3 qb0 qb7
        have hb_fin : ((f4PeirceExp 1 0 (zornCoord e₃.b 0)).1 e₃).b = 0 := by
          rw [← zornCoord_eq_zero_iff]; intro j
          fin_cases j <;> dsimp
          · rw [qb0]; ring
          · exact (qbmid 0).trans ((pbmid 0).trans (he₂_mid 0))
          · exact (qbmid 1).trans ((pbmid 1).trans (he₂_mid 1))
          · exact (qbmid 2).trans ((pbmid 2).trans (he₂_mid 2))
          · exact (qbmid 3).trans ((pbmid 3).trans (he₂_mid 3))
          · exact (qbmid 4).trans ((pbmid 4).trans (he₂_mid 4))
          · exact (qbmid 5).trans ((pbmid 5).trans (he₂_mid 5))
          · exact qb7
        refine ⟨f4PeirceExp 1 0 (zornCoord e₃.b 0) * f4PeirceExp 1 7 t₁ * w23,
          e6F4InChevalley.mul_mem
            (e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 1 0 _) (f4PeirceExp_mem_f4 1 7 _)) w23_mem_f4,
          ?_, ?_, ?_, ?_, ?_⟩
        · rw [hmul, hmul, w23_fix_diag1, f4Peirce_1_7_fix_diag1, f4Peirce_1_0_fix_diag1]
        · rw [hmul, hmul, he₂, he₃]; exact qa
        · rw [hmul, hmul, he₂, he₃]; exact hb_fin
        · rw [hmul, hmul, he₂, he₃]; exact qc
        · rw [hmul, hmul, he₂, he₃, q1, he₃_1]
    · have he₁_sum : e₁.α₂ + e₁.α₃ = 1 := by linarith [(isRankOneIdem_norm_eq he₁_idem).1, he₁_1]
      have he₁_hn : e₁.α₂ * e₁.α₃ = zornCoord e₁.b 0 * zornCoord e₁.b 7 := by
        rw [(isRankOneIdem_norm_eq he₁_idem).2.1, zorn_norm_of_mid_zero hmid]
      obtain ⟨hs2, hs3, hs7⟩ := scalar_peirce_kill_b7 e₁.α₂ e₁.α₃ (zornCoord e₁.b 0) (zornCoord e₁.b 7)
        hb0 he₁_hn he₁_sum
      let t₁ : ℝ := e₁.α₃ / zornCoord e₁.b 0
      obtain ⟨p1, p2, p3, pa, pc, pb0, pb7, pbmid⟩ := f4Peirce_1_7_coords t₁ he₁_a he₁_c
      obtain ⟨e₃, he₃⟩ : ∃ e₃, (f4PeirceExp 1 7 t₁).1 e₁ = e₃ := ⟨_, rfl⟩
      rw [he₃] at p1 p2 p3 pa pc pb0 pb7 pbmid
      have he₃_1 : e₃.α₁ = 0 := p1.trans he₁_1
      have he₃_2 : e₃.α₂ = 1 := p2.trans hs2
      have he₃_3 : e₃.α₃ = 0 := p3.trans hs3
      have he₃_7 : zornCoord e₃.b 7 = 0 := pb7.trans hs7
      obtain ⟨q1, q2, q3, qa, qc, qb0, qb7, qbmid⟩ :=
        f4Peirce_1_0_coords (zornCoord e₃.b 0) pa pc
      simp only [he₃_7, mul_zero, sub_zero, add_zero, he₃_2, he₃_3] at q1 q2 q3 qb0 qb7
      have hb_fin : ((f4PeirceExp 1 0 (zornCoord e₃.b 0)).1 e₃).b = 0 := by
        rw [← zornCoord_eq_zero_iff]; intro j
        fin_cases j <;> dsimp
        · rw [qb0]; ring
        · exact (qbmid 0).trans ((pbmid 0).trans (hmid 0))
        · exact (qbmid 1).trans ((pbmid 1).trans (hmid 1))
        · exact (qbmid 2).trans ((pbmid 2).trans (hmid 2))
        · exact (qbmid 3).trans ((pbmid 3).trans (hmid 3))
        · exact (qbmid 4).trans ((pbmid 4).trans (hmid 4))
        · exact (qbmid 5).trans ((pbmid 5).trans (hmid 5))
        · exact qb7
      refine ⟨f4PeirceExp 1 0 (zornCoord e₃.b 0) * f4PeirceExp 1 7 t₁,
        e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 1 0 _) (f4PeirceExp_mem_f4 1 7 _),
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [hmul, f4Peirce_1_7_fix_diag1, f4Peirce_1_0_fix_diag1]
      · rw [hmul, he₃]; exact qa
      · rw [hmul, he₃]; exact hb_fin
      · rw [hmul, he₃]; exact qc
      · rw [hmul, he₃, q1, he₃_1]
  obtain ⟨gb, hgb, hgb_d1, gba, gbb, gbc, gb1⟩ := hstepB
  obtain ⟨ef, hef⟩ : ∃ ef, gb.1 e₁ = ef := ⟨_, rfl⟩
  rw [hef] at gba gbb gbc gb1
  have hef_idem : isRankOneIdem ef := hef ▸ f4InChevalley_preserves_isRankOneIdem hgb he₁_idem
  have hnorm0 : ZornVectorMatrix.norm (0 : ZornVectorMatrix ℝ) = 0 := by
    simp [ZornVectorMatrix.norm, ZornVectorMatrix.zero, ZornVec3.dot]
  have hprod : ef.α₂ * ef.α₃ = 0 := by
    rw [(isRankOneIdem_norm_eq hef_idem).2.1, gbb, hnorm0]
  have hsum : ef.α₂ + ef.α₃ = 1 := by linarith [(isRankOneIdem_norm_eq hef_idem).1, gb1]
  rcases mul_eq_zero.mp hprod with h20 | h30
  · have h31 : ef.α₃ = 1 := by linarith [h20, hsum]
    obtain ⟨w1, w2, w3⟩ := w23_diag_coords ef
    obtain ⟨wa3, wc3⟩ := w23_preserves_zero_ac gba gbc
    obtain ⟨wb0, wb7, wbmid⟩ := w23_b_coords ef
    have hbf : (w23.1 ef).b = 0 := by
      have hbz := (zornCoord_eq_zero_iff ef.b).mpr gbb
      rw [← zornCoord_eq_zero_iff]; intro j
      fin_cases j <;> dsimp
      · rw [wb0, hbz 7, neg_zero]
      · exact (wbmid 0).trans (hbz 1)
      · exact (wbmid 1).trans (hbz 2)
      · exact (wbmid 2).trans (hbz 3)
      · exact (wbmid 3).trans (hbz 4)
      · exact (wbmid 4).trans (hbz 5)
      · exact (wbmid 5).trans (hbz 6)
      · rw [wb7, hbz 0, neg_zero]
    refine ⟨w23 * gb * hd,
      e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem w23_mem_f4 hgb) hhd_f4, ?_, ?_⟩
    · rw [hmul, hmul, hhd_d1, hgb_d1, w23_fix_diag1]
    · rw [hmul, hmul, he₁, hef]
      apply ext_h3
      · exact w1.trans gb1
      · exact w2.trans h31
      · exact w3.trans h20
      · exact wa3
      · exact hbf
      · exact wc3
  · have h21 : ef.α₂ = 1 := by linarith [h30, hsum]
    refine ⟨gb * hd, e6F4InChevalley.mul_mem hgb hhd_f4, ?_, ?_⟩
    · rw [hmul, hhd_d1, hgb_d1]
    · rw [hmul, he₁, hef]
      apply ext_h3
      · exact gb1
      · exact h21
      · exact h30
      · exact gba
      · exact gbb
      · exact gbc

/-! ### Step B3: Peirce Space Preservation, `J₁₂`/`J₂₃` Unit Normalization, and Triality -/

private theorem h3ZornCoordinate_e6TorusElt (i : Fin 6) (t : ℝˣ) (X : H3Zorn ℝ) (m : Fin 27) :
    h3ZornCoordinate ((e6TorusElt i t).1 X) m =
      (t : ℝ) ^ (h3zornWeight m i) * h3ZornCoordinate X m := by
  have hrep : X = ∑ k : Fin 27, h3ZornCoordinate X k • h3ZornBasis k :=
    (h3ZornBasis.sum_repr X).symm
  conv_lhs => rw [hrep, map_sum]
  change h3ZornCoordinateLM (∑ k : Fin 27, (e6TorusElt i t).1 (h3ZornCoordinate X k • h3ZornBasis k)) m = _
  rw [map_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single m]
  · rw [map_smul]
    change h3ZornCoordinate (h3ZornCoordinate X m • (e6TorusElt i t).1 (h3ZornBasis m)) m = _
    rw [h3ZornCoordinate_smul, e6TorusElt_apply_basis, h3ZornCoordinate_smul,
      h3ZornCoordinate_basis_self, if_pos rfl, Units.val_zpow_eq_zpow_val]
    ring
  · intro k _ hk
    rw [map_smul]
    change h3ZornCoordinate (h3ZornCoordinate X k • (e6TorusElt i t).1 (h3ZornBasis k)) m = 0
    rw [h3ZornCoordinate_smul, e6TorusElt_apply_basis, h3ZornCoordinate_smul]
    have hkm : h3ZornCoordinate (h3ZornBasis k) m = 0 := by
      simp [h3ZornCoordinate_basis_self, hk]
    rw [hkm, mul_zero, mul_zero]
  · intro hm; exact absurd (Finset.mem_univ m) hm

private theorem h3Zorn_diag_sum_one : h3_diag₁ + h3_diag₂ + h3_diag₃ = (1 : H3Zorn ℝ) := by
  apply ext_h3 <;> simp [h3_diag₁, h3_diag₂, h3_diag₃, add_readback, one_readback,
    ZornVectorMatrix.add_zero]

private theorem eq_J12_of_diag_action {Y : H3Zorn ℝ}
    (h1 : h3_diag₁ * Y = (1 / 2 : ℝ) • Y) (h3 : h3_diag₃ * Y = 0) :
    Y = embedJ12 Y.a := by
  have hdec : Y = Y.α₁ • h3_diag₁ + Y.α₂ • h3_diag₂ + Y.α₃ • h3_diag₃ +
      embedJ12 Y.a + embedJ23 Y.b + embedJ31 Y.c := by
    apply ext_h3 <;> simp [h3_diag₁, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31,
      add_readback, smul_readback, ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]
  have hm3 : h3_diag₃ * Y = Y.α₃ • h3_diag₃ + (1 / 2 : ℝ) • embedJ23 Y.b + (1 / 2 : ℝ) • embedJ31 Y.c := by
    conv_lhs => rw [hdec]
    simp only [mul_add, mul_smul_comm, h3_diag₃_mul_h3_diag₁, h3_diag₃_mul_h3_diag₂,
      h3_diag₃_mul_h3_diag₃, h3_diag₃_mul_embedJ12, h3_diag₃_mul_embedJ23, h3_diag₃_mul_embedJ31,
      smul_zero, zero_add, add_zero]
  rw [hm3] at h3
  have hα₃ : Y.α₃ = 0 := by
    have h0 := congrArg H3Zorn.α₃ h3
    simpa [h3_diag₃, embedJ23, embedJ31, add_readback, smul_readback] using h0
  have hb : Y.b = 0 := by
    have h0 := congrArg H3Zorn.b h3
    have h0' : ZornVectorMatrix.smul (1 / 2 : ℝ) Y.b = 0 := by
      simpa [h3_diag₃, embedJ23, embedJ31, add_readback, smul_readback, ZornVectorMatrix.smul_zero,
        ZornVectorMatrix.add_zero] using h0
    rw [← zornCoord_eq_zero_iff]; intro i
    have hi := congrArg (fun u => zornCoord u i) h0'
    have hsm : zornCoord (ZornVectorMatrix.smul (1 / 2 : ℝ) Y.b) i = (1 / 2 : ℝ) * zornCoord Y.b i := by
      fin_cases i <;> rfl
    rw [hsm] at hi
    have hz : zornCoord (0 : ZornVectorMatrix ℝ) i = 0 := by fin_cases i <;> rfl
    rw [hz] at hi
    have hi0 : zornCoord Y.b i = 0 := (mul_eq_zero.mp hi).resolve_left (by norm_num)
    rw [hi0]
  have hc : Y.c = 0 := by
    have h0 := congrArg H3Zorn.c h3
    have h0' : ZornVectorMatrix.smul (1 / 2 : ℝ) Y.c = 0 := by
      simpa [h3_diag₃, embedJ23, embedJ31, add_readback, smul_readback, ZornVectorMatrix.smul_zero,
        ZornVectorMatrix.add_zero] using h0
    rw [← zornCoord_eq_zero_iff]; intro i
    have hi := congrArg (fun u => zornCoord u i) h0'
    have hsm : zornCoord (ZornVectorMatrix.smul (1 / 2 : ℝ) Y.c) i = (1 / 2 : ℝ) * zornCoord Y.c i := by
      fin_cases i <;> rfl
    rw [hsm] at hi
    have hz : zornCoord (0 : ZornVectorMatrix ℝ) i = 0 := by fin_cases i <;> rfl
    rw [hz] at hi
    have hi0 : zornCoord Y.c i = 0 := (mul_eq_zero.mp hi).resolve_left (by norm_num)
    rw [hi0]
  have hm1 : h3_diag₁ * Y = Y.α₁ • h3_diag₁ + (1 / 2 : ℝ) • embedJ12 Y.a + (1 / 2 : ℝ) • embedJ31 Y.c := by
    conv_lhs => rw [hdec]
    simp only [mul_add, mul_smul_comm, h3_diag₁_mul_h3_diag₁, h3_diag₁_mul_h3_diag₂,
      h3_diag₁_mul_h3_diag₃, h3_diag₁_mul_embedJ12, h3_diag₁_mul_embedJ23, h3_diag₁_mul_embedJ31,
      smul_zero, add_zero]
  rw [hm1] at h1
  have hα₁ : Y.α₁ = 0 := by
    have h0 := congrArg H3Zorn.α₁ h1
    have h0' : Y.α₁ = (1 / 2 : ℝ) * Y.α₁ := by
      simpa [h3_diag₁, embedJ12, embedJ31, add_readback, smul_readback] using h0
    linarith [h0']
  have hα₂ : Y.α₂ = 0 := by
    have h0 := congrArg H3Zorn.α₂ h1
    have h0' : (0 : ℝ) = (1 / 2 : ℝ) * Y.α₂ := by
      simpa [h3_diag₁, embedJ12, embedJ31, add_readback, smul_readback] using h0
    linarith [h0']
  apply ext_h3 <;> simp [embedJ12, hα₁, hα₂, hα₃, hb, hc]

private theorem eq_J23_of_diag_action {Y : H3Zorn ℝ}
    (h1 : h3_diag₁ * Y = 0) (h2 : h3_diag₂ * Y = (1 / 2 : ℝ) • Y) :
    Y = embedJ23 Y.b := by
  have hdec : Y = Y.α₁ • h3_diag₁ + Y.α₂ • h3_diag₂ + Y.α₃ • h3_diag₃ +
      embedJ12 Y.a + embedJ23 Y.b + embedJ31 Y.c := by
    apply ext_h3 <;> simp [h3_diag₁, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31,
      add_readback, smul_readback, ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]
  obtain ⟨hα₁, ha, hc⟩ := eq_J23_of_diag1_mul_zero h1
  have hm2 : h3_diag₂ * Y = Y.α₂ • h3_diag₂ + (1 / 2 : ℝ) • embedJ12 Y.a + (1 / 2 : ℝ) • embedJ23 Y.b := by
    conv_lhs => rw [hdec]
    simp only [mul_add, mul_smul_comm, h3_diag₂_mul_h3_diag₁, h3_diag₂_mul_h3_diag₂,
      h3_diag₂_mul_h3_diag₃, h3_diag₂_mul_embedJ12, h3_diag₂_mul_embedJ23, h3_diag₂_mul_embedJ31,
      smul_zero, zero_add, add_zero]
  rw [hm2] at h2
  have hα₂ : Y.α₂ = 0 := by
    have h0 := congrArg H3Zorn.α₂ h2
    have h0' : Y.α₂ = (1 / 2 : ℝ) * Y.α₂ := by
      simpa [h3_diag₂, embedJ12, embedJ23, add_readback, smul_readback] using h0
    linarith [h0']
  have hα₃ : Y.α₃ = 0 := by
    have h0 := congrArg H3Zorn.α₃ h2
    have h0' : (0 : ℝ) = (1 / 2 : ℝ) * Y.α₃ := by
      simpa [h3_diag₂, embedJ12, embedJ23, add_readback, smul_readback] using h0
    linarith [h0']
  apply ext_h3 <;> simp [embedJ23, hα₁, hα₂, hα₃, ha, hc]

private theorem eq_J31_of_diag_action {Y : H3Zorn ℝ}
    (h2 : h3_diag₂ * Y = 0) (h3 : h3_diag₃ * Y = (1 / 2 : ℝ) • Y) :
    Y = embedJ31 Y.c := by
  have hdec : Y = Y.α₁ • h3_diag₁ + Y.α₂ • h3_diag₂ + Y.α₃ • h3_diag₃ +
      embedJ12 Y.a + embedJ23 Y.b + embedJ31 Y.c := by
    apply ext_h3 <;> simp [h3_diag₁, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31,
      add_readback, smul_readback, ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]
  have hm2 : h3_diag₂ * Y = Y.α₂ • h3_diag₂ + (1 / 2 : ℝ) • embedJ12 Y.a + (1 / 2 : ℝ) • embedJ23 Y.b := by
    conv_lhs => rw [hdec]
    simp only [mul_add, mul_smul_comm, h3_diag₂_mul_h3_diag₁, h3_diag₂_mul_h3_diag₂,
      h3_diag₂_mul_h3_diag₃, h3_diag₂_mul_embedJ12, h3_diag₂_mul_embedJ23, h3_diag₂_mul_embedJ31,
      smul_zero, zero_add, add_zero]
  rw [hm2] at h2
  have hα₂ : Y.α₂ = 0 := by
    have h0 := congrArg H3Zorn.α₂ h2
    simpa [h3_diag₂, embedJ12, embedJ23, add_readback, smul_readback] using h0
  have ha : Y.a = 0 := by
    have h0 := congrArg H3Zorn.a h2
    have h0' : ZornVectorMatrix.smul (1 / 2 : ℝ) Y.a = 0 := by
      simpa [h3_diag₂, embedJ12, embedJ23, add_readback, smul_readback, ZornVectorMatrix.smul_zero,
        ZornVectorMatrix.add_zero] using h0
    rw [← zornCoord_eq_zero_iff]; intro i
    have hi := congrArg (fun u => zornCoord u i) h0'
    have hsm : zornCoord (ZornVectorMatrix.smul (1 / 2 : ℝ) Y.a) i = (1 / 2 : ℝ) * zornCoord Y.a i := by
      fin_cases i <;> rfl
    rw [hsm] at hi
    have hz : zornCoord (0 : ZornVectorMatrix ℝ) i = 0 := by fin_cases i <;> rfl
    rw [hz] at hi
    have hi0 : zornCoord Y.a i = 0 := (mul_eq_zero.mp hi).resolve_left (by norm_num)
    rw [hi0]
  have hb : Y.b = 0 := by
    have h0 := congrArg H3Zorn.b h2
    have h0' : ZornVectorMatrix.smul (1 / 2 : ℝ) Y.b = 0 := by
      simpa [h3_diag₂, embedJ12, embedJ23, add_readback, smul_readback, ZornVectorMatrix.smul_zero,
        ZornVectorMatrix.add_zero] using h0
    rw [← zornCoord_eq_zero_iff]; intro i
    have hi := congrArg (fun u => zornCoord u i) h0'
    have hsm : zornCoord (ZornVectorMatrix.smul (1 / 2 : ℝ) Y.b) i = (1 / 2 : ℝ) * zornCoord Y.b i := by
      fin_cases i <;> rfl
    rw [hsm] at hi
    have hz : zornCoord (0 : ZornVectorMatrix ℝ) i = 0 := by fin_cases i <;> rfl
    rw [hz] at hi
    have hi0 : zornCoord Y.b i = 0 := (mul_eq_zero.mp hi).resolve_left (by norm_num)
    rw [hi0]
  have hm3 : h3_diag₃ * Y = Y.α₃ • h3_diag₃ + (1 / 2 : ℝ) • embedJ23 Y.b + (1 / 2 : ℝ) • embedJ31 Y.c := by
    conv_lhs => rw [hdec]
    simp only [mul_add, mul_smul_comm, h3_diag₃_mul_h3_diag₁, h3_diag₃_mul_h3_diag₂,
      h3_diag₃_mul_h3_diag₃, h3_diag₃_mul_embedJ12, h3_diag₃_mul_embedJ23, h3_diag₃_mul_embedJ31,
      smul_zero, zero_add, add_zero]
  rw [hm3] at h3
  have hα₃ : Y.α₃ = 0 := by
    have h0 := congrArg H3Zorn.α₃ h3
    have h0' : Y.α₃ = (1 / 2 : ℝ) * Y.α₃ := by
      simpa [h3_diag₃, embedJ23, embedJ31, add_readback, smul_readback] using h0
    linarith [h0']
  have hα₁ : Y.α₁ = 0 := by
    have h0 := congrArg H3Zorn.α₁ h3
    have h0' : (0 : ℝ) = (1 / 2 : ℝ) * Y.α₁ := by
      simpa [h3_diag₃, embedJ23, embedJ31, add_readback, smul_readback] using h0
    linarith [h0']
  apply ext_h3 <;> simp [embedJ31, hα₁, hα₂, hα₃, ha, hb]

private theorem peirce_spaces_preserved_of_fix_diags (A : H3ZornJordanAut)
    (h1 : A h3_diag₁ = h3_diag₁) (h2 : A h3_diag₂ = h3_diag₂) :
    A h3_diag₃ = h3_diag₃ ∧
    (∀ u : ZornVectorMatrix ℝ, A (embedJ12 u) = embedJ12 (A (embedJ12 u)).a) ∧
    (∀ u : ZornVectorMatrix ℝ, A (embedJ23 u) = embedJ23 (A (embedJ23 u)).b) ∧
    (∀ u : ZornVectorMatrix ℝ, A (embedJ31 u) = embedJ31 (A (embedJ31 u)).c) := by
  have h1' : A.toLinearEquiv h3_diag₁ = h3_diag₁ := h1
  have h2' : A.toLinearEquiv h3_diag₂ = h3_diag₂ := h2
  have hmul (x y : H3Zorn ℝ) :
      A.toLinearEquiv (x * y) = A.toLinearEquiv x * A.toLinearEquiv y := by
    change A (x * y) = A x * A y
    exact A.map_mul x y
  have hOne : A.toLinearEquiv 1 = 1 := by
    change A 1 = 1
    exact A.map_one
  have h3' : A.toLinearEquiv h3_diag₃ = h3_diag₃ := by
    have hs := congrArg A.toLinearEquiv h3Zorn_diag_sum_one
    rw [map_add, map_add, h1', h2', hOne] at hs
    have hs' : h3_diag₁ + h3_diag₂ + A.toLinearEquiv h3_diag₃ =
        h3_diag₁ + h3_diag₂ + h3_diag₃ :=
      hs.trans h3Zorn_diag_sum_one.symm
    exact add_left_cancel hs'
  have h3 : A h3_diag₃ = h3_diag₃ := h3'
  refine ⟨h3, ?_, ?_, ?_⟩
  · intro u
    apply eq_J12_of_diag_action
    · have hm := congrArg A.toLinearEquiv (h3_diag₁_mul_embedJ12 u)
      rw [hmul, map_smul, h1'] at hm
      exact hm
    · have hm := congrArg A.toLinearEquiv (h3_diag₃_mul_embedJ12 u)
      rw [hmul, map_zero, h3'] at hm
      exact hm
  · intro u
    apply eq_J23_of_diag_action
    · have hm := congrArg A.toLinearEquiv (h3_diag₁_mul_embedJ23 u)
      rw [hmul, map_zero, h1'] at hm
      exact hm
    · have hm := congrArg A.toLinearEquiv (h3_diag₂_mul_embedJ23 u)
      rw [hmul, map_smul, h2'] at hm
      exact hm
  · intro u
    apply eq_J31_of_diag_action
    · have hm := congrArg A.toLinearEquiv (h3_diag₂_mul_embedJ31 u)
      rw [hmul, map_zero, h2'] at hm
      exact hm
    · have hm := congrArg A.toLinearEquiv (h3_diag₃_mul_embedJ31 u)
      rw [hmul, map_smul, h3'] at hm
      exact hm

private theorem d4Subgroup_fix_diags {g : h3zornReducedStructureGroup} (hg : g ∈ d4Subgroup) :
    g.1 h3_diag₁ = h3_diag₁ ∧ g.1 h3_diag₂ = h3_diag₂ ∧ g.1 h3_diag₃ = h3_diag₃ := by
  refine ⟨d4Subgroup_fix_diag1 hg, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, ha, hb, hc⟩ := d4Subgroup_preserves_blocks hg h3_diag₂
    apply ext_h3 <;> [exact h1; exact h2; exact h3; exact ha rfl; exact hb rfl; exact hc rfl]
  · obtain ⟨h1, h2, h3, ha, hb, hc⟩ := d4Subgroup_preserves_blocks hg h3_diag₃
    apply ext_h3 <;> [exact h1; exact h2; exact h3; exact ha rfl; exact hb rfl; exact hc rfl]

private theorem zornBilin_self_eq_two_mul_norm (u : ZornVectorMatrix ℝ) :
    zornBilin u u = 2 * ZornVectorMatrix.norm u := by
  simp [zornBilin, ZornVectorMatrix.norm, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
    ZornVectorMatrix.conj, ZornVec3.dot]
  have hsum : (∑ x, u.w x * u.v x) = ∑ x, u.v x * u.w x := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  ring

private theorem zorn_norm_one_eq :
    ZornVectorMatrix.norm (ZornVectorMatrix.one : ZornVectorMatrix ℝ) = 1 := by
  simp [ZornVectorMatrix.norm, ZornVectorMatrix.one, ZornVec3.dot,
    Fin.sum_univ_three]

private theorem f4_reduce_j12_one_fixing_diags (A : H3ZornJordanAut)
    (h1 : A h3_diag₁ = h3_diag₁) (h2 : A h3_diag₂ = h3_diag₂) :
    ∃ h ∈ e6F4InChevalley,
      h.1 h3_diag₁ = h3_diag₁ ∧ h.1 h3_diag₂ = h3_diag₂ ∧ h.1 h3_diag₃ = h3_diag₃ ∧
      h.1 (A (embedJ12 1)) = embedJ12 1 := by
  have hmul : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Y : H3Zorn ℝ),
      (g₁ * g₂).1 Y = g₁.1 (g₂.1 Y) := fun _ _ _ => rfl
  have hA_mul (x y : H3Zorn ℝ) :
      A.toLinearEquiv (x * y) = A.toLinearEquiv x * A.toLinearEquiv y := by
    change A (x * y) = A x * A y
    exact A.map_mul x y
  obtain ⟨h3, hj12, _, _⟩ := peirce_spaces_preserved_of_fix_diags A h1 h2
  let u := (A (embedJ12 1)).a
  have hAu : A (embedJ12 1) = embedJ12 u := hj12 1
  have hAu' : A.toLinearEquiv (embedJ12 1) = embedJ12 u := hAu
  have h1' : A.toLinearEquiv h3_diag₁ = h3_diag₁ := h1
  have h2' : A.toLinearEquiv h3_diag₂ = h3_diag₂ := h2
  have hnorm_u : ZornVectorMatrix.norm u = 1 := by
    have hm := congrArg A.toLinearEquiv (embedJ12_mul_embedJ12 1 1)
    rw [hA_mul, hAu', embedJ12_mul_embedJ12, map_smul, map_add,
      h1', h2'] at hm
    have hα₁ := congrArg H3Zorn.α₁ hm
    have hsc : (1 / 2 : ℝ) * zornBilin u u = (1 / 2 : ℝ) * zornBilin (1 : ZornVectorMatrix ℝ) 1 := by
      simpa [h3_diag₁, h3_diag₂, add_readback, smul_readback] using hα₁
    have hnorm_one : ZornVectorMatrix.norm (1 : ZornVectorMatrix ℝ) = 1 := by
      change ZornVectorMatrix.norm ZornVectorMatrix.one = 1
      exact zorn_norm_one_eq
    rw [zornBilin_self_eq_two_mul_norm, zornBilin_self_eq_two_mul_norm,
      hnorm_one] at hsc
    linarith [hsc]
  obtain ⟨hd, hhd, hd1, hd2, hd3, hmid, _⟩ := d4_clear_a_mid (embedJ12 u)
  have hhd_f4 : hd ∈ e6F4InChevalley := d4Subgroup_le_f4InChevalley hhd
  obtain ⟨hd_d1, hd_d2, hd_d3⟩ := d4Subgroup_fix_diags hhd
  let A_d : H3ZornJordanAut := h3zornJordanAutOfReducedStructure hd hhd_f4.2
  have hAd_eq : ∀ Y, A_d Y = hd.1 Y := fun _ => rfl
  have hAd_eq' (Y : H3Zorn ℝ) : A_d.toLinearEquiv Y = hd.1 Y := hAd_eq Y
  have hAd_1 : A_d h3_diag₁ = h3_diag₁ := hd_d1
  have hAd_2 : A_d h3_diag₂ = h3_diag₂ := hd_d2
  have hAd_1' : A_d.toLinearEquiv h3_diag₁ = h3_diag₁ := hAd_1
  have hAd_2' : A_d.toLinearEquiv h3_diag₂ = h3_diag₂ := hAd_2
  obtain ⟨_, hAd12, _, _⟩ := peirce_spaces_preserved_of_fix_diags A_d hAd_1 hAd_2
  let u₁ := (hd.1 (embedJ12 u)).a
  have hdu₁ : hd.1 (embedJ12 u) = embedJ12 u₁ := hAd12 u
  have hdu₁' : A_d.toLinearEquiv (embedJ12 u) = embedJ12 u₁ := by
    rw [hAd_eq', hdu₁]
  have hAd_mul (x y : H3Zorn ℝ) :
      A_d.toLinearEquiv (x * y) = A_d.toLinearEquiv x * A_d.toLinearEquiv y := by
    change A_d (x * y) = A_d x * A_d y
    exact A_d.map_mul x y
  have hnorm_u₁ : ZornVectorMatrix.norm u₁ = 1 := by
    have hm := congrArg A_d.toLinearEquiv (embedJ12_mul_embedJ12 u u)
    rw [hAd_mul, hdu₁', embedJ12_mul_embedJ12, map_smul, map_add,
      hAd_1', hAd_2'] at hm
    have hα₁ := congrArg H3Zorn.α₁ hm
    have hsc : (1 / 2 : ℝ) * zornBilin u₁ u₁ = (1 / 2 : ℝ) * zornBilin u u := by
      simpa [h3_diag₁, h3_diag₂, add_readback, smul_readback] using hα₁
    rw [zornBilin_self_eq_two_mul_norm, zornBilin_self_eq_two_mul_norm, hnorm_u] at hsc
    linarith [hsc]
  have hprod : zornCoord u₁ 0 * zornCoord u₁ 7 = 1 := by
    rw [← zorn_norm_of_mid_zero hmid, hnorm_u₁]
  have hu0_ne : zornCoord u₁ 0 ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hprod; exact zero_ne_one hprod
  let v : ℝˣ := Units.mk0 (zornCoord u₁ 0) hu0_ne
  let t := e6TorusElt 0 v⁻¹ * e6TorusElt 5 v⁻¹
  have ht_che : t ∈ e6ChevalleySubgroup :=
    e6ChevalleySubgroup.mul_mem (e6TorusElt_mem_chevalley 0 _) (e6TorusElt_mem_chevalley 5 _)
  have ht_diag : t.1 h3_diag₁ = h3_diag₁ ∧ t.1 h3_diag₂ = h3_diag₂ ∧ t.1 h3_diag₃ = h3_diag₃ := by
    have hc₁ : ∀ m, h3ZornCoordinate h3_diag₁ m = if m = 0 then 1 else 0 := by
      intro m; rw [← h3ZornBasis_zero, h3ZornCoordinate_basis_self]; simp [eq_comm]
    have hc₂ : ∀ m, h3ZornCoordinate h3_diag₂ m = if m = 1 then 1 else 0 := by
      intro m; rw [← h3ZornBasis_one, h3ZornCoordinate_basis_self]; simp [eq_comm]
    have hc₃ : ∀ m, h3ZornCoordinate h3_diag₃ m = if m = 2 then 1 else 0 := by
      intro m; rw [← h3ZornBasis_two, h3ZornCoordinate_basis_self]; simp [eq_comm]
    refine ⟨?_, ?_, ?_⟩
    · apply h3Zorn_ext_coord; intro m
      dsimp only [t]
      rw [hmul, h3ZornCoordinate_e6TorusElt, h3ZornCoordinate_e6TorusElt]
      rw [hc₁]
      by_cases hm : m = 0
      · subst m
        rw [show h3zornWeight 0 0 = 1 by rfl,
          show h3zornWeight 0 5 = -1 by rfl]
        simp [zpow_neg_one]
      · simp [hm]
    · apply h3Zorn_ext_coord; intro m
      dsimp only [t]
      rw [hmul, h3ZornCoordinate_e6TorusElt, h3ZornCoordinate_e6TorusElt]
      rw [hc₂]
      by_cases hm : m = 1
      · subst m
        rw [show h3zornWeight 1 0 = 0 by rfl,
          show h3zornWeight 1 5 = 0 by rfl]
        simp
      · simp [hm]
    · apply h3Zorn_ext_coord; intro m
      dsimp only [t]
      rw [hmul, h3ZornCoordinate_e6TorusElt, h3ZornCoordinate_e6TorusElt]
      rw [hc₃]
      by_cases hm : m = 2
      · subst m
        rw [show h3zornWeight 2 0 = -1 by rfl,
          show h3zornWeight 2 5 = 1 by rfl]
        simp [zpow_neg_one]
      · simp [hm]
  have ht_one : t.1 1 = 1 := by
    rw [← h3Zorn_diag_sum_one, t.1.map_add, t.1.map_add, ht_diag.1, ht_diag.2.1, ht_diag.2.2]
  have ht_f4 : t ∈ e6F4InChevalley := ⟨ht_che, ht_one⟩
  have ht_j12 : t.1 (embedJ12 u₁) = embedJ12 1 := by
    apply h3Zorn_ext_coord; intro m
    dsimp only [t]
    rw [hmul, h3ZornCoordinate_e6TorusElt, h3ZornCoordinate_e6TorusElt]
    have hw3 : h3zornWeight 3 0 = 1 ∧ h3zornWeight 3 5 = 0 := ⟨rfl, rfl⟩
    have hw10 : h3zornWeight 10 0 = 0 ∧ h3zornWeight 10 5 = -1 := ⟨rfl, rfl⟩
    have hu1_7 : zornCoord u₁ 7 = (zornCoord u₁ 0)⁻¹ := by
      have : zornCoord u₁ 0 * zornCoord u₁ 7 = 1 := hprod
      field_simp [hu0_ne]; linarith [this]
    fin_cases m <;> dsimp
    · simp [embedJ12, h3ZornCoordinate]
    · simp [embedJ12, h3ZornCoordinate]
    · simp [embedJ12, h3ZornCoordinate]
    · change (v⁻¹ : ℝ) ^ (h3zornWeight 3 0) * ((v⁻¹ : ℝ) ^ (h3zornWeight 3 5) *
          zornCoord u₁ 0) = zornCoord (1 : ZornVectorMatrix ℝ) 0
      rw [hw3.1, hw3.2, zpow_one, zpow_zero, one_mul]
      have hv : (v : ℝ) = zornCoord u₁ 0 := rfl
      simp [hv, inv_mul_cancel₀ hu0_ne]; rfl
    · have hm4 := hmid 0
      have hv0 : u₁.v 0 = 0 := by simpa [zornCoord] using hm4
      simp [embedJ12, h3ZornCoordinate, ZornVectorMatrix.one, hv0] <;> rfl
    · have hm5 := hmid 1
      have hv1 : u₁.v 1 = 0 := by simpa [zornCoord] using hm5
      simp [embedJ12, h3ZornCoordinate, ZornVectorMatrix.one, hv1] <;> rfl
    · have hm6 := hmid 2
      have hv2 : u₁.v 2 = 0 := by simpa [zornCoord] using hm6
      simp [embedJ12, h3ZornCoordinate, ZornVectorMatrix.one, hv2] <;> rfl
    · have hm7 := hmid 3
      have hw0 : u₁.w 0 = 0 := by simpa [zornCoord] using hm7
      simp [embedJ12, h3ZornCoordinate, ZornVectorMatrix.one, hw0] <;> rfl
    · have hm8 := hmid 4
      have hw1 : u₁.w 1 = 0 := by simpa [zornCoord] using hm8
      simp [embedJ12, h3ZornCoordinate, ZornVectorMatrix.one, hw1] <;> rfl
    · have hm9 := hmid 5
      have hw2 : u₁.w 2 = 0 := by simpa [zornCoord] using hm9
      simp [embedJ12, h3ZornCoordinate, ZornVectorMatrix.one, hw2] <;> rfl
    · change (v⁻¹ : ℝ) ^ (h3zornWeight 10 0) * ((v⁻¹ : ℝ) ^ (h3zornWeight 10 5) *
          zornCoord u₁ 7) = zornCoord (1 : ZornVectorMatrix ℝ) 7
      rw [hw10.1, hw10.2, zpow_zero, zpow_neg_one, one_mul, inv_inv, hu1_7]
      have hv : (v : ℝ) = zornCoord u₁ 0 := rfl
      simp [hv, mul_inv_cancel₀ hu0_ne]; rfl
    all_goals simp [embedJ12, h3ZornCoordinate, ZornVectorMatrix.zero]
  refine ⟨t * hd, e6F4InChevalley.mul_mem ht_f4 hhd_f4, ?_, ?_, ?_, ?_⟩
  · rw [hmul, hd_d1, ht_diag.1]
  · rw [hmul, hd_d2, ht_diag.2.1]
  · rw [hmul, hd_d3, ht_diag.2.2]
  · rw [hmul, hAu, hdu₁, ht_j12]

private def sl4Root : Fin 6 → Fin 72
  | 0 => 21
  | 1 => 19
  | 2 => 18
  | 3 => 11
  | 4 => 7
  | 5 => 6

private theorem sl4Root_fix_check :
    (List.finRange 6).all (fun i =>
      decide ((sl4Root i).val < 24) &&
      (List.finRange 27).all (fun m =>
        sparseVal (e6RootSparse (sl4Root i)) m 3 +
        sparseVal (e6RootSparse (sl4Root i)) m 10 == 0)) = true := by
  decide

private theorem sl4Root_mem_fix_j12 (i : Fin 6) (t : ℝ) :
    e6RootExp (sl4Root i) t ∈ e6F4InChevalley ∧
    (e6RootExp (sl4Root i) t).1 h3_diag₁ = h3_diag₁ ∧
    (e6RootExp (sl4Root i) t).1 h3_diag₂ = h3_diag₂ ∧
    (e6RootExp (sl4Root i) t).1 h3_diag₃ = h3_diag₃ ∧
    (e6RootExp (sl4Root i) t).1 (embedJ12 1) = embedJ12 1 := by
  have hc := sl4Root_fix_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hc
  have hmem : e6RootExp (sl4Root i) t ∈ d4Subgroup :=
    Subgroup.subset_closure ⟨(⟨sl4Root i, (hc i).1⟩, t), rfl⟩
  obtain ⟨hd1, hd2, hd3⟩ := d4Subgroup_fix_diags hmem
  refine ⟨d4Subgroup_le_f4InChevalley hmem, hd1, hd2, hd3, ?_⟩
  apply h3Zorn_ext_coord; intro m
  rw [h3ZornCoordinate_e6RootExp]
  have hsum : (∑ k : Fin 27, (sparseVal (e6RootSparse (sl4Root i)) m k : ℝ) *
      h3ZornCoordinate (embedJ12 1) k) = 0 := by
    have h3c : h3ZornCoordinate (embedJ12 (1 : ZornVectorMatrix ℝ)) 3 = 1 := rfl
    have h10c : h3ZornCoordinate (embedJ12 (1 : ZornVectorMatrix ℝ)) 10 = 1 := rfl
    have hz : ∀ k : Fin 27, k ≠ 3 → k ≠ 10 → h3ZornCoordinate (embedJ12 (1 : ZornVectorMatrix ℝ)) k = 0 := by
      intro k hk3 hk10
      fin_cases k <;> (try simp at hk3) <;> (try simp at hk10) <;> rfl
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun k : Fin 27 => k = 3 ∨ k = 10)]
    have hrest : ∑ k ∈ Finset.univ.filter (fun k : Fin 27 => ¬(k = 3 ∨ k = 10)),
        (sparseVal (e6RootSparse (sl4Root i)) m k : ℝ) * h3ZornCoordinate (embedJ12 1) k = 0 :=
      Finset.sum_eq_zero fun k hk => by
        have hnk := (Finset.mem_filter.mp hk).2
        rw [hz k (fun h => hnk (Or.inl h)) (fun h => hnk (Or.inr h)), mul_zero]
    rw [hrest, add_zero]
    have hflt : Finset.univ.filter (fun k : Fin 27 => k = 3 ∨ k = 10) = {3, 10} := by decide
    rw [hflt, Finset.sum_insert (by decide), Finset.sum_singleton, h3c, h10c, mul_one, mul_one]
    have hzero := (hc i).2 m
    exact_mod_cast hzero
  rw [hsum, mul_zero, add_zero]

private theorem sl4_b_rows_check :
    (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 21) 11 k == 0) &&
      (sparseVal (e6RootSparse 21) 12 k == if k.val = 11 then 1 else 0) &&
      (sparseVal (e6RootSparse 19) 11 k == 0) &&
      (sparseVal (e6RootSparse 19) 12 k == 0) &&
      (sparseVal (e6RootSparse 19) 13 k == if k.val = 11 then -1 else 0) &&
      (sparseVal (e6RootSparse 18) 11 k == 0) &&
      (sparseVal (e6RootSparse 18) 12 k == 0) &&
      (sparseVal (e6RootSparse 18) 13 k == 0) &&
      (sparseVal (e6RootSparse 18) 14 k == if k.val = 11 then 1 else 0)) = true ∧
    (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse 11) 11 k == if k.val = 12 then -1 else 0) &&
      (sparseVal (e6RootSparse 11) 12 k == 0) &&
      (sparseVal (e6RootSparse 11) 13 k == 0) &&
      (sparseVal (e6RootSparse 11) 14 k == 0) &&
      (sparseVal (e6RootSparse 11) 15 k == if k.val = 18 then -1 else 0) &&
      (sparseVal (e6RootSparse 11) 18 k == 0) &&
      (sparseVal (e6RootSparse 7) 11 k == if k.val = 13 then 1 else 0) &&
      (sparseVal (e6RootSparse 7) 12 k == 0) &&
      (sparseVal (e6RootSparse 7) 13 k == 0) &&
      (sparseVal (e6RootSparse 7) 14 k == 0) &&
      (sparseVal (e6RootSparse 7) 15 k == 0) &&
      (sparseVal (e6RootSparse 7) 16 k == if k.val = 18 then 1 else 0) &&
      (sparseVal (e6RootSparse 7) 18 k == 0) &&
      (sparseVal (e6RootSparse 6) 11 k == if k.val = 14 then -1 else 0) &&
      (sparseVal (e6RootSparse 6) 12 k == 0) &&
      (sparseVal (e6RootSparse 6) 13 k == 0) &&
      (sparseVal (e6RootSparse 6) 14 k == 0) &&
      (sparseVal (e6RootSparse 6) 15 k == 0) &&
      (sparseVal (e6RootSparse 6) 16 k == 0) &&
      (sparseVal (e6RootSparse 6) 17 k == if k.val = 18 then -1 else 0) &&
      (sparseVal (e6RootSparse 6) 18 k == 0)) = true := by
  decide

private theorem f4_reduce_j23_one_fixing_diags_j12 (A : H3ZornJordanAut)
    (h1 : A h3_diag₁ = h3_diag₁) (h2 : A h3_diag₂ = h3_diag₂) :
    ∃ h ∈ e6F4InChevalley,
      h.1 h3_diag₁ = h3_diag₁ ∧ h.1 h3_diag₂ = h3_diag₂ ∧ h.1 h3_diag₃ = h3_diag₃ ∧
      h.1 (embedJ12 1) = embedJ12 1 ∧ h.1 (A (embedJ23 1)) = embedJ23 1 := by
  have hmul : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Y : H3Zorn ℝ),
      (g₁ * g₂).1 Y = g₁.1 (g₂.1 Y) := fun _ _ _ => rfl
  obtain ⟨h3, _, hj23, _⟩ := peirce_spaces_preserved_of_fix_diags A h1 h2
  let b := (A (embedJ23 1)).b
  have hAb : A (embedJ23 1) = embedJ23 b := hj23 1
  have hAb' : A.toLinearEquiv (embedJ23 1) = embedJ23 b := hAb
  have h1' : A.toLinearEquiv h3_diag₁ = h3_diag₁ := h1
  have h2' : A.toLinearEquiv h3_diag₂ = h3_diag₂ := h2
  have h3' : A.toLinearEquiv h3_diag₃ = h3_diag₃ := h3
  have hA_mul (x y : H3Zorn ℝ) :
      A.toLinearEquiv (x * y) = A.toLinearEquiv x * A.toLinearEquiv y := by
    change A (x * y) = A x * A y
    exact A.map_mul x y
  have hnorm_b : ZornVectorMatrix.norm b = 1 := by
    have hm := congrArg A.toLinearEquiv (embedJ23_mul_embedJ23 1 1)
    rw [hA_mul, hAb', embedJ23_mul_embedJ23, map_smul, map_add, h2', h3'] at hm
    have hα₂ := congrArg H3Zorn.α₂ hm
    have hsc : (1 / 2 : ℝ) * zornBilin b b = (1 / 2 : ℝ) * zornBilin (1 : ZornVectorMatrix ℝ) 1 := by
      simpa [h3_diag₂, h3_diag₃, add_readback, smul_readback] using hα₂
    have hnorm_one : ZornVectorMatrix.norm (1 : ZornVectorMatrix ℝ) = 1 := by
      change ZornVectorMatrix.norm ZornVectorMatrix.one = 1
      exact zorn_norm_one_eq
    rw [zornBilin_self_eq_two_mul_norm, zornBilin_self_eq_two_mul_norm,
      hnorm_one] at hsc
    linarith [hsc]
  have hr_pos := sl4_b_rows_check.1
  have hr_neg := sl4_b_rows_check.2
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hr_pos hr_neg
  -- Step 1: Make b₀ ≠ 0 using {11, 7, 6} = {sl4Root 3, sl4Root 4, sl4Root 5}
  have hStep0 : ∃ s0 ∈ e6F4InChevalley,
      s0.1 h3_diag₁ = h3_diag₁ ∧ s0.1 h3_diag₂ = h3_diag₂ ∧ s0.1 h3_diag₃ = h3_diag₃ ∧
      s0.1 (embedJ12 1) = embedJ12 1 ∧ zornCoord (s0.1 (embedJ23 b)).b 0 ≠ 0 := by
    by_cases hb0 : zornCoord b 0 ≠ 0
    · exact ⟨1, e6F4InChevalley.one_mem, rfl, rfl, rfl, rfl, hb0⟩
    · have hb00 : zornCoord b 0 = 0 := not_not.mp hb0
      have h123 : zornCoord b 1 ≠ 0 ∨ zornCoord b 2 ≠ 0 ∨ zornCoord b 3 ≠ 0 := by
        by_contra hall
        push Not at hall
        have hn0 : ZornVectorMatrix.norm b = 0 := by
          have hv0 : b.v 0 = 0 := hall.1
          have hv1 : b.v 1 = 0 := hall.2.1
          have hv2 : b.v 2 = 0 := hall.2.2
          have ha0 : b.a = 0 := hb00
          simp [ZornVectorMatrix.norm, ZornVec3.dot, Fin.sum_univ_three, ha0, hv0, hv1, hv2]
        linarith [hnorm_b, hn0]
      rcases h123 with h1n | h2n | h3n
      · obtain ⟨hm, hd1, hd2, hd3, hj12⟩ := sl4Root_mem_fix_j12 3 1
        refine ⟨e6RootExp (sl4Root 3) 1, hm, hd1, hd2, hd3, hj12, ?_⟩
        rw [← h3ZornCoord_b_eq]
        change h3ZornCoordinate ((e6RootExp 11 1).1 (embedJ23 b)) 11 ≠ 0
        rw [rootExp_coord_add_single 11 11 12 (-1) 1 (embedJ23 b) (fun k => by
          rw [(hr_neg k).1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1]; simp [Fin.ext_iff])]
        have h11c : h3ZornCoordinate (embedJ23 b) 11 = zornCoord b 0 := h3ZornCoord_b_eq _ 0
        have h12c : h3ZornCoordinate (embedJ23 b) 12 = zornCoord b 1 := h3ZornCoord_b_eq _ 1
        rw [h11c, h12c, hb00]; simpa using h1n
      · obtain ⟨hm, hd1, hd2, hd3, hj12⟩ := sl4Root_mem_fix_j12 4 1
        refine ⟨e6RootExp (sl4Root 4) 1, hm, hd1, hd2, hd3, hj12, ?_⟩
        rw [← h3ZornCoord_b_eq]
        change h3ZornCoordinate ((e6RootExp 7 1).1 (embedJ23 b)) 11 ≠ 0
        rw [rootExp_coord_add_single 7 11 13 1 1 (embedJ23 b) (fun k => by
          rw [(hr_neg k).1.1.1.1.1.1.1.1.1.1.1.1.1.1.2]; simp [Fin.ext_iff])]
        have h11c : h3ZornCoordinate (embedJ23 b) 11 = zornCoord b 0 := h3ZornCoord_b_eq _ 0
        have h13c : h3ZornCoordinate (embedJ23 b) 13 = zornCoord b 2 := h3ZornCoord_b_eq _ 2
        rw [h11c, h13c, hb00]; simpa using h2n
      · obtain ⟨hm, hd1, hd2, hd3, hj12⟩ := sl4Root_mem_fix_j12 5 1
        refine ⟨e6RootExp (sl4Root 5) 1, hm, hd1, hd2, hd3, hj12, ?_⟩
        rw [← h3ZornCoord_b_eq]
        change h3ZornCoordinate ((e6RootExp 6 1).1 (embedJ23 b)) 11 ≠ 0
        rw [rootExp_coord_add_single 6 11 14 (-1) 1 (embedJ23 b) (fun k => by
          rw [(hr_neg k).1.1.1.1.1.1.1.2]; simp [Fin.ext_iff])]
        have h11c : h3ZornCoordinate (embedJ23 b) 11 = zornCoord b 0 := h3ZornCoord_b_eq _ 0
        have h14c : h3ZornCoordinate (embedJ23 b) 14 = zornCoord b 3 := h3ZornCoord_b_eq _ 3
        rw [h11c, h14c, hb00]; simpa using h3n
  obtain ⟨s0, hs0_f4, hs0_1, hs0_2, hs0_3, hs0_j12, hb1_0⟩ := hStep0
  let As0 : H3ZornJordanAut := h3zornJordanAutOfReducedStructure s0 hs0_f4.2
  have hAs0_eq : ∀ Y, As0 Y = s0.1 Y := fun _ => rfl
  obtain ⟨_, _, hAs0_23, _⟩ := peirce_spaces_preserved_of_fix_diags As0 hs0_1 hs0_2
  let b1 := (s0.1 (embedJ23 b)).b
  have hb1_eq : s0.1 (embedJ23 b) = embedJ23 b1 := hAs0_23 b
  have hb1_0' : zornCoord b1 0 ≠ 0 := by simpa [b1] using hb1_0
  -- Step 2: Clear b₁, b₂, b₃ using {21, 19, 18} = {sl4Root 0, 1, 2}
  obtain ⟨h21_m, h21_1, h21_2, h21_3, h21_j12⟩ := sl4Root_mem_fix_j12 0 (-(zornCoord b1 1 / zornCoord b1 0))
  obtain ⟨X1, hX1⟩ : ∃ X1, (e6RootExp (sl4Root 0) (-(zornCoord b1 1 / zornCoord b1 0))).1 (embedJ23 b1) = X1 := ⟨_, rfl⟩
  have hX1_0 : zornCoord X1.b 0 = zornCoord b1 0 := by
    rw [← hX1, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 21 _).1 (embedJ23 b1)) 11 = zornCoord b1 0
    rw [rootExp_coord_unchanged 21 11 _ (embedJ23 b1) (fun k => (hr_pos k).1.1.1.1.1.1.1.1)]
    exact h3ZornCoord_b_eq _ 0
  have hX1_1 : zornCoord X1.b 1 = 0 := by
    rw [← hX1, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 21 _).1 (embedJ23 b1)) 12 = 0
    rw [rootExp_coord_add_single 21 12 11 1 _ (embedJ23 b1) (fun k => by
      rw [(hr_pos k).1.1.1.1.1.1.1.2]; simp [Fin.ext_iff])]
    have h11c : h3ZornCoordinate (embedJ23 b1) 11 = zornCoord b1 0 := h3ZornCoord_b_eq _ 0
    have h12c : h3ZornCoordinate (embedJ23 b1) 12 = zornCoord b1 1 := h3ZornCoord_b_eq _ 1
    rw [h11c, h12c]
    field_simp [hb1_0'] <;> ring
  obtain ⟨h19_m, h19_1, h19_2, h19_3, h19_j12⟩ := sl4Root_mem_fix_j12 1 (zornCoord X1.b 2 / zornCoord X1.b 0)
  obtain ⟨X2, hX2⟩ : ∃ X2, (e6RootExp (sl4Root 1) (zornCoord X1.b 2 / zornCoord X1.b 0)).1 X1 = X2 := ⟨_, rfl⟩
  have hX2_0 : zornCoord X2.b 0 = zornCoord b1 0 := by
    rw [← hX2, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 19 _).1 X1) 11 = zornCoord b1 0
    rw [rootExp_coord_unchanged 19 11 _ X1 (fun k => (hr_pos k).1.1.1.1.1.1.2)]
    calc h3ZornCoordinate X1 11 = zornCoord X1.b 0 := by
          simpa using h3ZornCoord_b_eq X1 0
      _ = zornCoord b1 0 := hX1_0
  have hX2_1 : zornCoord X2.b 1 = 0 := by
    rw [← hX2, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 19 _).1 X1) 12 = 0
    rw [rootExp_coord_unchanged 19 12 _ X1 (fun k => (hr_pos k).1.1.1.1.1.2)]
    calc h3ZornCoordinate X1 12 = zornCoord X1.b 1 := by
          simpa using h3ZornCoord_b_eq X1 1
      _ = 0 := hX1_1
  have hX2_2 : zornCoord X2.b 2 = 0 := by
    rw [← hX2, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 19 _).1 X1) 13 = 0
    rw [rootExp_coord_add_single 19 13 11 (-1) _ X1 (fun k => by
      rw [(hr_pos k).1.1.1.1.2]; simp [Fin.ext_iff])]
    have h11c : h3ZornCoordinate X1 11 = zornCoord X1.b 0 := h3ZornCoord_b_eq _ 0
    have h13c : h3ZornCoordinate X1 13 = zornCoord X1.b 2 := h3ZornCoord_b_eq _ 2
    have hX1_0ne : zornCoord X1.b 0 ≠ 0 := hX1_0 ▸ hb1_0
    rw [h11c, h13c]; simp; field_simp [hX1_0ne]; ring
  obtain ⟨h18_m, h18_1, h18_2, h18_3, h18_j12⟩ := sl4Root_mem_fix_j12 2 (-(zornCoord X2.b 3 / zornCoord X2.b 0))
  obtain ⟨X3, hX3⟩ : ∃ X3, (e6RootExp (sl4Root 2) (-(zornCoord X2.b 3 / zornCoord X2.b 0))).1 X2 = X3 := ⟨_, rfl⟩
  have hX3_0 : zornCoord X3.b 0 = zornCoord b1 0 := by
    rw [← hX3, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 18 _).1 X2) 11 = zornCoord b1 0
    rw [rootExp_coord_unchanged 18 11 _ X2 (fun k => (hr_pos k).1.1.1.2)]
    calc h3ZornCoordinate X2 11 = zornCoord X2.b 0 := by
          simpa using h3ZornCoord_b_eq X2 0
      _ = zornCoord b1 0 := hX2_0
  have hX3_1 : zornCoord X3.b 1 = 0 := by
    rw [← hX3, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 18 _).1 X2) 12 = 0
    rw [rootExp_coord_unchanged 18 12 _ X2 (fun k => (hr_pos k).1.1.2)]
    calc h3ZornCoordinate X2 12 = zornCoord X2.b 1 := by
          simpa using h3ZornCoord_b_eq X2 1
      _ = 0 := hX2_1
  have hX3_2 : zornCoord X3.b 2 = 0 := by
    rw [← hX3, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 18 _).1 X2) 13 = 0
    rw [rootExp_coord_unchanged 18 13 _ X2 (fun k => (hr_pos k).1.2)]
    calc h3ZornCoordinate X2 13 = zornCoord X2.b 2 := by
          simpa using h3ZornCoord_b_eq X2 2
      _ = 0 := hX2_2
  have hX3_3 : zornCoord X3.b 3 = 0 := by
    rw [← hX3, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 18 _).1 X2) 14 = 0
    rw [rootExp_coord_add_single 18 14 11 1 _ X2 (fun k => by
      rw [(hr_pos k).2]; simp [Fin.ext_iff])]
    have h11c : h3ZornCoordinate X2 11 = zornCoord X2.b 0 := h3ZornCoord_b_eq _ 0
    have h14c : h3ZornCoordinate X2 14 = zornCoord X2.b 3 := h3ZornCoord_b_eq _ 3
    have hX2_0ne : zornCoord X2.b 0 ≠ 0 := hX2_0 ▸ hb1_0
    rw [h11c, h14c]; simp; field_simp [hX2_0ne]; ring
  -- Preserve embedJ23 subspace and norm 1 through g_pos
  let g_pos := e6RootExp (sl4Root 2) (-(zornCoord X2.b 3 / zornCoord X2.b 0)) *
      e6RootExp (sl4Root 1) (zornCoord X1.b 2 / zornCoord X1.b 0) *
      e6RootExp (sl4Root 0) (-(zornCoord b1 1 / zornCoord b1 0)) * s0
  have hgpos_f4 : g_pos ∈ e6F4InChevalley :=
    e6F4InChevalley.mul_mem
      (e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem h18_m h19_m) h21_m) hs0_f4
  have hgpos_1 : g_pos.1 h3_diag₁ = h3_diag₁ := by
    dsimp only [g_pos]; rw [hmul, hmul, hmul, hs0_1, h21_1, h19_1, h18_1]
  have hgpos_2 : g_pos.1 h3_diag₂ = h3_diag₂ := by
    dsimp only [g_pos]; rw [hmul, hmul, hmul, hs0_2, h21_2, h19_2, h18_2]
  have hgpos_3 : g_pos.1 h3_diag₃ = h3_diag₃ := by
    dsimp only [g_pos]; rw [hmul, hmul, hmul, hs0_3, h21_3, h19_3, h18_3]
  have hgpos_j12 : g_pos.1 (embedJ12 1) = embedJ12 1 := by
    dsimp only [g_pos]; rw [hmul, hmul, hmul, hs0_j12, h21_j12, h19_j12, h18_j12]
  have hgpos_X3 : g_pos.1 (embedJ23 b) = X3 := by
    dsimp only [g_pos]; rw [hmul, hmul, hmul, hb1_eq, hX1, hX2, hX3]
  let Agp : H3ZornJordanAut := h3zornJordanAutOfReducedStructure g_pos hgpos_f4.2
  have hAgp_eq : ∀ Y, Agp Y = g_pos.1 Y := fun _ => rfl
  obtain ⟨_, _, hAgp_23, _⟩ := peirce_spaces_preserved_of_fix_diags Agp hgpos_1 hgpos_2
  have hAgp_mul (x y : H3Zorn ℝ) :
      Agp.toLinearEquiv (x * y) = Agp.toLinearEquiv x * Agp.toLinearEquiv y := by
    change Agp (x * y) = Agp x * Agp y
    exact Agp.map_mul x y
  have hAgp_2 : Agp h3_diag₂ = h3_diag₂ := by rw [hAgp_eq, hgpos_2]
  have hAgp_3 : Agp h3_diag₃ = h3_diag₃ := by rw [hAgp_eq, hgpos_3]
  have hAgp_b : Agp.toLinearEquiv (embedJ23 b) = X3 := by
    change Agp (embedJ23 b) = X3
    rw [hAgp_eq, hgpos_X3]
  have hX3_j23 : X3 = embedJ23 X3.b := by
    have hproj : (Agp (embedJ23 b)).b = X3.b := by rw [hAgp_eq, hgpos_X3]
    calc X3 = Agp (embedJ23 b) := by exact hAgp_b.symm
      _ = embedJ23 (Agp (embedJ23 b)).b := hAgp_23 b
      _ = embedJ23 X3.b := congrArg embedJ23 hproj
  have hnorm_X3 : ZornVectorMatrix.norm X3.b = 1 := by
    have hm := congrArg Agp.toLinearEquiv (embedJ23_mul_embedJ23 b b)
    rw [hAgp_mul, hAgp_b, map_smul, map_add] at hm
    have h2' : Agp.toLinearEquiv h3_diag₂ = h3_diag₂ := hAgp_2
    have h3' : Agp.toLinearEquiv h3_diag₃ = h3_diag₃ := hAgp_3
    rw [h2', h3'] at hm
    have hα₂ : (X3 * X3).α₂ = (1 / 2 : ℝ) * zornBilin b b := by
      simpa [h3_diag₂, h3_diag₃, add_readback, smul_readback] using
        congrArg H3Zorn.α₂ hm
    have hprod : X3 * X3 =
        (1 / 2 * zornBilin X3.b X3.b) • (h3_diag₂ + h3_diag₃) := by
      calc X3 * X3 = embedJ23 X3.b * embedJ23 X3.b :=
            congrArg₂ (fun x y : H3Zorn ℝ => x * y) hX3_j23 hX3_j23
        _ = (1 / 2 * zornBilin X3.b X3.b) • (h3_diag₂ + h3_diag₃) :=
          embedJ23_mul_embedJ23 _ _
    have hα₂' : (X3 * X3).α₂ = (1 / 2 : ℝ) * zornBilin X3.b X3.b := by
      rw [hprod]
      simp [h3_diag₂, h3_diag₃, add_readback, smul_readback]
    have hsc : (1 / 2 : ℝ) * zornBilin X3.b X3.b = (1 / 2 : ℝ) * zornBilin b b := by
      linarith [hα₂, hα₂']
    rw [zornBilin_self_eq_two_mul_norm, zornBilin_self_eq_two_mul_norm, hnorm_b] at hsc
    linarith [hsc]
  have hX3_07 : zornCoord X3.b 0 * zornCoord X3.b 7 = 1 := by
    have hv0 : X3.b.v 0 = 0 := hX3_1
    have hv1 : X3.b.v 1 = 0 := hX3_2
    have hv2 : X3.b.v 2 = 0 := hX3_3
    have hnm : ZornVectorMatrix.norm X3.b = zornCoord X3.b 0 * zornCoord X3.b 7 := by
      simp [ZornVectorMatrix.norm, ZornVec3.dot, Fin.sum_univ_three, zornCoord, hv0, hv1, hv2]
    rw [← hnm, hnorm_X3]
  have hX3_7ne : zornCoord X3.b 7 ≠ 0 := fun h7 => by
    rw [h7, mul_zero] at hX3_07; exact zero_ne_one hX3_07
  -- Step 3: Clear b₄, b₅, b₆ using {11, 7, 6} = {sl4Root 3, 4, 5}
  obtain ⟨h11_m, h11_1, h11_2, h11_3, h11_j12⟩ := sl4Root_mem_fix_j12 3 (zornCoord X3.b 4 / zornCoord X3.b 7)
  obtain ⟨X4, hX4⟩ : ∃ X4, (e6RootExp (sl4Root 3) (zornCoord X3.b 4 / zornCoord X3.b 7)).1 X3 = X4 := ⟨_, rfl⟩
  have hX4_0 : zornCoord X4.b 0 = zornCoord b1 0 := by
    rw [← hX4, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 11 _).1 X3) 11 = zornCoord b1 0
    rw [rootExp_coord_add_single 11 11 12 (-1) _ X3 (fun k => by
      rw [(hr_neg k).1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1]; simp [Fin.ext_iff])]
    rw [show h3ZornCoordinate X3 12 = zornCoord X3.b 1 from h3ZornCoord_b_eq _ 1, hX3_1,
      show h3ZornCoordinate X3 11 = zornCoord X3.b 0 from h3ZornCoord_b_eq _ 0, hX3_0]
    ring
  have hX4_1 : zornCoord X4.b 1 = 0 := by
    rw [← hX4, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 11 _).1 X3) 12 = 0
    rw [rootExp_coord_unchanged 11 12 _ X3 (fun k => (hr_neg k).1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2)]
    calc h3ZornCoordinate X3 12 = zornCoord X3.b 1 := by
          simpa using h3ZornCoord_b_eq X3 1
      _ = 0 := hX3_1
  have hX4_2 : zornCoord X4.b 2 = 0 := by
    rw [← hX4, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 11 _).1 X3) 13 = 0
    rw [rootExp_coord_unchanged 11 13 _ X3 (fun k => (hr_neg k).1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2)]
    calc h3ZornCoordinate X3 13 = zornCoord X3.b 2 := by
          simpa using h3ZornCoord_b_eq X3 2
      _ = 0 := hX3_2
  have hX4_3 : zornCoord X4.b 3 = 0 := by
    rw [← hX4, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 11 _).1 X3) 14 = 0
    rw [rootExp_coord_unchanged 11 14 _ X3 (fun k => (hr_neg k).1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2)]
    calc h3ZornCoordinate X3 14 = zornCoord X3.b 3 := by
          simpa using h3ZornCoord_b_eq X3 3
      _ = 0 := hX3_3
  have hX4_7 : zornCoord X4.b 7 = zornCoord X3.b 7 := by
    rw [← hX4, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 11 _).1 X3) 18 = zornCoord X3.b 7
    rw [rootExp_coord_unchanged 11 18 _ X3 (fun k => (hr_neg k).1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2)]
    simpa using h3ZornCoord_b_eq X3 7
  have hX4_4 : zornCoord X4.b 4 = 0 := by
    rw [← hX4, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 11 _).1 X3) 15 = 0
    rw [rootExp_coord_add_single 11 15 18 (-1) _ X3 (fun k => by
      rw [(hr_neg k).1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2]; simp [Fin.ext_iff])]
    rw [show h3ZornCoordinate X3 15 = zornCoord X3.b 4 from h3ZornCoord_b_eq _ 4,
      show h3ZornCoordinate X3 18 = zornCoord X3.b 7 from h3ZornCoord_b_eq _ 7]
    simp; field_simp [hX3_7ne]; ring
  obtain ⟨h7_m, h7_1, h7_2, h7_3, h7_j12⟩ := sl4Root_mem_fix_j12 4 (-(zornCoord X4.b 5 / zornCoord X4.b 7))
  obtain ⟨X5, hX5⟩ : ∃ X5, (e6RootExp (sl4Root 4) (-(zornCoord X4.b 5 / zornCoord X4.b 7))).1 X4 = X5 := ⟨_, rfl⟩
  have hX5_0 : zornCoord X5.b 0 = zornCoord b1 0 := by
    rw [← hX5, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 7 _).1 X4) 11 = zornCoord b1 0
    rw [rootExp_coord_add_single 7 11 13 1 _ X4 (fun k => by
      rw [(hr_neg k).1.1.1.1.1.1.1.1.1.1.1.1.1.1.2]; simp [Fin.ext_iff])]
    rw [show h3ZornCoordinate X4 13 = zornCoord X4.b 2 from h3ZornCoord_b_eq _ 2, hX4_2,
      show h3ZornCoordinate X4 11 = zornCoord X4.b 0 from h3ZornCoord_b_eq _ 0, hX4_0]
    ring
  have hX5_1 : zornCoord X5.b 1 = 0 := by
    rw [← hX5, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 7 _).1 X4) 12 = 0
    rw [rootExp_coord_unchanged 7 12 _ X4 (fun k => (hr_neg k).1.1.1.1.1.1.1.1.1.1.1.1.1.2)]
    calc h3ZornCoordinate X4 12 = zornCoord X4.b 1 := by
          simpa using h3ZornCoord_b_eq X4 1
      _ = 0 := hX4_1
  have hX5_2 : zornCoord X5.b 2 = 0 := by
    rw [← hX5, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 7 _).1 X4) 13 = 0
    rw [rootExp_coord_unchanged 7 13 _ X4 (fun k => (hr_neg k).1.1.1.1.1.1.1.1.1.1.1.1.2)]
    calc h3ZornCoordinate X4 13 = zornCoord X4.b 2 := by
          simpa using h3ZornCoord_b_eq X4 2
      _ = 0 := hX4_2
  have hX5_3 : zornCoord X5.b 3 = 0 := by
    rw [← hX5, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 7 _).1 X4) 14 = 0
    rw [rootExp_coord_unchanged 7 14 _ X4 (fun k => (hr_neg k).1.1.1.1.1.1.1.1.1.1.1.2)]
    calc h3ZornCoordinate X4 14 = zornCoord X4.b 3 := by
          simpa using h3ZornCoord_b_eq X4 3
      _ = 0 := hX4_3
  have hX5_4 : zornCoord X5.b 4 = 0 := by
    rw [← hX5, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 7 _).1 X4) 15 = 0
    rw [rootExp_coord_unchanged 7 15 _ X4 (fun k => (hr_neg k).1.1.1.1.1.1.1.1.1.1.2)]
    calc h3ZornCoordinate X4 15 = zornCoord X4.b 4 := by
          simpa using h3ZornCoord_b_eq X4 4
      _ = 0 := hX4_4
  have hX5_7 : zornCoord X5.b 7 = zornCoord X3.b 7 := by
    rw [← hX5, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 7 _).1 X4) 18 = zornCoord X3.b 7
    rw [rootExp_coord_unchanged 7 18 _ X4 (fun k => (hr_neg k).1.1.1.1.1.1.1.1.2)]
    calc h3ZornCoordinate X4 18 = zornCoord X4.b 7 := by
          simpa using h3ZornCoord_b_eq X4 7
      _ = zornCoord X3.b 7 := hX4_7
  have hX5_5 : zornCoord X5.b 5 = 0 := by
    rw [← hX5, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 7 _).1 X4) 16 = 0
    rw [rootExp_coord_add_single 7 16 18 1 _ X4 (fun k => by
      rw [(hr_neg k).1.1.1.1.1.1.1.1.1.2]; simp [Fin.ext_iff])]
    have hX4_7ne : zornCoord X4.b 7 ≠ 0 := hX4_7 ▸ hX3_7ne
    rw [show h3ZornCoordinate X4 16 = zornCoord X4.b 5 from h3ZornCoord_b_eq _ 5,
      show h3ZornCoordinate X4 18 = zornCoord X4.b 7 from h3ZornCoord_b_eq _ 7]
    simp; field_simp [hX4_7ne]; ring
  obtain ⟨h6_m, h6_1, h6_2, h6_3, h6_j12⟩ := sl4Root_mem_fix_j12 5 (zornCoord X5.b 6 / zornCoord X5.b 7)
  obtain ⟨X6, hX6⟩ : ∃ X6, (e6RootExp (sl4Root 5) (zornCoord X5.b 6 / zornCoord X5.b 7)).1 X5 = X6 := ⟨_, rfl⟩
  have hX6_0 : zornCoord X6.b 0 = zornCoord b1 0 := by
    rw [← hX6, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 6 _).1 X5) 11 = zornCoord b1 0
    rw [rootExp_coord_add_single 6 11 14 (-1) _ X5 (fun k => by
      rw [(hr_neg k).1.1.1.1.1.1.1.2]; simp [Fin.ext_iff])]
    rw [show h3ZornCoordinate X5 14 = zornCoord X5.b 3 from h3ZornCoord_b_eq _ 3, hX5_3,
      show h3ZornCoordinate X5 11 = zornCoord X5.b 0 from h3ZornCoord_b_eq _ 0, hX5_0]
    ring
  have hX6_1 : zornCoord X6.b 1 = 0 := by
    rw [← hX6, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 6 _).1 X5) 12 = 0
    rw [rootExp_coord_unchanged 6 12 _ X5 (fun k => (hr_neg k).1.1.1.1.1.1.2)]
    calc h3ZornCoordinate X5 12 = zornCoord X5.b 1 := by
          simpa using h3ZornCoord_b_eq X5 1
      _ = 0 := hX5_1
  have hX6_2 : zornCoord X6.b 2 = 0 := by
    rw [← hX6, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 6 _).1 X5) 13 = 0
    rw [rootExp_coord_unchanged 6 13 _ X5 (fun k => (hr_neg k).1.1.1.1.1.2)]
    calc h3ZornCoordinate X5 13 = zornCoord X5.b 2 := by
          simpa using h3ZornCoord_b_eq X5 2
      _ = 0 := hX5_2
  have hX6_3 : zornCoord X6.b 3 = 0 := by
    rw [← hX6, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 6 _).1 X5) 14 = 0
    rw [rootExp_coord_unchanged 6 14 _ X5 (fun k => (hr_neg k).1.1.1.1.2)]
    calc h3ZornCoordinate X5 14 = zornCoord X5.b 3 := by
          simpa using h3ZornCoord_b_eq X5 3
      _ = 0 := hX5_3
  have hX6_4 : zornCoord X6.b 4 = 0 := by
    rw [← hX6, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 6 _).1 X5) 15 = 0
    rw [rootExp_coord_unchanged 6 15 _ X5 (fun k => (hr_neg k).1.1.1.2)]
    calc h3ZornCoordinate X5 15 = zornCoord X5.b 4 := by
          simpa using h3ZornCoord_b_eq X5 4
      _ = 0 := hX5_4
  have hX6_5 : zornCoord X6.b 5 = 0 := by
    rw [← hX6, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 6 _).1 X5) 16 = 0
    rw [rootExp_coord_unchanged 6 16 _ X5 (fun k => (hr_neg k).1.1.2)]
    calc h3ZornCoordinate X5 16 = zornCoord X5.b 5 := by
          simpa using h3ZornCoord_b_eq X5 5
      _ = 0 := hX5_5
  have hX6_6 : zornCoord X6.b 6 = 0 := by
    rw [← hX6, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 6 _).1 X5) 17 = 0
    rw [rootExp_coord_add_single 6 17 18 (-1) _ X5 (fun k => by
      rw [(hr_neg k).1.2]; simp [Fin.ext_iff])]
    have hX5_7ne : zornCoord X5.b 7 ≠ 0 := hX5_7 ▸ hX3_7ne
    rw [show h3ZornCoordinate X5 17 = zornCoord X5.b 6 from h3ZornCoord_b_eq _ 6,
      show h3ZornCoordinate X5 18 = zornCoord X5.b 7 from h3ZornCoord_b_eq _ 7]
    simp; field_simp [hX5_7ne]; ring
  have hX6_7 : zornCoord X6.b 7 = (zornCoord b1 0)⁻¹ := by
    rw [← hX6, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp 6 _).1 X5) 18 = (zornCoord b1 0)⁻¹
    rw [rootExp_coord_unchanged 6 18 _ X5 (fun k => (hr_neg k).2)]
    calc h3ZornCoordinate X5 18 = zornCoord X5.b 7 := by
          simpa using h3ZornCoord_b_eq X5 7
      _ = zornCoord X3.b 7 := hX5_7
      _ = (zornCoord b1 0)⁻¹ := by
          have h1 : zornCoord X3.b 0 * zornCoord X3.b 7 = 1 := hX3_07
          rw [hX3_0] at h1
          field_simp [hb1_0] at h1
          field_simp [hb1_0]
          linarith [h1]
  have hg6_X6 : (e6RootExp (sl4Root 5) (zornCoord X5.b 6 / zornCoord X5.b 7) *
      e6RootExp (sl4Root 4) (-(zornCoord X4.b 5 / zornCoord X4.b 7)) *
      e6RootExp (sl4Root 3) (zornCoord X3.b 4 / zornCoord X3.b 7) * g_pos).1 (embedJ23 b) = X6 := by
    rw [hmul, hmul, hmul, hgpos_X3, hX4, hX5, hX6]
  have hg6_mem : e6RootExp (sl4Root 5) (zornCoord X5.b 6 / zornCoord X5.b 7) *
      e6RootExp (sl4Root 4) (-(zornCoord X4.b 5 / zornCoord X4.b 7)) *
      e6RootExp (sl4Root 3) (zornCoord X3.b 4 / zornCoord X3.b 7) * g_pos ∈ e6F4InChevalley :=
    e6F4InChevalley.mul_mem
      (e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem h6_m h7_m) h11_m) hgpos_f4
  let A6 : H3ZornJordanAut := h3zornJordanAutOfReducedStructure _ hg6_mem.2
  have hA6_1_raw : (e6RootExp (sl4Root 5) (zornCoord X5.b 6 / zornCoord X5.b 7) *
      e6RootExp (sl4Root 4) (-(zornCoord X4.b 5 / zornCoord X4.b 7)) *
      e6RootExp (sl4Root 3) (zornCoord X3.b 4 / zornCoord X3.b 7) * g_pos).1 h3_diag₁ =
      h3_diag₁ := by
    rw [hmul, hmul, hmul, hgpos_1, h11_1, h7_1, h6_1]
  have hA6_2_raw : (e6RootExp (sl4Root 5) (zornCoord X5.b 6 / zornCoord X5.b 7) *
      e6RootExp (sl4Root 4) (-(zornCoord X4.b 5 / zornCoord X4.b 7)) *
      e6RootExp (sl4Root 3) (zornCoord X3.b 4 / zornCoord X3.b 7) * g_pos).1 h3_diag₂ =
      h3_diag₂ := by
    rw [hmul, hmul, hmul, hgpos_2, h11_2, h7_2, h6_2]
  have hA6_3_raw : (e6RootExp (sl4Root 5) (zornCoord X5.b 6 / zornCoord X5.b 7) *
      e6RootExp (sl4Root 4) (-(zornCoord X4.b 5 / zornCoord X4.b 7)) *
      e6RootExp (sl4Root 3) (zornCoord X3.b 4 / zornCoord X3.b 7) * g_pos).1 h3_diag₃ =
      h3_diag₃ := by
    rw [hmul, hmul, hmul, hgpos_3, h11_3, h7_3, h6_3]
  have hA6_j12_raw : (e6RootExp (sl4Root 5) (zornCoord X5.b 6 / zornCoord X5.b 7) *
      e6RootExp (sl4Root 4) (-(zornCoord X4.b 5 / zornCoord X4.b 7)) *
      e6RootExp (sl4Root 3) (zornCoord X3.b 4 / zornCoord X3.b 7) * g_pos).1
      (embedJ12 1) = embedJ12 1 := by
    rw [hmul, hmul, hmul, hgpos_j12, h11_j12, h7_j12, h6_j12]
  have hA6_1 : A6 h3_diag₁ = h3_diag₁ := by change _ = _; exact hA6_1_raw
  have hA6_2 : A6 h3_diag₂ = h3_diag₂ := by change _ = _; exact hA6_2_raw
  obtain ⟨_, _, hA6_23, _⟩ := peirce_spaces_preserved_of_fix_diags A6 hA6_1 hA6_2
  have hX6_j23 : X6 = embedJ23 X6.b := by
    rw [← hg6_X6]
    change A6 (embedJ23 b) = embedJ23 ((e6RootExp (sl4Root 5) _ * _ * _ * g_pos).1 (embedJ23 b)).b
    rw [hA6_23 b]; rfl
  -- Step 4: Scale b₀ e₀ + b₀⁻¹ e₇ to 1 via e6TorusElt 2 v * e6TorusElt 4 v
  let v : ℝˣ := Units.mk0 (zornCoord b1 0) hb1_0
  let t := e6TorusElt 2 v * e6TorusElt 4 v
  have ht_che : t ∈ e6ChevalleySubgroup :=
    e6ChevalleySubgroup.mul_mem (e6TorusElt_mem_chevalley 2 _) (e6TorusElt_mem_chevalley 4 _)
  have hfixBasis (k : Fin 27) (hw : h3zornWeight k 2 + h3zornWeight k 4 = 0) :
      t.1 (h3ZornBasis k) = h3ZornBasis k := by
    change ((e6TorusElt 2 v * e6TorusElt 4 v).1) (h3ZornBasis k) = _
    rw [hmul, e6TorusElt_apply_basis, map_smul, e6TorusElt_apply_basis]
    simp only [Units.val_zpow_eq_zpow_val, smul_smul]
    rw [← zpow_add₀ (Units.ne_zero v), add_comm, hw]
    simp
  have hunit : (1 : ZornVectorMatrix ℝ) = zorn_basis 0 + zorn_basis 7 := by
    ext <;> simp [zorn_basis, ZornVectorMatrix.one, ZornVectorMatrix.add] <;> rfl
  have hJ121 : embedJ12 1 = h3ZornBasis 3 + h3ZornBasis 10 := by
    calc embedJ12 1 = embedJ12 (zorn_basis 0 + zorn_basis 7) := by rw [← hunit]
      _ = embedJ12 (zorn_basis 0) + embedJ12 (zorn_basis 7) := by
          ext <;> simp [embedJ12, ZornVectorMatrix.add]
      _ = h3ZornBasis 3 + h3ZornBasis 10 := by
          rw [← h3ZornBasis_12 0, ← h3ZornBasis_12 7]
          congr 1 <;> norm_num
  have ht_fix : t.1 h3_diag₁ = h3_diag₁ ∧ t.1 h3_diag₂ = h3_diag₂ ∧ t.1 h3_diag₃ = h3_diag₃ ∧
      t.1 (embedJ12 1) = embedJ12 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← h3ZornBasis_zero]; exact hfixBasis 0 (by decide)
    · rw [← h3ZornBasis_one]; exact hfixBasis 1 (by decide)
    · rw [← h3ZornBasis_two]; exact hfixBasis 2 (by decide)
    · rw [hJ121, t.1.map_add, hfixBasis 3 (by decide), hfixBasis 10 (by decide)]
  have ht_one : t.1 1 = 1 := by
    rw [← h3Zorn_diag_sum_one, t.1.map_add, t.1.map_add, ht_fix.1, ht_fix.2.1, ht_fix.2.2.1]
  have ht_f4 : t ∈ e6F4InChevalley := ⟨ht_che, ht_one⟩
  have ht_j23 : t.1 X6 = embedJ23 1 := by
    rw [hX6_j23]
    apply h3Zorn_ext_coord; intro m; dsimp only [t]
    rw [hmul, h3ZornCoordinate_e6TorusElt, h3ZornCoordinate_e6TorusElt]
    have hw11 : h3zornWeight 11 2 = 0 ∧ h3zornWeight 11 4 = -1 := ⟨rfl, rfl⟩
    have hw18 : h3zornWeight 18 2 = 1 ∧ h3zornWeight 18 4 = 0 := ⟨rfl, rfl⟩
    fin_cases m <;> dsimp
    · simp [embedJ23, h3ZornCoordinate, ZornVectorMatrix.one]
    · simp [embedJ23, h3ZornCoordinate, ZornVectorMatrix.one]
    · simp [embedJ23, h3ZornCoordinate, ZornVectorMatrix.one]
    · simp [embedJ23, h3ZornCoordinate, ZornVectorMatrix.one, ZornVectorMatrix.zero]
    · simp [embedJ23, h3ZornCoordinate, ZornVectorMatrix.one, ZornVectorMatrix.zero]
    · simp [embedJ23, h3ZornCoordinate, ZornVectorMatrix.one, ZornVectorMatrix.zero]
    · simp [embedJ23, h3ZornCoordinate, ZornVectorMatrix.one, ZornVectorMatrix.zero]
    · simp [embedJ23, h3ZornCoordinate, ZornVectorMatrix.one, ZornVectorMatrix.zero]
    · simp [embedJ23, h3ZornCoordinate, ZornVectorMatrix.one, ZornVectorMatrix.zero]
    · simp [embedJ23, h3ZornCoordinate, ZornVectorMatrix.one, ZornVectorMatrix.zero]
    · simp [embedJ23, h3ZornCoordinate, ZornVectorMatrix.one, ZornVectorMatrix.zero]
    · change (v : ℝ) ^ (h3zornWeight 11 2) * ((v : ℝ) ^ (h3zornWeight 11 4) *
          zornCoord X6.b 0) = zornCoord (1 : ZornVectorMatrix ℝ) 0
      rw [hw11.1, hw11.2, zpow_zero, zpow_neg_one, one_mul, hX6_0]
      have hv : (v : ℝ) = zornCoord b1 0 := rfl
      rw [hv, inv_mul_cancel₀ hb1_0]; rfl
    · simp [embedJ23, h3ZornCoordinate, show X6.b.v 0 = 0 from hX6_1]
      change (0 : ℝ) = (ZornVectorMatrix.one : ZornVectorMatrix ℝ).v 0
      simp [ZornVectorMatrix.one]
    · simp [embedJ23, h3ZornCoordinate, show X6.b.v 1 = 0 from hX6_2]
      change (0 : ℝ) = (ZornVectorMatrix.one : ZornVectorMatrix ℝ).v 1
      simp [ZornVectorMatrix.one]
    · simp [embedJ23, h3ZornCoordinate, show X6.b.v 2 = 0 from hX6_3]
      change (0 : ℝ) = (ZornVectorMatrix.one : ZornVectorMatrix ℝ).v 2
      simp [ZornVectorMatrix.one]
    · simp [embedJ23, h3ZornCoordinate, show X6.b.w 0 = 0 from hX6_4]
      change (0 : ℝ) = (ZornVectorMatrix.one : ZornVectorMatrix ℝ).w 0
      simp [ZornVectorMatrix.one]
    · simp [embedJ23, h3ZornCoordinate, show X6.b.w 1 = 0 from hX6_5]
      change (0 : ℝ) = (ZornVectorMatrix.one : ZornVectorMatrix ℝ).w 1
      simp [ZornVectorMatrix.one]
    · simp [embedJ23, h3ZornCoordinate, show X6.b.w 2 = 0 from hX6_6]
      change (0 : ℝ) = (ZornVectorMatrix.one : ZornVectorMatrix ℝ).w 2
      simp [ZornVectorMatrix.one]
    · change (v : ℝ) ^ (h3zornWeight 18 2) * ((v : ℝ) ^ (h3zornWeight 18 4) *
          zornCoord X6.b 7) = zornCoord (1 : ZornVectorMatrix ℝ) 7
      rw [hw18.1, hw18.2, zpow_one, zpow_zero, one_mul, hX6_7]
      have hv : (v : ℝ) = zornCoord b1 0 := rfl
      rw [hv, mul_inv_cancel₀ hb1_0]; rfl
    all_goals simp [embedJ23, h3ZornCoordinate, ZornVectorMatrix.zero,
      ZornVectorMatrix.one] <;> try rfl
  refine ⟨t * (e6RootExp (sl4Root 5) (zornCoord X5.b 6 / zornCoord X5.b 7) *
      e6RootExp (sl4Root 4) (-(zornCoord X4.b 5 / zornCoord X4.b 7)) *
      e6RootExp (sl4Root 3) (zornCoord X3.b 4 / zornCoord X3.b 7) * g_pos),
    e6F4InChevalley.mul_mem ht_f4 hg6_mem, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmul, hA6_1_raw, ht_fix.1]
  · rw [hmul, hA6_2_raw, ht_fix.2.1]
  · rw [hmul, hA6_3_raw, ht_fix.2.2.1]
  · rw [hmul, hA6_j12_raw, ht_fix.2.2.2]
  · rw [hmul, hAb, hg6_X6, ht_j23]

end PartBF4AndFullGeneration

end InfoGeometry.Algebra
