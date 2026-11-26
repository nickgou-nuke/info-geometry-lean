/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornE6RootSystem
import InfoGeometry.Algebra.H3ZornStructureGroup

/-!
# Constructive Generation and Bruhat Closure of `E₆(6) = Str₀(H₃(𝕆_s))`

Proves inside `h3zornReducedStructureGroup` (`Str₀(H₃(𝕆_s))`) without using the unsigned
`CFSGPort.Chevalley.xOp`/`yOp`/`pinnedX` operators:

1. **Root exponentials & Chevalley subgroup** (`e6ChevalleySubgroup := Subgroup.closure e6RootExpSet`),
   simple Chevalley generators `e6SimpleX`, `e6SimpleY`, Weyl elements `e6WeylElt`, and torus
   elements `e6TorusElt`.
2. **Transitivity** on `{X : H3Zorn ℝ | normCubic X = 1}` (`e6ChevalleySubgroup_transitive_normCubic_one`)
   and on rank-1 primitive idempotents (`e6ChevalleySubgroup_transitive_rankOneIdempotent`).
3. **Full generation (`Route A`)**: `F₄(4) = Aut(H₃(𝕆_s))` lies in `e6ChevalleySubgroup`,
   every quadratic operator `U(X)` (`normCubic X = ±1`) lies in `e6ChevalleySubgroup`, and
   `e6ChevalleySubgroup = ⊤` (`closure_e6RootExpSet_eq_top`).
4. **Native signed Bruhat closure (`B, W`)**: `e6PosUnipotent`, `e6NegUnipotent`, `e6Torus`,
   `e6Borel`, `e6WeylSubgroup`, `e6SimpleClosure`, disjointness intersections,
   `h3zornCubicStabilizerLieEquivOfNormSimilitude_injective`, simple-root generation,
   Weyl-root/torus conjugation, rank-1 `SL₂` Bruhat identity, and the full Bruhat
   decomposition `G = B * W * B`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn

section RootExponentials

/-- Exponential endomorphism `1 + c • X` for a square-zero Lie-algebra element. -/
def e6RootExpEnd (X : h3zornCubicStabilizer) (c : ℝ) : Module.End ℝ (H3Zorn ℝ) :=
  1 + c • X.1

@[simp] theorem e6RootExpEnd_apply (X : h3zornCubicStabilizer) (c : ℝ) (x : H3Zorn ℝ) :
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

private theorem normCubic_line_coeffs_zero_cb (n c : ℝ) :
    n + c * 0 + c ^ 2 * 0 + c ^ 3 * 0 = n := by ring

private theorem sqZero_cubic_scalar_kill_cb {a b d : ℝ}
    (hp : a + b + d = 0) (hm : a - b + d = 0) (ha : a = 0) :
    b = 0 ∧ d = 0 :=
  ⟨by linarith [hp, hm], by linarith [hp, hm, ha]⟩

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
  have hkill := sqZero_cubic_scalar_kill_cb hp_exp hm_exp (htr x)
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
  exact normCubic_line_coeffs_zero_cb (normCubic x) c

/-- Exponential map `Multiplicative ℝ →* h3zornReducedStructureGroup` for square-zero `X`. -/
def e6SqZeroExp (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    h3zornReducedStructureGroup :=
  ⟨e6RootExpEquiv X hsq c, e6RootExp_mem_reducedStructureGroup X hsq c⟩

@[simp] theorem e6SqZeroExp_coe (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    ((e6SqZeroExp X hsq c).1 : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) = e6RootExpEquiv X hsq c := rfl

theorem e6SqZeroExp_add (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (a b : ℝ) :
    e6SqZeroExp X hsq (a + b) = e6SqZeroExp X hsq a * e6SqZeroExp X hsq b := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  change e6RootExpEnd X (a + b) = e6RootExpEnd X a * e6RootExpEnd X b
  exact (e6RootExpEnd_mul X hsq a b).symm

theorem e6SqZeroExp_zero (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) :
    e6SqZeroExp X hsq 0 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact e6RootExpEnd_zero X

/-- Root subgroup generator `x_r(t) = 1 + t • e6RootVec r ∈ h3zornReducedStructureGroup`. -/
def e6RootExp (r : Fin 72) (t : ℝ) : h3zornReducedStructureGroup :=
  e6SqZeroExp (e6RootVec r) (e6RootVec_sq_zero r) t

@[simp] theorem e6RootExp_apply (r : Fin 72) (t : ℝ) (x : H3Zorn ℝ) :
    (e6RootExp r t).1 x = x + t • (e6RootVec r).1 x :=
  e6RootExpEquiv_apply (e6RootVec r) (e6RootVec_sq_zero r) t x

theorem e6RootExp_add (r : Fin 72) (a b : ℝ) :
    e6RootExp r (a + b) = e6RootExp r a * e6RootExp r b :=
  e6SqZeroExp_add (e6RootVec r) (e6RootVec_sq_zero r) a b

theorem e6RootExp_zero (r : Fin 72) : e6RootExp r 0 = 1 :=
  e6SqZeroExp_zero (e6RootVec r) (e6RootVec_sq_zero r)

theorem e6RootExp_inv (r : Fin 72) (t : ℝ) : (e6RootExp r t)⁻¹ = e6RootExp r (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← e6RootExp_add, add_neg_cancel, e6RootExp_zero]

/-- Set of all 72 root-subgroup elements in `h3zornReducedStructureGroup`. -/
def e6RootExpSet : Set h3zornReducedStructureGroup :=
  {g | ∃ (r : Fin 72) (t : ℝ), g = e6RootExp r t}

/-- Native Chevalley subgroup `E₆(6) ≤ Str₀(H₃(𝕆_s))` generated by `e6RootExpSet`. -/
def e6ChevalleySubgroup : Subgroup h3zornReducedStructureGroup :=
  Subgroup.closure e6RootExpSet

theorem e6RootExp_mem_chevalley (r : Fin 72) (t : ℝ) :
    e6RootExp r t ∈ e6ChevalleySubgroup :=
  Subgroup.subset_closure ⟨r, t, rfl⟩

theorem e6SimpleE_sq_zero (i : Fin 6) :
    ((e6SimpleE i).1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0 :=
  e6RootVec_sq_zero (eSimpleIdx i)

private theorem e6SimpleF_sq_zero_cb (i : Fin 6) :
    ((e6SimpleF i).1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0 := by
  change (((fSimpleSign i : ℝ) • (e6RootVec (fSimpleIdx i)).1 : Module.End ℝ (H3Zorn ℝ))) ^ 2 = 0
  rw [smul_pow, e6RootVec_sq_zero, smul_zero]

/-- Simple positive Chevalley root generator `x_i(c)`. -/
def e6SimpleX (i : Fin 6) (c : ℝ) : h3zornReducedStructureGroup :=
  e6SqZeroExp (e6SimpleE i) (e6SimpleE_sq_zero i) c

/-- Simple negative Chevalley root generator `y_i(c)`. -/
def e6SimpleY (i : Fin 6) (c : ℝ) : h3zornReducedStructureGroup :=
  e6SqZeroExp (e6SimpleF i) (e6SimpleF_sq_zero_cb i) c

theorem e6SimpleX_eq_rootExp (i : Fin 6) (c : ℝ) :
    e6SimpleX i c = e6RootExp (eSimpleIdx i) c := rfl

theorem e6SimpleY_eq_rootExp (i : Fin 6) (c : ℝ) :
    e6SimpleY i c = e6RootExp (fSimpleIdx i) ((fSimpleSign i : ℝ) * c) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro x
  change x + c • ((fSimpleSign i : ℝ) • (e6RootVec (fSimpleIdx i)).1) x =
    x + ((fSimpleSign i : ℝ) * c) • (e6RootVec (fSimpleIdx i)).1 x
  simp [smul_smul, mul_comm]

theorem e6SimpleX_mem_chevalley (i : Fin 6) (c : ℝ) :
    e6SimpleX i c ∈ e6ChevalleySubgroup := by
  rw [e6SimpleX_eq_rootExp]
  exact e6RootExp_mem_chevalley _ _

theorem e6SimpleY_mem_chevalley (i : Fin 6) (c : ℝ) :
    e6SimpleY i c ∈ e6ChevalleySubgroup := by
  rw [e6SimpleY_eq_rootExp]
  exact e6RootExp_mem_chevalley _ _

/-- Native Chevalley Weyl element `w_i(t) = x_i(t) y_i(-t⁻¹) x_i(t)`. -/
def e6WeylElt (i : Fin 6) (t : ℝˣ) : h3zornReducedStructureGroup :=
  e6SimpleX i (t : ℝ) * e6SimpleY i (-((t⁻¹ : ℝˣ) : ℝ)) * e6SimpleX i (t : ℝ)

/-- Native Chevalley torus element `h_i(t) = w_i(t) * w_i(-1)`. -/
def e6TorusElt (i : Fin 6) (t : ℝˣ) : h3zornReducedStructureGroup :=
  e6WeylElt i t * e6WeylElt i (-1)

theorem e6WeylElt_mem_chevalley (i : Fin 6) (t : ℝˣ) :
    e6WeylElt i t ∈ e6ChevalleySubgroup :=
  e6ChevalleySubgroup.mul_mem
    (e6ChevalleySubgroup.mul_mem (e6SimpleX_mem_chevalley i _) (e6SimpleY_mem_chevalley i _))
    (e6SimpleX_mem_chevalley i _)

theorem e6TorusElt_mem_chevalley (i : Fin 6) (t : ℝˣ) :
    e6TorusElt i t ∈ e6ChevalleySubgroup :=
  e6ChevalleySubgroup.mul_mem (e6WeylElt_mem_chevalley i t) (e6WeylElt_mem_chevalley i (-1))

private theorem e6Simple_comm_apply_cb (i : Fin 6) (v : H3Zorn ℝ) :
    (e6SimpleE i).1 ((e6SimpleF i).1 v) - (e6SimpleF i).1 ((e6SimpleE i).1 v) =
      (e6SimpleH i).1 v :=
  congrArg (fun x : h3zornCubicStabilizer => x.1 v) (e6Simple_bracket_EF_same i)

private theorem e6SimpleE_sq_apply_cb (i : Fin 6) (v : H3Zorn ℝ) :
    (e6SimpleE i).1 ((e6SimpleE i).1 v) = 0 := by
  have h := LinearMap.ext_iff.mp (e6SimpleE_sq_zero i) v
  simpa [sq, Module.End.mul_apply] using h

private theorem e6SimpleF_sq_apply_cb (i : Fin 6) (v : H3Zorn ℝ) :
    (e6SimpleF i).1 ((e6SimpleF i).1 v) = 0 := by
  have h := LinearMap.ext_iff.mp (e6SimpleF_sq_zero_cb i) v
  simpa [sq, Module.End.mul_apply] using h

private theorem simpleE_kill_of_weight_nonneg_cb (i : Fin 6) (k : Fin 27)
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
    rcases hw with hw | hw <;> simp [hw]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hcond)] at hi
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hi
  have hrep : (e6SimpleE i).1 (h3ZornBasis k) =
      ∑ r : Fin 27, ((h3zornToMatrix (e6SimpleE i).1) r k) • h3ZornBasis r := by
    rw [← h3ZornBasis.sum_repr ((e6SimpleE i).1 (h3ZornBasis k))]
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1; exact (h3zornToMatrix_apply (e6SimpleE i).1 r k).symm
  rw [hrep]
  refine Finset.sum_eq_zero fun r _ => ?_
  have hzero : (h3zornToMatrix (e6SimpleE i).1) r k = 0 := by
    rw [h3zornToMatrix_e6SimpleE]
    change ((sparseVal (e6SimpleESparse i) r k : ℤ) : ℝ) = 0
    rw [hi r, Int.cast_zero]
  rw [hzero, zero_smul]

private theorem simpleF_kill_of_weight_nonpos_cb (i : Fin 6) (k : Fin 27)
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
    rcases hw with hw | hw <;> simp [hw]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hcond)] at hi
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hi
  have hrep : (e6SimpleF i).1 (h3ZornBasis k) =
      ∑ r : Fin 27, ((h3zornToMatrix (e6SimpleF i).1) r k) • h3ZornBasis r := by
    rw [← h3ZornBasis.sum_repr ((e6SimpleF i).1 (h3ZornBasis k))]
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1; exact (h3zornToMatrix_apply (e6SimpleF i).1 r k).symm
  rw [hrep]
  refine Finset.sum_eq_zero fun r _ => ?_
  have hzero : (h3zornToMatrix (e6SimpleF i).1) r k = 0 := by
    rw [h3zornToMatrix_e6SimpleF]
    change ((sparseVal (e6SimpleFSparse i) r k : ℤ) : ℝ) = 0
    rw [hi r, Int.cast_zero]
  rw [hzero, zero_smul]

private theorem weyl_on_highest_like_cb (i : Fin 6) (s : ℝ) (hs : s ≠ 0) (v : H3Zorn ℝ)
    (hE : (e6SimpleE i).1 v = 0)
    (hEF : (e6SimpleE i).1 ((e6SimpleF i).1 v) = v) :
    (e6SimpleX i s).1 ((e6SimpleY i (-s⁻¹)).1 ((e6SimpleX i s).1 v)) =
      (-s⁻¹) • (e6SimpleF i).1 v := by
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

private theorem weyl_on_lowest_like_cb (i : Fin 6) (s : ℝ) (hs : s ≠ 0) (v : H3Zorn ℝ)
    (hF : (e6SimpleF i).1 v = 0)
    (hFE : (e6SimpleF i).1 ((e6SimpleE i).1 v) = v) :
    (e6SimpleX i s).1 ((e6SimpleY i (-s⁻¹)).1 ((e6SimpleX i s).1 v)) =
      s • (e6SimpleE i).1 v := by
  have hEE : (e6RootVec (eSimpleIdx i)).1 = (e6SimpleE i).1 := rfl
  have h1 : (e6SimpleX i s).1 v = v + s • (e6SimpleE i).1 v := rfl
  have h2 : (e6SimpleY i (-s⁻¹)).1 (v + s • (e6SimpleE i).1 v) = s • (e6SimpleE i).1 v := by
    change v + s • (e6SimpleE i).1 v + (-s⁻¹) • (e6SimpleF i).1 (v + s • (e6SimpleE i).1 v) = _
    rw [map_add, map_smul, hF, hFE, zero_add, smul_smul,
      show (-s⁻¹) * s = -1 by rw [neg_mul, inv_mul_cancel₀ hs], neg_one_smul]
    module
  have h3 : (e6SimpleX i s).1 (s • (e6SimpleE i).1 v) = s • (e6SimpleE i).1 v := by
    change s • (e6SimpleE i).1 v + s • (e6RootVec (eSimpleIdx i)).1 (s • (e6SimpleE i).1 v) = _
    rw [hEE, map_smul, e6SimpleE_sq_apply_cb, smul_zero, smul_zero, add_zero]
  rw [h1, h2, h3]

private theorem h3zornWeight_values_cb (k : Fin 27) (i : Fin 6) :
    h3zornWeight k i = -1 ∨ h3zornWeight k i = 0 ∨ h3zornWeight k i = 1 := by
  have hchk : (List.finRange 27).all (fun k => (List.finRange 6).all (fun i =>
      (h3zornWeight k i == -1) || (h3zornWeight k i == 0) || (h3zornWeight k i == 1))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, beq_iff_eq] at hchk
  rcases hchk k i with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

private theorem neg_inv_val_neg_one_cb : -(((-1 : ℝˣ)⁻¹ : ℝˣ) : ℝ) = 1 := by norm_num

private theorem zpow_neg_mul_self_cb (t : ℝˣ) (z : ℤ) :
    (t : ℝ) ^ (-z) * (t : ℝ) ^ z = 1 := by
  rw [← zpow_add₀ t.ne_zero, neg_add_cancel, zpow_zero]

theorem e6TorusElt_apply_basis (i : Fin 6) (t : ℝˣ) (k : Fin 27) :
    (e6TorusElt i t).1 (h3ZornBasis k) = ((t ^ h3zornWeight k i : ℝˣ) : ℝ) • h3ZornBasis k := by
  have hmul_torus : (e6TorusElt i t).1 (h3ZornBasis k) =
      (e6WeylElt i t).1 ((e6WeylElt i (-1)).1 (h3ZornBasis k)) := rfl
  have hw_unfold : ∀ (s : ℝˣ) (v : H3Zorn ℝ),
      (e6WeylElt i s).1 v =
        (e6SimpleX i (s : ℝ)).1 ((e6SimpleY i (-((s⁻¹ : ℝˣ) : ℝ))).1
          ((e6SimpleX i (s : ℝ)).1 v)) := fun _ _ => rfl
  rw [hmul_torus]
  rcases h3zornWeight_values_cb k i with hm1 | h0 | h1
  · have hF : (e6SimpleF i).1 (h3ZornBasis k) = 0 :=
      simpleF_kill_of_weight_nonpos_cb i k (Or.inr hm1)
    have hFE : (e6SimpleF i).1 ((e6SimpleE i).1 (h3ZornBasis k)) = h3ZornBasis k := by
      have hc := e6Simple_comm_apply_cb i (h3ZornBasis k)
      rw [hF, map_zero, zero_sub, e6SimpleH_apply_basis, hm1, Int.cast_neg, Int.cast_one] at hc
      change -((e6SimpleF i).1 ((e6SimpleE i).1 (h3ZornBasis k))) = (-1 : ℝ) • h3ZornBasis k at hc
      simpa using congrArg Neg.neg hc
    have h1_res : (e6WeylElt i (-1)).1 (h3ZornBasis k) = -(e6SimpleE i).1 (h3ZornBasis k) := by
      rw [hw_unfold]
      have hs : ((-1 : ℝˣ) : ℝ) ≠ 0 := by norm_num
      have hloc := weyl_on_lowest_like_cb i (-1) hs (h3ZornBasis k) hF hFE
      simpa [neg_inv_val_neg_one_cb] using hloc
    let u := (e6SimpleE i).1 (h3ZornBasis k)
    have hEu : (e6SimpleE i).1 u = 0 := e6SimpleE_sq_apply_cb i (h3ZornBasis k)
    have hEFu : (e6SimpleE i).1 ((e6SimpleF i).1 u) = u := by dsimp [u]; rw [hFE]
    have ht_res : (e6WeylElt i t).1 u = (-((t⁻¹ : ℝˣ) : ℝ)) • (h3ZornBasis k) := by
      rw [hw_unfold]
      have hloc := weyl_on_highest_like_cb i (t : ℝ) t.ne_zero u hEu hEFu
      rw [Units.val_inv_eq_inv_val]
      simpa [u, hFE] using hloc
    rw [h1_res, map_neg, ht_res, hm1, zpow_neg_one, Units.val_inv_eq_inv_val]
    module
  · have hE : (e6SimpleE i).1 (h3ZornBasis k) = 0 :=
      simpleE_kill_of_weight_nonneg_cb i k (Or.inl h0)
    have hF : (e6SimpleF i).1 (h3ZornBasis k) = 0 :=
      simpleF_kill_of_weight_nonpos_cb i k (Or.inl h0)
    have hfix : ∀ (s : ℝˣ), (e6WeylElt i s).1 (h3ZornBasis k) = h3ZornBasis k := by
      intro s
      rw [hw_unfold]
      simp only [e6SimpleX, e6SimpleY, e6SqZeroExp_coe, e6RootExpEquiv_apply]
      rw [hE, smul_zero, add_zero, hF, smul_zero, add_zero, hE, smul_zero, add_zero]
    rw [hfix (-1), hfix t, h0, zpow_zero, Units.val_one, one_smul]
  · have hE : (e6SimpleE i).1 (h3ZornBasis k) = 0 :=
      simpleE_kill_of_weight_nonneg_cb i k (Or.inr h1)
    have hEF : (e6SimpleE i).1 ((e6SimpleF i).1 (h3ZornBasis k)) = h3ZornBasis k := by
      have hc := e6Simple_comm_apply_cb i (h3ZornBasis k)
      rw [hE, map_zero, sub_zero, e6SimpleH_apply_basis, h1] at hc
      simpa using hc
    have h1_res : (e6WeylElt i (-1)).1 (h3ZornBasis k) = (e6SimpleF i).1 (h3ZornBasis k) := by
      rw [hw_unfold]
      have hs : ((-1 : ℝˣ) : ℝ) ≠ 0 := by norm_num
      have hloc := weyl_on_highest_like_cb i (-1) hs (h3ZornBasis k) hE hEF
      simpa [neg_inv_val_neg_one_cb] using hloc
    let u := (e6SimpleF i).1 (h3ZornBasis k)
    have hFu : (e6SimpleF i).1 u = 0 := e6SimpleF_sq_apply_cb i (h3ZornBasis k)
    have hFEu : (e6SimpleF i).1 ((e6SimpleE i).1 u) = u := by dsimp [u]; rw [hEF]
    have ht_res : (e6WeylElt i t).1 u = (t : ℝ) • h3ZornBasis k := by
      rw [hw_unfold]
      have hloc := weyl_on_lowest_like_cb i (t : ℝ) t.ne_zero u hFu hFEu
      simpa [u, hEF] using hloc
    rw [h1_res, ht_res, h1, zpow_one]

theorem e6TorusElt_symm_apply_basis (i : Fin 6) (t : ℝˣ) (k : Fin 27) :
    (e6TorusElt i t).1.symm (h3ZornBasis k) =
      ((t : ℝ) ^ (-h3zornWeight k i)) • h3ZornBasis k := by
  rw [LinearEquiv.symm_apply_eq, map_smul, e6TorusElt_apply_basis, smul_smul,
    Units.val_zpow_eq_zpow_val, zpow_neg_mul_self_cb, one_smul]

end RootExponentials

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
  · funext k; fin_cases k <;> [exact h 1; exact h 2; exact h 3]
  · funext k; fin_cases k <;> [exact h 4; exact h 5; exact h 6]
  · exact h 7

theorem zornCoord_eq_zero_iff (u : ZornVectorMatrix ℝ) :
    (∀ i : Fin 8, zornCoord u i = 0) ↔ u = 0 := by
  constructor
  · intro h
    exact zorn_eq_of_zornCoord_eq fun i => (h i).trans (by fin_cases i <;> rfl)
  · rintro rfl i
    fin_cases i <;> rfl

private theorem zorn_eq_zero_of_half_smul_eq_zero {u : ZornVectorMatrix ℝ}
    (h : ZornVectorMatrix.smul (1 / 2 : ℝ) u = 0) : u = 0 := by
  rw [← zornCoord_eq_zero_iff]; intro i
  have hi := congrArg (fun x => zornCoord x i) h
  have hsm : zornCoord (ZornVectorMatrix.smul (1 / 2 : ℝ) u) i = (1 / 2 : ℝ) * zornCoord u i := by
    fin_cases i <;> rfl
  have hz : zornCoord (0 : ZornVectorMatrix ℝ) i = 0 := by fin_cases i <;> rfl
  rw [hsm, hz] at hi
  exact (mul_eq_zero.mp hi).resolve_left (by norm_num)

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

theorem h3ZornCoordinate_e6TorusElt (i : Fin 6) (t : ℝˣ) (X : H3Zorn ℝ) (m : Fin 27) :
    h3ZornCoordinate ((e6TorusElt i t).1 X) m =
      (t : ℝ) ^ (h3zornWeight m i) * h3ZornCoordinate X m := by
  have hrep : X = ∑ k : Fin 27, h3ZornCoordinate X k • h3ZornBasis k :=
    (h3ZornBasis.sum_repr X).symm
  conv_lhs => rw [hrep, map_sum]
  change h3ZornCoordinateLM (∑ k : Fin 27, (e6TorusElt i t).1 (h3ZornCoordinate X k • h3ZornBasis k)) m = _
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single m]
  · rw [map_smul]
    change h3ZornCoordinate (h3ZornCoordinate X m • (e6TorusElt i t).1 (h3ZornBasis m)) m = _
    rw [h3ZornCoordinate_smul, e6TorusElt_apply_basis, h3ZornCoordinate_smul,
      h3ZornCoordinate_basis_self]
    simp only [↓reduceIte, one_mul, Units.val_zpow_eq_zpow_val, mul_comm]
  · intro k _ hk
    rw [map_smul]
    change h3ZornCoordinate (h3ZornCoordinate X k • (e6TorusElt i t).1 (h3ZornBasis k)) m = 0
    rw [h3ZornCoordinate_smul, e6TorusElt_apply_basis, h3ZornCoordinate_smul,
      h3ZornCoordinate_basis_self]
    simp [hk]
  · intro hm; exact absurd (Finset.mem_univ m) hm

private theorem rootExp_coord_unchanged (r : Fin 72) (m : Fin 27) (t : ℝ) (X : H3Zorn ℝ)
    (hrow : ∀ k : Fin 27, sparseVal (e6RootSparse r) m k = 0) :
    h3ZornCoordinate ((e6RootExp r t).1 X) m = h3ZornCoordinate X m := by
  rw [h3ZornCoordinate_e6RootExp]
  have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse r) m k : ℝ) *
      h3ZornCoordinate X k) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hrow k, Int.cast_zero, zero_mul]
  rw [hs, mul_zero, add_zero]

private theorem rootExp_coord_add_single (r : Fin 72) (m k₀ : Fin 27) (c t : ℝ) (X : H3Zorn ℝ)
    (hrow : ∀ k : Fin 27, (sparseVal (e6RootSparse r) m k : ℝ) = if k = k₀ then c else 0) :
    h3ZornCoordinate ((e6RootExp r t).1 X) m =
      h3ZornCoordinate X m + t * c * h3ZornCoordinate X k₀ := by
  rw [h3ZornCoordinate_e6RootExp]
  have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse r) m k : ℝ) * h3ZornCoordinate X k) =
      c * h3ZornCoordinate X k₀ := by
    rw [Finset.sum_eq_single k₀]
    · rw [hrow k₀]; simp
    · intro k _ hk
      rw [hrow k]; simp [hk]
    · intro h; exact absurd (Finset.mem_univ k₀) h
  rw [hs, mul_assoc]

private theorem h3Zorn_diag_sum_one : h3_diag₁ + h3_diag₂ + h3_diag₃ = (1 : H3Zorn ℝ) := by
  apply ext_h3 <;> simp [h3_diag₁, h3_diag₂, h3_diag₃, add_readback, one_readback,
    ZornVectorMatrix.add_zero]

private theorem h3_diag₂_mul_h3_diag₁ : h3_diag₂ * h3_diag₁ = 0 := by
  rw [mul_comm]; exact h3_diag₁_mul_h3_diag₂

private theorem h3_diag₃_mul_h3_diag₁ : h3_diag₃ * h3_diag₁ = 0 := by
  rw [mul_comm]; exact h3_diag₁_mul_h3_diag₃

private theorem h3_diag₃_mul_h3_diag₂ : h3_diag₃ * h3_diag₂ = 0 := by
  rw [mul_comm]; exact h3_diag₂_mul_h3_diag₃

private theorem zorn_norm_of_mid_zero {u : ZornVectorMatrix ℝ}
    (hmid : ∀ j : Fin 6, zornCoord u ⟨1 + j.val, by omega⟩ = 0) :
    ZornVectorMatrix.norm u = zornCoord u 0 * zornCoord u 7 := by
  have hv0 : u.v 0 = 0 := hmid 0
  have hv1 : u.v 1 = 0 := hmid 1
  have hv2 : u.v 2 = 0 := hmid 2
  have hw0 : u.w 0 = 0 := hmid 3
  have hw1 : u.w 1 = 0 := hmid 4
  have hw2 : u.w 2 = 0 := hmid 5
  simp [ZornVectorMatrix.norm, ZornVec3.dot, Fin.sum_univ_three, zornCoord,
    hv0, hv1, hv2, hw0, hw1, hw2]

private theorem zornBilin_self_eq_two_mul_norm (u : ZornVectorMatrix ℝ) :
    zornBilin u u = 2 * ZornVectorMatrix.norm u := by
  simp [zornBilin, ZornVectorMatrix.norm, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
    ZornVectorMatrix.conj, ZornVec3.dot, Fin.sum_univ_three]
  ring

private theorem zorn_norm_one_eq : ZornVectorMatrix.norm (ZornVectorMatrix.one : ZornVectorMatrix ℝ) = 1 := by
  simp [ZornVectorMatrix.norm, ZornVectorMatrix.one, ZornVec3.dot]

private theorem zorn_conj_eq_trace_sub (x : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.conj x =
      ZornVectorMatrix.sub (ZornVectorMatrix.smul (ZornVectorMatrix.trace x) ZornVectorMatrix.one) x := by
  ext i <;> simp [ZornVectorMatrix.conj, ZornVectorMatrix.sub, ZornVectorMatrix.add,
    ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.trace, ZornVectorMatrix.one]

private theorem zorn_conj_mul_one_eq (x : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.mul ZornVectorMatrix.one (ZornVectorMatrix.conj x) =
      ZornVectorMatrix.conj x ∧
    ZornVectorMatrix.mul (ZornVectorMatrix.conj x) ZornVectorMatrix.one =
      ZornVectorMatrix.conj x := by
  constructor <;> ext i <;> simp [ZornVectorMatrix.mul, ZornVectorMatrix.one, ZornVectorMatrix.conj,
    ZornVec3.dot, ZornVec3.cross]

private theorem jordanAut_map_zero (A : H3ZornJordanAut) : A 0 = 0 :=
  A.toLinearEquiv.map_zero

private theorem jordanAut_map_add (A : H3ZornJordanAut) (x y : H3Zorn ℝ) : A (x + y) = A x + A y :=
  A.toLinearEquiv.map_add x y

private theorem jordanAut_map_smul (A : H3ZornJordanAut) (c : ℝ) (x : H3Zorn ℝ) :
    A (c • x) = c • A x :=
  A.toLinearEquiv.map_smul c x

private def weylOneSparseMat (i : Fin 6) : SparseMat27 :=
  match i.val with
  | 0 => [(0, 19, 1), (1, 1, 1), (2, 26, -1), (3, 18, 1), (4, 12, -1), (5, 13, -1), (6, 14, -1),
      (7, 7, 1), (8, 8, 1), (9, 9, 1), (10, 10, 1), (11, 11, 1), (12, 4, 1), (13, 5, 1),
      (14, 6, 1), (15, 15, 1), (16, 16, 1), (17, 17, 1), (18, 3, -1), (19, 0, -1), (20, 20, 1),
      (21, 21, 1), (22, 22, 1), (23, 23, 1), (24, 24, 1), (25, 25, 1), (26, 2, 1)]
  | 1 => [(0, 0, 1), (1, 1, 1), (2, 2, 1), (3, 3, 1), (4, 5, 1), (5, 4, -1), (6, 6, 1),
      (7, 8, 1), (8, 7, -1), (9, 9, 1), (10, 10, 1), (11, 11, 1), (12, 13, 1), (13, 12, -1),
      (14, 14, 1), (15, 16, 1), (16, 15, -1), (17, 17, 1), (18, 18, 1), (19, 19, 1), (20, 21, 1),
      (21, 20, -1), (22, 22, 1), (23, 24, 1), (24, 23, -1), (25, 25, 1), (26, 26, 1)]
  | 2 => [(0, 9, -1), (1, 6, -1), (2, 2, 1), (3, 3, 1), (4, 4, 1), (5, 5, 1), (6, 1, 1),
      (7, 7, 1), (8, 8, 1), (9, 0, 1), (10, 10, 1), (11, 11, 1), (12, 24, 1), (13, 23, -1),
      (14, 14, 1), (15, 15, 1), (16, 16, 1), (17, 26, -1), (18, 22, 1), (19, 19, 1), (20, 20, 1),
      (21, 21, 1), (22, 18, -1), (23, 13, 1), (24, 12, -1), (25, 25, 1), (26, 17, 1)]
  | 3 => [(0, 0, 1), (1, 1, 1), (2, 2, 1), (3, 3, 1), (4, 4, 1), (5, 6, 1), (6, 5, -1),
      (7, 7, 1), (8, 9, 1), (9, 8, -1), (10, 10, 1), (11, 11, 1), (12, 12, 1), (13, 14, 1),
      (14, 13, -1), (15, 15, 1), (16, 17, 1), (17, 16, -1), (18, 18, 1), (19, 19, 1), (20, 20, 1),
      (21, 22, 1), (22, 21, -1), (23, 23, 1), (24, 25, 1), (25, 24, -1), (26, 26, 1)]
  | 4 => [(0, 6, -1), (1, 9, -1), (2, 2, 1), (3, 3, 1), (4, 4, 1), (5, 5, 1), (6, 0, 1),
      (7, 7, 1), (8, 8, 1), (9, 1, 1), (10, 10, 1), (11, 25, 1), (12, 12, 1), (13, 13, 1),
      (14, 19, -1), (15, 21, -1), (16, 20, 1), (17, 17, 1), (18, 18, 1), (19, 14, 1), (20, 16, -1),
      (21, 15, 1), (22, 22, 1), (23, 23, 1), (24, 24, 1), (25, 11, -1), (26, 26, 1)]
  | _ => [(0, 26, -1), (1, 1, 1), (2, 19, 1), (3, 3, 1), (4, 4, 1), (5, 5, 1), (6, 6, 1),
      (7, 15, 1), (8, 16, 1), (9, 17, 1), (10, 11, -1), (11, 10, 1), (12, 12, 1), (13, 13, 1),
      (14, 14, 1), (15, 7, -1), (16, 8, -1), (17, 9, -1), (18, 18, 1), (19, 2, -1), (20, 20, 1),
      (21, 21, 1), (22, 22, 1), (23, 23, 1), (24, 24, 1), (25, 25, 1), (26, 0, 1)]

private theorem sparseVal_eq_zero_of_not_mem_cb (s : SparseMat27) (i j : Fin 27)
    (h : ∀ p ∈ s, ¬(p.1 = i ∧ p.2.1 = j)) : sparseVal s i j = 0 := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    rcases p with ⟨r, c, v⟩
    have hp := h (r, c, v) List.mem_cons_self
    have hs : ∀ q ∈ s, ¬(q.1 = i ∧ q.2.1 = j) := fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hrc : (r == i && c == j) = false := by
      rw [Bool.eq_false_iff, ne_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
      exact hp
    simp only [sparseVal_cons, hrc, Bool.false_eq_true, ↓reduceIte, zero_add, ih hs]

private def sparseEqOneAdd_cb (w d : SparseMat27) : Bool :=
  (List.finRange 27).all (fun k => sparseVal w k k == 1 + sparseVal d k k) &&
  w.all (fun p => sparseVal w p.1 p.2.1 == (if p.1 == p.2.1 then 1 else 0) + sparseVal d p.1 p.2.1) &&
  d.all (fun p => sparseVal w p.1 p.2.1 == (if p.1 == p.2.1 then 1 else 0) + sparseVal d p.1 p.2.1)

private theorem sparseToMat_eq_one_add_of_check_cb (w d : SparseMat27)
    (h : sparseEqOneAdd_cb w d = true) :
    sparseToMat w = (1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat d := by
  simp only [sparseEqOneAdd_cb, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies, beq_iff_eq] at h
  rcases h with ⟨⟨hdiag, hw⟩, hd⟩
  ext r c
  change sparseVal w r c = (1 : Matrix (Fin 27) (Fin 27) ℤ) r c + sparseVal d r c
  by_cases hrc : r = c
  · subst hrc
    simpa [Matrix.one_apply] using hdiag r
  · rw [Matrix.one_apply_ne hrc, zero_add]
    by_cases hmw : ∃ p ∈ w, p.1 = r ∧ p.2.1 = c
    · rcases hmw with ⟨p, hpw, rfl, rfl⟩
      simpa [hrc] using hw p hpw
    · by_cases hmd : ∃ p ∈ d, p.1 = r ∧ p.2.1 = c
      · rcases hmd with ⟨p, hpd, rfl, rfl⟩
        simpa [hrc] using hd p hpd
      · have hw0 := sparseVal_eq_zero_of_not_mem_cb w r c (fun p hp hpe => hmw ⟨p, hp, hpe⟩)
        have hd0 := sparseVal_eq_zero_of_not_mem_cb d r c (fun p hp hpe => hmd ⟨p, hp, hpe⟩)
        rw [hw0, hd0]

private def weylDeltaSparse_cb (i : Fin 6) : SparseMat27 :=
  let E := e6SimpleESparse i
  let F := e6SimpleFSparse i
  sparseSub (sparseSub (sparseSub E F) (sparseMul E F)) (sparseMul F E)

private theorem weyl_expand_mat_cb (E F : Matrix (Fin 27) (Fin 27) ℤ)
    (hEE : E * E = 0) (hEFE : E * (F * E) = E) :
    (1 + E) * ((1 - F) * (1 + E)) = 1 + E - F - E * F - F * E := by
  simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, hEE, hEFE]
  abel

private theorem e6SimpleESparse_mul_self_cb (i : Fin 6) :
    sparseToMat (e6SimpleESparse i) * sparseToMat (e6SimpleESparse i) = 0 := by
  rw [← sparseToMat_mul]
  fin_cases i <;> exact sparseToMat_eq_zero_of_sparseZeroCheck (by decide)

private theorem e6SimpleESparse_mul_F_mul_E_cb (i : Fin 6) :
    sparseToMat (e6SimpleESparse i) *
      (sparseToMat (e6SimpleFSparse i) * sparseToMat (e6SimpleESparse i)) =
      sparseToMat (e6SimpleESparse i) := by
  rw [← sparseToMat_mul, ← sparseToMat_mul]
  fin_cases i <;> exact sparseToMat_eq_of_sparseEq (by decide)

private theorem sparseToMat_weylOneSparseMat_eq (i : Fin 6) :
    sparseToMat (weylOneSparseMat i) =
      ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat (e6SimpleESparse i)) *
        (((1 : Matrix (Fin 27) (Fin 27) ℤ) - sparseToMat (e6SimpleFSparse i)) *
          ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat (e6SimpleESparse i))) := by
  rw [weyl_expand_mat_cb _ _ (e6SimpleESparse_mul_self_cb i) (e6SimpleESparse_mul_F_mul_E_cb i)]
  have hwd : sparseToMat (weylOneSparseMat i) =
      (1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat (weylDeltaSparse_cb i) := by
    fin_cases i <;> exact sparseToMat_eq_one_add_of_check_cb _ _ (by decide)
  rw [hwd]
  simp only [weylDeltaSparse_cb, sparseToMat_sub, sparseToMat_mul]
  abel

private theorem h3zornToMatrix_e6WeylOne (i : Fin 6) :
    h3zornToMatrix ((e6WeylElt i 1).1.toLinearMap) =
      (sparseToMat (weylOneSparseMat i)).map Int.cast := by
  have h1m : h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) = 1 := _root_.map_one h3zornToMatrix
  have hx : h3zornToMatrix (e6SimpleX i 1).1.toLinearMap =
      ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat (e6SimpleESparse i)).map Int.cast := by
    change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + (1 : ℝ) • (e6SimpleE i).1) = _
    rw [one_smul, map_add, h1m, h3zornToMatrix_e6SimpleE]
    ext r c
    by_cases h : r = c <;> simp [h]
  have hy : h3zornToMatrix (e6SimpleY i (-1)).1.toLinearMap =
      ((1 : Matrix (Fin 27) (Fin 27) ℤ) - sparseToMat (e6SimpleFSparse i)).map Int.cast := by
    change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + (-1 : ℝ) • (e6SimpleF i).1) = _
    rw [neg_one_smul, ← sub_eq_add_neg, map_sub, h1m, h3zornToMatrix_e6SimpleF]
    ext r c
    by_cases h : r = c <;> simp [h]
  have hm : ((e6WeylElt i 1).1 : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ).toLinearMap =
      (e6SimpleX i 1).1.toLinearMap *
        ((e6SimpleY i (-1)).1.toLinearMap * (e6SimpleX i 1).1.toLinearMap) := by
    simp [e6WeylElt, mul_assoc]
  rw [hm, map_mul, map_mul, hx, hy, sparseToMat_weylOneSparseMat_eq i]
  ext r c
  simp [Matrix.mul_apply]

private theorem h3ZornCoordinate_e6WeylElt_one (i : Fin 6) (X : H3Zorn ℝ) (m : Fin 27) :
    h3ZornCoordinate ((e6WeylElt i 1).1 X) m =
      ∑ k : Fin 27, (sparseVal (weylOneSparseMat i) m k : ℝ) * h3ZornCoordinate X k := by
  have hrep : X = ∑ k : Fin 27, h3ZornCoordinate X k • h3ZornBasis k :=
    (h3ZornBasis.sum_repr X).symm
  conv_lhs => rw [hrep, map_sum]
  change h3ZornCoordinateLM (∑ k : Fin 27, (e6WeylElt i 1).1 (h3ZornCoordinate X k • h3ZornBasis k)) m = _
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  change h3ZornCoordinate (h3ZornCoordinate X k • (e6WeylElt i 1).1 (h3ZornBasis k)) m = _
  rw [h3ZornCoordinate_smul, mul_comm]
  congr 1
  have hm : h3ZornCoordinate ((e6WeylElt i 1).1 (h3ZornBasis k)) m =
      h3zornToMatrix ((e6WeylElt i 1).1.toLinearMap) m k :=
    (h3zornToMatrix_apply (e6WeylElt i 1).1.toLinearMap m k).symm
  rw [hm, h3zornToMatrix_e6WeylOne i, Matrix.map_apply, sparseToMat]

end CoordinateReadout

section PartATransitivity

private def slot0Pos (j : Fin 8) : Fin 72 := ⟨24 + 2 * j.val, by omega⟩
private def slot0Neg (j : Fin 8) : Fin 72 := ⟨25 + 2 * j.val, by omega⟩
private def slot1Pos (j : Fin 8) : Fin 72 := ⟨40 + 2 * j.val, by omega⟩
private def slot1Neg (j : Fin 8) : Fin 72 := ⟨41 + 2 * j.val, by omega⟩
private def slot2Pos (j : Fin 8) : Fin 72 := ⟨56 + 2 * j.val, by omega⟩
private def slot2Neg (j : Fin 8) : Fin 72 := ⟨57 + 2 * j.val, by omega⟩

private def dualIdx : Fin 8 → Fin 8
  | 0 => 7 | 1 => 4 | 2 => 5 | 3 => 6 | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 0

private def dualSign : Fin 8 → ℤ
  | 0 => 1 | 7 => 1 | _ => -1

private theorem dualSign_ne_zero (j : Fin 8) : (dualSign j : ℝ) ≠ 0 := by
  fin_cases j <;> norm_num [dualSign]

private theorem slot0Pos_row0_check :
    (List.finRange 8).all (fun j => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot0Pos j)) 0 k ==
        if k.val = 3 + (dualIdx j).val then dualSign j else 0)) = true := by
  decide

private theorem slot2Neg_row0_check :
    (List.finRange 8).all (fun j => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot2Neg j)) 0 k ==
        if k.val = 19 + (dualIdx j).val then dualSign j else 0)) = true := by
  decide

private theorem slot0Neg_row0_check :
    (List.finRange 8).all (fun j => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot0Neg j)) 0 k == 0)) = true := by
  decide

private theorem slot0Neg_a_check :
    (List.finRange 8).all (fun j => (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot0Neg j)) ⟨3 + i.val, by omega⟩ k ==
        if i = j ∧ k.val = 0 then 1 else 0))) = true := by
  decide

private theorem slot0Neg_c_check :
    (List.finRange 8).all (fun j => (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot0Neg j)) ⟨19 + i.val, by omega⟩ k == 0))) = true := by
  decide

private theorem slot2Pos_row0_check :
    (List.finRange 8).all (fun j => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot2Pos j)) 0 k == 0)) = true := by
  decide

private theorem slot2Pos_a_check :
    (List.finRange 8).all (fun j => (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot2Pos j)) ⟨3 + i.val, by omega⟩ k == 0))) = true := by
  decide

private theorem slot2Pos_c_check :
    (List.finRange 8).all (fun j => (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot2Pos j)) ⟨19 + i.val, by omega⟩ k ==
        if i = j ∧ k.val = 0 then 1 else 0))) = true := by
  decide

private theorem slot1Pos_row0_check :
    (List.finRange 8).all (fun j => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot1Pos j)) 0 k == 0)) = true := by
  decide

private theorem slot1Pos_row1_check :
    (List.finRange 8).all (fun j => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot1Pos j)) 1 k ==
        if k.val = 11 + (dualIdx j).val then dualSign j else 0)) = true := by
  decide

private theorem slot1Pos_a_check :
    (List.finRange 8).all (fun j => (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      if k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19) then
        sparseVal (e6RootSparse (slot1Pos j)) ⟨3 + i.val, by omega⟩ k == 0
      else true))) = true := by
  decide

private theorem slot1Pos_c_check :
    (List.finRange 8).all (fun j => (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      if k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19) then
        sparseVal (e6RootSparse (slot1Pos j)) ⟨19 + i.val, by omega⟩ k == 0
      else true))) = true := by
  decide

private theorem slot1Neg_row01_check :
    (List.finRange 8).all (fun j => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (slot1Neg j)) 0 k == 0) &&
      (sparseVal (e6RootSparse (slot1Neg j)) 1 k == 0))) = true := by
  decide

private theorem slot1Neg_a_check :
    (List.finRange 8).all (fun j => (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot1Neg j)) ⟨3 + i.val, by omega⟩ k == 0))) = true := by
  decide

private theorem slot1Neg_b_check :
    (List.finRange 8).all (fun j => (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      sparseVal (e6RootSparse (slot1Neg j)) ⟨11 + i.val, by omega⟩ k ==
        if i = j ∧ k.val = 1 then 1 else 0))) = true := by
  decide

private theorem slot1Neg_c_check :
    (List.finRange 8).all (fun j => (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      if k.val < 3 ∨ 11 ≤ k.val then
        sparseVal (e6RootSparse (slot1Neg j)) ⟨19 + i.val, by omega⟩ k == 0
      else true))) = true := by
  decide

private theorem slot0Pos_alpha1 (j : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot0Pos j) t).1 X).α₁ =
      X.α₁ + t * (dualSign j : ℝ) * zornCoord X.a (dualIdx j) := by
  have hc := slot0Pos_row0_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  change h3ZornCoordinate ((e6RootExp (slot0Pos j) t).1 X) 0 = _
  rw [rootExp_coord_add_single (slot0Pos j) 0 ⟨3 + (dualIdx j).val, by omega⟩ (dualSign j) t X
    (fun k => by
      rw [hc j k]
      by_cases h : k.val = 3 + (dualIdx j).val
      · have he : k = ⟨3 + (dualIdx j).val, by omega⟩ := Fin.ext h
        simp [he]
      · have he : k ≠ ⟨3 + (dualIdx j).val, by omega⟩ := fun heq => h (congrArg Fin.val heq)
        simp [h, he])]
  rw [h3ZornCoord_zero_eq, h3ZornCoord_a_eq]

private theorem slot2Neg_alpha1 (j : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot2Neg j) t).1 X).α₁ =
      X.α₁ + t * (dualSign j : ℝ) * zornCoord X.c (dualIdx j) := by
  have hc := slot2Neg_row0_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  change h3ZornCoordinate ((e6RootExp (slot2Neg j) t).1 X) 0 = _
  rw [rootExp_coord_add_single (slot2Neg j) 0 ⟨19 + (dualIdx j).val, by omega⟩ (dualSign j) t X
    (fun k => by
      rw [hc j k]
      by_cases h : k.val = 19 + (dualIdx j).val
      · have he : k = ⟨19 + (dualIdx j).val, by omega⟩ := Fin.ext h
        simp [he]
      · have he : k ≠ ⟨19 + (dualIdx j).val, by omega⟩ := fun heq => h (congrArg Fin.val heq)
        simp [h, he])]
  rw [h3ZornCoord_zero_eq, h3ZornCoord_c_eq]

private theorem slot0Neg_action (j : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot0Neg j) t).1 X).α₁ = X.α₁ ∧
    ((e6RootExp (slot0Neg j) t).1 X).c = X.c ∧
    zornCoord ((e6RootExp (slot0Neg j) t).1 X).a j = zornCoord X.a j + t * X.α₁ ∧
    (∀ i : Fin 8, i ≠ j → zornCoord ((e6RootExp (slot0Neg j) t).1 X).a i = zornCoord X.a i) := by
  have h0 := slot0Neg_row0_check
  have ha := slot0Neg_a_check
  have hc := slot0Neg_c_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h0 ha hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((e6RootExp (slot0Neg j) t).1 X) 0 = h3ZornCoordinate X 0
    exact rootExp_coord_unchanged (slot0Neg j) 0 t X (fun k => h0 j k)
  · refine zorn_eq_of_zornCoord_eq fun i => ?_
    rw [← h3ZornCoord_c_eq, ← h3ZornCoord_c_eq]
    exact rootExp_coord_unchanged (slot0Neg j) ⟨19 + i.val, by omega⟩ t X (fun k => hc j i k)
  · rw [← h3ZornCoord_a_eq, rootExp_coord_add_single (slot0Neg j) ⟨3 + j.val, by omega⟩ 0 1 t X
      (fun k => by
        rw [ha j j k]
        by_cases hk0 : k = 0
        · subst hk0; simp
        · have hv : k.val ≠ 0 := fun hv => hk0 (Fin.ext hv)
          simp [hk0, hv])]
    rw [h3ZornCoord_a_eq, h3ZornCoord_zero_eq, mul_one]
  · intro i hi
    rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    exact rootExp_coord_unchanged (slot0Neg j) ⟨3 + i.val, by omega⟩ t X
      (fun k => by rw [ha j i k]; simp [hi])

private theorem slot2Pos_action (j : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (slot2Pos j) t).1 X).α₁ = X.α₁ ∧
    ((e6RootExp (slot2Pos j) t).1 X).a = X.a ∧
    zornCoord ((e6RootExp (slot2Pos j) t).1 X).c j = zornCoord X.c j + t * X.α₁ ∧
    (∀ i : Fin 8, i ≠ j → zornCoord ((e6RootExp (slot2Pos j) t).1 X).c i = zornCoord X.c i) := by
  have h0 := slot2Pos_row0_check
  have ha := slot2Pos_a_check
  have hc := slot2Pos_c_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h0 ha hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((e6RootExp (slot2Pos j) t).1 X) 0 = h3ZornCoordinate X 0
    exact rootExp_coord_unchanged (slot2Pos j) 0 t X (fun k => h0 j k)
  · refine zorn_eq_of_zornCoord_eq fun i => ?_
    rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    exact rootExp_coord_unchanged (slot2Pos j) ⟨3 + i.val, by omega⟩ t X (fun k => ha j i k)
  · rw [← h3ZornCoord_c_eq, rootExp_coord_add_single (slot2Pos j) ⟨19 + j.val, by omega⟩ 0 1 t X
      (fun k => by
        rw [hc j j k]
        by_cases hk0 : k = 0
        · subst hk0; simp
        · have hv : k.val ≠ 0 := fun hv => hk0 (Fin.ext hv)
          simp [hk0, hv])]
    rw [h3ZornCoord_c_eq, h3ZornCoord_zero_eq, mul_one]
  · intro i hi
    rw [← h3ZornCoord_c_eq, ← h3ZornCoord_c_eq]
    exact rootExp_coord_unchanged (slot2Pos j) ⟨19 + i.val, by omega⟩ t X
      (fun k => by rw [hc j i k]; simp [hi])

private theorem slot1Pos_action_of_ac_zero (j : Fin 8) (t : ℝ) {X : H3Zorn ℝ}
    (ha : X.a = 0) (hc0 : X.c = 0) :
    ((e6RootExp (slot1Pos j) t).1 X).α₁ = X.α₁ ∧
    ((e6RootExp (slot1Pos j) t).1 X).a = 0 ∧
    ((e6RootExp (slot1Pos j) t).1 X).c = 0 ∧
    ((e6RootExp (slot1Pos j) t).1 X).α₂ =
      X.α₂ + t * (dualSign j : ℝ) * zornCoord X.b (dualIdx j) := by
  have h0 := slot1Pos_row0_check
  have h1 := slot1Pos_row1_check
  have hca := slot1Pos_a_check
  have hcc := slot1Pos_c_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h0 h1 hca hcc
  have hx_ac : ∀ k : Fin 27, ¬(k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19)) →
      h3ZornCoordinate X k = 0 := by
    intro k hk
    by_cases hk11 : k.val < 11
    · have hne : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hne, h3ZornCoord_a_eq, ha]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
    · have hne : k = ⟨19 + (⟨k.val - 19, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hne, h3ZornCoord_c_eq, hc0]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
  refine ⟨?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((e6RootExp (slot1Pos j) t).1 X) 0 = h3ZornCoordinate X 0
    exact rootExp_coord_unchanged (slot1Pos j) 0 t X (fun k => h0 j k)
  · refine zorn_eq_of_zornCoord_eq fun i => ?_
    rw [← h3ZornCoord_a_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_a_eq, ha,
      (zornCoord_eq_zero_iff 0).mpr rfl i, zero_add]
    have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse (slot1Pos j)) ⟨3 + i.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate X k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19)
      · have hm := hca j i k
        rw [ite_eq_left_of_eq_true _ _ (eq_true hk)] at hm
        rw [beq_iff_eq.mp hm, Int.cast_zero, zero_mul]
      · rw [hx_ac k hk, mul_zero]
    rw [hs, mul_zero]
  · refine zorn_eq_of_zornCoord_eq fun i => ?_
    rw [← h3ZornCoord_c_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_c_eq, hc0,
      (zornCoord_eq_zero_iff 0).mpr rfl i, zero_add]
    have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse (slot1Pos j)) ⟨19 + i.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate X k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19)
      · have hm := hcc j i k
        rw [ite_eq_left_of_eq_true _ _ (eq_true hk)] at hm
        rw [beq_iff_eq.mp hm, Int.cast_zero, zero_mul]
      · rw [hx_ac k hk, mul_zero]
    rw [hs, mul_zero]
  · change h3ZornCoordinate ((e6RootExp (slot1Pos j) t).1 X) 1 = _
    rw [rootExp_coord_add_single (slot1Pos j) 1 ⟨11 + (dualIdx j).val, by omega⟩ (dualSign j) t X
      (fun k => by
        rw [h1 j k]
        by_cases h : k.val = 11 + (dualIdx j).val
        · have he : k = ⟨11 + (dualIdx j).val, by omega⟩ := Fin.ext h
          simp [he]
        · have he : k ≠ ⟨11 + (dualIdx j).val, by omega⟩ := fun heq => h (congrArg Fin.val heq)
          simp [h, he])]
    rw [h3ZornCoord_one_eq, h3ZornCoord_b_eq]

private theorem slot1Neg_action_of_ac_zero (j : Fin 8) (t : ℝ) {X : H3Zorn ℝ}
    (ha : X.a = 0) (hc0 : X.c = 0) :
    ((e6RootExp (slot1Neg j) t).1 X).α₁ = X.α₁ ∧
    ((e6RootExp (slot1Neg j) t).1 X).α₂ = X.α₂ ∧
    ((e6RootExp (slot1Neg j) t).1 X).a = 0 ∧
    ((e6RootExp (slot1Neg j) t).1 X).c = 0 ∧
    zornCoord ((e6RootExp (slot1Neg j) t).1 X).b j = zornCoord X.b j + t * X.α₂ ∧
    (∀ i : Fin 8, i ≠ j → zornCoord ((e6RootExp (slot1Neg j) t).1 X).b i = zornCoord X.b i) := by
  have h01 := slot1Neg_row01_check
  have hca := slot1Neg_a_check
  have hcb := slot1Neg_b_check
  have hcc := slot1Neg_c_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at h01 hca hcb hcc
  have hx_a : ∀ k : Fin 27, ¬(k.val < 3 ∨ 11 ≤ k.val) → h3ZornCoordinate X k = 0 := by
    intro k hk
    have hne : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hne, h3ZornCoord_a_eq, ha]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((e6RootExp (slot1Neg j) t).1 X) 0 = h3ZornCoordinate X 0
    exact rootExp_coord_unchanged (slot1Neg j) 0 t X (fun k => (h01 j k).1)
  · change h3ZornCoordinate ((e6RootExp (slot1Neg j) t).1 X) 1 = h3ZornCoordinate X 1
    exact rootExp_coord_unchanged (slot1Neg j) 1 t X (fun k => (h01 j k).2)
  · refine zorn_eq_of_zornCoord_eq fun i => ?_
    rw [← h3ZornCoord_a_eq, rootExp_coord_unchanged (slot1Neg j) ⟨3 + i.val, by omega⟩ t X
      (fun k => hca j i k), h3ZornCoord_a_eq, ha]
  · refine zorn_eq_of_zornCoord_eq fun i => ?_
    rw [← h3ZornCoord_c_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_c_eq, hc0,
      (zornCoord_eq_zero_iff 0).mpr rfl i, zero_add]
    have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse (slot1Neg j)) ⟨19 + i.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate X k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k.val < 3 ∨ 11 ≤ k.val
      · have hm := hcc j i k
        rw [ite_eq_left_of_eq_true _ _ (eq_true hk)] at hm
        rw [beq_iff_eq.mp hm, Int.cast_zero, zero_mul]
      · rw [hx_a k hk, mul_zero]
    rw [hs, mul_zero]
  · rw [← h3ZornCoord_b_eq, rootExp_coord_add_single (slot1Neg j) ⟨11 + j.val, by omega⟩ 1 1 t X
      (fun k => by
        rw [hcb j j k]
        by_cases hk1 : k = 1
        · subst hk1; simp
        · have hv : k.val ≠ 1 := fun hv => hk1 (Fin.ext hv)
          simp [hk1, hv])]
    rw [h3ZornCoord_b_eq, h3ZornCoord_one_eq, mul_one]
  · intro i hi
    rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    exact rootExp_coord_unchanged (slot1Neg j) ⟨11 + i.val, by omega⟩ t X
      (fun k => by rw [hcb j i k]; simp [hi])

private theorem normCubic_of_a_zero_c_zero (X : H3Zorn ℝ) (ha : X.a = 0) (hc : X.c = 0) :
    normCubic X = X.α₁ * (X.α₂ * X.α₃ - ZornVectorMatrix.norm X.b) := by
  simp [normCubic, ha, hc, ZornVectorMatrix.norm, ZornVectorMatrix.mul,
    ZornVectorMatrix.trace, ZornVectorMatrix.zero, ZornVec3.dot]
  ring

private theorem clear_a_of_alpha1_ne_zero (X : H3Zorn ℝ) (h1 : X.α₁ ≠ 0) :
    ∃ h ∈ e6ChevalleySubgroup, (h.1 X).α₁ = X.α₁ ∧ (h.1 X).a = 0 := by
  have hmul : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Y : H3Zorn ℝ),
      (g₁ * g₂).1 Y = g₁.1 (g₂.1 Y) := fun _ _ _ => rfl
  have hind : ∀ n : ℕ, n ≤ 8 → ∃ h ∈ e6ChevalleySubgroup,
      (h.1 X).α₁ = X.α₁ ∧ ∀ i : Fin 8, i.val < n → zornCoord (h.1 X).a i = 0 := by
    intro n hn
    induction n with
    | zero =>
      refine ⟨1, e6ChevalleySubgroup.one_mem, rfl, fun i hi => by omega⟩
    | succ k ih =>
      obtain ⟨h, hh, hα, hk⟩ := ih (by omega)
      let jk : Fin 8 := ⟨k, hn⟩
      let Y := h.1 X
      have hY1 : Y.α₁ ≠ 0 := hα ▸ h1
      let t : ℝ := -zornCoord Y.a jk / Y.α₁
      obtain ⟨s1, _, sa_eq, sa_other⟩ := slot0Neg_action jk t Y
      refine ⟨e6RootExp (slot0Neg jk) t * h,
        e6ChevalleySubgroup.mul_mem (e6RootExp_mem_chevalley _ _) hh, ?_, ?_⟩
      · rw [hmul]; exact s1.trans hα
      · intro i hi
        rw [hmul]
        by_cases hik : i = jk
        · subst hik; rw [sa_eq]; dsimp only [t]; field_simp [hY1]; ring
        · have hik' : i.val < k := by
            have hne : i.val ≠ k := fun heq => hik (Fin.ext heq)
            omega
          rw [sa_other i hik]; exact hk i hik'
  obtain ⟨h, hh, hα, hall⟩ := hind 8 (le_refl 8)
  exact ⟨h, hh, hα, (zornCoord_eq_zero_iff (h.1 X).a).mp fun i => hall i i.isLt⟩

private theorem clear_c_of_alpha1_ne_zero_a_zero (X : H3Zorn ℝ) (h1 : X.α₁ ≠ 0) (ha : X.a = 0) :
    ∃ h ∈ e6ChevalleySubgroup, (h.1 X).α₁ = X.α₁ ∧ (h.1 X).a = 0 ∧ (h.1 X).c = 0 := by
  have hmul : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Y : H3Zorn ℝ),
      (g₁ * g₂).1 Y = g₁.1 (g₂.1 Y) := fun _ _ _ => rfl
  have hind : ∀ n : ℕ, n ≤ 8 → ∃ h ∈ e6ChevalleySubgroup,
      (h.1 X).α₁ = X.α₁ ∧ (h.1 X).a = 0 ∧ ∀ i : Fin 8, i.val < n → zornCoord (h.1 X).c i = 0 := by
    intro n hn
    induction n with
    | zero =>
      refine ⟨1, e6ChevalleySubgroup.one_mem, rfl, ha, fun i hi => by omega⟩
    | succ k ih =>
      obtain ⟨h, hh, hα, hha, hk⟩ := ih (by omega)
      let jk : Fin 8 := ⟨k, hn⟩
      let Y := h.1 X
      have hY1 : Y.α₁ ≠ 0 := hα ▸ h1
      let t : ℝ := -zornCoord Y.c jk / Y.α₁
      obtain ⟨s1, sa, sc_eq, sc_other⟩ := slot2Pos_action jk t Y
      refine ⟨e6RootExp (slot2Pos jk) t * h,
        e6ChevalleySubgroup.mul_mem (e6RootExp_mem_chevalley _ _) hh, ?_, ?_, ?_⟩
      · rw [hmul]; exact s1.trans hα
      · rw [hmul]; exact sa.trans hha
      · intro i hi
        rw [hmul]
        by_cases hik : i = jk
        · subst hik; rw [sc_eq]; dsimp only [t]; field_simp [hY1]; ring
        · have hik' : i.val < k := by
            have hne : i.val ≠ k := fun heq => hik (Fin.ext heq)
            omega
          rw [sc_other i hik]; exact hk i hik'
  obtain ⟨h, hh, hα, hha, hall⟩ := hind 8 (le_refl 8)
  exact ⟨h, hh, hα, hha, (zornCoord_eq_zero_iff (h.1 X).c).mp fun i => hall i i.isLt⟩

private theorem clear_b_of_alpha2_ne_zero_ac_zero (X : H3Zorn ℝ) (h2 : X.α₂ ≠ 0)
    (ha : X.a = 0) (hc : X.c = 0) :
    ∃ h ∈ e6ChevalleySubgroup,
      (h.1 X).α₁ = X.α₁ ∧ (h.1 X).α₂ = X.α₂ ∧ (h.1 X).a = 0 ∧ (h.1 X).b = 0 ∧ (h.1 X).c = 0 := by
  have hmul : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Y : H3Zorn ℝ),
      (g₁ * g₂).1 Y = g₁.1 (g₂.1 Y) := fun _ _ _ => rfl
  have hind : ∀ n : ℕ, n ≤ 8 → ∃ h ∈ e6ChevalleySubgroup,
      (h.1 X).α₁ = X.α₁ ∧ (h.1 X).α₂ = X.α₂ ∧ (h.1 X).a = 0 ∧ (h.1 X).c = 0 ∧
      ∀ i : Fin 8, i.val < n → zornCoord (h.1 X).b i = 0 := by
    intro n hn
    induction n with
    | zero =>
      refine ⟨1, e6ChevalleySubgroup.one_mem, rfl, rfl, ha, hc, fun i hi => by omega⟩
    | succ k ih =>
      obtain ⟨h, hh, hα₁, hα₂, hha, hhc, hk⟩ := ih (by omega)
      let jk : Fin 8 := ⟨k, hn⟩
      let Y := h.1 X
      have hY2 : Y.α₂ ≠ 0 := hα₂ ▸ h2
      let t : ℝ := -zornCoord Y.b jk / Y.α₂
      obtain ⟨s1, s2, sa, sc, sb_eq, sb_other⟩ := slot1Neg_action_of_ac_zero jk t hha hhc
      refine ⟨e6RootExp (slot1Neg jk) t * h,
        e6ChevalleySubgroup.mul_mem (e6RootExp_mem_chevalley _ _) hh, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hmul]; exact s1.trans hα₁
      · rw [hmul]; exact s2.trans hα₂
      · rw [hmul]; exact sa
      · rw [hmul]; exact sc
      · intro i hi
        rw [hmul]
        by_cases hik : i = jk
        · subst hik; rw [sb_eq]; dsimp only [t]; field_simp [hY2]; ring
        · have hik' : i.val < k := by
            have hne : i.val ≠ k := fun heq => hik (Fin.ext heq)
            omega
          rw [sb_other i hik]; exact hk i hik'
  obtain ⟨h, hh, hα₁, hα₂, hha, hhc, hall⟩ := hind 8 (le_refl 8)
  exact ⟨h, hh, hα₁, hα₂, hha, (zornCoord_eq_zero_iff (h.1 X).b).mp fun i => hall i i.isLt, hhc⟩

/-- **Part A (Move `normCubic = 1` to `1`)**: any element of split cubic norm `1` is moved
to `1 : H3Zorn ℝ` by `e6ChevalleySubgroup`. -/
theorem e6ChevalleySubgroup_move_normCubic_one_to_one (X : H3Zorn ℝ) (hN : normCubic X = 1) :
    ∃ h ∈ e6ChevalleySubgroup, h.1 X = 1 := by
  have hmul : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Y : H3Zorn ℝ),
      (g₁ * g₂).1 Y = g₁.1 (g₂.1 Y) := fun _ _ _ => rfl
  -- Step 1: Make α₁ ≠ 0
  have hStep1 : ∃ g₁ ∈ e6ChevalleySubgroup, (g₁.1 X).α₁ ≠ 0 := by
    by_cases h1 : X.α₁ ≠ 0
    · exact ⟨1, e6ChevalleySubgroup.one_mem, h1⟩
    · have h1z : X.α₁ = 0 := not_not.mp h1
      by_cases ha : X.a = 0
      · by_cases hc : X.c = 0
        · exfalso
          rw [normCubic_of_a_zero_c_zero X ha hc, h1z, zero_mul] at hN
          exact zero_ne_one hN
        · have hne : ∃ i : Fin 8, zornCoord X.c i ≠ 0 := by
            by_contra hall
            push Not at hall
            exact hc ((zornCoord_eq_zero_iff X.c).mp hall)
          obtain ⟨i, hi⟩ := hne
          have hj : ∃ j : Fin 8, dualIdx j = i := by
            fin_cases i
            · exact ⟨7, rfl⟩
            · exact ⟨4, rfl⟩
            · exact ⟨5, rfl⟩
            · exact ⟨6, rfl⟩
            · exact ⟨1, rfl⟩
            · exact ⟨2, rfl⟩
            · exact ⟨3, rfl⟩
            · exact ⟨0, rfl⟩
          obtain ⟨j, rfl⟩ := hj
          refine ⟨e6RootExp (slot2Neg j) 1, e6RootExp_mem_chevalley _ _, ?_⟩
          rw [slot2Neg_alpha1, h1z, zero_add, one_mul]
          exact mul_ne_zero (dualSign_ne_zero j) hi
      · have hne : ∃ i : Fin 8, zornCoord X.a i ≠ 0 := by
          by_contra hall
          push Not at hall
          exact ha ((zornCoord_eq_zero_iff X.a).mp hall)
        obtain ⟨i, hi⟩ := hne
        have hj : ∃ j : Fin 8, dualIdx j = i := by
          fin_cases i
          · exact ⟨7, rfl⟩
          · exact ⟨4, rfl⟩
          · exact ⟨5, rfl⟩
          · exact ⟨6, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨2, rfl⟩
          · exact ⟨3, rfl⟩
          · exact ⟨0, rfl⟩
        obtain ⟨j, rfl⟩ := hj
        refine ⟨e6RootExp (slot0Pos j) 1, e6RootExp_mem_chevalley _ _, ?_⟩
        rw [slot0Pos_alpha1, h1z, zero_add, one_mul]
        exact mul_ne_zero (dualSign_ne_zero j) hi
  obtain ⟨g₁, hg₁, hX1_α₁⟩ := hStep1
  obtain ⟨X₁, hX₁⟩ : ∃ X₁, g₁.1 X = X₁ := ⟨_, rfl⟩
  rw [hX₁] at hX1_α₁
  -- Step 2: Clear a = 0 and c = 0
  obtain ⟨g_a, hga, hga_α₁, hga_a⟩ := clear_a_of_alpha1_ne_zero X₁ hX1_α₁
  obtain ⟨X₂, hX₂⟩ : ∃ X₂, g_a.1 X₁ = X₂ := ⟨_, rfl⟩
  rw [hX₂] at hga_α₁ hga_a
  have hX2_α₁ : X₂.α₁ ≠ 0 := hga_α₁ ▸ hX1_α₁
  obtain ⟨g_c, hgc, hgc_α₁, hgc_a, hgc_c⟩ := clear_c_of_alpha1_ne_zero_a_zero X₂ hX2_α₁ hga_a
  obtain ⟨X₃, hX₃⟩ : ∃ X₃, g_c.1 X₂ = X₃ := ⟨_, rfl⟩
  rw [hX₃] at hgc_α₁ hgc_a hgc_c
  have hX3_N : normCubic X₃ = 1 := by
    rw [← hX₃, ← hX₂, ← hX₁, ← hmul, ← hmul]
    exact (g_c * g_a * g₁).2 X ▸ hN
  -- Step 3: Make α₂ ≠ 0 while preserving a = 0, c = 0
  have hStep3 : ∃ g₂ ∈ e6ChevalleySubgroup,
      (g₂.1 X₃).α₂ ≠ 0 ∧ (g₂.1 X₃).a = 0 ∧ (g₂.1 X₃).c = 0 := by
    by_cases h2 : X₃.α₂ ≠ 0
    · exact ⟨1, e6ChevalleySubgroup.one_mem, h2, hgc_a, hgc_c⟩
    · have h2z : X₃.α₂ = 0 := not_not.mp h2
      have hbn : X₃.b ≠ 0 := by
        intro hbz
        rw [normCubic_of_a_zero_c_zero X₃ hgc_a hgc_c, h2z, zero_mul, hbz,
          show ZornVectorMatrix.norm (0 : ZornVectorMatrix ℝ) = 0 by
            simp [ZornVectorMatrix.norm, ZornVec3.dot, ZornVectorMatrix.zero],
          sub_self, mul_zero] at hX3_N
        exact zero_ne_one hX3_N
      have hne : ∃ i : Fin 8, zornCoord X₃.b i ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hbn ((zornCoord_eq_zero_iff X₃.b).mp hall)
      obtain ⟨i, hi⟩ := hne
      have hj : ∃ j : Fin 8, dualIdx j = i := by
        fin_cases i
        · exact ⟨7, rfl⟩
        · exact ⟨4, rfl⟩
        · exact ⟨5, rfl⟩
        · exact ⟨6, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩
        · exact ⟨0, rfl⟩
      obtain ⟨j, rfl⟩ := hj
      obtain ⟨_, sa, sc, s2⟩ := slot1Pos_action_of_ac_zero j 1 hgc_a hgc_c
      refine ⟨e6RootExp (slot1Pos j) 1, e6RootExp_mem_chevalley _ _, ?_, sa, sc⟩
      rw [s2, h2z, zero_add, one_mul]
      exact mul_ne_zero (dualSign_ne_zero j) hi
  obtain ⟨g₂, hg₂, hX4_α₂, hX4_a, hX4_c⟩ := hStep3
  obtain ⟨X₄, hX₄⟩ : ∃ X₄, g₂.1 X₃ = X₄ := ⟨_, rfl⟩
  rw [hX₄] at hX4_α₂ hX4_a hX4_c
  -- Step 4: Clear b = 0
  obtain ⟨g_b, hgb, _, hgb_α₂, hgb_a, hgb_b, hgb_c⟩ :=
    clear_b_of_alpha2_ne_zero_ac_zero X₄ hX4_α₂ hX4_a hX4_c
  obtain ⟨X₅, hX₅⟩ : ∃ X₅, g_b.1 X₄ = X₅ := ⟨_, rfl⟩
  rw [hX₅] at hgb_α₂ hgb_a hgb_b hgb_c
  have hg_pre_mem : g_b * g₂ * g_c * g_a * g₁ ∈ e6ChevalleySubgroup :=
    e6ChevalleySubgroup.mul_mem
      (e6ChevalleySubgroup.mul_mem
        (e6ChevalleySubgroup.mul_mem (e6ChevalleySubgroup.mul_mem hgb hg₂) hgc) hga) hg₁
  have hg_pre_eq : (g_b * g₂ * g_c * g_a * g₁).1 X = X₅ := by
    rw [hmul, hmul, hmul, hmul, hX₁, hX₂, hX₃, hX₄, hX₅]
  have hX5_N : normCubic X₅ = 1 := by
    rw [← hg_pre_eq]
    exact (g_b * g₂ * g_c * g_a * g₁).2 X ▸ hN
  have hprod : X₅.α₁ * X₅.α₂ * X₅.α₃ = 1 := by
    rw [normCubic_of_a_zero_c_zero X₅ hgb_a hgb_c, hgb_b,
      show ZornVectorMatrix.norm (0 : ZornVectorMatrix ℝ) = 0 by
        simp [ZornVectorMatrix.norm, ZornVec3.dot, ZornVectorMatrix.zero],
      sub_zero] at hX5_N
    linarith [hX5_N]
  have hα₁_ne : X₅.α₁ ≠ 0 := fun h0 => by rw [h0, zero_mul, zero_mul] at hprod; exact zero_ne_one hprod
  have hα₂_ne : X₅.α₂ ≠ 0 := fun h0 => by rw [h0, mul_zero, zero_mul] at hprod; exact zero_ne_one hprod
  have hα₃_ne : X₅.α₃ ≠ 0 := fun h0 => by rw [h0, mul_zero] at hprod; exact zero_ne_one hprod
  -- Step 5: Scale diagonal (α₁, α₂, α₃) to (1, 1, 1) via e6TorusElt 0 u * e6TorusElt 2 v
  let u : ℝˣ := Units.mk0 X₅.α₃ hα₃_ne
  let v : ℝˣ := (Units.mk0 X₅.α₂ hα₂_ne)⁻¹
  let t := e6TorusElt 0 u * e6TorusElt 2 v
  have ht_mem : t ∈ e6ChevalleySubgroup :=
    e6ChevalleySubgroup.mul_mem (e6TorusElt_mem_chevalley 0 u) (e6TorusElt_mem_chevalley 2 v)
  refine ⟨t * (g_b * g₂ * g_c * g_a * g₁), e6ChevalleySubgroup.mul_mem ht_mem hg_pre_mem, ?_⟩
  rw [hmul, hg_pre_eq]
  apply h3Zorn_ext_coord
  intro m
  dsimp only [t]
  rw [hmul, h3ZornCoordinate_e6TorusElt, h3ZornCoordinate_e6TorusElt]
  have hw0 : h3zornWeight 0 0 = 1 ∧ h3zornWeight 0 2 = -1 := ⟨rfl, rfl⟩
  have hw1 : h3zornWeight 1 0 = 0 ∧ h3zornWeight 1 2 = 1 := ⟨rfl, rfl⟩
  have hw2 : h3zornWeight 2 0 = -1 ∧ h3zornWeight 2 2 = 0 := ⟨rfl, rfl⟩
  have hX5_rest : ∀ m : Fin 27, 3 ≤ m.val → h3ZornCoordinate X₅ m = 0 := by
    intro m hm
    by_cases hm11 : m.val < 11
    · have hne : m = ⟨3 + (⟨m.val - 3, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hne, h3ZornCoord_a_eq, hgb_a]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
    · by_cases hm19 : m.val < 19
      · have hne : m = ⟨11 + (⟨m.val - 11, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hne, h3ZornCoord_b_eq, hgb_b]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
      · have hne : m = ⟨19 + (⟨m.val - 19, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hne, h3ZornCoord_c_eq, hgb_c]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
  have hm012 : m = 0 ∨ m = 1 ∨ m = 2 ∨ 3 ≤ m.val := by omega
  rcases hm012 with rfl | rfl | rfl | hm3
  · change (u : ℝ) ^ (h3zornWeight 0 0) * ((v : ℝ) ^ (h3zornWeight 0 2) * X₅.α₁) = 1
    rw [hw0.1, hw0.2, zpow_one, zpow_neg_one]
    have hu : (u : ℝ) = X₅.α₃ := rfl
    have hv : (v : ℝ) = (X₅.α₂)⁻¹ := Units.val_inv_eq_inv_val _
    have hre : X₅.α₃ * (X₅.α₂ * X₅.α₁) = X₅.α₁ * X₅.α₂ * X₅.α₃ := by ring
    rw [hu, hv, inv_inv, hre, hprod]
  · change (u : ℝ) ^ (h3zornWeight 1 0) * ((v : ℝ) ^ (h3zornWeight 1 2) * X₅.α₂) = 1
    rw [hw1.1, hw1.2, zpow_zero, zpow_one, one_mul]
    have hv : (v : ℝ) = (X₅.α₂)⁻¹ := Units.val_inv_eq_inv_val _
    rw [hv, inv_mul_cancel₀ hα₂_ne]
  · change (u : ℝ) ^ (h3zornWeight 2 0) * ((v : ℝ) ^ (h3zornWeight 2 2) * X₅.α₃) = 1
    rw [hw2.1, hw2.2, zpow_neg_one, zpow_zero, one_mul]
    have hu : (u : ℝ) = X₅.α₃ := rfl
    rw [hu, inv_mul_cancel₀ hα₃_ne]
  · rw [hX5_rest m hm3, mul_zero, mul_zero]
    have hm1_rest : ∀ m' : Fin 27, 3 ≤ m'.val → h3ZornCoordinate (1 : H3Zorn ℝ) m' = 0 := by
      intro m' hm'
      fin_cases m' <;> first | exact absurd hm' (by decide) | rfl
    exact (hm1_rest m hm3).symm

/-- **Part A (Transitivity on `{X : H3Zorn ℝ | normCubic X = 1}`)**: for any `X` with
`normCubic X = 1`, there exists `h ∈ e6ChevalleySubgroup` with `h.1 1 = X`. -/
theorem e6ChevalleySubgroup_transitive_normCubic_one (X : H3Zorn ℝ) (hN : normCubic X = 1) :
    ∃ h ∈ e6ChevalleySubgroup, h.1 1 = X := by
  obtain ⟨h, hh, h1⟩ := e6ChevalleySubgroup_move_normCubic_one_to_one X hN
  refine ⟨h⁻¹, e6ChevalleySubgroup.inv_mem hh, ?_⟩
  change h.1.symm 1 = X
  exact h.1.symm_apply_eq.mpr h1.symm

/-- Every `g ∈ Str₀(H₃(𝕆_s))` factors as `g = h * f` with `h ∈ e6ChevalleySubgroup` and
`f ∈ h3zornReducedStructureFixOne`. -/
theorem e6ChevalleySubgroup_reduce_to_fixOne (g : h3zornReducedStructureGroup) :
    ∃ h ∈ e6ChevalleySubgroup, ∃ f ∈ h3zornReducedStructureFixOne, g = h * f := by
  have hN : normCubic (g.1 1) = 1 := by simpa [normCubic_one] using g.2 1
  obtain ⟨h, hh, hh1⟩ := e6ChevalleySubgroup_transitive_normCubic_one (g.1 1) hN
  refine ⟨h, hh, h⁻¹ * g, ?_, by simp⟩
  change (h⁻¹ * g).1 1 = 1
  change h.1.symm (g.1 1) = 1
  rw [← hh1, h.1.symm_apply_apply]

end PartATransitivity

section PartBF4AndFullGeneration

/-- Subgroup `F₄(4) = Str₀(H₃(𝕆_s))₁ ∩ E₆(6)` fixing `1 : H3Zorn ℝ`. -/
def e6F4InChevalley : Subgroup h3zornReducedStructureGroup :=
  e6ChevalleySubgroup ⊓ h3zornReducedStructureFixOne

/-- Rank-1 primitive idempotent predicate on `H3Zorn ℝ`. -/
def isRankOneIdem (e : H3Zorn ℝ) : Prop :=
  e * e = e ∧ linearTrace e = 1 ∧ adjointQuad e = 0

private theorem h3_diag₁_isRankOneIdem : isRankOneIdem h3_diag₁ := by
  refine ⟨h3_diag₁_mul_h3_diag₁, ?_, ?_⟩
  · simp [h3_diag₁, linearTrace]
  · ext i <;> simp [h3_diag₁, adjointQuad, ZornVectorMatrix.norm, ZornVec3.dot,
      ZornVectorMatrix.zero, ZornVectorMatrix.sub, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
      ZornVectorMatrix.smul, ZornVectorMatrix.add, ZornVectorMatrix.neg]

private theorem h3_diag₂_isRankOneIdem : isRankOneIdem h3_diag₂ := by
  refine ⟨h3_diag₂_mul_h3_diag₂, ?_, ?_⟩
  · simp [h3_diag₂, linearTrace]
  · ext i <;> simp [h3_diag₂, adjointQuad, ZornVectorMatrix.norm, ZornVec3.dot,
      ZornVectorMatrix.zero, ZornVectorMatrix.sub, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
      ZornVectorMatrix.smul, ZornVectorMatrix.add, ZornVectorMatrix.neg]

private theorem jordanAut_preserves_linearTrace (A : H3ZornJordanAut) (X : H3Zorn ℝ) :
    linearTrace (A X) = linearTrace X := by
  have hN : ∀ y : H3Zorn ℝ, normCubic (A.1 y) = normCubic y :=
    H3ZornJordanAut.mem_reducedStructureGroup A
  have h1 : A.1 (1 : H3Zorn ℝ) = 1 := A.map_one
  have hpos : normCubic ((1 : H3Zorn ℝ) + (1 : ℝ) • A X) =
      normCubic ((1 : H3Zorn ℝ) + (1 : ℝ) • X) := by
    have ha : (1 : H3Zorn ℝ) + (1 : ℝ) • A X = A.1 ((1 : H3Zorn ℝ) + (1 : ℝ) • X) := by
      rw [map_add, map_smul, h1]
    rw [ha, hN]
  have hneg : normCubic ((1 : H3Zorn ℝ) + (-1 : ℝ) • A X) =
      normCubic ((1 : H3Zorn ℝ) + (-1 : ℝ) • X) := by
    have ha : (1 : H3Zorn ℝ) + (-1 : ℝ) • A X = A.1 ((1 : H3Zorn ℝ) + (-1 : ℝ) • X) := by
      rw [map_add, map_smul, h1]
    rw [ha, hN]
  rw [normCubic_line, normCubic_line, adjointQuad_one, traceBilin_symm 1 (A X),
    traceBilin_symm 1 X] at hpos hneg
  simp only [traceBilin_one] at hpos hneg
  have hNX : normCubic (A X) = normCubic X := hN X
  rw [hNX] at hpos hneg
  linarith [hpos, hneg]

private theorem jordanAut_preserves_isRankOneIdem (A : H3ZornJordanAut) {e : H3Zorn ℝ}
    (he : isRankOneIdem e) : isRankOneIdem (A e) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← A.map_mul, he.1]
  · rw [jordanAut_preserves_linearTrace A e, he.2.1]
  · have hN : ∀ y : H3Zorn ℝ, normCubic (A.1 y) = (1 : ℝˣ) * normCubic y := fun y => by
      rw [Units.val_one, one_mul]
      exact H3ZornJordanAut.mem_reducedStructureGroup A y
    have hadj := h3zorn_adjointQuad_similitude_intertwines A.1 1 hN e
    change adjointQuad (A.1 e) = _ at hadj
    rw [he.2.2, map_zero, smul_zero] at hadj
    exact hadj

private theorem f4InChevalley_preserves_isRankOneIdem {g : h3zornReducedStructureGroup}
    (hg : g ∈ e6F4InChevalley) {e : H3Zorn ℝ} (he : isRankOneIdem e) :
    isRankOneIdem (g.1 e) :=
  jordanAut_preserves_isRankOneIdem (h3zornJordanAutOfReducedStructure g hg.2) he

private theorem isRankOneIdem_norm_eq {e : H3Zorn ℝ} (he : isRankOneIdem e) :
    e.α₁ + e.α₂ + e.α₃ = 1 ∧
    e.α₂ * e.α₃ = ZornVectorMatrix.norm e.b ∧
    e.α₁ * e.α₃ = ZornVectorMatrix.norm e.c ∧
    e.α₁ * e.α₂ = ZornVectorMatrix.norm e.a := by
  refine ⟨he.2.1, ?_, ?_, ?_⟩
  · have h1 := congrArg H3Zorn.α₁ he.2.2
    change e.α₂ * e.α₃ - ZornVectorMatrix.norm e.b = 0 at h1
    linarith [h1]
  · have h2 := congrArg H3Zorn.α₂ he.2.2
    change e.α₁ * e.α₃ - ZornVectorMatrix.norm e.c = 0 at h2
    linarith [h2]
  · have h3 := congrArg H3Zorn.α₃ he.2.2
    change e.α₁ * e.α₂ - ZornVectorMatrix.norm e.a = 0 at h3
    linarith [h3]

/-- `D₄` root subgroup inside `F₄(4)` generated by roots `r < 24`. -/
def d4Subgroup : Subgroup h3zornReducedStructureGroup :=
  Subgroup.closure {g | ∃ (r : Fin 72), r.val < 24 ∧ ∃ t : ℝ, g = e6RootExp r t}

private theorem d4_sparse_blocks_check :
    (List.finRange 24).all (fun r =>
      (List.finRange 27).all (fun m =>
        (if m.val < 3 then
          (List.finRange 27).all (fun k => sparseVal (e6RootSparse ⟨r.val, by omega⟩) m k == 0)
         else true) &&
        (if 3 ≤ m.val ∧ m.val < 11 then
          (List.finRange 27).all (fun k =>
            if k.val < 3 ∨ 11 ≤ k.val then
              sparseVal (e6RootSparse ⟨r.val, by omega⟩) m k == 0
            else true)
         else true) &&
        (if 11 ≤ m.val ∧ m.val < 19 then
          (List.finRange 27).all (fun k =>
            if k.val < 11 ∨ 19 ≤ k.val then
              sparseVal (e6RootSparse ⟨r.val, by omega⟩) m k == 0
            else true)
         else true) &&
        (if 19 ≤ m.val then
          (List.finRange 27).all (fun k =>
            if k.val < 19 then
              sparseVal (e6RootSparse ⟨r.val, by omega⟩) m k == 0
            else true)
         else true))) = true := by
  decide

private theorem d4_rootExp_preserves_blocks {r : Fin 72} (hr : r.val < 24) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp r t).1 X).α₁ = X.α₁ ∧
    ((e6RootExp r t).1 X).α₂ = X.α₂ ∧
    ((e6RootExp r t).1 X).α₃ = X.α₃ ∧
    (X.a = 0 → ((e6RootExp r t).1 X).a = 0) ∧
    (X.b = 0 → ((e6RootExp r t).1 X).b = 0) ∧
    (X.c = 0 → ((e6RootExp r t).1 X).c = 0) := by
  have hc := d4_sparse_blocks_check
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true] at hc
  have hcr := hc ⟨r.val, hr⟩
  have hdiag : ∀ m : Fin 27, m.val < 3 →
      h3ZornCoordinate ((e6RootExp r t).1 X) m = h3ZornCoordinate X m := fun m hm => by
    have hm' := (hcr m).1.1.1
    rw [ite_eq_left_of_eq_true _ _ (eq_true hm), List.all_eq_true] at hm'
    exact rootExp_coord_unchanged r m t X fun k =>
      beq_iff_eq.mp (hm' k (List.mem_finRange k))
  refine ⟨hdiag 0 (by decide), hdiag 1 (by decide), hdiag 2 (by decide), ?_, ?_, ?_⟩
  · intro ha
    refine zorn_eq_of_zornCoord_eq fun j => ?_
    rw [← h3ZornCoord_a_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_a_eq, ha,
      (zornCoord_eq_zero_iff 0).mpr rfl j, zero_add]
    have hm' := (hcr ⟨3 + j.val, by omega⟩).1.1.2
    have hcond : 3 ≤ (⟨3 + j.val, by omega⟩ : Fin 27).val ∧
        (⟨3 + j.val, by omega⟩ : Fin 27).val < 11 := by dsimp; omega
    simp only [hcond, and_self, ↓reduceIte, List.all_eq_true] at hm'
    have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse r) ⟨3 + j.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate X k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k.val < 3 ∨ 11 ≤ k.val
      · have hkz := hm' k (List.mem_finRange k)
        simp only [hk, ↓reduceIte, beq_iff_eq] at hkz
        change (sparseVal (e6RootSparse r) ⟨3 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k = 0
        rw [hkz, Int.cast_zero, zero_mul]
      · have hne : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hne, h3ZornCoord_a_eq, ha, (zornCoord_eq_zero_iff 0).mpr rfl _, mul_zero]
    rw [hs, mul_zero]
  · intro hb
    refine zorn_eq_of_zornCoord_eq fun j => ?_
    rw [← h3ZornCoord_b_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_b_eq, hb,
      (zornCoord_eq_zero_iff 0).mpr rfl j, zero_add]
    have hm' := (hcr ⟨11 + j.val, by omega⟩).1.2
    have hcond : 11 ≤ (⟨11 + j.val, by omega⟩ : Fin 27).val ∧
        (⟨11 + j.val, by omega⟩ : Fin 27).val < 19 := by dsimp; omega
    simp only [hcond, and_self, ↓reduceIte, List.all_eq_true] at hm'
    have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse r) ⟨11 + j.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate X k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k.val < 11 ∨ 19 ≤ k.val
      · have hkz := hm' k (List.mem_finRange k)
        simp only [hk, ↓reduceIte, beq_iff_eq] at hkz
        change (sparseVal (e6RootSparse r) ⟨11 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k = 0
        rw [hkz, Int.cast_zero, zero_mul]
      · have hne : k = ⟨11 + (⟨k.val - 11, by omega⟩ : Fin 8).val, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hne, h3ZornCoord_b_eq, hb, (zornCoord_eq_zero_iff 0).mpr rfl _, mul_zero]
    rw [hs, mul_zero]
  · intro hc0
    refine zorn_eq_of_zornCoord_eq fun j => ?_
    rw [← h3ZornCoord_c_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_c_eq, hc0,
      (zornCoord_eq_zero_iff 0).mpr rfl j, zero_add]
    have hm' := (hcr ⟨19 + j.val, by omega⟩).2
    have hcond : 19 ≤ (⟨19 + j.val, by omega⟩ : Fin 27).val := by dsimp; omega
    simp only [hcond, ↓reduceIte, List.all_eq_true] at hm'
    have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse r) ⟨19 + j.val, by omega⟩ k : ℝ) *
        h3ZornCoordinate X k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k.val < 19
      · have hkz := hm' k (List.mem_finRange k)
        simp only [hk, ↓reduceIte, beq_iff_eq] at hkz
        change (sparseVal (e6RootSparse r) ⟨19 + j.val, by omega⟩ k : ℝ) * h3ZornCoordinate X k = 0
        rw [hkz, Int.cast_zero, zero_mul]
      · have hne : k = ⟨19 + (⟨k.val - 19, by omega⟩ : Fin 8).val, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hne, h3ZornCoord_c_eq, hc0, (zornCoord_eq_zero_iff 0).mpr rfl _, mul_zero]
    rw [hs, mul_zero]

private theorem d4_rootExp_preserves_blocks_iff {r : Fin 72} (hr : r.val < 24) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp r t).1 X).α₁ = X.α₁ ∧
    ((e6RootExp r t).1 X).α₂ = X.α₂ ∧
    ((e6RootExp r t).1 X).α₃ = X.α₃ ∧
    (((e6RootExp r t).1 X).a = 0 ↔ X.a = 0) ∧
    (((e6RootExp r t).1 X).b = 0 ↔ X.b = 0) ∧
    (((e6RootExp r t).1 X).c = 0 ↔ X.c = 0) := by
  obtain ⟨h1, h2, h3, ha, hb, hc⟩ := d4_rootExp_preserves_blocks hr t X
  obtain ⟨_, _, _, ha', hb', hc'⟩ := d4_rootExp_preserves_blocks hr (-t) ((e6RootExp r t).1 X)
  have hinv : (e6RootExp r (-t)).1 ((e6RootExp r t).1 X) = X := by
    change ((e6RootExp r (-t) * e6RootExp r t).1 X) = X
    rw [← e6RootExp_add, neg_add_cancel, e6RootExp_zero]; rfl
  rw [hinv] at ha' hb' hc'
  exact ⟨h1, h2, h3, ⟨ha', ha⟩, ⟨hb', hb⟩, ⟨hc', hc⟩⟩

private theorem d4Subgroup_preserves_blocks {g : h3zornReducedStructureGroup} (hg : g ∈ d4Subgroup) :
    ∀ X : H3Zorn ℝ,
      (g.1 X).α₁ = X.α₁ ∧ (g.1 X).α₂ = X.α₂ ∧ (g.1 X).α₃ = X.α₃ ∧
      ((g.1 X).a = 0 ↔ X.a = 0) ∧ ((g.1 X).b = 0 ↔ X.b = 0) ∧ ((g.1 X).c = 0 ↔ X.c = 0) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨r, hr, t, rfl⟩
    exact d4_rootExp_preserves_blocks_iff hr t
  | one => intro X; exact ⟨rfl, rfl, rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩
  | mul x y _ _ ihx ihy =>
    intro X
    obtain ⟨x1, x2, x3, xa, xb, xc⟩ := ihx (y.1 X)
    obtain ⟨y1, y2, y3, ya, yb, yc⟩ := ihy X
    exact ⟨x1.trans y1, x2.trans y2, x3.trans y3, xa.trans ya, xb.trans yb, xc.trans yc⟩
  | inv x _ ihx =>
    intro X
    obtain ⟨x1, x2, x3, xa, xb, xc⟩ := ihx (x⁻¹.1 X)
    have hinv : x.1 (x⁻¹.1 X) = X := x.1.apply_symm_apply X
    rw [hinv] at x1 x2 x3 xa xb xc
    exact ⟨x1.symm, x2.symm, x3.symm, xa.symm, xb.symm, xc.symm⟩

private theorem d4Subgroup_fix_diags {g : h3zornReducedStructureGroup} (hg : g ∈ d4Subgroup) :
    g.1 h3_diag₁ = h3_diag₁ ∧ g.1 h3_diag₂ = h3_diag₂ ∧ g.1 h3_diag₃ = h3_diag₃ := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, ha, hb, hc⟩ := d4Subgroup_preserves_blocks hg h3_diag₁
    apply ext_h3 <;> [exact h1; exact h2; exact h3; exact ha.mpr rfl; exact hb.mpr rfl; exact hc.mpr rfl]
  · obtain ⟨h1, h2, h3, ha, hb, hc⟩ := d4Subgroup_preserves_blocks hg h3_diag₂
    apply ext_h3 <;> [exact h1; exact h2; exact h3; exact ha.mpr rfl; exact hb.mpr rfl; exact hc.mpr rfl]
  · obtain ⟨h1, h2, h3, ha, hb, hc⟩ := d4Subgroup_preserves_blocks hg h3_diag₃
    apply ext_h3 <;> [exact h1; exact h2; exact h3; exact ha.mpr rfl; exact hb.mpr rfl; exact hc.mpr rfl]

private theorem d4Subgroup_le_f4InChevalley : d4Subgroup ≤ e6F4InChevalley := by
  intro g hg
  refine ⟨?_, ?_⟩
  · induction hg using Subgroup.closure_induction with
    | mem x hx => rcases hx with ⟨r, _, t, rfl⟩; exact e6RootExp_mem_chevalley r t
    | one => exact e6ChevalleySubgroup.one_mem
    | mul _ _ _ _ ih1 ih2 => exact e6ChevalleySubgroup.mul_mem ih1 ih2
    | inv _ _ ih => exact e6ChevalleySubgroup.inv_mem ih
  · obtain ⟨h1, h2, h3⟩ := d4Subgroup_fix_diags hg
    change g.1 1 = 1
    rw [← h3Zorn_diag_sum_one, g.1.map_add, g.1.map_add, h1, h2, h3]

private def f4PosIdx (s : Fin 3) (j : Fin 8) : Fin 72 :=
  ⟨16 * s.val + 2 * j.val + 24, by omega⟩

private def f4NegIdx (s : Fin 3) (j : Fin 8) : Fin 72 :=
  ⟨16 * s.val + 2 * j.val + 25, by omega⟩

/-- Peirce-coupled `F₄(4)` root exponential `exp(t R_{rPos}) exp(-t R_{rNeg})` fixing `1`. -/
private def f4PeirceExp (s : Fin 3) (j : Fin 8) (t : ℝ) : h3zornReducedStructureGroup :=
  e6RootExp (f4PosIdx s j) t * e6RootExp (f4NegIdx s j) (-t)

private theorem f4Peirce_fix1_sum_eq (s : Fin 3) (j : Fin 8) (m : Fin 27) :
    sparseVal (e6RootSparse (f4PosIdx s j)) m 0 + sparseVal (e6RootSparse (f4PosIdx s j)) m 1 +
      sparseVal (e6RootSparse (f4PosIdx s j)) m 2 =
    sparseVal (e6RootSparse (f4NegIdx s j)) m 0 + sparseVal (e6RootSparse (f4NegIdx s j)) m 1 +
      sparseVal (e6RootSparse (f4NegIdx s j)) m 2 := by
  have h : (List.finRange 3).all (fun s => (List.finRange 8).all (fun j =>
      (List.finRange 27).all (fun m =>
        sparseVal (e6RootSparse (f4PosIdx s j)) m 0 + sparseVal (e6RootSparse (f4PosIdx s j)) m 1 +
          sparseVal (e6RootSparse (f4PosIdx s j)) m 2 ==
        sparseVal (e6RootSparse (f4NegIdx s j)) m 0 + sparseVal (e6RootSparse (f4NegIdx s j)) m 1 +
          sparseVal (e6RootSparse (f4NegIdx s j)) m 2))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h s j m

private theorem f4Peirce_fix1_mul_zero (s : Fin 3) (j : Fin 8) (m : Fin 27) :
    sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m 0 +
      sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m 1 +
      sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m 2 = 0 := by
  have h : (List.finRange 3).all (fun s => (List.finRange 8).all (fun j =>
      (List.finRange 27).all (fun m =>
        sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m 0 +
          sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m 1 +
          sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m 2 == 0))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h s j m

private theorem h3ZornCoordinate_one_rest (k : Fin 27) (hk : ¬(k.val < 3)) :
    h3ZornCoordinate (1 : H3Zorn ℝ) k = 0 := by
  fin_cases k <;> first | exact absurd (by decide : _ < 3) hk | rfl

private theorem f4PeirceExp_mem_f4 (s : Fin 3) (j : Fin 8) (t : ℝ) :
    f4PeirceExp s j t ∈ e6F4InChevalley := by
  refine ⟨e6ChevalleySubgroup.mul_mem (e6RootExp_mem_chevalley _ _) (e6RootExp_mem_chevalley _ _), ?_⟩
  change (f4PeirceExp s j t).1 1 = 1
  apply h3Zorn_ext_coord; intro m
  have hsum1 : ∀ (r : Fin 72) (a : Fin 27),
      (∑ k : Fin 27, (sparseVal (e6RootSparse r) a k : ℝ) * h3ZornCoordinate (1 : H3Zorn ℝ) k) =
        (sparseVal (e6RootSparse r) a 0 + sparseVal (e6RootSparse r) a 1 +
          sparseVal (e6RootSparse r) a 2 : ℝ) := fun r a => by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun k : Fin 27 => k.val < 3)]
    have hhz : ∑ k ∈ Finset.univ.filter (fun k : Fin 27 => ¬(k.val < 3)),
        (sparseVal (e6RootSparse r) a k : ℝ) * h3ZornCoordinate (1 : H3Zorn ℝ) k = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [h3ZornCoordinate_one_rest k (Finset.mem_filter.mp hk).2, mul_zero]
    rw [hhz, add_zero]
    have hflt : Finset.univ.filter (fun k : Fin 27 => k.val < 3) = {0, 1, 2} := by decide
    rw [hflt, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    have h0 : h3ZornCoordinate (1 : H3Zorn ℝ) 0 = 1 := rfl
    have h1 : h3ZornCoordinate (1 : H3Zorn ℝ) 1 = 1 := rfl
    have h2 : h3ZornCoordinate (1 : H3Zorn ℝ) 2 = 1 := rfl
    rw [h0, h1, h2]; ring
  have hstep1 : ∀ a : Fin 27,
      h3ZornCoordinate ((e6RootExp (f4NegIdx s j) (-t)).1 1) a =
        h3ZornCoordinate (1 : H3Zorn ℝ) a +
          (-t) * (sparseVal (e6RootSparse (f4NegIdx s j)) a 0 +
            sparseVal (e6RootSparse (f4NegIdx s j)) a 1 +
            sparseVal (e6RootSparse (f4NegIdx s j)) a 2 : ℝ) := fun a => by
    rw [h3ZornCoordinate_e6RootExp, hsum1]
  change h3ZornCoordinate ((e6RootExp (f4PosIdx s j) t).1
      ((e6RootExp (f4NegIdx s j) (-t)).1 1)) m = _
  rw [h3ZornCoordinate_e6RootExp, hstep1 m]
  have hexp : ∑ a : Fin 27, (sparseVal (e6RootSparse (f4PosIdx s j)) m a : ℝ) *
      h3ZornCoordinate ((e6RootExp (f4NegIdx s j) (-t)).1 1) a =
      (∑ a : Fin 27, (sparseVal (e6RootSparse (f4PosIdx s j)) m a : ℝ) *
        h3ZornCoordinate (1 : H3Zorn ℝ) a) +
      ∑ a : Fin 27, (sparseVal (e6RootSparse (f4PosIdx s j)) m a : ℝ) *
        ((-t) * (sparseVal (e6RootSparse (f4NegIdx s j)) a 0 +
          sparseVal (e6RootSparse (f4NegIdx s j)) a 1 +
          sparseVal (e6RootSparse (f4NegIdx s j)) a 2 : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hstep1 a, mul_add]
  rw [hexp, hsum1]
  have hmul : ∑ a : Fin 27, (sparseVal (e6RootSparse (f4PosIdx s j)) m a : ℝ) *
      ((-t) * (sparseVal (e6RootSparse (f4NegIdx s j)) a 0 +
        sparseVal (e6RootSparse (f4NegIdx s j)) a 1 +
        sparseVal (e6RootSparse (f4NegIdx s j)) a 2 : ℝ)) = 0 := by
    have hs : ∑ a : Fin 27, (sparseVal (e6RootSparse (f4PosIdx s j)) m a : ℝ) *
        (sparseVal (e6RootSparse (f4NegIdx s j)) a 0 +
          sparseVal (e6RootSparse (f4NegIdx s j)) a 1 +
          sparseVal (e6RootSparse (f4NegIdx s j)) a 2 : ℝ) =
        ((sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m 0 +
          sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m 1 +
          sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m 2 : ℤ) :
            ℝ) := by
      simp only [sparseVal_mul, Int.cast_sum, Int.cast_add, Int.cast_mul]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => by ring
    simp_rw [mul_left_comm _ (-t), ← Finset.mul_sum, hs]
    have h0 : sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m 0 +
        sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m 1 +
        sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m 2 = 0 :=
      f4Peirce_fix1_mul_zero s j m
    rw [h0, Int.cast_zero, mul_zero]
  rw [hmul, add_zero]
  have heqR : (sparseVal (e6RootSparse (f4PosIdx s j)) m 0 +
      sparseVal (e6RootSparse (f4PosIdx s j)) m 1 +
      sparseVal (e6RootSparse (f4PosIdx s j)) m 2 : ℝ) =
      (sparseVal (e6RootSparse (f4NegIdx s j)) m 0 +
        sparseVal (e6RootSparse (f4NegIdx s j)) m 1 +
        sparseVal (e6RootSparse (f4NegIdx s j)) m 2 : ℝ) := by
    exact_mod_cast f4Peirce_fix1_sum_eq s j m
  rw [heqR]; ring

private def w12 : h3zornReducedStructureGroup :=
  f4PeirceExp 0 0 1 * f4PeirceExp 0 7 1 * f4PeirceExp 0 0 1

private def w23 : h3zornReducedStructureGroup :=
  f4PeirceExp 1 0 1 * f4PeirceExp 1 7 1 * f4PeirceExp 1 0 1

private def w31 : h3zornReducedStructureGroup :=
  f4PeirceExp 2 0 1 * f4PeirceExp 2 7 1 * f4PeirceExp 2 0 1

private theorem w12_mem_f4 : w12 ∈ e6F4InChevalley :=
  e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 0 0 1) (f4PeirceExp_mem_f4 0 7 1))
    (f4PeirceExp_mem_f4 0 0 1)

private theorem w23_mem_f4 : w23 ∈ e6F4InChevalley :=
  e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 1 0 1) (f4PeirceExp_mem_f4 1 7 1))
    (f4PeirceExp_mem_f4 1 0 1)

private theorem w31_mem_f4 : w31 ∈ e6F4InChevalley :=
  e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 2 0 1) (f4PeirceExp_mem_f4 2 7 1))
    (f4PeirceExp_mem_f4 2 0 1)

private def w12Sparse : SparseMat27 :=
  [(0, 1, 1), (1, 0, 1), (2, 2, 1), (3, 10, -1), (4, 4, 1), (5, 5, 1), (6, 6, 1),
   (7, 7, 1), (8, 8, 1), (9, 9, 1), (10, 3, -1), (11, 26, -1), (12, 20, 1), (13, 21, 1),
   (14, 22, 1), (15, 23, 1), (16, 24, 1), (17, 25, 1), (18, 19, -1), (19, 18, 1),
   (20, 12, -1), (21, 13, -1), (22, 14, -1), (23, 15, -1), (24, 16, -1), (25, 17, -1), (26, 11, 1)]

private def w23Sparse : SparseMat27 :=
  [(0, 0, 1), (1, 2, 1), (2, 1, 1), (3, 26, 1), (4, 20, -1), (5, 21, -1), (6, 22, -1),
   (7, 23, -1), (8, 24, -1), (9, 25, -1), (10, 19, 1), (11, 18, -1), (12, 12, 1), (13, 13, 1),
   (14, 14, 1), (15, 15, 1), (16, 16, 1), (17, 17, 1), (18, 11, -1), (19, 10, -1), (20, 4, 1),
   (21, 5, 1), (22, 6, 1), (23, 7, 1), (24, 8, 1), (25, 9, 1), (26, 3, -1)]

private def w31Sparse : SparseMat27 :=
  [(0, 2, 1), (1, 1, 1), (2, 0, 1), (3, 18, -1), (4, 12, 1), (5, 13, 1), (6, 14, 1),
   (7, 15, 1), (8, 16, 1), (9, 17, 1), (10, 11, -1), (11, 10, 1), (12, 4, -1), (13, 5, -1),
   (14, 6, -1), (15, 7, -1), (16, 8, -1), (17, 9, -1), (18, 3, 1), (19, 26, -1), (20, 20, 1),
   (21, 21, 1), (22, 22, 1), (23, 23, 1), (24, 24, 1), (25, 25, 1), (26, 19, -1)]

private def w12P0Sparse : SparseMat27 :=
  [(0, 10, 1), (1, 10, -1), (3, 0, -1), (3, 1, 1), (3, 10, -1), (15, 23, 1), (16, 24, 1),
   (17, 25, 1), (18, 19, -1), (20, 12, -1), (21, 13, -1), (22, 14, -1), (26, 11, 1)]

private def w12P7Sparse : SparseMat27 :=
  [(0, 3, 1), (1, 3, -1), (10, 0, -1), (10, 1, 1), (10, 3, -1), (11, 26, -1), (12, 20, 1),
   (13, 21, 1), (14, 22, 1), (19, 18, 1), (23, 15, -1), (24, 16, -1), (25, 17, -1)]

private def w23P0Sparse : SparseMat27 :=
  [(1, 18, 1), (2, 18, -1), (4, 20, -1), (5, 21, -1), (6, 22, -1), (10, 19, 1), (11, 1, -1),
   (11, 2, 1), (11, 18, -1), (23, 7, 1), (24, 8, 1), (25, 9, 1), (26, 3, -1)]

private def w23P7Sparse : SparseMat27 :=
  [(1, 11, 1), (2, 11, -1), (3, 26, 1), (7, 23, -1), (8, 24, -1), (9, 25, -1), (18, 1, -1),
   (18, 2, 1), (18, 11, -1), (19, 10, -1), (20, 4, 1), (21, 5, 1), (22, 6, 1)]

private def w31P0Sparse : SparseMat27 :=
  [(0, 26, -1), (2, 26, 1), (7, 15, 1), (8, 16, 1), (9, 17, 1), (10, 11, -1), (12, 4, -1),
   (13, 5, -1), (14, 6, -1), (18, 3, 1), (19, 0, 1), (19, 2, -1), (19, 26, -1)]

private def w31P7Sparse : SparseMat27 :=
  [(0, 19, -1), (2, 19, 1), (3, 18, -1), (4, 12, 1), (5, 13, 1), (6, 14, 1), (11, 10, 1),
   (15, 7, -1), (16, 8, -1), (17, 9, -1), (26, 0, 1), (26, 2, -1), (26, 19, -1)]

private def w12HalfSparse : SparseMat27 :=
  [(0, 1, 1), (0, 10, 1), (1, 0, 1), (1, 10, -1), (2, 2, 1), (3, 10, -1), (4, 4, 1),
   (5, 5, 1), (6, 6, 1), (7, 7, 1), (8, 8, 1), (9, 9, 1), (10, 0, -1), (10, 1, 1),
   (10, 3, -1), (10, 10, 1), (11, 11, 1), (11, 26, -1), (12, 12, 1), (12, 20, 1),
   (13, 13, 1), (13, 21, 1), (14, 14, 1), (14, 22, 1), (15, 23, 1), (16, 24, 1),
   (17, 25, 1), (18, 19, -1), (19, 18, 1), (19, 19, 1), (20, 12, -1), (21, 13, -1),
   (22, 14, -1), (23, 15, -1), (23, 23, 1), (24, 16, -1), (24, 24, 1), (25, 17, -1),
   (25, 25, 1), (26, 11, 1)]

private def w23HalfSparse : SparseMat27 :=
  [(0, 0, 1), (1, 2, 1), (1, 18, 1), (2, 1, 1), (2, 18, -1), (3, 3, 1), (3, 26, 1),
   (4, 20, -1), (5, 21, -1), (6, 22, -1), (7, 7, 1), (7, 23, -1), (8, 8, 1), (8, 24, -1),
   (9, 9, 1), (9, 25, -1), (10, 19, 1), (11, 18, -1), (12, 12, 1), (13, 13, 1), (14, 14, 1),
   (15, 15, 1), (16, 16, 1), (17, 17, 1), (18, 1, -1), (18, 2, 1), (18, 11, -1), (18, 18, 1),
   (19, 10, -1), (19, 19, 1), (20, 4, 1), (20, 20, 1), (21, 5, 1), (21, 21, 1), (22, 6, 1),
   (22, 22, 1), (23, 7, 1), (24, 8, 1), (25, 9, 1), (26, 3, -1)]

private def w31HalfSparse : SparseMat27 :=
  [(0, 2, 1), (0, 26, -1), (1, 1, 1), (2, 0, 1), (2, 26, 1), (3, 3, 1), (3, 18, -1),
   (4, 4, 1), (4, 12, 1), (5, 5, 1), (5, 13, 1), (6, 6, 1), (6, 14, 1), (7, 15, 1),
   (8, 16, 1), (9, 17, 1), (10, 11, -1), (11, 10, 1), (11, 11, 1), (12, 4, -1), (13, 5, -1),
   (14, 6, -1), (15, 7, -1), (15, 15, 1), (16, 8, -1), (16, 16, 1), (17, 9, -1), (17, 17, 1),
   (18, 3, 1), (19, 26, -1), (20, 20, 1), (21, 21, 1), (22, 22, 1), (23, 23, 1), (24, 24, 1),
   (25, 25, 1), (26, 0, 1), (26, 2, -1), (26, 19, -1), (26, 26, 1)]

private theorem foldl_add_eq_init_add_map_sum_cb {α : Type*} (f : α → ℤ) (l : List α) (init : ℤ) :
    l.foldl (fun acc x => acc + f x) init = init + (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih => simp [List.foldl_cons, List.map_cons, List.sum_cons, ih, add_assoc]

private theorem foldl_add_finRange_eq_sum_cb (f : Fin 27 → ℤ) :
    (List.finRange 27).foldl (fun acc k => acc + f k) 0 = ∑ k : Fin 27, f k := by
  rw [foldl_add_eq_init_add_map_sum_cb, zero_add, Fin.sum_univ_def]

private def sparseAddMulCheckRow_cb (C A B : SparseMat27) (r : Fin 27) : Bool :=
  (List.finRange 27).all fun c =>
    sparseVal C r c == sparseVal A r c +
      (List.finRange 27).foldl (fun acc k => acc + sparseVal A r k * sparseVal B k c) 0

private theorem sparseToMat_eq_mul_one_add_of_rows_cb (C A B : SparseMat27)
    (h : ∀ r : Fin 27, sparseAddMulCheckRow_cb C A B r = true) :
    sparseToMat C = sparseToMat A * ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat B) := by
  ext r c
  have hr := h r
  simp only [sparseAddMulCheckRow_cb, List.all_eq_true, List.mem_finRange, true_implies,
    beq_iff_eq] at hr
  have hrc := hr c
  rw [foldl_add_finRange_eq_sum_cb] at hrc
  change sparseVal C r c = _
  rw [hrc, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  rfl

private theorem h3zornToMatrix_e6RootExp_int (r : Fin 72) (k : ℤ) :
    h3zornToMatrix ((e6RootExp r (k : ℝ)).1.toLinearMap) =
      ((1 : Matrix (Fin 27) (Fin 27) ℤ) + k • sparseToMat (e6RootSparse r)).map Int.cast := by
  change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + (k : ℝ) • (e6RootVec r).1) = _
  rw [map_add, _root_.map_one h3zornToMatrix, map_smul, h3zornToMatrix_e6RootVec]
  ext a b
  by_cases h : a = b <;>
    simp only [h, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul, Int.cast_add, Int.cast_one, Int.cast_zero, Int.cast_mul, ↓reduceIte]

private theorem h3zornToMatrix_f4PeirceExp_one (s : Fin 3) (j : Fin 8) (d : SparseMat27)
    (hd : sparseToMat d = sparseToMat (e6RootSparse (f4PosIdx s j)) -
      sparseToMat (e6RootSparse (f4NegIdx s j)) -
      sparseToMat (e6RootSparse (f4PosIdx s j)) *
        sparseToMat (e6RootSparse (f4NegIdx s j))) :
    h3zornToMatrix ((f4PeirceExp s j 1).1.toLinearMap) =
      ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat d).map Int.cast := by
  have hm : (f4PeirceExp s j 1).1.toLinearMap =
      (e6RootExp (f4PosIdx s j) (1 : ℤ)).1.toLinearMap *
      (e6RootExp (f4NegIdx s j) (-1 : ℤ)).1.toLinearMap := by
    simp [f4PeirceExp]
  rw [hm, map_mul, h3zornToMatrix_e6RootExp_int, h3zornToMatrix_e6RootExp_int]
  have hmat : ((1 : Matrix (Fin 27) (Fin 27) ℤ) +
        (1 : ℤ) • sparseToMat (e6RootSparse (f4PosIdx s j))) *
      ((1 : Matrix (Fin 27) (Fin 27) ℤ) +
        (-1 : ℤ) • sparseToMat (e6RootSparse (f4NegIdx s j))) =
      (1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat d := by
    rw [hd]
    simp only [one_zsmul, neg_one_zsmul, sub_eq_add_neg, add_mul, mul_add,
      one_mul, mul_one, mul_neg]
    abel
  rw [← hmat]
  ext r c
  simp [Matrix.mul_apply]

private theorem h3zornToMatrix_w12 :
    h3zornToMatrix (w12.1.toLinearMap) = (sparseToMat w12Sparse).map Int.cast := by
  have hp0d : sparseToMat w12P0Sparse = sparseToMat (e6RootSparse (f4PosIdx 0 0)) -
      sparseToMat (e6RootSparse (f4NegIdx 0 0)) -
      sparseToMat (e6RootSparse (f4PosIdx 0 0)) * sparseToMat (e6RootSparse (f4NegIdx 0 0)) := by
    have h1 := sparseToMat_eq_of_sparseEq (show sparseEq w12P0Sparse
      (sparseSub (sparseSub (e6RootSparse (f4PosIdx 0 0)) (e6RootSparse (f4NegIdx 0 0)))
        (sparseMul (e6RootSparse (f4PosIdx 0 0)) (e6RootSparse (f4NegIdx 0 0)))) = true by decide)
    simpa [sparseToMat_sub, sparseToMat_mul] using h1
  have hp7d : sparseToMat w12P7Sparse = sparseToMat (e6RootSparse (f4PosIdx 0 7)) -
      sparseToMat (e6RootSparse (f4NegIdx 0 7)) -
      sparseToMat (e6RootSparse (f4PosIdx 0 7)) * sparseToMat (e6RootSparse (f4NegIdx 0 7)) := by
    have h1 := sparseToMat_eq_of_sparseEq (show sparseEq w12P7Sparse
      (sparseSub (sparseSub (e6RootSparse (f4PosIdx 0 7)) (e6RootSparse (f4NegIdx 0 7)))
        (sparseMul (e6RootSparse (f4PosIdx 0 7)) (e6RootSparse (f4NegIdx 0 7)))) = true by decide)
    simpa [sparseToMat_sub, sparseToMat_mul] using h1
  have hp0 := h3zornToMatrix_f4PeirceExp_one 0 0 w12P0Sparse hp0d
  have hp7 := h3zornToMatrix_f4PeirceExp_one 0 7 w12P7Sparse hp7d
  have hw_half : sparseToMat w12HalfSparse =
      ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat w12P0Sparse) *
      ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat w12P7Sparse) := by
    have h1 := sparseToMat_eq_one_add_of_check_cb w12HalfSparse
      (sparseAdd (sparseAdd w12P0Sparse w12P7Sparse) (sparseMul w12P0Sparse w12P7Sparse)) (by decide)
    rw [h1, sparseToMat_add, sparseToMat_add, sparseToMat_mul]
    simp only [add_mul, mul_add, one_mul, mul_one, add_assoc]
  have hw_full : sparseToMat w12Sparse =
      sparseToMat w12HalfSparse * ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat w12P0Sparse) :=
    sparseToMat_eq_mul_one_add_of_rows_cb w12Sparse w12HalfSparse w12P0Sparse (fun r => by
      fin_cases r <;> decide)
  have hm : w12.1.toLinearMap =
      ((f4PeirceExp 0 0 1).1.toLinearMap * (f4PeirceExp 0 7 1).1.toLinearMap) *
        (f4PeirceExp 0 0 1).1.toLinearMap := rfl
  rw [hm, map_mul, map_mul, hp0, hp7, hw_full, hw_half]
  ext r c
  simp [Matrix.mul_apply]

private theorem h3zornToMatrix_w23 :
    h3zornToMatrix (w23.1.toLinearMap) = (sparseToMat w23Sparse).map Int.cast := by
  have hp0d : sparseToMat w23P0Sparse = sparseToMat (e6RootSparse (f4PosIdx 1 0)) -
      sparseToMat (e6RootSparse (f4NegIdx 1 0)) -
      sparseToMat (e6RootSparse (f4PosIdx 1 0)) * sparseToMat (e6RootSparse (f4NegIdx 1 0)) := by
    have h1 := sparseToMat_eq_of_sparseEq (show sparseEq w23P0Sparse
      (sparseSub (sparseSub (e6RootSparse (f4PosIdx 1 0)) (e6RootSparse (f4NegIdx 1 0)))
        (sparseMul (e6RootSparse (f4PosIdx 1 0)) (e6RootSparse (f4NegIdx 1 0)))) = true by decide)
    simpa [sparseToMat_sub, sparseToMat_mul] using h1
  have hp7d : sparseToMat w23P7Sparse = sparseToMat (e6RootSparse (f4PosIdx 1 7)) -
      sparseToMat (e6RootSparse (f4NegIdx 1 7)) -
      sparseToMat (e6RootSparse (f4PosIdx 1 7)) * sparseToMat (e6RootSparse (f4NegIdx 1 7)) := by
    have h1 := sparseToMat_eq_of_sparseEq (show sparseEq w23P7Sparse
      (sparseSub (sparseSub (e6RootSparse (f4PosIdx 1 7)) (e6RootSparse (f4NegIdx 1 7)))
        (sparseMul (e6RootSparse (f4PosIdx 1 7)) (e6RootSparse (f4NegIdx 1 7)))) = true by decide)
    simpa [sparseToMat_sub, sparseToMat_mul] using h1
  have hp0 := h3zornToMatrix_f4PeirceExp_one 1 0 w23P0Sparse hp0d
  have hp7 := h3zornToMatrix_f4PeirceExp_one 1 7 w23P7Sparse hp7d
  have hw_half : sparseToMat w23HalfSparse =
      ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat w23P0Sparse) *
      ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat w23P7Sparse) := by
    have h1 := sparseToMat_eq_one_add_of_check_cb w23HalfSparse
      (sparseAdd (sparseAdd w23P0Sparse w23P7Sparse) (sparseMul w23P0Sparse w23P7Sparse)) (by decide)
    rw [h1, sparseToMat_add, sparseToMat_add, sparseToMat_mul]
    simp only [add_mul, mul_add, one_mul, mul_one, add_assoc]
  have hw_full : sparseToMat w23Sparse =
      sparseToMat w23HalfSparse * ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat w23P0Sparse) :=
    sparseToMat_eq_mul_one_add_of_rows_cb w23Sparse w23HalfSparse w23P0Sparse (fun r => by
      fin_cases r <;> decide)
  have hm : w23.1.toLinearMap =
      ((f4PeirceExp 1 0 1).1.toLinearMap * (f4PeirceExp 1 7 1).1.toLinearMap) *
        (f4PeirceExp 1 0 1).1.toLinearMap := rfl
  rw [hm, map_mul, map_mul, hp0, hp7, hw_full, hw_half]
  ext r c
  simp [Matrix.mul_apply]

private theorem h3zornToMatrix_w31 :
    h3zornToMatrix (w31.1.toLinearMap) = (sparseToMat w31Sparse).map Int.cast := by
  have hp0d : sparseToMat w31P0Sparse = sparseToMat (e6RootSparse (f4PosIdx 2 0)) -
      sparseToMat (e6RootSparse (f4NegIdx 2 0)) -
      sparseToMat (e6RootSparse (f4PosIdx 2 0)) * sparseToMat (e6RootSparse (f4NegIdx 2 0)) := by
    have h1 := sparseToMat_eq_of_sparseEq (show sparseEq w31P0Sparse
      (sparseSub (sparseSub (e6RootSparse (f4PosIdx 2 0)) (e6RootSparse (f4NegIdx 2 0)))
        (sparseMul (e6RootSparse (f4PosIdx 2 0)) (e6RootSparse (f4NegIdx 2 0)))) = true by decide)
    simpa [sparseToMat_sub, sparseToMat_mul] using h1
  have hp7d : sparseToMat w31P7Sparse = sparseToMat (e6RootSparse (f4PosIdx 2 7)) -
      sparseToMat (e6RootSparse (f4NegIdx 2 7)) -
      sparseToMat (e6RootSparse (f4PosIdx 2 7)) * sparseToMat (e6RootSparse (f4NegIdx 2 7)) := by
    have h1 := sparseToMat_eq_of_sparseEq (show sparseEq w31P7Sparse
      (sparseSub (sparseSub (e6RootSparse (f4PosIdx 2 7)) (e6RootSparse (f4NegIdx 2 7)))
        (sparseMul (e6RootSparse (f4PosIdx 2 7)) (e6RootSparse (f4NegIdx 2 7)))) = true by decide)
    simpa [sparseToMat_sub, sparseToMat_mul] using h1
  have hp0 := h3zornToMatrix_f4PeirceExp_one 2 0 w31P0Sparse hp0d
  have hp7 := h3zornToMatrix_f4PeirceExp_one 2 7 w31P7Sparse hp7d
  have hw_half : sparseToMat w31HalfSparse =
      ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat w31P0Sparse) *
      ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat w31P7Sparse) := by
    have h1 := sparseToMat_eq_one_add_of_check_cb w31HalfSparse
      (sparseAdd (sparseAdd w31P0Sparse w31P7Sparse) (sparseMul w31P0Sparse w31P7Sparse)) (by decide)
    rw [h1, sparseToMat_add, sparseToMat_add, sparseToMat_mul]
    simp only [add_mul, mul_add, one_mul, mul_one, add_assoc]
  have hw_full : sparseToMat w31Sparse =
      sparseToMat w31HalfSparse * ((1 : Matrix (Fin 27) (Fin 27) ℤ) + sparseToMat w31P0Sparse) :=
    sparseToMat_eq_mul_one_add_of_rows_cb w31Sparse w31HalfSparse w31P0Sparse (fun r => by
      fin_cases r <;> decide)
  have hm : w31.1.toLinearMap =
      ((f4PeirceExp 2 0 1).1.toLinearMap * (f4PeirceExp 2 7 1).1.toLinearMap) *
        (f4PeirceExp 2 0 1).1.toLinearMap := rfl
  rw [hm, map_mul, map_mul, hp0, hp7, hw_full, hw_half]
  ext r c
  simp [Matrix.mul_apply]

private theorem h3ZornCoordinate_of_toMatrix {T : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ} {s : SparseMat27}
    (hs : h3zornToMatrix T.toLinearMap = (sparseToMat s).map Int.cast)
    (X : H3Zorn ℝ) (m : Fin 27) :
    h3ZornCoordinate (T X) m = ∑ k : Fin 27, (sparseVal s m k : ℝ) * h3ZornCoordinate X k := by
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
    rw [h3ZornCoordinate_of_toMatrix h3zornToMatrix_w12, Finset.sum_eq_single 1]
    · rw [(hc 1).1.1]; simp
    · intro k _ hk; rw [(hc k).1.1]
      have hk' : k.val ≠ 1 := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ 1) h
  · change h3ZornCoordinate (w12.1 X) 1 = h3ZornCoordinate X 0
    rw [h3ZornCoordinate_of_toMatrix h3zornToMatrix_w12, Finset.sum_eq_single 0]
    · rw [(hc 0).1.2]; simp
    · intro k _ hk; rw [(hc k).1.2]
      have hk' : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ 0) h
  · change h3ZornCoordinate (w12.1 X) 2 = h3ZornCoordinate X 2
    rw [h3ZornCoordinate_of_toMatrix h3zornToMatrix_w12, Finset.sum_eq_single 2]
    · rw [(hc 2).2]; simp
    · intro k _ hk; rw [(hc k).2]
      have hk' : k.val ≠ 2 := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ 2) h

private theorem w31_diag_coords (X : H3Zorn ℝ) :
    (w31.1 X).α₁ = X.α₃ ∧ (w31.1 X).α₂ = X.α₂ ∧ (w31.1 X).α₃ = X.α₁ := by
  have hc : (List.finRange 27).all (fun k =>
      (sparseVal w31Sparse 0 k == if k.val = 2 then 1 else 0) &&
      (sparseVal w31Sparse 1 k == if k.val = 1 then 1 else 0) &&
      (sparseVal w31Sparse 2 k == if k.val = 0 then 1 else 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc
  refine ⟨?_, ?_, ?_⟩
  · change h3ZornCoordinate (w31.1 X) 0 = h3ZornCoordinate X 2
    rw [h3ZornCoordinate_of_toMatrix h3zornToMatrix_w31, Finset.sum_eq_single 2]
    · rw [(hc 2).1.1]; simp
    · intro k _ hk; rw [(hc k).1.1]
      have hk' : k.val ≠ 2 := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ 2) h
  · change h3ZornCoordinate (w31.1 X) 1 = h3ZornCoordinate X 1
    rw [h3ZornCoordinate_of_toMatrix h3zornToMatrix_w31, Finset.sum_eq_single 1]
    · rw [(hc 1).1.2]; simp
    · intro k _ hk; rw [(hc k).1.2]
      have hk' : k.val ≠ 1 := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ 1) h
  · change h3ZornCoordinate (w31.1 X) 2 = h3ZornCoordinate X 0
    rw [h3ZornCoordinate_of_toMatrix h3zornToMatrix_w31, Finset.sum_eq_single 0]
    · rw [(hc 0).2]; simp
    · intro k _ hk; rw [(hc k).2]
      have hk' : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ 0) h

private theorem w23_coords (X : H3Zorn ℝ) :
    (w23.1 X).α₁ = X.α₁ ∧ (w23.1 X).α₂ = X.α₃ ∧ (w23.1 X).α₃ = X.α₂ ∧
    (X.a = 0 → X.c = 0 → (w23.1 X).a = 0 ∧ (w23.1 X).c = 0) ∧
    zornCoord (w23.1 X).b 0 = -zornCoord X.b 7 ∧
    zornCoord (w23.1 X).b 7 = -zornCoord X.b 0 ∧
    (∀ j : Fin 6, zornCoord (w23.1 X).b ⟨1 + j.val, by omega⟩ =
      zornCoord X.b ⟨1 + j.val, by omega⟩) := by
  have hc1 : (List.finRange 27).all (fun k =>
      (sparseVal w23Sparse 0 k == if k.val = 0 then 1 else 0) &&
      (sparseVal w23Sparse 1 k == if k.val = 2 then 1 else 0) &&
      (sparseVal w23Sparse 2 k == if k.val = 1 then 1 else 0)) = true := by decide
  have hc2 : (List.finRange 8).all (fun j => (List.finRange 27).all (fun k =>
      (if k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19) then
        (sparseVal w23Sparse ⟨3 + j.val, by omega⟩ k == 0) &&
        (sparseVal w23Sparse ⟨19 + j.val, by omega⟩ k == 0)
       else true))) = true := by decide
  have hc3 : (List.finRange 27).all (fun k =>
      (sparseVal w23Sparse 11 k == if k.val = 18 then -1 else 0) &&
      (sparseVal w23Sparse 18 k == if k.val = 11 then -1 else 0)) = true := by decide
  have hc4 : (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      sparseVal w23Sparse ⟨12 + j.val, by omega⟩ k ==
        if k.val = 12 + j.val then 1 else 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc1 hc2 hc3 hc4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate (w23.1 X) 0 = h3ZornCoordinate X 0
    rw [h3ZornCoordinate_of_toMatrix h3zornToMatrix_w23, Finset.sum_eq_single 0]
    · rw [(hc1 0).1.1]; simp
    · intro k _ hk; rw [(hc1 k).1.1]
      have hk' : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ 0) h
  · change h3ZornCoordinate (w23.1 X) 1 = h3ZornCoordinate X 2
    rw [h3ZornCoordinate_of_toMatrix h3zornToMatrix_w23, Finset.sum_eq_single 2]
    · rw [(hc1 2).1.2]; simp
    · intro k _ hk; rw [(hc1 k).1.2]
      have hk' : k.val ≠ 2 := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ 2) h
  · change h3ZornCoordinate (w23.1 X) 2 = h3ZornCoordinate X 1
    rw [h3ZornCoordinate_of_toMatrix h3zornToMatrix_w23, Finset.sum_eq_single 1]
    · rw [(hc1 1).2]; simp
    · intro k _ hk; rw [(hc1 k).2]
      have hk' : k.val ≠ 1 := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ 1) h
  · intro ha hc0
    have hx_ac : ∀ k : Fin 27, ¬(k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19)) →
        h3ZornCoordinate X k = 0 := by
      intro k hk
      by_cases hk11 : k.val < 11
      · have hne : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hne, h3ZornCoord_a_eq, ha]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
      · have hne : k = ⟨19 + (⟨k.val - 19, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hne, h3ZornCoord_c_eq, hc0]; exact (zornCoord_eq_zero_iff 0).mpr rfl _
    constructor <;> refine zorn_eq_of_zornCoord_eq fun j => ?_
    · rw [← h3ZornCoord_a_eq, h3ZornCoordinate_of_toMatrix h3zornToMatrix_w23,
        (zornCoord_eq_zero_iff 0).mpr rfl j]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19)
      · have hm := hc2 j k
        simp only [hk, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hm
        rw [hm.1, Int.cast_zero, zero_mul]
      · rw [hx_ac k hk, mul_zero]
    · rw [← h3ZornCoord_c_eq, h3ZornCoordinate_of_toMatrix h3zornToMatrix_w23,
        (zornCoord_eq_zero_iff 0).mpr rfl j]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19)
      · have hm := hc2 j k
        simp only [hk, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hm
        rw [hm.2, Int.cast_zero, zero_mul]
      · rw [hx_ac k hk, mul_zero]
  · rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate (w23.1 X) 11 = -h3ZornCoordinate X 18
    rw [h3ZornCoordinate_of_toMatrix h3zornToMatrix_w23, Finset.sum_eq_single 18]
    · rw [(hc3 18).1]; simp
    · intro k _ hk; rw [(hc3 k).1]
      have hk' : k.val ≠ 18 := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ 18) h
  · rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate (w23.1 X) 18 = -h3ZornCoordinate X 11
    rw [h3ZornCoordinate_of_toMatrix h3zornToMatrix_w23, Finset.sum_eq_single 11]
    · rw [(hc3 11).2]; simp
    · intro k _ hk; rw [(hc3 k).2]
      have hk' : k.val ≠ 11 := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ 11) h
  · intro j
    rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    have hidx : (⟨11 + (⟨1 + j.val, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
        ⟨12 + j.val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hidx, h3ZornCoordinate_of_toMatrix h3zornToMatrix_w23,
      Finset.sum_eq_single ⟨12 + j.val, by omega⟩]
    · rw [hc4 j ⟨12 + j.val, by omega⟩]; simp
    · intro k _ hk; rw [hc4 j k]
      have hk' : k.val ≠ 12 + j.val := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ _) h

private theorem w23_fix_diag1 : w23.1 h3_diag₁ = h3_diag₁ := by
  obtain ⟨d1, d2, d3, hda, _, _, _⟩ := w23_coords h3_diag₁
  have ha0 : (h3_diag₁ : H3Zorn ℝ).a = 0 := rfl
  have hc0 : (h3_diag₁ : H3Zorn ℝ).c = 0 := rfl
  obtain ⟨da', dc'⟩ := hda ha0 hc0
  have hb0 : (w23.1 h3_diag₁).b = 0 := by
    obtain ⟨_, _, _, _, hb0, hb7, hbmid⟩ := w23_coords h3_diag₁
    rw [← zornCoord_eq_zero_iff]; intro j
    fin_cases j <;> dsimp only
    · change zornCoord (w23.1 h3_diag₁).b 0 = 0
      rw [hb0]; change -(0 : ℝ) = 0; simp
    · exact hbmid 0
    · exact hbmid 1
    · exact hbmid 2
    · exact hbmid 3
    · exact hbmid 4
    · exact hbmid 5
    · change zornCoord (w23.1 h3_diag₁).b 7 = 0
      rw [hb7]; change -(0 : ℝ) = 0; simp
  apply ext_h3 <;> [exact d1; exact d2; exact d3; exact da'; exact hb0; exact dc']

/-! ### Steps B1–B3: `F₄(4)` Peirce/D₄/Triality Reduction -/

private theorem real_quad_root_cb {a b c : ℝ} (ha : a ≠ 0) (hd : 0 ≤ b ^ 2 + 4 * a * c) :
    ∃ t : ℝ, c + t * b - t ^ 2 * a = 0 := by
  set s := Real.sqrt (b ^ 2 + 4 * a * c)
  refine ⟨(b + s) / (2 * a), ?_⟩
  have hsq : s ^ 2 = b ^ 2 + 4 * a * c := Real.sq_sqrt hd
  field_simp [ha]
  linear_combination -hsq

private theorem zorn_norm_zornCoord (x : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.norm x = zornCoord x 0 * zornCoord x 7 -
      (zornCoord x 1 * zornCoord x 4 + zornCoord x 2 * zornCoord x 5 +
        zornCoord x 3 * zornCoord x 6) := by
  simp [ZornVectorMatrix.norm, ZornVec3.dot, zornCoord, Fin.sum_univ_three]

private theorem neg_sum_neg_of_lt_cb {a₁ a₂ a₀ a₇ s : ℝ}
    (hnorm : a₁ * a₂ = a₀ * a₇ - s)
    (hlt : (a₁ - a₂) ^ 2 + 4 * a₀ * a₇ < 0) :
    s ≠ 0 := by
  intro hs
  rw [hs, sub_zero] at hnorm
  have hsq : 0 ≤ (a₁ + a₂) ^ 2 := sq_nonneg _
  linarith [hnorm, hlt, hsq]

private theorem choose_nonzero_of_one_neg_sum_cb {x₁ x₂ x₃ y₁ y₂ y₃ : ℝ}
    (h : x₁ * y₁ + x₂ * y₂ + x₃ * y₃ = -1) :
    x₁ ≠ 0 ∨ x₂ ≠ 0 ∨ x₃ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  rcases hcon with ⟨h1, h2, h3⟩
  rw [h1, h2, h3] at h
  norm_num at h

private theorem sub_ne_of_mul_zero_sum_ne_cb {x y : ℝ} (hm : x * y = 0) (hs : x + y ≠ 0) :
    x ≠ y := by
  intro heq
  subst heq
  rcases mul_eq_zero.mp hm with h | h <;> simp [h] at hs

private theorem h3ZornCoordinate_f4PeirceExp (s : Fin 3) (j : Fin 8) (t : ℝ)
    (X : H3Zorn ℝ) (m : Fin 27) :
    h3ZornCoordinate ((f4PeirceExp s j t).1 X) m =
      h3ZornCoordinate X m +
        t * ∑ k : Fin 27,
          ((sparseVal (e6RootSparse (f4PosIdx s j)) m k -
            sparseVal (e6RootSparse (f4NegIdx s j)) m k : ℤ) : ℝ) * h3ZornCoordinate X k -
        t ^ 2 * ∑ l : Fin 27,
          (sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m l : ℝ) *
            h3ZornCoordinate X l := by
  have hY : ∀ k : Fin 27,
      h3ZornCoordinate ((e6RootExp (f4NegIdx s j) (-t)).1 X) k =
        h3ZornCoordinate X k -
          t * ∑ l : Fin 27,
            (sparseVal (e6RootSparse (f4NegIdx s j)) k l : ℝ) * h3ZornCoordinate X l := by
    intro k
    rw [h3ZornCoordinate_e6RootExp]
    ring
  change h3ZornCoordinate ((e6RootExp (f4PosIdx s j) t).1
      ((e6RootExp (f4NegIdx s j) (-t)).1 X)) m = _
  rw [h3ZornCoordinate_e6RootExp, hY m]
  have hsum : ∑ k : Fin 27, (sparseVal (e6RootSparse (f4PosIdx s j)) m k : ℝ) *
      h3ZornCoordinate ((e6RootExp (f4NegIdx s j) (-t)).1 X) k =
      (∑ k : Fin 27, (sparseVal (e6RootSparse (f4PosIdx s j)) m k : ℝ) * h3ZornCoordinate X k) -
      t * ∑ l : Fin 27,
        (sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m l : ℝ) *
          h3ZornCoordinate X l := by
    have hsplit : ∑ k : Fin 27, (sparseVal (e6RootSparse (f4PosIdx s j)) m k : ℝ) *
        h3ZornCoordinate ((e6RootExp (f4NegIdx s j) (-t)).1 X) k =
        (∑ k : Fin 27, (sparseVal (e6RootSparse (f4PosIdx s j)) m k : ℝ) * h3ZornCoordinate X k) -
        t * ∑ k : Fin 27, (sparseVal (e6RootSparse (f4PosIdx s j)) m k : ℝ) *
          ∑ l : Fin 27, (sparseVal (e6RootSparse (f4NegIdx s j)) k l : ℝ) * h3ZornCoordinate X l := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hY k]
      ring
    rw [hsplit]
    congr 2
    calc
      ∑ k : Fin 27, (sparseVal (e6RootSparse (f4PosIdx s j)) m k : ℝ) *
          ∑ l : Fin 27, (sparseVal (e6RootSparse (f4NegIdx s j)) k l : ℝ) * h3ZornCoordinate X l
        = ∑ k : Fin 27, ∑ l : Fin 27,
            ((sparseVal (e6RootSparse (f4PosIdx s j)) m k : ℝ) *
              (sparseVal (e6RootSparse (f4NegIdx s j)) k l : ℝ)) * h3ZornCoordinate X l := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ l : Fin 27, ∑ k : Fin 27,
            ((sparseVal (e6RootSparse (f4PosIdx s j)) m k : ℝ) *
              (sparseVal (e6RootSparse (f4NegIdx s j)) k l : ℝ)) * h3ZornCoordinate X l :=
          Finset.sum_comm
      _ = ∑ l : Fin 27,
            (sparseVal (sparseMul (e6RootSparse (f4PosIdx s j)) (e6RootSparse (f4NegIdx s j))) m l : ℝ) *
              h3ZornCoordinate X l := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.sum_mul, sparseVal_mul, Int.cast_sum]
          congr 1
          refine Finset.sum_congr rfl fun k _ => by simp
  rw [hsum]
  have hsub :
      (∑ k : Fin 27,
          ((sparseVal (e6RootSparse (f4PosIdx s j)) m k -
            sparseVal (e6RootSparse (f4NegIdx s j)) m k : ℤ) : ℝ) * h3ZornCoordinate X k) =
      (∑ k : Fin 27, (sparseVal (e6RootSparse (f4PosIdx s j)) m k : ℝ) * h3ZornCoordinate X k) -
      (∑ l : Fin 27, (sparseVal (e6RootSparse (f4NegIdx s j)) m l : ℝ) * h3ZornCoordinate X l) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [hsub]
  ring

private theorem f4Peirce_0_0_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((f4PeirceExp 0 0 t).1 X).α₁ = X.α₁ + t * zornCoord X.a 7 ∧
    ((f4PeirceExp 0 0 t).1 X).α₂ = X.α₂ - t * zornCoord X.a 7 ∧
    ((f4PeirceExp 0 0 t).1 X).α₃ = X.α₃ ∧
    zornCoord ((f4PeirceExp 0 0 t).1 X).a 0 =
      zornCoord X.a 0 + t * (X.α₂ - X.α₁) - t ^ 2 * zornCoord X.a 7 ∧
    zornCoord ((f4PeirceExp 0 0 t).1 X).a 7 = zornCoord X.a 7 ∧
    (∀ k : Fin 6, zornCoord ((f4PeirceExp 0 0 t).1 X).a ⟨1 + k.val, by omega⟩ =
      zornCoord X.a ⟨1 + k.val, by omega⟩) := by
  have hc1 : (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 0 0)) 0 k -
        sparseVal (e6RootSparse (f4NegIdx 0 0)) 0 k == if k.val = 10 then 1 else 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 0 0)) 1 k -
        sparseVal (e6RootSparse (f4NegIdx 0 0)) 1 k == if k.val = 10 then -1 else 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 0 0)) 2 k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 0 0)) 2 k == 0)) = true := by decide
  have hc2 : (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 0 0)) 3 k -
        sparseVal (e6RootSparse (f4NegIdx 0 0)) 3 k ==
          if k.val = 1 then 1 else if k.val = 0 then -1 else 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 0)) (e6RootSparse (f4NegIdx 0 0))) 3 k ==
        if k.val = 10 then 1 else 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 0 0)) 10 k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 0 0)) 10 k == 0)) = true := by decide
  have hc3 : (List.finRange 27).all (fun k =>
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 0)) (e6RootSparse (f4NegIdx 0 0))) 0 k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 0)) (e6RootSparse (f4NegIdx 0 0))) 1 k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 0)) (e6RootSparse (f4NegIdx 0 0))) 2 k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 0)) (e6RootSparse (f4NegIdx 0 0))) 10 k == 0)) =
      true := by decide
  have hc4 : (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 0 0)) ⟨4 + i.val, by omega⟩ k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 0 0)) ⟨4 + i.val, by omega⟩ k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 0)) (e6RootSparse (f4NegIdx 0 0)))
        ⟨4 + i.val, by omega⟩ k == 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc1 hc2 hc3 hc4
  have ha7eq : h3ZornCoordinate X 10 = zornCoord X.a 7 := (h3ZornCoord_a_eq X 7).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((f4PeirceExp 0 0 t).1 X) 0 = _
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_single 10, Finset.sum_eq_zero]
    · rw [(hc1 10).1.1.1]; simp; rw [ha7eq]; rfl
    · intro k _; rw [(hc3 k).1.1.1]; simp
    · intro k _ hk; rw [(hc1 k).1.1.1]; have hk' : k.val ≠ 10 := fun h => hk (Fin.ext h); simp [hk']
    · intro h; exact absurd (Finset.mem_univ 10) h
  · change h3ZornCoordinate ((f4PeirceExp 0 0 t).1 X) 1 = _
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_single 10, Finset.sum_eq_zero]
    · rw [(hc1 10).1.1.2]; simp; rw [ha7eq]
      change X.α₂ + -(t * zornCoord X.a 7) = X.α₂ - t * zornCoord X.a 7
      ring
    · intro k _; rw [(hc3 k).1.1.2]; simp
    · intro k _ hk; rw [(hc1 k).1.1.2]; have hk' : k.val ≠ 10 := fun h => hk (Fin.ext h); simp [hk']
    · intro h; exact absurd (Finset.mem_univ 10) h
  · change h3ZornCoordinate ((f4PeirceExp 0 0 t).1 X) 2 = h3ZornCoordinate X 2
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · ring
    · intro k _; rw [(hc3 k).1.2]; simp
    · intro k _; rw [(hc1 k).1.2, (hc1 k).2]; simp
  · rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    change h3ZornCoordinate ((f4PeirceExp 0 0 t).1 X) 3 =
      h3ZornCoordinate X 3 + t * (h3ZornCoordinate X 1 - h3ZornCoordinate X 0) -
        t ^ 2 * h3ZornCoordinate X 10
    rw [h3ZornCoordinate_f4PeirceExp]
    have hs1 : ∑ k : Fin 27,
        ((sparseVal (e6RootSparse (f4PosIdx 0 0)) 3 k -
          sparseVal (e6RootSparse (f4NegIdx 0 0)) 3 k : ℤ) : ℝ) * h3ZornCoordinate X k =
        h3ZornCoordinate X 1 - h3ZornCoordinate X 0 := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun k : Fin 27 => k = 0 ∨ k = 1)]
      have hz : ∑ k ∈ Finset.univ.filter (fun k : Fin 27 => ¬(k = 0 ∨ k = 1)),
          ((sparseVal (e6RootSparse (f4PosIdx 0 0)) 3 k -
            sparseVal (e6RootSparse (f4NegIdx 0 0)) 3 k : ℤ) : ℝ) * h3ZornCoordinate X k = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hnk := (Finset.mem_filter.mp hk).2
        push Not at hnk
        have hk0 : k.val ≠ 0 := fun h => hnk.1 (Fin.ext h)
        have hk1 : k.val ≠ 1 := fun h => hnk.2 (Fin.ext h)
        rw [(hc2 k).1.1.1]; simp [hk0, hk1]
      rw [hz, add_zero]
      have hf : Finset.univ.filter (fun k : Fin 27 => k = 0 ∨ k = 1) = {0, 1} := by decide
      rw [hf, Finset.sum_insert (by decide), Finset.sum_singleton, (hc2 0).1.1.1, (hc2 1).1.1.1]
      simp; ring
    have hs2 : ∑ l : Fin 27,
        (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 0)) (e6RootSparse (f4NegIdx 0 0))) 3 l : ℝ) *
          h3ZornCoordinate X l = h3ZornCoordinate X 10 := by
      rw [Finset.sum_eq_single 10]
      · rw [(hc2 10).1.1.2]; simp
      · intro k _ hk; rw [(hc2 k).1.1.2]; have hk' : k.val ≠ 10 := fun h => hk (Fin.ext h); simp [hk']
      · intro h; exact absurd (Finset.mem_univ 10) h
    rw [hs1, hs2]
  · rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    change h3ZornCoordinate ((f4PeirceExp 0 0 t).1 X) 10 = h3ZornCoordinate X 10
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · ring
    · intro k _; rw [(hc3 k).2]; simp
    · intro k _; rw [(hc2 k).1.2, (hc2 k).2]; simp
  · intro i
    rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    have hidx : (⟨3 + (⟨1 + i.val, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
        ⟨4 + i.val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hidx, h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · ring
    · intro k _; rw [(hc4 i k).2]; simp
    · intro k _; rw [(hc4 i k).1.1, (hc4 i k).1.2]; simp

private theorem f4Peirce_0_7_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((f4PeirceExp 0 7 t).1 X).α₁ = X.α₁ + t * zornCoord X.a 0 ∧
    ((f4PeirceExp 0 7 t).1 X).α₂ = X.α₂ - t * zornCoord X.a 0 ∧
    ((f4PeirceExp 0 7 t).1 X).α₃ = X.α₃ ∧
    zornCoord ((f4PeirceExp 0 7 t).1 X).a 0 = zornCoord X.a 0 ∧
    zornCoord ((f4PeirceExp 0 7 t).1 X).a 7 =
      zornCoord X.a 7 + t * (X.α₂ - X.α₁) - t ^ 2 * zornCoord X.a 0 ∧
    (∀ k : Fin 6, zornCoord ((f4PeirceExp 0 7 t).1 X).a ⟨1 + k.val, by omega⟩ =
      zornCoord X.a ⟨1 + k.val, by omega⟩) := by
  have hc1 : (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 0 7)) 0 k -
        sparseVal (e6RootSparse (f4NegIdx 0 7)) 0 k == if k.val = 3 then 1 else 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 0 7)) 1 k -
        sparseVal (e6RootSparse (f4NegIdx 0 7)) 1 k == if k.val = 3 then -1 else 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 0 7)) 2 k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 0 7)) 2 k == 0)) = true := by decide
  have hc2 : (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 0 7)) 10 k -
        sparseVal (e6RootSparse (f4NegIdx 0 7)) 10 k ==
          if k.val = 1 then 1 else if k.val = 0 then -1 else 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 7)) (e6RootSparse (f4NegIdx 0 7))) 10 k ==
        if k.val = 3 then 1 else 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 0 7)) 3 k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 0 7)) 3 k == 0)) = true := by decide
  have hc3 : (List.finRange 27).all (fun k =>
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 7)) (e6RootSparse (f4NegIdx 0 7))) 0 k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 7)) (e6RootSparse (f4NegIdx 0 7))) 1 k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 7)) (e6RootSparse (f4NegIdx 0 7))) 2 k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 7)) (e6RootSparse (f4NegIdx 0 7))) 3 k == 0)) =
      true := by decide
  have hc4 : (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 0 7)) ⟨4 + i.val, by omega⟩ k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 0 7)) ⟨4 + i.val, by omega⟩ k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 7)) (e6RootSparse (f4NegIdx 0 7)))
        ⟨4 + i.val, by omega⟩ k == 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc1 hc2 hc3 hc4
  have ha0eq : h3ZornCoordinate X 3 = zornCoord X.a 0 := (h3ZornCoord_a_eq X 0).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((f4PeirceExp 0 7 t).1 X) 0 = _
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_single 3, Finset.sum_eq_zero]
    · rw [(hc1 3).1.1.1]; simp; rw [ha0eq]; rfl
    · intro k _; rw [(hc3 k).1.1.1]; simp
    · intro k _ hk; rw [(hc1 k).1.1.1]; have hk' : k.val ≠ 3 := fun h => hk (Fin.ext h); simp [hk']
    · intro h; exact absurd (Finset.mem_univ 3) h
  · change h3ZornCoordinate ((f4PeirceExp 0 7 t).1 X) 1 = _
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_single 3, Finset.sum_eq_zero]
    · rw [(hc1 3).1.1.2]; simp; rw [ha0eq]
      change X.α₂ + -(t * zornCoord X.a 0) = X.α₂ - t * zornCoord X.a 0
      ring
    · intro k _; rw [(hc3 k).1.1.2]; simp
    · intro k _ hk; rw [(hc1 k).1.1.2]; have hk' : k.val ≠ 3 := fun h => hk (Fin.ext h); simp [hk']
    · intro h; exact absurd (Finset.mem_univ 3) h
  · change h3ZornCoordinate ((f4PeirceExp 0 7 t).1 X) 2 = h3ZornCoordinate X 2
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · ring
    · intro k _; rw [(hc3 k).1.2]; simp
    · intro k _; rw [(hc1 k).1.2, (hc1 k).2]; simp
  · rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    change h3ZornCoordinate ((f4PeirceExp 0 7 t).1 X) 3 = h3ZornCoordinate X 3
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · ring
    · intro k _; rw [(hc3 k).2]; simp
    · intro k _; rw [(hc2 k).1.2, (hc2 k).2]; simp
  · rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    change h3ZornCoordinate ((f4PeirceExp 0 7 t).1 X) 10 =
      h3ZornCoordinate X 10 + t * (h3ZornCoordinate X 1 - h3ZornCoordinate X 0) -
        t ^ 2 * h3ZornCoordinate X 3
    rw [h3ZornCoordinate_f4PeirceExp]
    have hs1 : ∑ k : Fin 27,
        ((sparseVal (e6RootSparse (f4PosIdx 0 7)) 10 k -
          sparseVal (e6RootSparse (f4NegIdx 0 7)) 10 k : ℤ) : ℝ) * h3ZornCoordinate X k =
        h3ZornCoordinate X 1 - h3ZornCoordinate X 0 := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun k : Fin 27 => k = 0 ∨ k = 1)]
      have hz : ∑ k ∈ Finset.univ.filter (fun k : Fin 27 => ¬(k = 0 ∨ k = 1)),
          ((sparseVal (e6RootSparse (f4PosIdx 0 7)) 10 k -
            sparseVal (e6RootSparse (f4NegIdx 0 7)) 10 k : ℤ) : ℝ) * h3ZornCoordinate X k = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hnk := (Finset.mem_filter.mp hk).2
        push Not at hnk
        have hk0 : k.val ≠ 0 := fun h => hnk.1 (Fin.ext h)
        have hk1 : k.val ≠ 1 := fun h => hnk.2 (Fin.ext h)
        rw [(hc2 k).1.1.1]; simp [hk0, hk1]
      rw [hz, add_zero]
      have hf : Finset.univ.filter (fun k : Fin 27 => k = 0 ∨ k = 1) = {0, 1} := by decide
      rw [hf, Finset.sum_insert (by decide), Finset.sum_singleton, (hc2 0).1.1.1, (hc2 1).1.1.1]
      simp; ring
    have hs2 : ∑ l : Fin 27,
        (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 7)) (e6RootSparse (f4NegIdx 0 7))) 10 l : ℝ) *
          h3ZornCoordinate X l = h3ZornCoordinate X 3 := by
      rw [Finset.sum_eq_single 3]
      · rw [(hc2 3).1.1.2]; simp
      · intro k _ hk; rw [(hc2 k).1.1.2]; have hk' : k.val ≠ 3 := fun h => hk (Fin.ext h); simp [hk']
      · intro h; exact absurd (Finset.mem_univ 3) h
    rw [hs1, hs2]
  · intro i
    rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    have hidx : (⟨3 + (⟨1 + i.val, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
        ⟨4 + i.val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hidx, h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · ring
    · intro k _; rw [(hc4 i k).2]; simp
    · intro k _; rw [(hc4 i k).1.1, (hc4 i k).1.2]; simp

private theorem f4Peirce_0_preserves_blocks (j : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((f4PeirceExp 0 j t).1 X).α₁ + ((f4PeirceExp 0 j t).1 X).α₂ = X.α₁ + X.α₂ ∧
    ((f4PeirceExp 0 j t).1 X).α₃ = X.α₃ ∧
    (X.b = 0 → X.c = 0 → ((f4PeirceExp 0 j t).1 X).b = 0 ∧ ((f4PeirceExp 0 j t).1 X).c = 0) := by
  have hc1 : (List.finRange 8).all (fun j => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 0 j)) 0 k +
        sparseVal (e6RootSparse (f4PosIdx 0 j)) 1 k ==
        sparseVal (e6RootSparse (f4NegIdx 0 j)) 0 k +
        sparseVal (e6RootSparse (f4NegIdx 0 j)) 1 k) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 0 k +
        sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 1 k == 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 0 j)) 2 k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 0 j)) 2 k == 0))) = true := by decide
  have hc2 : (List.finRange 8).all (fun j => (List.finRange 16).all (fun r =>
      (List.finRange 11).all (fun k =>
        (sparseVal (e6RootSparse (f4PosIdx 0 j)) ⟨11 + r.val, by omega⟩ ⟨k.val, by omega⟩ == 0) &&
        (sparseVal (e6RootSparse (f4NegIdx 0 j)) ⟨11 + r.val, by omega⟩ ⟨k.val, by omega⟩ == 0)))) =
      true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc1 hc2
  have hzero_bc : ∀ (r : Fin 72) (s : ℝ) (Y : H3Zorn ℝ),
      (∀ (i : Fin 16) (k : Fin 11),
        sparseVal (e6RootSparse r) ⟨11 + i.val, by omega⟩ ⟨k.val, by omega⟩ = 0) →
      Y.b = 0 → Y.c = 0 →
      ((e6RootExp r s).1 Y).b = 0 ∧ ((e6RootExp r s).1 Y).c = 0 := by
    intro r s Y hzr hb hc0
    have hyk : ∀ k : Fin 27, 11 ≤ k.val → h3ZornCoordinate Y k = 0 := by
      intro k hk
      by_cases hk19 : k.val < 19
      · have hne : k = ⟨11 + (⟨k.val - 11, by omega⟩ : Fin 8).val, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hne, h3ZornCoord_b_eq, hb, (zornCoord_eq_zero_iff 0).mpr rfl]
      · have hne : k = ⟨19 + (⟨k.val - 19, by omega⟩ : Fin 8).val, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hne, h3ZornCoord_c_eq, hc0, (zornCoord_eq_zero_iff 0).mpr rfl]
    have hrow : ∀ i : Fin 16, h3ZornCoordinate ((e6RootExp r s).1 Y) ⟨11 + i.val, by omega⟩ = 0 := by
      intro i
      rw [h3ZornCoordinate_e6RootExp, hyk _ (by dsimp; omega), zero_add]
      have hs0 : ∑ k : Fin 27,
          (sparseVal (e6RootSparse r) ⟨11 + i.val, by omega⟩ k : ℝ) * h3ZornCoordinate Y k = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k.val < 11
        · have hne : k = ⟨(⟨k.val, hk⟩ : Fin 11).val, by omega⟩ := Fin.ext rfl
          rw [hne, hzr i ⟨k.val, hk⟩, Int.cast_zero, zero_mul]
        · rw [hyk k (by omega), mul_zero]
      rw [hs0, mul_zero]
    constructor <;> refine zorn_eq_of_zornCoord_eq fun l => ?_
    · rw [← h3ZornCoord_b_eq, (zornCoord_eq_zero_iff 0).mpr rfl l]
      have hne : (⟨11 + l.val, by omega⟩ : Fin 27) = ⟨11 + (⟨l.val, by omega⟩ : Fin 16).val, by omega⟩ :=
        Fin.ext rfl
      rw [hne]
      exact hrow ⟨l.val, by omega⟩
    · rw [← h3ZornCoord_c_eq, (zornCoord_eq_zero_iff 0).mpr rfl l]
      have hne : (⟨19 + l.val, by omega⟩ : Fin 27) = ⟨11 + (⟨8 + l.val, by omega⟩ : Fin 16).val, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hne]
      exact hrow ⟨8 + l.val, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · change h3ZornCoordinate ((f4PeirceExp 0 j t).1 X) 0 +
      h3ZornCoordinate ((f4PeirceExp 0 j t).1 X) 1 = X.α₁ + X.α₂
    rw [h3ZornCoordinate_f4PeirceExp, h3ZornCoordinate_f4PeirceExp]
    have hs1 : ∑ k : Fin 27,
        ((sparseVal (e6RootSparse (f4PosIdx 0 j)) 0 k -
          sparseVal (e6RootSparse (f4NegIdx 0 j)) 0 k : ℤ) : ℝ) * h3ZornCoordinate X k +
        ∑ k : Fin 27,
        ((sparseVal (e6RootSparse (f4PosIdx 0 j)) 1 k -
          sparseVal (e6RootSparse (f4NegIdx 0 j)) 1 k : ℤ) : ℝ) * h3ZornCoordinate X k = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun k _ => ?_
      have h01 : sparseVal (e6RootSparse (f4PosIdx 0 j)) 0 k -
            sparseVal (e6RootSparse (f4NegIdx 0 j)) 0 k +
          (sparseVal (e6RootSparse (f4PosIdx 0 j)) 1 k -
            sparseVal (e6RootSparse (f4NegIdx 0 j)) 1 k) = 0 := by
        have h := (hc1 j k).1.1.1
        omega
      have h01R : ((sparseVal (e6RootSparse (f4PosIdx 0 j)) 0 k -
            sparseVal (e6RootSparse (f4NegIdx 0 j)) 0 k : ℤ) : ℝ) +
          ((sparseVal (e6RootSparse (f4PosIdx 0 j)) 1 k -
            sparseVal (e6RootSparse (f4NegIdx 0 j)) 1 k : ℤ) : ℝ) = 0 := by
        exact_mod_cast h01
      calc
        ((sparseVal (e6RootSparse (f4PosIdx 0 j)) 0 k -
            sparseVal (e6RootSparse (f4NegIdx 0 j)) 0 k : ℤ) : ℝ) * h3ZornCoordinate X k +
          ((sparseVal (e6RootSparse (f4PosIdx 0 j)) 1 k -
            sparseVal (e6RootSparse (f4NegIdx 0 j)) 1 k : ℤ) : ℝ) * h3ZornCoordinate X k
          = (((sparseVal (e6RootSparse (f4PosIdx 0 j)) 0 k -
              sparseVal (e6RootSparse (f4NegIdx 0 j)) 0 k : ℤ) : ℝ) +
            ((sparseVal (e6RootSparse (f4PosIdx 0 j)) 1 k -
              sparseVal (e6RootSparse (f4NegIdx 0 j)) 1 k : ℤ) : ℝ)) * h3ZornCoordinate X k := by
            ring
        _ = 0 := by rw [h01R, zero_mul]
    have hs2 : ∑ l : Fin 27,
        (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 0 l : ℝ) *
          h3ZornCoordinate X l +
        ∑ l : Fin 27,
        (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 1 l : ℝ) *
          h3ZornCoordinate X l = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun l _ => ?_
      have h01R : (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 0 l : ℝ) +
          (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 1 l : ℝ) = 0 := by
        exact_mod_cast (hc1 j l).1.1.2
      calc
        (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 0 l : ℝ) *
            h3ZornCoordinate X l +
          (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 1 l : ℝ) *
            h3ZornCoordinate X l
          = ((sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 0 l : ℝ) +
            (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 1 l : ℝ)) *
              h3ZornCoordinate X l := by
            ring
        _ = 0 := by rw [h01R, zero_mul]
    calc
      h3ZornCoordinate X 0 + t * ∑ k : Fin 27,
            ((sparseVal (e6RootSparse (f4PosIdx 0 j)) 0 k -
              sparseVal (e6RootSparse (f4NegIdx 0 j)) 0 k : ℤ) : ℝ) * h3ZornCoordinate X k -
          t ^ 2 * ∑ l : Fin 27,
            (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 0 l : ℝ) *
              h3ZornCoordinate X l +
        (h3ZornCoordinate X 1 + t * ∑ k : Fin 27,
            ((sparseVal (e6RootSparse (f4PosIdx 0 j)) 1 k -
              sparseVal (e6RootSparse (f4NegIdx 0 j)) 1 k : ℤ) : ℝ) * h3ZornCoordinate X k -
          t ^ 2 * ∑ l : Fin 27,
            (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 1 l : ℝ) *
              h3ZornCoordinate X l)
        = (h3ZornCoordinate X 0 + h3ZornCoordinate X 1) +
            t * (∑ k : Fin 27,
              ((sparseVal (e6RootSparse (f4PosIdx 0 j)) 0 k -
                sparseVal (e6RootSparse (f4NegIdx 0 j)) 0 k : ℤ) : ℝ) * h3ZornCoordinate X k +
              ∑ k : Fin 27,
              ((sparseVal (e6RootSparse (f4PosIdx 0 j)) 1 k -
                sparseVal (e6RootSparse (f4NegIdx 0 j)) 1 k : ℤ) : ℝ) * h3ZornCoordinate X k) -
            t ^ 2 * (∑ l : Fin 27,
              (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 0 l : ℝ) *
                h3ZornCoordinate X l +
              ∑ l : Fin 27,
              (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 1 l : ℝ) *
                h3ZornCoordinate X l) := by ring
      _ = X.α₁ + X.α₂ := by rw [hs1, hs2]; change (X.α₁ + X.α₂) + t * 0 - t ^ 2 * 0 = _; ring
  · change h3ZornCoordinate ((f4PeirceExp 0 j t).1 X) 2 = h3ZornCoordinate X 2
    rw [h3ZornCoordinate_f4PeirceExp]
    have hs1 : ∑ k : Fin 27,
        ((sparseVal (e6RootSparse (f4PosIdx 0 j)) 2 k -
          sparseVal (e6RootSparse (f4NegIdx 0 j)) 2 k : ℤ) : ℝ) * h3ZornCoordinate X k = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [(hc1 j k).1.2, (hc1 j k).2]; simp
    have hs2 : ∑ l : Fin 27,
        (sparseVal (sparseMul (e6RootSparse (f4PosIdx 0 j)) (e6RootSparse (f4NegIdx 0 j))) 2 l : ℝ) *
          h3ZornCoordinate X l = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [sparseVal_mul]
      have hz : ∑ k : Fin 27, sparseVal (e6RootSparse (f4PosIdx 0 j)) 2 k *
          sparseVal (e6RootSparse (f4NegIdx 0 j)) k l = 0 :=
        Finset.sum_eq_zero fun k _ => by rw [(hc1 j k).1.2, zero_mul]
      rw [hz, Int.cast_zero, zero_mul]
    rw [hs1, hs2]; ring
  · intro hb hc0
    obtain ⟨hb1, hc1'⟩ := hzero_bc (f4NegIdx 0 j) (-t) X (fun i k => (hc2 j i k).2) hb hc0
    exact hzero_bc (f4PosIdx 0 j) t _ (fun i k => (hc2 j i k).1) hb1 hc1'

private def aMidRoot (j : Fin 6) : Fin 72 :=
  ![10, 14, 17, 20, 22, 23] j

private def aMidOppIdx (j : Fin 6) : Fin 8 :=
  ![4, 5, 6, 1, 2, 3] j

private theorem d4_aMidRoot_lt24 (j : Fin 6) : (aMidRoot j).val < 24 := by
  fin_cases j <;> decide

private theorem d4_aMidRoot_coords (j : Fin 6) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (aMidRoot j) t).1 X).α₁ = X.α₁ ∧
    ((e6RootExp (aMidRoot j) t).1 X).α₂ = X.α₂ ∧
    ((e6RootExp (aMidRoot j) t).1 X).α₃ = X.α₃ ∧
    zornCoord ((e6RootExp (aMidRoot j) t).1 X).a 0 = zornCoord X.a 0 ∧
    zornCoord ((e6RootExp (aMidRoot j) t).1 X).a 7 =
      zornCoord X.a 7 + t * zornCoord X.a (aMidOppIdx j) ∧
    (∀ i : Fin 6, zornCoord ((e6RootExp (aMidRoot j) t).1 X).a ⟨1 + i.val, by omega⟩ =
      if i = j then zornCoord X.a ⟨1 + i.val, by omega⟩ + t * zornCoord X.a 0
      else zornCoord X.a ⟨1 + i.val, by omega⟩) := by
  have hb := d4_rootExp_preserves_blocks (d4_aMidRoot_lt24 j) t X
  have hc : (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (aMidRoot j)) 3 k == 0) &&
      (sparseVal (e6RootSparse (aMidRoot j)) 10 k ==
        if k.val = 3 + (aMidOppIdx j).val then 1 else 0))) = true := by decide
  have hc2 : (List.finRange 6).all (fun j => (List.finRange 6).all (fun i =>
      (List.finRange 27).all (fun k =>
        sparseVal (e6RootSparse (aMidRoot j)) ⟨4 + i.val, by omega⟩ k ==
          if i == j && k.val == 3 then 1 else 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc hc2
  refine ⟨hb.1, hb.2.1, hb.2.2.1, ?_, ?_, ?_⟩
  · rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    exact rootExp_coord_unchanged (aMidRoot j) 3 t X fun k => (hc j k).1
  · rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    change h3ZornCoordinate ((e6RootExp (aMidRoot j) t).1 X) 10 =
      h3ZornCoordinate X 10 + t * h3ZornCoordinate X ⟨3 + (aMidOppIdx j).val, by omega⟩
    rw [h3ZornCoordinate_e6RootExp, Finset.sum_eq_single ⟨3 + (aMidOppIdx j).val, by omega⟩]
    · rw [(hc j _).2]; simp
    · intro k _ hk; rw [(hc j k).2]
      have hk' : k.val ≠ 3 + (aMidOppIdx j).val := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i
    rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    have hidx : (⟨3 + (⟨1 + i.val, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
        ⟨4 + i.val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hidx, h3ZornCoordinate_e6RootExp]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single 3]
      · rw [hc2 i i 3, ← h3ZornCoord_a_eq X 0]; simp
      · intro k _ hk; rw [hc2 i i k]
        have hk' : k.val ≠ 3 := fun h => hk (Fin.ext h)
        simp [hk']
      · intro h; exact absurd (Finset.mem_univ 3) h
    · have hs0 : ∑ k : Fin 27,
          (sparseVal (e6RootSparse (aMidRoot j)) ⟨4 + i.val, by omega⟩ k : ℝ) *
            h3ZornCoordinate X k = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hc2 j i k]
        simp [hij]
      rw [hs0, mul_zero, add_zero]
      simp [hij]

private def aPullRoot (j : Fin 6) : Fin 72 := ⟨j.val, by omega⟩

private theorem d4_aPullRoot_lt24 (j : Fin 6) : (aPullRoot j).val < 24 := by
  dsimp [aPullRoot]; omega

private theorem d4_aPullRoot_coords (j : Fin 6) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (aPullRoot j) t).1 X).α₁ = X.α₁ ∧
    ((e6RootExp (aPullRoot j) t).1 X).α₂ = X.α₂ ∧
    ((e6RootExp (aPullRoot j) t).1 X).α₃ = X.α₃ ∧
    zornCoord ((e6RootExp (aPullRoot j) t).1 X).a 0 =
      zornCoord X.a 0 - t * zornCoord X.a (aMidOppIdx j) ∧
    zornCoord ((e6RootExp (aPullRoot j) t).1 X).a 7 = zornCoord X.a 7 ∧
    (∀ i : Fin 6, zornCoord ((e6RootExp (aPullRoot j) t).1 X).a ⟨1 + i.val, by omega⟩ =
      if i = j then zornCoord X.a ⟨1 + i.val, by omega⟩ - t * zornCoord X.a 7
      else zornCoord X.a ⟨1 + i.val, by omega⟩) := by
  have hb := d4_rootExp_preserves_blocks (d4_aPullRoot_lt24 j) t X
  have hc : (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (aPullRoot j)) 10 k == 0) &&
      (sparseVal (e6RootSparse (aPullRoot j)) 3 k ==
        if k.val = 3 + (aMidOppIdx j).val then -1 else 0))) = true := by decide
  have hc2 : (List.finRange 6).all (fun j => (List.finRange 6).all (fun i =>
      (List.finRange 27).all (fun k =>
        sparseVal (e6RootSparse (aPullRoot j)) ⟨4 + i.val, by omega⟩ k ==
          if i == j && k.val == 10 then -1 else 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc hc2
  refine ⟨hb.1, hb.2.1, hb.2.2.1, ?_, ?_, ?_⟩
  · rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    change h3ZornCoordinate ((e6RootExp (aPullRoot j) t).1 X) 3 =
      h3ZornCoordinate X 3 - t * h3ZornCoordinate X ⟨3 + (aMidOppIdx j).val, by omega⟩
    rw [h3ZornCoordinate_e6RootExp, Finset.sum_eq_single ⟨3 + (aMidOppIdx j).val, by omega⟩]
    · rw [(hc j _).2]; simp; ring
    · intro k _ hk; rw [(hc j k).2]
      have hk' : k.val ≠ 3 + (aMidOppIdx j).val := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    exact rootExp_coord_unchanged (aPullRoot j) 10 t X fun k => (hc j k).1
  · intro i
    rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
    have hidx : (⟨3 + (⟨1 + i.val, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
        ⟨4 + i.val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hidx, h3ZornCoordinate_e6RootExp]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single 10]
      · rw [hc2 i i 10, ← h3ZornCoord_a_eq X 7]; simp; ring
      · intro k _ hk; rw [hc2 i i k]
        have hk' : k.val ≠ 10 := fun h => hk (Fin.ext h)
        simp [hk']
      · intro h; exact absurd (Finset.mem_univ 10) h
    · have hs0 : ∑ k : Fin 27,
          (sparseVal (e6RootSparse (aPullRoot j)) ⟨4 + i.val, by omega⟩ k : ℝ) *
            h3ZornCoordinate X k = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hc2 j i k]
        simp [hij]
      rw [hs0, mul_zero, add_zero]
      simp [hij]

private theorem w12_preserves_a_bc (X : H3Zorn ℝ) :
    (X.a = 0 → (w12.1 X).a = 0) ∧
    (X.b = 0 → X.c = 0 → (w12.1 X).b = 0 ∧ (w12.1 X).c = 0) := by
  have hc1 : (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      if k.val < 3 ∨ 11 ≤ k.val then
        sparseVal w12Sparse ⟨3 + i.val, by omega⟩ k == 0
      else true)) = true := by decide
  have hc2 : (List.finRange 16).all (fun i => (List.finRange 11).all (fun k =>
      sparseVal w12Sparse ⟨11 + i.val, by omega⟩ ⟨k.val, by omega⟩ == 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc1 hc2
  refine ⟨fun ha => ?_, fun hb hc0 => ?_⟩
  · refine zorn_eq_of_zornCoord_eq fun l => ?_
    rw [← h3ZornCoord_a_eq, h3ZornCoordinate_of_toMatrix h3zornToMatrix_w12,
      (zornCoord_eq_zero_iff 0).mpr rfl l]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k.val < 3 ∨ 11 ≤ k.val
    · have hzm := hc1 l k
      simp only [hk, ↓reduceIte, beq_iff_eq] at hzm
      rw [hzm, Int.cast_zero, zero_mul]
    · have hne : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hne, h3ZornCoord_a_eq, ha, (zornCoord_eq_zero_iff 0).mpr rfl _, mul_zero]
  · have hyk : ∀ k : Fin 27, 11 ≤ k.val → h3ZornCoordinate X k = 0 := by
      intro k hk
      by_cases hk19 : k.val < 19
      · have hne : k = ⟨11 + (⟨k.val - 11, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hne, h3ZornCoord_b_eq, hb, (zornCoord_eq_zero_iff 0).mpr rfl]
      · have hne : k = ⟨19 + (⟨k.val - 19, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hne, h3ZornCoord_c_eq, hc0, (zornCoord_eq_zero_iff 0).mpr rfl]
    have hrow : ∀ i : Fin 16, h3ZornCoordinate (w12.1 X) ⟨11 + i.val, by omega⟩ = 0 := by
      intro i
      rw [h3ZornCoordinate_of_toMatrix h3zornToMatrix_w12]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k.val < 11
      · have hne : k = ⟨(⟨k.val, hk⟩ : Fin 11).val, by omega⟩ := Fin.ext rfl
        rw [hne, hc2 i ⟨k.val, hk⟩, Int.cast_zero, zero_mul]
      · rw [hyk k (by omega), mul_zero]
    constructor <;> refine zorn_eq_of_zornCoord_eq fun l => ?_
    · rw [← h3ZornCoord_b_eq, (zornCoord_eq_zero_iff 0).mpr rfl l]
      have hne : (⟨11 + l.val, by omega⟩ : Fin 27) = ⟨11 + (⟨l.val, by omega⟩ : Fin 16).val, by omega⟩ :=
        Fin.ext rfl
      rw [hne]
      exact hrow ⟨l.val, by omega⟩
    · rw [← h3ZornCoord_c_eq, (zornCoord_eq_zero_iff 0).mpr rfl l]
      have hne : (⟨19 + l.val, by omega⟩ : Fin 27) = ⟨11 + (⟨8 + l.val, by omega⟩ : Fin 16).val, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hne]
      exact hrow ⟨8 + l.val, by omega⟩

private theorem w23_preserves_ab_zero {X : H3Zorn ℝ} (ha : X.a = 0) (hb : X.b = 0) :
    (w23.1 X).b = 0 ∧ (w23.1 X).c = 0 := by
  have hc1 : (List.finRange 8).all (fun i => (List.finRange 27).all (fun k =>
      (if k.val < 11 ∨ 19 ≤ k.val then
        sparseVal w23Sparse ⟨11 + i.val, by omega⟩ k == 0
       else true) &&
      (if k.val < 3 ∨ 11 ≤ k.val then
        sparseVal w23Sparse ⟨19 + i.val, by omega⟩ k == 0
       else true))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true] at hc1
  constructor <;> refine zorn_eq_of_zornCoord_eq fun l => ?_
  · rw [← h3ZornCoord_b_eq, h3ZornCoordinate_of_toMatrix h3zornToMatrix_w23,
      (zornCoord_eq_zero_iff 0).mpr rfl l]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k.val < 11 ∨ 19 ≤ k.val
    · have hm := (hc1 l k).1
      simp only [hk, ↓reduceIte, beq_iff_eq] at hm
      rw [hm, Int.cast_zero, zero_mul]
    · have hne : k = ⟨11 + (⟨k.val - 11, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hne, h3ZornCoord_b_eq, hb, (zornCoord_eq_zero_iff 0).mpr rfl _, mul_zero]
  · rw [← h3ZornCoord_c_eq, h3ZornCoordinate_of_toMatrix h3zornToMatrix_w23,
      (zornCoord_eq_zero_iff 0).mpr rfl l]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k.val < 3 ∨ 11 ≤ k.val
    · have hm := (hc1 l k).2
      simp only [hk, ↓reduceIte, beq_iff_eq] at hm
      rw [hm, Int.cast_zero, zero_mul]
    · have hne : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hne, h3ZornCoord_a_eq, ha, (zornCoord_eq_zero_iff 0).mpr rfl _, mul_zero]

private theorem f4_clear_a (X : H3Zorn ℝ) (he : isRankOneIdem X) (hsum : X.α₁ + X.α₂ ≠ 0) :
    ∃ f ∈ e6F4InChevalley,
      (f.1 X).a = 0 ∧
      (f.1 X).α₁ + (f.1 X).α₂ = X.α₁ + X.α₂ ∧
      (f.1 X).α₃ = X.α₃ ∧
      (X.b = 0 → X.c = 0 → (f.1 X).b = 0 ∧ (f.1 X).c = 0) := by
  -- Sub-step 1: ensure (α₁ - α₂)^2 + 4 * a₀ * a₇ ≥ 0
  have hs1 : ∃ f₁ ∈ e6F4InChevalley,
      0 ≤ ((f₁.1 X).α₁ - (f₁.1 X).α₂) ^ 2 + 4 * zornCoord (f₁.1 X).a 0 * zornCoord (f₁.1 X).a 7 ∧
      (f₁.1 X).α₁ + (f₁.1 X).α₂ = X.α₁ + X.α₂ ∧
      (f₁.1 X).α₃ = X.α₃ ∧
      (X.b = 0 → X.c = 0 → (f₁.1 X).b = 0 ∧ (f₁.1 X).c = 0) := by
    by_cases hdisc : 0 ≤ (X.α₁ - X.α₂) ^ 2 + 4 * zornCoord X.a 0 * zornCoord X.a 7
    · exact ⟨1, e6F4InChevalley.one_mem, hdisc, rfl, rfl, fun hb hc0 => ⟨hb, hc0⟩⟩
    · have hlt : (X.α₁ - X.α₂) ^ 2 + 4 * zornCoord X.a 0 * zornCoord X.a 7 < 0 :=
        lt_of_not_ge hdisc
      have hnorm := (isRankOneIdem_norm_eq he).2.2.2
      rw [zorn_norm_zornCoord] at hnorm
      have hsne := neg_sum_neg_of_lt_cb hnorm hlt
      have hexj : ∃ j : Fin 6, zornCoord X.a (aMidOppIdx j) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have h1 := hcon 3; have h2 := hcon 4; have h3 := hcon 5
        have h4 := hcon 0; have h5 := hcon 1; have h6 := hcon 2
        dsimp [aMidOppIdx] at h1 h2 h3 h4 h5 h6
        exact hsne (by rw [h1, h2, h3, h4, h5, h6]; ring)
      obtain ⟨j, hj⟩ := hexj
      let t := -zornCoord X.a 7 / zornCoord X.a (aMidOppIdx j)
      let g := e6RootExp (aMidRoot j) t
      have hg_d4 : g ∈ d4Subgroup := Subgroup.subset_closure ⟨aMidRoot j, d4_aMidRoot_lt24 j, t, rfl⟩
      have hg_f4 : g ∈ e6F4InChevalley := d4Subgroup_le_f4InChevalley hg_d4
      obtain ⟨hd1, hd2, hd3, ha0, ha7, _⟩ := d4_aMidRoot_coords j t X
      have hb_blk := d4_rootExp_preserves_blocks (d4_aMidRoot_lt24 j) t X
      refine ⟨g, hg_f4, ?_, ?_, hd3, fun hb hc0 => ⟨hb_blk.2.2.2.2.1 hb, hb_blk.2.2.2.2.2 hc0⟩⟩
      · have h7z : zornCoord (g.1 X).a 7 = 0 := by
          rw [ha7]; dsimp [t]; field_simp [hj]; ring
        rw [h7z, mul_zero, add_zero]
        exact sq_nonneg _
      · rw [hd1, hd2]
  obtain ⟨f₁, hf₁, hdisc₁, hsum₁, h3₁, hbc₁⟩ := hs1
  let X₁ := f₁.1 X
  have he₁ : isRankOneIdem X₁ := f4InChevalley_preserves_isRankOneIdem hf₁ he
  -- Sub-step 2: kill a₀ to 0 while keeping a_mid unchanged
  have hs2 : ∃ f₂ ∈ e6F4InChevalley,
      zornCoord (f₂.1 X₁).a 0 = 0 ∧
      (f₂.1 X₁).α₁ + (f₂.1 X₁).α₂ = X₁.α₁ + X₁.α₂ ∧
      (f₂.1 X₁).α₃ = X₁.α₃ ∧
      (X₁.b = 0 → X₁.c = 0 → (f₂.1 X₁).b = 0 ∧ (f₂.1 X₁).c = 0) := by
    by_cases ha7 : zornCoord X₁.a 7 ≠ 0
    · have hdisc' : 0 ≤ (X₁.α₂ - X₁.α₁) ^ 2 + 4 * zornCoord X₁.a 7 * zornCoord X₁.a 0 := by
        nlinarith [hdisc₁]
      obtain ⟨t, ht⟩ := real_quad_root_cb ha7 hdisc'
      obtain ⟨_, _, _, ha0', _, _⟩ := f4Peirce_0_0_coords t X₁
      obtain ⟨hs01, hs3, hsbc⟩ := f4Peirce_0_preserves_blocks 0 t X₁
      exact ⟨f4PeirceExp 0 0 t, f4PeirceExp_mem_f4 0 0 t, ha0'.trans ht, hs01, hs3, hsbc⟩
    · push Not at ha7
      by_cases hα : X₁.α₂ - X₁.α₁ ≠ 0
      · let t := -zornCoord X₁.a 0 / (X₁.α₂ - X₁.α₁)
        obtain ⟨_, _, _, ha0', _, _⟩ := f4Peirce_0_0_coords t X₁
        obtain ⟨hs01, hs3, hsbc⟩ := f4Peirce_0_preserves_blocks 0 t X₁
        refine ⟨f4PeirceExp 0 0 t, f4PeirceExp_mem_f4 0 0 t, ?_, hs01, hs3, hsbc⟩
        rw [ha0', ha7, mul_zero, sub_zero]
        dsimp [t]; field_simp [hα]; ring
      · push Not at hα
        by_cases ha0 : zornCoord X₁.a 0 = 0
        · exact ⟨1, e6F4InChevalley.one_mem, ha0, rfl, rfl, fun hb hc0 => ⟨hb, hc0⟩⟩
        · let g := f4PeirceExp 0 0 1 * f4PeirceExp 0 7 1
          have hg_mem : g ∈ e6F4InChevalley :=
            e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 0 0 1) (f4PeirceExp_mem_f4 0 7 1)
          obtain ⟨p1, p2, p3, pa0, pa7, _⟩ := f4Peirce_0_7_coords 1 X₁
          obtain ⟨q01, q3, qbc⟩ := f4Peirce_0_preserves_blocks 7 1 X₁
          obtain ⟨_, _, _, r0, _, _⟩ := f4Peirce_0_0_coords 1 ((f4PeirceExp 0 7 1).1 X₁)
          obtain ⟨r01, r3, rbc⟩ := f4Peirce_0_preserves_blocks 0 1 ((f4PeirceExp 0 7 1).1 X₁)
          refine ⟨g, hg_mem, ?_, r01.trans q01, r3.trans q3, fun hb hc0 => ?_⟩
          · change zornCoord ((f4PeirceExp 0 0 1).1 ((f4PeirceExp 0 7 1).1 X₁)).a 0 = 0
            rw [r0, pa0, pa7, p2, p1]
            linarith [hα]
          · obtain ⟨hb1, hc1'⟩ := qbc hb hc0
            exact rbc hb1 hc1'
  obtain ⟨f₂, hf₂, ha0₂, hsum₂, h3₂, hbc₂⟩ := hs2
  let X₂ := f₂.1 X₁
  have he₂ : isRankOneIdem X₂ := f4InChevalley_preserves_isRankOneIdem hf₂ he₁
  -- Sub-step 3: kill a_mid (1..6) AND keep a₀ = 0
  have hs3 : ∃ f₃ ∈ e6F4InChevalley,
      zornCoord (f₃.1 X₂).a 0 = 0 ∧
      (∀ i : Fin 6, zornCoord (f₃.1 X₂).a ⟨1 + i.val, by omega⟩ = 0) ∧
      (f₃.1 X₂).α₁ + (f₃.1 X₂).α₂ = X₂.α₁ + X₂.α₂ ∧
      (f₃.1 X₂).α₃ = X₂.α₃ ∧
      (X₂.b = 0 → X₂.c = 0 → (f₃.1 X₂).b = 0 ∧ (f₃.1 X₂).c = 0) := by
    by_cases hmid : ∀ i : Fin 6, zornCoord X₂.a ⟨1 + i.val, by omega⟩ = 0
    · exact ⟨1, e6F4InChevalley.one_mem, ha0₂, hmid, rfl, rfl, fun hb hc0 => ⟨hb, hc0⟩⟩
    · push Not at hmid
      obtain ⟨i₀, hi₀⟩ := hmid
      -- First ensure a₇ ≠ 0
      have hs3a : ∃ g₁ ∈ e6F4InChevalley,
          zornCoord (g₁.1 X₂).a 7 ≠ 0 ∧
          (g₁.1 X₂).α₁ + (g₁.1 X₂).α₂ = X₂.α₁ + X₂.α₂ ∧
          (g₁.1 X₂).α₃ = X₂.α₃ ∧
          (X₂.b = 0 → X₂.c = 0 → (g₁.1 X₂).b = 0 ∧ (g₁.1 X₂).c = 0) := by
        by_cases ha7 : zornCoord X₂.a 7 ≠ 0
        · exact ⟨1, e6F4InChevalley.one_mem, ha7, rfl, rfl, fun hb hc0 => ⟨hb, hc0⟩⟩
        · push Not at ha7
          have hexopp : ∃ j : Fin 6, zornCoord X₂.a (aMidOppIdx j) ≠ 0 := by
            by_contra hcon; push Not at hcon
            have hopp : ∀ k : Fin 8, k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 →
                zornCoord X₂.a k = 0 := by
              intro k hk
              rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
              · exact hcon 3
              · exact hcon 4
              · exact hcon 5
              · exact hcon 0
              · exact hcon 1
              · exact hcon 2
            apply hi₀
            apply hopp
            fin_cases i₀ <;> decide
          obtain ⟨j, hj⟩ := hexopp
          let gp := e6RootExp (aPullRoot j) 1
          have hgp_f4 : gp ∈ e6F4InChevalley :=
            d4Subgroup_le_f4InChevalley (Subgroup.subset_closure ⟨aPullRoot j, d4_aPullRoot_lt24 j, 1, rfl⟩)
          obtain ⟨gd1, gd2, gd3, ga0, _, _⟩ := d4_aPullRoot_coords j 1 X₂
          have gblk := d4_rootExp_preserves_blocks (d4_aPullRoot_lt24 j) 1 X₂
          have ga0_ne : zornCoord (gp.1 X₂).a 0 ≠ 0 := by
            rw [ga0, ha0₂]; simpa using hj
          let Y := gp.1 X₂
          by_cases h1 : zornCoord ((f4PeirceExp 0 7 1).1 Y).a 7 ≠ 0
          · obtain ⟨p01, p3, pbc⟩ := f4Peirce_0_preserves_blocks 7 1 Y
            refine ⟨f4PeirceExp 0 7 1 * gp, e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 0 7 1) hgp_f4,
              h1, ?_, p3.trans gd3, fun hb hc0 => pbc (gblk.2.2.2.2.1 hb) (gblk.2.2.2.2.2 hc0)⟩
            change ((f4PeirceExp 0 7 1).1 Y).α₁ + ((f4PeirceExp 0 7 1).1 Y).α₂ = _
            rw [p01, gd1, gd2]
          · push Not at h1
            have hm1 : zornCoord ((f4PeirceExp 0 7 (-1)).1 Y).a 7 ≠ 0 := by
              obtain ⟨_, _, _, _, ha7p, _⟩ := f4Peirce_0_7_coords 1 Y
              obtain ⟨_, _, _, _, ha7m, _⟩ := f4Peirce_0_7_coords (-1) Y
              rw [ha7p] at h1
              rw [ha7m]
              intro hz
              apply ga0_ne
              linarith [h1, hz]
            obtain ⟨p01, p3, pbc⟩ := f4Peirce_0_preserves_blocks 7 (-1) Y
            refine ⟨f4PeirceExp 0 7 (-1) * gp, e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 0 7 (-1)) hgp_f4,
              hm1, ?_, p3.trans gd3, fun hb hc0 => pbc (gblk.2.2.2.2.1 hb) (gblk.2.2.2.2.2 hc0)⟩
            change ((f4PeirceExp 0 7 (-1)).1 Y).α₁ + ((f4PeirceExp 0 7 (-1)).1 Y).α₂ = _
            rw [p01, gd1, gd2]
      obtain ⟨g₁, hg₁, ha7', hsum', h3', hbc'⟩ := hs3a
      let Y := g₁.1 X₂
      have heY : isRankOneIdem Y := f4InChevalley_preserves_isRankOneIdem hg₁ he₂
      -- Apply the 6 pull roots to clear a₁..a₆ while preserving a₇ ≠ 0
      have hclear_step : ∀ (j : Fin 6) (Z : H3Zorn ℝ),
          zornCoord Z.a 7 ≠ 0 →
          ∃ g ∈ d4Subgroup,
            zornCoord (g.1 Z).a 7 = zornCoord Z.a 7 ∧
            zornCoord (g.1 Z).a ⟨1 + j.val, by omega⟩ = 0 ∧
            (∀ i : Fin 6, i ≠ j →
              zornCoord (g.1 Z).a ⟨1 + i.val, by omega⟩ = zornCoord Z.a ⟨1 + i.val, by omega⟩) := by
        intro j Z hz7
        let t := zornCoord Z.a ⟨1 + j.val, by omega⟩ / zornCoord Z.a 7
        refine ⟨e6RootExp (aPullRoot j) t, Subgroup.subset_closure ⟨aPullRoot j, d4_aPullRoot_lt24 j, t, rfl⟩, ?_⟩
        obtain ⟨_, _, _, _, ga7, gmid⟩ := d4_aPullRoot_coords j t Z
        refine ⟨ga7, ?_, fun i hij => ?_⟩
        · rw [gmid j]; simp only [↓reduceIte]; dsimp [t]; field_simp [hz7]; ring
        · rw [gmid i]; simp [hij]
      obtain ⟨p0, hp0, ha7_0, h0_0, ho_0⟩ := hclear_step 0 Y ha7'
      have ha7_0n : zornCoord (p0.1 Y).a 7 ≠ 0 := by rw [ha7_0]; exact ha7'
      obtain ⟨p1, hp1, ha7_1, h1_1, ho_1⟩ := hclear_step 1 (p0.1 Y) ha7_0n
      have ha7_1n : zornCoord (p1.1 (p0.1 Y)).a 7 ≠ 0 := by rw [ha7_1]; exact ha7_0n
      obtain ⟨p2, hp2, ha7_2, h2_2, ho_2⟩ := hclear_step 2 (p1.1 (p0.1 Y)) ha7_1n
      have ha7_2n : zornCoord (p2.1 (p1.1 (p0.1 Y))).a 7 ≠ 0 := by rw [ha7_2]; exact ha7_1n
      obtain ⟨p3, hp3, ha7_3, h3_3, ho_3⟩ := hclear_step 3 (p2.1 (p1.1 (p0.1 Y))) ha7_2n
      have ha7_3n : zornCoord (p3.1 (p2.1 (p1.1 (p0.1 Y)))).a 7 ≠ 0 := by rw [ha7_3]; exact ha7_2n
      obtain ⟨p4, hp4, ha7_4, h4_4, ho_4⟩ := hclear_step 4 (p3.1 (p2.1 (p1.1 (p0.1 Y)))) ha7_3n
      have ha7_4n : zornCoord (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y))))).a 7 ≠ 0 := by rw [ha7_4]; exact ha7_3n
      obtain ⟨p5, hp5, ha7_5, h5_5, ho_5⟩ := hclear_step 5 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y))))) ha7_4n
      let pd := p5 * p4 * p3 * p2 * p1 * p0
      have hpd_d4 : pd ∈ d4Subgroup :=
        d4Subgroup.mul_mem (d4Subgroup.mul_mem (d4Subgroup.mul_mem (d4Subgroup.mul_mem
          (d4Subgroup.mul_mem hp5 hp4) hp3) hp2) hp1) hp0
      have hpd_f4 : pd ∈ e6F4InChevalley := d4Subgroup_le_f4InChevalley hpd_d4
      let Z := pd.1 Y
      have hz0 : zornCoord Z.a 1 = 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).a ⟨1 + (0 : Fin 6).val, by omega⟩ = 0
        rw [ho_5 0 (by decide), ho_4 0 (by decide), ho_3 0 (by decide), ho_2 0 (by decide),
          ho_1 0 (by decide)]; exact h0_0
      have hz1 : zornCoord Z.a 2 = 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).a ⟨1 + (1 : Fin 6).val, by omega⟩ = 0
        rw [ho_5 1 (by decide), ho_4 1 (by decide), ho_3 1 (by decide), ho_2 1 (by decide)]; exact h1_1
      have hz2 : zornCoord Z.a 3 = 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).a ⟨1 + (2 : Fin 6).val, by omega⟩ = 0
        rw [ho_5 2 (by decide), ho_4 2 (by decide), ho_3 2 (by decide)]; exact h2_2
      have hz3 : zornCoord Z.a 4 = 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).a ⟨1 + (3 : Fin 6).val, by omega⟩ = 0
        rw [ho_5 3 (by decide), ho_4 3 (by decide)]; exact h3_3
      have hz4 : zornCoord Z.a 5 = 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).a ⟨1 + (4 : Fin 6).val, by omega⟩ = 0
        rw [ho_5 4 (by decide)]; exact h4_4
      have hz5 : zornCoord Z.a 6 = 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).a ⟨1 + (5 : Fin 6).val, by omega⟩ = 0
        exact h5_5
      have hZ_mid : ∀ i : Fin 6, zornCoord Z.a ⟨1 + i.val, by omega⟩ = 0 := by
        intro i
        fin_cases i
        · exact hz0
        · exact hz1
        · exact hz2
        · exact hz3
        · exact hz4
        · exact hz5
      have hZ_a7 : zornCoord Z.a 7 ≠ 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).a 7 ≠ 0
        rw [ha7_5]; exact ha7_4n
      have heZ : isRankOneIdem Z := f4InChevalley_preserves_isRankOneIdem hpd_f4 heY
      have hZ_norm := (isRankOneIdem_norm_eq heZ).2.2.2
      rw [zorn_norm_zornCoord, hz0, hz1, hz2, hz3, hz4, hz5] at hZ_norm
      have hdiscZ : 0 ≤ (Z.α₂ - Z.α₁) ^ 2 + 4 * zornCoord Z.a 7 * zornCoord Z.a 0 := by
        have h1 : Z.α₁ * Z.α₂ = zornCoord Z.a 0 * zornCoord Z.a 7 := by linarith [hZ_norm]
        nlinarith [sq_nonneg (Z.α₁ + Z.α₂), h1]
      obtain ⟨tz, htz⟩ := real_quad_root_cb hZ_a7 hdiscZ
      obtain ⟨_, _, _, za0, _, zmid⟩ := f4Peirce_0_0_coords tz Z
      obtain ⟨z01, z3, zbc⟩ := f4Peirce_0_preserves_blocks 0 tz Z
      obtain ⟨d1, d2, d3, da, db, dc⟩ := d4Subgroup_preserves_blocks hpd_d4 Y
      have hact : (f4PeirceExp 0 0 tz * pd * g₁).1 X₂ = (f4PeirceExp 0 0 tz).1 Z := rfl
      refine ⟨f4PeirceExp 0 0 tz * pd * g₁,
        e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 0 0 tz) hpd_f4) hg₁,
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [hact]; exact za0.trans htz
      · intro i; rw [hact, zmid i]; exact hZ_mid i
      · rw [hact, z01, d1, d2]; exact hsum'
      · rw [hact, z3, d3]; exact h3'
      · intro hb hc0
        rw [hact]
        obtain ⟨hb1, hc1'⟩ := hbc' hb hc0
        exact zbc (db.mpr hb1) (dc.mpr hc1')
  obtain ⟨f₃, hf₃, ha0₃, hamid₃, hsum₃, h3₃, hbc₃⟩ := hs3
  let X₃ := f₃.1 X₂
  have he₃ : isRankOneIdem X₃ := f4InChevalley_preserves_isRankOneIdem hf₃ he₂
  -- Sub-step 4: kill a₇ using α₁ ≠ α₂
  have hm1 : zornCoord X₃.a 1 = 0 := hamid₃ 0
  have hm2 : zornCoord X₃.a 2 = 0 := hamid₃ 1
  have hm3 : zornCoord X₃.a 3 = 0 := hamid₃ 2
  have hm4 : zornCoord X₃.a 4 = 0 := hamid₃ 3
  have hm5 : zornCoord X₃.a 5 = 0 := hamid₃ 4
  have hm6 : zornCoord X₃.a 6 = 0 := hamid₃ 5
  have hX3_norm := (isRankOneIdem_norm_eq he₃).2.2.2
  rw [zorn_norm_zornCoord, ha0₃, hm1, hm2, hm3, hm4, hm5, hm6] at hX3_norm
  have hX3_mul : X₃.α₁ * X₃.α₂ = 0 := by linarith [hX3_norm]
  have hX3_sum : X₃.α₁ + X₃.α₂ ≠ 0 := by rw [hsum₃, hsum₂, hsum₁]; exact hsum
  have hX3_ne : X₃.α₂ - X₃.α₁ ≠ 0 :=
    sub_ne_zero.mpr (sub_ne_of_mul_zero_sum_ne_cb hX3_mul hX3_sum).symm
  let t₄ := -zornCoord X₃.a 7 / (X₃.α₂ - X₃.α₁)
  obtain ⟨_, _, _, ha0₄, ha7₄, hamid₄⟩ := f4Peirce_0_7_coords t₄ X₃
  obtain ⟨h01₄, h3₄, hbc₄⟩ := f4Peirce_0_preserves_blocks 7 t₄ X₃
  refine ⟨f4PeirceExp 0 7 t₄ * f₃ * f₂ * f₁,
    e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem
      (f4PeirceExp_mem_f4 0 7 t₄) hf₃) hf₂) hf₁,
    ?_, ?_, ?_, ?_⟩
  · refine zorn_eq_of_zornCoord_eq fun k => ?_
    rw [(zornCoord_eq_zero_iff 0).mpr rfl k]
    fin_cases k
    · change zornCoord ((f4PeirceExp 0 7 t₄).1 X₃).a 0 = 0
      rw [ha0₄, ha0₃]
    · exact (hamid₄ 0).trans (hamid₃ 0)
    · exact (hamid₄ 1).trans (hamid₃ 1)
    · exact (hamid₄ 2).trans (hamid₃ 2)
    · exact (hamid₄ 3).trans (hamid₃ 3)
    · exact (hamid₄ 4).trans (hamid₃ 4)
    · exact (hamid₄ 5).trans (hamid₃ 5)
    · change zornCoord ((f4PeirceExp 0 7 t₄).1 X₃).a 7 = 0
      rw [ha7₄, ha0₃, mul_zero, sub_zero]
      dsimp [t₄]; field_simp [hX3_ne]; ring
  · change ((f4PeirceExp 0 7 t₄).1 X₃).α₁ + ((f4PeirceExp 0 7 t₄).1 X₃).α₂ = _
    rw [h01₄, hsum₃, hsum₂, hsum₁]
  · change ((f4PeirceExp 0 7 t₄).1 X₃).α₃ = _
    rw [h3₄, h3₃, h3₂, h3₁]
  · intro hb hc0
    obtain ⟨hb1, hc1'⟩ := hbc₁ hb hc0
    obtain ⟨hb2, hc2'⟩ := hbc₂ hb1 hc1'
    obtain ⟨hb3, hc3'⟩ := hbc₃ hb2 hc2'
    exact hbc₄ hb3 hc3'

theorem f4_reduce_idempotent_to_diag1 (e : H3Zorn ℝ) (he : isRankOneIdem e) :
    ∃ f ∈ e6F4InChevalley, f.1 e = h3_diag₁ := by
  have hmul_act : ∀ (g₁ g₂ : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (g₁ * g₂).1 Z = g₁.1 (g₂.1 Z) := fun _ _ _ => rfl
  -- Step 1: get α₁ + α₂ ≠ 0
  have hs0 : ∃ f₀ ∈ e6F4InChevalley, (f₀.1 e).α₁ + (f₀.1 e).α₂ ≠ 0 := by
    by_cases h12 : e.α₁ + e.α₂ ≠ 0
    · exact ⟨1, e6F4InChevalley.one_mem, h12⟩
    · by_cases h13 : e.α₁ + e.α₃ ≠ 0
      · obtain ⟨d1, d2, _, _, _, _, _⟩ := w23_coords e
        exact ⟨w23, w23_mem_f4, by rw [d1, d2]; exact h13⟩
      · obtain ⟨d1, d2, _⟩ := w31_diag_coords e
        have h23 : e.α₂ + e.α₃ ≠ 0 := by
          have htr := he.2.1
          change e.α₁ + e.α₂ + e.α₃ = 1 at htr
          push Not at h12 h13
          linarith [htr, h12, h13]
        exact ⟨w31, w31_mem_f4, by rw [d1, d2]; intro hz; apply h23; linarith⟩
  obtain ⟨f₀, hf₀, hsum₀⟩ := hs0
  let e₁ := f₀.1 e
  have he₁ : isRankOneIdem e₁ := f4InChevalley_preserves_isRankOneIdem hf₀ he
  -- Step 2: clear a
  obtain ⟨f₁, hf₁, ha₁, hsum₁, _, _⟩ := f4_clear_a e₁ he₁ hsum₀
  let e₂ := f₁.1 e₁
  have he₂ : isRankOneIdem e₂ := f4InChevalley_preserves_isRankOneIdem hf₁ he₁
  -- Step 3: ensure α₁ ≠ 0 and α₂ = 0 while preserving a = 0
  have ha2_mul : e₂.α₁ * e₂.α₂ = 0 := by
    have hn := (isRankOneIdem_norm_eq he₂).2.2.2
    rw [ha₁, show (0 : ZornVectorMatrix ℝ) = ZornVectorMatrix.zero from rfl,
      ZornVectorMatrix.norm_zero] at hn
    exact hn
  have hs2 : ∃ f₂ ∈ e6F4InChevalley, (f₂.1 e₂).a = 0 ∧ (f₂.1 e₂).α₁ ≠ 0 ∧ (f₂.1 e₂).α₂ = 0 := by
    by_cases hα1 : e₂.α₁ = 0
    · obtain ⟨d1, d2, _⟩ := w12_diag_coords e₂
      have ha_w := (w12_preserves_a_bc e₂).1 ha₁
      have hα2 : e₂.α₂ ≠ 0 := by
        rw [hα1, zero_add] at hsum₁
        rw [hsum₁]
        exact hsum₀
      exact ⟨w12, w12_mem_f4, ha_w, by rw [d1]; exact hα2, by rw [d2, hα1]⟩
    · have hα2 : e₂.α₂ = 0 := (mul_eq_zero.mp ha2_mul).resolve_left hα1
      exact ⟨1, e6F4InChevalley.one_mem, ha₁, hα1, hα2⟩
  obtain ⟨f₂, hf₂, ha₂, hα1₂, hα2₂⟩ := hs2
  let e₃ := f₂.1 e₂
  have he₃ : isRankOneIdem e₃ := f4InChevalley_preserves_isRankOneIdem hf₂ he₂
  -- Step 4: from adjointQuad e₃ = 0, a = 0 and α₁ ≠ 0 imply b = 0
  have hb₃ : e₃.b = 0 := by
    have hadj_b := congrArg H3Zorn.b he₃.2.2
    change ZornVectorMatrix.sub (ZornVectorMatrix.mul (ZornVectorMatrix.conj e₃.a)
      (ZornVectorMatrix.conj e₃.c)) (ZornVectorMatrix.smul e₃.α₁ e₃.b) = ZornVectorMatrix.zero at hadj_b
    rw [ha₂, show (0 : ZornVectorMatrix ℝ) = ZornVectorMatrix.zero from rfl,
      ZornVectorMatrix.conj_zero, ZornVectorMatrix.zero_mul] at hadj_b
    refine zorn_eq_of_zornCoord_eq fun i => ?_
    rw [(zornCoord_eq_zero_iff 0).mpr rfl i]
    have hi := congrArg (fun z : ZornVectorMatrix ℝ => zornCoord z i) hadj_b
    have hsm : e₃.α₁ * zornCoord e₃.b i = 0 := by
      fin_cases i <;>
        (dsimp only [zornCoord]
         simp [ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg,
           ZornVectorMatrix.zero, ZornVectorMatrix.smul, zornCoord] at hi
         rcases hi with h | h <;> simp [h])
    exact (mul_eq_zero.mp hsm).resolve_left hα1₂
  -- Step 5: swap 2 ↔ 3 via w23 so b' = 0, c' = 0, α₃' = 0
  let e₄ := w23.1 e₃
  have he₄ : isRankOneIdem e₄ := f4InChevalley_preserves_isRankOneIdem w23_mem_f4 he₃
  obtain ⟨hb₄, hc₄⟩ := w23_preserves_ab_zero ha₂ hb₃
  obtain ⟨_, _, hα3₄, _, _, _, _⟩ := w23_coords e₃
  have hα3₄_zero : e₄.α₃ = 0 := by change (w23.1 e₃).α₃ = 0; rw [hα3₄, hα2₂]
  have hsum₄ : e₄.α₁ + e₄.α₂ ≠ 0 := by
    have htr := he₄.2.1
    change e₄.α₁ + e₄.α₂ + e₄.α₃ = 1 at htr
    rw [hα3₄_zero, add_zero] at htr
    rw [htr]; norm_num
  -- Step 6: clear a while preserving b = 0, c = 0, α₃ = 0
  obtain ⟨f₅, hf₅, ha₅, _, hα3₅, hbc₅⟩ := f4_clear_a e₄ he₄ hsum₄
  let e₅ := f₅.1 e₄
  have he₅ : isRankOneIdem e₅ := f4InChevalley_preserves_isRankOneIdem hf₅ he₄
  obtain ⟨hb₅, hc₅⟩ := hbc₅ hb₄ hc₄
  have hα3₅_zero : e₅.α₃ = 0 := hα3₅.trans hα3₄_zero
  -- Step 7: swap 1 ↔ 2 if α₁ = 0 to land on h3_diag₁
  have hsum₅ : e₅.α₁ + e₅.α₂ = 1 := by
    have htr := he₅.2.1
    change e₅.α₁ + e₅.α₂ + e₅.α₃ = 1 at htr
    rw [hα3₅_zero, add_zero] at htr
    exact htr
  have hmul₅ : e₅.α₁ * e₅.α₂ = 0 := by
    have hn := (isRankOneIdem_norm_eq he₅).2.2.2
    rw [ha₅, show (0 : ZornVectorMatrix ℝ) = ZornVectorMatrix.zero from rfl,
      ZornVectorMatrix.norm_zero] at hn
    exact hn
  have hact1 : (f₁ * f₀).1 e = e₂ := rfl
  have hact2 : (f₂ * (f₁ * f₀)).1 e = e₃ := by rw [hmul_act, hact1]
  have hact3 : (w23 * (f₂ * (f₁ * f₀))).1 e = e₄ := by rw [hmul_act, hact2]
  have hact4 : (f₅ * (w23 * (f₂ * (f₁ * f₀)))).1 e = e₅ := by rw [hmul_act, hact3]
  obtain ⟨g_all, hg_all, hg_act⟩ : ∃ g ∈ e6F4InChevalley, g.1 e = e₅ :=
    ⟨f₅ * (w23 * (f₂ * (f₁ * f₀))),
      e6F4InChevalley.mul_mem hf₅ (e6F4InChevalley.mul_mem w23_mem_f4
        (e6F4InChevalley.mul_mem hf₂ (e6F4InChevalley.mul_mem hf₁ hf₀))),
      hact4⟩
  by_cases hα1₅ : e₅.α₁ = 0
  · refine ⟨w12 * g_all, e6F4InChevalley.mul_mem w12_mem_f4 hg_all, ?_⟩
    rw [hmul_act, hg_act]
    obtain ⟨d1, d2, d3⟩ := w12_diag_coords e₅
    have ha6 := (w12_preserves_a_bc e₅).1 ha₅
    obtain ⟨hb6, hc6⟩ := (w12_preserves_a_bc e₅).2 hb₅ hc₅
    have hα2₅ : e₅.α₂ = 1 := by rw [hα1₅, zero_add] at hsum₅; exact hsum₅
    apply ext_h3
    · rw [d1, hα2₅]; rfl
    · rw [d2, hα1₅]; rfl
    · rw [d3, hα3₅_zero]; rfl
    · exact ha6
    · exact hb6
    · exact hc6
  · refine ⟨g_all, hg_all, ?_⟩
    rw [hg_act]
    have hα2₅ : e₅.α₂ = 0 := (mul_eq_zero.mp hmul₅).resolve_left hα1₅
    have hα1₅_one : e₅.α₁ = 1 := by rw [hα2₅, add_zero] at hsum₅; exact hsum₅
    apply ext_h3
    · rw [hα1₅_one]; rfl
    · rw [hα2₅]; rfl
    · rw [hα3₅_zero]; rfl
    · exact ha₅
    · exact hb₅
    · exact hc₅

/-- **Chevalley `E₆(6)` Transitivity on Rank-1 Primitive Idempotents**:
any two rank-1 idempotents (`e * e = e ∧ linearTrace e = 1 ∧ adjointQuad e = 0`)
are conjugate under `e6ChevalleySubgroup`. -/
theorem e6ChevalleySubgroup_transitive_rankOneIdempotent (e₁ e₂ : H3Zorn ℝ)
    (he₁ : isRankOneIdem e₁) (he₂ : isRankOneIdem e₂) :
    ∃ g ∈ e6ChevalleySubgroup, g.1 e₁ = e₂ := by
  obtain ⟨f₁, hf₁, h1⟩ := f4_reduce_idempotent_to_diag1 e₁ he₁
  obtain ⟨f₂, hf₂, h2⟩ := f4_reduce_idempotent_to_diag1 e₂ he₂
  refine ⟨f₂⁻¹ * f₁, e6ChevalleySubgroup.mul_mem (e6ChevalleySubgroup.inv_mem hf₂.1) hf₁.1, ?_⟩
  change f₂.1.symm (f₁.1 e₁) = e₂
  rw [h1, ← h2]
  exact f₂.1.symm_apply_apply e₂

/-! #### Step B2: Stabilizer of `h3_diag₁` acts transitively on orthogonal rank-1 idempotents -/

private theorem h3_diag₁_mul_eq_cb (X : H3Zorn ℝ) :
    h3_diag₁ * X =
      { α₁ := X.α₁, α₂ := 0, α₃ := 0
        a := (1 / 2 : ℝ) • X.a, b := 0, c := (1 / 2 : ℝ) • X.c } := by
  change candidateJordanMul h3_diag₁ X = _
  rw [candidateJordanMul_trace_formula]
  have hcp : H3Zorn.crossProduct h3_diag₁ X =
      { α₁ := 0, α₂ := X.α₃, α₃ := X.α₂, a := 0, b := -X.b, c := 0 } := by
    change H3Zorn.crossProduct (diagCartan 1 0 0) X = _
    rw [crossProduct_diagCartan_left]
    apply ext_h3
    · ring
    · ring
    · ring
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg]
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
  rw [hcp]
  apply ext_h3
  · simp [h3_diag₁, linearTrace, add_readback, sub_readback, smul_readback, one_readback]; ring
  · simp [h3_diag₁, linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · simp [h3_diag₁, linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · ext i <;> simp [h3_diag₁, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · ext i <;> simp [h3_diag₁, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · ext i <;> simp [h3_diag₁, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]

private theorem zorn_eq_zero_of_half_smul_eq_zero_cb {x : ZornVectorMatrix ℝ}
    (h : (1 / 2 : ℝ) • x = 0) : x = 0 := by
  have h2 := congrArg (fun z : ZornVectorMatrix ℝ => (2 : ℝ) • z) h
  rw [smul_zero, smul_smul] at h2
  norm_num at h2
  exact h2

private theorem eq_J23_of_diag1_mul_zero_cb {X : H3Zorn ℝ} (hm : h3_diag₁ * X = 0) :
    X.α₁ = 0 ∧ X.a = 0 ∧ X.c = 0 := by
  rw [h3_diag₁_mul_eq_cb] at hm
  refine ⟨congrArg H3Zorn.α₁ hm,
    zorn_eq_zero_of_half_smul_eq_zero_cb (congrArg H3Zorn.a hm),
    zorn_eq_zero_of_half_smul_eq_zero_cb (congrArg H3Zorn.c hm)⟩

private theorem f4Peirce_1_0_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((f4PeirceExp 1 0 t).1 X).α₁ = X.α₁ ∧
    ((f4PeirceExp 1 0 t).1 X).α₂ = X.α₂ + t * zornCoord X.b 7 ∧
    ((f4PeirceExp 1 0 t).1 X).α₃ = X.α₃ - t * zornCoord X.b 7 ∧
    zornCoord ((f4PeirceExp 1 0 t).1 X).b 0 =
      zornCoord X.b 0 + t * (X.α₃ - X.α₂) - t ^ 2 * zornCoord X.b 7 ∧
    zornCoord ((f4PeirceExp 1 0 t).1 X).b 7 = zornCoord X.b 7 ∧
    (∀ k : Fin 6, zornCoord ((f4PeirceExp 1 0 t).1 X).b ⟨1 + k.val, by omega⟩ =
      zornCoord X.b ⟨1 + k.val, by omega⟩) := by
  have hc1 : (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 1 0)) 0 k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 1 0)) 0 k == 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 1 0)) 1 k -
        sparseVal (e6RootSparse (f4NegIdx 1 0)) 1 k == if k.val = 18 then 1 else 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 1 0)) 2 k -
        sparseVal (e6RootSparse (f4NegIdx 1 0)) 2 k == if k.val = 18 then -1 else 0)) = true := by decide
  have hc2 : (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 1 0)) 11 k -
        sparseVal (e6RootSparse (f4NegIdx 1 0)) 11 k ==
          if k.val = 2 then 1 else if k.val = 1 then -1 else 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 0)) (e6RootSparse (f4NegIdx 1 0))) 11 k ==
        if k.val = 18 then 1 else 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 1 0)) 18 k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 1 0)) 18 k == 0)) = true := by decide
  have hc3 : (List.finRange 27).all (fun k =>
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 0)) (e6RootSparse (f4NegIdx 1 0))) 0 k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 0)) (e6RootSparse (f4NegIdx 1 0))) 1 k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 0)) (e6RootSparse (f4NegIdx 1 0))) 2 k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 0)) (e6RootSparse (f4NegIdx 1 0))) 18 k == 0)) =
      true := by decide
  have hc4 : (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 1 0)) ⟨12 + i.val, by omega⟩ k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 1 0)) ⟨12 + i.val, by omega⟩ k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 0)) (e6RootSparse (f4NegIdx 1 0)))
        ⟨12 + i.val, by omega⟩ k == 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc1 hc2 hc3 hc4
  have hb7eq : h3ZornCoordinate X 18 = zornCoord X.b 7 := (h3ZornCoord_b_eq X 7).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((f4PeirceExp 1 0 t).1 X) 0 = h3ZornCoordinate X 0
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · ring
    · intro k _; rw [(hc3 k).1.1.1]; simp
    · intro k _; rw [(hc1 k).1.1.1, (hc1 k).1.1.2]; simp
  · change h3ZornCoordinate ((f4PeirceExp 1 0 t).1 X) 1 = _
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_single 18, Finset.sum_eq_zero]
    · rw [(hc1 18).1.2]; simp; rw [hb7eq]; rfl
    · intro k _; rw [(hc3 k).1.1.2]; simp
    · intro k _ hk; rw [(hc1 k).1.2]; have hk' : k.val ≠ 18 := fun h => hk (Fin.ext h); simp [hk']
    · intro h; exact absurd (Finset.mem_univ 18) h
  · change h3ZornCoordinate ((f4PeirceExp 1 0 t).1 X) 2 = _
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_single 18, Finset.sum_eq_zero]
    · rw [(hc1 18).2]; simp; rw [hb7eq]
      change X.α₃ + -(t * zornCoord X.b 7) = X.α₃ - t * zornCoord X.b 7
      ring
    · intro k _; rw [(hc3 k).1.2]; simp
    · intro k _ hk; rw [(hc1 k).2]; have hk' : k.val ≠ 18 := fun h => hk (Fin.ext h); simp [hk']
    · intro h; exact absurd (Finset.mem_univ 18) h
  · rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((f4PeirceExp 1 0 t).1 X) 11 =
      h3ZornCoordinate X 11 + t * (h3ZornCoordinate X 2 - h3ZornCoordinate X 1) -
        t ^ 2 * h3ZornCoordinate X 18
    rw [h3ZornCoordinate_f4PeirceExp]
    have hs1 : ∑ k : Fin 27,
        ((sparseVal (e6RootSparse (f4PosIdx 1 0)) 11 k -
          sparseVal (e6RootSparse (f4NegIdx 1 0)) 11 k : ℤ) : ℝ) * h3ZornCoordinate X k =
        h3ZornCoordinate X 2 - h3ZornCoordinate X 1 := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun k : Fin 27 => k = 1 ∨ k = 2)]
      have hz : ∑ k ∈ Finset.univ.filter (fun k : Fin 27 => ¬(k = 1 ∨ k = 2)),
          ((sparseVal (e6RootSparse (f4PosIdx 1 0)) 11 k -
            sparseVal (e6RootSparse (f4NegIdx 1 0)) 11 k : ℤ) : ℝ) * h3ZornCoordinate X k = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hnk := (Finset.mem_filter.mp hk).2
        push Not at hnk
        have hk1 : k.val ≠ 1 := fun h => hnk.1 (Fin.ext h)
        have hk2 : k.val ≠ 2 := fun h => hnk.2 (Fin.ext h)
        rw [(hc2 k).1.1.1]; simp [hk1, hk2]
      rw [hz, add_zero]
      have hf : Finset.univ.filter (fun k : Fin 27 => k = 1 ∨ k = 2) = {1, 2} := by decide
      rw [hf, Finset.sum_insert (by decide), Finset.sum_singleton, (hc2 1).1.1.1, (hc2 2).1.1.1]
      simp; ring
    have hs2 : ∑ l : Fin 27,
        (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 0)) (e6RootSparse (f4NegIdx 1 0))) 11 l : ℝ) *
          h3ZornCoordinate X l = h3ZornCoordinate X 18 := by
      rw [Finset.sum_eq_single 18]
      · rw [(hc2 18).1.1.2]; simp
      · intro k _ hk; rw [(hc2 k).1.1.2]; have hk' : k.val ≠ 18 := fun h => hk (Fin.ext h); simp [hk']
      · intro h; exact absurd (Finset.mem_univ 18) h
    rw [hs1, hs2]
  · rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((f4PeirceExp 1 0 t).1 X) 18 = h3ZornCoordinate X 18
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · ring
    · intro k _; rw [(hc3 k).2]; simp
    · intro k _; rw [(hc2 k).1.2, (hc2 k).2]; simp
  · intro i
    rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    have hidx : (⟨11 + (⟨1 + i.val, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
        ⟨12 + i.val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hidx, h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · ring
    · intro k _; rw [(hc4 i k).2]; simp
    · intro k _; rw [(hc4 i k).1.1, (hc4 i k).1.2]; simp

private theorem f4Peirce_1_7_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((f4PeirceExp 1 7 t).1 X).α₁ = X.α₁ ∧
    ((f4PeirceExp 1 7 t).1 X).α₂ = X.α₂ + t * zornCoord X.b 0 ∧
    ((f4PeirceExp 1 7 t).1 X).α₃ = X.α₃ - t * zornCoord X.b 0 ∧
    zornCoord ((f4PeirceExp 1 7 t).1 X).b 0 = zornCoord X.b 0 ∧
    zornCoord ((f4PeirceExp 1 7 t).1 X).b 7 =
      zornCoord X.b 7 + t * (X.α₃ - X.α₂) - t ^ 2 * zornCoord X.b 0 ∧
    (∀ k : Fin 6, zornCoord ((f4PeirceExp 1 7 t).1 X).b ⟨1 + k.val, by omega⟩ =
      zornCoord X.b ⟨1 + k.val, by omega⟩) := by
  have hc1 : (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 1 7)) 0 k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 1 7)) 0 k == 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 1 7)) 1 k -
        sparseVal (e6RootSparse (f4NegIdx 1 7)) 1 k == if k.val = 11 then 1 else 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 1 7)) 2 k -
        sparseVal (e6RootSparse (f4NegIdx 1 7)) 2 k == if k.val = 11 then -1 else 0)) = true := by decide
  have hc2 : (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 1 7)) 18 k -
        sparseVal (e6RootSparse (f4NegIdx 1 7)) 18 k ==
          if k.val = 2 then 1 else if k.val = 1 then -1 else 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 7)) (e6RootSparse (f4NegIdx 1 7))) 18 k ==
        if k.val = 11 then 1 else 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 1 7)) 11 k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 1 7)) 11 k == 0)) = true := by decide
  have hc3 : (List.finRange 27).all (fun k =>
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 7)) (e6RootSparse (f4NegIdx 1 7))) 0 k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 7)) (e6RootSparse (f4NegIdx 1 7))) 1 k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 7)) (e6RootSparse (f4NegIdx 1 7))) 2 k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 7)) (e6RootSparse (f4NegIdx 1 7))) 11 k == 0)) =
      true := by decide
  have hc4 : (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 1 7)) ⟨12 + i.val, by omega⟩ k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 1 7)) ⟨12 + i.val, by omega⟩ k == 0) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 7)) (e6RootSparse (f4NegIdx 1 7)))
        ⟨12 + i.val, by omega⟩ k == 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc1 hc2 hc3 hc4
  have hb0eq : h3ZornCoordinate X 11 = zornCoord X.b 0 := (h3ZornCoord_b_eq X 0).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change h3ZornCoordinate ((f4PeirceExp 1 7 t).1 X) 0 = h3ZornCoordinate X 0
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · ring
    · intro k _; rw [(hc3 k).1.1.1]; simp
    · intro k _; rw [(hc1 k).1.1.1, (hc1 k).1.1.2]; simp
  · change h3ZornCoordinate ((f4PeirceExp 1 7 t).1 X) 1 = _
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_single 11, Finset.sum_eq_zero]
    · rw [(hc1 11).1.2]; simp; rw [hb0eq]; rfl
    · intro k _; rw [(hc3 k).1.1.2]; simp
    · intro k _ hk; rw [(hc1 k).1.2]; have hk' : k.val ≠ 11 := fun h => hk (Fin.ext h); simp [hk']
    · intro h; exact absurd (Finset.mem_univ 11) h
  · change h3ZornCoordinate ((f4PeirceExp 1 7 t).1 X) 2 = _
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_single 11, Finset.sum_eq_zero]
    · rw [(hc1 11).2]; simp; rw [hb0eq]
      change X.α₃ + -(t * zornCoord X.b 0) = X.α₃ - t * zornCoord X.b 0
      ring
    · intro k _; rw [(hc3 k).1.2]; simp
    · intro k _ hk; rw [(hc1 k).2]; have hk' : k.val ≠ 11 := fun h => hk (Fin.ext h); simp [hk']
    · intro h; exact absurd (Finset.mem_univ 11) h
  · rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((f4PeirceExp 1 7 t).1 X) 11 = h3ZornCoordinate X 11
    rw [h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · ring
    · intro k _; rw [(hc3 k).2]; simp
    · intro k _; rw [(hc2 k).1.2, (hc2 k).2]; simp
  · rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((f4PeirceExp 1 7 t).1 X) 18 =
      h3ZornCoordinate X 18 + t * (h3ZornCoordinate X 2 - h3ZornCoordinate X 1) -
        t ^ 2 * h3ZornCoordinate X 11
    rw [h3ZornCoordinate_f4PeirceExp]
    have hs1 : ∑ k : Fin 27,
        ((sparseVal (e6RootSparse (f4PosIdx 1 7)) 18 k -
          sparseVal (e6RootSparse (f4NegIdx 1 7)) 18 k : ℤ) : ℝ) * h3ZornCoordinate X k =
        h3ZornCoordinate X 2 - h3ZornCoordinate X 1 := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun k : Fin 27 => k = 1 ∨ k = 2)]
      have hz : ∑ k ∈ Finset.univ.filter (fun k : Fin 27 => ¬(k = 1 ∨ k = 2)),
          ((sparseVal (e6RootSparse (f4PosIdx 1 7)) 18 k -
            sparseVal (e6RootSparse (f4NegIdx 1 7)) 18 k : ℤ) : ℝ) * h3ZornCoordinate X k = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hnk := (Finset.mem_filter.mp hk).2
        push Not at hnk
        have hk1 : k.val ≠ 1 := fun h => hnk.1 (Fin.ext h)
        have hk2 : k.val ≠ 2 := fun h => hnk.2 (Fin.ext h)
        rw [(hc2 k).1.1.1]; simp [hk1, hk2]
      rw [hz, add_zero]
      have hf : Finset.univ.filter (fun k : Fin 27 => k = 1 ∨ k = 2) = {1, 2} := by decide
      rw [hf, Finset.sum_insert (by decide), Finset.sum_singleton, (hc2 1).1.1.1, (hc2 2).1.1.1]
      simp; ring
    have hs2 : ∑ l : Fin 27,
        (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 7)) (e6RootSparse (f4NegIdx 1 7))) 18 l : ℝ) *
          h3ZornCoordinate X l = h3ZornCoordinate X 11 := by
      rw [Finset.sum_eq_single 11]
      · rw [(hc2 11).1.1.2]; simp
      · intro k _ hk; rw [(hc2 k).1.1.2]; have hk' : k.val ≠ 11 := fun h => hk (Fin.ext h); simp [hk']
      · intro h; exact absurd (Finset.mem_univ 11) h
    rw [hs1, hs2]
  · intro i
    rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    have hidx : (⟨11 + (⟨1 + i.val, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
        ⟨12 + i.val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hidx, h3ZornCoordinate_f4PeirceExp, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · ring
    · intro k _; rw [(hc4 i k).2]; simp
    · intro k _; rw [(hc4 i k).1.1, (hc4 i k).1.2]; simp

private theorem f4Peirce_1_preserves_blocks (j : Fin 8) (t : ℝ) (X : H3Zorn ℝ) :
    ((f4PeirceExp 1 j t).1 X).α₁ = X.α₁ ∧
    ((f4PeirceExp 1 j t).1 X).α₂ + ((f4PeirceExp 1 j t).1 X).α₃ = X.α₂ + X.α₃ ∧
    (X.a = 0 → X.c = 0 → ((f4PeirceExp 1 j t).1 X).a = 0 ∧ ((f4PeirceExp 1 j t).1 X).c = 0) := by
  have hc1 : (List.finRange 8).all (fun j => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (f4PosIdx 1 j)) 0 k == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 1 j)) 0 k == 0) &&
      (sparseVal (e6RootSparse (f4PosIdx 1 j)) 1 k +
        sparseVal (e6RootSparse (f4PosIdx 1 j)) 2 k ==
        sparseVal (e6RootSparse (f4NegIdx 1 j)) 1 k +
        sparseVal (e6RootSparse (f4NegIdx 1 j)) 2 k) &&
      (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 1 k +
        sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 2 k == 0))) =
      true := by decide
  have hc2 : (List.finRange 8).all (fun j => (List.finRange 8).all (fun r =>
      (List.finRange 27).all (fun k =>
        if k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19) then
          (sparseVal (e6RootSparse (f4PosIdx 1 j)) ⟨3 + r.val, by omega⟩ k == 0) &&
          (sparseVal (e6RootSparse (f4NegIdx 1 j)) ⟨3 + r.val, by omega⟩ k == 0) &&
          (sparseVal (e6RootSparse (f4PosIdx 1 j)) ⟨19 + r.val, by omega⟩ k == 0) &&
          (sparseVal (e6RootSparse (f4NegIdx 1 j)) ⟨19 + r.val, by omega⟩ k == 0)
        else true))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc1 hc2
  have hzero_ac : ∀ (r : Fin 72) (s : ℝ) (Y : H3Zorn ℝ),
      (∀ (i : Fin 8) (k : Fin 27), k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19) →
        sparseVal (e6RootSparse r) ⟨3 + i.val, by omega⟩ k = 0 ∧
        sparseVal (e6RootSparse r) ⟨19 + i.val, by omega⟩ k = 0) →
      Y.a = 0 → Y.c = 0 →
      ((e6RootExp r s).1 Y).a = 0 ∧ ((e6RootExp r s).1 Y).c = 0 := by
    intro r s Y hzr ha hc0
    have hyk : ∀ k : Fin 27, ¬(k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19)) →
        h3ZornCoordinate Y k = 0 := by
      intro k hk
      by_cases hk11 : k.val < 11
      · have hne : k = ⟨3 + (⟨k.val - 3, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hne, h3ZornCoord_a_eq, ha, (zornCoord_eq_zero_iff 0).mpr rfl]
      · have hne : k = ⟨19 + (⟨k.val - 19, by omega⟩ : Fin 8).val, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hne, h3ZornCoord_c_eq, hc0, (zornCoord_eq_zero_iff 0).mpr rfl]
    constructor <;> refine zorn_eq_of_zornCoord_eq fun l => ?_
    · rw [← h3ZornCoord_a_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_a_eq, ha,
        (zornCoord_eq_zero_iff 0).mpr rfl l, zero_add]
      have hs0 : ∑ k : Fin 27,
          (sparseVal (e6RootSparse r) ⟨3 + l.val, by omega⟩ k : ℝ) * h3ZornCoordinate Y k = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19)
        · rw [(hzr l k hk).1, Int.cast_zero, zero_mul]
        · rw [hyk k hk, mul_zero]
      rw [hs0, mul_zero]
    · rw [← h3ZornCoord_c_eq, h3ZornCoordinate_e6RootExp, h3ZornCoord_c_eq, hc0,
        (zornCoord_eq_zero_iff 0).mpr rfl l, zero_add]
      have hs0 : ∑ k : Fin 27,
          (sparseVal (e6RootSparse r) ⟨19 + l.val, by omega⟩ k : ℝ) * h3ZornCoordinate Y k = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19)
        · rw [(hzr l k hk).2, Int.cast_zero, zero_mul]
        · rw [hyk k hk, mul_zero]
      rw [hs0, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · change h3ZornCoordinate ((f4PeirceExp 1 j t).1 X) 0 = h3ZornCoordinate X 0
    rw [h3ZornCoordinate_f4PeirceExp]
    have hs1 : ∑ k : Fin 27,
        ((sparseVal (e6RootSparse (f4PosIdx 1 j)) 0 k -
          sparseVal (e6RootSparse (f4NegIdx 1 j)) 0 k : ℤ) : ℝ) * h3ZornCoordinate X k = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [(hc1 j k).1.1.1, (hc1 j k).1.1.2]; simp
    have hs2 : ∑ l : Fin 27,
        (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 0 l : ℝ) *
          h3ZornCoordinate X l = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [sparseVal_mul]
      have hz : ∑ k : Fin 27, sparseVal (e6RootSparse (f4PosIdx 1 j)) 0 k *
          sparseVal (e6RootSparse (f4NegIdx 1 j)) k l = 0 :=
        Finset.sum_eq_zero fun k _ => by rw [(hc1 j k).1.1.1, zero_mul]
      rw [hz, Int.cast_zero, zero_mul]
    rw [hs1, hs2]; ring
  · change h3ZornCoordinate ((f4PeirceExp 1 j t).1 X) 1 +
      h3ZornCoordinate ((f4PeirceExp 1 j t).1 X) 2 = X.α₂ + X.α₃
    rw [h3ZornCoordinate_f4PeirceExp, h3ZornCoordinate_f4PeirceExp]
    have hs1 : ∑ k : Fin 27,
        ((sparseVal (e6RootSparse (f4PosIdx 1 j)) 1 k -
          sparseVal (e6RootSparse (f4NegIdx 1 j)) 1 k : ℤ) : ℝ) * h3ZornCoordinate X k +
        ∑ k : Fin 27,
        ((sparseVal (e6RootSparse (f4PosIdx 1 j)) 2 k -
          sparseVal (e6RootSparse (f4NegIdx 1 j)) 2 k : ℤ) : ℝ) * h3ZornCoordinate X k = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun k _ => ?_
      have h12 : sparseVal (e6RootSparse (f4PosIdx 1 j)) 1 k -
            sparseVal (e6RootSparse (f4NegIdx 1 j)) 1 k +
          (sparseVal (e6RootSparse (f4PosIdx 1 j)) 2 k -
            sparseVal (e6RootSparse (f4NegIdx 1 j)) 2 k) = 0 := by
        have h := (hc1 j k).1.2; omega
      have h12R : ((sparseVal (e6RootSparse (f4PosIdx 1 j)) 1 k -
            sparseVal (e6RootSparse (f4NegIdx 1 j)) 1 k : ℤ) : ℝ) +
          ((sparseVal (e6RootSparse (f4PosIdx 1 j)) 2 k -
            sparseVal (e6RootSparse (f4NegIdx 1 j)) 2 k : ℤ) : ℝ) = 0 := by exact_mod_cast h12
      calc
        ((sparseVal (e6RootSparse (f4PosIdx 1 j)) 1 k -
            sparseVal (e6RootSparse (f4NegIdx 1 j)) 1 k : ℤ) : ℝ) * h3ZornCoordinate X k +
          ((sparseVal (e6RootSparse (f4PosIdx 1 j)) 2 k -
            sparseVal (e6RootSparse (f4NegIdx 1 j)) 2 k : ℤ) : ℝ) * h3ZornCoordinate X k
          = (((sparseVal (e6RootSparse (f4PosIdx 1 j)) 1 k -
              sparseVal (e6RootSparse (f4NegIdx 1 j)) 1 k : ℤ) : ℝ) +
            ((sparseVal (e6RootSparse (f4PosIdx 1 j)) 2 k -
              sparseVal (e6RootSparse (f4NegIdx 1 j)) 2 k : ℤ) : ℝ)) * h3ZornCoordinate X k := by
            ring
        _ = 0 := by rw [h12R, zero_mul]
    have hs2 : ∑ l : Fin 27,
        (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 1 l : ℝ) *
          h3ZornCoordinate X l +
        ∑ l : Fin 27,
        (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 2 l : ℝ) *
          h3ZornCoordinate X l = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun l _ => ?_
      have h12R : (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 1 l : ℝ) +
          (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 2 l : ℝ) = 0 := by
        exact_mod_cast (hc1 j l).2
      calc
        (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 1 l : ℝ) *
            h3ZornCoordinate X l +
          (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 2 l : ℝ) *
            h3ZornCoordinate X l
          = ((sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 1 l : ℝ) +
            (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 2 l : ℝ)) *
              h3ZornCoordinate X l := by
            ring
        _ = 0 := by rw [h12R, zero_mul]
    calc
      h3ZornCoordinate X 1 + t * ∑ k : Fin 27,
            ((sparseVal (e6RootSparse (f4PosIdx 1 j)) 1 k -
              sparseVal (e6RootSparse (f4NegIdx 1 j)) 1 k : ℤ) : ℝ) * h3ZornCoordinate X k -
          t ^ 2 * ∑ l : Fin 27,
            (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 1 l : ℝ) *
              h3ZornCoordinate X l +
        (h3ZornCoordinate X 2 + t * ∑ k : Fin 27,
            ((sparseVal (e6RootSparse (f4PosIdx 1 j)) 2 k -
              sparseVal (e6RootSparse (f4NegIdx 1 j)) 2 k : ℤ) : ℝ) * h3ZornCoordinate X k -
          t ^ 2 * ∑ l : Fin 27,
            (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 2 l : ℝ) *
              h3ZornCoordinate X l)
        = (h3ZornCoordinate X 1 + h3ZornCoordinate X 2) +
            t * (∑ k : Fin 27,
              ((sparseVal (e6RootSparse (f4PosIdx 1 j)) 1 k -
                sparseVal (e6RootSparse (f4NegIdx 1 j)) 1 k : ℤ) : ℝ) * h3ZornCoordinate X k +
              ∑ k : Fin 27,
              ((sparseVal (e6RootSparse (f4PosIdx 1 j)) 2 k -
                sparseVal (e6RootSparse (f4NegIdx 1 j)) 2 k : ℤ) : ℝ) * h3ZornCoordinate X k) -
            t ^ 2 * (∑ l : Fin 27,
              (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 1 l : ℝ) *
                h3ZornCoordinate X l +
              ∑ l : Fin 27,
              (sparseVal (sparseMul (e6RootSparse (f4PosIdx 1 j)) (e6RootSparse (f4NegIdx 1 j))) 2 l : ℝ) *
                h3ZornCoordinate X l) := by ring
      _ = X.α₂ + X.α₃ := by rw [hs1, hs2]; change (X.α₂ + X.α₃) + t * 0 - t ^ 2 * 0 = _; ring
  · intro ha hc0
    have hzrNeg : ∀ (i : Fin 8) (k : Fin 27), k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19) →
        sparseVal (e6RootSparse (f4NegIdx 1 j)) ⟨3 + i.val, by omega⟩ k = 0 ∧
        sparseVal (e6RootSparse (f4NegIdx 1 j)) ⟨19 + i.val, by omega⟩ k = 0 := fun i k hk => by
      have hm := hc2 j i k
      simp only [hk, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hm
      exact ⟨hm.1.1.2, hm.2⟩
    have hzrPos : ∀ (i : Fin 8) (k : Fin 27), k.val < 3 ∨ (11 ≤ k.val ∧ k.val < 19) →
        sparseVal (e6RootSparse (f4PosIdx 1 j)) ⟨3 + i.val, by omega⟩ k = 0 ∧
        sparseVal (e6RootSparse (f4PosIdx 1 j)) ⟨19 + i.val, by omega⟩ k = 0 := fun i k hk => by
      have hm := hc2 j i k
      simp only [hk, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hm
      exact ⟨hm.1.1.1, hm.1.2⟩
    obtain ⟨ha1, hc1'⟩ := hzero_ac (f4NegIdx 1 j) (-t) X hzrNeg ha hc0
    exact hzero_ac (f4PosIdx 1 j) t _ hzrPos ha1 hc1'

private theorem e6RootExp_fix_diag1_of_col0_zero (r : Fin 72) (t : ℝ)
    (hcol0 : ∀ m : Fin 27, sparseVal (e6RootSparse r) m 0 = 0) :
    (e6RootExp r t).1 h3_diag₁ = h3_diag₁ := by
  apply h3Zorn_ext_coord; intro m
  rw [h3ZornCoordinate_e6RootExp]
  have hs0 : ∑ k : Fin 27, (sparseVal (e6RootSparse r) m k : ℝ) *
      h3ZornCoordinate h3_diag₁ k = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = 0
    · subst hk; rw [hcol0 m, Int.cast_zero, zero_mul]
    · have hk0 : h3ZornCoordinate h3_diag₁ k = 0 := by
        fin_cases k
        · exact absurd rfl hk
        all_goals rfl
      rw [hk0, mul_zero]
  rw [hs0, mul_zero, add_zero]

private theorem f4Peirce_1_fix_diag1 (j : Fin 8) (t : ℝ) :
    (f4PeirceExp 1 j t).1 h3_diag₁ = h3_diag₁ := by
  have hc : (List.finRange 8).all (fun j => (List.finRange 27).all (fun m =>
      (sparseVal (e6RootSparse (f4PosIdx 1 j)) m 0 == 0) &&
      (sparseVal (e6RootSparse (f4NegIdx 1 j)) m 0 == 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc
  change (e6RootExp (f4PosIdx 1 j) t).1 ((e6RootExp (f4NegIdx 1 j) (-t)).1 h3_diag₁) = h3_diag₁
  rw [e6RootExp_fix_diag1_of_col0_zero (f4NegIdx 1 j) (-t) (fun m => (hc j m).2)]
  exact e6RootExp_fix_diag1_of_col0_zero (f4PosIdx 1 j) t (fun m => (hc j m).1)

private def bMidRoot (j : Fin 6) : Fin 72 :=
  ![21, 19, 18, 3, 4, 5] j

private def bMidOppIdx (j : Fin 6) : Fin 8 :=
  ![4, 5, 6, 1, 2, 3] j

private def bMidSign (j : Fin 6) : ℝ :=
  ![1, -1, 1, 1, 1, 1] j

private theorem d4_bMidRoot_lt24 (j : Fin 6) : (bMidRoot j).val < 24 := by
  fin_cases j <;> decide

private theorem d4_bMidRoot_coords (j : Fin 6) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (bMidRoot j) t).1 X).α₁ = X.α₁ ∧
    ((e6RootExp (bMidRoot j) t).1 X).α₂ = X.α₂ ∧
    ((e6RootExp (bMidRoot j) t).1 X).α₃ = X.α₃ ∧
    zornCoord ((e6RootExp (bMidRoot j) t).1 X).b 0 = zornCoord X.b 0 ∧
    zornCoord ((e6RootExp (bMidRoot j) t).1 X).b 7 =
      zornCoord X.b 7 + bMidSign j * t * zornCoord X.b (bMidOppIdx j) ∧
    (∀ i : Fin 6, zornCoord ((e6RootExp (bMidRoot j) t).1 X).b ⟨1 + i.val, by omega⟩ =
      if i = j then zornCoord X.b ⟨1 + i.val, by omega⟩ + bMidSign j * t * zornCoord X.b 0
      else zornCoord X.b ⟨1 + i.val, by omega⟩) := by
  have hb := d4_rootExp_preserves_blocks (d4_bMidRoot_lt24 j) t X
  let bMidS : Fin 6 → ℤ := ![1, -1, 1, 1, 1, 1]
  have hs_cast : (bMidS j : ℝ) = bMidSign j := by
    fin_cases j <;> simp [bMidS, bMidSign]
  have hc : (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (bMidRoot j)) 11 k == 0) &&
      (sparseVal (e6RootSparse (bMidRoot j)) 18 k ==
        if k.val = 11 + (bMidOppIdx j).val then bMidS j else 0))) = true := by decide
  have hc2 : (List.finRange 6).all (fun j => (List.finRange 6).all (fun i =>
      (List.finRange 27).all (fun k =>
        sparseVal (e6RootSparse (bMidRoot j)) ⟨12 + i.val, by omega⟩ k ==
          if i == j && k.val == 11 then bMidS j else 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc hc2
  refine ⟨hb.1, hb.2.1, hb.2.2.1, ?_, ?_, ?_⟩
  · rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    exact rootExp_coord_unchanged (bMidRoot j) 11 t X fun k => (hc j k).1
  · rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp (bMidRoot j) t).1 X) 18 =
      h3ZornCoordinate X 18 + bMidSign j * t * h3ZornCoordinate X ⟨11 + (bMidOppIdx j).val, by omega⟩
    rw [h3ZornCoordinate_e6RootExp, Finset.sum_eq_single ⟨11 + (bMidOppIdx j).val, by omega⟩]
    · rw [(hc j _).2]; simp [hs_cast]; ring
    · intro k _ hk; rw [(hc j k).2]
      have hk' : k.val ≠ 11 + (bMidOppIdx j).val := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i
    rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    have hidx : (⟨11 + (⟨1 + i.val, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
        ⟨12 + i.val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hidx, h3ZornCoordinate_e6RootExp]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single 11]
      · rw [hc2 i i 11, ← h3ZornCoord_b_eq X 0]; simp [hs_cast]; ring
      · intro k _ hk; rw [hc2 i i k]
        have hk' : k.val ≠ 11 := fun h => hk (Fin.ext h)
        simp [hk']
      · intro h; exact absurd (Finset.mem_univ 11) h
    · have hs0 : ∑ k : Fin 27,
          (sparseVal (e6RootSparse (bMidRoot j)) ⟨12 + i.val, by omega⟩ k : ℝ) *
            h3ZornCoordinate X k = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hc2 j i k]
        simp [hij]
      rw [hs0, mul_zero, add_zero]
      simp [hij]

private def bPullFullRoot (j : Fin 6) : Fin 72 :=
  ![10, 14, 17, 11, 7, 6] j

private def bPullFullSign (j : Fin 6) : ℝ :=
  ![-1, -1, -1, -1, 1, -1] j

private theorem d4_bPullFullRoot_lt24 (j : Fin 6) : (bPullFullRoot j).val < 24 := by
  fin_cases j <;> decide

private theorem d4_bPullFullRoot_coords (j : Fin 6) (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp (bPullFullRoot j) t).1 X).α₁ = X.α₁ ∧
    ((e6RootExp (bPullFullRoot j) t).1 X).α₂ = X.α₂ ∧
    ((e6RootExp (bPullFullRoot j) t).1 X).α₃ = X.α₃ ∧
    zornCoord ((e6RootExp (bPullFullRoot j) t).1 X).b 0 =
      zornCoord X.b 0 + bPullFullSign j * t * zornCoord X.b (bMidOppIdx j) ∧
    zornCoord ((e6RootExp (bPullFullRoot j) t).1 X).b 7 = zornCoord X.b 7 ∧
    (∀ i : Fin 6, zornCoord ((e6RootExp (bPullFullRoot j) t).1 X).b ⟨1 + i.val, by omega⟩ =
      if i = j then zornCoord X.b ⟨1 + i.val, by omega⟩ + bPullFullSign j * t * zornCoord X.b 7
      else zornCoord X.b ⟨1 + i.val, by omega⟩) := by
  have hb := d4_rootExp_preserves_blocks (d4_bPullFullRoot_lt24 j) t X
  let bPullS : Fin 6 → ℤ := ![-1, -1, -1, -1, 1, -1]
  have hs_cast : (bPullS j : ℝ) = bPullFullSign j := by
    fin_cases j <;> simp [bPullS, bPullFullSign]
  have hc : (List.finRange 6).all (fun j => (List.finRange 27).all (fun k =>
      (sparseVal (e6RootSparse (bPullFullRoot j)) 18 k == 0) &&
      (sparseVal (e6RootSparse (bPullFullRoot j)) 11 k ==
        if k.val = 11 + (bMidOppIdx j).val then bPullS j else 0))) = true := by decide
  have hc2 : (List.finRange 6).all (fun j => (List.finRange 6).all (fun i =>
      (List.finRange 27).all (fun k =>
        sparseVal (e6RootSparse (bPullFullRoot j)) ⟨12 + i.val, by omega⟩ k ==
          if i == j && k.val == 18 then bPullS j else 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, beq_iff_eq] at hc hc2
  refine ⟨hb.1, hb.2.1, hb.2.2.1, ?_, ?_, ?_⟩
  · rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    change h3ZornCoordinate ((e6RootExp (bPullFullRoot j) t).1 X) 11 =
      h3ZornCoordinate X 11 + bPullFullSign j * t * h3ZornCoordinate X ⟨11 + (bMidOppIdx j).val, by omega⟩
    rw [h3ZornCoordinate_e6RootExp, Finset.sum_eq_single ⟨11 + (bMidOppIdx j).val, by omega⟩]
    · rw [(hc j _).2]; simp [hs_cast]; ring
    · intro k _ hk; rw [(hc j k).2]
      have hk' : k.val ≠ 11 + (bMidOppIdx j).val := fun h => hk (Fin.ext h)
      simp [hk']
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    exact rootExp_coord_unchanged (bPullFullRoot j) 18 t X fun k => (hc j k).1
  · intro i
    rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
    have hidx : (⟨11 + (⟨1 + i.val, by omega⟩ : Fin 8).val, by omega⟩ : Fin 27) =
        ⟨12 + i.val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hidx, h3ZornCoordinate_e6RootExp]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single 18]
      · rw [hc2 i i 18, ← h3ZornCoord_b_eq X 7]; simp [hs_cast]; ring
      · intro k _ hk; rw [hc2 i i k]
        have hk' : k.val ≠ 18 := fun h => hk (Fin.ext h)
        simp [hk']
      · intro h; exact absurd (Finset.mem_univ 18) h
    · have hs0 : ∑ k : Fin 27,
          (sparseVal (e6RootSparse (bPullFullRoot j)) ⟨12 + i.val, by omega⟩ k : ℝ) *
            h3ZornCoordinate X k = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hc2 j i k]
        simp [hij]
      rw [hs0, mul_zero, add_zero]
      simp [hij]

private theorem f4_clear_b_fix_diag1 (X : H3Zorn ℝ) (he : isRankOneIdem X)
    (h1 : X.α₁ = 0) (ha : X.a = 0) (hc : X.c = 0) (hsum : X.α₂ + X.α₃ ≠ 0) :
    ∃ f ∈ e6F4InChevalley, f.1 h3_diag₁ = h3_diag₁ ∧
      (f.1 X).b = 0 ∧ (f.1 X).α₁ = 0 ∧ (f.1 X).a = 0 ∧ (f.1 X).c = 0 ∧
      (f.1 X).α₂ + (f.1 X).α₃ = X.α₂ + X.α₃ := by
  -- Sub-step 1: ensure (α₂ - α₃)^2 + 4 * b₀ * b₇ ≥ 0
  have hs1 : ∃ f₁ ∈ e6F4InChevalley, f₁.1 h3_diag₁ = h3_diag₁ ∧
      0 ≤ ((f₁.1 X).α₂ - (f₁.1 X).α₃) ^ 2 + 4 * zornCoord (f₁.1 X).b 0 * zornCoord (f₁.1 X).b 7 ∧
      (f₁.1 X).α₁ = 0 ∧ (f₁.1 X).a = 0 ∧ (f₁.1 X).c = 0 ∧
      (f₁.1 X).α₂ + (f₁.1 X).α₃ = X.α₂ + X.α₃ := by
    by_cases hdisc : 0 ≤ (X.α₂ - X.α₃) ^ 2 + 4 * zornCoord X.b 0 * zornCoord X.b 7
    · exact ⟨1, e6F4InChevalley.one_mem, rfl, hdisc, h1, ha, hc, rfl⟩
    · have hlt : (X.α₂ - X.α₃) ^ 2 + 4 * zornCoord X.b 0 * zornCoord X.b 7 < 0 := lt_of_not_ge hdisc
      have hnorm := (isRankOneIdem_norm_eq he).2.1
      rw [zorn_norm_zornCoord] at hnorm
      have hsne := neg_sum_neg_of_lt_cb hnorm hlt
      have hexj : ∃ j : Fin 6, zornCoord X.b (bMidOppIdx j) ≠ 0 := by
        by_contra hcon; push Not at hcon
        have h1' := hcon 3; have h2' := hcon 4; have h3' := hcon 5
        have h4' := hcon 0; have h5' := hcon 1; have h6' := hcon 2
        dsimp [bMidOppIdx] at h1' h2' h3' h4' h5' h6'
        exact hsne (by rw [h1', h2', h3', h4', h5', h6']; ring)
      obtain ⟨j, hj⟩ := hexj
      have hsign : bMidSign j ≠ 0 := by fin_cases j <;> simp [bMidSign]
      let t := -zornCoord X.b 7 / (bMidSign j * zornCoord X.b (bMidOppIdx j))
      let g := e6RootExp (bMidRoot j) t
      have hg_d4 : g ∈ d4Subgroup := Subgroup.subset_closure ⟨bMidRoot j, d4_bMidRoot_lt24 j, t, rfl⟩
      have hg_f4 : g ∈ e6F4InChevalley := d4Subgroup_le_f4InChevalley hg_d4
      obtain ⟨hd1, hd2, hd3, _, hb7, _⟩ := d4_bMidRoot_coords j t X
      have hblk := d4_rootExp_preserves_blocks (d4_bMidRoot_lt24 j) t X
      refine ⟨g, hg_f4, (d4Subgroup_fix_diags hg_d4).1, ?_,
        hd1.trans h1, hblk.2.2.2.1 ha, hblk.2.2.2.2.2 hc, by rw [hd2, hd3]⟩
      have h7z : zornCoord (g.1 X).b 7 = 0 := by
        rw [hb7]; dsimp [t]; field_simp [hsign, hj]; ring
      rw [h7z, mul_zero, add_zero]; exact sq_nonneg _
  obtain ⟨f₁, hf₁, hf1_d, hdisc₁, h1₁, ha₁, hc₁, hsum₁⟩ := hs1
  let X₁ := f₁.1 X
  have he₁ : isRankOneIdem X₁ := f4InChevalley_preserves_isRankOneIdem hf₁ he
  -- Sub-step 2: kill b₀ to 0
  have hs2 : ∃ f₂ ∈ e6F4InChevalley, f₂.1 h3_diag₁ = h3_diag₁ ∧
      zornCoord (f₂.1 X₁).b 0 = 0 ∧
      (f₂.1 X₁).α₁ = 0 ∧ (f₂.1 X₁).a = 0 ∧ (f₂.1 X₁).c = 0 ∧
      (f₂.1 X₁).α₂ + (f₂.1 X₁).α₃ = X₁.α₂ + X₁.α₃ := by
    by_cases hb7 : zornCoord X₁.b 7 ≠ 0
    · have hdisc' : 0 ≤ (X₁.α₃ - X₁.α₂) ^ 2 + 4 * zornCoord X₁.b 7 * zornCoord X₁.b 0 := by
        nlinarith [hdisc₁]
      obtain ⟨t, ht⟩ := real_quad_root_cb hb7 hdisc'
      obtain ⟨_, _, _, hb0', _, _⟩ := f4Peirce_1_0_coords t X₁
      obtain ⟨p1, p23, pac⟩ := f4Peirce_1_preserves_blocks 0 t X₁
      obtain ⟨pa, pc⟩ := pac ha₁ hc₁
      exact ⟨f4PeirceExp 1 0 t, f4PeirceExp_mem_f4 1 0 t, f4Peirce_1_fix_diag1 0 t,
        hb0'.trans ht, p1.trans h1₁, pa, pc, p23⟩
    · push Not at hb7
      by_cases hα : X₁.α₃ - X₁.α₂ ≠ 0
      · let t := -zornCoord X₁.b 0 / (X₁.α₃ - X₁.α₂)
        obtain ⟨_, _, _, hb0', _, _⟩ := f4Peirce_1_0_coords t X₁
        obtain ⟨p1, p23, pac⟩ := f4Peirce_1_preserves_blocks 0 t X₁
        obtain ⟨pa, pc⟩ := pac ha₁ hc₁
        refine ⟨f4PeirceExp 1 0 t, f4PeirceExp_mem_f4 1 0 t, f4Peirce_1_fix_diag1 0 t,
          ?_, p1.trans h1₁, pa, pc, p23⟩
        rw [hb0', hb7, mul_zero, sub_zero]; dsimp [t]; field_simp [hα]; ring
      · push Not at hα
        by_cases hb0 : zornCoord X₁.b 0 = 0
        · exact ⟨1, e6F4InChevalley.one_mem, rfl, hb0, h1₁, ha₁, hc₁, rfl⟩
        · have hact : (f4PeirceExp 1 0 1 * f4PeirceExp 1 7 1).1 X₁ =
              (f4PeirceExp 1 0 1).1 ((f4PeirceExp 1 7 1).1 X₁) := rfl
          have hd_fix : (f4PeirceExp 1 0 1 * f4PeirceExp 1 7 1).1 h3_diag₁ = h3_diag₁ := by
            change (f4PeirceExp 1 0 1).1 ((f4PeirceExp 1 7 1).1 h3_diag₁) = h3_diag₁
            rw [f4Peirce_1_fix_diag1 7 1, f4Peirce_1_fix_diag1 0 1]
          obtain ⟨p1, p2, p3, pb0, pb7, _⟩ := f4Peirce_1_7_coords 1 X₁
          obtain ⟨q1, q23, qac⟩ := f4Peirce_1_preserves_blocks 7 1 X₁
          obtain ⟨qa, qc⟩ := qac ha₁ hc₁
          obtain ⟨_, _, _, r0, _, _⟩ := f4Peirce_1_0_coords 1 ((f4PeirceExp 1 7 1).1 X₁)
          obtain ⟨r1, r23, rac⟩ := f4Peirce_1_preserves_blocks 0 1 ((f4PeirceExp 1 7 1).1 X₁)
          obtain ⟨ra, rc⟩ := rac qa qc
          refine ⟨f4PeirceExp 1 0 1 * f4PeirceExp 1 7 1,
            e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 1 0 1) (f4PeirceExp_mem_f4 1 7 1),
            hd_fix, ?_, r1.trans (q1.trans h1₁), ra, rc, r23.trans q23⟩
          rw [hact, r0, pb0, pb7, p3, p2]; linarith [hα]
  obtain ⟨f₂, hf₂, hf2_d, hb0₂, h1₂, ha₂, hc₂, hsum₂⟩ := hs2
  let X₂ := f₂.1 X₁
  have he₂ : isRankOneIdem X₂ := f4InChevalley_preserves_isRankOneIdem hf₂ he₁
  -- Sub-step 3: kill b_mid (1..6) AND keep b₀ = 0
  have hs3 : ∃ f₃ ∈ e6F4InChevalley, f₃.1 h3_diag₁ = h3_diag₁ ∧
      zornCoord (f₃.1 X₂).b 0 = 0 ∧
      (∀ i : Fin 6, zornCoord (f₃.1 X₂).b ⟨1 + i.val, by omega⟩ = 0) ∧
      (f₃.1 X₂).α₁ = 0 ∧ (f₃.1 X₂).a = 0 ∧ (f₃.1 X₂).c = 0 ∧
      (f₃.1 X₂).α₂ + (f₃.1 X₂).α₃ = X₂.α₂ + X₂.α₃ := by
    by_cases hmid : ∀ i : Fin 6, zornCoord X₂.b ⟨1 + i.val, by omega⟩ = 0
    · exact ⟨1, e6F4InChevalley.one_mem, rfl, hb0₂, hmid, h1₂, ha₂, hc₂, rfl⟩
    · push Not at hmid
      obtain ⟨i₀, hi₀⟩ := hmid
      have hs3a : ∃ g₁ ∈ e6F4InChevalley, g₁.1 h3_diag₁ = h3_diag₁ ∧
          zornCoord (g₁.1 X₂).b 7 ≠ 0 ∧
          (g₁.1 X₂).α₁ = 0 ∧ (g₁.1 X₂).a = 0 ∧ (g₁.1 X₂).c = 0 ∧
          (g₁.1 X₂).α₂ + (g₁.1 X₂).α₃ = X₂.α₂ + X₂.α₃ := by
        by_cases hb7 : zornCoord X₂.b 7 ≠ 0
        · exact ⟨1, e6F4InChevalley.one_mem, rfl, hb7, h1₂, ha₂, hc₂, rfl⟩
        · push Not at hb7
          have hexopp : ∃ j : Fin 6, zornCoord X₂.b (bMidOppIdx j) ≠ 0 := by
            by_contra hcon; push Not at hcon
            have hopp : ∀ k : Fin 8, k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 →
                zornCoord X₂.b k = 0 := by
              intro k hk
              rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
              · exact hcon 3
              · exact hcon 4
              · exact hcon 5
              · exact hcon 0
              · exact hcon 1
              · exact hcon 2
            apply hi₀; apply hopp; fin_cases i₀ <;> decide
          obtain ⟨j, hj⟩ := hexopp
          let gp := e6RootExp (bPullFullRoot j) 1
          have hgp_d4 : gp ∈ d4Subgroup :=
            Subgroup.subset_closure ⟨bPullFullRoot j, d4_bPullFullRoot_lt24 j, 1, rfl⟩
          have hgp_f4 : gp ∈ e6F4InChevalley := d4Subgroup_le_f4InChevalley hgp_d4
          obtain ⟨gd1, gd2, gd3, gb0, _, _⟩ := d4_bPullFullRoot_coords j 1 X₂
          have gblk := d4_rootExp_preserves_blocks (d4_bPullFullRoot_lt24 j) 1 X₂
          have hsign : bPullFullSign j ≠ 0 := by fin_cases j <;> simp [bPullFullSign]
          have gb0_ne : zornCoord (gp.1 X₂).b 0 ≠ 0 := by
            rw [gb0, hb0₂, zero_add, mul_one]; exact mul_ne_zero hsign hj
          let Y := gp.1 X₂
          by_cases h1b : zornCoord ((f4PeirceExp 1 7 1).1 Y).b 7 ≠ 0
          · obtain ⟨p1, p23, pac⟩ := f4Peirce_1_preserves_blocks 7 1 Y
            obtain ⟨pa, pc⟩ := pac (gblk.2.2.2.1 ha₂) (gblk.2.2.2.2.2 hc₂)
            have hdf : (f4PeirceExp 1 7 1 * gp).1 h3_diag₁ = h3_diag₁ := by
              change (f4PeirceExp 1 7 1).1 (gp.1 h3_diag₁) = h3_diag₁
              rw [(d4Subgroup_fix_diags hgp_d4).1, f4Peirce_1_fix_diag1 7 1]
            refine ⟨f4PeirceExp 1 7 1 * gp, e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 1 7 1) hgp_f4,
              hdf, h1b, p1.trans (gd1.trans h1₂), pa, pc, ?_⟩
            change ((f4PeirceExp 1 7 1).1 Y).α₂ + ((f4PeirceExp 1 7 1).1 Y).α₃ = _
            rw [p23, gd2, gd3]
          · push Not at h1b
            have hm1b : zornCoord ((f4PeirceExp 1 7 (-1)).1 Y).b 7 ≠ 0 := by
              obtain ⟨_, _, _, _, hb7p, _⟩ := f4Peirce_1_7_coords 1 Y
              obtain ⟨_, _, _, _, hb7m, _⟩ := f4Peirce_1_7_coords (-1) Y
              rw [hb7p] at h1b; rw [hb7m]
              intro hz; apply gb0_ne; linarith [h1b, hz]
            obtain ⟨p1, p23, pac⟩ := f4Peirce_1_preserves_blocks 7 (-1) Y
            obtain ⟨pa, pc⟩ := pac (gblk.2.2.2.1 ha₂) (gblk.2.2.2.2.2 hc₂)
            have hdf : (f4PeirceExp 1 7 (-1) * gp).1 h3_diag₁ = h3_diag₁ := by
              change (f4PeirceExp 1 7 (-1)).1 (gp.1 h3_diag₁) = h3_diag₁
              rw [(d4Subgroup_fix_diags hgp_d4).1, f4Peirce_1_fix_diag1 7 (-1)]
            refine ⟨f4PeirceExp 1 7 (-1) * gp, e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 1 7 (-1)) hgp_f4,
              hdf, hm1b, p1.trans (gd1.trans h1₂), pa, pc, ?_⟩
            change ((f4PeirceExp 1 7 (-1)).1 Y).α₂ + ((f4PeirceExp 1 7 (-1)).1 Y).α₃ = _
            rw [p23, gd2, gd3]
      obtain ⟨g₁, hg₁, hg1_d, hb7', h1', ha', hc', hsum'⟩ := hs3a
      let Y := g₁.1 X₂
      have heY : isRankOneIdem Y := f4InChevalley_preserves_isRankOneIdem hg₁ he₂
      have hclear_step : ∀ (j : Fin 6) (Z : H3Zorn ℝ), zornCoord Z.b 7 ≠ 0 →
          ∃ g ∈ d4Subgroup,
            zornCoord (g.1 Z).b 7 = zornCoord Z.b 7 ∧
            zornCoord (g.1 Z).b ⟨1 + j.val, by omega⟩ = 0 ∧
            (∀ i : Fin 6, i ≠ j →
              zornCoord (g.1 Z).b ⟨1 + i.val, by omega⟩ = zornCoord Z.b ⟨1 + i.val, by omega⟩) := by
        intro j Z hz7
        have hsign : bPullFullSign j ≠ 0 := by fin_cases j <;> simp [bPullFullSign]
        let t := -zornCoord Z.b ⟨1 + j.val, by omega⟩ / (bPullFullSign j * zornCoord Z.b 7)
        refine ⟨e6RootExp (bPullFullRoot j) t,
          Subgroup.subset_closure ⟨bPullFullRoot j, d4_bPullFullRoot_lt24 j, t, rfl⟩, ?_⟩
        obtain ⟨_, _, _, _, gb7, gmid⟩ := d4_bPullFullRoot_coords j t Z
        refine ⟨gb7, ?_, fun i hij => ?_⟩
        · rw [gmid j]; simp only [↓reduceIte]; dsimp [t]; field_simp [hsign, hz7]; ring
        · rw [gmid i]; simp [hij]
      obtain ⟨p0, hp0, hb7_0, h0_0, ho_0⟩ := hclear_step 0 Y hb7'
      have hb7_0n : zornCoord (p0.1 Y).b 7 ≠ 0 := by rw [hb7_0]; exact hb7'
      obtain ⟨p1, hp1, hb7_1, h1_1, ho_1⟩ := hclear_step 1 (p0.1 Y) hb7_0n
      have hb7_1n : zornCoord (p1.1 (p0.1 Y)).b 7 ≠ 0 := by rw [hb7_1]; exact hb7_0n
      obtain ⟨p2, hp2, hb7_2, h2_2, ho_2⟩ := hclear_step 2 (p1.1 (p0.1 Y)) hb7_1n
      have hb7_2n : zornCoord (p2.1 (p1.1 (p0.1 Y))).b 7 ≠ 0 := by rw [hb7_2]; exact hb7_1n
      obtain ⟨p3, hp3, hb7_3, h3_3, ho_3⟩ := hclear_step 3 (p2.1 (p1.1 (p0.1 Y))) hb7_2n
      have hb7_3n : zornCoord (p3.1 (p2.1 (p1.1 (p0.1 Y)))).b 7 ≠ 0 := by rw [hb7_3]; exact hb7_2n
      obtain ⟨p4, hp4, hb7_4, h4_4, ho_4⟩ := hclear_step 4 (p3.1 (p2.1 (p1.1 (p0.1 Y)))) hb7_3n
      have hb7_4n : zornCoord (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y))))).b 7 ≠ 0 := by rw [hb7_4]; exact hb7_3n
      obtain ⟨p5, hp5, hb7_5, h5_5, ho_5⟩ := hclear_step 5 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y))))) hb7_4n
      let pd := p5 * p4 * p3 * p2 * p1 * p0
      have hpd_d4 : pd ∈ d4Subgroup :=
        d4Subgroup.mul_mem (d4Subgroup.mul_mem (d4Subgroup.mul_mem (d4Subgroup.mul_mem
          (d4Subgroup.mul_mem hp5 hp4) hp3) hp2) hp1) hp0
      have hpd_f4 : pd ∈ e6F4InChevalley := d4Subgroup_le_f4InChevalley hpd_d4
      let Z := pd.1 Y
      have hz0 : zornCoord Z.b 1 = 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).b ⟨1 + (0 : Fin 6).val, by omega⟩ = 0
        rw [ho_5 0 (by decide), ho_4 0 (by decide), ho_3 0 (by decide), ho_2 0 (by decide),
          ho_1 0 (by decide)]; exact h0_0
      have hz1 : zornCoord Z.b 2 = 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).b ⟨1 + (1 : Fin 6).val, by omega⟩ = 0
        rw [ho_5 1 (by decide), ho_4 1 (by decide), ho_3 1 (by decide), ho_2 1 (by decide)]; exact h1_1
      have hz2 : zornCoord Z.b 3 = 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).b ⟨1 + (2 : Fin 6).val, by omega⟩ = 0
        rw [ho_5 2 (by decide), ho_4 2 (by decide), ho_3 2 (by decide)]; exact h2_2
      have hz3 : zornCoord Z.b 4 = 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).b ⟨1 + (3 : Fin 6).val, by omega⟩ = 0
        rw [ho_5 3 (by decide), ho_4 3 (by decide)]; exact h3_3
      have hz4 : zornCoord Z.b 5 = 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).b ⟨1 + (4 : Fin 6).val, by omega⟩ = 0
        rw [ho_5 4 (by decide)]; exact h4_4
      have hz5 : zornCoord Z.b 6 = 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).b ⟨1 + (5 : Fin 6).val, by omega⟩ = 0
        exact h5_5
      have hZ_mid : ∀ i : Fin 6, zornCoord Z.b ⟨1 + i.val, by omega⟩ = 0 := by
        intro i; fin_cases i <;> [exact hz0; exact hz1; exact hz2; exact hz3; exact hz4; exact hz5]
      have hZ_b7 : zornCoord Z.b 7 ≠ 0 := by
        change zornCoord (p5.1 (p4.1 (p3.1 (p2.1 (p1.1 (p0.1 Y)))))).b 7 ≠ 0
        rw [hb7_5]; exact hb7_4n
      have heZ : isRankOneIdem Z := f4InChevalley_preserves_isRankOneIdem hpd_f4 heY
      have hZ_norm := (isRankOneIdem_norm_eq heZ).2.1
      rw [zorn_norm_zornCoord, hz0, hz1, hz2, hz3, hz4, hz5] at hZ_norm
      have hdiscZ : 0 ≤ (Z.α₃ - Z.α₂) ^ 2 + 4 * zornCoord Z.b 7 * zornCoord Z.b 0 := by
        have h1z : Z.α₂ * Z.α₃ = zornCoord Z.b 0 * zornCoord Z.b 7 := by linarith [hZ_norm]
        nlinarith [sq_nonneg (Z.α₂ + Z.α₃), h1z]
      obtain ⟨tz, htz⟩ := real_quad_root_cb hZ_b7 hdiscZ
      obtain ⟨_, _, _, zb0, _, zmid⟩ := f4Peirce_1_0_coords tz Z
      obtain ⟨z1, z23, zac⟩ := f4Peirce_1_preserves_blocks 0 tz Z
      obtain ⟨d1, d2, d3, da, db, dc⟩ := d4Subgroup_preserves_blocks hpd_d4 Y
      obtain ⟨za, zc⟩ := zac (da.mpr ha') (dc.mpr hc')
      have hact : (f4PeirceExp 1 0 tz * pd * g₁).1 X₂ = (f4PeirceExp 1 0 tz).1 Z := rfl
      have hdf : (f4PeirceExp 1 0 tz * pd * g₁).1 h3_diag₁ = h3_diag₁ := by
        change (f4PeirceExp 1 0 tz).1 (pd.1 (g₁.1 h3_diag₁)) = h3_diag₁
        rw [hg1_d, (d4Subgroup_fix_diags hpd_d4).1, f4Peirce_1_fix_diag1 0 tz]
      refine ⟨f4PeirceExp 1 0 tz * pd * g₁,
        e6F4InChevalley.mul_mem (e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 1 0 tz) hpd_f4) hg₁,
        hdf, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hact]; exact zb0.trans htz
      · intro i; rw [hact, zmid i]; exact hZ_mid i
      · rw [hact, z1, d1, h1']
      · rw [hact]; exact za
      · rw [hact]; exact zc
      · rw [hact, z23, d2, d3, hsum']
  obtain ⟨f₃, hf₃, hf3_d, hb0₃, hbmid₃, h1₃, ha₃, hc₃, hsum₃⟩ := hs3
  let X₃ := f₃.1 X₂
  have he₃ : isRankOneIdem X₃ := f4InChevalley_preserves_isRankOneIdem hf₃ he₂
  -- Sub-step 4: kill b₇ using α₂ ≠ α₃
  have hm1 : zornCoord X₃.b 1 = 0 := hbmid₃ 0
  have hm2 : zornCoord X₃.b 2 = 0 := hbmid₃ 1
  have hm3 : zornCoord X₃.b 3 = 0 := hbmid₃ 2
  have hm4 : zornCoord X₃.b 4 = 0 := hbmid₃ 3
  have hm5 : zornCoord X₃.b 5 = 0 := hbmid₃ 4
  have hm6 : zornCoord X₃.b 6 = 0 := hbmid₃ 5
  have hX3_norm := (isRankOneIdem_norm_eq he₃).2.1
  rw [zorn_norm_zornCoord, hb0₃, hm1, hm2, hm3, hm4, hm5, hm6] at hX3_norm
  have hX3_mul : X₃.α₂ * X₃.α₃ = 0 := by linarith [hX3_norm]
  have hX3_sum : X₃.α₂ + X₃.α₃ ≠ 0 := by rw [hsum₃, hsum₂, hsum₁]; exact hsum
  have hX3_ne : X₃.α₃ - X₃.α₂ ≠ 0 :=
    sub_ne_zero.mpr (sub_ne_of_mul_zero_sum_ne_cb hX3_mul hX3_sum).symm
  let t₄ := -zornCoord X₃.b 7 / (X₃.α₃ - X₃.α₂)
  obtain ⟨_, _, _, hb0₄, hb7₄, hbmid₄⟩ := f4Peirce_1_7_coords t₄ X₃
  obtain ⟨h1₄, h23₄, hac₄⟩ := f4Peirce_1_preserves_blocks 7 t₄ X₃
  obtain ⟨ha₄, hc₄⟩ := hac₄ ha₃ hc₃
  have hact_x : (f4PeirceExp 1 7 t₄ * (f₃ * (f₂ * f₁))).1 X = (f4PeirceExp 1 7 t₄).1 X₃ := rfl
  have hdf_all : (f4PeirceExp 1 7 t₄ * (f₃ * (f₂ * f₁))).1 h3_diag₁ = h3_diag₁ := by
    change (f4PeirceExp 1 7 t₄).1 (f₃.1 (f₂.1 (f₁.1 h3_diag₁))) = h3_diag₁
    rw [hf1_d, hf2_d, hf3_d, f4Peirce_1_fix_diag1 7 t₄]
  refine ⟨f4PeirceExp 1 7 t₄ * (f₃ * (f₂ * f₁)),
    e6F4InChevalley.mul_mem (f4PeirceExp_mem_f4 1 7 t₄) (e6F4InChevalley.mul_mem hf₃
      (e6F4InChevalley.mul_mem hf₂ hf₁)),
    hdf_all, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hact_x]; refine zorn_eq_of_zornCoord_eq fun k => ?_
    rw [(zornCoord_eq_zero_iff 0).mpr rfl k]
    fin_cases k
    · change zornCoord ((f4PeirceExp 1 7 t₄).1 X₃).b 0 = 0; rw [hb0₄, hb0₃]
    · exact (hbmid₄ 0).trans (hbmid₃ 0)
    · exact (hbmid₄ 1).trans (hbmid₃ 1)
    · exact (hbmid₄ 2).trans (hbmid₃ 2)
    · exact (hbmid₄ 3).trans (hbmid₃ 3)
    · exact (hbmid₄ 4).trans (hbmid₃ 4)
    · exact (hbmid₄ 5).trans (hbmid₃ 5)
    · change zornCoord ((f4PeirceExp 1 7 t₄).1 X₃).b 7 = 0
      rw [hb7₄, hb0₃, mul_zero, sub_zero]; dsimp [t₄]; field_simp [hX3_ne]; ring
  · rw [hact_x, h1₄, h1₃]
  · rw [hact_x]; exact ha₄
  · rw [hact_x]; exact hc₄
  · rw [hact_x, h23₄, hsum₃, hsum₂, hsum₁]

private theorem f4_reduce_diag2_fixing_diag1 {f : h3zornReducedStructureGroup}
    (hf : f.1 1 = 1) (hf1 : f.1 h3_diag₁ = h3_diag₁) :
    ∃ g ∈ e6F4InChevalley, g.1 h3_diag₁ = h3_diag₁ ∧ g.1 (f.1 h3_diag₂) = h3_diag₂ := by
  let e := f.1 h3_diag₂
  have he : isRankOneIdem e :=
    jordanAut_preserves_isRankOneIdem (h3zornJordanAutOfReducedStructure f hf) h3_diag₂_isRankOneIdem
  have hmul : h3_diag₁ * e = 0 := by
    let A := h3zornJordanAutOfReducedStructure f hf
    have hmul0 : h3_diag₁ * h3_diag₂ = 0 := h3_diag₁_mul_h3_diag₂
    have hA : A (h3_diag₁ * h3_diag₂) = A h3_diag₁ * A h3_diag₂ := A.map_mul h3_diag₁ h3_diag₂
    change f.1 (h3_diag₁ * h3_diag₂) = f.1 h3_diag₁ * f.1 h3_diag₂ at hA
    rw [hmul0, map_zero, hf1] at hA
    exact hA.symm
  obtain ⟨he1, hea, hec⟩ := eq_J23_of_diag1_mul_zero_cb hmul
  have hsum : e.α₂ + e.α₃ ≠ 0 := by
    have htr := he.2.1
    change e.α₁ + e.α₂ + e.α₃ = 1 at htr
    rw [he1, zero_add] at htr
    rw [htr]; norm_num
  obtain ⟨g₁, hg₁, hg1_d, hb₁, h1₁, ha₁, hc₁, hsum₁⟩ := f4_clear_b_fix_diag1 e he he1 hea hec hsum
  let e₁ := g₁.1 e
  have he₁ : isRankOneIdem e₁ := f4InChevalley_preserves_isRankOneIdem hg₁ he
  have hsum_e1 : e₁.α₂ + e₁.α₃ = 1 := by
    have htr := he₁.2.1
    change e₁.α₁ + e₁.α₂ + e₁.α₃ = 1 at htr
    rw [h1₁, zero_add] at htr
    exact htr
  have hmul_e1 : e₁.α₂ * e₁.α₃ = 0 := by
    have hn := (isRankOneIdem_norm_eq he₁).2.1
    rw [hb₁, show (0 : ZornVectorMatrix ℝ) = ZornVectorMatrix.zero from rfl,
      ZornVectorMatrix.norm_zero] at hn
    exact hn
  have h1' : e₁.α₁ = 0 := h1₁
  have ha1' : e₁.a = 0 := ha₁
  have hb1' : e₁.b = 0 := hb₁
  have hc1' : e₁.c = 0 := hc₁
  have he1_def : e₁ = g₁.1 e := rfl
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  by_cases hα2 : e₁.α₂ = 0
  · have hw_res : w23.1 e₁ = h3_diag₂ := by
      obtain ⟨d1, d2, d3, hac, _, _, _⟩ := w23_coords e₁
      obtain ⟨da', dc'⟩ := hac ha1' hc1'
      have db' := (w23_preserves_ab_zero ha1' hb1').1
      have hα3 : e₁.α₃ = 1 := by rw [hα2, zero_add] at hsum_e1; exact hsum_e1
      apply ext_h3
      · rw [d1, h1']; rfl
      · rw [d2, hα3]; rfl
      · rw [d3, hα2]; rfl
      · exact da'
      · exact db'
      · exact dc'
    refine ⟨w23 * g₁, e6F4InChevalley.mul_mem w23_mem_f4 hg₁, ?_, ?_⟩
    · rw [hmul_act, hg1_d, w23_fix_diag1]
    · rw [hmul_act, ← he1_def]; exact hw_res
  · refine ⟨g₁, hg₁, hg1_d, ?_⟩
    have hα3 : e₁.α₃ = 0 := (mul_eq_zero.mp hmul_e1).resolve_left hα2
    have hα2_one : e₁.α₂ = 1 := by rw [hα3, add_zero] at hsum_e1; exact hsum_e1
    apply ext_h3
    · change e₁.α₁ = _; rw [h1']; rfl
    · change e₁.α₂ = _; rw [hα2_one]; rfl
    · change e₁.α₃ = _; rw [hα3]; rfl
    · exact ha1'
    · exact hb1'
    · exact hc1'

/-! #### Step B3: Diagonal-pair reduction, `J₁₂`/`J₂₃` unit reduction, and Cartan triality -/

private def embedJ12_cb (x : ZornVectorMatrix ℝ) : H3Zorn ℝ :=
  ⟨0, 0, 0, x, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

private def embedJ23_cb (y : ZornVectorMatrix ℝ) : H3Zorn ℝ :=
  ⟨0, 0, 0, ZornVectorMatrix.zero, y, ZornVectorMatrix.zero⟩

private def embedJ31_cb (z : ZornVectorMatrix ℝ) : H3Zorn ℝ :=
  ⟨0, 0, 0, ZornVectorMatrix.zero, ZornVectorMatrix.zero, z⟩

private def zornBilin_cb (x y : ZornVectorMatrix ℝ) : ℝ :=
  ZornVectorMatrix.trace (ZornVectorMatrix.mul x (ZornVectorMatrix.conj y))

private theorem zornBilin_cb_symm (x y : ZornVectorMatrix ℝ) :
    zornBilin_cb x y = zornBilin_cb y x :=
  ZornVectorMatrix.trace_mul_conj_comm x y

private theorem zornBilin_cb_self (x : ZornVectorMatrix ℝ) :
    zornBilin_cb x x = 2 * ZornVectorMatrix.norm x := by
  have hn := ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj x x
  have hadd : ZornVectorMatrix.add x x = ZornVectorMatrix.smul 2 x := by
    ext i <;> simp [ZornVectorMatrix.add, ZornVectorMatrix.smul] <;> ring
  change (ZornVectorMatrix.add x x).norm = x.norm + x.norm + zornBilin_cb x x at hn
  rw [hadd, ZornVectorMatrix.norm_smul] at hn
  linarith [hn]

private theorem h3_diag₂_mul_eq_cb (X : H3Zorn ℝ) :
    h3_diag₂ * X =
      { α₁ := 0, α₂ := X.α₂, α₃ := 0
        a := (1 / 2 : ℝ) • X.a, b := (1 / 2 : ℝ) • X.b, c := 0 } := by
  change candidateJordanMul h3_diag₂ X = _
  rw [candidateJordanMul_trace_formula]
  have hcp : H3Zorn.crossProduct h3_diag₂ X =
      { α₁ := X.α₃, α₂ := 0, α₃ := X.α₁, a := 0, b := 0, c := -X.c } := by
    change H3Zorn.crossProduct (diagCartan 0 1 0) X = _
    rw [crossProduct_diagCartan_left]
    apply ext_h3
    · ring
    · ring
    · ring
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg]
  rw [hcp]
  apply ext_h3
  · simp [h3_diag₂, linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · simp [h3_diag₂, linearTrace, add_readback, sub_readback, smul_readback, one_readback]; ring
  · simp [h3_diag₂, linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · ext i <;> simp [h3_diag₂, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · ext i <;> simp [h3_diag₂, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · ext i <;> simp [h3_diag₂, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]

private theorem h3_diag₃_mul_eq_cb (X : H3Zorn ℝ) :
    h3_diag₃ * X =
      { α₁ := 0, α₂ := 0, α₃ := X.α₃
        a := 0, b := (1 / 2 : ℝ) • X.b, c := (1 / 2 : ℝ) • X.c } := by
  change candidateJordanMul h3_diag₃ X = _
  rw [candidateJordanMul_trace_formula]
  have hcp : H3Zorn.crossProduct h3_diag₃ X =
      { α₁ := X.α₂, α₂ := X.α₁, α₃ := 0, a := -X.a, b := 0, c := 0 } := by
    change H3Zorn.crossProduct (diagCartan 0 0 1) X = _
    rw [crossProduct_diagCartan_left]
    apply ext_h3
    · ring
    · ring
    · ring
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg]
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
  rw [hcp]
  apply ext_h3
  · simp [h3_diag₃, linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · simp [h3_diag₃, linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · simp [h3_diag₃, linearTrace, add_readback, sub_readback, smul_readback, one_readback]; ring
  · ext i <;> simp [h3_diag₃, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · ext i <;> simp [h3_diag₃, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · ext i <;> simp [h3_diag₃, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]

private theorem embedJ12_mul_embedJ12_cb (x y : ZornVectorMatrix ℝ) :
    embedJ12_cb x * embedJ12_cb y = ((1 / 2 : ℝ) * zornBilin_cb x y) • (h3_diag₁ + h3_diag₂) := by
  change candidateJordanMul (embedJ12_cb x) (embedJ12_cb y) = _
  rw [candidateJordanMul_trace_formula]
  have hlt1 : linearTrace (embedJ12_cb x) = 0 := by simp [linearTrace, embedJ12_cb]
  have hlt2 : linearTrace (embedJ12_cb y) = 0 := by simp [linearTrace, embedJ12_cb]
  have hcp : H3Zorn.crossProduct (embedJ12_cb x) (embedJ12_cb y) =
      { α₁ := 0, α₂ := 0, α₃ := -zornBilin_cb x y, a := 0, b := 0, c := 0 } := by
    have hn := ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj x y
    change (x.add y).norm = x.norm + y.norm + zornBilin_cb x y at hn
    apply ext_h3
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ12_cb, sub_readback, add_readback]
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ12_cb, sub_readback, add_readback]
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ12_cb, sub_readback, add_readback]
      linarith
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ12_cb, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ12_cb, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ12_cb, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  rw [hlt1, hlt2, hcp]
  apply ext_h3 <;> simp [linearTrace, h3_diag₁, h3_diag₂, add_readback,
    smul_readback, one_readback, ZornVectorMatrix.add_zero, ZornVectorMatrix.smul_zero]

private theorem embedJ23_mul_embedJ23_cb (x y : ZornVectorMatrix ℝ) :
    embedJ23_cb x * embedJ23_cb y = ((1 / 2 : ℝ) * zornBilin_cb x y) • (h3_diag₂ + h3_diag₃) := by
  change candidateJordanMul (embedJ23_cb x) (embedJ23_cb y) = _
  rw [candidateJordanMul_trace_formula]
  have hlt1 : linearTrace (embedJ23_cb x) = 0 := by simp [linearTrace, embedJ23_cb]
  have hlt2 : linearTrace (embedJ23_cb y) = 0 := by simp [linearTrace, embedJ23_cb]
  have hcp : H3Zorn.crossProduct (embedJ23_cb x) (embedJ23_cb y) =
      { α₁ := -zornBilin_cb x y, α₂ := 0, α₃ := 0, a := 0, b := 0, c := 0 } := by
    have hn := ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj x y
    change (x.add y).norm = x.norm + y.norm + zornBilin_cb x y at hn
    apply ext_h3
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ23_cb, sub_readback, add_readback]
      linarith
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ23_cb, sub_readback, add_readback]
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ23_cb, sub_readback, add_readback]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ23_cb, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ23_cb, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ23_cb, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  rw [hlt1, hlt2, hcp]
  apply ext_h3 <;> simp [linearTrace, h3_diag₂, h3_diag₃, add_readback,
    smul_readback, one_readback, ZornVectorMatrix.add_zero, ZornVectorMatrix.smul_zero]

private theorem embedJ31_mul_embedJ31_cb (x y : ZornVectorMatrix ℝ) :
    embedJ31_cb x * embedJ31_cb y = ((1 / 2 : ℝ) * zornBilin_cb x y) • (h3_diag₃ + h3_diag₁) := by
  change candidateJordanMul (embedJ31_cb x) (embedJ31_cb y) = _
  rw [candidateJordanMul_trace_formula]
  have hlt1 : linearTrace (embedJ31_cb x) = 0 := by simp [linearTrace, embedJ31_cb]
  have hlt2 : linearTrace (embedJ31_cb y) = 0 := by simp [linearTrace, embedJ31_cb]
  have hcp : H3Zorn.crossProduct (embedJ31_cb x) (embedJ31_cb y) =
      { α₁ := 0, α₂ := -zornBilin_cb x y, α₃ := 0, a := 0, b := 0, c := 0 } := by
    have hn := ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj x y
    change (x.add y).norm = x.norm + y.norm + zornBilin_cb x y at hn
    apply ext_h3
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ31_cb, sub_readback, add_readback]
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ31_cb, sub_readback, add_readback]
      linarith
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ31_cb, sub_readback, add_readback]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ31_cb, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ31_cb, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ31_cb, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  rw [hlt1, hlt2, hcp]
  apply ext_h3 <;> simp [linearTrace, h3_diag₃, h3_diag₁, add_readback,
    smul_readback, one_readback, ZornVectorMatrix.add_zero, ZornVectorMatrix.smul_zero]

private theorem embedJ12_mul_embedJ23_cb (x y : ZornVectorMatrix ℝ) :
    embedJ12_cb x * embedJ23_cb y =
      (1 / 2 : ℝ) • embedJ31_cb (ZornVectorMatrix.mul (ZornVectorMatrix.conj y) (ZornVectorMatrix.conj x)) := by
  change candidateJordanMul (embedJ12_cb x) (embedJ23_cb y) = _
  rw [candidateJordanMul_trace_formula]
  have hlt1 : linearTrace (embedJ12_cb x) = 0 := by simp [linearTrace, embedJ12_cb]
  have hlt2 : linearTrace (embedJ23_cb y) = 0 := by simp [linearTrace, embedJ23_cb]
  have hcp : H3Zorn.crossProduct (embedJ12_cb x) (embedJ23_cb y) =
      embedJ31_cb (ZornVectorMatrix.mul (ZornVectorMatrix.conj y) (ZornVectorMatrix.conj x)) := by
    apply ext_h3 <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ12_cb, embedJ23_cb, embedJ31_cb,
      sub_readback, add_readback, ZornVectorMatrix.norm_zero, ZornVectorMatrix.conj_zero,
      ZornVectorMatrix.zero_mul, ZornVectorMatrix.mul_zero, ZornVectorMatrix.smul_zero,
      ZornVectorMatrix.sub_zero, ZornVectorMatrix.add_zero]
  rw [hlt1, hlt2, hcp]
  apply ext_h3 <;> simp [linearTrace, embedJ31_cb, add_readback, smul_readback,
    one_readback, ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]

private theorem embedJ23_mul_embedJ31_cb (y z : ZornVectorMatrix ℝ) :
    embedJ23_cb y * embedJ31_cb z =
      (1 / 2 : ℝ) • embedJ12_cb (ZornVectorMatrix.mul (ZornVectorMatrix.conj z) (ZornVectorMatrix.conj y)) := by
  change candidateJordanMul (embedJ23_cb y) (embedJ31_cb z) = _
  rw [candidateJordanMul_trace_formula]
  have hlt1 : linearTrace (embedJ23_cb y) = 0 := by simp [linearTrace, embedJ23_cb]
  have hlt2 : linearTrace (embedJ31_cb z) = 0 := by simp [linearTrace, embedJ31_cb]
  have hcp : H3Zorn.crossProduct (embedJ23_cb y) (embedJ31_cb z) =
      embedJ12_cb (ZornVectorMatrix.mul (ZornVectorMatrix.conj z) (ZornVectorMatrix.conj y)) := by
    apply ext_h3 <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ12_cb, embedJ23_cb, embedJ31_cb,
      sub_readback, add_readback, ZornVectorMatrix.norm_zero, ZornVectorMatrix.conj_zero,
      ZornVectorMatrix.zero_mul, ZornVectorMatrix.mul_zero, ZornVectorMatrix.smul_zero,
      ZornVectorMatrix.sub_zero, ZornVectorMatrix.add_zero]
  rw [hlt1, hlt2, hcp]
  apply ext_h3 <;> simp [linearTrace, embedJ12_cb, add_readback, smul_readback,
    one_readback, ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]

private theorem embedJ31_mul_embedJ12_cb (z x : ZornVectorMatrix ℝ) :
    embedJ31_cb z * embedJ12_cb x =
      (1 / 2 : ℝ) • embedJ23_cb (ZornVectorMatrix.mul (ZornVectorMatrix.conj x) (ZornVectorMatrix.conj z)) := by
  change candidateJordanMul (embedJ31_cb z) (embedJ12_cb x) = _
  rw [candidateJordanMul_trace_formula]
  have hlt1 : linearTrace (embedJ31_cb z) = 0 := by simp [linearTrace, embedJ31_cb]
  have hlt2 : linearTrace (embedJ12_cb x) = 0 := by simp [linearTrace, embedJ12_cb]
  have hcp : H3Zorn.crossProduct (embedJ31_cb z) (embedJ12_cb x) =
      embedJ23_cb (ZornVectorMatrix.mul (ZornVectorMatrix.conj x) (ZornVectorMatrix.conj z)) := by
    apply ext_h3 <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ12_cb, embedJ23_cb, embedJ31_cb,
      sub_readback, add_readback, ZornVectorMatrix.norm_zero, ZornVectorMatrix.conj_zero,
      ZornVectorMatrix.zero_mul, ZornVectorMatrix.mul_zero, ZornVectorMatrix.smul_zero,
      ZornVectorMatrix.sub_zero, ZornVectorMatrix.add_zero]
  rw [hlt1, hlt2, hcp]
  apply ext_h3 <;> simp [linearTrace, embedJ23_cb, add_readback, smul_readback,
    one_readback, ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]

private theorem peirce_spaces_preserved_of_fix_diags (A : H3ZornJordanAut)
    (h1 : A h3_diag₁ = h3_diag₁) (h2 : A h3_diag₂ = h3_diag₂) (h3 : A h3_diag₃ = h3_diag₃) :
    (∀ x : ZornVectorMatrix ℝ, A (embedJ12_cb x) = embedJ12_cb (A (embedJ12_cb x)).a) ∧
    (∀ y : ZornVectorMatrix ℝ, A (embedJ23_cb y) = embedJ23_cb (A (embedJ23_cb y)).b) ∧
    (∀ z : ZornVectorMatrix ℝ, A (embedJ31_cb z) = embedJ31_cb (A (embedJ31_cb z)).c) := by
  refine ⟨fun x => ?_, fun y => ?_, fun z => ?_⟩
  · let Y := A (embedJ12_cb x)
    have hm1 : h3_diag₁ * Y = (1 / 2 : ℝ) • Y := by
      have hm : h3_diag₁ * embedJ12_cb x = (1 / 2 : ℝ) • embedJ12_cb x := by
        rw [h3_diag₁_mul_eq_cb]; apply ext_h3 <;> simp [embedJ12_cb, smul_readback, ZornVectorMatrix.smul_zero]
      calc h3_diag₁ * Y = A h3_diag₁ * A (embedJ12_cb x) := by rw [h1]
        _ = A (h3_diag₁ * embedJ12_cb x) := (A.map_mul _ _).symm
        _ = (1 / 2 : ℝ) • Y := by rw [hm, A.1.map_smul]
    have hm2 : h3_diag₂ * Y = (1 / 2 : ℝ) • Y := by
      have hm : h3_diag₂ * embedJ12_cb x = (1 / 2 : ℝ) • embedJ12_cb x := by
        rw [h3_diag₂_mul_eq_cb]; apply ext_h3 <;> simp [embedJ12_cb, smul_readback, ZornVectorMatrix.smul_zero]
      calc h3_diag₂ * Y = A h3_diag₂ * A (embedJ12_cb x) := by rw [h2]
        _ = A (h3_diag₂ * embedJ12_cb x) := (A.map_mul _ _).symm
        _ = (1 / 2 : ℝ) • Y := by rw [hm, A.1.map_smul]
    have hm3 : h3_diag₃ * Y = 0 := by
      have hm : h3_diag₃ * embedJ12_cb x = 0 := by
        rw [h3_diag₃_mul_eq_cb]; apply ext_h3 <;> simp [embedJ12_cb, ZornVectorMatrix.smul_zero]
      calc h3_diag₃ * Y = A h3_diag₃ * A (embedJ12_cb x) := by rw [h3]
        _ = A (h3_diag₃ * embedJ12_cb x) := (A.map_mul _ _).symm
        _ = 0 := by rw [hm, map_zero]
    rw [h3_diag₁_mul_eq_cb] at hm1
    rw [h3_diag₂_mul_eq_cb] at hm2
    rw [h3_diag₃_mul_eq_cb] at hm3
    have ha1 : Y.α₁ = 0 := by
      have hα := congrArg H3Zorn.α₁ hm1
      change Y.α₁ = (1 / 2 : ℝ) * Y.α₁ at hα; linarith
    have ha2 : Y.α₂ = 0 := by
      have hα := congrArg H3Zorn.α₂ hm2
      change Y.α₂ = (1 / 2 : ℝ) * Y.α₂ at hα; linarith
    have ha3 : Y.α₃ = 0 := congrArg H3Zorn.α₃ hm3
    have hb : Y.b = 0 := zorn_eq_zero_of_half_smul_eq_zero_cb (congrArg H3Zorn.b hm3)
    have hc : Y.c = 0 := zorn_eq_zero_of_half_smul_eq_zero_cb (congrArg H3Zorn.c hm3)
    apply ext_h3
    · exact ha1
    · exact ha2
    · exact ha3
    · rfl
    · exact hb
    · exact hc
  · let Y := A (embedJ23_cb y)
    have hm1 : h3_diag₁ * Y = 0 := by
      have hm : h3_diag₁ * embedJ23_cb y = 0 := by
        rw [h3_diag₁_mul_eq_cb]; apply ext_h3 <;> simp [embedJ23_cb, ZornVectorMatrix.smul_zero]
      calc h3_diag₁ * Y = A h3_diag₁ * A (embedJ23_cb y) := by rw [h1]
        _ = A (h3_diag₁ * embedJ23_cb y) := (A.map_mul _ _).symm
        _ = 0 := by rw [hm, map_zero]
    have hm2 : h3_diag₂ * Y = (1 / 2 : ℝ) • Y := by
      have hm : h3_diag₂ * embedJ23_cb y = (1 / 2 : ℝ) • embedJ23_cb y := by
        rw [h3_diag₂_mul_eq_cb]; apply ext_h3 <;> simp [embedJ23_cb, smul_readback, ZornVectorMatrix.smul_zero]
      calc h3_diag₂ * Y = A h3_diag₂ * A (embedJ23_cb y) := by rw [h2]
        _ = A (h3_diag₂ * embedJ23_cb y) := (A.map_mul _ _).symm
        _ = (1 / 2 : ℝ) • Y := by rw [hm, A.1.map_smul]
    have hm3 : h3_diag₃ * Y = (1 / 2 : ℝ) • Y := by
      have hm : h3_diag₃ * embedJ23_cb y = (1 / 2 : ℝ) • embedJ23_cb y := by
        rw [h3_diag₃_mul_eq_cb]; apply ext_h3 <;> simp [embedJ23_cb, smul_readback, ZornVectorMatrix.smul_zero]
      calc h3_diag₃ * Y = A h3_diag₃ * A (embedJ23_cb y) := by rw [h3]
        _ = A (h3_diag₃ * embedJ23_cb y) := (A.map_mul _ _).symm
        _ = (1 / 2 : ℝ) • Y := by rw [hm, A.1.map_smul]
    rw [h3_diag₁_mul_eq_cb] at hm1
    rw [h3_diag₂_mul_eq_cb] at hm2
    rw [h3_diag₃_mul_eq_cb] at hm3
    have ha1 : Y.α₁ = 0 := congrArg H3Zorn.α₁ hm1
    have ha2 : Y.α₂ = 0 := by
      have hα := congrArg H3Zorn.α₂ hm2
      change Y.α₂ = (1 / 2 : ℝ) * Y.α₂ at hα; linarith
    have ha3 : Y.α₃ = 0 := by
      have hα := congrArg H3Zorn.α₃ hm3
      change Y.α₃ = (1 / 2 : ℝ) * Y.α₃ at hα; linarith
    have ha : Y.a = 0 := zorn_eq_zero_of_half_smul_eq_zero_cb (congrArg H3Zorn.a hm1)
    have hc : Y.c = 0 := zorn_eq_zero_of_half_smul_eq_zero_cb (congrArg H3Zorn.c hm1)
    apply ext_h3
    · exact ha1
    · exact ha2
    · exact ha3
    · exact ha
    · rfl
    · exact hc
  · let Y := A (embedJ31_cb z)
    have hm2 : h3_diag₂ * Y = 0 := by
      have hm : h3_diag₂ * embedJ31_cb z = 0 := by
        rw [h3_diag₂_mul_eq_cb]; apply ext_h3 <;> simp [embedJ31_cb, ZornVectorMatrix.smul_zero]
      calc h3_diag₂ * Y = A h3_diag₂ * A (embedJ31_cb z) := by rw [h2]
        _ = A (h3_diag₂ * embedJ31_cb z) := (A.map_mul _ _).symm
        _ = 0 := by rw [hm, map_zero]
    have hm1 : h3_diag₁ * Y = (1 / 2 : ℝ) • Y := by
      have hm : h3_diag₁ * embedJ31_cb z = (1 / 2 : ℝ) • embedJ31_cb z := by
        rw [h3_diag₁_mul_eq_cb]; apply ext_h3 <;> simp [embedJ31_cb, smul_readback, ZornVectorMatrix.smul_zero]
      calc h3_diag₁ * Y = A h3_diag₁ * A (embedJ31_cb z) := by rw [h1]
        _ = A (h3_diag₁ * embedJ31_cb z) := (A.map_mul _ _).symm
        _ = (1 / 2 : ℝ) • Y := by rw [hm, A.1.map_smul]
    have hm3 : h3_diag₃ * Y = (1 / 2 : ℝ) • Y := by
      have hm : h3_diag₃ * embedJ31_cb z = (1 / 2 : ℝ) • embedJ31_cb z := by
        rw [h3_diag₃_mul_eq_cb]; apply ext_h3 <;> simp [embedJ31_cb, smul_readback, ZornVectorMatrix.smul_zero]
      calc h3_diag₃ * Y = A h3_diag₃ * A (embedJ31_cb z) := by rw [h3]
        _ = A (h3_diag₃ * embedJ31_cb z) := (A.map_mul _ _).symm
        _ = (1 / 2 : ℝ) • Y := by rw [hm, A.1.map_smul]
    rw [h3_diag₁_mul_eq_cb] at hm1
    rw [h3_diag₂_mul_eq_cb] at hm2
    rw [h3_diag₃_mul_eq_cb] at hm3
    have ha1 : Y.α₁ = 0 := by
      have hα := congrArg H3Zorn.α₁ hm1
      change Y.α₁ = (1 / 2 : ℝ) * Y.α₁ at hα; linarith
    have ha2 : Y.α₂ = 0 := congrArg H3Zorn.α₂ hm2
    have ha3 : Y.α₃ = 0 := by
      have hα := congrArg H3Zorn.α₃ hm3
      change Y.α₃ = (1 / 2 : ℝ) * Y.α₃ at hα; linarith
    have ha : Y.a = 0 := zorn_eq_zero_of_half_smul_eq_zero_cb (congrArg H3Zorn.a hm2)
    have hb : Y.b = 0 := zorn_eq_zero_of_half_smul_eq_zero_cb (congrArg H3Zorn.b hm2)
    apply ext_h3
    · exact ha1
    · exact ha2
    · exact ha3
    · exact ha
    · exact hb
    · rfl

private theorem f4_reduce_j12_one_fixing_diags (x : ZornVectorMatrix ℝ) (hx : x.norm = 1) :
    ∃ d ∈ d4Subgroup, (d.1 (embedJ12_cb x)).a = ZornVectorMatrix.one := by
  let X₀ := embedJ12_cb x
  -- Step 1: ensure a₀ ≠ 0
  have hs1 : ∃ d₁ ∈ d4Subgroup, zornCoord (d₁.1 X₀).a 0 ≠ 0 := by
    by_cases ha0 : zornCoord X₀.a 0 ≠ 0
    · exact ⟨1, d4Subgroup.one_mem, ha0⟩
    · push Not at ha0
      have hnorm : ZornVectorMatrix.norm x = 1 := hx
      rw [zorn_norm_zornCoord] at hnorm
      have ha0x : zornCoord x 0 = 0 := ha0
      rw [ha0x, zero_mul, zero_sub] at hnorm
      have hsum_neg : zornCoord x 1 * zornCoord x 4 + zornCoord x 2 * zornCoord x 5 +
          zornCoord x 3 * zornCoord x 6 = -1 := by linarith [hnorm]
      have hexj : ∃ j : Fin 6, zornCoord X₀.a (aMidOppIdx j) ≠ 0 := by
        rcases choose_nonzero_of_one_neg_sum_cb hsum_neg with h | h | h
        · exact ⟨3, h⟩
        · exact ⟨4, h⟩
        · exact ⟨5, h⟩
      obtain ⟨j, hj⟩ := hexj
      obtain ⟨_, _, _, ga0, _, _⟩ := d4_aPullRoot_coords j 1 X₀
      refine ⟨e6RootExp (aPullRoot j) 1,
        Subgroup.subset_closure ⟨aPullRoot j, d4_aPullRoot_lt24 j, 1, rfl⟩, ?_⟩
      rw [ga0, ha0, zero_sub, one_mul, neg_ne_zero]
      exact hj
  obtain ⟨d₁, hd₁, ha0_ne⟩ := hs1
  let X₁ := d₁.1 X₀
  -- Step 2: clear a₁..a₆ using aMidRoot 0..5 while keeping a₀ fixed
  have hmid_step : ∀ (j : Fin 6) (Z : H3Zorn ℝ), zornCoord Z.a 0 ≠ 0 →
      ∃ g ∈ d4Subgroup,
        zornCoord (g.1 Z).a 0 = zornCoord Z.a 0 ∧
        zornCoord (g.1 Z).a ⟨1 + j.val, by omega⟩ = 0 ∧
        (∀ i : Fin 6, i ≠ j →
          zornCoord (g.1 Z).a ⟨1 + i.val, by omega⟩ = zornCoord Z.a ⟨1 + i.val, by omega⟩) := by
    intro j Z hz0
    let t := -zornCoord Z.a ⟨1 + j.val, by omega⟩ / zornCoord Z.a 0
    refine ⟨e6RootExp (aMidRoot j) t,
      Subgroup.subset_closure ⟨aMidRoot j, d4_aMidRoot_lt24 j, t, rfl⟩, ?_⟩
    obtain ⟨_, _, _, ga0, _, gmid⟩ := d4_aMidRoot_coords j t Z
    refine ⟨ga0, ?_, fun i hij => ?_⟩
    · rw [gmid j]; simp only [↓reduceIte]; dsimp [t]; field_simp [hz0]; ring
    · rw [gmid i]; simp [hij]
  obtain ⟨q0, hq0, ha0_0, m0, mo0⟩ := hmid_step 0 X₁ ha0_ne
  have ha0_0n : zornCoord (q0.1 X₁).a 0 ≠ 0 := by rw [ha0_0]; exact ha0_ne
  obtain ⟨q1, hq1, ha0_1, m1, mo1⟩ := hmid_step 1 (q0.1 X₁) ha0_0n
  have ha0_1n : zornCoord (q1.1 (q0.1 X₁)).a 0 ≠ 0 := by rw [ha0_1]; exact ha0_0n
  obtain ⟨q2, hq2, ha0_2, m2, mo2⟩ := hmid_step 2 (q1.1 (q0.1 X₁)) ha0_1n
  have ha0_2n : zornCoord (q2.1 (q1.1 (q0.1 X₁))).a 0 ≠ 0 := by rw [ha0_2]; exact ha0_1n
  obtain ⟨q3, hq3, ha0_3, m3, mo3⟩ := hmid_step 3 (q2.1 (q1.1 (q0.1 X₁))) ha0_2n
  have ha0_3n : zornCoord (q3.1 (q2.1 (q1.1 (q0.1 X₁)))).a 0 ≠ 0 := by rw [ha0_3]; exact ha0_2n
  obtain ⟨q4, hq4, ha0_4, m4, mo4⟩ := hmid_step 4 (q3.1 (q2.1 (q1.1 (q0.1 X₁)))) ha0_3n
  have ha0_4n : zornCoord (q4.1 (q3.1 (q2.1 (q1.1 (q0.1 X₁))))).a 0 ≠ 0 := by rw [ha0_4]; exact ha0_3n
  obtain ⟨q5, hq5, ha0_5, m5, mo5⟩ := hmid_step 5 (q4.1 (q3.1 (q2.1 (q1.1 (q0.1 X₁))))) ha0_4n
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  let qd := q5 * (q4 * (q3 * (q2 * (q1 * q0))))
  have hqd : qd ∈ d4Subgroup :=
    d4Subgroup.mul_mem hq5 (d4Subgroup.mul_mem hq4 (d4Subgroup.mul_mem hq3
      (d4Subgroup.mul_mem hq2 (d4Subgroup.mul_mem hq1 hq0))))
  have hqd_eq : qd.1 X₁ = q5.1 (q4.1 (q3.1 (q2.1 (q1.1 (q0.1 X₁))))) := by
    have ha1 : (q1 * q0).1 X₁ = q1.1 (q0.1 X₁) := rfl
    have ha2 : (q2 * (q1 * q0)).1 X₁ = q2.1 (q1.1 (q0.1 X₁)) := by rw [hmul_act, ha1]
    have ha3 : (q3 * (q2 * (q1 * q0))).1 X₁ = q3.1 (q2.1 (q1.1 (q0.1 X₁))) := by rw [hmul_act, ha2]
    have ha4 : (q4 * (q3 * (q2 * (q1 * q0)))).1 X₁ = q4.1 (q3.1 (q2.1 (q1.1 (q0.1 X₁)))) := by
      rw [hmul_act, ha3]
    rw [hmul_act, ha4]
  let X₂ := qd.1 X₁
  have h0_1 : (⟨1 + (0 : Fin 6).val, by omega⟩ : Fin 8) = 1 := rfl
  have h0_4 : (⟨1 + (3 : Fin 6).val, by omega⟩ : Fin 8) = 4 := rfl
  have hX2_a0 : zornCoord X₂.a 0 ≠ 0 := by
    change zornCoord (qd.1 X₁).a 0 ≠ 0; rw [hqd_eq, ha0_5]; exact ha0_4n
  have hX2_1 : zornCoord X₂.a 1 = 0 := by
    change zornCoord (qd.1 X₁).a ⟨1 + (0 : Fin 6).val, by omega⟩ = 0
    rw [hqd_eq, mo5 0 (by decide), mo4 0 (by decide), mo3 0 (by decide), mo2 0 (by decide),
      mo1 0 (by decide)]; exact m0
  have hX2_2 : zornCoord X₂.a 2 = 0 := by
    change zornCoord (qd.1 X₁).a ⟨1 + (1 : Fin 6).val, by omega⟩ = 0
    rw [hqd_eq, mo5 1 (by decide), mo4 1 (by decide), mo3 1 (by decide), mo2 1 (by decide)]
    exact m1
  have hX2_3 : zornCoord X₂.a 3 = 0 := by
    change zornCoord (qd.1 X₁).a ⟨1 + (2 : Fin 6).val, by omega⟩ = 0
    rw [hqd_eq, mo5 2 (by decide), mo4 2 (by decide), mo3 2 (by decide)]; exact m2
  have hX2_4 : zornCoord X₂.a 4 = 0 := by
    change zornCoord (qd.1 X₁).a ⟨1 + (3 : Fin 6).val, by omega⟩ = 0
    rw [hqd_eq, mo5 3 (by decide), mo4 3 (by decide)]; exact m3
  have hX2_5 : zornCoord X₂.a 5 = 0 := by
    change zornCoord (qd.1 X₁).a ⟨1 + (4 : Fin 6).val, by omega⟩ = 0
    rw [hqd_eq, mo5 4 (by decide)]; exact m4
  have hX2_6 : zornCoord X₂.a 6 = 0 := by
    change zornCoord (qd.1 X₁).a ⟨1 + (5 : Fin 6).val, by omega⟩ = 0
    rw [hqd_eq]; exact m5
  -- Norm of X₂.a is 1 since qd * d₁ ∈ e6F4InChevalley fixes h3_diag₁, h3_diag₂
  have hX2_norm : X₂.a.norm = 1 := by
    let df := qd * d₁
    have hdf_d4 : df ∈ d4Subgroup := d4Subgroup.mul_mem hqd hd₁
    have hdf_f4 : df ∈ e6F4InChevalley := d4Subgroup_le_f4InChevalley hdf_d4
    let A := h3zornJordanAutOfReducedStructure df hdf_f4.2
    have hfix := d4Subgroup_fix_diags hdf_d4
    have hblk := d4Subgroup_preserves_blocks hdf_d4 X₀
    have hX2_eq : df.1 (embedJ12_cb x) = embedJ12_cb X₂.a := by
      have hx0 : df.1 X₀ = X₂ := rfl
      rw [hx0]
      apply ext_h3
      · change (df.1 X₀).α₁ = 0; rw [hblk.1]; rfl
      · change (df.1 X₀).α₂ = 0; rw [hblk.2.1]; rfl
      · change (df.1 X₀).α₃ = 0; rw [hblk.2.2.1]; rfl
      · rfl
      · change (df.1 X₀).b = 0; rw [hblk.2.2.2.2.1]; rfl
      · change (df.1 X₀).c = 0; rw [hblk.2.2.2.2.2]; rfl
    have hsq := congrArg A (embedJ12_mul_embedJ12_cb x x)
    rw [A.map_mul, A.1.map_smul, map_add] at hsq
    change df.1 (embedJ12_cb x) * df.1 (embedJ12_cb x) =
      ((1 / 2 : ℝ) * zornBilin_cb x x) • (df.1 h3_diag₁ + df.1 h3_diag₂) at hsq
    rw [hX2_eq, embedJ12_mul_embedJ12_cb, hfix.1, hfix.2.1, zornBilin_cb_self, zornBilin_cb_self] at hsq
    have hα1 := congrArg H3Zorn.α₁ hsq
    simp only [smul_readback, add_readback, h3_diag₁, h3_diag₂, add_zero] at hα1
    linarith [hα1, hx]
  rw [zorn_norm_zornCoord, hX2_1, hX2_2, hX2_3, hX2_4, hX2_5, hX2_6] at hX2_norm
  have hX2_a7 : zornCoord X₂.a 7 = (zornCoord X₂.a 0)⁻¹ := by
    have hmul1 : zornCoord X₂.a 0 * zornCoord X₂.a 7 = 1 := by linarith [hX2_norm]
    field_simp [hX2_a0]
    linarith [hmul1]
  -- Step 3: apply Wa(a₀⁻¹) * Wa(-1) using r = 3 (aPullRoot 3) and r = 10 (aMidRoot 0)
  let lam := zornCoord X₂.a 0
  let s1 := e6RootExp (aPullRoot 3) 1
  let s2 := e6RootExp (aMidRoot 0) 1
  let s3 := e6RootExp (aPullRoot 3) 1
  let s4 := e6RootExp (aPullRoot 3) (-lam⁻¹)
  let s5 := e6RootExp (aMidRoot 0) (-lam)
  let s6 := e6RootExp (aPullRoot 3) (-lam⁻¹)
  let ss := s6 * (s5 * (s4 * (s3 * (s2 * s1))))
  have hs_d4 : ss ∈ d4Subgroup := by
    refine d4Subgroup.mul_mem ?_ (d4Subgroup.mul_mem ?_ (d4Subgroup.mul_mem ?_
      (d4Subgroup.mul_mem ?_ (d4Subgroup.mul_mem ?_ ?_)))) <;>
      exact Subgroup.subset_closure ⟨_, by decide, _, rfl⟩
  let Z1 := s1.1 X₂
  let Z2 := s2.1 Z1
  let Z3 := s3.1 Z2
  let Z4 := s4.1 Z3
  let Z5 := s5.1 Z4
  let Z6 := s6.1 Z5
  have hz1 := d4_aPullRoot_coords 3 1 X₂
  have hz2 := d4_aMidRoot_coords 0 1 Z1
  have hz3 := d4_aPullRoot_coords 3 1 Z2
  have hz4 := d4_aPullRoot_coords 3 (-lam⁻¹) Z3
  have hz5 := d4_aMidRoot_coords 0 (-lam) Z4
  have hz6 := d4_aPullRoot_coords 3 (-lam⁻¹) Z5
  have haOpp0 : aMidOppIdx 0 = 4 := rfl
  have haOpp3 : aMidOppIdx 3 = 1 := rfl
  have hlam_ne : lam ≠ 0 := hX2_a0
  have h1_0 : zornCoord Z1.a 0 = lam := by rw [hz1.2.2.2.1, haOpp3, hX2_1]; ring
  have h1_1 : zornCoord Z1.a 1 = 0 := by
    have h := hz1.2.2.2.2.2 0; rw [h0_1, ite_eq_right (by decide)] at h; rw [h, hX2_1]
  have h1_4 : zornCoord Z1.a 4 = -lam⁻¹ := by
    have h := hz1.2.2.2.2.2 3; rw [h0_4, ite_eq_left rfl] at h; rw [h, hX2_4, hX2_a7]; ring
  have h1_7 : zornCoord Z1.a 7 = lam⁻¹ := by rw [hz1.2.2.2.2.1]; exact hX2_a7
  have h2_0 : zornCoord Z2.a 0 = lam := by rw [hz2.2.2.2.1, h1_0]
  have h2_1 : zornCoord Z2.a 1 = lam := by
    have h := hz2.2.2.2.2.2 0; rw [h0_1, ite_eq_left rfl] at h; rw [h, h1_1, h1_0]; ring
  have h2_4 : zornCoord Z2.a 4 = -lam⁻¹ := by
    have h := hz2.2.2.2.2.2 3; rw [h0_4, ite_eq_right (by decide)] at h; rw [h, h1_4]
  have h2_7 : zornCoord Z2.a 7 = 0 := by
    rw [hz2.2.2.2.2.1, haOpp0, h1_7, h1_4]; ring
  have h3_0 : zornCoord Z3.a 0 = 0 := by
    rw [hz3.2.2.2.1, haOpp3, h2_0, h2_1]; ring
  have h3_1 : zornCoord Z3.a 1 = lam := by
    have h := hz3.2.2.2.2.2 0; rw [h0_1, ite_eq_right (by decide)] at h; rw [h, h2_1]
  have h3_4 : zornCoord Z3.a 4 = -lam⁻¹ := by
    have h := hz3.2.2.2.2.2 3; rw [h0_4, ite_eq_left rfl] at h; rw [h, h2_4, h2_7]; ring
  have h3_7 : zornCoord Z3.a 7 = 0 := by rw [hz3.2.2.2.2.1, h2_7]
  have h4_0 : zornCoord Z4.a 0 = 1 := by
    rw [hz4.2.2.2.1, haOpp3, h3_0, h3_1]; field_simp [hlam_ne]; ring
  have h4_1 : zornCoord Z4.a 1 = lam := by
    have h := hz4.2.2.2.2.2 0; rw [h0_1, ite_eq_right (by decide)] at h; rw [h, h3_1]
  have h4_4 : zornCoord Z4.a 4 = -lam⁻¹ := by
    have h := hz4.2.2.2.2.2 3; rw [h0_4, ite_eq_left rfl] at h; rw [h, h3_4, h3_7]; ring
  have h4_7 : zornCoord Z4.a 7 = 0 := by rw [hz4.2.2.2.2.1, h3_7]
  have h5_0 : zornCoord Z5.a 0 = 1 := by rw [hz5.2.2.2.1, h4_0]
  have h5_1 : zornCoord Z5.a 1 = 0 := by
    have h := hz5.2.2.2.2.2 0; rw [h0_1, ite_eq_left rfl] at h; rw [h, h4_1, h4_0]; ring
  have h5_4 : zornCoord Z5.a 4 = -lam⁻¹ := by
    have h := hz5.2.2.2.2.2 3; rw [h0_4, ite_eq_right (by decide)] at h; rw [h, h4_4]
  have h5_7 : zornCoord Z5.a 7 = 1 := by
    rw [hz5.2.2.2.2.1, haOpp0, h4_7, h4_4]; field_simp [hlam_ne]; ring
  have hZ6_0 : zornCoord Z6.a 0 = 1 := by
    rw [hz6.2.2.2.1, haOpp3, h5_0, h5_1]; ring
  have hZ6_7 : zornCoord Z6.a 7 = 1 := by
    rw [hz6.2.2.2.2.1, h5_7]
  have hZ6_mid : ∀ i : Fin 6, zornCoord Z6.a ⟨1 + i.val, by omega⟩ = 0 := by
    intro i
    fin_cases i <;> dsimp only
    · change zornCoord Z6.a 1 = 0
      have h := hz6.2.2.2.2.2 0; rw [h0_1, ite_eq_right (by decide)] at h; rw [h, h5_1]
    · change zornCoord Z6.a ⟨1 + (1 : Fin 6).val, by omega⟩ = 0
      have h6 := hz6.2.2.2.2.2 1; rw [ite_eq_right (by decide)] at h6
      have h5 := hz5.2.2.2.2.2 1; rw [ite_eq_right (by decide)] at h5
      have h4 := hz4.2.2.2.2.2 1; rw [ite_eq_right (by decide)] at h4
      have h3 := hz3.2.2.2.2.2 1; rw [ite_eq_right (by decide)] at h3
      have h2 := hz2.2.2.2.2.2 1; rw [ite_eq_right (by decide)] at h2
      have h1 := hz1.2.2.2.2.2 1; rw [ite_eq_right (by decide)] at h1
      rw [h6, h5, h4, h3, h2, h1]; exact hX2_2
    · change zornCoord Z6.a ⟨1 + (2 : Fin 6).val, by omega⟩ = 0
      have h6 := hz6.2.2.2.2.2 2; rw [ite_eq_right (by decide)] at h6
      have h5 := hz5.2.2.2.2.2 2; rw [ite_eq_right (by decide)] at h5
      have h4 := hz4.2.2.2.2.2 2; rw [ite_eq_right (by decide)] at h4
      have h3 := hz3.2.2.2.2.2 2; rw [ite_eq_right (by decide)] at h3
      have h2 := hz2.2.2.2.2.2 2; rw [ite_eq_right (by decide)] at h2
      have h1 := hz1.2.2.2.2.2 2; rw [ite_eq_right (by decide)] at h1
      rw [h6, h5, h4, h3, h2, h1]; exact hX2_3
    · change zornCoord Z6.a 4 = 0
      have h := hz6.2.2.2.2.2 3; rw [h0_4, ite_eq_left rfl] at h; rw [h, h5_4, h5_7]; ring
    · change zornCoord Z6.a ⟨1 + (4 : Fin 6).val, by omega⟩ = 0
      have h6 := hz6.2.2.2.2.2 4; rw [ite_eq_right (by decide)] at h6
      have h5 := hz5.2.2.2.2.2 4; rw [ite_eq_right (by decide)] at h5
      have h4 := hz4.2.2.2.2.2 4; rw [ite_eq_right (by decide)] at h4
      have h3 := hz3.2.2.2.2.2 4; rw [ite_eq_right (by decide)] at h3
      have h2 := hz2.2.2.2.2.2 4; rw [ite_eq_right (by decide)] at h2
      have h1 := hz1.2.2.2.2.2 4; rw [ite_eq_right (by decide)] at h1
      rw [h6, h5, h4, h3, h2, h1]; exact hX2_5
    · change zornCoord Z6.a ⟨1 + (5 : Fin 6).val, by omega⟩ = 0
      have h6 := hz6.2.2.2.2.2 5; rw [ite_eq_right (by decide)] at h6
      have h5 := hz5.2.2.2.2.2 5; rw [ite_eq_right (by decide)] at h5
      have h4 := hz4.2.2.2.2.2 5; rw [ite_eq_right (by decide)] at h4
      have h3 := hz3.2.2.2.2.2 5; rw [ite_eq_right (by decide)] at h3
      have h2 := hz2.2.2.2.2.2 5; rw [ite_eq_right (by decide)] at h2
      have h1 := hz1.2.2.2.2.2 5; rw [ite_eq_right (by decide)] at h1
      rw [h6, h5, h4, h3, h2, h1]; exact hX2_6
  refine ⟨ss * (qd * d₁), d4Subgroup.mul_mem hs_d4 (d4Subgroup.mul_mem hqd hd₁), ?_⟩
  have hact_s : ss.1 X₂ = Z6 := by
    have ha1 : (s2 * s1).1 X₂ = Z2 := rfl
    have ha2 : (s3 * (s2 * s1)).1 X₂ = Z3 := by rw [hmul_act, ha1]
    have ha3 : (s4 * (s3 * (s2 * s1))).1 X₂ = Z4 := by rw [hmul_act, ha2]
    have ha4 : (s5 * (s4 * (s3 * (s2 * s1)))).1 X₂ = Z5 := by rw [hmul_act, ha3]
    rw [hmul_act, ha4]
  have hact_all : (ss * (qd * d₁)).1 X₀ = Z6 := by
    have hqd_d1 : (qd * d₁).1 X₀ = X₂ := rfl
    rw [hmul_act, hqd_d1, hact_s]
  rw [hact_all]
  refine zorn_eq_of_zornCoord_eq fun k => ?_
  fin_cases k <;> dsimp only
  · exact hZ6_0
  · exact hZ6_mid 0
  · exact hZ6_mid 1
  · exact hZ6_mid 2
  · exact hZ6_mid 3
  · exact hZ6_mid 4
  · exact hZ6_mid 5
  · exact hZ6_7

private def bAddRoot (j : Fin 3) : Fin 72 := ![21, 19, 18] j

private def bAddSign (j : Fin 3) : ℝ := ![1, -1, 1] j

private def bPullRoot (j : Fin 3) : Fin 72 := ![11, 7, 6] j

private def bPullSign (j : Fin 3) : ℝ := ![-1, 1, -1] j

private theorem d4_j23_roots_lt24 :
    (∀ j : Fin 3, (bAddRoot j).val < 24) ∧ (∀ j : Fin 3, (bPullRoot j).val < 24) :=
  ⟨fun j => by fin_cases j <;> decide, fun j => by fin_cases j <;> decide⟩

private theorem d4_j23_roots_fix_j12_one :
    (∀ (j : Fin 3) (t : ℝ), (e6RootExp (bAddRoot j) t).1 (embedJ12_cb ZornVectorMatrix.one) =
      embedJ12_cb ZornVectorMatrix.one) ∧
    (∀ (j : Fin 3) (t : ℝ), (e6RootExp (bPullRoot j) t).1 (embedJ12_cb ZornVectorMatrix.one) =
      embedJ12_cb ZornVectorMatrix.one) := by
  have hc1 : (List.finRange 3).all (fun j => (List.finRange 27).all (fun m =>
      sparseVal (e6RootSparse (bAddRoot j)) m 3 +
        sparseVal (e6RootSparse (bAddRoot j)) m 10 == 0)) = true := by decide
  have hc2 : (List.finRange 3).all (fun j => (List.finRange 27).all (fun m =>
      sparseVal (e6RootSparse (bPullRoot j)) m 3 +
        sparseVal (e6RootSparse (bPullRoot j)) m 10 == 0)) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc1 hc2
  have hfix : ∀ (r : Fin 72) (t : ℝ),
      (∀ m : Fin 27, sparseVal (e6RootSparse r) m 3 + sparseVal (e6RootSparse r) m 10 = 0) →
      (e6RootExp r t).1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one := by
    intro r t hrz
    apply h3Zorn_ext_coord; intro m
    rw [h3ZornCoordinate_e6RootExp]
    have hs : ∑ k : Fin 27, (sparseVal (e6RootSparse r) m k : ℝ) *
        h3ZornCoordinate (embedJ12_cb ZornVectorMatrix.one) k = 0 := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun k : Fin 27 => k = 3 ∨ k = 10)]
      have hz : ∑ k ∈ Finset.univ.filter (fun k : Fin 27 => ¬(k = 3 ∨ k = 10)),
          (sparseVal (e6RootSparse r) m k : ℝ) *
            h3ZornCoordinate (embedJ12_cb ZornVectorMatrix.one) k = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hnk := (Finset.mem_filter.mp hk).2
        have hkz : h3ZornCoordinate (embedJ12_cb ZornVectorMatrix.one) k = 0 := by
          fin_cases k
          all_goals first | exact absurd (Or.inl rfl) hnk | exact absurd (Or.inr rfl) hnk | rfl
        rw [hkz, mul_zero]
      rw [hz, add_zero]
      have hf : Finset.univ.filter (fun k : Fin 27 => k = 3 ∨ k = 10) = {3, 10} := by decide
      rw [hf, Finset.sum_insert (by decide), Finset.sum_singleton]
      have h3 : h3ZornCoordinate (embedJ12_cb ZornVectorMatrix.one) 3 = 1 := rfl
      have h10 : h3ZornCoordinate (embedJ12_cb ZornVectorMatrix.one) 10 = 1 := rfl
      rw [h3, h10, mul_one, mul_one]
      exact_mod_cast hrz m
    rw [hs, mul_zero, add_zero]
  exact ⟨fun j t => hfix (bAddRoot j) t (hc1 j), fun j t => hfix (bPullRoot j) t (hc2 j)⟩

private theorem d4_bAddRoot_coords (j : Fin 3) (t : ℝ) (X : H3Zorn ℝ) :
    zornCoord ((e6RootExp (bAddRoot j) t).1 X).b 0 = zornCoord X.b 0 ∧
    zornCoord ((e6RootExp (bAddRoot j) t).1 X).b 7 =
      zornCoord X.b 7 + bAddSign j * t * zornCoord X.b ⟨4 + j.val, by omega⟩ ∧
    (∀ i : Fin 3, zornCoord ((e6RootExp (bAddRoot j) t).1 X).b ⟨1 + i.val, by omega⟩ =
      if i = j then zornCoord X.b ⟨1 + i.val, by omega⟩ + bAddSign j * t * zornCoord X.b 0
      else zornCoord X.b ⟨1 + i.val, by omega⟩) ∧
    (∀ i : Fin 3, zornCoord ((e6RootExp (bAddRoot j) t).1 X).b ⟨4 + i.val, by omega⟩ =
      zornCoord X.b ⟨4 + i.val, by omega⟩) := by
  have hj : (⟨j.val, by omega⟩ : Fin 6) = ⟨j.val, by omega⟩ := rfl
  have heq : bAddRoot j = bMidRoot ⟨j.val, by omega⟩ := by fin_cases j <;> rfl
  have hs : bAddSign j = bMidSign ⟨j.val, by omega⟩ := by fin_cases j <;> rfl
  have hopp : bMidOppIdx ⟨j.val, by omega⟩ = ⟨4 + j.val, by omega⟩ := by fin_cases j <;> rfl
  rw [heq, hs]
  obtain ⟨_, _, _, hb0, hb7, hbmid⟩ := d4_bMidRoot_coords ⟨j.val, by omega⟩ t X
  refine ⟨hb0, by rw [← hopp]; exact hb7, fun i => ?_, fun i => ?_⟩
  · have hi := hbmid ⟨i.val, by omega⟩
    by_cases hij : i = j
    · subst hij; simpa using hi
    · have hij' : (⟨i.val, by omega⟩ : Fin 6) ≠ ⟨j.val, by omega⟩ := fun h => hij (Fin.ext (by simp [Fin.ext_iff] at h; exact h))
      simp [hij, hij'] at hi ⊢; exact hi
  · have hi := hbmid ⟨3 + i.val, by omega⟩
    have hne : (⟨3 + i.val, by omega⟩ : Fin 6) ≠ ⟨j.val, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; dsimp at hv; omega
    simp only [hne, ↓reduceIte] at hi
    have hidx : (⟨1 + (⟨3 + i.val, by omega⟩ : Fin 6).val, by omega⟩ : Fin 8) = ⟨4 + i.val, by omega⟩ :=
      Fin.ext (by dsimp; omega)
    rw [← hidx]; exact hi

private theorem d4_bPullRoot_coords (j : Fin 3) (t : ℝ) (X : H3Zorn ℝ) :
    zornCoord ((e6RootExp (bPullRoot j) t).1 X).b 0 =
      zornCoord X.b 0 + bPullSign j * t * zornCoord X.b ⟨1 + j.val, by omega⟩ ∧
    zornCoord ((e6RootExp (bPullRoot j) t).1 X).b 7 = zornCoord X.b 7 ∧
    (∀ i : Fin 3, zornCoord ((e6RootExp (bPullRoot j) t).1 X).b ⟨1 + i.val, by omega⟩ =
      zornCoord X.b ⟨1 + i.val, by omega⟩) ∧
    (∀ i : Fin 3, zornCoord ((e6RootExp (bPullRoot j) t).1 X).b ⟨4 + i.val, by omega⟩ =
      if i = j then zornCoord X.b ⟨4 + i.val, by omega⟩ + bPullSign j * t * zornCoord X.b 7
      else zornCoord X.b ⟨4 + i.val, by omega⟩) := by
  have heq : bPullRoot j = bPullFullRoot ⟨3 + j.val, by omega⟩ := by fin_cases j <;> rfl
  have hs : bPullSign j = bPullFullSign ⟨3 + j.val, by omega⟩ := by fin_cases j <;> rfl
  have hopp : bMidOppIdx ⟨3 + j.val, by omega⟩ = ⟨1 + j.val, by omega⟩ := by fin_cases j <;> rfl
  rw [heq, hs]
  obtain ⟨_, _, _, hb0, hb7, hbmid⟩ := d4_bPullFullRoot_coords ⟨3 + j.val, by omega⟩ t X
  refine ⟨by rw [← hopp]; exact hb0, hb7, fun i => ?_, fun i => ?_⟩
  · have hi := hbmid ⟨i.val, by omega⟩
    have hne : (⟨i.val, by omega⟩ : Fin 6) ≠ ⟨3 + j.val, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; dsimp at hv; omega
    simp only [hne, ↓reduceIte] at hi
    exact hi
  · have hi := hbmid ⟨3 + i.val, by omega⟩
    have hidx : (⟨1 + (⟨3 + i.val, by omega⟩ : Fin 6).val, by omega⟩ : Fin 8) = ⟨4 + i.val, by omega⟩ :=
      Fin.ext (by dsimp; omega)
    rw [hidx] at hi
    by_cases hij : i = j
    · subst hij
      simpa using hi
    · have hij' : (⟨3 + i.val, by omega⟩ : Fin 6) ≠ ⟨3 + j.val, by omega⟩ := fun h =>
        hij (Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; omega))
      simp [hij, hij'] at hi ⊢; exact hi

private theorem f4_reduce_j23_one_fixing_diags (y : ZornVectorMatrix ℝ) (hy : y.norm = 1) :
    ∃ d ∈ d4Subgroup,
      d.1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one ∧
      (d.1 (embedJ23_cb y)).b = ZornVectorMatrix.one := by
  let Y₀ := embedJ23_cb y
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  -- Step 1: ensure b₀ ≠ 0 using bPullRoot (fixes J₁₂(1))
  have hs1 : ∃ d₁ ∈ d4Subgroup,
      d₁.1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one ∧
      zornCoord (d₁.1 Y₀).b 0 ≠ 0 := by
    by_cases hb0 : zornCoord Y₀.b 0 ≠ 0
    · exact ⟨1, d4Subgroup.one_mem, rfl, hb0⟩
    · push Not at hb0
      have hnorm : ZornVectorMatrix.norm y = 1 := hy
      rw [zorn_norm_zornCoord] at hnorm
      have hb0y : zornCoord y 0 = 0 := hb0
      rw [hb0y, zero_mul, zero_sub] at hnorm
      have hsum_neg : zornCoord y 1 * zornCoord y 4 + zornCoord y 2 * zornCoord y 5 +
          zornCoord y 3 * zornCoord y 6 = -1 := by linarith [hnorm]
      have hexj : ∃ j : Fin 3, zornCoord Y₀.b ⟨1 + j.val, by omega⟩ ≠ 0 := by
        rcases choose_nonzero_of_one_neg_sum_cb hsum_neg with h | h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
      obtain ⟨j, hj⟩ := hexj
      have hsign : bPullSign j ≠ 0 := by fin_cases j <;> simp [bPullSign]
      obtain ⟨gb0, _, _, _⟩ := d4_bPullRoot_coords j 1 Y₀
      refine ⟨e6RootExp (bPullRoot j) 1,
        Subgroup.subset_closure ⟨bPullRoot j, d4_j23_roots_lt24.2 j, 1, rfl⟩,
        d4_j23_roots_fix_j12_one.2 j 1, ?_⟩
      rw [gb0, hb0, zero_add, mul_one]
      exact mul_ne_zero hsign hj
  obtain ⟨d₁, hd₁, hd1_12, hb0_ne⟩ := hs1
  let Y₁ := d₁.1 Y₀
  -- Step 2: clear b₁, b₂, b₃ using bAddRoot 0, 1, 2
  have hadd_step : ∀ (j : Fin 3) (Z : H3Zorn ℝ), zornCoord Z.b 0 ≠ 0 →
      ∃ g ∈ d4Subgroup,
        g.1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one ∧
        zornCoord (g.1 Z).b 0 = zornCoord Z.b 0 ∧
        zornCoord (g.1 Z).b ⟨1 + j.val, by omega⟩ = 0 ∧
        (∀ i : Fin 3, i ≠ j →
          zornCoord (g.1 Z).b ⟨1 + i.val, by omega⟩ = zornCoord Z.b ⟨1 + i.val, by omega⟩) := by
    intro j Z hz0
    have hsign : bAddSign j ≠ 0 := by fin_cases j <;> simp [bAddSign]
    let t := -zornCoord Z.b ⟨1 + j.val, by omega⟩ / (bAddSign j * zornCoord Z.b 0)
    refine ⟨e6RootExp (bAddRoot j) t,
      Subgroup.subset_closure ⟨bAddRoot j, d4_j23_roots_lt24.1 j, t, rfl⟩,
      d4_j23_roots_fix_j12_one.1 j t, ?_⟩
    obtain ⟨gb0, _, gb13, _⟩ := d4_bAddRoot_coords j t Z
    refine ⟨gb0, ?_, fun i hij => ?_⟩
    · rw [gb13 j]; simp only [↓reduceIte]; dsimp [t]; field_simp [hsign, hz0]; ring
    · rw [gb13 i]; simp [hij]
  obtain ⟨a0, ha0_d4, ha0_12, hb0_0, m1_0, mo1_0⟩ := hadd_step 0 Y₁ hb0_ne
  have hb0_0n : zornCoord (a0.1 Y₁).b 0 ≠ 0 := by rw [hb0_0]; exact hb0_ne
  obtain ⟨a1, ha1_d4, ha1_12, hb0_1, m1_1, mo1_1⟩ := hadd_step 1 (a0.1 Y₁) hb0_0n
  have hb0_1n : zornCoord (a1.1 (a0.1 Y₁)).b 0 ≠ 0 := by rw [hb0_1]; exact hb0_0n
  obtain ⟨a2, ha2_d4, ha2_12, hb0_2, m1_2, mo1_2⟩ := hadd_step 2 (a1.1 (a0.1 Y₁)) hb0_1n
  let ad := a2 * (a1 * a0)
  have had_d4 : ad ∈ d4Subgroup := d4Subgroup.mul_mem ha2_d4 (d4Subgroup.mul_mem ha1_d4 ha0_d4)
  have had_12 : ad.1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one := by
    have ha12 : (a1 * a0).1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one := by
      rw [hmul_act, ha0_12, ha1_12]
    rw [hmul_act, ha12, ha2_12]
  have had_eq : ad.1 Y₁ = a2.1 (a1.1 (a0.1 Y₁)) := by rw [hmul_act]; rfl
  let Y₂ := ad.1 Y₁
  have hY2_0 : zornCoord Y₂.b 0 ≠ 0 := by change zornCoord (ad.1 Y₁).b 0 ≠ 0; rw [had_eq, hb0_2]; exact hb0_1n
  have hY2_1 : zornCoord Y₂.b 1 = 0 := by
    change zornCoord (ad.1 Y₁).b ⟨1 + (0 : Fin 3).val, by omega⟩ = 0
    rw [had_eq, mo1_2 0 (by decide), mo1_1 0 (by decide)]; exact m1_0
  have hY2_2 : zornCoord Y₂.b 2 = 0 := by
    change zornCoord (ad.1 Y₁).b ⟨1 + (1 : Fin 3).val, by omega⟩ = 0
    rw [had_eq, mo1_2 1 (by decide)]; exact m1_1
  have hY2_3 : zornCoord Y₂.b 3 = 0 := by
    change zornCoord (ad.1 Y₁).b ⟨1 + (2 : Fin 3).val, by omega⟩ = 0
    rw [had_eq]; exact m1_2
  -- Norm of Y₂.b is 1 so b₀ * b₇ = 1
  have hY2_norm : Y₂.b.norm = 1 := by
    let df := ad * d₁
    have hdf_d4 : df ∈ d4Subgroup := d4Subgroup.mul_mem had_d4 hd₁
    have hdf_f4 : df ∈ e6F4InChevalley := d4Subgroup_le_f4InChevalley hdf_d4
    let A := h3zornJordanAutOfReducedStructure df hdf_f4.2
    have hfix := d4Subgroup_fix_diags hdf_d4
    have hblk := d4Subgroup_preserves_blocks hdf_d4 Y₀
    have hY2_eq : df.1 (embedJ23_cb y) = embedJ23_cb Y₂.b := by
      have hy0 : df.1 Y₀ = Y₂ := rfl
      rw [hy0]
      apply ext_h3
      · change (df.1 Y₀).α₁ = 0; rw [hblk.1]; rfl
      · change (df.1 Y₀).α₂ = 0; rw [hblk.2.1]; rfl
      · change (df.1 Y₀).α₃ = 0; rw [hblk.2.2.1]; rfl
      · change (df.1 Y₀).a = 0; rw [hblk.2.2.2.1]; rfl
      · rfl
      · change (df.1 Y₀).c = 0; rw [hblk.2.2.2.2.2]; rfl
    have hsq := congrArg A (embedJ23_mul_embedJ23_cb y y)
    rw [A.map_mul, A.1.map_smul, map_add] at hsq
    change df.1 (embedJ23_cb y) * df.1 (embedJ23_cb y) =
      ((1 / 2 : ℝ) * zornBilin_cb y y) • (df.1 h3_diag₂ + df.1 h3_diag₃) at hsq
    rw [hY2_eq, embedJ23_mul_embedJ23_cb, hfix.2.1, hfix.2.2, zornBilin_cb_self, zornBilin_cb_self] at hsq
    have hα2 := congrArg H3Zorn.α₂ hsq
    simp only [smul_readback, add_readback, h3_diag₂, h3_diag₃, add_zero] at hα2
    linarith [hα2, hy]
  rw [zorn_norm_zornCoord, hY2_1, hY2_2, hY2_3] at hY2_norm
  have hY2_b7 : zornCoord Y₂.b 7 ≠ 0 := by
    intro hz; rw [hz, mul_zero, zero_sub] at hY2_norm; linarith [hY2_norm]
  -- Step 3: clear b₄, b₅, b₆ using bPullRoot 0, 1, 2 (preserves b₁=b₂=b₃=0 so b₀ is unchanged!)
  have hpull_step : ∀ (j : Fin 3) (Z : H3Zorn ℝ),
      zornCoord Z.b ⟨1 + j.val, by omega⟩ = 0 → zornCoord Z.b 7 ≠ 0 →
      ∃ g ∈ d4Subgroup,
        g.1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one ∧
        zornCoord (g.1 Z).b 0 = zornCoord Z.b 0 ∧
        zornCoord (g.1 Z).b 7 = zornCoord Z.b 7 ∧
        (∀ i : Fin 3, zornCoord (g.1 Z).b ⟨1 + i.val, by omega⟩ =
          zornCoord Z.b ⟨1 + i.val, by omega⟩) ∧
        zornCoord (g.1 Z).b ⟨4 + j.val, by omega⟩ = 0 ∧
        (∀ i : Fin 3, i ≠ j →
          zornCoord (g.1 Z).b ⟨4 + i.val, by omega⟩ = zornCoord Z.b ⟨4 + i.val, by omega⟩) := by
    intro j Z hjz hz7
    have hsign : bPullSign j ≠ 0 := by fin_cases j <;> simp [bPullSign]
    let t := -zornCoord Z.b ⟨4 + j.val, by omega⟩ / (bPullSign j * zornCoord Z.b 7)
    refine ⟨e6RootExp (bPullRoot j) t,
      Subgroup.subset_closure ⟨bPullRoot j, d4_j23_roots_lt24.2 j, t, rfl⟩,
      d4_j23_roots_fix_j12_one.2 j t, ?_⟩
    obtain ⟨gb0, gb7, gb13, gb46⟩ := d4_bPullRoot_coords j t Z
    refine ⟨by rw [gb0, hjz, mul_zero, add_zero], gb7, gb13, ?_, fun i hij => ?_⟩
    · rw [gb46 j]; simp only [↓reduceIte]; dsimp [t]; field_simp [hsign, hz7]; ring
    · rw [gb46 i]; simp [hij]
  have hY2_1i : zornCoord Y₂.b ⟨1 + (0 : Fin 3).val, by omega⟩ = 0 := hY2_1
  obtain ⟨c0, hc0_d4, hc0_12, hc0_b0, hc0_b7, hc0_13, mc0, moc0⟩ := hpull_step 0 Y₂ hY2_1i hY2_b7
  have hc0_2 : zornCoord (c0.1 Y₂).b ⟨1 + (1 : Fin 3).val, by omega⟩ = 0 := by
    rw [hc0_13 1]; exact hY2_2
  have hc0_b7n : zornCoord (c0.1 Y₂).b 7 ≠ 0 := by rw [hc0_b7]; exact hY2_b7
  obtain ⟨c1, hc1_d4, hc1_12, hc1_b0, hc1_b7, hc1_13, mc1, moc1⟩ :=
    hpull_step 1 (c0.1 Y₂) hc0_2 hc0_b7n
  have hc1_3 : zornCoord (c1.1 (c0.1 Y₂)).b ⟨1 + (2 : Fin 3).val, by omega⟩ = 0 := by
    rw [hc1_13 2, hc0_13 2]; exact hY2_3
  have hc1_b7n : zornCoord (c1.1 (c0.1 Y₂)).b 7 ≠ 0 := by rw [hc1_b7]; exact hc0_b7n
  obtain ⟨c2, hc2_d4, hc2_12, hc2_b0, hc2_b7, hc2_13, mc2, moc2⟩ :=
    hpull_step 2 (c1.1 (c0.1 Y₂)) hc1_3 hc1_b7n
  let cd := c2 * (c1 * c0)
  have hcd_d4 : cd ∈ d4Subgroup := d4Subgroup.mul_mem hc2_d4 (d4Subgroup.mul_mem hc1_d4 hc0_d4)
  have hcd_12 : cd.1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one := by
    have hc12 : (c1 * c0).1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one := by
      rw [hmul_act, hc0_12, hc1_12]
    rw [hmul_act, hc12, hc2_12]
  have hcd_eq : cd.1 Y₂ = c2.1 (c1.1 (c0.1 Y₂)) := by rw [hmul_act]; rfl
  let Y₃ := cd.1 Y₂
  have hY3_0 : zornCoord Y₃.b 0 = zornCoord Y₂.b 0 := by
    change zornCoord (cd.1 Y₂).b 0 = _; rw [hcd_eq, hc2_b0, hc1_b0, hc0_b0]
  have hY3_0n : zornCoord Y₃.b 0 ≠ 0 := by rw [hY3_0]; exact hY2_0
  have hY3_1 : zornCoord Y₃.b 1 = 0 := by
    change zornCoord (cd.1 Y₂).b ⟨1 + (0 : Fin 3).val, by omega⟩ = 0
    rw [hcd_eq, hc2_13 0, hc1_13 0, hc0_13 0]; exact hY2_1
  have hY3_2 : zornCoord Y₃.b 2 = 0 := by
    change zornCoord (cd.1 Y₂).b ⟨1 + (1 : Fin 3).val, by omega⟩ = 0
    rw [hcd_eq, hc2_13 1, hc1_13 1, hc0_13 1]; exact hY2_2
  have hY3_3 : zornCoord Y₃.b 3 = 0 := by
    change zornCoord (cd.1 Y₂).b ⟨1 + (2 : Fin 3).val, by omega⟩ = 0
    rw [hcd_eq, hc2_13 2, hc1_13 2, hc0_13 2]; exact hY2_3
  have hY3_4 : zornCoord Y₃.b 4 = 0 := by
    change zornCoord (cd.1 Y₂).b ⟨4 + (0 : Fin 3).val, by omega⟩ = 0
    rw [hcd_eq, moc2 0 (by decide), moc1 0 (by decide)]; exact mc0
  have hY3_5 : zornCoord Y₃.b 5 = 0 := by
    change zornCoord (cd.1 Y₂).b ⟨4 + (1 : Fin 3).val, by omega⟩ = 0
    rw [hcd_eq, moc2 1 (by decide)]; exact mc1
  have hY3_6 : zornCoord Y₃.b 6 = 0 := by
    change zornCoord (cd.1 Y₂).b ⟨4 + (2 : Fin 3).val, by omega⟩ = 0
    rw [hcd_eq]; exact mc2
  have hY3_7 : zornCoord Y₃.b 7 = (zornCoord Y₃.b 0)⁻¹ := by
    have hb7eq : zornCoord Y₃.b 7 = zornCoord Y₂.b 7 := by
      change zornCoord (cd.1 Y₂).b 7 = _; rw [hcd_eq, hc2_b7, hc1_b7, hc0_b7]
    have hmul1 : zornCoord Y₃.b 0 * zornCoord Y₃.b 7 = 1 := by
      rw [hY3_0, hb7eq]; linarith [hY2_norm]
    field_simp [hY3_0n]
    linarith [hmul1]
  -- Step 4: apply Wb(b₀⁻¹) * Wb(-1) using r = 11 (bPullRoot 0) and r = 21 (bAddRoot 0)
  let lam := zornCoord Y₃.b 0
  let s1 := e6RootExp (bPullRoot 0) 1
  let s2 := e6RootExp (bAddRoot 0) 1
  let s3 := e6RootExp (bPullRoot 0) 1
  let s4 := e6RootExp (bPullRoot 0) (-lam⁻¹)
  let s5 := e6RootExp (bAddRoot 0) (-lam)
  let s6 := e6RootExp (bPullRoot 0) (-lam⁻¹)
  let ss := s6 * (s5 * (s4 * (s3 * (s2 * s1))))
  have hs_d4 : ss ∈ d4Subgroup := by
    refine d4Subgroup.mul_mem ?_ (d4Subgroup.mul_mem ?_ (d4Subgroup.mul_mem ?_
      (d4Subgroup.mul_mem ?_ (d4Subgroup.mul_mem ?_ ?_))))
    · exact Subgroup.subset_closure ⟨bPullRoot 0, d4_j23_roots_lt24.2 0, -lam⁻¹, rfl⟩
    · exact Subgroup.subset_closure ⟨bAddRoot 0, d4_j23_roots_lt24.1 0, -lam, rfl⟩
    · exact Subgroup.subset_closure ⟨bPullRoot 0, d4_j23_roots_lt24.2 0, -lam⁻¹, rfl⟩
    · exact Subgroup.subset_closure ⟨bPullRoot 0, d4_j23_roots_lt24.2 0, 1, rfl⟩
    · exact Subgroup.subset_closure ⟨bAddRoot 0, d4_j23_roots_lt24.1 0, 1, rfl⟩
    · exact Subgroup.subset_closure ⟨bPullRoot 0, d4_j23_roots_lt24.2 0, 1, rfl⟩
  have hs_12 : ss.1 (embedJ12_cb ZornVectorMatrix.one) =
      embedJ12_cb ZornVectorMatrix.one := by
    have ha1 : (s2 * s1).1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one := by
      rw [hmul_act, d4_j23_roots_fix_j12_one.2, d4_j23_roots_fix_j12_one.1]
    have ha2 : (s3 * (s2 * s1)).1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one := by
      rw [hmul_act, ha1, d4_j23_roots_fix_j12_one.2]
    have ha3 : (s4 * (s3 * (s2 * s1))).1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one := by
      rw [hmul_act, ha2, d4_j23_roots_fix_j12_one.2]
    have ha4 : (s5 * (s4 * (s3 * (s2 * s1)))).1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one := by
      rw [hmul_act, ha3, d4_j23_roots_fix_j12_one.1]
    rw [hmul_act, ha4, d4_j23_roots_fix_j12_one.2]
  let Z1 := s1.1 Y₃
  let Z2 := s2.1 Z1
  let Z3 := s3.1 Z2
  let Z4 := s4.1 Z3
  let Z5 := s5.1 Z4
  let Z6 := s6.1 Z5
  have hz1 := d4_bPullRoot_coords 0 1 Y₃
  have hz2 := d4_bAddRoot_coords 0 1 Z1
  have hz3 := d4_bPullRoot_coords 0 1 Z2
  have hz4 := d4_bPullRoot_coords 0 (-lam⁻¹) Z3
  have hz5 := d4_bAddRoot_coords 0 (-lam) Z4
  have hz6 := d4_bPullRoot_coords 0 (-lam⁻¹) Z5
  have hp0 : bPullSign 0 = -1 := by simp [bPullSign]
  have ha0 : bAddSign 0 = 1 := by simp [bAddSign]
  have h1_idx : (⟨1 + (0 : Fin 3).val, by omega⟩ : Fin 8) = 1 := rfl
  have h4_idx : (⟨4 + (0 : Fin 3).val, by omega⟩ : Fin 8) = 4 := rfl
  have hlam_ne : lam ≠ 0 := hY3_0n
  have h1_0 : zornCoord Z1.b 0 = lam := by rw [hz1.1, h1_idx, hY3_1]; ring
  have h1_1 : zornCoord Z1.b 1 = 0 := by have h := hz1.2.2.1 0; rw [h1_idx] at h; rw [h, hY3_1]
  have h1_4 : zornCoord Z1.b 4 = -lam⁻¹ := by
    have h := hz1.2.2.2 0; rw [h4_idx, ite_eq_left rfl, hp0] at h; rw [h, hY3_4, hY3_7]; ring
  have h1_7 : zornCoord Z1.b 7 = lam⁻¹ := by rw [hz1.2.1]; exact hY3_7
  have h2_0 : zornCoord Z2.b 0 = lam := by rw [hz2.1, h1_0]
  have h2_1 : zornCoord Z2.b 1 = lam := by
    have h := hz2.2.2.1 0; rw [h1_idx, ite_eq_left rfl, ha0] at h; rw [h, h1_1, h1_0]; ring
  have h2_4 : zornCoord Z2.b 4 = -lam⁻¹ := by
    have h := hz2.2.2.2 0; rw [h4_idx] at h; rw [h, h1_4]
  have h2_7 : zornCoord Z2.b 7 = 0 := by rw [hz2.2.1, h4_idx, ha0, h1_7, h1_4]; ring
  have h3_0 : zornCoord Z3.b 0 = 0 := by rw [hz3.1, h1_idx, hp0, h2_0, h2_1]; ring
  have h3_1 : zornCoord Z3.b 1 = lam := by
    have h := hz3.2.2.1 0; rw [h1_idx] at h; rw [h, h2_1]
  have h3_4 : zornCoord Z3.b 4 = -lam⁻¹ := by
    have h := hz3.2.2.2 0; rw [h4_idx, ite_eq_left rfl, hp0] at h; rw [h, h2_4, h2_7]; ring
  have h3_7 : zornCoord Z3.b 7 = 0 := by rw [hz3.2.1, h2_7]
  have h4_0 : zornCoord Z4.b 0 = 1 := by
    rw [hz4.1, h1_idx, hp0, h3_0, h3_1]; field_simp [hlam_ne]; ring
  have h4_1 : zornCoord Z4.b 1 = lam := by
    have h := hz4.2.2.1 0; rw [h1_idx] at h; rw [h, h3_1]
  have h4_4 : zornCoord Z4.b 4 = -lam⁻¹ := by
    have h := hz4.2.2.2 0; rw [h4_idx, ite_eq_left rfl, hp0] at h; rw [h, h3_4, h3_7]; ring
  have h4_7 : zornCoord Z4.b 7 = 0 := by rw [hz4.2.1, h3_7]
  have h5_0 : zornCoord Z5.b 0 = 1 := by rw [hz5.1, h4_0]
  have h5_1 : zornCoord Z5.b 1 = 0 := by
    have h := hz5.2.2.1 0; rw [h1_idx, ite_eq_left rfl, ha0] at h; rw [h, h4_1, h4_0]; ring
  have h5_4 : zornCoord Z5.b 4 = -lam⁻¹ := by
    have h := hz5.2.2.2 0; rw [h4_idx] at h; rw [h, h4_4]
  have h5_7 : zornCoord Z5.b 7 = 1 := by
    rw [hz5.2.1, h4_idx, ha0, h4_7, h4_4]; field_simp [hlam_ne]; ring
  refine ⟨ss * (cd * (ad * d₁)),
    d4Subgroup.mul_mem hs_d4 (d4Subgroup.mul_mem hcd_d4 (d4Subgroup.mul_mem had_d4 hd₁)), ?_, ?_⟩
  · have h3_12 : (cd * (ad * d₁)).1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one := by
      have h2_12 : (ad * d₁).1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one := by
        rw [hmul_act, hd1_12, had_12]
      rw [hmul_act, h2_12, hcd_12]
    rw [hmul_act, h3_12, hs_12]
  · have hact_s : ss.1 Y₃ = Z6 := by
      have ha1 : (s2 * s1).1 Y₃ = Z2 := rfl
      have ha2 : (s3 * (s2 * s1)).1 Y₃ = Z3 := by rw [hmul_act, ha1]
      have ha3 : (s4 * (s3 * (s2 * s1))).1 Y₃ = Z4 := by rw [hmul_act, ha2]
      have ha4 : (s5 * (s4 * (s3 * (s2 * s1)))).1 Y₃ = Z5 := by rw [hmul_act, ha3]
      rw [hmul_act, ha4]
    have hact_all : (ss * (cd * (ad * d₁))).1 Y₀ = Z6 := by
      have hpre : (cd * (ad * d₁)).1 Y₀ = Y₃ := rfl
      rw [hmul_act, hpre, hact_s]
    rw [hact_all]
    refine zorn_eq_of_zornCoord_eq fun k => ?_
    fin_cases k <;> dsimp only
    · change zornCoord Z6.b 0 = 1; rw [hz6.1, h1_idx, hp0, h5_0, h5_1]; ring
    · change zornCoord Z6.b 1 = 0; have h := hz6.2.2.1 0; rw [h1_idx] at h; rw [h, h5_1]
    · change zornCoord Z6.b ⟨1 + (1 : Fin 3).val, by omega⟩ = 0
      have h6 := hz6.2.2.1 1
      have h5 := hz5.2.2.1 1; rw [ite_eq_right (by decide)] at h5
      have h4 := hz4.2.2.1 1
      have h3 := hz3.2.2.1 1
      have h2 := hz2.2.2.1 1; rw [ite_eq_right (by decide)] at h2
      have h1 := hz1.2.2.1 1
      rw [h6, h5, h4, h3, h2, h1]; exact hY3_2
    · change zornCoord Z6.b ⟨1 + (2 : Fin 3).val, by omega⟩ = 0
      have h6 := hz6.2.2.1 2
      have h5 := hz5.2.2.1 2; rw [ite_eq_right (by decide)] at h5
      have h4 := hz4.2.2.1 2
      have h3 := hz3.2.2.1 2
      have h2 := hz2.2.2.1 2; rw [ite_eq_right (by decide)] at h2
      have h1 := hz1.2.2.1 2
      rw [h6, h5, h4, h3, h2, h1]; exact hY3_3
    · change zornCoord Z6.b 4 = 0
      have h := hz6.2.2.2 0; rw [h4_idx, ite_eq_left rfl, hp0] at h; rw [h, h5_4, h5_7]; ring
    · change zornCoord Z6.b ⟨4 + (1 : Fin 3).val, by omega⟩ = 0
      have h6 := hz6.2.2.2 1; rw [ite_eq_right (by decide)] at h6
      have h5 := hz5.2.2.2 1
      have h4 := hz4.2.2.2 1; rw [ite_eq_right (by decide)] at h4
      have h3 := hz3.2.2.2 1; rw [ite_eq_right (by decide)] at h3
      have h2 := hz2.2.2.2 1
      have h1 := hz1.2.2.2 1; rw [ite_eq_right (by decide)] at h1
      rw [h6, h5, h4, h3, h2, h1]; exact hY3_5
    · change zornCoord Z6.b ⟨4 + (2 : Fin 3).val, by omega⟩ = 0
      have h6 := hz6.2.2.2 2; rw [ite_eq_right (by decide)] at h6
      have h5 := hz5.2.2.2 2
      have h4 := hz4.2.2.2 2; rw [ite_eq_right (by decide)] at h4
      have h3 := hz3.2.2.2 2; rw [ite_eq_right (by decide)] at h3
      have h2 := hz2.2.2.2 2
      have h1 := hz1.2.2.2 2; rw [ite_eq_right (by decide)] at h1
      rw [h6, h5, h4, h3, h2, h1]; exact hY3_6
    · change zornCoord Z6.b 7 = 1; rw [hz6.2.1, h5_7]

private theorem triality_of_fix_diags_and_ones {f : h3zornReducedStructureGroup}
    (hf : f.1 1 = 1)
    (h1 : f.1 h3_diag₁ = h3_diag₁)
    (h2 : f.1 h3_diag₂ = h3_diag₂)
    (h3 : f.1 h3_diag₃ = h3_diag₃)
    (h12 : f.1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one)
    (h23 : f.1 (embedJ23_cb ZornVectorMatrix.one) = embedJ23_cb ZornVectorMatrix.one) :
    ∃ g : ZornVectorMatrix ℝ ≃ₗ[ℝ] ZornVectorMatrix ℝ,
      g ZornVectorMatrix.one = ZornVectorMatrix.one ∧
      (∀ x : ZornVectorMatrix ℝ, g (ZornVectorMatrix.conj x) = ZornVectorMatrix.conj (g x)) ∧
      (∀ x y : ZornVectorMatrix ℝ, g (ZornVectorMatrix.mul x y) = ZornVectorMatrix.mul (g x) (g y)) ∧
      (∀ x y : ZornVectorMatrix ℝ, zornBilin_cb (g x) (g y) = zornBilin_cb x y) ∧
      (∀ x : ZornVectorMatrix ℝ, ZornVectorMatrix.norm (g x) = ZornVectorMatrix.norm x) ∧
      (∀ X : H3Zorn ℝ, f.1 X = ⟨X.α₁, X.α₂, X.α₃, g X.a, g X.b, g X.c⟩) := by
  let A := h3zornJordanAutOfReducedStructure f hf
  have hA1 : A h3_diag₁ = h3_diag₁ := h1
  have hA2 : A h3_diag₂ = h3_diag₂ := h2
  have hA3 : A h3_diag₃ = h3_diag₃ := h3
  obtain ⟨p12, p23, p31⟩ := peirce_spaces_preserved_of_fix_diags A hA1 hA2 hA3
  let g₁₂ : ZornVectorMatrix ℝ →ₗ[ℝ] ZornVectorMatrix ℝ :=
    { toFun := fun x => (f.1 (embedJ12_cb x)).a
      map_add' := fun x y => by
        have had : embedJ12_cb (x + y) = embedJ12_cb x + embedJ12_cb y := by
          apply ext_h3 <;> simp [embedJ12_cb, add_readback, ZornVectorMatrix.add_zero]
        rw [had, map_add]; rfl
      map_smul' := fun r x => by
        have hsm : embedJ12_cb (r • x) = r • embedJ12_cb x := by
          apply ext_h3 <;> simp [embedJ12_cb, smul_readback, ZornVectorMatrix.smul_zero]
        rw [hsm, map_smul]; rfl }
  let g₂₃ : ZornVectorMatrix ℝ → ZornVectorMatrix ℝ := fun y => (f.1 (embedJ23_cb y)).b
  let g₃₁ : ZornVectorMatrix ℝ → ZornVectorMatrix ℝ := fun z => (f.1 (embedJ31_cb z)).c
  have hp12 : ∀ x, f.1 (embedJ12_cb x) = embedJ12_cb (g₁₂ x) := p12
  have hp23 : ∀ y, f.1 (embedJ23_cb y) = embedJ23_cb (g₂₃ y) := p23
  have hp31 : ∀ z, f.1 (embedJ31_cb z) = embedJ31_cb (g₃₁ z) := p31
  have hg12_1 : g₁₂ ZornVectorMatrix.one = ZornVectorMatrix.one := by
    have h := congrArg H3Zorn.a h12; exact h
  have hg23_1 : g₂₃ ZornVectorMatrix.one = ZornVectorMatrix.one := by
    have h := congrArg H3Zorn.b h23; exact h
  have hg31_1 : g₃₁ ZornVectorMatrix.one = ZornVectorMatrix.one := by
    have hm := embedJ12_mul_embedJ23_cb ZornVectorMatrix.one ZornVectorMatrix.one
    have hconj1 : ZornVectorMatrix.conj (ZornVectorMatrix.one : ZornVectorMatrix ℝ) =
        ZornVectorMatrix.one := by
      ext i <;> simp [ZornVectorMatrix.conj, ZornVectorMatrix.one]
    have hmul1 : ZornVectorMatrix.mul (ZornVectorMatrix.one : ZornVectorMatrix ℝ)
        ZornVectorMatrix.one = ZornVectorMatrix.one := by
      ext i <;> simp [ZornVectorMatrix.mul, ZornVectorMatrix.one, ZornVec3.cross]
    rw [hconj1, hmul1] at hm
    have hAp := congrArg A hm
    rw [A.map_mul, A.1.map_smul] at hAp
    change f.1 (embedJ12_cb ZornVectorMatrix.one) * f.1 (embedJ23_cb ZornVectorMatrix.one) =
      (1 / 2 : ℝ) • f.1 (embedJ31_cb ZornVectorMatrix.one) at hAp
    rw [h12, h23, hm, hp31] at hAp
    have h31 := congrArg H3Zorn.c hAp
    have hhalf : (1 / 2 : ℝ) • ZornVectorMatrix.one = (1 / 2 : ℝ) • g₃₁ ZornVectorMatrix.one := h31
    have h2' := congrArg (fun z : ZornVectorMatrix ℝ => (2 : ℝ) • z) hhalf
    rw [smul_smul, smul_smul] at h2'
    norm_num at h2'
    exact h2'.symm
  have half_cancel : ∀ u v : ZornVectorMatrix ℝ, (1 / 2 : ℝ) • u = (1 / 2 : ℝ) • v → u = v := by
    intro u v huv
    have h2' := congrArg (fun z : ZornVectorMatrix ℝ => (2 : ℝ) • z) huv
    rw [smul_smul, smul_smul] at h2'
    norm_num at h2'
    exact h2'
  have hconj1 : ZornVectorMatrix.conj (ZornVectorMatrix.one : ZornVectorMatrix ℝ) =
      ZornVectorMatrix.one := by
    ext i <;> simp [ZornVectorMatrix.conj, ZornVectorMatrix.one]
  have hmul1l : ∀ w : ZornVectorMatrix ℝ, ZornVectorMatrix.mul ZornVectorMatrix.one w = w := fun w => by
    ext i <;> simp [ZornVectorMatrix.mul, ZornVectorMatrix.one, ZornVec3.dot, ZornVec3.cross]
  have hmul1r : ∀ w : ZornVectorMatrix ℝ, ZornVectorMatrix.mul w ZornVectorMatrix.one = w := fun w => by
    ext i <;> simp [ZornVectorMatrix.mul, ZornVectorMatrix.one, ZornVec3.dot, ZornVec3.cross]
  have h31_12 : ∀ x : ZornVectorMatrix ℝ,
      g₃₁ (ZornVectorMatrix.conj x) = ZornVectorMatrix.conj (g₁₂ x) := by
    intro x
    have hm := embedJ12_mul_embedJ23_cb x ZornVectorMatrix.one
    rw [hconj1, hmul1l] at hm
    have hAp := congrArg A hm
    rw [A.map_mul, A.1.map_smul] at hAp
    change f.1 (embedJ12_cb x) * f.1 (embedJ23_cb ZornVectorMatrix.one) =
      (1 / 2 : ℝ) • f.1 (embedJ31_cb (ZornVectorMatrix.conj x)) at hAp
    rw [hp12, h23, embedJ12_mul_embedJ23_cb, hconj1, hmul1l, hp31] at hAp
    exact (half_cancel _ _ (congrArg H3Zorn.c hAp)).symm
  have h31_23 : ∀ y : ZornVectorMatrix ℝ,
      g₃₁ (ZornVectorMatrix.conj y) = ZornVectorMatrix.conj (g₂₃ y) := by
    intro y
    have hm := embedJ12_mul_embedJ23_cb ZornVectorMatrix.one y
    rw [hconj1, hmul1r] at hm
    have hAp := congrArg A hm
    rw [A.map_mul, A.1.map_smul] at hAp
    change f.1 (embedJ12_cb ZornVectorMatrix.one) * f.1 (embedJ23_cb y) =
      (1 / 2 : ℝ) • f.1 (embedJ31_cb (ZornVectorMatrix.conj y)) at hAp
    rw [h12, hp23, embedJ12_mul_embedJ23_cb, hconj1, hmul1r, hp31] at hAp
    exact (half_cancel _ _ (congrArg H3Zorn.c hAp)).symm
  have h12_23 : ∀ y : ZornVectorMatrix ℝ,
      g₁₂ (ZornVectorMatrix.conj y) = ZornVectorMatrix.conj (g₂₃ y) := by
    intro y
    have hm := embedJ23_mul_embedJ31_cb y ZornVectorMatrix.one
    rw [hconj1, hmul1l] at hm
    have hAp := congrArg A hm
    rw [A.map_mul, A.1.map_smul] at hAp
    change f.1 (embedJ23_cb y) * f.1 (embedJ31_cb ZornVectorMatrix.one) =
      (1 / 2 : ℝ) • f.1 (embedJ12_cb (ZornVectorMatrix.conj y)) at hAp
    rw [hp23, hp31, hg31_1, embedJ23_mul_embedJ31_cb, hconj1, hmul1l, hp12] at hAp
    exact (half_cancel _ _ (congrArg H3Zorn.a hAp)).symm
  have hg23_eq : ∀ x : ZornVectorMatrix ℝ, g₂₃ x = g₁₂ x := fun x => by
    have hcc := (h31_12 x).symm.trans (h31_23 x)
    have hc := congrArg ZornVectorMatrix.conj hcc
    rw [ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_conj] at hc
    exact hc.symm
  have hg_conj : ∀ x : ZornVectorMatrix ℝ,
      g₁₂ (ZornVectorMatrix.conj x) = ZornVectorMatrix.conj (g₁₂ x) := fun x => by
    rw [h12_23 x, hg23_eq]
  have hg31_eq : ∀ z : ZornVectorMatrix ℝ, g₃₁ z = g₁₂ z := fun z => by
    have h := h31_12 (ZornVectorMatrix.conj z)
    rw [ZornVectorMatrix.conj_conj, hg_conj, ZornVectorMatrix.conj_conj] at h
    exact h
  have hg_mul : ∀ x y : ZornVectorMatrix ℝ,
      g₁₂ (ZornVectorMatrix.mul x y) = ZornVectorMatrix.mul (g₁₂ x) (g₁₂ y) := by
    intro x y
    have hm := embedJ12_mul_embedJ23_cb (ZornVectorMatrix.conj y) (ZornVectorMatrix.conj x)
    rw [ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_conj] at hm
    have hAp := congrArg A hm
    rw [A.map_mul, A.1.map_smul] at hAp
    change f.1 (embedJ12_cb (ZornVectorMatrix.conj y)) * f.1 (embedJ23_cb (ZornVectorMatrix.conj x)) =
      (1 / 2 : ℝ) • f.1 (embedJ31_cb (ZornVectorMatrix.mul x y)) at hAp
    rw [hp12, hp23, hg23_eq, hp31, hg31_eq, embedJ12_mul_embedJ23_cb,
      hg_conj, hg_conj, ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_conj] at hAp
    exact (half_cancel _ _ (congrArg H3Zorn.c hAp)).symm
  have hg_bilin : ∀ x y : ZornVectorMatrix ℝ, zornBilin_cb (g₁₂ x) (g₁₂ y) = zornBilin_cb x y := by
    intro x y
    have hm := congrArg A (embedJ12_mul_embedJ12_cb x y)
    rw [A.map_mul, A.1.map_smul, map_add] at hm
    change f.1 (embedJ12_cb x) * f.1 (embedJ12_cb y) =
      ((1 / 2 : ℝ) * zornBilin_cb x y) • (f.1 h3_diag₁ + f.1 h3_diag₂) at hm
    rw [hp12, hp12, embedJ12_mul_embedJ12_cb, h1, h2] at hm
    have hα1 := congrArg H3Zorn.α₁ hm
    simp only [smul_readback, add_readback, h3_diag₁, h3_diag₂, add_zero, mul_one] at hα1
    linarith [hα1]
  have hg_norm : ∀ x : ZornVectorMatrix ℝ, ZornVectorMatrix.norm (g₁₂ x) = ZornVectorMatrix.norm x := by
    intro x
    have hb := hg_bilin x x
    rw [zornBilin_cb_self, zornBilin_cb_self] at hb
    linarith [hb]
  have hg_inj : Function.Injective g₁₂ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hxf : f.1 (embedJ12_cb x) = 0 := by rw [hp12, hx]; rfl
    have hxe : embedJ12_cb x = 0 := f.1.injective (by rw [hxf, map_zero])
    exact congrArg H3Zorn.a hxe
  have hg_surj : Function.Surjective g₁₂ :=
    LinearMap.surjective_of_injective (V := ZornVectorMatrix ℝ) hg_inj
  let gEquiv : ZornVectorMatrix ℝ ≃ₗ[ℝ] ZornVectorMatrix ℝ :=
    LinearEquiv.ofBijective g₁₂ ⟨hg_inj, hg_surj⟩
  have hgEquiv_apply : ∀ x : ZornVectorMatrix ℝ, gEquiv x = g₁₂ x := fun _ => rfl
  refine ⟨gEquiv, hg12_1, fun x => ?_, fun x y => ?_, fun x y => ?_, fun x => ?_, fun X => ?_⟩
  · simp only [hgEquiv_apply]; exact hg_conj x
  · simp only [hgEquiv_apply]; exact hg_mul x y
  · simp only [hgEquiv_apply]; exact hg_bilin x y
  · simp only [hgEquiv_apply]; exact hg_norm x
  · have hdec : X = X.α₁ • h3_diag₁ + X.α₂ • h3_diag₂ + X.α₃ • h3_diag₃ +
        embedJ12_cb X.a + embedJ23_cb X.b + embedJ31_cb X.c := by
      apply ext_h3 <;>
        simp [add_readback, smul_readback, h3_diag₁, h3_diag₂, h3_diag₃, embedJ12_cb, embedJ23_cb, embedJ31_cb,
          ZornVectorMatrix.add_zero, ZornVectorMatrix.zero_add, ZornVectorMatrix.smul_zero]
    conv_lhs => rw [hdec]
    simp only [map_add, map_smul, h1, h2, h3, hp12, hp23, hp31, hg23_eq, hg31_eq]
    apply ext_h3 <;>
      simp [add_readback, smul_readback, h3_diag₁, h3_diag₂, h3_diag₃, embedJ12_cb, embedJ23_cb, embedJ31_cb,
        ZornVectorMatrix.add_zero, ZornVectorMatrix.zero_add, ZornVectorMatrix.smul_zero, hgEquiv_apply]

/-! #### Step B4: `G₂` / `SL₃` reduction, `Aut(H₃(𝕆_s)) ⊆ G(E₆)`, and full generation `G(E₆) = ⊤` -/

private def g2Subgroup : Subgroup h3zornReducedStructureGroup where
  carrier := {d | d ∈ d4Subgroup ∧
    d.1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one ∧
    d.1 (embedJ23_cb ZornVectorMatrix.one) = embedJ23_cb ZornVectorMatrix.one}
  one_mem' := ⟨d4Subgroup.one_mem, rfl, rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, ha12, ha23⟩ ⟨hb, hb12, hb23⟩
    refine ⟨d4Subgroup.mul_mem ha hb, ?_, ?_⟩
    · change a.1 (b.1 _) = _; rw [hb12, ha12]
    · change a.1 (b.1 _) = _; rw [hb23, ha23]
  inv_mem' := by
    rintro a ⟨ha, ha12, ha23⟩
    refine ⟨d4Subgroup.inv_mem ha, ?_, ?_⟩
    · change a.1.symm _ = _
      calc a.1.symm (embedJ12_cb ZornVectorMatrix.one)
          = a.1.symm (a.1 (embedJ12_cb ZornVectorMatrix.one)) := congrArg a.1.symm ha12.symm
        _ = embedJ12_cb ZornVectorMatrix.one := a.1.symm_apply_apply _
    · change a.1.symm _ = _
      calc a.1.symm (embedJ23_cb ZornVectorMatrix.one)
          = a.1.symm (a.1 (embedJ23_cb ZornVectorMatrix.one)) := congrArg a.1.symm ha23.symm
        _ = embedJ23_cb ZornVectorMatrix.one := a.1.symm_apply_apply _

private theorem g2Subgroup_le_d4 : g2Subgroup ≤ d4Subgroup := fun _ h => h.1

private theorem g2Subgroup_le_f4 : g2Subgroup ≤ e6F4InChevalley :=
  fun _ h => d4Subgroup_le_f4InChevalley h.1

private theorem g2Subgroup_preserves_norm_trace {d : h3zornReducedStructureGroup}
    (hd : d ∈ g2Subgroup) (x : ZornVectorMatrix ℝ) :
    d.1 (embedJ12_cb x) = embedJ12_cb (d.1 (embedJ12_cb x)).a ∧
    (d.1 (embedJ12_cb x)).a.norm = x.norm ∧
    (d.1 (embedJ12_cb x)).a.trace = x.trace := by
  have hd_f4 := g2Subgroup_le_f4 hd
  have hfix := d4Subgroup_fix_diags hd.1
  obtain ⟨g, hg1, _, _, hgb, hgn, hact⟩ :=
    triality_of_fix_diags_and_ones hd_f4.2 hfix.1 hfix.2.1 hfix.2.2 hd.2.1 hd.2.2
  have hdx : d.1 (embedJ12_cb x) = embedJ12_cb (g x) := by
    rw [hact (embedJ12_cb x)]
    apply ext_h3 <;> simp [embedJ12_cb]
    · exact g.map_zero
    · exact g.map_zero
  have hda : (d.1 (embedJ12_cb x)).a = g x := by rw [hdx]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hda]; exact hdx
  · rw [hda]; exact hgn x
  · have htr1 : ∀ u : ZornVectorMatrix ℝ, u.trace = zornBilin_cb u ZornVectorMatrix.one := fun u => by
      have hcu : ZornVectorMatrix.conj (ZornVectorMatrix.one : ZornVectorMatrix ℝ) =
          ZornVectorMatrix.one := by
        ext i <;> simp [ZornVectorMatrix.conj, ZornVectorMatrix.one]
      have hmu : ZornVectorMatrix.mul u ZornVectorMatrix.one = u := by
        ext i <;> simp [ZornVectorMatrix.mul, ZornVectorMatrix.one, ZornVec3.dot, ZornVec3.cross]
      rw [zornBilin_cb, hcu, hmu]
    calc (d.1 (embedJ12_cb x)).a.trace
        = zornBilin_cb (g x) ZornVectorMatrix.one := by rw [hda, htr1]
      _ = zornBilin_cb (g x) (g ZornVectorMatrix.one) := by rw [hg1]
      _ = zornBilin_cb x ZornVectorMatrix.one := hgb x ZornVectorMatrix.one
      _ = x.trace := (htr1 x).symm

private theorem zornCoord_eq_0 (u : ZornVectorMatrix ℝ) : zornCoord u 0 = u.a := rfl
private theorem zornCoord_eq_1 (u : ZornVectorMatrix ℝ) : zornCoord u 1 = u.v 0 := rfl
private theorem zornCoord_eq_2 (u : ZornVectorMatrix ℝ) : zornCoord u 2 = u.v 1 := rfl
private theorem zornCoord_eq_3 (u : ZornVectorMatrix ℝ) : zornCoord u 3 = u.v 2 := rfl
private theorem zornCoord_eq_4 (u : ZornVectorMatrix ℝ) : zornCoord u 4 = u.w 0 := rfl
private theorem zornCoord_eq_5 (u : ZornVectorMatrix ℝ) : zornCoord u 5 = u.w 1 := rfl
private theorem zornCoord_eq_6 (u : ZornVectorMatrix ℝ) : zornCoord u 6 = u.w 2 := rfl
private theorem zornCoord_eq_7 (u : ZornVectorMatrix ℝ) : zornCoord u 7 = u.b := rfl

private theorem rootExp_a_coord_unchanged {r : Fin 72} {k : Fin 8} (t : ℝ) (X : H3Zorn ℝ)
    (hc : (List.finRange 27).all (fun j =>
      sparseVal (e6RootSparse r) ⟨3 + k.val, by omega⟩ j == 0) = true) :
    zornCoord ((e6RootExp r t).1 X).a k = zornCoord X.a k := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq]
  exact rootExp_coord_unchanged r ⟨3 + k.val, by omega⟩ t X hc

private theorem rootExp_a_coord_add_single {r : Fin 72} {k j₀ : Fin 8} {c : ℤ}
    (cr : ℝ) (t : ℝ) (X : H3Zorn ℝ)
    (hcr : (c : ℝ) = cr := by norm_num)
    (hc : (List.finRange 27).all (fun j =>
      sparseVal (e6RootSparse r) ⟨3 + k.val, by omega⟩ j ==
        if j = ⟨3 + j₀.val, by omega⟩ then c else 0) = true) :
    zornCoord ((e6RootExp r t).1 X).a k =
      zornCoord X.a k + t * cr * zornCoord X.a j₀ := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  rw [← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq, ← h3ZornCoord_a_eq, ← hcr]
  refine rootExp_coord_add_single r ⟨3 + k.val, by omega⟩ ⟨3 + j₀.val, by omega⟩ (c : ℝ) t X fun j => ?_
  rw [hc j]
  by_cases hj : j = ⟨3 + j₀.val, by omega⟩
  · simp [hj]
  · simp [hj]

private theorem rootExp_b_coord_unchanged {r : Fin 72} {k : Fin 8} (t : ℝ) (X : H3Zorn ℝ)
    (hc : (List.finRange 27).all (fun j =>
      sparseVal (e6RootSparse r) ⟨11 + k.val, by omega⟩ j == 0) = true) :
    zornCoord ((e6RootExp r t).1 X).b k = zornCoord X.b k := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq]
  exact rootExp_coord_unchanged r ⟨11 + k.val, by omega⟩ t X hc

private theorem rootExp_b_coord_add_single {r : Fin 72} {k j₀ : Fin 8} {c : ℤ}
    (cr : ℝ) (t : ℝ) (X : H3Zorn ℝ)
    (hcr : (c : ℝ) = cr := by norm_num)
    (hc : (List.finRange 27).all (fun j =>
      sparseVal (e6RootSparse r) ⟨11 + k.val, by omega⟩ j ==
        if j = ⟨11 + j₀.val, by omega⟩ then c else 0) = true) :
    zornCoord ((e6RootExp r t).1 X).b k =
      zornCoord X.b k + t * cr * zornCoord X.b j₀ := by
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hc
  rw [← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq, ← h3ZornCoord_b_eq, ← hcr]
  refine rootExp_coord_add_single r ⟨11 + k.val, by omega⟩ ⟨11 + j₀.val, by omega⟩ (c : ℝ) t X fun j => ?_
  rw [hc j]
  by_cases hj : j = ⟨11 + j₀.val, by omega⟩
  · simp [hj]
  · simp [hj]

private theorem e6RootExp_fix_of_cols_outside {r : Fin 72} (t : ℝ) (X : H3Zorn ℝ)
    (hX : ∀ m k : Fin 27, h3ZornCoordinate X k ≠ 0 → sparseVal (e6RootSparse r) m k = 0) :
    (e6RootExp r t).1 X = X := by
  apply h3Zorn_ext_coord
  intro m
  rw [h3ZornCoordinate_e6RootExp]
  have hs : (∑ k : Fin 27, (sparseVal (e6RootSparse r) m k : ℝ) *
      h3ZornCoordinate X k) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : h3ZornCoordinate X k = 0
    · rw [hk, mul_zero]
    · rw [hX m k hk, Int.cast_zero, zero_mul]
  rw [hs, mul_zero, add_zero]

private def sl3Idx (j : Fin 6) : Fin 72 := ![8, 9, 12, 13, 15, 16] j

private theorem sl3Idx_lt24 (j : Fin 6) : (sl3Idx j).val < 24 := by
  fin_cases j <;> decide

private theorem sl3_cols_outside_zero (j : Fin 6) :
    ∀ (m : Fin 27),
      sparseVal (e6RootSparse (sl3Idx j)) m 0 = 0 ∧
      sparseVal (e6RootSparse (sl3Idx j)) m 1 = 0 ∧
      sparseVal (e6RootSparse (sl3Idx j)) m 2 = 0 ∧
      sparseVal (e6RootSparse (sl3Idx j)) m 3 = 0 ∧
      sparseVal (e6RootSparse (sl3Idx j)) m 10 = 0 ∧
      sparseVal (e6RootSparse (sl3Idx j)) m 11 = 0 ∧
      sparseVal (e6RootSparse (sl3Idx j)) m 18 = 0 ∧
      sparseVal (e6RootSparse (sl3Idx j)) m 19 = 0 ∧
      sparseVal (e6RootSparse (sl3Idx j)) m 26 = 0 := by
  have hc : (List.finRange 6).all (fun j => (List.finRange 27).all (fun m =>
      [0, 1, 2, 3, 10, 11, 18, 19, 26].all (fun k =>
        sparseVal (e6RootSparse (sl3Idx j)) m k == 0))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, List.mem_cons, List.not_mem_nil,
    or_false, true_implies, beq_iff_eq] at hc
  intro m
  have hm := hc j m
  exact ⟨hm 0 (by simp), hm 1 (by simp), hm 2 (by simp), hm 3 (by simp), hm 10 (by simp),
    hm 11 (by simp), hm 18 (by simp), hm 19 (by simp), hm 26 (by simp)⟩

private theorem sl3_mem_g2 (j : Fin 6) (t : ℝ) : e6RootExp (sl3Idx j) t ∈ g2Subgroup := by
  refine ⟨Subgroup.subset_closure ⟨sl3Idx j, sl3Idx_lt24 j, t, rfl⟩, ?_, ?_⟩
  · refine e6RootExp_fix_of_cols_outside t (embedJ12_cb ZornVectorMatrix.one) fun m k hk => ?_
    have hz := sl3_cols_outside_zero j m
    fin_cases k <;>
      first | exact hz.1 | exact hz.2.1 | exact hz.2.2.1 | exact hz.2.2.2.1 |
        exact hz.2.2.2.2.1 | exact hz.2.2.2.2.2.1 | exact hz.2.2.2.2.2.2.1 |
        exact hz.2.2.2.2.2.2.2.1 | exact hz.2.2.2.2.2.2.2.2 | exact absurd rfl hk
  · refine e6RootExp_fix_of_cols_outside t (embedJ23_cb ZornVectorMatrix.one) fun m k hk => ?_
    have hz := sl3_cols_outside_zero j m
    fin_cases k <;>
      first | exact hz.1 | exact hz.2.1 | exact hz.2.2.1 | exact hz.2.2.2.1 |
        exact hz.2.2.2.2.1 | exact hz.2.2.2.2.2.1 | exact hz.2.2.2.2.2.2.1 |
        exact hz.2.2.2.2.2.2.2.1 | exact hz.2.2.2.2.2.2.2.2 | exact absurd rfl hk

private theorem sl3_fix_E11 (j : Fin 6) (t : ℝ) :
    (e6RootExp (sl3Idx j) t).1 (embedJ12_cb ZornVectorMatrix.E11) =
      embedJ12_cb ZornVectorMatrix.E11 := by
  refine e6RootExp_fix_of_cols_outside t (embedJ12_cb ZornVectorMatrix.E11) fun m k hk => ?_
  have hz := sl3_cols_outside_zero j m
  fin_cases k <;>
    first | exact hz.1 | exact hz.2.1 | exact hz.2.2.1 | exact hz.2.2.2.1 |
      exact hz.2.2.2.2.1 | exact hz.2.2.2.2.2.1 | exact hz.2.2.2.2.2.2.1 |
      exact hz.2.2.2.2.2.2.2.1 | exact hz.2.2.2.2.2.2.2.2 | exact absurd rfl hk

private theorem sl3_8_a_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp 8 t).1 X).a.a = X.a.a ∧
    ((e6RootExp 8 t).1 X).a.v 0 = X.a.v 0 - t * X.a.v 1 ∧
    ((e6RootExp 8 t).1 X).a.v 1 = X.a.v 1 ∧
    ((e6RootExp 8 t).1 X).a.v 2 = X.a.v 2 ∧
    ((e6RootExp 8 t).1 X).a.w 0 = X.a.w 0 ∧
    ((e6RootExp 8 t).1 X).a.w 1 = X.a.w 1 + t * X.a.w 0 ∧
    ((e6RootExp 8 t).1 X).a.w 2 = X.a.w 2 ∧
    ((e6RootExp 8 t).1 X).a.b = X.a.b := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := rootExp_a_coord_unchanged (r := 8) (k := 0) t X (by decide)
    rw [zornCoord_eq_0, zornCoord_eq_0] at h; exact h
  · have h := rootExp_a_coord_add_single (r := 8) (k := 1) (j₀ := 2) (c := -1) (-1) t X (hc := by decide)
    rw [zornCoord_eq_1, zornCoord_eq_1, zornCoord_eq_2] at h; linarith [h]
  · have h := rootExp_a_coord_unchanged (r := 8) (k := 2) t X (by decide)
    rw [zornCoord_eq_2, zornCoord_eq_2] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 8) (k := 3) t X (by decide)
    rw [zornCoord_eq_3, zornCoord_eq_3] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 8) (k := 4) t X (by decide)
    rw [zornCoord_eq_4, zornCoord_eq_4] at h; exact h
  · have h := rootExp_a_coord_add_single (r := 8) (k := 5) (j₀ := 4) (c := 1) 1 t X (hc := by decide)
    rw [zornCoord_eq_5, zornCoord_eq_5, zornCoord_eq_4] at h; linarith [h]
  · have h := rootExp_a_coord_unchanged (r := 8) (k := 6) t X (by decide)
    rw [zornCoord_eq_6, zornCoord_eq_6] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 8) (k := 7) t X (by decide)
    rw [zornCoord_eq_7, zornCoord_eq_7] at h; exact h

private theorem sl3_9_a_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp 9 t).1 X).a.a = X.a.a ∧
    ((e6RootExp 9 t).1 X).a.v 0 = X.a.v 0 - t * X.a.v 2 ∧
    ((e6RootExp 9 t).1 X).a.v 1 = X.a.v 1 ∧
    ((e6RootExp 9 t).1 X).a.v 2 = X.a.v 2 ∧
    ((e6RootExp 9 t).1 X).a.w 0 = X.a.w 0 ∧
    ((e6RootExp 9 t).1 X).a.w 1 = X.a.w 1 ∧
    ((e6RootExp 9 t).1 X).a.w 2 = X.a.w 2 + t * X.a.w 0 ∧
    ((e6RootExp 9 t).1 X).a.b = X.a.b := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := rootExp_a_coord_unchanged (r := 9) (k := 0) t X (by decide)
    rw [zornCoord_eq_0, zornCoord_eq_0] at h; exact h
  · have h := rootExp_a_coord_add_single (r := 9) (k := 1) (j₀ := 3) (c := -1) (-1) t X (hc := by decide)
    rw [zornCoord_eq_1, zornCoord_eq_1, zornCoord_eq_3] at h; linarith [h]
  · have h := rootExp_a_coord_unchanged (r := 9) (k := 2) t X (by decide)
    rw [zornCoord_eq_2, zornCoord_eq_2] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 9) (k := 3) t X (by decide)
    rw [zornCoord_eq_3, zornCoord_eq_3] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 9) (k := 4) t X (by decide)
    rw [zornCoord_eq_4, zornCoord_eq_4] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 9) (k := 5) t X (by decide)
    rw [zornCoord_eq_5, zornCoord_eq_5] at h; exact h
  · have h := rootExp_a_coord_add_single (r := 9) (k := 6) (j₀ := 4) (c := 1) 1 t X (hc := by decide)
    rw [zornCoord_eq_6, zornCoord_eq_6, zornCoord_eq_4] at h; linarith [h]
  · have h := rootExp_a_coord_unchanged (r := 9) (k := 7) t X (by decide)
    rw [zornCoord_eq_7, zornCoord_eq_7] at h; exact h

private theorem sl3_12_a_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp 12 t).1 X).a.a = X.a.a ∧
    ((e6RootExp 12 t).1 X).a.v 0 = X.a.v 0 ∧
    ((e6RootExp 12 t).1 X).a.v 1 = X.a.v 1 - t * X.a.v 0 ∧
    ((e6RootExp 12 t).1 X).a.v 2 = X.a.v 2 ∧
    ((e6RootExp 12 t).1 X).a.w 0 = X.a.w 0 + t * X.a.w 1 ∧
    ((e6RootExp 12 t).1 X).a.w 1 = X.a.w 1 ∧
    ((e6RootExp 12 t).1 X).a.w 2 = X.a.w 2 ∧
    ((e6RootExp 12 t).1 X).a.b = X.a.b := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := rootExp_a_coord_unchanged (r := 12) (k := 0) t X (by decide)
    rw [zornCoord_eq_0, zornCoord_eq_0] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 12) (k := 1) t X (by decide)
    rw [zornCoord_eq_1, zornCoord_eq_1] at h; exact h
  · have h := rootExp_a_coord_add_single (r := 12) (k := 2) (j₀ := 1) (c := -1) (-1) t X (hc := by decide)
    rw [zornCoord_eq_2, zornCoord_eq_2, zornCoord_eq_1] at h; linarith [h]
  · have h := rootExp_a_coord_unchanged (r := 12) (k := 3) t X (by decide)
    rw [zornCoord_eq_3, zornCoord_eq_3] at h; exact h
  · have h := rootExp_a_coord_add_single (r := 12) (k := 4) (j₀ := 5) (c := 1) 1 t X (hc := by decide)
    rw [zornCoord_eq_4, zornCoord_eq_4, zornCoord_eq_5] at h; linarith [h]
  · have h := rootExp_a_coord_unchanged (r := 12) (k := 5) t X (by decide)
    rw [zornCoord_eq_5, zornCoord_eq_5] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 12) (k := 6) t X (by decide)
    rw [zornCoord_eq_6, zornCoord_eq_6] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 12) (k := 7) t X (by decide)
    rw [zornCoord_eq_7, zornCoord_eq_7] at h; exact h

private theorem sl3_13_a_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp 13 t).1 X).a.a = X.a.a ∧
    ((e6RootExp 13 t).1 X).a.v 0 = X.a.v 0 ∧
    ((e6RootExp 13 t).1 X).a.v 1 = X.a.v 1 - t * X.a.v 2 ∧
    ((e6RootExp 13 t).1 X).a.v 2 = X.a.v 2 ∧
    ((e6RootExp 13 t).1 X).a.w 0 = X.a.w 0 ∧
    ((e6RootExp 13 t).1 X).a.w 1 = X.a.w 1 ∧
    ((e6RootExp 13 t).1 X).a.w 2 = X.a.w 2 + t * X.a.w 1 ∧
    ((e6RootExp 13 t).1 X).a.b = X.a.b := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := rootExp_a_coord_unchanged (r := 13) (k := 0) t X (by decide)
    rw [zornCoord_eq_0, zornCoord_eq_0] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 13) (k := 1) t X (by decide)
    rw [zornCoord_eq_1, zornCoord_eq_1] at h; exact h
  · have h := rootExp_a_coord_add_single (r := 13) (k := 2) (j₀ := 3) (c := -1) (-1) t X (hc := by decide)
    rw [zornCoord_eq_2, zornCoord_eq_2, zornCoord_eq_3] at h; linarith [h]
  · have h := rootExp_a_coord_unchanged (r := 13) (k := 3) t X (by decide)
    rw [zornCoord_eq_3, zornCoord_eq_3] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 13) (k := 4) t X (by decide)
    rw [zornCoord_eq_4, zornCoord_eq_4] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 13) (k := 5) t X (by decide)
    rw [zornCoord_eq_5, zornCoord_eq_5] at h; exact h
  · have h := rootExp_a_coord_add_single (r := 13) (k := 6) (j₀ := 5) (c := 1) 1 t X (hc := by decide)
    rw [zornCoord_eq_6, zornCoord_eq_6, zornCoord_eq_5] at h; linarith [h]
  · have h := rootExp_a_coord_unchanged (r := 13) (k := 7) t X (by decide)
    rw [zornCoord_eq_7, zornCoord_eq_7] at h; exact h

private theorem sl3_15_a_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp 15 t).1 X).a.a = X.a.a ∧
    ((e6RootExp 15 t).1 X).a.v 0 = X.a.v 0 ∧
    ((e6RootExp 15 t).1 X).a.v 1 = X.a.v 1 ∧
    ((e6RootExp 15 t).1 X).a.v 2 = X.a.v 2 - t * X.a.v 0 ∧
    ((e6RootExp 15 t).1 X).a.w 0 = X.a.w 0 + t * X.a.w 2 ∧
    ((e6RootExp 15 t).1 X).a.w 1 = X.a.w 1 ∧
    ((e6RootExp 15 t).1 X).a.w 2 = X.a.w 2 ∧
    ((e6RootExp 15 t).1 X).a.b = X.a.b := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := rootExp_a_coord_unchanged (r := 15) (k := 0) t X (by decide)
    rw [zornCoord_eq_0, zornCoord_eq_0] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 15) (k := 1) t X (by decide)
    rw [zornCoord_eq_1, zornCoord_eq_1] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 15) (k := 2) t X (by decide)
    rw [zornCoord_eq_2, zornCoord_eq_2] at h; exact h
  · have h := rootExp_a_coord_add_single (r := 15) (k := 3) (j₀ := 1) (c := -1) (-1) t X (hc := by decide)
    rw [zornCoord_eq_3, zornCoord_eq_3, zornCoord_eq_1] at h; linarith [h]
  · have h := rootExp_a_coord_add_single (r := 15) (k := 4) (j₀ := 6) (c := 1) 1 t X (hc := by decide)
    rw [zornCoord_eq_4, zornCoord_eq_4, zornCoord_eq_6] at h; linarith [h]
  · have h := rootExp_a_coord_unchanged (r := 15) (k := 5) t X (by decide)
    rw [zornCoord_eq_5, zornCoord_eq_5] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 15) (k := 6) t X (by decide)
    rw [zornCoord_eq_6, zornCoord_eq_6] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 15) (k := 7) t X (by decide)
    rw [zornCoord_eq_7, zornCoord_eq_7] at h; exact h

private theorem sl3_16_a_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((e6RootExp 16 t).1 X).a.a = X.a.a ∧
    ((e6RootExp 16 t).1 X).a.v 0 = X.a.v 0 ∧
    ((e6RootExp 16 t).1 X).a.v 1 = X.a.v 1 ∧
    ((e6RootExp 16 t).1 X).a.v 2 = X.a.v 2 - t * X.a.v 1 ∧
    ((e6RootExp 16 t).1 X).a.w 0 = X.a.w 0 ∧
    ((e6RootExp 16 t).1 X).a.w 1 = X.a.w 1 + t * X.a.w 2 ∧
    ((e6RootExp 16 t).1 X).a.w 2 = X.a.w 2 ∧
    ((e6RootExp 16 t).1 X).a.b = X.a.b := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := rootExp_a_coord_unchanged (r := 16) (k := 0) t X (by decide)
    rw [zornCoord_eq_0, zornCoord_eq_0] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 16) (k := 1) t X (by decide)
    rw [zornCoord_eq_1, zornCoord_eq_1] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 16) (k := 2) t X (by decide)
    rw [zornCoord_eq_2, zornCoord_eq_2] at h; exact h
  · have h := rootExp_a_coord_add_single (r := 16) (k := 3) (j₀ := 2) (c := -1) (-1) t X (hc := by decide)
    rw [zornCoord_eq_3, zornCoord_eq_3, zornCoord_eq_2] at h; linarith [h]
  · have h := rootExp_a_coord_unchanged (r := 16) (k := 4) t X (by decide)
    rw [zornCoord_eq_4, zornCoord_eq_4] at h; exact h
  · have h := rootExp_a_coord_add_single (r := 16) (k := 5) (j₀ := 6) (c := 1) 1 t X (hc := by decide)
    rw [zornCoord_eq_5, zornCoord_eq_5, zornCoord_eq_6] at h; linarith [h]
  · have h := rootExp_a_coord_unchanged (r := 16) (k := 6) t X (by decide)
    rw [zornCoord_eq_6, zornCoord_eq_6] at h; exact h
  · have h := rootExp_a_coord_unchanged (r := 16) (k := 7) t X (by decide)
    rw [zornCoord_eq_7, zornCoord_eq_7] at h; exact h

private def g2Short0 (t : ℝ) : h3zornReducedStructureGroup :=
  e6RootExp 0 t * (e6RootExp 10 t * e6RootExp 21 t)

private def g2Short3 (t : ℝ) : h3zornReducedStructureGroup :=
  e6RootExp 3 t * (e6RootExp 20 t * e6RootExp 11 t)

private theorem g2Short0_mem_g2 (t : ℝ) : g2Short0 t ∈ g2Subgroup := by
  have hd4 : g2Short0 t ∈ d4Subgroup :=
    d4Subgroup.mul_mem (Subgroup.subset_closure ⟨0, by decide, t, rfl⟩)
      (d4Subgroup.mul_mem (Subgroup.subset_closure ⟨10, by decide, t, rfl⟩)
        (Subgroup.subset_closure ⟨21, by decide, t, rfl⟩))
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  refine ⟨hd4, ?_, ?_⟩
  · have hblk1 : (e6RootExp 21 t).1 (embedJ12_cb ZornVectorMatrix.one) =
        embedJ12_cb ZornVectorMatrix.one := by
      refine e6RootExp_fix_of_cols_outside t (embedJ12_cb ZornVectorMatrix.one) fun m k hk => ?_
      have hc : (List.finRange 27).all (fun m =>
          sparseVal (e6RootSparse 21) m 3 == 0 &&
          sparseVal (e6RootSparse 21) m 10 == 0) = true := by decide
      simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, beq_iff_eq,
        true_implies] at hc
      fin_cases k <;> first | exact (hc m).1 | exact (hc m).2 | exact absurd rfl hk
    have ha1 : ∀ k : Fin 8, zornCoord ((e6RootExp 10 t).1 (embedJ12_cb ZornVectorMatrix.one)).a k =
        if k = 1 then t else zornCoord (ZornVectorMatrix.one : ZornVectorMatrix ℝ) k := by
      have c0 := rootExp_a_coord_unchanged (r := 10) (k := 0) t (embedJ12_cb ZornVectorMatrix.one) (by decide)
      have c1 : zornCoord ((e6RootExp 10 t).1 (embedJ12_cb ZornVectorMatrix.one)).a 1 = t := by
        have h := rootExp_a_coord_add_single (r := 10) (k := 1) (j₀ := 0) (c := 1) 1 t
          (embedJ12_cb ZornVectorMatrix.one) (hc := by decide)
        rw [zornCoord_eq_1, zornCoord_eq_1, zornCoord_eq_0] at h
        have hz1 : (embedJ12_cb ZornVectorMatrix.one).a.v 0 = 0 := rfl
        have hz0 : (embedJ12_cb ZornVectorMatrix.one).a.a = 1 := rfl
        rw [hz1, hz0] at h; rw [zornCoord_eq_1]; linarith [h]
      have c2 := rootExp_a_coord_unchanged (r := 10) (k := 2) t (embedJ12_cb ZornVectorMatrix.one) (by decide)
      have c3 := rootExp_a_coord_unchanged (r := 10) (k := 3) t (embedJ12_cb ZornVectorMatrix.one) (by decide)
      have c4 := rootExp_a_coord_unchanged (r := 10) (k := 4) t (embedJ12_cb ZornVectorMatrix.one) (by decide)
      have c5 := rootExp_a_coord_unchanged (r := 10) (k := 5) t (embedJ12_cb ZornVectorMatrix.one) (by decide)
      have c6 := rootExp_a_coord_unchanged (r := 10) (k := 6) t (embedJ12_cb ZornVectorMatrix.one) (by decide)
      have c7 : zornCoord ((e6RootExp 10 t).1 (embedJ12_cb ZornVectorMatrix.one)).a 7 = 1 := by
        have h := rootExp_a_coord_add_single (r := 10) (k := 7) (j₀ := 4) (c := 1) 1 t
          (embedJ12_cb ZornVectorMatrix.one) (hc := by decide)
        rw [zornCoord_eq_7, zornCoord_eq_7, zornCoord_eq_4] at h
        have hz7 : (embedJ12_cb ZornVectorMatrix.one).a.b = 1 := rfl
        have hz4 : (embedJ12_cb ZornVectorMatrix.one).a.w 0 = 0 := rfl
        rw [hz7, hz4] at h; rw [zornCoord_eq_7]; linarith [h]
      intro k
      fin_cases k
      · exact c0
      · exact c1
      · exact c2
      · exact c3
      · exact c4
      · exact c5
      · exact c6
      · exact c7
    let X₂ := (e6RootExp 10 t).1 (embedJ12_cb ZornVectorMatrix.one)
    have hX2_blk := d4Subgroup_preserves_blocks
      (Subgroup.subset_closure ⟨10, by decide, t, rfl⟩) (embedJ12_cb ZornVectorMatrix.one)
    have hX2_0 : h3ZornCoordinate X₂ 0 = 0 := hX2_blk.1
    have hX2_1 : h3ZornCoordinate X₂ 1 = 0 := hX2_blk.2.1
    have hX2_2 : h3ZornCoordinate X₂ 2 = 0 := hX2_blk.2.2.1
    have hX2_a : ∀ k : Fin 8, zornCoord X₂.a k =
        if k = 1 then t else zornCoord (ZornVectorMatrix.one : ZornVectorMatrix ℝ) k := ha1
    have hX2_b : X₂.b = 0 := hX2_blk.2.2.2.2.1.mpr rfl
    have hX2_c : X₂.c = 0 := hX2_blk.2.2.2.2.2.mpr rfl
    have hX3_blk := d4Subgroup_preserves_blocks
      (Subgroup.subset_closure ⟨0, by decide, t, rfl⟩) X₂
    have hX3_eq : g2Short0 t = e6RootExp 0 t * (e6RootExp 10 t * e6RootExp 21 t) := rfl
    rw [hX3_eq, hmul_act, hmul_act, hblk1]
    change (e6RootExp 0 t).1 X₂ = embedJ12_cb ZornVectorMatrix.one
    apply ext_h3
    · rw [hX3_blk.1]; exact hX2_0
    · rw [hX3_blk.2.1]; exact hX2_1
    · rw [hX3_blk.2.2.1]; exact hX2_2
    · have d0 : zornCoord ((e6RootExp 0 t).1 X₂).a 0 = 1 := by
        have h := rootExp_a_coord_add_single (r := 0) (k := 0) (j₀ := 4) (c := -1) (-1) t X₂ (hc := by decide)
        rw [h, hX2_a 0, hX2_a 4]; simp [ZornVectorMatrix.one, zornCoord]
      have d1 : zornCoord ((e6RootExp 0 t).1 X₂).a 1 = 0 := by
        have h := rootExp_a_coord_add_single (r := 0) (k := 1) (j₀ := 7) (c := -1) (-1) t X₂ (hc := by decide)
        rw [h, hX2_a 1, hX2_a 7]; simp [ZornVectorMatrix.one, zornCoord]
      have d2 : zornCoord ((e6RootExp 0 t).1 X₂).a 2 = 0 := by
        rw [rootExp_a_coord_unchanged (r := 0) (k := 2) t X₂ (by decide), hX2_a 2]; simp [ZornVectorMatrix.one, zornCoord]
      have d3 : zornCoord ((e6RootExp 0 t).1 X₂).a 3 = 0 := by
        rw [rootExp_a_coord_unchanged (r := 0) (k := 3) t X₂ (by decide), hX2_a 3]; simp [ZornVectorMatrix.one, zornCoord]
      have d4 : zornCoord ((e6RootExp 0 t).1 X₂).a 4 = 0 := by
        rw [rootExp_a_coord_unchanged (r := 0) (k := 4) t X₂ (by decide), hX2_a 4]; simp [ZornVectorMatrix.one, zornCoord]
      have d5 : zornCoord ((e6RootExp 0 t).1 X₂).a 5 = 0 := by
        rw [rootExp_a_coord_unchanged (r := 0) (k := 5) t X₂ (by decide), hX2_a 5]; simp [ZornVectorMatrix.one, zornCoord]
      have d6 : zornCoord ((e6RootExp 0 t).1 X₂).a 6 = 0 := by
        rw [rootExp_a_coord_unchanged (r := 0) (k := 6) t X₂ (by decide), hX2_a 6]; simp [ZornVectorMatrix.one, zornCoord]
      have d7 : zornCoord ((e6RootExp 0 t).1 X₂).a 7 = 1 := by
        rw [rootExp_a_coord_unchanged (r := 0) (k := 7) t X₂ (by decide), hX2_a 7]; simp [ZornVectorMatrix.one, zornCoord]
      refine zorn_eq_of_zornCoord_eq fun k => ?_
      fin_cases k <;> [exact d0; exact d1; exact d2; exact d3; exact d4; exact d5; exact d6; exact d7]
    · exact hX3_blk.2.2.2.2.1.mpr hX2_b
    · exact hX3_blk.2.2.2.2.2.mpr hX2_c
  · have hb1_blk := d4Subgroup_preserves_blocks
      (Subgroup.subset_closure ⟨21, by decide, t, rfl⟩) (embedJ23_cb ZornVectorMatrix.one)
    let Y₁ := (e6RootExp 21 t).1 (embedJ23_cb ZornVectorMatrix.one)
    have hY1_b : ∀ k : Fin 8, zornCoord Y₁.b k =
        if k = 1 then t else zornCoord (ZornVectorMatrix.one : ZornVectorMatrix ℝ) k := by
      have c0 := rootExp_b_coord_unchanged (r := 21) (k := 0) t (embedJ23_cb ZornVectorMatrix.one) (by decide)
      have c1 : zornCoord Y₁.b 1 = t := by
        have h := rootExp_b_coord_add_single (r := 21) (k := 1) (j₀ := 0) (c := 1) 1 t
          (embedJ23_cb ZornVectorMatrix.one) (hc := by decide)
        rw [zornCoord_eq_1, zornCoord_eq_1, zornCoord_eq_0] at h
        have hz1 : (embedJ23_cb ZornVectorMatrix.one).b.v 0 = 0 := rfl
        have hz0 : (embedJ23_cb ZornVectorMatrix.one).b.a = 1 := rfl
        rw [hz1, hz0] at h; dsimp [Y₁]; rw [zornCoord_eq_1]; linarith [h]
      have c2 := rootExp_b_coord_unchanged (r := 21) (k := 2) t (embedJ23_cb ZornVectorMatrix.one) (by decide)
      have c3 := rootExp_b_coord_unchanged (r := 21) (k := 3) t (embedJ23_cb ZornVectorMatrix.one) (by decide)
      have c4 := rootExp_b_coord_unchanged (r := 21) (k := 4) t (embedJ23_cb ZornVectorMatrix.one) (by decide)
      have c5 := rootExp_b_coord_unchanged (r := 21) (k := 5) t (embedJ23_cb ZornVectorMatrix.one) (by decide)
      have c6 := rootExp_b_coord_unchanged (r := 21) (k := 6) t (embedJ23_cb ZornVectorMatrix.one) (by decide)
      have c7 : zornCoord Y₁.b 7 = 1 := by
        have h := rootExp_b_coord_add_single (r := 21) (k := 7) (j₀ := 4) (c := 1) 1 t
          (embedJ23_cb ZornVectorMatrix.one) (hc := by decide)
        rw [zornCoord_eq_7, zornCoord_eq_7, zornCoord_eq_4] at h
        have hz7 : (embedJ23_cb ZornVectorMatrix.one).b.b = 1 := rfl
        have hz4 : (embedJ23_cb ZornVectorMatrix.one).b.w 0 = 0 := rfl
        rw [hz7, hz4] at h; dsimp [Y₁]; rw [zornCoord_eq_7]; linarith [h]
      intro k
      fin_cases k <;> [exact c0; exact c1; exact c2; exact c3; exact c4; exact c5; exact c6; exact c7]
    have hY2_blk := d4Subgroup_preserves_blocks
      (Subgroup.subset_closure ⟨10, by decide, t, rfl⟩) Y₁
    have hY2_eq : (e6RootExp 10 t).1 Y₁ = embedJ23_cb ZornVectorMatrix.one := by
      apply ext_h3
      · rw [hY2_blk.1, hb1_blk.1]
      · rw [hY2_blk.2.1, hb1_blk.2.1]
      · rw [hY2_blk.2.2.1, hb1_blk.2.2.1]
      · exact hY2_blk.2.2.2.1.mpr (hb1_blk.2.2.2.1.mpr rfl)
      · have d0 : zornCoord ((e6RootExp 10 t).1 Y₁).b 0 = 1 := by
          have h := rootExp_b_coord_add_single (r := 10) (k := 0) (j₀ := 4) (c := -1) (-1) t Y₁ (hc := by decide)
          rw [h, hY1_b 0, hY1_b 4]; simp [ZornVectorMatrix.one, zornCoord]
        have d1 : zornCoord ((e6RootExp 10 t).1 Y₁).b 1 = 0 := by
          have h := rootExp_b_coord_add_single (r := 10) (k := 1) (j₀ := 7) (c := -1) (-1) t Y₁ (hc := by decide)
          rw [h, hY1_b 1, hY1_b 7]; simp [ZornVectorMatrix.one, zornCoord]
        have d2 : zornCoord ((e6RootExp 10 t).1 Y₁).b 2 = 0 := by
          rw [rootExp_b_coord_unchanged (r := 10) (k := 2) t Y₁ (by decide), hY1_b 2]; simp [ZornVectorMatrix.one, zornCoord]
        have d3 : zornCoord ((e6RootExp 10 t).1 Y₁).b 3 = 0 := by
          rw [rootExp_b_coord_unchanged (r := 10) (k := 3) t Y₁ (by decide), hY1_b 3]; simp [ZornVectorMatrix.one, zornCoord]
        have d4 : zornCoord ((e6RootExp 10 t).1 Y₁).b 4 = 0 := by
          rw [rootExp_b_coord_unchanged (r := 10) (k := 4) t Y₁ (by decide), hY1_b 4]; simp [ZornVectorMatrix.one, zornCoord]
        have d5 : zornCoord ((e6RootExp 10 t).1 Y₁).b 5 = 0 := by
          rw [rootExp_b_coord_unchanged (r := 10) (k := 5) t Y₁ (by decide), hY1_b 5]; simp [ZornVectorMatrix.one, zornCoord]
        have d6 : zornCoord ((e6RootExp 10 t).1 Y₁).b 6 = 0 := by
          rw [rootExp_b_coord_unchanged (r := 10) (k := 6) t Y₁ (by decide), hY1_b 6]; simp [ZornVectorMatrix.one, zornCoord]
        have d7 : zornCoord ((e6RootExp 10 t).1 Y₁).b 7 = 1 := by
          rw [rootExp_b_coord_unchanged (r := 10) (k := 7) t Y₁ (by decide), hY1_b 7]; simp [ZornVectorMatrix.one, zornCoord]
        refine zorn_eq_of_zornCoord_eq fun k => ?_
        fin_cases k <;> [exact d0; exact d1; exact d2; exact d3; exact d4; exact d5; exact d6; exact d7]
      · exact hY2_blk.2.2.2.2.2.mpr (hb1_blk.2.2.2.2.2.mpr rfl)
    have hY3_fix : (e6RootExp 0 t).1 (embedJ23_cb ZornVectorMatrix.one) =
        embedJ23_cb ZornVectorMatrix.one := by
      refine e6RootExp_fix_of_cols_outside t (embedJ23_cb ZornVectorMatrix.one) fun m k hk => ?_
      have hc : (List.finRange 27).all (fun m =>
          sparseVal (e6RootSparse 0) m 11 == 0 &&
          sparseVal (e6RootSparse 0) m 18 == 0) = true := by decide
      simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, beq_iff_eq,
        true_implies] at hc
      fin_cases k <;> first | exact (hc m).1 | exact (hc m).2 | exact absurd rfl hk
    change (e6RootExp 0 t).1 ((e6RootExp 10 t).1 Y₁) = embedJ23_cb ZornVectorMatrix.one
    rw [hY2_eq, hY3_fix]

private theorem g2Short3_mem_g2 (t : ℝ) : g2Short3 t ∈ g2Subgroup := by
  have hd4 : g2Short3 t ∈ d4Subgroup :=
    d4Subgroup.mul_mem (Subgroup.subset_closure ⟨3, by decide, t, rfl⟩)
      (d4Subgroup.mul_mem (Subgroup.subset_closure ⟨20, by decide, t, rfl⟩)
        (Subgroup.subset_closure ⟨11, by decide, t, rfl⟩))
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  refine ⟨hd4, ?_, ?_⟩
  · have hblk1 : (e6RootExp 11 t).1 (embedJ12_cb ZornVectorMatrix.one) =
        embedJ12_cb ZornVectorMatrix.one := by
      refine e6RootExp_fix_of_cols_outside t (embedJ12_cb ZornVectorMatrix.one) fun m k hk => ?_
      have hc : (List.finRange 27).all (fun m =>
          sparseVal (e6RootSparse 11) m 3 == 0 &&
          sparseVal (e6RootSparse 11) m 10 == 0) = true := by decide
      simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, beq_iff_eq,
        true_implies] at hc
      fin_cases k <;> first | exact (hc m).1 | exact (hc m).2 | exact absurd rfl hk
    let X₂ := (e6RootExp 20 t).1 (embedJ12_cb ZornVectorMatrix.one)
    have hX2_blk := d4Subgroup_preserves_blocks
      (Subgroup.subset_closure ⟨20, by decide, t, rfl⟩) (embedJ12_cb ZornVectorMatrix.one)
    have hX2_a : ∀ k : Fin 8, zornCoord X₂.a k =
        if k = 4 then t else zornCoord (ZornVectorMatrix.one : ZornVectorMatrix ℝ) k := by
      have c0 := rootExp_a_coord_unchanged (r := 20) (k := 0) t (embedJ12_cb ZornVectorMatrix.one) (by decide)
      have c1 := rootExp_a_coord_unchanged (r := 20) (k := 1) t (embedJ12_cb ZornVectorMatrix.one) (by decide)
      have c2 := rootExp_a_coord_unchanged (r := 20) (k := 2) t (embedJ12_cb ZornVectorMatrix.one) (by decide)
      have c3 := rootExp_a_coord_unchanged (r := 20) (k := 3) t (embedJ12_cb ZornVectorMatrix.one) (by decide)
      have c4 : zornCoord X₂.a 4 = t := by
        have h := rootExp_a_coord_add_single (r := 20) (k := 4) (j₀ := 0) (c := 1) 1 t
          (embedJ12_cb ZornVectorMatrix.one) (hc := by decide)
        rw [zornCoord_eq_4, zornCoord_eq_4, zornCoord_eq_0] at h
        have hz4 : (embedJ12_cb ZornVectorMatrix.one).a.w 0 = 0 := rfl
        have hz0 : (embedJ12_cb ZornVectorMatrix.one).a.a = 1 := rfl
        rw [hz4, hz0] at h; dsimp [X₂]; rw [zornCoord_eq_4]; linarith [h]
      have c5 := rootExp_a_coord_unchanged (r := 20) (k := 5) t (embedJ12_cb ZornVectorMatrix.one) (by decide)
      have c6 := rootExp_a_coord_unchanged (r := 20) (k := 6) t (embedJ12_cb ZornVectorMatrix.one) (by decide)
      have c7 : zornCoord X₂.a 7 = 1 := by
        have h := rootExp_a_coord_add_single (r := 20) (k := 7) (j₀ := 1) (c := 1) 1 t
          (embedJ12_cb ZornVectorMatrix.one) (hc := by decide)
        rw [zornCoord_eq_7, zornCoord_eq_7, zornCoord_eq_1] at h
        have hz7 : (embedJ12_cb ZornVectorMatrix.one).a.b = 1 := rfl
        have hz1 : (embedJ12_cb ZornVectorMatrix.one).a.v 0 = 0 := rfl
        rw [hz7, hz1] at h; dsimp [X₂]; rw [zornCoord_eq_7]; linarith [h]
      intro k
      fin_cases k <;> [exact c0; exact c1; exact c2; exact c3; exact c4; exact c5; exact c6; exact c7]
    have hX3_blk := d4Subgroup_preserves_blocks
      (Subgroup.subset_closure ⟨3, by decide, t, rfl⟩) X₂
    change (e6RootExp 3 t).1 ((e6RootExp 20 t).1 ((e6RootExp 11 t).1
      (embedJ12_cb ZornVectorMatrix.one))) = embedJ12_cb ZornVectorMatrix.one
    rw [hblk1]
    change (e6RootExp 3 t).1 X₂ = embedJ12_cb ZornVectorMatrix.one
    apply ext_h3
    · rw [hX3_blk.1, hX2_blk.1]
    · rw [hX3_blk.2.1, hX2_blk.2.1]
    · rw [hX3_blk.2.2.1, hX2_blk.2.2.1]
    · have d0 : zornCoord ((e6RootExp 3 t).1 X₂).a 0 = 1 := by
        have h := rootExp_a_coord_add_single (r := 3) (k := 0) (j₀ := 1) (c := -1) (-1) t X₂ (hc := by decide)
        rw [h, hX2_a 0, hX2_a 1]; simp [ZornVectorMatrix.one, zornCoord]
      have d1 : zornCoord ((e6RootExp 3 t).1 X₂).a 1 = 0 := by
        rw [rootExp_a_coord_unchanged (r := 3) (k := 1) t X₂ (by decide), hX2_a 1]; simp [ZornVectorMatrix.one, zornCoord]
      have d2 : zornCoord ((e6RootExp 3 t).1 X₂).a 2 = 0 := by
        rw [rootExp_a_coord_unchanged (r := 3) (k := 2) t X₂ (by decide), hX2_a 2]; simp [ZornVectorMatrix.one, zornCoord]
      have d3 : zornCoord ((e6RootExp 3 t).1 X₂).a 3 = 0 := by
        rw [rootExp_a_coord_unchanged (r := 3) (k := 3) t X₂ (by decide), hX2_a 3]; simp [ZornVectorMatrix.one, zornCoord]
      have d4 : zornCoord ((e6RootExp 3 t).1 X₂).a 4 = 0 := by
        have h := rootExp_a_coord_add_single (r := 3) (k := 4) (j₀ := 7) (c := -1) (-1) t X₂ (hc := by decide)
        rw [h, hX2_a 4, hX2_a 7]; simp [ZornVectorMatrix.one, zornCoord]
      have d5 : zornCoord ((e6RootExp 3 t).1 X₂).a 5 = 0 := by
        rw [rootExp_a_coord_unchanged (r := 3) (k := 5) t X₂ (by decide), hX2_a 5]; simp [ZornVectorMatrix.one, zornCoord]
      have d6 : zornCoord ((e6RootExp 3 t).1 X₂).a 6 = 0 := by
        rw [rootExp_a_coord_unchanged (r := 3) (k := 6) t X₂ (by decide), hX2_a 6]; simp [ZornVectorMatrix.one, zornCoord]
      have d7 : zornCoord ((e6RootExp 3 t).1 X₂).a 7 = 1 := by
        rw [rootExp_a_coord_unchanged (r := 3) (k := 7) t X₂ (by decide), hX2_a 7]; simp [ZornVectorMatrix.one, zornCoord]
      refine zorn_eq_of_zornCoord_eq fun k => ?_
      fin_cases k <;> [exact d0; exact d1; exact d2; exact d3; exact d4; exact d5; exact d6; exact d7]
    · exact hX3_blk.2.2.2.2.1.mpr (hX2_blk.2.2.2.2.1.mpr rfl)
    · exact hX3_blk.2.2.2.2.2.mpr (hX2_blk.2.2.2.2.2.mpr rfl)
  · let Y₁ := (e6RootExp 11 t).1 (embedJ23_cb ZornVectorMatrix.one)
    have hY1_blk := d4Subgroup_preserves_blocks
      (Subgroup.subset_closure ⟨11, by decide, t, rfl⟩) (embedJ23_cb ZornVectorMatrix.one)
    have hY1_b : ∀ k : Fin 8, zornCoord Y₁.b k =
        if k = 4 then -t else zornCoord (ZornVectorMatrix.one : ZornVectorMatrix ℝ) k := by
      have c0 : zornCoord Y₁.b 0 = 1 := by
        have h := rootExp_b_coord_add_single (r := 11) (k := 0) (j₀ := 1) (c := -1) (-1) t
          (embedJ23_cb ZornVectorMatrix.one) (hc := by decide)
        rw [zornCoord_eq_0, zornCoord_eq_0, zornCoord_eq_1] at h
        have hz0 : (embedJ23_cb ZornVectorMatrix.one).b.a = 1 := rfl
        have hz1 : (embedJ23_cb ZornVectorMatrix.one).b.v 0 = 0 := rfl
        rw [hz0, hz1] at h; dsimp [Y₁]; rw [zornCoord_eq_0]; linarith [h]
      have c1 := rootExp_b_coord_unchanged (r := 11) (k := 1) t (embedJ23_cb ZornVectorMatrix.one) (by decide)
      have c2 := rootExp_b_coord_unchanged (r := 11) (k := 2) t (embedJ23_cb ZornVectorMatrix.one) (by decide)
      have c3 := rootExp_b_coord_unchanged (r := 11) (k := 3) t (embedJ23_cb ZornVectorMatrix.one) (by decide)
      have c4 : zornCoord Y₁.b 4 = -t := by
        have h := rootExp_b_coord_add_single (r := 11) (k := 4) (j₀ := 7) (c := -1) (-1) t
          (embedJ23_cb ZornVectorMatrix.one) (hc := by decide)
        rw [zornCoord_eq_4, zornCoord_eq_4, zornCoord_eq_7] at h
        have hz4 : (embedJ23_cb ZornVectorMatrix.one).b.w 0 = 0 := rfl
        have hz7 : (embedJ23_cb ZornVectorMatrix.one).b.b = 1 := rfl
        rw [hz4, hz7] at h; dsimp [Y₁]; rw [zornCoord_eq_4]; linarith [h]
      have c5 := rootExp_b_coord_unchanged (r := 11) (k := 5) t (embedJ23_cb ZornVectorMatrix.one) (by decide)
      have c6 := rootExp_b_coord_unchanged (r := 11) (k := 6) t (embedJ23_cb ZornVectorMatrix.one) (by decide)
      have c7 := rootExp_b_coord_unchanged (r := 11) (k := 7) t (embedJ23_cb ZornVectorMatrix.one) (by decide)
      intro k
      fin_cases k <;> [exact c0; exact c1; exact c2; exact c3; exact c4; exact c5; exact c6; exact c7]
    have hY2_blk := d4Subgroup_preserves_blocks
      (Subgroup.subset_closure ⟨20, by decide, t, rfl⟩) Y₁
    let Y₂ := (e6RootExp 20 t).1 Y₁
    have hY2_b : ∀ k : Fin 8, zornCoord Y₂.b k = zornCoord Y₁.b k := by
      have c0 := rootExp_b_coord_unchanged (r := 20) (k := 0) t Y₁ (by decide)
      have c1 := rootExp_b_coord_unchanged (r := 20) (k := 1) t Y₁ (by decide)
      have c2 : zornCoord Y₂.b 2 = zornCoord Y₁.b 2 := by
        have h := rootExp_b_coord_add_single (r := 20) (k := 2) (j₀ := 6) (c := -1) (-1) t Y₁ (hc := by decide)
        rw [h, hY1_b 6]; simp [ZornVectorMatrix.one, zornCoord]
      have c3 : zornCoord Y₂.b 3 = zornCoord Y₁.b 3 := by
        have h := rootExp_b_coord_add_single (r := 20) (k := 3) (j₀ := 5) (c := 1) 1 t Y₁ (hc := by decide)
        rw [h, hY1_b 5]; simp [ZornVectorMatrix.one, zornCoord]
      have c4 := rootExp_b_coord_unchanged (r := 20) (k := 4) t Y₁ (by decide)
      have c5 := rootExp_b_coord_unchanged (r := 20) (k := 5) t Y₁ (by decide)
      have c6 := rootExp_b_coord_unchanged (r := 20) (k := 6) t Y₁ (by decide)
      have c7 := rootExp_b_coord_unchanged (r := 20) (k := 7) t Y₁ (by decide)
      intro k
      fin_cases k <;> [exact c0; exact c1; exact c2; exact c3; exact c4; exact c5; exact c6; exact c7]
    have hY3_blk := d4Subgroup_preserves_blocks
      (Subgroup.subset_closure ⟨3, by decide, t, rfl⟩) Y₂
    change (e6RootExp 3 t).1 Y₂ = embedJ23_cb ZornVectorMatrix.one
    apply ext_h3
    · rw [hY3_blk.1, hY2_blk.1, hY1_blk.1]
    · rw [hY3_blk.2.1, hY2_blk.2.1, hY1_blk.2.1]
    · rw [hY3_blk.2.2.1, hY2_blk.2.2.1, hY1_blk.2.2.1]
    · exact hY3_blk.2.2.2.1.mpr (hY2_blk.2.2.2.1.mpr (hY1_blk.2.2.2.1.mpr rfl))
    · have d0 : zornCoord ((e6RootExp 3 t).1 Y₂).b 0 = 1 := by
        rw [rootExp_b_coord_unchanged (r := 3) (k := 0) t Y₂ (by decide), hY2_b 0, hY1_b 0]
        simp [ZornVectorMatrix.one, zornCoord]
      have d1 : zornCoord ((e6RootExp 3 t).1 Y₂).b 1 = 0 := by
        rw [rootExp_b_coord_unchanged (r := 3) (k := 1) t Y₂ (by decide), hY2_b 1, hY1_b 1]
        simp [ZornVectorMatrix.one, zornCoord]
      have d2 : zornCoord ((e6RootExp 3 t).1 Y₂).b 2 = 0 := by
        rw [rootExp_b_coord_unchanged (r := 3) (k := 2) t Y₂ (by decide), hY2_b 2, hY1_b 2]
        simp [ZornVectorMatrix.one, zornCoord]
      have d3 : zornCoord ((e6RootExp 3 t).1 Y₂).b 3 = 0 := by
        rw [rootExp_b_coord_unchanged (r := 3) (k := 3) t Y₂ (by decide), hY2_b 3, hY1_b 3]
        simp [ZornVectorMatrix.one, zornCoord]
      have d4 : zornCoord ((e6RootExp 3 t).1 Y₂).b 4 = 0 := by
        have h := rootExp_b_coord_add_single (r := 3) (k := 4) (j₀ := 0) (c := 1) 1 t Y₂ (hc := by decide)
        rw [h, hY2_b 4, hY2_b 0, hY1_b 4, hY1_b 0]; simp [ZornVectorMatrix.one, zornCoord]
      have d5 : zornCoord ((e6RootExp 3 t).1 Y₂).b 5 = 0 := by
        rw [rootExp_b_coord_unchanged (r := 3) (k := 5) t Y₂ (by decide), hY2_b 5, hY1_b 5]
        simp [ZornVectorMatrix.one, zornCoord]
      have d6 : zornCoord ((e6RootExp 3 t).1 Y₂).b 6 = 0 := by
        rw [rootExp_b_coord_unchanged (r := 3) (k := 6) t Y₂ (by decide), hY2_b 6, hY1_b 6]
        simp [ZornVectorMatrix.one, zornCoord]
      have d7 : zornCoord ((e6RootExp 3 t).1 Y₂).b 7 = 1 := by
        have h := rootExp_b_coord_add_single (r := 3) (k := 7) (j₀ := 1) (c := 1) 1 t Y₂ (hc := by decide)
        rw [h, hY2_b 7, hY2_b 1, hY1_b 7, hY1_b 1]; simp [ZornVectorMatrix.one, zornCoord]
      refine zorn_eq_of_zornCoord_eq fun k => ?_
      fin_cases k <;> [exact d0; exact d1; exact d2; exact d3; exact d4; exact d5; exact d6; exact d7]
    · exact hY3_blk.2.2.2.2.2.mpr (hY2_blk.2.2.2.2.2.mpr (hY1_blk.2.2.2.2.2.mpr rfl))

private theorem g2Short0_a_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((g2Short0 t).1 X).a.a = X.a.a - t * X.a.w 0 ∧
    ((g2Short0 t).1 X).a.v 0 = X.a.v 0 + t * (X.a.a - X.a.b) - t ^ 2 * X.a.w 0 ∧
    ((g2Short0 t).1 X).a.v 1 = X.a.v 1 ∧ ((g2Short0 t).1 X).a.v 2 = X.a.v 2 ∧
    ((g2Short0 t).1 X).a.w 0 = X.a.w 0 ∧
    ((g2Short0 t).1 X).a.w 1 = X.a.w 1 - t * X.a.v 2 ∧
    ((g2Short0 t).1 X).a.w 2 = X.a.w 2 + t * X.a.v 1 ∧
    ((g2Short0 t).1 X).a.b = X.a.b + t * X.a.w 0 := by
  let X₁ := (e6RootExp 21 t).1 X
  let X₂ := (e6RootExp 10 t).1 X₁
  let X₃ := (e6RootExp 0 t).1 X₂
  have h1_0 : zornCoord X₁.a 0 = zornCoord X.a 0 := rootExp_a_coord_unchanged t X (by decide)
  have h1_1 : zornCoord X₁.a 1 = zornCoord X.a 1 := rootExp_a_coord_unchanged t X (by decide)
  have h1_2 : zornCoord X₁.a 2 = zornCoord X.a 2 := rootExp_a_coord_unchanged t X (by decide)
  have h1_3 : zornCoord X₁.a 3 = zornCoord X.a 3 := rootExp_a_coord_unchanged t X (by decide)
  have h1_4 : zornCoord X₁.a 4 = zornCoord X.a 4 := rootExp_a_coord_unchanged t X (by decide)
  have h1_5 : zornCoord X₁.a 5 = zornCoord X.a 5 - t * zornCoord X.a 3 := by
    have h := rootExp_a_coord_add_single (r := 21) (k := 5) (j₀ := 3) (c := -1) (-1) t X (hc := by decide)
    linarith [h]
  have h1_6 : zornCoord X₁.a 6 = zornCoord X.a 6 + t * zornCoord X.a 2 := by
    have h := rootExp_a_coord_add_single (r := 21) (k := 6) (j₀ := 2) (c := 1) 1 t X (hc := by decide)
    linarith [h]
  have h1_7 : zornCoord X₁.a 7 = zornCoord X.a 7 := rootExp_a_coord_unchanged t X (by decide)
  have h2_0 : zornCoord X₂.a 0 = zornCoord X₁.a 0 := rootExp_a_coord_unchanged t X₁ (by decide)
  have h2_1 : zornCoord X₂.a 1 = zornCoord X₁.a 1 + t * zornCoord X₁.a 0 := by
    have h := rootExp_a_coord_add_single (r := 10) (k := 1) (j₀ := 0) (c := 1) 1 t X₁ (hc := by decide)
    linarith [h]
  have h2_2 : zornCoord X₂.a 2 = zornCoord X₁.a 2 := rootExp_a_coord_unchanged t X₁ (by decide)
  have h2_3 : zornCoord X₂.a 3 = zornCoord X₁.a 3 := rootExp_a_coord_unchanged t X₁ (by decide)
  have h2_4 : zornCoord X₂.a 4 = zornCoord X₁.a 4 := rootExp_a_coord_unchanged t X₁ (by decide)
  have h2_5 : zornCoord X₂.a 5 = zornCoord X₁.a 5 := rootExp_a_coord_unchanged t X₁ (by decide)
  have h2_6 : zornCoord X₂.a 6 = zornCoord X₁.a 6 := rootExp_a_coord_unchanged t X₁ (by decide)
  have h2_7 : zornCoord X₂.a 7 = zornCoord X₁.a 7 + t * zornCoord X₁.a 4 := by
    have h := rootExp_a_coord_add_single (r := 10) (k := 7) (j₀ := 4) (c := 1) 1 t X₁ (hc := by decide)
    linarith [h]
  have h3_0 : zornCoord X₃.a 0 = zornCoord X₂.a 0 - t * zornCoord X₂.a 4 := by
    have h := rootExp_a_coord_add_single (r := 0) (k := 0) (j₀ := 4) (c := -1) (-1) t X₂ (hc := by decide)
    linarith [h]
  have h3_1 : zornCoord X₃.a 1 = zornCoord X₂.a 1 - t * zornCoord X₂.a 7 := by
    have h := rootExp_a_coord_add_single (r := 0) (k := 1) (j₀ := 7) (c := -1) (-1) t X₂ (hc := by decide)
    linarith [h]
  have h3_2 : zornCoord X₃.a 2 = zornCoord X₂.a 2 := rootExp_a_coord_unchanged t X₂ (by decide)
  have h3_3 : zornCoord X₃.a 3 = zornCoord X₂.a 3 := rootExp_a_coord_unchanged t X₂ (by decide)
  have h3_4 : zornCoord X₃.a 4 = zornCoord X₂.a 4 := rootExp_a_coord_unchanged t X₂ (by decide)
  have h3_5 : zornCoord X₃.a 5 = zornCoord X₂.a 5 := rootExp_a_coord_unchanged t X₂ (by decide)
  have h3_6 : zornCoord X₃.a 6 = zornCoord X₂.a 6 := rootExp_a_coord_unchanged t X₂ (by decide)
  have h3_7 : zornCoord X₃.a 7 = zornCoord X₂.a 7 := rootExp_a_coord_unchanged t X₂ (by decide)
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  have hX3 : (g2Short0 t).1 X = X₃ := by
    have h1 : (e6RootExp 10 t * e6RootExp 21 t).1 X = X₂ := rfl
    change (e6RootExp 0 t * (e6RootExp 10 t * e6RootExp 21 t)).1 X = X₃
    rw [hmul_act, h1]
  rw [hX3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← zornCoord_eq_0 X₃.a, h3_0, h2_0, h2_4, h1_0, h1_4, zornCoord_eq_0, zornCoord_eq_4]
  · rw [← zornCoord_eq_1 X₃.a, h3_1, h2_1, h2_7, h1_0, h1_1, h1_4, h1_7,
      zornCoord_eq_0, zornCoord_eq_1, zornCoord_eq_4, zornCoord_eq_7]; ring
  · rw [← zornCoord_eq_2 X₃.a, h3_2, h2_2, h1_2, zornCoord_eq_2]
  · rw [← zornCoord_eq_3 X₃.a, h3_3, h2_3, h1_3, zornCoord_eq_3]
  · rw [← zornCoord_eq_4 X₃.a, h3_4, h2_4, h1_4, zornCoord_eq_4]
  · rw [← zornCoord_eq_5 X₃.a, h3_5, h2_5, h1_5, zornCoord_eq_5, zornCoord_eq_3]
  · rw [← zornCoord_eq_6 X₃.a, h3_6, h2_6, h1_6, zornCoord_eq_6, zornCoord_eq_2]
  · rw [← zornCoord_eq_7 X₃.a, h3_7, h2_7, h1_7, h1_4, zornCoord_eq_7, zornCoord_eq_4]

private theorem g2Short3_a_coords (t : ℝ) (X : H3Zorn ℝ) :
    ((g2Short3 t).1 X).a.a = X.a.a - t * X.a.v 0 ∧
    ((g2Short3 t).1 X).a.v 0 = X.a.v 0 ∧
    ((g2Short3 t).1 X).a.v 1 = X.a.v 1 - t * X.a.w 2 ∧
    ((g2Short3 t).1 X).a.v 2 = X.a.v 2 + t * X.a.w 1 ∧
    ((g2Short3 t).1 X).a.w 0 = X.a.w 0 + t * (X.a.a - X.a.b) - t ^ 2 * X.a.v 0 ∧
    ((g2Short3 t).1 X).a.w 1 = X.a.w 1 ∧ ((g2Short3 t).1 X).a.w 2 = X.a.w 2 ∧
    ((g2Short3 t).1 X).a.b = X.a.b + t * X.a.v 0 := by
  let X₁ := (e6RootExp 11 t).1 X
  let X₂ := (e6RootExp 20 t).1 X₁
  let X₃ := (e6RootExp 3 t).1 X₂
  have h1_0 : zornCoord X₁.a 0 = zornCoord X.a 0 := rootExp_a_coord_unchanged t X (by decide)
  have h1_1 : zornCoord X₁.a 1 = zornCoord X.a 1 := rootExp_a_coord_unchanged t X (by decide)
  have h1_2 : zornCoord X₁.a 2 = zornCoord X.a 2 - t * zornCoord X.a 6 := by
    have h := rootExp_a_coord_add_single (r := 11) (k := 2) (j₀ := 6) (c := -1) (-1) t X (hc := by decide)
    linarith [h]
  have h1_3 : zornCoord X₁.a 3 = zornCoord X.a 3 + t * zornCoord X.a 5 := by
    have h := rootExp_a_coord_add_single (r := 11) (k := 3) (j₀ := 5) (c := 1) 1 t X (hc := by decide)
    linarith [h]
  have h1_4 : zornCoord X₁.a 4 = zornCoord X.a 4 := rootExp_a_coord_unchanged t X (by decide)
  have h1_5 : zornCoord X₁.a 5 = zornCoord X.a 5 := rootExp_a_coord_unchanged t X (by decide)
  have h1_6 : zornCoord X₁.a 6 = zornCoord X.a 6 := rootExp_a_coord_unchanged t X (by decide)
  have h1_7 : zornCoord X₁.a 7 = zornCoord X.a 7 := rootExp_a_coord_unchanged t X (by decide)
  have h2_0 : zornCoord X₂.a 0 = zornCoord X₁.a 0 := rootExp_a_coord_unchanged t X₁ (by decide)
  have h2_1 : zornCoord X₂.a 1 = zornCoord X₁.a 1 := rootExp_a_coord_unchanged t X₁ (by decide)
  have h2_2 : zornCoord X₂.a 2 = zornCoord X₁.a 2 := rootExp_a_coord_unchanged t X₁ (by decide)
  have h2_3 : zornCoord X₂.a 3 = zornCoord X₁.a 3 := rootExp_a_coord_unchanged t X₁ (by decide)
  have h2_4 : zornCoord X₂.a 4 = zornCoord X₁.a 4 + t * zornCoord X₁.a 0 := by
    have h := rootExp_a_coord_add_single (r := 20) (k := 4) (j₀ := 0) (c := 1) 1 t X₁ (hc := by decide)
    linarith [h]
  have h2_5 : zornCoord X₂.a 5 = zornCoord X₁.a 5 := rootExp_a_coord_unchanged t X₁ (by decide)
  have h2_6 : zornCoord X₂.a 6 = zornCoord X₁.a 6 := rootExp_a_coord_unchanged t X₁ (by decide)
  have h2_7 : zornCoord X₂.a 7 = zornCoord X₁.a 7 + t * zornCoord X₁.a 1 := by
    have h := rootExp_a_coord_add_single (r := 20) (k := 7) (j₀ := 1) (c := 1) 1 t X₁ (hc := by decide)
    linarith [h]
  have h3_0 : zornCoord X₃.a 0 = zornCoord X₂.a 0 - t * zornCoord X₂.a 1 := by
    have h := rootExp_a_coord_add_single (r := 3) (k := 0) (j₀ := 1) (c := -1) (-1) t X₂ (hc := by decide)
    linarith [h]
  have h3_1 : zornCoord X₃.a 1 = zornCoord X₂.a 1 := rootExp_a_coord_unchanged t X₂ (by decide)
  have h3_2 : zornCoord X₃.a 2 = zornCoord X₂.a 2 := rootExp_a_coord_unchanged t X₂ (by decide)
  have h3_3 : zornCoord X₃.a 3 = zornCoord X₂.a 3 := rootExp_a_coord_unchanged t X₂ (by decide)
  have h3_4 : zornCoord X₃.a 4 = zornCoord X₂.a 4 - t * zornCoord X₂.a 7 := by
    have h := rootExp_a_coord_add_single (r := 3) (k := 4) (j₀ := 7) (c := -1) (-1) t X₂ (hc := by decide)
    linarith [h]
  have h3_5 : zornCoord X₃.a 5 = zornCoord X₂.a 5 := rootExp_a_coord_unchanged t X₂ (by decide)
  have h3_6 : zornCoord X₃.a 6 = zornCoord X₂.a 6 := rootExp_a_coord_unchanged t X₂ (by decide)
  have h3_7 : zornCoord X₃.a 7 = zornCoord X₂.a 7 := rootExp_a_coord_unchanged t X₂ (by decide)
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  have hX3 : (g2Short3 t).1 X = X₃ := by
    have h1 : (e6RootExp 20 t * e6RootExp 11 t).1 X = X₂ := rfl
    change (e6RootExp 3 t * (e6RootExp 20 t * e6RootExp 11 t)).1 X = X₃
    rw [hmul_act, h1]
  rw [hX3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← zornCoord_eq_0 X₃.a, h3_0, h2_0, h2_1, h1_0, h1_1, zornCoord_eq_0, zornCoord_eq_1]
  · rw [← zornCoord_eq_1 X₃.a, h3_1, h2_1, h1_1, zornCoord_eq_1]
  · rw [← zornCoord_eq_2 X₃.a, h3_2, h2_2, h1_2, zornCoord_eq_2, zornCoord_eq_6]
  · rw [← zornCoord_eq_3 X₃.a, h3_3, h2_3, h1_3, zornCoord_eq_3, zornCoord_eq_5]
  · rw [← zornCoord_eq_4 X₃.a, h3_4, h2_4, h2_7, h1_0, h1_1, h1_4, h1_7,
      zornCoord_eq_0, zornCoord_eq_1, zornCoord_eq_4, zornCoord_eq_7]; ring
  · rw [← zornCoord_eq_5 X₃.a, h3_5, h2_5, h1_5, zornCoord_eq_5]
  · rw [← zornCoord_eq_6 X₃.a, h3_6, h2_6, h1_6, zornCoord_eq_6]
  · rw [← zornCoord_eq_7 X₃.a, h3_7, h2_7, h1_7, h1_1, zornCoord_eq_7, zornCoord_eq_1]

private theorem fin3_fun_eq_zero (f : Fin 3 → ℝ) (h0 : f 0 = 0) (h1 : f 1 = 0) (h2 : f 2 = 0) :
    f = 0 := by
  funext k; fin_cases k <;> [exact h0; exact h1; exact h2]

private theorem fin3_fun_eq (f g : Fin 3 → ℝ) (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2) :
    f = g := by
  funext k; fin_cases k <;> [exact h0; exact h1; exact h2]

private theorem sl3_reduce_v_to_e0 (u : ZornVectorMatrix ℝ) (hv : u.v ≠ 0) :
    ∃ d ∈ g2Subgroup,
      d.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 ∧
      (let u' := (d.1 (embedJ12_cb u)).a
      u'.a = u.a ∧ u'.b = u.b ∧ u'.v 0 ≠ 0 ∧ u'.v 1 = 0 ∧ u'.v 2 = 0 ∧
      (u.w = 0 → u'.w = 0)) := by
  have hv_nz : u.v 0 ≠ 0 ∨ u.v 1 ≠ 0 ∨ u.v 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext k; fin_cases k <;> [exact h.1; exact h.2.1; exact h.2.2]
  have hs1 : ∃ d₁ ∈ g2Subgroup,
      d₁.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 ∧
      (let u₁ := (d₁.1 (embedJ12_cb u)).a
      u₁.a = u.a ∧ u₁.b = u.b ∧ u₁.v 0 ≠ 0 ∧ (u.w = 0 → u₁.w = 0)) := by
    by_cases hv0 : u.v 0 ≠ 0
    · exact ⟨1, g2Subgroup.one_mem, rfl, rfl, rfl, hv0, id⟩
    · push Not at hv0
      rcases hv_nz with h0 | h1 | h2
      · exact absurd hv0 h0
      · refine ⟨e6RootExp 8 1, sl3_mem_g2 0 1, sl3_fix_E11 0 1, ?_⟩
        have hc := sl3_8_a_coords 1 (embedJ12_cb u)
        refine ⟨hc.1, hc.2.2.2.2.2.2.2, ?_, fun hw => ?_⟩
        · rw [hc.2.1]; change u.v 0 - 1 * u.v 1 ≠ 0; rw [hv0, zero_sub, one_mul, neg_ne_zero]; exact h1
        · have w0 : ((e6RootExp 8 1).1 (embedJ12_cb u)).a.w 0 = 0 := by
            rw [hc.2.2.2.2.1]; change u.w 0 = 0; rw [hw]; rfl
          have w1 : ((e6RootExp 8 1).1 (embedJ12_cb u)).a.w 1 = 0 := by
            rw [hc.2.2.2.2.2.1]; change u.w 1 + 1 * u.w 0 = 0; rw [hw]; simp
          have w2 : ((e6RootExp 8 1).1 (embedJ12_cb u)).a.w 2 = 0 := by
            rw [hc.2.2.2.2.2.2.1]; change u.w 2 = 0; rw [hw]; rfl
          exact fin3_fun_eq_zero _ w0 w1 w2
      · refine ⟨e6RootExp 9 1, sl3_mem_g2 1 1, sl3_fix_E11 1 1, ?_⟩
        have hc := sl3_9_a_coords 1 (embedJ12_cb u)
        refine ⟨hc.1, hc.2.2.2.2.2.2.2, ?_, fun hw => ?_⟩
        · rw [hc.2.1]; change u.v 0 - 1 * u.v 2 ≠ 0; rw [hv0, zero_sub, one_mul, neg_ne_zero]; exact h2
        · have w0 : ((e6RootExp 9 1).1 (embedJ12_cb u)).a.w 0 = 0 := by
            rw [hc.2.2.2.2.1]; change u.w 0 = 0; rw [hw]; rfl
          have w1 : ((e6RootExp 9 1).1 (embedJ12_cb u)).a.w 1 = 0 := by
            rw [hc.2.2.2.2.2.1]; change u.w 1 = 0; rw [hw]; rfl
          have w2 : ((e6RootExp 9 1).1 (embedJ12_cb u)).a.w 2 = 0 := by
            rw [hc.2.2.2.2.2.2.1]; change u.w 2 + 1 * u.w 0 = 0; rw [hw]; simp
          exact fin3_fun_eq_zero _ w0 w1 w2
  obtain ⟨d₁, hd₁, h1E, h1a, h1b, h1v0, h1w⟩ := hs1
  let X₁ := d₁.1 (embedJ12_cb u)
  have h1v0' : X₁.a.v 0 ≠ 0 := h1v0
  let t₂ := X₁.a.v 1 / X₁.a.v 0
  let d₂ := e6RootExp 12 t₂
  let X₂ := d₂.1 X₁
  have hc2 := sl3_12_a_coords t₂ X₁
  have h2v0 : X₂.a.v 0 ≠ 0 := by rw [hc2.2.1]; exact h1v0'
  have h2v1 : X₂.a.v 1 = 0 := by
    change ((e6RootExp 12 t₂).1 X₁).a.v 1 = 0
    rw [hc2.2.2.1]; dsimp [t₂]; field_simp [h1v0']; ring
  let t₃ := X₂.a.v 2 / X₂.a.v 0
  let d₃ := e6RootExp 15 t₃
  have hc3 := sl3_15_a_coords t₃ X₂
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  refine ⟨d₃ * (d₂ * d₁),
    g2Subgroup.mul_mem (sl3_mem_g2 4 t₃) (g2Subgroup.mul_mem (sl3_mem_g2 2 t₂) hd₁), ?_, ?_⟩
  · have hfix2 : (e6RootExp 12 t₂).1 (embedJ12_cb ZornVectorMatrix.E11) =
        embedJ12_cb ZornVectorMatrix.E11 := sl3_fix_E11 2 t₂
    have hfix3 : (e6RootExp 15 t₃).1 (embedJ12_cb ZornVectorMatrix.E11) =
        embedJ12_cb ZornVectorMatrix.E11 := sl3_fix_E11 4 t₃
    have h2E : (d₂ * d₁).1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 := by
      rw [hmul_act, h1E]; exact hfix2
    rw [hmul_act, h2E]; exact hfix3
  · have hact : (d₃ * (d₂ * d₁)).1 (embedJ12_cb u) = d₃.1 X₂ := by
      have ha1 : (d₂ * d₁).1 (embedJ12_cb u) = X₂ := rfl
      rw [hmul_act, ha1]
    rw [hact]
    refine ⟨?_, ?_, ?_, ?_, ?_, fun hw => ?_⟩
    · rw [hc3.1, hc2.1, h1a]
    · rw [hc3.2.2.2.2.2.2.2, hc2.2.2.2.2.2.2.2, h1b]
    · rw [hc3.2.1]; exact h2v0
    · rw [hc3.2.2.1]; exact h2v1
    · rw [hc3.2.2.2.1]; dsimp [t₃]; field_simp [h2v0]; ring
    · have hw1 : X₁.a.w = 0 := h1w hw
      have hw2 : X₂.a.w = 0 := by
        have w0 : X₂.a.w 0 = 0 := by
          change ((e6RootExp 12 t₂).1 X₁).a.w 0 = 0; rw [hc2.2.2.2.2.1, hw1]; simp
        have w1 : X₂.a.w 1 = 0 := by
          change ((e6RootExp 12 t₂).1 X₁).a.w 1 = 0; rw [hc2.2.2.2.2.2.1, hw1]; rfl
        have w2 : X₂.a.w 2 = 0 := by
          change ((e6RootExp 12 t₂).1 X₁).a.w 2 = 0; rw [hc2.2.2.2.2.2.2.1, hw1]; rfl
        exact fin3_fun_eq_zero _ w0 w1 w2
      have w0 : (d₃.1 X₂).a.w 0 = 0 := by
        change ((e6RootExp 15 t₃).1 X₂).a.w 0 = 0; rw [hc3.2.2.2.2.1, hw2]; simp
      have w1 : (d₃.1 X₂).a.w 1 = 0 := by
        change ((e6RootExp 15 t₃).1 X₂).a.w 1 = 0; rw [hc3.2.2.2.2.2.1, hw2]; rfl
      have w2 : (d₃.1 X₂).a.w 2 = 0 := by
        change ((e6RootExp 15 t₃).1 X₂).a.w 2 = 0; rw [hc3.2.2.2.2.2.2.1, hw2]; rfl
      exact fin3_fun_eq_zero _ w0 w1 w2

private theorem sl3_reduce_w_to_e0 (u : ZornVectorMatrix ℝ) (hw : u.w ≠ 0) :
    ∃ d ∈ g2Subgroup,
      let u' := (d.1 (embedJ12_cb u)).a
      u'.a = u.a ∧ u'.b = u.b ∧ u'.w 0 ≠ 0 ∧ u'.w 1 = 0 ∧ u'.w 2 = 0 := by
  have hw_nz : u.w 0 ≠ 0 ∨ u.w 1 ≠ 0 ∨ u.w 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    funext k; fin_cases k <;> [exact h.1; exact h.2.1; exact h.2.2]
  have hs1 : ∃ d₁ ∈ g2Subgroup,
      let u₁ := (d₁.1 (embedJ12_cb u)).a
      u₁.a = u.a ∧ u₁.b = u.b ∧ u₁.w 0 ≠ 0 := by
    by_cases hw0 : u.w 0 ≠ 0
    · exact ⟨1, g2Subgroup.one_mem, rfl, rfl, hw0⟩
    · push Not at hw0
      rcases hw_nz with h0 | h1 | h2
      · exact absurd hw0 h0
      · refine ⟨e6RootExp 12 1, sl3_mem_g2 2 1, ?_⟩
        have hc := sl3_12_a_coords 1 (embedJ12_cb u)
        refine ⟨hc.1, hc.2.2.2.2.2.2.2, ?_⟩
        rw [hc.2.2.2.2.1]; change u.w 0 + 1 * u.w 1 ≠ 0; rw [hw0, zero_add, one_mul]; exact h1
      · refine ⟨e6RootExp 15 1, sl3_mem_g2 4 1, ?_⟩
        have hc := sl3_15_a_coords 1 (embedJ12_cb u)
        refine ⟨hc.1, hc.2.2.2.2.2.2.2, ?_⟩
        rw [hc.2.2.2.2.1]; change u.w 0 + 1 * u.w 2 ≠ 0; rw [hw0, zero_add, one_mul]; exact h2
  obtain ⟨d₁, hd₁, h1a, h1b, h1w0⟩ := hs1
  let X₁ := d₁.1 (embedJ12_cb u)
  have h1w0' : X₁.a.w 0 ≠ 0 := h1w0
  let t₂ := -X₁.a.w 1 / X₁.a.w 0
  let d₂ := e6RootExp 8 t₂
  let X₂ := d₂.1 X₁
  have hc2 := sl3_8_a_coords t₂ X₁
  have h2w0 : X₂.a.w 0 ≠ 0 := by
    change ((e6RootExp 8 t₂).1 X₁).a.w 0 ≠ 0; rw [hc2.2.2.2.2.1]; exact h1w0'
  have h2w1 : X₂.a.w 1 = 0 := by
    change ((e6RootExp 8 t₂).1 X₁).a.w 1 = 0
    rw [hc2.2.2.2.2.2.1]; dsimp [t₂]; field_simp [h1w0']; ring
  let t₃ := -X₂.a.w 2 / X₂.a.w 0
  let d₃ := e6RootExp 9 t₃
  have hc3 := sl3_9_a_coords t₃ X₂
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  refine ⟨d₃ * (d₂ * d₁),
    g2Subgroup.mul_mem (sl3_mem_g2 1 t₃) (g2Subgroup.mul_mem (sl3_mem_g2 0 t₂) hd₁), ?_⟩
  have hact : (d₃ * (d₂ * d₁)).1 (embedJ12_cb u) = d₃.1 X₂ := by
    have ha1 : (d₂ * d₁).1 (embedJ12_cb u) = X₂ := rfl
    rw [hmul_act, ha1]
  rw [hact]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hc3.1, hc2.1, h1a]
  · rw [hc3.2.2.2.2.2.2.2, hc2.2.2.2.2.2.2.2, h1b]
  · rw [hc3.2.2.2.2.1]; exact h2w0
  · rw [hc3.2.2.2.2.2.1]; exact h2w1
  · rw [hc3.2.2.2.2.2.2.1]; dsimp [t₃]; field_simp [h2w0]; ring

private theorem g2_reduce_idempotent_to_E11 (w : ZornVectorMatrix ℝ)
    (hw_tr : w.trace = 1) (hw_norm : w.norm = 0) :
    ∃ d ∈ g2Subgroup, (d.1 (embedJ12_cb w)).a = ZornVectorMatrix.E11 := by
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  -- Step 1: achieve a = 1, b = 0
  have hs1 : ∃ d₁ ∈ g2Subgroup,
      let w₁ := (d₁.1 (embedJ12_cb w)).a
      w₁.a = 1 ∧ w₁.b = 0 := by
    by_cases ha1 : w.a = 1
    · have hb0 : w.b = 0 := by change w.a + w.b = 1 at hw_tr; linarith
      exact ⟨1, g2Subgroup.one_mem, ha1, hb0⟩
    · by_cases hw0 : w.w ≠ 0
      · have hw_nz : w.w 0 ≠ 0 ∨ w.w 1 ≠ 0 ∨ w.w 2 ≠ 0 := by
          by_contra h; push Not at h; apply hw0
          funext k; fin_cases k <;> [exact h.1; exact h.2.1; exact h.2.2]
        have hs0 : ∃ d0 ∈ g2Subgroup,
            (d0.1 (embedJ12_cb w)).a.a = w.a ∧
            (d0.1 (embedJ12_cb w)).a.b = w.b ∧
            (d0.1 (embedJ12_cb w)).a.w 0 ≠ 0 := by
          by_cases h0 : w.w 0 ≠ 0
          · exact ⟨1, g2Subgroup.one_mem, rfl, rfl, h0⟩
          · push Not at h0
            rcases hw_nz with k0 | k1 | k2
            · exact absurd h0 k0
            · refine ⟨e6RootExp 12 1, sl3_mem_g2 2 1, ?_⟩
              have hc := sl3_12_a_coords 1 (embedJ12_cb w)
              refine ⟨hc.1, hc.2.2.2.2.2.2.2, ?_⟩
              rw [hc.2.2.2.2.1]; change w.w 0 + 1 * w.w 1 ≠ 0; rw [h0, zero_add, one_mul]; exact k1
            · refine ⟨e6RootExp 15 1, sl3_mem_g2 4 1, ?_⟩
              have hc := sl3_15_a_coords 1 (embedJ12_cb w)
              refine ⟨hc.1, hc.2.2.2.2.2.2.2, ?_⟩
              rw [hc.2.2.2.2.1]; change w.w 0 + 1 * w.w 2 ≠ 0; rw [h0, zero_add, one_mul]; exact k2
        obtain ⟨d0, hd0, h0a, h0b, h0w0⟩ := hs0
        let X₀ := d0.1 (embedJ12_cb w)
        have h0a' : X₀.a.a = w.a := h0a
        have h0b' : X₀.a.b = w.b := h0b
        have h0w0' : X₀.a.w 0 ≠ 0 := h0w0
        let t := (X₀.a.a - 1) / X₀.a.w 0
        have hc := g2Short0_a_coords t X₀
        refine ⟨g2Short0 t * d0, g2Subgroup.mul_mem (g2Short0_mem_g2 t) hd0, ?_, ?_⟩
        · rw [hmul_act, hc.1]; dsimp [t]; field_simp [h0w0']; ring
        · rw [hmul_act, hc.2.2.2.2.2.2.2, h0b']
          have htr : w.a + w.b = 1 := hw_tr
          dsimp [t]; rw [h0a']; field_simp [h0w0']; linarith
      · push Not at hw0
        by_cases hv0 : w.v ≠ 0
        · have hv_nz : w.v 0 ≠ 0 ∨ w.v 1 ≠ 0 ∨ w.v 2 ≠ 0 := by
            by_contra h; push Not at h; apply hv0
            funext k; fin_cases k <;> [exact h.1; exact h.2.1; exact h.2.2]
          have hs0 : ∃ d0 ∈ g2Subgroup,
              (d0.1 (embedJ12_cb w)).a.a = w.a ∧
              (d0.1 (embedJ12_cb w)).a.b = w.b ∧
              (d0.1 (embedJ12_cb w)).a.v 0 ≠ 0 := by
            by_cases h0 : w.v 0 ≠ 0
            · exact ⟨1, g2Subgroup.one_mem, rfl, rfl, h0⟩
            · push Not at h0
              rcases hv_nz with k0 | k1 | k2
              · exact absurd h0 k0
              · refine ⟨e6RootExp 8 1, sl3_mem_g2 0 1, ?_⟩
                have hc := sl3_8_a_coords 1 (embedJ12_cb w)
                refine ⟨hc.1, hc.2.2.2.2.2.2.2, ?_⟩
                rw [hc.2.1]; change w.v 0 - 1 * w.v 1 ≠ 0; rw [h0, zero_sub, one_mul, neg_ne_zero]; exact k1
              · refine ⟨e6RootExp 9 1, sl3_mem_g2 1 1, ?_⟩
                have hc := sl3_9_a_coords 1 (embedJ12_cb w)
                refine ⟨hc.1, hc.2.2.2.2.2.2.2, ?_⟩
                rw [hc.2.1]; change w.v 0 - 1 * w.v 2 ≠ 0; rw [h0, zero_sub, one_mul, neg_ne_zero]; exact k2
          obtain ⟨d0, hd0, h0a, h0b, h0v0⟩ := hs0
          let X₀ := d0.1 (embedJ12_cb w)
          have h0a' : X₀.a.a = w.a := h0a
          have h0b' : X₀.a.b = w.b := h0b
          have h0v0' : X₀.a.v 0 ≠ 0 := h0v0
          let t := (X₀.a.a - 1) / X₀.a.v 0
          have hc := g2Short3_a_coords t X₀
          refine ⟨g2Short3 t * d0, g2Subgroup.mul_mem (g2Short3_mem_g2 t) hd0, ?_, ?_⟩
          · rw [hmul_act, hc.1]; dsimp [t]; field_simp [h0v0']; ring
          · rw [hmul_act, hc.2.2.2.2.2.2.2, h0b']
            have htr : w.a + w.b = 1 := hw_tr
            dsimp [t]; rw [h0a']; field_simp [h0v0']; linarith
        · push Not at hv0
          have hnorm0 : w.a * w.b = 0 := by
            change w.a * w.b - ZornVec3.dot w.v w.w = 0 at hw_norm
            rw [hw0, ZornVec3.dot, Finset.sum_eq_zero (fun _ _ => by simp), sub_zero] at hw_norm
            exact hw_norm
          have ha0 : w.a = 0 := (mul_eq_zero.mp hnorm0).resolve_right (fun hb => by
            have htr : w.a + w.b = 1 := hw_tr
            rw [hb, add_zero] at htr; exact ha1 htr)
          have hb1 : w.b = 1 := by
            have htr : w.a + w.b = 1 := hw_tr
            rw [ha0, zero_add] at htr; exact htr
          let X₀ := (g2Short0 1).1 (embedJ12_cb w)
          have hc0 := g2Short0_a_coords 1 (embedJ12_cb w)
          have h0a : X₀.a.a = 0 := by rw [hc0.1]; change w.a - 1 * w.w 0 = 0; rw [ha0, hw0]; simp
          have h0b : X₀.a.b = 1 := by rw [hc0.2.2.2.2.2.2.2]; change w.b + 1 * w.w 0 = 1; rw [hb1, hw0]; simp
          have h0v0 : X₀.a.v 0 = -1 := by
            rw [hc0.2.1]; change w.v 0 + 1 * (w.a - w.b) - 1 ^ 2 * w.w 0 = -1
            rw [hv0, hw0, ha0, hb1]; norm_num
          have hc3 := g2Short3_a_coords 1 X₀
          refine ⟨g2Short3 1 * g2Short0 1,
            g2Subgroup.mul_mem (g2Short3_mem_g2 1) (g2Short0_mem_g2 1), ?_, ?_⟩
          · rw [hmul_act, hc3.1, h0a, h0v0]; norm_num
          · rw [hmul_act, hc3.2.2.2.2.2.2.2, h0b, h0v0]; norm_num
  obtain ⟨d₁, hd₁, h1a, h1b⟩ := hs1
  have h1_blk := (g2Subgroup_preserves_norm_trace hd₁ w).1
  let w₁ := (d₁.1 (embedJ12_cb w)).a
  have h1norm : w₁.norm = 0 := by rw [(g2Subgroup_preserves_norm_trace hd₁ w).2.1, hw_norm]
  -- Step 2: clear w using sl3_reduce_w_to_e0 + g2Short3
  have hs2 : ∃ d₂ ∈ g2Subgroup,
      let w₂ := (d₂.1 (embedJ12_cb w)).a
      w₂.a = 1 ∧ w₂.b = 0 ∧ w₂.w = 0 := by
    by_cases hw1 : w₁.w = 0
    · exact ⟨d₁, hd₁, h1a, h1b, hw1⟩
    · obtain ⟨dw, hdw_g2, hwa, hwb, hww0, hww1, hww2⟩ := sl3_reduce_w_to_e0 w₁ hw1
      have hdw_f := g2Subgroup.mul_mem hdw_g2 hd₁
      have hdw_blk := (g2Subgroup_preserves_norm_trace hdw_f w).1
      have hdw_eq : (dw * d₁).1 (embedJ12_cb w) = dw.1 (embedJ12_cb w₁) := by
        rw [hmul_act, h1_blk]
      let Xw := (dw * d₁).1 (embedJ12_cb w)
      have hXa : Xw.a.a = 1 := by change ((dw * d₁).1 (embedJ12_cb w)).a.a = 1; rw [hdw_eq, hwa]; exact h1a
      have hXb : Xw.a.b = 0 := by change ((dw * d₁).1 (embedJ12_cb w)).a.b = 0; rw [hdw_eq, hwb]; exact h1b
      have hXw0 : Xw.a.w 0 ≠ 0 := by change ((dw * d₁).1 (embedJ12_cb w)).a.w 0 ≠ 0; rw [hdw_eq]; exact hww0
      have hXw1 : Xw.a.w 1 = 0 := by change ((dw * d₁).1 (embedJ12_cb w)).a.w 1 = 0; rw [hdw_eq]; exact hww1
      have hXw2 : Xw.a.w 2 = 0 := by change ((dw * d₁).1 (embedJ12_cb w)).a.w 2 = 0; rw [hdw_eq]; exact hww2
      have hXnorm : Xw.a.norm = 0 := by rw [(g2Subgroup_preserves_norm_trace hdw_f w).2.1, hw_norm]
      have hXv0 : Xw.a.v 0 = 0 := by
        change Xw.a.a * Xw.a.b - ZornVec3.dot Xw.a.v Xw.a.w = 0 at hXnorm
        rw [hXa, hXb, one_mul, zero_sub] at hXnorm
        have hdot : ZornVec3.dot Xw.a.v Xw.a.w = Xw.a.v 0 * Xw.a.w 0 := by
          simp [ZornVec3.dot, Fin.sum_univ_three, hXw1, hXw2]
        rw [hdot, neg_eq_zero] at hXnorm
        exact (mul_eq_zero.mp hXnorm).resolve_right hXw0
      let t := -Xw.a.w 0
      have hc := g2Short3_a_coords t Xw
      refine ⟨g2Short3 t * (dw * d₁), g2Subgroup.mul_mem (g2Short3_mem_g2 t) hdw_f, ?_, ?_, ?_⟩
      · rw [hmul_act, hc.1, hXa, hXv0, mul_zero, sub_zero]
      · rw [hmul_act, hc.2.2.2.2.2.2.2, hXb, hXv0, mul_zero, add_zero]
      · have w0 : ((g2Short3 t * (dw * d₁)).1 (embedJ12_cb w)).a.w 0 = 0 := by
          rw [hmul_act, hc.2.2.2.2.1, hXa, hXb, hXv0]; dsimp [t]; ring
        have w1 : ((g2Short3 t * (dw * d₁)).1 (embedJ12_cb w)).a.w 1 = 0 := by
          rw [hmul_act, hc.2.2.2.2.2.1, hXw1]
        have w2 : ((g2Short3 t * (dw * d₁)).1 (embedJ12_cb w)).a.w 2 = 0 := by
          rw [hmul_act, hc.2.2.2.2.2.2.1, hXw2]
        exact fin3_fun_eq_zero _ w0 w1 w2
  obtain ⟨d₂, hd₂, h2a, h2b, h2w⟩ := hs2
  have h2_blk := (g2Subgroup_preserves_norm_trace hd₂ w).1
  let w₂ := (d₂.1 (embedJ12_cb w)).a
  -- Step 3: clear v using sl3_reduce_v_to_e0 + g2Short0
  by_cases hv2 : w₂.v = 0
  · refine ⟨d₂, hd₂, ?_⟩
    apply ZornVectorMatrix.ext <;> [exact h2a; exact hv2; exact h2w; exact h2b]
  · obtain ⟨dv, hdv_g2, _, hva, hvb, hvv0, hvv1, hvv2, hvw⟩ := sl3_reduce_v_to_e0 w₂ hv2
    have hdv_f := g2Subgroup.mul_mem hdv_g2 hd₂
    have hdv_eq : (dv * d₂).1 (embedJ12_cb w) = dv.1 (embedJ12_cb w₂) := by
      rw [hmul_act, h2_blk]
    let Xv := (dv * d₂).1 (embedJ12_cb w)
    have hXa : Xv.a.a = 1 := by change ((dv * d₂).1 (embedJ12_cb w)).a.a = 1; rw [hdv_eq, hva]; exact h2a
    have hXb : Xv.a.b = 0 := by change ((dv * d₂).1 (embedJ12_cb w)).a.b = 0; rw [hdv_eq, hvb]; exact h2b
    have hXv1 : Xv.a.v 1 = 0 := by change ((dv * d₂).1 (embedJ12_cb w)).a.v 1 = 0; rw [hdv_eq]; exact hvv1
    have hXv2 : Xv.a.v 2 = 0 := by change ((dv * d₂).1 (embedJ12_cb w)).a.v 2 = 0; rw [hdv_eq]; exact hvv2
    have hXw : Xv.a.w = 0 := by change ((dv * d₂).1 (embedJ12_cb w)).a.w = 0; rw [hdv_eq]; exact hvw h2w
    have hXw0 : Xv.a.w 0 = 0 := by rw [hXw]; rfl
    have hXw1 : Xv.a.w 1 = 0 := by rw [hXw]; rfl
    have hXw2 : Xv.a.w 2 = 0 := by rw [hXw]; rfl
    let t := -Xv.a.v 0
    have hc := g2Short0_a_coords t Xv
    refine ⟨g2Short0 t * (dv * d₂), g2Subgroup.mul_mem (g2Short0_mem_g2 t) hdv_f, ?_⟩
    apply ZornVectorMatrix.ext
    · rw [hmul_act, hc.1, hXa, hXw0, mul_zero, sub_zero]; rfl
    · have v0 : ((g2Short0 t * (dv * d₂)).1 (embedJ12_cb w)).a.v 0 = 0 := by
        rw [hmul_act, hc.2.1, hXa, hXb, hXw0]; dsimp [t]; ring
      have v1 : ((g2Short0 t * (dv * d₂)).1 (embedJ12_cb w)).a.v 1 = 0 := by
        rw [hmul_act, hc.2.2.1, hXv1]
      have v2 : ((g2Short0 t * (dv * d₂)).1 (embedJ12_cb w)).a.v 2 = 0 := by
        rw [hmul_act, hc.2.2.2.1, hXv2]
      exact fin3_fun_eq_zero _ v0 v1 v2
    · have w0 : ((g2Short0 t * (dv * d₂)).1 (embedJ12_cb w)).a.w 0 = 0 := by
        rw [hmul_act, hc.2.2.2.2.1, hXw0]
      have w1 : ((g2Short0 t * (dv * d₂)).1 (embedJ12_cb w)).a.w 1 = 0 := by
        rw [hmul_act, hc.2.2.2.2.2.1, hXw1, hXv2]; ring
      have w2 : ((g2Short0 t * (dv * d₂)).1 (embedJ12_cb w)).a.w 2 = 0 := by
        rw [hmul_act, hc.2.2.2.2.2.2.1, hXw2, hXv1]; ring
      exact fin3_fun_eq_zero _ w0 w1 w2
    · rw [hmul_act, hc.2.2.2.2.2.2.2, hXb, hXw0, mul_zero, add_zero]; rfl

private theorem sl3_torus12_a_coords (r : ℝ) (hr : r ≠ 0) (X : H3Zorn ℝ) :
    ∃ d ∈ g2Subgroup, d.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 ∧
    (d.1 X).a.a = X.a.a ∧ (d.1 X).a.b = X.a.b ∧
    (d.1 X).a.v 0 = r⁻¹ * X.a.v 0 ∧ (d.1 X).a.v 1 = r * X.a.v 1 ∧ (d.1 X).a.v 2 = X.a.v 2 ∧
    (d.1 X).a.w 0 = r * X.a.w 0 ∧ (d.1 X).a.w 1 = r⁻¹ * X.a.w 1 ∧ (d.1 X).a.w 2 = X.a.w 2 := by
  have w12_coords : ∀ (s : ℝ) (hs : s ≠ 0) (Z : H3Zorn ℝ),
      let w := e6RootExp 12 s * (e6RootExp 8 (-s⁻¹) * e6RootExp 12 s)
      w ∈ g2Subgroup ∧ w.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 ∧
      (w.1 Z).a.a = Z.a.a ∧ (w.1 Z).a.b = Z.a.b ∧
      (w.1 Z).a.v 0 = s⁻¹ * Z.a.v 1 ∧ (w.1 Z).a.v 1 = -s * Z.a.v 0 ∧ (w.1 Z).a.v 2 = Z.a.v 2 ∧
      (w.1 Z).a.w 0 = s * Z.a.w 1 ∧ (w.1 Z).a.w 1 = -s⁻¹ * Z.a.w 0 ∧ (w.1 Z).a.w 2 = Z.a.w 2 := by
    intro s hs Z
    have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
        (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
    refine ⟨g2Subgroup.mul_mem (sl3_mem_g2 2 s) (g2Subgroup.mul_mem (sl3_mem_g2 0 (-s⁻¹)) (sl3_mem_g2 2 s)),
      ?_, ?_⟩
    · have hf0 : (e6RootExp 8 (-s⁻¹)).1 (embedJ12_cb ZornVectorMatrix.E11) =
          embedJ12_cb ZornVectorMatrix.E11 := sl3_fix_E11 0 (-s⁻¹)
      have hf2 : (e6RootExp 12 s).1 (embedJ12_cb ZornVectorMatrix.E11) =
          embedJ12_cb ZornVectorMatrix.E11 := sl3_fix_E11 2 s
      have ha1 : (e6RootExp 8 (-s⁻¹) * e6RootExp 12 s).1 (embedJ12_cb ZornVectorMatrix.E11) =
          embedJ12_cb ZornVectorMatrix.E11 := by
        rw [hmul_act, hf2, hf0]
      rw [hmul_act, ha1, hf2]
    · let Z1 := (e6RootExp 12 s).1 Z
      let Z2 := (e6RootExp 8 (-s⁻¹)).1 Z1
      let Z3 := (e6RootExp 12 s).1 Z2
      have ha1 : (e6RootExp 8 (-s⁻¹) * e6RootExp 12 s).1 Z = Z2 := rfl
      have ha2 : (e6RootExp 12 s * (e6RootExp 8 (-s⁻¹) * e6RootExp 12 s)).1 Z = Z3 := by
        rw [hmul_act, ha1]
      rw [ha2]
      have h1 := sl3_12_a_coords s Z
      have h2 := sl3_8_a_coords (-s⁻¹) Z1
      have h3 := sl3_12_a_coords s Z2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h3.1, h2.1, h1.1]
      · rw [h3.2.2.2.2.2.2.2, h2.2.2.2.2.2.2.2, h1.2.2.2.2.2.2.2]
      · rw [h3.2.1, h2.2.1, h1.2.1, h1.2.2.1]; field_simp [hs]; ring
      · rw [h3.2.2.1, h2.2.1, h2.2.2.1, h1.2.1, h1.2.2.1]; field_simp [hs]; ring
      · rw [h3.2.2.2.1, h2.2.2.2.1, h1.2.2.2.1]
      · rw [h3.2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1]; field_simp [hs]; ring
      · rw [h3.2.2.2.2.2.1, h2.2.2.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1]; field_simp [hs]; ring
      · rw [h3.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.1]
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  obtain ⟨hmg1, hE1, ha1, hb1, hv10, hv11, hv12, hw10, hw11, hw12⟩ := w12_coords (-1) (by norm_num) X
  have h1m : -((-1 : ℝ)⁻¹) = 1 := by norm_num
  rw [h1m] at hmg1 hE1 ha1 hb1 hv10 hv11 hv12 hw10 hw11 hw12
  let X1 := (e6RootExp 12 (-1) * (e6RootExp 8 1 * e6RootExp 12 (-1))).1 X
  obtain ⟨hmg2, hE2, ha2, hb2, hv20, hv21, hv22, hw20, hw21, hw22⟩ := w12_coords r hr X1
  refine ⟨_, g2Subgroup.mul_mem hmg2 hmg1, ?_, ?_⟩
  · change (e6RootExp 12 r * (e6RootExp 8 (-r⁻¹) * e6RootExp 12 r)).1
        ((e6RootExp 12 (-1) * (e6RootExp 8 1 * e6RootExp 12 (-1))).1
          (embedJ12_cb ZornVectorMatrix.E11)) = embedJ12_cb ZornVectorMatrix.E11
    rw [hE1]; exact hE2
  · have hact : ((e6RootExp 12 r * (e6RootExp 8 (-r⁻¹) * e6RootExp 12 r)) *
        (e6RootExp 12 (-1) * (e6RootExp 8 1 * e6RootExp 12 (-1)))).1 X =
        (e6RootExp 12 r * (e6RootExp 8 (-r⁻¹) * e6RootExp 12 r)).1 X1 := rfl
    rw [hact]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha2, ha1]
    · rw [hb2, hb1]
    · rw [hv20, hv11]; ring
    · rw [hv21, hv10]; ring
    · rw [hv22, hv12]
    · rw [hw20, hw11]; ring
    · rw [hw21, hw10]; ring
    · rw [hw22, hw12]

private theorem sl3_torus23_a_coords (r : ℝ) (hr : r ≠ 0) (X : H3Zorn ℝ) :
    ∃ d ∈ g2Subgroup,
    d.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 ∧
    d.1 (embedJ12_cb (ZornVectorMatrix.U 0)) = embedJ12_cb (ZornVectorMatrix.U 0) ∧
    (d.1 X).a.a = X.a.a ∧ (d.1 X).a.b = X.a.b ∧
    (d.1 X).a.v 0 = X.a.v 0 ∧ (d.1 X).a.v 1 = r⁻¹ * X.a.v 1 ∧ (d.1 X).a.v 2 = r * X.a.v 2 := by
  have hfixU0 : ∀ (j : Fin 6) (t : ℝ), j = 3 ∨ j = 5 →
      (e6RootExp (sl3Idx j) t).1 (embedJ12_cb (ZornVectorMatrix.U 0)) =
        embedJ12_cb (ZornVectorMatrix.U 0) := by
    intro j t hj
    refine e6RootExp_fix_of_cols_outside t (embedJ12_cb (ZornVectorMatrix.U 0)) fun m k hk => ?_
    have hc : (List.finRange 27).all (fun m =>
        sparseVal (e6RootSparse 13) m 4 == 0 &&
        sparseVal (e6RootSparse 16) m 4 == 0) = true := by decide
    simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, beq_iff_eq,
      true_implies] at hc
    fin_cases k
    all_goals first
      | (rcases hj with rfl | rfl; exact (hc m).1; exact (hc m).2)
      | exact absurd rfl hk
  have w23_coords : ∀ (s : ℝ) (hs : s ≠ 0) (Z : H3Zorn ℝ),
      let w := e6RootExp 16 s * (e6RootExp 13 (-s⁻¹) * e6RootExp 16 s)
      w ∈ g2Subgroup ∧
      w.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 ∧
      w.1 (embedJ12_cb (ZornVectorMatrix.U 0)) = embedJ12_cb (ZornVectorMatrix.U 0) ∧
      (w.1 Z).a.a = Z.a.a ∧ (w.1 Z).a.b = Z.a.b ∧
      (w.1 Z).a.v 0 = Z.a.v 0 ∧ (w.1 Z).a.v 1 = s⁻¹ * Z.a.v 2 ∧ (w.1 Z).a.v 2 = -s * Z.a.v 1 := by
    intro s hs Z
    have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
        (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
    refine ⟨g2Subgroup.mul_mem (sl3_mem_g2 5 s) (g2Subgroup.mul_mem (sl3_mem_g2 3 (-s⁻¹)) (sl3_mem_g2 5 s)),
      ?_, ?_, ?_⟩
    · have hf3 : (e6RootExp 13 (-s⁻¹)).1 (embedJ12_cb ZornVectorMatrix.E11) =
          embedJ12_cb ZornVectorMatrix.E11 := sl3_fix_E11 3 (-s⁻¹)
      have hf5 : (e6RootExp 16 s).1 (embedJ12_cb ZornVectorMatrix.E11) =
          embedJ12_cb ZornVectorMatrix.E11 := sl3_fix_E11 5 s
      have ha1 : (e6RootExp 13 (-s⁻¹) * e6RootExp 16 s).1 (embedJ12_cb ZornVectorMatrix.E11) =
          embedJ12_cb ZornVectorMatrix.E11 := by
        rw [hmul_act, hf5, hf3]
      rw [hmul_act, ha1, hf5]
    · have hu3 : (e6RootExp 13 (-s⁻¹)).1 (embedJ12_cb (ZornVectorMatrix.U 0)) =
          embedJ12_cb (ZornVectorMatrix.U 0) := hfixU0 3 (-s⁻¹) (Or.inl rfl)
      have hu5 : (e6RootExp 16 s).1 (embedJ12_cb (ZornVectorMatrix.U 0)) =
          embedJ12_cb (ZornVectorMatrix.U 0) := hfixU0 5 s (Or.inr rfl)
      have ha1 : (e6RootExp 13 (-s⁻¹) * e6RootExp 16 s).1 (embedJ12_cb (ZornVectorMatrix.U 0)) =
          embedJ12_cb (ZornVectorMatrix.U 0) := by
        rw [hmul_act, hu5, hu3]
      rw [hmul_act, ha1, hu5]
    · let Z1 := (e6RootExp 16 s).1 Z
      let Z2 := (e6RootExp 13 (-s⁻¹)).1 Z1
      let Z3 := (e6RootExp 16 s).1 Z2
      have ha1 : (e6RootExp 13 (-s⁻¹) * e6RootExp 16 s).1 Z = Z2 := rfl
      have ha2 : (e6RootExp 16 s * (e6RootExp 13 (-s⁻¹) * e6RootExp 16 s)).1 Z = Z3 := by
        rw [hmul_act, ha1]
      rw [ha2]
      have h1 := sl3_16_a_coords s Z
      have h2 := sl3_13_a_coords (-s⁻¹) Z1
      have h3 := sl3_16_a_coords s Z2
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [h3.1, h2.1, h1.1]
      · rw [h3.2.2.2.2.2.2.2, h2.2.2.2.2.2.2.2, h1.2.2.2.2.2.2.2]
      · rw [h3.2.1, h2.2.1, h1.2.1]
      · rw [h3.2.2.1, h2.2.2.1, h1.2.2.1, h1.2.2.2.1]; field_simp [hs]; ring
      · rw [h3.2.2.2.1, h2.2.2.1, h2.2.2.2.1, h1.2.2.1, h1.2.2.2.1]; field_simp [hs]; ring
  obtain ⟨hmg1, hE1, hU1, ha1, hb1, hv10, hv11, hv12⟩ := w23_coords (-1) (by norm_num) X
  have h1m : -((-1 : ℝ)⁻¹) = 1 := by norm_num
  rw [h1m] at hmg1 hE1 hU1 ha1 hb1 hv10 hv11 hv12
  let X1 := (e6RootExp 16 (-1) * (e6RootExp 13 1 * e6RootExp 16 (-1))).1 X
  obtain ⟨hmg2, hE2, hU2, ha2, hb2, hv20, hv21, hv22⟩ := w23_coords r hr X1
  refine ⟨_, g2Subgroup.mul_mem hmg2 hmg1, ?_, ?_, ?_⟩
  · change (e6RootExp 16 r * (e6RootExp 13 (-r⁻¹) * e6RootExp 16 r)).1
        ((e6RootExp 16 (-1) * (e6RootExp 13 1 * e6RootExp 16 (-1))).1
          (embedJ12_cb ZornVectorMatrix.E11)) = embedJ12_cb ZornVectorMatrix.E11
    rw [hE1]; exact hE2
  · change (e6RootExp 16 r * (e6RootExp 13 (-r⁻¹) * e6RootExp 16 r)).1
        ((e6RootExp 16 (-1) * (e6RootExp 13 1 * e6RootExp 16 (-1))).1
          (embedJ12_cb (ZornVectorMatrix.U 0))) = embedJ12_cb (ZornVectorMatrix.U 0)
    rw [hU1]; exact hU2
  · have hact : ((e6RootExp 16 r * (e6RootExp 13 (-r⁻¹) * e6RootExp 16 r)) *
        (e6RootExp 16 (-1) * (e6RootExp 13 1 * e6RootExp 16 (-1)))).1 X =
        (e6RootExp 16 r * (e6RootExp 13 (-r⁻¹) * e6RootExp 16 r)).1 X1 := rfl
    rw [hact]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [ha2, ha1]
    · rw [hb2, hb1]
    · rw [hv20, hv10]
    · rw [hv21, hv12]; ring
    · rw [hv22, hv11]; ring

private theorem sl3_reduce_U_to_U0 (u : ZornVectorMatrix ℝ)
    (hu_in : u.a = 0 ∧ u.w = 0 ∧ u.b = 0) (hu_ne : u ≠ 0) :
    ∃ d ∈ g2Subgroup,
      d.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 ∧
      (d.1 (embedJ12_cb u)).a = ZornVectorMatrix.U 0 := by
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  have hv_ne : u.v ≠ 0 := fun hv => hu_ne (ZornVectorMatrix.ext hu_in.1 hv hu_in.2.1 hu_in.2.2)
  obtain ⟨d₁, hd₁, h1E, h1a, h1b, h1v0, h1v1, h1v2, h1w⟩ := sl3_reduce_v_to_e0 u hv_ne
  have h1w0 : (d₁.1 (embedJ12_cb u)).a.w = 0 := h1w hu_in.2.1
  let X₁ := d₁.1 (embedJ12_cb u)
  let r := X₁.a.v 0
  have hr : r ≠ 0 := h1v0
  obtain ⟨d₂, hd₂, h2E, h2a, h2b, h2v0, h2v1, h2v2, h2w0, h2w1, h2w2⟩ := sl3_torus12_a_coords r hr X₁
  refine ⟨d₂ * d₁, g2Subgroup.mul_mem hd₂ hd₁, ?_, ?_⟩
  · rw [hmul_act, h1E]; exact h2E
  · change (d₂.1 X₁).a = ZornVectorMatrix.U 0
    apply ZornVectorMatrix.ext
    · rw [h2a, h1a, hu_in.1]; rfl
    · have v0 : (d₂.1 X₁).a.v 0 = (ZornVectorMatrix.U 0).v 0 := by
        rw [h2v0]; change r⁻¹ * r = 1; field_simp [hr]
      have v1 : (d₂.1 X₁).a.v 1 = (ZornVectorMatrix.U 0).v 1 := by rw [h2v1, h1v1, mul_zero]; rfl
      have v2 : (d₂.1 X₁).a.v 2 = (ZornVectorMatrix.U 0).v 2 := by rw [h2v2, h1v2]; rfl
      exact fin3_fun_eq _ _ v0 v1 v2
    · have w0 : (d₂.1 X₁).a.w 0 = 0 := by rw [h2w0, h1w0]; simp
      have w1 : (d₂.1 X₁).a.w 1 = 0 := by rw [h2w1, h1w0]; simp
      have w2 : (d₂.1 X₁).a.w 2 = 0 := by rw [h2w2, h1w0]; rfl
      exact fin3_fun_eq_zero _ w0 w1 w2
    · rw [h2b, h1b, hu_in.2.2]; rfl

private theorem sl3_fixU0_cols (j : Fin 6) (t : ℝ) (hj : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 5) :
    (e6RootExp (sl3Idx j) t).1 (embedJ12_cb (ZornVectorMatrix.U 0)) =
      embedJ12_cb (ZornVectorMatrix.U 0) := by
  refine e6RootExp_fix_of_cols_outside t (embedJ12_cb (ZornVectorMatrix.U 0)) fun m k hk => ?_
  have hc : (List.finRange 27).all (fun m =>
      sparseVal (e6RootSparse 8) m 4 == 0 &&
      sparseVal (e6RootSparse 9) m 4 == 0 &&
      sparseVal (e6RootSparse 13) m 4 == 0 &&
      sparseVal (e6RootSparse 16) m 4 == 0) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, beq_iff_eq,
    true_implies] at hc
  fin_cases k
  all_goals first
    | (rcases hj with rfl | rfl | rfl | rfl; exact (hc m).1.1.1; exact (hc m).1.1.2;
        exact (hc m).1.2; exact (hc m).2)
    | exact absurd rfl hk

private theorem sl3_reduce_U_to_U1_fixing_U0 (u : ZornVectorMatrix ℝ)
    (hu_in : u.a = 0 ∧ u.w = 0 ∧ u.b = 0) (hu_12 : u.v 1 ≠ 0 ∨ u.v 2 ≠ 0) :
    ∃ d ∈ g2Subgroup,
      d.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 ∧
      d.1 (embedJ12_cb (ZornVectorMatrix.U 0)) = embedJ12_cb (ZornVectorMatrix.U 0) ∧
      (d.1 (embedJ12_cb u)).a = ZornVectorMatrix.U 1 := by
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  have hs1 : ∃ d₁ ∈ g2Subgroup,
      d₁.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 ∧
      d₁.1 (embedJ12_cb (ZornVectorMatrix.U 0)) = embedJ12_cb (ZornVectorMatrix.U 0) ∧
      (d₁.1 (embedJ12_cb u)).a.a = 0 ∧ (d₁.1 (embedJ12_cb u)).a.b = 0 ∧
      (d₁.1 (embedJ12_cb u)).a.w = 0 ∧ (d₁.1 (embedJ12_cb u)).a.v 1 ≠ 0 := by
    by_cases hv1 : u.v 1 ≠ 0
    · exact ⟨1, g2Subgroup.one_mem, rfl, rfl, hu_in.1, hu_in.2.2, hu_in.2.1, hv1⟩
    · push Not at hv1
      have hv2 : u.v 2 ≠ 0 := hu_12.resolve_left (not_not.mpr hv1)
      have hfE : (e6RootExp 13 1).1 (embedJ12_cb ZornVectorMatrix.E11) =
          embedJ12_cb ZornVectorMatrix.E11 := sl3_fix_E11 3 1
      have hfU : (e6RootExp 13 1).1 (embedJ12_cb (ZornVectorMatrix.U 0)) =
          embedJ12_cb (ZornVectorMatrix.U 0) := sl3_fixU0_cols 3 1 (Or.inr (Or.inr (Or.inl rfl)))
      refine ⟨e6RootExp 13 1, sl3_mem_g2 3 1, hfE, hfU, ?_⟩
      have hc := sl3_13_a_coords 1 (embedJ12_cb u)
      refine ⟨by rw [hc.1]; exact hu_in.1, by rw [hc.2.2.2.2.2.2.2]; exact hu_in.2.2, ?_, ?_⟩
      · have w0 : ((e6RootExp 13 1).1 (embedJ12_cb u)).a.w 0 = 0 := by
          rw [hc.2.2.2.2.1]; change u.w 0 = 0; rw [hu_in.2.1]; rfl
        have w1 : ((e6RootExp 13 1).1 (embedJ12_cb u)).a.w 1 = 0 := by
          rw [hc.2.2.2.2.2.1]; change u.w 1 = 0; rw [hu_in.2.1]; rfl
        have w2 : ((e6RootExp 13 1).1 (embedJ12_cb u)).a.w 2 = 0 := by
          rw [hc.2.2.2.2.2.2.1]; change u.w 2 + 1 * u.w 1 = 0; rw [hu_in.2.1]; simp
        exact fin3_fun_eq_zero _ w0 w1 w2
      · rw [hc.2.2.1]; change u.v 1 - 1 * u.v 2 ≠ 0; rw [hv1, zero_sub, one_mul, neg_ne_zero]; exact hv2
  obtain ⟨d₁, hd₁, h1E, h1U, h1a, h1b, h1w, h1v1⟩ := hs1
  let X₁ := d₁.1 (embedJ12_cb u)
  have h1v1' : X₁.a.v 1 ≠ 0 := h1v1
  let t₂ := X₁.a.v 2 / X₁.a.v 1
  let d₂ := e6RootExp 16 t₂
  let X₂ := d₂.1 X₁
  have hc2 := sl3_16_a_coords t₂ X₁
  have h2a : X₂.a.a = 0 := by change ((e6RootExp 16 t₂).1 X₁).a.a = 0; rw [hc2.1, h1a]
  have h2b : X₂.a.b = 0 := by change ((e6RootExp 16 t₂).1 X₁).a.b = 0; rw [hc2.2.2.2.2.2.2.2, h1b]
  have h2v1 : X₂.a.v 1 ≠ 0 := by change ((e6RootExp 16 t₂).1 X₁).a.v 1 ≠ 0; rw [hc2.2.2.1]; exact h1v1'
  have h2v2 : X₂.a.v 2 = 0 := by
    change ((e6RootExp 16 t₂).1 X₁).a.v 2 = 0; rw [hc2.2.2.2.1]; dsimp [t₂]; field_simp [h1v1']; ring
  have h2w : X₂.a.w = 0 := by
    have w0 : X₂.a.w 0 = 0 := by
      change ((e6RootExp 16 t₂).1 X₁).a.w 0 = 0; rw [hc2.2.2.2.2.1, h1w]; rfl
    have w1 : X₂.a.w 1 = 0 := by
      change ((e6RootExp 16 t₂).1 X₁).a.w 1 = 0; rw [hc2.2.2.2.2.2.1, h1w]; simp
    have w2 : X₂.a.w 2 = 0 := by
      change ((e6RootExp 16 t₂).1 X₁).a.w 2 = 0; rw [hc2.2.2.2.2.2.2.1, h1w]; rfl
    exact fin3_fun_eq_zero _ w0 w1 w2
  let r := X₂.a.v 1
  have hr : r ≠ 0 := h2v1
  obtain ⟨d₃, hd₃, h3E, h3U, h3a, h3b, h3v0, h3v1, h3v2⟩ := sl3_torus23_a_coords r hr X₂
  let X₃ := d₃.1 X₂
  have h3w : X₃.a.w = 0 := by
    have hdx2 : d₃.1 (embedJ12_cb X₂.a) = embedJ12_cb (d₃.1 (embedJ12_cb X₂.a)).a :=
      (g2Subgroup_preserves_norm_trace hd₃ X₂.a).1
    have hX2_blk := (g2Subgroup_preserves_norm_trace
      (g2Subgroup.mul_mem (sl3_mem_g2 5 t₂) hd₁) u).1
    have hX2_eq : X₂ = embedJ12_cb X₂.a := hX2_blk
    have hfix_d3 := g2Subgroup_le_f4 hd₃
    have hfix_d := d4Subgroup_fix_diags hd₃.1
    obtain ⟨g₃, _, _, hg3_mul, _, _, hg3_act⟩ :=
      triality_of_fix_diags_and_ones hfix_d3.2 hfix_d.1 hfix_d.2.1 hfix_d.2.2 hd₃.2.1 hd₃.2.2
    have hg3_E11 : g₃ ZornVectorMatrix.E11 = ZornVectorMatrix.E11 := by
      have h := congrArg H3Zorn.a h3E
      rw [hg3_act (embedJ12_cb ZornVectorMatrix.E11)] at h; exact h
    have hg3_X2 : g₃ X₂.a = X₃.a := by
      change g₃ X₂.a = (d₃.1 X₂).a
      rw [hX2_eq, hg3_act]
    have hX2_mulE : ZornVectorMatrix.mul X₂.a ZornVectorMatrix.E11 = 0 := by
      apply ZornVectorMatrix.ext
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot, h2a]
      · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross]
      · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross, h2w]
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot, h2b]
    have hmul0 := congrArg g₃ hX2_mulE
    rw [hg3_mul, hg3_X2, hg3_E11, map_zero] at hmul0
    funext k
    have hk := congrArg (fun z : ZornVectorMatrix ℝ => z.w k) hmul0
    simpa [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross] using hk
  let c := X₃.a.v 0
  let d₄ := e6RootExp 8 c
  have hc4 := sl3_8_a_coords c X₃
  refine ⟨d₄ * (d₃ * (d₂ * d₁)),
    g2Subgroup.mul_mem (sl3_mem_g2 0 c)
      (g2Subgroup.mul_mem hd₃ (g2Subgroup.mul_mem (sl3_mem_g2 5 t₂) hd₁)), ?_, ?_, ?_⟩
  · have hfix2 : (e6RootExp 16 t₂).1 (embedJ12_cb ZornVectorMatrix.E11) =
        embedJ12_cb ZornVectorMatrix.E11 := sl3_fix_E11 5 t₂
    have hfix4 : (e6RootExp 8 c).1 (embedJ12_cb ZornVectorMatrix.E11) =
        embedJ12_cb ZornVectorMatrix.E11 := sl3_fix_E11 0 c
    have h2E : (d₂ * d₁).1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 := by
      rw [hmul_act, h1E]; exact hfix2
    have h3E' : (d₃ * (d₂ * d₁)).1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 := by
      rw [hmul_act, h2E]; exact h3E
    rw [hmul_act, h3E']; exact hfix4
  · have hfix2u : (e6RootExp 16 t₂).1 (embedJ12_cb (ZornVectorMatrix.U 0)) =
        embedJ12_cb (ZornVectorMatrix.U 0) := sl3_fixU0_cols 5 t₂ (Or.inr (Or.inr (Or.inr rfl)))
    have hfix4u : (e6RootExp 8 c).1 (embedJ12_cb (ZornVectorMatrix.U 0)) =
        embedJ12_cb (ZornVectorMatrix.U 0) := sl3_fixU0_cols 0 c (Or.inl rfl)
    have h2U : (d₂ * d₁).1 (embedJ12_cb (ZornVectorMatrix.U 0)) = embedJ12_cb (ZornVectorMatrix.U 0) := by
      rw [hmul_act, h1U]; exact hfix2u
    have h3U' : (d₃ * (d₂ * d₁)).1 (embedJ12_cb (ZornVectorMatrix.U 0)) = embedJ12_cb (ZornVectorMatrix.U 0) := by
      rw [hmul_act, h2U]; exact h3U
    rw [hmul_act, h3U']; exact hfix4u
  · have hact : (d₄ * (d₃ * (d₂ * d₁))).1 (embedJ12_cb u) = d₄.1 X₃ := by
      have ha1 : (d₂ * d₁).1 (embedJ12_cb u) = X₂ := rfl
      have ha2 : (d₃ * (d₂ * d₁)).1 (embedJ12_cb u) = X₃ := by rw [hmul_act, ha1]
      rw [hmul_act, ha2]
    rw [hact]
    apply ZornVectorMatrix.ext
    · rw [hc4.1, h3a, h2a]; rfl
    · have v0 : (d₄.1 X₃).a.v 0 = (ZornVectorMatrix.U 1).v 0 := by
        change ((e6RootExp 8 c).1 X₃).a.v 0 = 0
        rw [hc4.2.1, h3v1]; change c - c * (r⁻¹ * r) = 0; field_simp [hr]; ring
      have v1 : (d₄.1 X₃).a.v 1 = (ZornVectorMatrix.U 1).v 1 := by
        change ((e6RootExp 8 c).1 X₃).a.v 1 = 1
        rw [hc4.2.2.1, h3v1]; change r⁻¹ * r = 1; field_simp [hr]
      have v2 : (d₄.1 X₃).a.v 2 = (ZornVectorMatrix.U 1).v 2 := by
        change ((e6RootExp 8 c).1 X₃).a.v 2 = 0
        rw [hc4.2.2.2.1, h3v2, h2v2, mul_zero]
      exact fin3_fun_eq _ _ v0 v1 v2
    · have w0 : (d₄.1 X₃).a.w 0 = 0 := by
        change ((e6RootExp 8 c).1 X₃).a.w 0 = 0; rw [hc4.2.2.2.2.1, h3w]; rfl
      have w1 : (d₄.1 X₃).a.w 1 = 0 := by
        change ((e6RootExp 8 c).1 X₃).a.w 1 = 0; rw [hc4.2.2.2.2.2.1, h3w]; simp
      have w2 : (d₄.1 X₃).a.w 2 = 0 := by
        change ((e6RootExp 8 c).1 X₃).a.w 2 = 0; rw [hc4.2.2.2.2.2.2.1, h3w]; rfl
      exact fin3_fun_eq_zero _ w0 w1 w2
    · rw [hc4.2.2.2.2.2.2.2, h3b, h2b]; rfl

private theorem sl3_reduce_U_to_U2_fixing_U0_U1 (u : ZornVectorMatrix ℝ)
    (hu_in : u.a = 0 ∧ u.w = 0 ∧ u.b = 0) (hu2 : u.v 2 = 1) :
    ∃ d ∈ g2Subgroup,
      d.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 ∧
      d.1 (embedJ12_cb (ZornVectorMatrix.U 0)) = embedJ12_cb (ZornVectorMatrix.U 0) ∧
      d.1 (embedJ12_cb (ZornVectorMatrix.U 1)) = embedJ12_cb (ZornVectorMatrix.U 1) ∧
      (d.1 (embedJ12_cb u)).a = ZornVectorMatrix.U 2 := by
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  have hfixU1 : ∀ (j : Fin 6) (t : ℝ), j = 1 ∨ j = 3 →
      (e6RootExp (sl3Idx j) t).1 (embedJ12_cb (ZornVectorMatrix.U 1)) =
        embedJ12_cb (ZornVectorMatrix.U 1) := by
    intro j t hj
    refine e6RootExp_fix_of_cols_outside t (embedJ12_cb (ZornVectorMatrix.U 1)) fun m k hk => ?_
    have hc : (List.finRange 27).all (fun m =>
        sparseVal (e6RootSparse 9) m 5 == 0 &&
        sparseVal (e6RootSparse 13) m 5 == 0) = true := by decide
    simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, beq_iff_eq,
      true_implies] at hc
    fin_cases k
    all_goals first
      | (rcases hj with rfl | rfl; exact (hc m).1; exact (hc m).2)
      | exact absurd rfl hk
  let c0 := u.v 0
  let c1 := u.v 1
  let d₁ := e6RootExp 9 c0
  let d₂ := e6RootExp 13 c1
  let X₁ := d₁.1 (embedJ12_cb u)
  let X₂ := d₂.1 X₁
  have hc1 := sl3_9_a_coords c0 (embedJ12_cb u)
  have hc2 := sl3_13_a_coords c1 X₁
  have hf1E : (e6RootExp 9 c0).1 (embedJ12_cb ZornVectorMatrix.E11) =
      embedJ12_cb ZornVectorMatrix.E11 := sl3_fix_E11 1 c0
  have hf2E : (e6RootExp 13 c1).1 (embedJ12_cb ZornVectorMatrix.E11) =
      embedJ12_cb ZornVectorMatrix.E11 := sl3_fix_E11 3 c1
  have hf1U0 : (e6RootExp 9 c0).1 (embedJ12_cb (ZornVectorMatrix.U 0)) =
      embedJ12_cb (ZornVectorMatrix.U 0) := sl3_fixU0_cols 1 c0 (Or.inr (Or.inl rfl))
  have hf2U0 : (e6RootExp 13 c1).1 (embedJ12_cb (ZornVectorMatrix.U 0)) =
      embedJ12_cb (ZornVectorMatrix.U 0) := sl3_fixU0_cols 3 c1 (Or.inr (Or.inr (Or.inl rfl)))
  have hf1U1 : (e6RootExp 9 c0).1 (embedJ12_cb (ZornVectorMatrix.U 1)) =
      embedJ12_cb (ZornVectorMatrix.U 1) := hfixU1 1 c0 (Or.inl rfl)
  have hf2U1 : (e6RootExp 13 c1).1 (embedJ12_cb (ZornVectorMatrix.U 1)) =
      embedJ12_cb (ZornVectorMatrix.U 1) := hfixU1 3 c1 (Or.inr rfl)
  refine ⟨d₂ * d₁, g2Subgroup.mul_mem (sl3_mem_g2 3 c1) (sl3_mem_g2 1 c0), ?_, ?_, ?_, ?_⟩
  · rw [hmul_act, hf1E, hf2E]
  · rw [hmul_act, hf1U0, hf2U0]
  · rw [hmul_act, hf1U1, hf2U1]
  · change X₂.a = ZornVectorMatrix.U 2
    apply ZornVectorMatrix.ext
    · change ((e6RootExp 13 c1).1 X₁).a.a = _; rw [hc2.1, hc1.1]; change u.a = 0; rw [hu_in.1]
    · have v0 : X₂.a.v 0 = 0 := by
        change ((e6RootExp 13 c1).1 X₁).a.v 0 = 0
        rw [hc2.2.1, hc1.2.1]; change u.v 0 - c0 * u.v 2 = 0; rw [hu2]; dsimp [c0]; ring
      have v1 : X₂.a.v 1 = 0 := by
        change ((e6RootExp 13 c1).1 X₁).a.v 1 = 0
        rw [hc2.2.2.1, hc1.2.2.1, hc1.2.2.2.1]; change u.v 1 - c1 * u.v 2 = 0
        rw [hu2]; dsimp [c1]; ring
      have v2 : X₂.a.v 2 = 1 := by
        change ((e6RootExp 13 c1).1 X₁).a.v 2 = 1
        rw [hc2.2.2.2.1, hc1.2.2.2.1]; change u.v 2 = 1; exact hu2
      have hv0' : X₂.a.v 0 = (ZornVectorMatrix.U 2).v 0 := v0
      have hv1' : X₂.a.v 1 = (ZornVectorMatrix.U 2).v 1 := v1
      have hv2' : X₂.a.v 2 = (ZornVectorMatrix.U 2).v 2 := v2
      exact fin3_fun_eq _ _ hv0' hv1' hv2'
    · have w0 : X₂.a.w 0 = 0 := by
        change ((e6RootExp 13 c1).1 X₁).a.w 0 = 0
        rw [hc2.2.2.2.2.1, hc1.2.2.2.2.1]; change u.w 0 = 0; rw [hu_in.2.1]; rfl
      have w1 : X₂.a.w 1 = 0 := by
        change ((e6RootExp 13 c1).1 X₁).a.w 1 = 0
        rw [hc2.2.2.2.2.2.1, hc1.2.2.2.2.2.1]; change u.w 1 = 0; rw [hu_in.2.1]; rfl
      have w2 : X₂.a.w 2 = 0 := by
        change ((e6RootExp 13 c1).1 X₁).a.w 2 = 0
        rw [hc2.2.2.2.2.2.2.1, hc1.2.2.2.2.2.2.1, hc1.2.2.2.2.2.1]
        have huw : u.w = 0 := hu_in.2.1
        change (embedJ12_cb u).a.w 2 + c0 * (embedJ12_cb u).a.w 0 +
          c1 * (embedJ12_cb u).a.w 1 = 0
        change u.w 2 + c0 * u.w 0 + c1 * u.w 1 = 0
        rw [huw]; simp
      exact fin3_fun_eq_zero _ w0 w1 w2
    · change ((e6RootExp 13 c1).1 X₁).a.b = _; rw [hc2.2.2.2.2.2.2.2, hc1.2.2.2.2.2.2.2]
      change u.b = 0; rw [hu_in.2.2]

private theorem g2_kill_fix_diags_and_ones {f : h3zornReducedStructureGroup}
    (hf : f.1 1 = 1)
    (h1 : f.1 h3_diag₁ = h3_diag₁)
    (h2 : f.1 h3_diag₂ = h3_diag₂)
    (h3 : f.1 h3_diag₃ = h3_diag₃)
    (h12 : f.1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one)
    (h23 : f.1 (embedJ23_cb ZornVectorMatrix.one) = embedJ23_cb ZornVectorMatrix.one) :
    f ∈ d4Subgroup := by
  have hmul_act : ∀ (a b : h3zornReducedStructureGroup) (Z : H3Zorn ℝ),
      (a * b).1 Z = a.1 (b.1 Z) := fun _ _ _ => rfl
  have hstep_fix : ∀ (d : h3zornReducedStructureGroup) (g : h3zornReducedStructureGroup),
      d ∈ g2Subgroup → g.1 1 = 1 →
      g.1 h3_diag₁ = h3_diag₁ → g.1 h3_diag₂ = h3_diag₂ → g.1 h3_diag₃ = h3_diag₃ →
      g.1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one →
      g.1 (embedJ23_cb ZornVectorMatrix.one) = embedJ23_cb ZornVectorMatrix.one →
      (d * g).1 1 = 1 ∧
      (d * g).1 h3_diag₁ = h3_diag₁ ∧ (d * g).1 h3_diag₂ = h3_diag₂ ∧
      (d * g).1 h3_diag₃ = h3_diag₃ ∧
      (d * g).1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one ∧
      (d * g).1 (embedJ23_cb ZornVectorMatrix.one) = embedJ23_cb ZornVectorMatrix.one := by
    intro d g hd hg hg1 hg2 hg3 hg12 hg23
    have hdf := d4Subgroup_fix_diags hd.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmul_act, hg, (g2Subgroup_le_f4 hd).2]
    · rw [hmul_act, hg1, hdf.1]
    · rw [hmul_act, hg2, hdf.2.1]
    · rw [hmul_act, hg3, hdf.2.2]
    · rw [hmul_act, hg12, hd.2.1]
    · rw [hmul_act, hg23, hd.2.2]
  have htri_apply : ∀ (d g : h3zornReducedStructureGroup) (x : ZornVectorMatrix ℝ),
      d ∈ g2Subgroup → g.1 1 = 1 →
      g.1 h3_diag₁ = h3_diag₁ → g.1 h3_diag₂ = h3_diag₂ → g.1 h3_diag₃ = h3_diag₃ →
      g.1 (embedJ12_cb ZornVectorMatrix.one) = embedJ12_cb ZornVectorMatrix.one →
      g.1 (embedJ23_cb ZornVectorMatrix.one) = embedJ23_cb ZornVectorMatrix.one →
      (d * g).1 (embedJ12_cb x) = embedJ12_cb (d.1 (embedJ12_cb (g.1 (embedJ12_cb x)).a)).a := by
    intro d g x hd hg hg1 hg2 hg3 hg12 hg23
    obtain ⟨φ, _, _, _, _, _, hφ⟩ := triality_of_fix_diags_and_ones hg hg1 hg2 hg3 hg12 hg23
    have hgx : g.1 (embedJ12_cb x) = embedJ12_cb (g.1 (embedJ12_cb x)).a := by
      rw [hφ (embedJ12_cb x)]
      apply ext_h3
      · rfl
      · rfl
      · rfl
      · rfl
      · exact φ.map_zero
      · exact φ.map_zero
    rw [hmul_act]
    conv_lhs => rw [hgx]
    rw [(g2Subgroup_preserves_norm_trace hd _).1]; rfl
  -- Step 1: reduce to fixing E11
  obtain ⟨g₀, hg0_1, _, _, hg0_b, hg0_n, hg0_act⟩ :=
    triality_of_fix_diags_and_ones hf h1 h2 h3 h12 h23
  have hw_tr : (g₀ ZornVectorMatrix.E11).trace = 1 := by
    have htr1 : ∀ u : ZornVectorMatrix ℝ, u.trace = zornBilin_cb u ZornVectorMatrix.one := fun u => by
      have hcu : ZornVectorMatrix.conj (ZornVectorMatrix.one : ZornVectorMatrix ℝ) =
          ZornVectorMatrix.one := by ext i <;> simp [ZornVectorMatrix.conj, ZornVectorMatrix.one]
      have hmu : ZornVectorMatrix.mul u ZornVectorMatrix.one = u := by
        ext i <;> simp [ZornVectorMatrix.mul, ZornVectorMatrix.one, ZornVec3.dot, ZornVec3.cross]
      rw [zornBilin_cb, hcu, hmu]
    rw [htr1, ← hg0_1, hg0_b, ← htr1]
    simp [ZornVectorMatrix.trace, ZornVectorMatrix.E11]
  have hw_norm : (g₀ ZornVectorMatrix.E11).norm = 0 := by
    rw [hg0_n]
    simp [ZornVectorMatrix.norm, ZornVectorMatrix.E11, ZornVec3.dot]
  obtain ⟨d_E, hd_E, hE_eq⟩ := g2_reduce_idempotent_to_E11 (g₀ ZornVectorMatrix.E11) hw_tr hw_norm
  let f₁ := d_E * f
  obtain ⟨hf₁, hf1_1, hf1_2, hf1_3, hf1_12, hf1_23⟩ := hstep_fix d_E f hd_E hf h1 h2 h3 h12 h23
  have hf1_E11 : f₁.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 := by
    have h0 : (f.1 (embedJ12_cb ZornVectorMatrix.E11)).a = g₀ ZornVectorMatrix.E11 := by
      rw [hg0_act (embedJ12_cb ZornVectorMatrix.E11)]; rfl
    rw [htri_apply d_E f ZornVectorMatrix.E11 hd_E hf h1 h2 h3 h12 h23, h0, hE_eq]
  -- Step 2: reduce to fixing U 0
  obtain ⟨g₁, _, _, hg1_mul, _, _, hg1_act⟩ :=
    triality_of_fix_diags_and_ones hf₁ hf1_1 hf1_2 hf1_3 hf1_12 hf1_23
  have hg1_E11 : g₁ ZornVectorMatrix.E11 = ZornVectorMatrix.E11 := by
    have h := congrArg H3Zorn.a hf1_E11; rw [hg1_act] at h; exact h
  have hU_mem : ∀ x : ZornVectorMatrix ℝ,
      x.a = 0 ∧ x.w = 0 ∧ x.b = 0 →
      (g₁ x).a = 0 ∧ (g₁ x).w = 0 ∧ (g₁ x).b = 0 := by
    intro x hx
    have hl : ZornVectorMatrix.mul ZornVectorMatrix.E11 x = x := by
      apply ZornVectorMatrix.ext
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot, hx.1]
      · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross]
      · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross, hx.2.1]
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot, hx.2.2]
    have hr : ZornVectorMatrix.mul x ZornVectorMatrix.E11 = 0 := by
      apply ZornVectorMatrix.ext
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot, hx.1]
      · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross]
      · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross, hx.2.1]
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot, hx.2.2]
    have hl' := congrArg g₁ hl
    rw [hg1_mul, hg1_E11] at hl'
    have hr' := congrArg g₁ hr
    rw [hg1_mul, hg1_E11, map_zero] at hr'
    refine ⟨?_, ?_, ?_⟩
    · have ha := congrArg ZornVectorMatrix.a hr'
      simpa [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot] using ha
    · funext k; have hk := congrArg (fun z : ZornVectorMatrix ℝ => z.w k) hl'
      simpa [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross] using hk.symm
    · have hb := congrArg ZornVectorMatrix.b hl'
      simpa [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot] using hb.symm
  have hu0_in : (ZornVectorMatrix.U 0 : ZornVectorMatrix ℝ).a = 0 ∧
      (ZornVectorMatrix.U 0 : ZornVectorMatrix ℝ).w = 0 ∧
      (ZornVectorMatrix.U 0 : ZornVectorMatrix ℝ).b = 0 := ⟨rfl, rfl, rfl⟩
  have hg1U0_ne : g₁ (ZornVectorMatrix.U 0) ≠ 0 := by
    intro hz
    have h0 : ZornVectorMatrix.U 0 = (0 : ZornVectorMatrix ℝ) := g₁.injective (by rw [hz, map_zero])
    have hv := congrArg (fun z : ZornVectorMatrix ℝ => z.v 0) h0
    simp [ZornVectorMatrix.U, ZornVec3.basis] at hv
  obtain ⟨d_U0, hd_U0, hU0_E, hU0_eq⟩ :=
    sl3_reduce_U_to_U0 (g₁ (ZornVectorMatrix.U 0)) (hU_mem _ hu0_in) hg1U0_ne
  let f₂ := d_U0 * f₁
  obtain ⟨hf₂, hf2_1, hf2_2, hf2_3, hf2_12, hf2_23⟩ :=
    hstep_fix d_U0 f₁ hd_U0 hf₁ hf1_1 hf1_2 hf1_3 hf1_12 hf1_23
  have hf2_E11 : f₂.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 := by
    rw [hmul_act, hf1_E11, hU0_E]
  have hf2_U0 : f₂.1 (embedJ12_cb (ZornVectorMatrix.U 0)) = embedJ12_cb (ZornVectorMatrix.U 0) := by
    have h0 : (f₁.1 (embedJ12_cb (ZornVectorMatrix.U 0))).a = g₁ (ZornVectorMatrix.U 0) := by
      rw [hg1_act (embedJ12_cb (ZornVectorMatrix.U 0))]; rfl
    rw [htri_apply d_U0 f₁ (ZornVectorMatrix.U 0) hd_U0 hf₁ hf1_1 hf1_2 hf1_3 hf1_12 hf1_23, h0, hU0_eq]
  -- Step 3: reduce to fixing U 1
  obtain ⟨g₂, _, _, hg2_mul, _, _, hg2_act⟩ :=
    triality_of_fix_diags_and_ones hf₂ hf2_1 hf2_2 hf2_3 hf2_12 hf2_23
  have hg2_E11 : g₂ ZornVectorMatrix.E11 = ZornVectorMatrix.E11 := by
    have h := congrArg H3Zorn.a hf2_E11; rw [hg2_act] at h; exact h
  have hg2_U0 : g₂ (ZornVectorMatrix.U 0) = ZornVectorMatrix.U 0 := by
    have h := congrArg H3Zorn.a hf2_U0; rw [hg2_act] at h; exact h
  have hU_mem₂ : ∀ x : ZornVectorMatrix ℝ,
      x.a = 0 ∧ x.w = 0 ∧ x.b = 0 →
      (g₂ x).a = 0 ∧ (g₂ x).w = 0 ∧ (g₂ x).b = 0 := by
    intro x hx
    have hl : ZornVectorMatrix.mul ZornVectorMatrix.E11 x = x := by
      apply ZornVectorMatrix.ext
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot, hx.1]
      · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross]
      · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross, hx.2.1]
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot, hx.2.2]
    have hr : ZornVectorMatrix.mul x ZornVectorMatrix.E11 = 0 := by
      apply ZornVectorMatrix.ext
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot, hx.1]
      · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross]
      · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross, hx.2.1]
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot, hx.2.2]
    have hl' := congrArg g₂ hl; rw [hg2_mul, hg2_E11] at hl'
    have hr' := congrArg g₂ hr; rw [hg2_mul, hg2_E11, map_zero] at hr'
    refine ⟨?_, ?_, ?_⟩
    · have ha := congrArg ZornVectorMatrix.a hr'
      simpa [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot] using ha
    · funext k; have hk := congrArg (fun z : ZornVectorMatrix ℝ => z.w k) hl'
      simpa [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross] using hk.symm
    · have hb := congrArg ZornVectorMatrix.b hl'
      simpa [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot] using hb.symm
  have hg2U1_in := hU_mem₂ (ZornVectorMatrix.U 1) ⟨rfl, rfl, rfl⟩
  have hg2U1_12 : (g₂ (ZornVectorMatrix.U 1)).v 1 ≠ 0 ∨ (g₂ (ZornVectorMatrix.U 1)).v 2 ≠ 0 := by
    by_contra h
    push Not at h
    let c := (g₂ (ZornVectorMatrix.U 1)).v 0
    have hsm : g₂ (ZornVectorMatrix.U 1) = c • ZornVectorMatrix.U 0 := by
      apply ZornVectorMatrix.ext
      · change (g₂ (ZornVectorMatrix.U 1)).a = c * 0; rw [hg2U1_in.1, mul_zero]
      · funext k; fin_cases k
        · change c = c * 1; ring
        · change (g₂ (ZornVectorMatrix.U 1)).v 1 = c * 0; rw [h.1, mul_zero]
        · change (g₂ (ZornVectorMatrix.U 1)).v 2 = c * 0; rw [h.2, mul_zero]
      · funext k; fin_cases k <;>
          [change (g₂ (ZornVectorMatrix.U 1)).w 0 = c * 0;
           change (g₂ (ZornVectorMatrix.U 1)).w 1 = c * 0;
           change (g₂ (ZornVectorMatrix.U 1)).w 2 = c * 0] <;> rw [hg2U1_in.2.1] <;> simp
      · change (g₂ (ZornVectorMatrix.U 1)).b = c * 0; rw [hg2U1_in.2.2, mul_zero]
    rw [← hg2_U0, ← map_smul] at hsm
    have hinj := g₂.injective hsm
    have hv1 := congrArg (fun z : ZornVectorMatrix ℝ => z.v 1) hinj
    simp [ZornVectorMatrix.U, ZornVec3.basis] at hv1
  obtain ⟨d_U1, hd_U1, hU1_E, hU1_U0, hU1_eq⟩ :=
    sl3_reduce_U_to_U1_fixing_U0 (g₂ (ZornVectorMatrix.U 1)) hg2U1_in hg2U1_12
  let f₃ := d_U1 * f₂
  obtain ⟨hf₃, hf3_1, hf3_2, hf3_3, hf3_12, hf3_23⟩ :=
    hstep_fix d_U1 f₂ hd_U1 hf₂ hf2_1 hf2_2 hf2_3 hf2_12 hf2_23
  have hf3_E11 : f₃.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 := by
    rw [hmul_act, hf2_E11, hU1_E]
  have hf3_U0 : f₃.1 (embedJ12_cb (ZornVectorMatrix.U 0)) = embedJ12_cb (ZornVectorMatrix.U 0) := by
    rw [hmul_act, hf2_U0, hU1_U0]
  have hf3_U1 : f₃.1 (embedJ12_cb (ZornVectorMatrix.U 1)) = embedJ12_cb (ZornVectorMatrix.U 1) := by
    have h0 : (f₂.1 (embedJ12_cb (ZornVectorMatrix.U 1))).a = g₂ (ZornVectorMatrix.U 1) := by
      rw [hg2_act (embedJ12_cb (ZornVectorMatrix.U 1))]; rfl
    rw [htri_apply d_U1 f₂ (ZornVectorMatrix.U 1) hd_U1 hf₂ hf2_1 hf2_2 hf2_3 hf2_12 hf2_23, h0, hU1_eq]
  -- Step 4: reduce to fixing U 2
  obtain ⟨g₃, _, _, hg3_mul, hg3_b, _, hg3_act⟩ :=
    triality_of_fix_diags_and_ones hf₃ hf3_1 hf3_2 hf3_3 hf3_12 hf3_23
  have hg3_E11 : g₃ ZornVectorMatrix.E11 = ZornVectorMatrix.E11 := by
    have h := congrArg H3Zorn.a hf3_E11; rw [hg3_act] at h; exact h
  have hg3_U0 : g₃ (ZornVectorMatrix.U 0) = ZornVectorMatrix.U 0 := by
    have h := congrArg H3Zorn.a hf3_U0; rw [hg3_act] at h; exact h
  have hg3_U1 : g₃ (ZornVectorMatrix.U 1) = ZornVectorMatrix.U 1 := by
    have h := congrArg H3Zorn.a hf3_U1; rw [hg3_act] at h; exact h
  have hg3U2_in : (g₃ (ZornVectorMatrix.U 2)).a = 0 ∧
      (g₃ (ZornVectorMatrix.U 2)).w = 0 ∧ (g₃ (ZornVectorMatrix.U 2)).b = 0 := by
    have hl : ZornVectorMatrix.mul (ZornVectorMatrix.E11 : ZornVectorMatrix ℝ) (ZornVectorMatrix.U 2) =
        ZornVectorMatrix.U 2 := by
      apply ZornVectorMatrix.ext
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVectorMatrix.U, ZornVec3.dot]
      · funext k; fin_cases k <;>
          simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVectorMatrix.U, ZornVec3.cross, ZornVec3.basis]
      · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVectorMatrix.U, ZornVec3.cross]
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVectorMatrix.U, ZornVec3.dot]
    have hr : ZornVectorMatrix.mul (ZornVectorMatrix.U 2 : ZornVectorMatrix ℝ) ZornVectorMatrix.E11 = 0 := by
      apply ZornVectorMatrix.ext
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVectorMatrix.U, ZornVec3.dot]
      · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVectorMatrix.U, ZornVec3.cross]
      · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVectorMatrix.U, ZornVec3.cross]
      · simp [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVectorMatrix.U, ZornVec3.dot]
    have hl' := congrArg g₃ hl; rw [hg3_mul, hg3_E11] at hl'
    have hr' := congrArg g₃ hr; rw [hg3_mul, hg3_E11, map_zero] at hr'
    refine ⟨?_, ?_, ?_⟩
    · have ha := congrArg ZornVectorMatrix.a hr'
      simpa [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot] using ha
    · funext k; have hk := congrArg (fun z : ZornVectorMatrix ℝ => z.w k) hl'
      simpa [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.cross] using hk.symm
    · have hb := congrArg ZornVectorMatrix.b hl'
      simpa [ZornVectorMatrix.mul, ZornVectorMatrix.E11, ZornVec3.dot] using hb.symm
  let w2 : ZornVectorMatrix ℝ := ⟨0, 0, ZornVec3.basis 2, 0⟩
  have hw2_mul : ZornVectorMatrix.mul (ZornVectorMatrix.U 0) (ZornVectorMatrix.U 1) = w2 := by
    apply ZornVectorMatrix.ext
    · simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.dot, w2]
    · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.cross, w2]
    · funext k; fin_cases k <;>
        simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.cross, ZornVec3.basis, w2]
    · simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.dot, w2]
  have hg3_w2 : g₃ w2 = w2 := by
    rw [← hw2_mul, hg3_mul, hg3_U0, hg3_U1, hw2_mul]
  have hg3U2_v2 : (g₃ (ZornVectorMatrix.U 2)).v 2 = 1 := by
    have hb := hg3_b (ZornVectorMatrix.U 2) w2
    rw [hg3_w2] at hb
    have hLHS : zornBilin_cb (g₃ (ZornVectorMatrix.U 2)) w2 = -(g₃ (ZornVectorMatrix.U 2)).v 2 := by
      simp [zornBilin_cb, ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
        ZornVec3.dot, hg3U2_in.1, hg3U2_in.2.2, w2, ZornVec3.basis]
    have hRHS : zornBilin_cb (ZornVectorMatrix.U 2) w2 = -1 := by
      simp [zornBilin_cb, ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
        ZornVec3.dot, ZornVectorMatrix.U, w2, ZornVec3.basis]
    linarith
  obtain ⟨d_U2, hd_U2, hU2_E, hU2_U0, hU2_U1, hU2_eq⟩ :=
    sl3_reduce_U_to_U2_fixing_U0_U1 (g₃ (ZornVectorMatrix.U 2)) hg3U2_in hg3U2_v2
  let f₄ := d_U2 * f₃
  obtain ⟨hf₄, hf4_1, hf4_2, hf4_3, hf4_12, hf4_23⟩ :=
    hstep_fix d_U2 f₃ hd_U2 hf₃ hf3_1 hf3_2 hf3_3 hf3_12 hf3_23
  have hf4_E11 : f₄.1 (embedJ12_cb ZornVectorMatrix.E11) = embedJ12_cb ZornVectorMatrix.E11 := by
    rw [hmul_act, hf3_E11, hU2_E]
  have hf4_U0 : f₄.1 (embedJ12_cb (ZornVectorMatrix.U 0)) = embedJ12_cb (ZornVectorMatrix.U 0) := by
    rw [hmul_act, hf3_U0, hU2_U0]
  have hf4_U1 : f₄.1 (embedJ12_cb (ZornVectorMatrix.U 1)) = embedJ12_cb (ZornVectorMatrix.U 1) := by
    rw [hmul_act, hf3_U1, hU2_U1]
  have hf4_U2 : f₄.1 (embedJ12_cb (ZornVectorMatrix.U 2)) = embedJ12_cb (ZornVectorMatrix.U 2) := by
    have h0 : (f₃.1 (embedJ12_cb (ZornVectorMatrix.U 2))).a = g₃ (ZornVectorMatrix.U 2) := by
      rw [hg3_act (embedJ12_cb (ZornVectorMatrix.U 2))]; rfl
    rw [htri_apply d_U2 f₃ (ZornVectorMatrix.U 2) hd_U2 hf₃ hf3_1 hf3_2 hf3_3 hf3_12 hf3_23, h0, hU2_eq]
  -- Step 5: f₄ = 1
  obtain ⟨g₄, hg4_1, _, hg4_mul, _, _, hg4_act⟩ :=
    triality_of_fix_diags_and_ones hf₄ hf4_1 hf4_2 hf4_3 hf4_12 hf4_23
  have hg4_E11 : g₄ ZornVectorMatrix.E11 = ZornVectorMatrix.E11 := by
    have h := congrArg H3Zorn.a hf4_E11; rw [hg4_act] at h; exact h
  have hg4_E22 : g₄ ZornVectorMatrix.E22 = ZornVectorMatrix.E22 := by
    have hsum : (ZornVectorMatrix.E11 : ZornVectorMatrix ℝ) + ZornVectorMatrix.E22 =
        ZornVectorMatrix.one := by
      apply ZornVectorMatrix.ext
      · simp [ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVectorMatrix.one]
      · funext k; simp [ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVectorMatrix.one]
      · funext k; simp [ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVectorMatrix.one]
      · simp [ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVectorMatrix.one]
    have h := congrArg g₄ hsum
    rw [map_add, hg4_E11, hg4_1, ← hsum] at h
    exact add_left_cancel h
  have hg4_U0 : g₄ (ZornVectorMatrix.U 0) = ZornVectorMatrix.U 0 := by
    have h := congrArg H3Zorn.a hf4_U0; rw [hg4_act] at h; exact h
  have hg4_U1 : g₄ (ZornVectorMatrix.U 1) = ZornVectorMatrix.U 1 := by
    have h := congrArg H3Zorn.a hf4_U1; rw [hg4_act] at h; exact h
  have hg4_U2 : g₄ (ZornVectorMatrix.U 2) = ZornVectorMatrix.U 2 := by
    have h := congrArg H3Zorn.a hf4_U2; rw [hg4_act] at h; exact h
  let w0 : ZornVectorMatrix ℝ := ⟨0, 0, ZornVec3.basis 0, 0⟩
  let w1 : ZornVectorMatrix ℝ := ⟨0, 0, ZornVec3.basis 1, 0⟩
  have hw0_mul : ZornVectorMatrix.mul (ZornVectorMatrix.U 1) (ZornVectorMatrix.U 2) = w0 := by
    apply ZornVectorMatrix.ext
    · simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.dot, w0]
    · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.cross, w0]
    · funext k; fin_cases k <;>
        simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.cross, ZornVec3.basis, w0]
    · simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.dot, w0]
  have hw1_mul : ZornVectorMatrix.mul (ZornVectorMatrix.U 2) (ZornVectorMatrix.U 0) = w1 := by
    apply ZornVectorMatrix.ext
    · simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.dot, w1]
    · funext k; simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.cross, w1]
    · funext k; fin_cases k <;>
        simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.cross, ZornVec3.basis, w1]
    · simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.dot, w1]
  have hg4_w0 : g₄ w0 = w0 := by rw [← hw0_mul, hg4_mul, hg4_U1, hg4_U2, hw0_mul]
  have hg4_w1 : g₄ w1 = w1 := by rw [← hw1_mul, hg4_mul, hg4_U2, hg4_U0, hw1_mul]
  have hg4_w2 : g₄ w2 = w2 := by rw [← hw2_mul, hg4_mul, hg4_U0, hg4_U1, hw2_mul]
  have hg4_id : ∀ x : ZornVectorMatrix ℝ, g₄ x = x := fun x => by
    have hdec : x = x.a • ZornVectorMatrix.E11 + x.b • ZornVectorMatrix.E22 +
        x.v 0 • ZornVectorMatrix.U 0 + x.v 1 • ZornVectorMatrix.U 1 + x.v 2 • ZornVectorMatrix.U 2 +
        x.w 0 • w0 + x.w 1 • w1 + x.w 2 • w2 := by
      apply ZornVectorMatrix.ext
      · simp [ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVectorMatrix.U, w0, w1, w2]
      · funext k; fin_cases k <;>
          simp [ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVectorMatrix.U, w0, w1, w2, ZornVec3.basis]
      · funext k; fin_cases k <;>
          simp [ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVectorMatrix.U, w0, w1, w2, ZornVec3.basis]
      · simp [ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVectorMatrix.U, w0, w1, w2]
    conv_lhs => rw [hdec]
    simp only [map_add, map_smul, hg4_E11, hg4_E22, hg4_U0, hg4_U1, hg4_U2, hg4_w0, hg4_w1, hg4_w2]
    exact hdec.symm
  have hf4_one : f₄ = 1 := by
    apply Subtype.ext; apply LinearEquiv.ext; intro X
    rw [hg4_act X, hg4_id, hg4_id, hg4_id]
    rfl
  let d_all := d_U2 * (d_U1 * (d_U0 * d_E))
  have hd_all : d_all ∈ d4Subgroup :=
    d4Subgroup.mul_mem hd_U2.1 (d4Subgroup.mul_mem hd_U1.1 (d4Subgroup.mul_mem hd_U0.1 hd_E.1))
  have hmul_f : d_all * f = 1 := by
    calc d_all * f = d_U2 * (d_U1 * (d_U0 * (d_E * f))) := by simp only [d_all, mul_assoc]
      _ = 1 := hf4_one
  have hf_eq : f = d_all⁻¹ := eq_inv_of_mul_eq_one_right hmul_f
  rw [hf_eq]
  exact d4Subgroup.inv_mem hd_all

end PartBF4AndFullGeneration

/-- Every `ReducedStructureFixOne` element lies in `e6ChevalleySubgroup`. -/
theorem h3zornReducedStructureFixOne_le_e6ChevalleySubgroup
    {f : h3zornReducedStructureGroup} (hf : f.1 1 = 1) : f ∈ e6ChevalleySubgroup := by
  obtain ⟨g₁, hg₁, hg1_d1⟩ :=
    f4_reduce_idempotent_to_diag1 (f.1 h3_diag₁)
      (jordanAut_preserves_isRankOneIdem (h3zornJordanAutOfReducedStructure f hf)
        h3_diag₁_isRankOneIdem)
  have hfix1 : (g₁ * f).1 1 = 1 ∧ (g₁ * f).1 h3_diag₁ = h3_diag₁ :=
    ⟨by change g₁.1 (f.1 1) = 1; rw [hf, hg₁.2], hg1_d1⟩
  obtain ⟨g₂, hg₂, hg2_d1, hg2_d2⟩ :=
    f4_reduce_diag2_fixing_diag1 hfix1.1 hfix1.2
  let f₂ := g₂ * (g₁ * f)
  have hf₂_1 : f₂.1 1 = 1 := by
    change g₂.1 ((g₁ * f).1 1) = 1; rw [hfix1.1, hg₂.2]
  have hf₂_d1 : f₂.1 h3_diag₁ = h3_diag₁ := by
    change g₂.1 ((g₁ * f).1 h3_diag₁) = _; rw [hfix1.2, hg2_d1]
  have hf₂_d2 : f₂.1 h3_diag₂ = h3_diag₂ := by
    change g₂.1 ((g₁ * f).1 h3_diag₂) = _; exact hg2_d2
  have hf₂_d3 : f₂.1 h3_diag₃ = h3_diag₃ := by
    have hsum : h3_diag₁ + h3_diag₂ + h3_diag₃ = 1 := by
      apply ext_h3
      · change (1 : ℝ) + 0 + 0 = (1 : H3Zorn ℝ).α₁; simp [one_readback]
      · change (0 : ℝ) + 1 + 0 = (1 : H3Zorn ℝ).α₂; simp [one_readback]
      · change (0 : ℝ) + 0 + 1 = (1 : H3Zorn ℝ).α₃; simp [one_readback]
      · simp [add_readback, one_readback, h3_diag₁, h3_diag₂, h3_diag₃]
      · simp [add_readback, one_readback, h3_diag₁, h3_diag₂, h3_diag₃]
      · simp [add_readback, one_readback, h3_diag₁, h3_diag₂, h3_diag₃]
    have h1' : f₂.1 1 = 1 := hf₂_1
    have hmap := congrArg f₂.1 hsum
    rw [map_add, map_add, hf₂_d1, hf₂_d2, h1', ← hsum] at hmap
    exact add_left_cancel hmap
  let A₂ := h3zornJordanAutOfReducedStructure f₂ hf₂_1
  have hnorm12 : ((f₂.1 (embedJ12_cb ZornVectorMatrix.one)).a).norm = 1 := by
    have hblk := peirce_spaces_preserved_of_fix_diags
      A₂ hf₂_d1 hf₂_d2 hf₂_d3
    have hsq := congrArg A₂ (embedJ12_mul_embedJ12_cb
      ZornVectorMatrix.one ZornVectorMatrix.one)
    rw [A₂.map_mul, A₂.1.map_smul, map_add] at hsq
    have hp := hblk.1 ZornVectorMatrix.one
    change f₂.1 (embedJ12_cb ZornVectorMatrix.one) *
        f₂.1 (embedJ12_cb ZornVectorMatrix.one) =
      ((1 / 2 : ℝ) * zornBilin_cb ZornVectorMatrix.one ZornVectorMatrix.one) •
        (f₂.1 h3_diag₁ + f₂.1 h3_diag₂) at hsq
    change f₂.1 (embedJ12_cb ZornVectorMatrix.one) =
      embedJ12_cb
        (f₂.1 (embedJ12_cb ZornVectorMatrix.one)).a at hp
    rw [hp, embedJ12_mul_embedJ12_cb, hf₂_d1, hf₂_d2,
      zornBilin_cb_self,
      zornBilin_cb_self] at hsq
    have hα1 := congrArg H3Zorn.α₁ hsq
    have h1n : (ZornVectorMatrix.one : ZornVectorMatrix ℝ).norm = 1 := by
      simp [ZornVectorMatrix.norm, ZornVectorMatrix.one, ZornVec3.dot]
    simp only [smul_readback, add_readback, h3_diag₁, h3_diag₂, add_zero, h1n] at hα1
    linarith [hα1]
  obtain ⟨d₃, hd₃, hd3_12⟩ :=
    f4_reduce_j12_one_fixing_diags _ hnorm12
  let f₃ := d₃ * f₂
  have hf₃_1 : f₃.1 1 = 1 := by
    change d₃.1 (f₂.1 1) = 1; rw [hf₂_1, (d4Subgroup_le_f4InChevalley hd₃).2]
  have hfix_d3 := d4Subgroup_fix_diags hd₃
  have hf₃_d1 : f₃.1 h3_diag₁ = h3_diag₁ := by change d₃.1 (f₂.1 _) = _; rw [hf₂_d1, hfix_d3.1]
  have hf₃_d2 : f₃.1 h3_diag₂ = h3_diag₂ := by change d₃.1 (f₂.1 _) = _; rw [hf₂_d2, hfix_d3.2.1]
  have hf₃_d3 : f₃.1 h3_diag₃ = h3_diag₃ := by change d₃.1 (f₂.1 _) = _; rw [hf₂_d3, hfix_d3.2.2]
  have hf₃_12 : f₃.1 (embedJ12_cb ZornVectorMatrix.one) =
      embedJ12_cb ZornVectorMatrix.one := by
    have hblk2 := peirce_spaces_preserved_of_fix_diags
      A₂ hf₂_d1 hf₂_d2 hf₂_d3
    have hp2 : f₂.1 (embedJ12_cb ZornVectorMatrix.one) =
        embedJ12_cb
          (f₂.1 (embedJ12_cb ZornVectorMatrix.one)).a :=
      hblk2.1 ZornVectorMatrix.one
    have hblk3 := d4Subgroup_preserves_blocks hd₃
      (embedJ12_cb (f₂.1 (embedJ12_cb ZornVectorMatrix.one)).a)
    change d₃.1 (f₂.1 (embedJ12_cb ZornVectorMatrix.one)) = _
    rw [hp2]
    apply ext_h3
    · rw [hblk3.1]; rfl
    · rw [hblk3.2.1]; rfl
    · rw [hblk3.2.2.1]; rfl
    · exact hd3_12
    · exact hblk3.2.2.2.2.1.mpr rfl
    · exact hblk3.2.2.2.2.2.mpr rfl
  let A₃ := h3zornJordanAutOfReducedStructure f₃ hf₃_1
  have hnorm23 : ((f₃.1 (embedJ23_cb ZornVectorMatrix.one)).b).norm = 1 := by
    have hblk := peirce_spaces_preserved_of_fix_diags
      A₃ hf₃_d1 hf₃_d2 hf₃_d3
    have hsq := congrArg A₃ (embedJ23_mul_embedJ23_cb
      ZornVectorMatrix.one ZornVectorMatrix.one)
    rw [A₃.map_mul, A₃.1.map_smul, map_add] at hsq
    have hp := hblk.2.1 ZornVectorMatrix.one
    change f₃.1 (embedJ23_cb ZornVectorMatrix.one) *
        f₃.1 (embedJ23_cb ZornVectorMatrix.one) =
      ((1 / 2 : ℝ) * zornBilin_cb ZornVectorMatrix.one ZornVectorMatrix.one) •
        (f₃.1 h3_diag₂ + f₃.1 h3_diag₃) at hsq
    change f₃.1 (embedJ23_cb ZornVectorMatrix.one) =
      embedJ23_cb
        (f₃.1 (embedJ23_cb ZornVectorMatrix.one)).b at hp
    rw [hp, embedJ23_mul_embedJ23_cb, hf₃_d2, hf₃_d3,
      zornBilin_cb_self,
      zornBilin_cb_self] at hsq
    have hα2 := congrArg H3Zorn.α₂ hsq
    have h1n : (ZornVectorMatrix.one : ZornVectorMatrix ℝ).norm = 1 := by
      simp [ZornVectorMatrix.norm, ZornVectorMatrix.one, ZornVec3.dot]
    simp only [smul_readback, add_readback, h3_diag₂, h3_diag₃, add_zero, h1n] at hα2
    linarith [hα2]
  obtain ⟨d₄, hd₄, hd4_12, hd4_23⟩ :=
    f4_reduce_j23_one_fixing_diags _ hnorm23
  let f₄ := d₄ * f₃
  have hf₄_1 : f₄.1 1 = 1 := by
    change d₄.1 (f₃.1 1) = 1; rw [hf₃_1, (d4Subgroup_le_f4InChevalley hd₄).2]
  have hfix_d4 := d4Subgroup_fix_diags hd₄
  have hf₄_d1 : f₄.1 h3_diag₁ = h3_diag₁ := by change d₄.1 (f₃.1 _) = _; rw [hf₃_d1, hfix_d4.1]
  have hf₄_d2 : f₄.1 h3_diag₂ = h3_diag₂ := by change d₄.1 (f₃.1 _) = _; rw [hf₃_d2, hfix_d4.2.1]
  have hf₄_d3 : f₄.1 h3_diag₃ = h3_diag₃ := by change d₄.1 (f₃.1 _) = _; rw [hf₃_d3, hfix_d4.2.2]
  have hf₄_12 : f₄.1 (embedJ12_cb ZornVectorMatrix.one) =
      embedJ12_cb ZornVectorMatrix.one := by
    change d₄.1 (f₃.1 _) = _; rw [hf₃_12, hd4_12]
  have hf₄_23 : f₄.1 (embedJ23_cb ZornVectorMatrix.one) =
      embedJ23_cb ZornVectorMatrix.one := by
    have hblk3 := peirce_spaces_preserved_of_fix_diags
      A₃ hf₃_d1 hf₃_d2 hf₃_d3
    have hp3 : f₃.1 (embedJ23_cb ZornVectorMatrix.one) =
        embedJ23_cb
          (f₃.1 (embedJ23_cb ZornVectorMatrix.one)).b :=
      hblk3.2.1 ZornVectorMatrix.one
    have hblk4 := d4Subgroup_preserves_blocks hd₄
      (embedJ23_cb (f₃.1 (embedJ23_cb ZornVectorMatrix.one)).b)
    change d₄.1 (f₃.1 (embedJ23_cb ZornVectorMatrix.one)) = _
    rw [hp3]
    apply ext_h3
    · rw [hblk4.1]; rfl
    · rw [hblk4.2.1]; rfl
    · rw [hblk4.2.2.1]; rfl
    · exact hblk4.2.2.2.1.mpr rfl
    · exact hd4_23
    · exact hblk4.2.2.2.2.2.mpr rfl
  have hf₄_d4 := g2_kill_fix_diags_and_ones hf₄_1
    hf₄_d1 hf₄_d2 hf₄_d3 hf₄_12 hf₄_23
  have hf₄_che : f₄ ∈ e6ChevalleySubgroup :=
    (d4Subgroup_le_f4InChevalley hf₄_d4).1
  have hf₃_che : f₃ ∈ e6ChevalleySubgroup := by
    have h : f₃ = d₄⁻¹ * f₄ := by simp [f₄]
    rw [h]
    exact e6ChevalleySubgroup.mul_mem
      (e6ChevalleySubgroup.inv_mem (d4Subgroup_le_f4InChevalley hd₄).1)
      hf₄_che
  have hf₂_che : f₂ ∈ e6ChevalleySubgroup := by
    have h : f₂ = d₃⁻¹ * f₃ := by simp [f₃]
    rw [h]
    exact e6ChevalleySubgroup.mul_mem
      (e6ChevalleySubgroup.inv_mem (d4Subgroup_le_f4InChevalley hd₃).1)
      hf₃_che
  have hf₁_che : (g₁ * f) ∈ e6ChevalleySubgroup := by
    have h : g₁ * f = g₂⁻¹ * f₂ := by simp [f₂]
    rw [h]
    exact e6ChevalleySubgroup.mul_mem (e6ChevalleySubgroup.inv_mem hg₂.1) hf₂_che
  have h : f = g₁⁻¹ * (g₁ * f) := by simp
  rw [h]
  exact e6ChevalleySubgroup.mul_mem (e6ChevalleySubgroup.inv_mem hg₁.1) hf₁_che

/-- Every Jordan automorphism `A : H3ZornJordanAut` lies in `e6ChevalleySubgroup`. -/
theorem h3zornJordanAut_mem_e6ChevalleySubgroup (A : H3ZornJordanAut) :
    (⟨A.toLinearEquiv, A.mem_reducedStructureGroup⟩ : h3zornReducedStructureGroup) ∈
      e6ChevalleySubgroup :=
  h3zornReducedStructureFixOne_le_e6ChevalleySubgroup A.map_one

/-- Full generation of `Str₀(H₃(𝕆_s)) = h3zornReducedStructureGroup` by `E₆(6)` root
exponentials (`e6ChevalleySubgroup = ⊤`). -/
theorem e6ChevalleySubgroup_eq_top : e6ChevalleySubgroup = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨c, hc_mem, f, hf, rfl⟩ := e6ChevalleySubgroup_reduce_to_fixOne g
  exact e6ChevalleySubgroup.mul_mem hc_mem (h3zornReducedStructureFixOne_le_e6ChevalleySubgroup hf)

/-- Quadratic Jordan operator `U(X)` for `normCubic X = ±1` lies in `e6ChevalleySubgroup`. -/
theorem h3zornULinearEquiv_mem_e6ChevalleySubgroup (X : H3Zorn ℝ)
    (hN : normCubic X ≠ 0) (hpm : normCubic X = 1 ∨ normCubic X = -1) :
    (⟨h3zornULinearEquiv X hN, h3zornULinearEquiv_mem_reducedStructureGroup X hN hpm⟩ :
      h3zornReducedStructureGroup) ∈ e6ChevalleySubgroup := by
  rw [e6ChevalleySubgroup_eq_top]
  trivial

section PartCNativeBruhat

/-- Root subgroup `U_r = {x_r(c) | c ∈ ℝ}` inside `Str₀(H₃(𝕆_s))`. -/
def e6RootSubgroup (r : Fin 72) : Subgroup h3zornReducedStructureGroup :=
  Subgroup.closure (Set.range (e6RootExp r))

/-- Positive root predicate in the simple-root coordinate sum. -/
def e6IsPosRoot (r : Fin 72) : Bool :=
  decide (0 < ∑ i : Fin 6, e6RootCoord r i)

/-- Positive unipotent subgroup `U⁺` generated by positive root exponentials. -/
def e6PosUnipotent : Subgroup h3zornReducedStructureGroup :=
  Subgroup.closure { g | ∃ r : Fin 72, e6IsPosRoot r = true ∧ ∃ c : ℝ, g = e6RootExp r c }

/-- Negative unipotent subgroup `U⁻` generated by negative root exponentials. -/
def e6NegUnipotent : Subgroup h3zornReducedStructureGroup :=
  Subgroup.closure { g | ∃ r : Fin 72, e6IsPosRoot r = false ∧ ∃ c : ℝ, g = e6RootExp r c }

/-- Split maximal torus `T` generated by the 6 simple torus subgroups `h_i(t)`. -/
def e6Torus : Subgroup h3zornReducedStructureGroup :=
  Subgroup.closure { g | ∃ (i : Fin 6) (t : ℝˣ), g = e6TorusElt i t }

/-- Standard split Borel subgroup `B = ⟨T ∪ U⁺⟩`. -/
def e6Borel : Subgroup h3zornReducedStructureGroup :=
  Subgroup.closure ((e6Torus : Set h3zornReducedStructureGroup) ∪
    (e6PosUnipotent : Set h3zornReducedStructureGroup))

/-- Representative Weyl subgroup `W = ⟨w_i(1) | i : Fin 6⟩`. -/
def e6WeylSubgroup : Subgroup h3zornReducedStructureGroup :=
  Subgroup.closure (Set.range fun i : Fin 6 => e6WeylElt i 1)

/-- Simple-generator Chevalley subgroup `⟨x_i(c), y_i(c) | i : Fin 6, c ∈ ℝ⟩`. -/
def e6SimpleClosure : Subgroup h3zornReducedStructureGroup :=
  Subgroup.closure ({ g | ∃ (i : Fin 6) (c : ℝ), g = e6SimpleX i c } ∪
    { g | ∃ (i : Fin 6) (c : ℝ), g = e6SimpleY i c })

/-- Positive unipotent radical missing simple root `α_i`. -/
def e6PosUnipotentExcept (i : Fin 6) : Subgroup h3zornReducedStructureGroup :=
  Subgroup.closure
    { g | ∃ r : Fin 72, e6IsPosRoot r = true ∧ r ≠ eSimpleIdx i ∧ ∃ c : ℝ, g = e6RootExp r c }

private def allPow2Bool (p : ℕ → Bool) (d lo : ℕ) : Bool :=
  @Nat.rec (fun _ => ℕ → Bool) (fun l => p l) (fun n ih l => ih l && ih (l + 2 ^ n)) d lo

private theorem allPow2Bool_sound (p : ℕ → Bool) (d lo : ℕ)
    (h : allPow2Bool p d lo = true) : ∀ k, lo ≤ k → k < lo + 2 ^ d → p k = true := by
  induction d generalizing lo with
  | zero =>
    intro k h1 h2
    have hk : k = lo := by simp at h2; omega
    subst hk; exact h
  | succ d ih =>
    intro k h1 h2
    change (allPow2Bool p d lo && allPow2Bool p d (lo + 2 ^ d)) = true at h
    rw [Bool.and_eq_true] at h
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
    by_cases hk : k < lo + 2 ^ d
    · exact ih lo h.1 k h1 hk
    · exact ih (lo + 2 ^ d) h.2 k (by omega) (by omega)

private def allFin72Bool (p : Fin 72 → Bool) : Bool :=
  let q : ℕ → Bool := fun n => if h : n < 72 then p ⟨n, h⟩ else true
  allPow2Bool q 6 0 && allPow2Bool q 3 64

private theorem allFin72Bool_sound (p : Fin 72 → Bool) (h : allFin72Bool p = true) :
    ∀ r : Fin 72, p r = true := by
  intro r
  simp only [allFin72Bool, Bool.and_eq_true] at h
  have hr : (if hlt : r.val < 72 then p ⟨r.val, hlt⟩ else true) = true := by
    by_cases hlt : r.val < 64
    · exact allPow2Bool_sound _ 6 0 h.1 r.val (Nat.zero_le _) hlt
    · exact allPow2Bool_sound _ 3 64 h.2 r.val (by omega) (by have := r.isLt; omega)
  simpa [r.isLt] using hr

private theorem allFin72_by9 (p : Fin 72 → Bool)
    (h : ∀ k : Fin 9, allPow2Bool
      (fun n => if h : n < 72 then p ⟨n, h⟩ else true) 3 (8 * k.val) = true) :
    ∀ r : Fin 72, p r = true := by
  intro r
  have hr := allPow2Bool_sound _ 3 (8 * (⟨r.val / 8, by omega⟩ : Fin 9).val)
    (h ⟨r.val / 8, by omega⟩) r.val (by simp only; omega) (by simp only; omega)
  simpa [r.isLt] using hr

private theorem exists_mem_of_sparseVal_ne_zero (s : SparseMat27) (a b : Fin 27)
    (h : sparseVal s a b ≠ 0) : ∃ p ∈ s, p.1 = a ∧ p.2.1 = b := by
  by_contra hne
  push Not at hne
  exact h (sparseVal_eq_zero_of_not_mem_cb s a b (fun p hp ⟨h1, h2⟩ => hne p hp h1 h2))

private theorem e6RootExp_mul_cb (r : Fin 72) (a b : ℝ) :
    e6RootExp r a * e6RootExp r b = e6RootExp r (a + b) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  change ((1 : Module.End ℝ (H3Zorn ℝ)) + a • (e6RootVec r).1) *
      ((1 : Module.End ℝ (H3Zorn ℝ)) + b • (e6RootVec r).1) =
    (1 : Module.End ℝ (H3Zorn ℝ)) + (a + b) • (e6RootVec r).1
  have hsq : (e6RootVec r).1 * (e6RootVec r).1 = 0 := by
    rw [← sq]; exact e6RootVec_sq_zero r
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hsq,
    smul_zero, add_zero, add_smul]
  module

private theorem e6RootExp_zero_cb (r : Fin 72) : e6RootExp r 0 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  change (1 : Module.End ℝ (H3Zorn ℝ)) + (0 : ℝ) • (e6RootVec r).1 = 1
  simp

private theorem e6RootExp_inv_cb (r : Fin 72) (c : ℝ) :
    (e6RootExp r c)⁻¹ = e6RootExp r (-c) := by
  apply inv_eq_of_mul_eq_one_left
  rw [e6RootExp_mul_cb, neg_add_cancel, e6RootExp_zero_cb]

private theorem h3zornToMatrix_e6RootExp (r : Fin 72) (c : ℝ) :
    h3zornToMatrix (e6RootExp r c).1.toLinearMap =
      (1 : Matrix (Fin 27) (Fin 27) ℝ) + c • (sparseToMat (e6RootSparse r)).map Int.cast := by
  change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + c • (e6RootVec r).1) = _
  rw [map_add, _root_.map_one, map_smul, h3zornToMatrix_e6RootVec]

private theorem h3zornToMatrix_e6TorusElt (j : Fin 6) (t : ℝˣ) (a b : Fin 27) :
    h3zornToMatrix (e6TorusElt j t).1.toLinearMap a b =
      if a = b then ((t ^ h3zornWeight a j : ℝˣ) : ℝ) else 0 := by
  rw [h3zornToMatrix_apply]
  change h3ZornBasis.repr ((e6TorusElt j t).1 (h3ZornBasis b)) a = _
  rw [e6TorusElt_apply_basis, map_smul, Finsupp.smul_apply, h3ZornBasis.repr_self,
    Finsupp.single_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab; simp
  · have hba : b ≠ a := fun h => hab h.symm
    simp [hab, hba]

private theorem h3zornToMatrix_mul_group (g₁ g₂ : h3zornReducedStructureGroup) :
    h3zornToMatrix (g₁ * g₂).1.toLinearMap =
      h3zornToMatrix g₁.1.toLinearMap * h3zornToMatrix g₂.1.toLinearMap :=
  _root_.map_mul h3zornToMatrix g₁.1.toLinearMap g₂.1.toLinearMap

private theorem h3zornToMatrix_group_injective :
    Function.Injective (fun g : h3zornReducedStructureGroup =>
      h3zornToMatrix g.1.toLinearMap) := by
  intro g₁ g₂ h
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact h3zornToMatrix.injective h

private theorem e6TorusElt_inv_cb (j : Fin 6) (t : ℝˣ) :
    (e6TorusElt j t)⁻¹ = e6TorusElt j t⁻¹ := by
  apply inv_eq_of_mul_eq_one_left
  apply h3zornToMatrix_group_injective
  dsimp only
  rw [h3zornToMatrix_mul_group]
  change h3zornToMatrix (e6TorusElt j t⁻¹).1.toLinearMap *
      h3zornToMatrix (e6TorusElt j t).1.toLinearMap =
    h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ))
  rw [_root_.map_one]
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [h3zornToMatrix_e6TorusElt, h3zornToMatrix_e6TorusElt]
    by_cases hab : a = b
    · subst hab
      simp only [↓reduceIte, Matrix.one_apply_eq, Units.val_zpow_eq_zpow_val,
        Units.val_inv_eq_inv_val, inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ t.ne_zero)]
    · rw [Matrix.one_apply_ne hab]; simp [hab]
  · intro k _ hka; rw [h3zornToMatrix_e6TorusElt]; simp [hka.symm]
  · intro ha; exact absurd (Finset.mem_univ a) ha

/-- Injectivity of the native 78D adjoint conjugation representation `Str₀(H₃(𝕆_s)) → Aut(𝔢₆(6))`. -/
theorem h3zornCubicStabilizerLieEquiv_injective_of_normOne :
    Function.Injective (fun g : h3zornReducedStructureGroup =>
      h3zornCubicStabilizerLieEquivOfNormSimilitude g.1 1 (fun x => by simpa using g.2 x)) := by
  have hker : ∀ g : h3zornReducedStructureGroup,
      (∀ (Y : h3zornCubicStabilizer) (v : H3Zorn ℝ), g.1 (Y.1 v) = Y.1 (g.1 v)) →
      g = 1 := by
    intro g hcomm
    let c : Fin 27 → ℝ := fun k => h3ZornBasis.repr (g.1 (h3ZornBasis k)) k
    have hdiag : ∀ k m : Fin 27, k ≠ m → h3ZornBasis.repr (g.1 (h3ZornBasis k)) m = 0 := by
      have hdist : (List.finRange 27).all (fun k => (List.finRange 27).all (fun m =>
          k == m || (List.finRange 6).any (fun i => h3zornWeight k i != h3zornWeight m i))) =
            true := by
        decide
      simp only [List.all_eq_true, List.mem_finRange, Bool.or_eq_true, List.any_eq_true,
        beq_iff_eq, bne_iff_ne, true_implies] at hdist
      intro k m hkm
      have hi_ex := (hdist k m).resolve_left hkm
      obtain ⟨i, _, hi⟩ := hi_ex
      have hc := hcomm (e6SimpleH i) (h3ZornBasis k)
      have hL : h3ZornBasis.repr (g.1 ((e6SimpleH i).1 (h3ZornBasis k))) m =
          (h3zornWeight k i : ℝ) * h3ZornBasis.repr (g.1 (h3ZornBasis k)) m := by
        rw [e6SimpleH_apply_basis, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
      have hR : h3ZornBasis.repr ((e6SimpleH i).1 (g.1 (h3ZornBasis k))) m =
          (h3zornWeight m i : ℝ) * h3ZornBasis.repr (g.1 (h3ZornBasis k)) m := by
        have hrepr : g.1 (h3ZornBasis k) =
            ∑ r : Fin 27, h3ZornBasis.repr (g.1 (h3ZornBasis k)) r • h3ZornBasis r :=
          (h3ZornBasis.sum_repr _).symm
        conv_lhs => rw [hrepr]
        rw [map_sum, map_sum, Finset.sum_apply']
        simp only [map_smul, e6SimpleH_apply_basis, Finsupp.smul_apply, h3ZornBasis.repr_self,
          Finsupp.single_apply, smul_eq_mul]
        rw [Finset.sum_eq_single m]
        · simp [mul_comm]
        · intro r _ hrm; simp [hrm]
        · intro hm'; exact absurd (Finset.mem_univ m) hm'
      have heq := congrArg (fun x => h3ZornBasis.repr x m) hc
      rw [hL, hR] at heq
      have hsub : ((h3zornWeight k i : ℝ) - (h3zornWeight m i : ℝ)) *
          h3ZornBasis.repr (g.1 (h3ZornBasis k)) m = 0 := by linarith
      have hne : (h3zornWeight k i : ℝ) - (h3zornWeight m i : ℝ) ≠ 0 := by
        exact sub_ne_zero.mpr (Int.cast_injective.ne hi)
      exact (mul_eq_zero.mp hsub).resolve_left hne
    have hbasis : ∀ k : Fin 27, g.1 (h3ZornBasis k) = c k • h3ZornBasis k := by
      intro k
      rw [← h3ZornBasis.sum_repr (g.1 (h3ZornBasis k))]
      rw [Finset.sum_eq_single k]
      · intro m _ hmk; rw [hdiag k m hmk.symm, zero_smul]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    have hedge : ∀ (r : Fin 72) (a b : Fin 27),
        sparseVal (e6RootSparse r) a b ≠ 0 → c a = c b := by
      intro r a b hsp
      have hc := hcomm (e6RootVec r) (h3ZornBasis b)
      have heq := congrArg (fun x => h3ZornBasis.repr x a) hc
      have hR : h3ZornBasis.repr ((e6RootVec r).1 (g.1 (h3ZornBasis b))) a =
          c b * (sparseVal (e6RootSparse r) a b : ℝ) := by
        rw [hbasis b, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
        have hma : h3ZornBasis.repr ((e6RootVec r).1 (h3ZornBasis b)) a =
            h3zornToMatrix (e6RootVec r).1 a b := by
          rw [h3zornToMatrix_apply]; rfl
        rw [hma, h3zornToMatrix_e6RootVec, Matrix.map_apply]
        rfl
      have hL : h3ZornBasis.repr (g.1 ((e6RootVec r).1 (h3ZornBasis b))) a =
          c a * (sparseVal (e6RootSparse r) a b : ℝ) := by
        have hrepr : (e6RootVec r).1 (h3ZornBasis b) =
            ∑ m : Fin 27, h3ZornBasis.repr ((e6RootVec r).1 (h3ZornBasis b)) m • h3ZornBasis m :=
          (h3ZornBasis.sum_repr _).symm
        conv_lhs => rw [hrepr]
        rw [map_sum, map_sum, Finset.sum_apply']
        simp only [map_smul, hbasis, Finsupp.smul_apply, h3ZornBasis.repr_self,
          Finsupp.single_apply, smul_eq_mul]
        rw [Finset.sum_eq_single a]
        · simp only [↓reduceIte, mul_one]
          have hma : h3ZornBasis.repr ((e6RootVec r).1 (h3ZornBasis b)) a =
              h3zornToMatrix (e6RootVec r).1 a b := by
            rw [h3zornToMatrix_apply]; rfl
          rw [hma, h3zornToMatrix_e6RootVec, Matrix.map_apply]
          change _ = c a * (sparseVal (e6RootSparse r) a b : ℝ)
          rw [mul_comm]
          rfl
        · intro m _ hma; simp [hma]
        · intro ha'; exact absurd (Finset.mem_univ a) ha'
      rw [hL, hR] at heq
      exact mul_right_cancel₀ (Int.cast_ne_zero.mpr hsp) heq
    have htree : ([(10, 0, 39), (3, 0, 25), (7, 0, 33), (4, 0, 27), (8, 0, 35),
        (5, 0, 29), (9, 0, 37), (6, 0, 31), (19, 0, 56), (26, 0, 70), (20, 0, 58),
        (23, 0, 64), (21, 0, 60), (24, 0, 66), (22, 0, 62), (25, 0, 68),
        (1, 10, 25), (11, 10, 70), (12, 10, 58), (13, 10, 60), (14, 10, 62),
        (18, 3, 56), (15, 3, 64), (16, 3, 66), (17, 3, 68), (2, 19, 70)] :
        List (Fin 27 × Fin 27 × Fin 72)).all
        (fun e => sparseVal (e6RootSparse e.2.2) e.1 e.2.1 != 0) = true := by
      decide
    simp only [List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false,
      bne_iff_ne] at htree
    have he10 : c 10 = c 0 := hedge 39 10 0 (htree (10, 0, 39) (by simp))
    have he3 : c 3 = c 0 := hedge 25 3 0 (htree (3, 0, 25) (by simp))
    have he7 : c 7 = c 0 := hedge 33 7 0 (htree (7, 0, 33) (by simp))
    have he4 : c 4 = c 0 := hedge 27 4 0 (htree (4, 0, 27) (by simp))
    have he8 : c 8 = c 0 := hedge 35 8 0 (htree (8, 0, 35) (by simp))
    have he5 : c 5 = c 0 := hedge 29 5 0 (htree (5, 0, 29) (by simp))
    have he9 : c 9 = c 0 := hedge 37 9 0 (htree (9, 0, 37) (by simp))
    have he6 : c 6 = c 0 := hedge 31 6 0 (htree (6, 0, 31) (by simp))
    have he19 : c 19 = c 0 := hedge 56 19 0 (htree (19, 0, 56) (by simp))
    have he26 : c 26 = c 0 := hedge 70 26 0 (htree (26, 0, 70) (by simp))
    have he20 : c 20 = c 0 := hedge 58 20 0 (htree (20, 0, 58) (by simp))
    have he23 : c 23 = c 0 := hedge 64 23 0 (htree (23, 0, 64) (by simp))
    have he21 : c 21 = c 0 := hedge 60 21 0 (htree (21, 0, 60) (by simp))
    have he24 : c 24 = c 0 := hedge 66 24 0 (htree (24, 0, 66) (by simp))
    have he22 : c 22 = c 0 := hedge 62 22 0 (htree (22, 0, 62) (by simp))
    have he25 : c 25 = c 0 := hedge 68 25 0 (htree (25, 0, 68) (by simp))
    have he1 : c 1 = c 0 := (hedge 25 1 10 (htree (1, 10, 25) (by simp))).trans he10
    have he11 : c 11 = c 0 := (hedge 70 11 10 (htree (11, 10, 70) (by simp))).trans he10
    have he12 : c 12 = c 0 := (hedge 58 12 10 (htree (12, 10, 58) (by simp))).trans he10
    have he13 : c 13 = c 0 := (hedge 60 13 10 (htree (13, 10, 60) (by simp))).trans he10
    have he14 : c 14 = c 0 := (hedge 62 14 10 (htree (14, 10, 62) (by simp))).trans he10
    have he18 : c 18 = c 0 := (hedge 56 18 3 (htree (18, 3, 56) (by simp))).trans he3
    have he15 : c 15 = c 0 := (hedge 64 15 3 (htree (15, 3, 64) (by simp))).trans he3
    have he16 : c 16 = c 0 := (hedge 66 16 3 (htree (16, 3, 66) (by simp))).trans he3
    have he17 : c 17 = c 0 := (hedge 68 17 3 (htree (17, 3, 68) (by simp))).trans he3
    have he2 : c 2 = c 0 := (hedge 70 2 19 (htree (2, 19, 70) (by simp))).trans he19
    have hall : ∀ k : Fin 27, c k = c 0 := fun k => by
      fin_cases k
      · rfl
      · exact he1
      · exact he2
      · exact he3
      · exact he4
      · exact he5
      · exact he6
      · exact he7
      · exact he8
      · exact he9
      · exact he10
      · exact he11
      · exact he12
      · exact he13
      · exact he14
      · exact he15
      · exact he16
      · exact he17
      · exact he18
      · exact he19
      · exact he20
      · exact he21
      · exact he22
      · exact he23
      · exact he24
      · exact he25
      · exact he26
    have hg_smul : ∀ x : H3Zorn ℝ, g.1 x = (c 0) • x := by
      intro x
      rw [← h3ZornBasis.sum_repr x, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hbasis k, hall k, smul_comm]
    have h1n : normCubic (g.1 1) = 1 := by simpa [normCubic_one] using g.2 1
    rw [hg_smul 1, normCubic_smul, normCubic_one, mul_one] at h1n
    have hlam : c 0 = 1 := by
      have hfac : (c 0 - 1) * ((c 0) ^ 2 + c 0 + 1) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h0 | hpos
      · linarith
      · exfalso
        nlinarith [sq_nonneg (c 0 + 1 / 2)]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [hg_smul x, hlam, one_smul]
    rfl
  intro g₁ g₂ heq
  have hinv_eq : g₂⁻¹ * g₁ = 1 := by
    apply hker
    intro Y v
    have hcon := congrArg (fun (e : h3zornCubicStabilizer ≃ₗ⁅ℝ⁆ h3zornCubicStabilizer) =>
      (e Y : Module.End ℝ (H3Zorn ℝ))) heq
    simp only [h3zornCubicStabilizerLieEquivOfNormSimilitude_apply,
      LinearEquiv.lieConj_apply] at hcon
    have hv := congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f (g₁.1 v)) hcon
    change g₁.1 (Y.1 (g₁.1.symm (g₁.1 v))) = g₂.1 (Y.1 (g₂.1.symm (g₁.1 v))) at hv
    rw [g₁.1.symm_apply_apply] at hv
    have hv2 := congrArg g₂.1.symm hv
    rw [g₂.1.symm_apply_apply] at hv2
    exact hv2
  exact (inv_mul_eq_one.mp hinv_eq).symm

private def basisWeightHeight (k : Fin 27) : ℕ :=
  ![8, 8, 8, 16, 5, 6, 7, 11, 10, 9, 0, 1, 4, 5, 6, 12, 11, 10, 15, 7, 12, 13, 14, 4, 3, 2, 9] k

private theorem posRoot_strict_height (r : Fin 72) (a b : Fin 27)
    (hpos : e6IsPosRoot r = true) (hsp : sparseVal (e6RootSparse r) a b ≠ 0) :
    basisWeightHeight b < basisWeightHeight a := by
  have hchk : ∀ r : Fin 72, (if e6IsPosRoot r then
      (e6RootSparse r).all (fun p => decide (basisWeightHeight p.2.1 < basisWeightHeight p.1))
      else true) = true :=
    allFin72Bool_sound _ (by decide)
  have hr := hchk r
  simp only [hpos, ↓reduceIte, List.all_eq_true, decide_eq_true_eq] at hr
  obtain ⟨p, hp, rfl, rfl⟩ := exists_mem_of_sparseVal_ne_zero (e6RootSparse r) a b hsp
  exact hr p hp

private theorem negRoot_strict_height (r : Fin 72) (a b : Fin 27)
    (hneg : e6IsPosRoot r = false) (hsp : sparseVal (e6RootSparse r) a b ≠ 0) :
    basisWeightHeight a < basisWeightHeight b := by
  have hchk : ∀ r : Fin 72, (if !e6IsPosRoot r then
      (e6RootSparse r).all (fun p => decide (basisWeightHeight p.1 < basisWeightHeight p.2.1))
      else true) = true :=
    allFin72Bool_sound _ (by decide)
  have hr := hchk r
  simp only [hneg, Bool.not_false, ↓reduceIte, List.all_eq_true, decide_eq_true_eq] at hr
  obtain ⟨p, hp, rfl, rfl⟩ := exists_mem_of_sparseVal_ne_zero (e6RootSparse r) a b hsp
  exact hr p hp

private theorem subgroup_closure_symm_induction {G : Type*} [Group G] (S : Set G)
    (hsymm : ∀ x ∈ S, x⁻¹ ∈ S) (P : G → Prop)
    (hone : P 1) (hmem : ∀ x ∈ S, P x) (hmul : ∀ x y, P x → P y → P (x * y)) :
    ∀ g ∈ Subgroup.closure S, P g := by
  intro g hg
  let M : Submonoid G := Submonoid.closure S
  let H : Subgroup G :=
    { toSubmonoid := M
      inv_mem' := by
        intro x hx
        induction hx using Submonoid.closure_induction with
        | mem y hy => exact Submonoid.subset_closure (hsymm y hy)
        | one => simp [M]
        | mul a b _ _ iha ihb =>
          rw [mul_inv_rev]
          exact M.mul_mem ihb iha }
  have hle : Subgroup.closure S ≤ H := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Submonoid.subset_closure hx
  have hm : g ∈ M := hle hg
  exact @Submonoid.closure_induction _ _ S (fun x _ => P x)
    (fun x hx => hmem x hx) hone (fun x y _ _ hx hy => hmul x y hx hy) g hm

private theorem e6PosUnipotent_triangular (g : h3zornReducedStructureGroup)
    (hg : g ∈ e6PosUnipotent) :
    (∀ a b : Fin 27, basisWeightHeight a < basisWeightHeight b →
      h3zornToMatrix g.1.toLinearMap a b = 0) ∧
    (∀ a b : Fin 27, basisWeightHeight a = basisWeightHeight b →
      h3zornToMatrix g.1.toLinearMap a b = if a = b then 1 else 0) := by
  let S : Set h3zornReducedStructureGroup :=
    { x | ∃ r : Fin 72, e6IsPosRoot r = true ∧ ∃ c : ℝ, x = e6RootExp r c }
  refine subgroup_closure_symm_induction S
    (by rintro _ ⟨r, hpos, c, rfl⟩; exact ⟨r, hpos, -c, e6RootExp_inv_cb r c⟩)
    (fun g => (∀ a b : Fin 27, basisWeightHeight a < basisWeightHeight b →
      h3zornToMatrix g.1.toLinearMap a b = 0) ∧
      (∀ a b : Fin 27, basisWeightHeight a = basisWeightHeight b →
      h3zornToMatrix g.1.toLinearMap a b = if a = b then 1 else 0))
    ?_ ?_ ?_ g hg
  · refine ⟨fun a b hab => ?_, fun a b _ => ?_⟩
    · have hne : a ≠ b := fun h => by subst h; omega
      change h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) a b = 0
      rw [_root_.map_one, Matrix.one_apply_ne hne]
    · change h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) a b = if a = b then 1 else 0
      rw [_root_.map_one, Matrix.one_apply]
  · rintro _ ⟨r, hpos, c, rfl⟩
    refine ⟨fun a b hab => ?_, fun a b heq => ?_⟩
    · rw [h3zornToMatrix_e6RootExp]
      have hne : a ≠ b := fun h => by subst h; omega
      have hsp : sparseVal (e6RootSparse r) a b = 0 := by
        by_contra hnz
        have hlt := posRoot_strict_height r a b hpos hnz
        omega
      simp only [Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul, zero_add]
      change c * (sparseVal (e6RootSparse r) a b : ℝ) = 0
      rw [hsp, Int.cast_zero, mul_zero]
    · rw [h3zornToMatrix_e6RootExp]
      have hsp : sparseVal (e6RootSparse r) a b = 0 := by
        by_contra hnz
        have hlt := posRoot_strict_height r a b hpos hnz
        omega
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul]
      change (if a = b then (1 : ℝ) else 0) + c * (sparseVal (e6RootSparse r) a b : ℝ) =
        if a = b then 1 else 0
      rw [hsp, Int.cast_zero, mul_zero, add_zero]
  · intro x y hx hy
    refine ⟨fun a b hab => ?_, fun a b heq => ?_⟩
    · rw [h3zornToMatrix_mul_group, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hak : basisWeightHeight a < basisWeightHeight k
      · rw [hx.1 a k hak, zero_mul]
      · have hkb : basisWeightHeight k < basisWeightHeight b := by omega
        rw [hy.1 k b hkb, mul_zero]
    · rw [h3zornToMatrix_mul_group, Matrix.mul_apply]
      by_cases hab : a = b
      · subst hab
        simp only [↓reduceIte]
        rw [Finset.sum_eq_single a]
        · have hx1 := hx.2 a a rfl
          have hy1 := hy.2 a a rfl
          simp only [↓reduceIte] at hx1 hy1
          rw [hx1, hy1, mul_one]
        · intro k _ hka
          by_cases hklt : basisWeightHeight a < basisWeightHeight k
          · rw [hx.1 a k hklt, zero_mul]
          · by_cases hkeq : basisWeightHeight a = basisWeightHeight k
            · have hxk := hx.2 a k hkeq
              simp only [hka.symm, ↓reduceIte] at hxk
              rw [hxk, zero_mul]
            · have hkgt : basisWeightHeight k < basisWeightHeight a := by omega
              rw [hy.1 k a hkgt, mul_zero]
        · intro ha; exact absurd (Finset.mem_univ a) ha
      · simp only [hab, ↓reduceIte]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hklt : basisWeightHeight a < basisWeightHeight k
        · rw [hx.1 a k hklt, zero_mul]
        · by_cases hkeq : basisWeightHeight a = basisWeightHeight k
          · by_cases hka : a = k
            · have hyab := hy.2 a b heq
              simp only [hab, ↓reduceIte] at hyab
              rw [← hka, hyab, mul_zero]
            · have hxak := hx.2 a k hkeq
              simp only [hka, ↓reduceIte] at hxak
              rw [hxak, zero_mul]
          · have hkgt : basisWeightHeight k < basisWeightHeight b := by omega
            rw [hy.1 k b hkgt, mul_zero]

private theorem e6NegUnipotent_triangular (g : h3zornReducedStructureGroup)
    (hg : g ∈ e6NegUnipotent) :
    (∀ a b : Fin 27, basisWeightHeight b < basisWeightHeight a →
      h3zornToMatrix g.1.toLinearMap a b = 0) ∧
    (∀ a b : Fin 27, basisWeightHeight a = basisWeightHeight b →
      h3zornToMatrix g.1.toLinearMap a b = if a = b then 1 else 0) := by
  let S : Set h3zornReducedStructureGroup :=
    { x | ∃ r : Fin 72, e6IsPosRoot r = false ∧ ∃ c : ℝ, x = e6RootExp r c }
  refine subgroup_closure_symm_induction S
    (by rintro _ ⟨r, hneg, c, rfl⟩; exact ⟨r, hneg, -c, e6RootExp_inv_cb r c⟩)
    (fun g => (∀ a b : Fin 27, basisWeightHeight b < basisWeightHeight a →
      h3zornToMatrix g.1.toLinearMap a b = 0) ∧
      (∀ a b : Fin 27, basisWeightHeight a = basisWeightHeight b →
      h3zornToMatrix g.1.toLinearMap a b = if a = b then 1 else 0))
    ?_ ?_ ?_ g hg
  · refine ⟨fun a b hab => ?_, fun a b _ => ?_⟩
    · have hne : a ≠ b := fun h => by subst h; omega
      change h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) a b = 0
      rw [_root_.map_one, Matrix.one_apply_ne hne]
    · change h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) a b = if a = b then 1 else 0
      rw [_root_.map_one, Matrix.one_apply]
  · rintro _ ⟨r, hneg, c, rfl⟩
    refine ⟨fun a b hab => ?_, fun a b heq => ?_⟩
    · rw [h3zornToMatrix_e6RootExp]
      have hne : a ≠ b := fun h => by subst h; omega
      have hsp : sparseVal (e6RootSparse r) a b = 0 := by
        by_contra hnz
        have hlt := negRoot_strict_height r a b hneg hnz
        omega
      simp only [Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul, zero_add]
      change c * (sparseVal (e6RootSparse r) a b : ℝ) = 0
      rw [hsp, Int.cast_zero, mul_zero]
    · rw [h3zornToMatrix_e6RootExp]
      have hsp : sparseVal (e6RootSparse r) a b = 0 := by
        by_contra hnz
        have hlt := negRoot_strict_height r a b hneg hnz
        omega
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul]
      change (if a = b then (1 : ℝ) else 0) + c * (sparseVal (e6RootSparse r) a b : ℝ) =
        if a = b then 1 else 0
      rw [hsp, Int.cast_zero, mul_zero, add_zero]
  · intro x y hx hy
    refine ⟨fun a b hab => ?_, fun a b heq => ?_⟩
    · rw [h3zornToMatrix_mul_group, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hak : basisWeightHeight k < basisWeightHeight a
      · rw [hx.1 a k hak, zero_mul]
      · have hkb : basisWeightHeight b < basisWeightHeight k := by omega
        rw [hy.1 k b hkb, mul_zero]
    · rw [h3zornToMatrix_mul_group, Matrix.mul_apply]
      by_cases hab : a = b
      · subst hab
        simp only [↓reduceIte]
        rw [Finset.sum_eq_single a]
        · have hx1 := hx.2 a a rfl
          have hy1 := hy.2 a a rfl
          simp only [↓reduceIte] at hx1 hy1
          rw [hx1, hy1, mul_one]
        · intro k _ hka
          by_cases hklt : basisWeightHeight k < basisWeightHeight a
          · rw [hx.1 a k hklt, zero_mul]
          · by_cases hkeq : basisWeightHeight a = basisWeightHeight k
            · have hxk := hx.2 a k hkeq
              simp only [hka.symm, ↓reduceIte] at hxk
              rw [hxk, zero_mul]
            · have hkgt : basisWeightHeight a < basisWeightHeight k := by omega
              rw [hy.1 k a hkgt, mul_zero]
        · intro ha; exact absurd (Finset.mem_univ a) ha
      · simp only [hab, ↓reduceIte]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hklt : basisWeightHeight k < basisWeightHeight a
        · rw [hx.1 a k hklt, zero_mul]
        · by_cases hkeq : basisWeightHeight a = basisWeightHeight k
          · by_cases hka : a = k
            · have hyab := hy.2 a b heq
              simp only [hab, ↓reduceIte] at hyab
              rw [← hka, hyab, mul_zero]
            · have hxak := hx.2 a k hkeq
              simp only [hka, ↓reduceIte] at hxak
              rw [hxak, zero_mul]
          · have hkgt : basisWeightHeight b < basisWeightHeight k := by omega
            rw [hy.1 k b hkgt, mul_zero]

private theorem e6Torus_diag (g : h3zornReducedStructureGroup) (hg : g ∈ e6Torus) :
    ∀ a b : Fin 27, a ≠ b → h3zornToMatrix g.1.toLinearMap a b = 0 := by
  let S : Set h3zornReducedStructureGroup :=
    { x | ∃ (i : Fin 6) (t : ℝˣ), x = e6TorusElt i t }
  refine subgroup_closure_symm_induction S
    (by rintro _ ⟨i, t, rfl⟩; exact ⟨i, t⁻¹, e6TorusElt_inv_cb i t⟩)
    (fun g => ∀ a b : Fin 27, a ≠ b → h3zornToMatrix g.1.toLinearMap a b = 0)
    ?_ ?_ ?_ g hg
  · intro a b hab
    change h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) a b = 0
    rw [_root_.map_one, Matrix.one_apply_ne hab]
  · rintro _ ⟨i, t, rfl⟩ a b hab
    rw [h3zornToMatrix_e6TorusElt]
    simp only [hab, ↓reduceIte]
  · intro x y hx hy a b hab
    rw [h3zornToMatrix_mul_group, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hak : a = k
    · subst hak; rw [hy a b hab, mul_zero]
    · rw [hx a k hak, zero_mul]

/-- Disjointness of torus and positive unipotent subgroup: `T ∩ U⁺ = ⊥`. -/
theorem e6Torus_inf_posUnipotent_eq_bot : e6Torus ⊓ e6PosUnipotent = ⊥ := by
  rw [eq_bot_iff]
  intro g ⟨hgt, hgu⟩
  change g = 1
  apply h3zornToMatrix_group_injective
  change h3zornToMatrix g.1.toLinearMap = h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ))
  rw [_root_.map_one]
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq]
    have h := (e6PosUnipotent_triangular g hgu).2 a a rfl
    simp only [↓reduceIte] at h
    exact h
  · rw [Matrix.one_apply_ne hab]
    exact e6Torus_diag g hgt a b hab

/-- Disjointness of positive and negative unipotent subgroups: `U⁺ ∩ U⁻ = ⊥`. -/
theorem e6PosUnipotent_inf_negUnipotent_eq_bot : e6PosUnipotent ⊓ e6NegUnipotent = ⊥ := by
  rw [eq_bot_iff]
  intro g ⟨hgp, hgn⟩
  change g = 1
  apply h3zornToMatrix_group_injective
  change h3zornToMatrix g.1.toLinearMap = h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ))
  rw [_root_.map_one]
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq]
    have h := (e6PosUnipotent_triangular g hgp).2 a a rfl
    simp only [↓reduceIte] at h
    exact h
  · rw [Matrix.one_apply_ne hab]
    by_cases hlt : basisWeightHeight a < basisWeightHeight b
    · exact (e6PosUnipotent_triangular g hgp).1 a b hlt
    · by_cases heq : basisWeightHeight a = basisWeightHeight b
      · have h := (e6PosUnipotent_triangular g hgp).2 a b heq
        simp only [hab, ↓reduceIte] at h
        exact h
      · have hgt : basisWeightHeight b < basisWeightHeight a := by omega
        exact (e6NegUnipotent_triangular g hgn).1 a b hgt

private def e6TorusRootExp (j : Fin 6) (r : Fin 72) : ℤ :=
  (match j.val with
  | 0 => ![1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, 1, 0, 1, 0, 1, 0, 1, 0, 0, -1, 0, -1, 0, -1, 0, -1, 1, 0, 0, -1, 0, -1, 0, -1, 1, 0, 1, 0, 1, 0, 0, -1, -2, 0, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, 0, 2]
  | 1 => ![-1, 1, 0, 1, -1, 0, 0, -1, -2, -1, -1, 1, 2, 1, 1, 1, -1, 0, 0, 1, 1, -1, -1, 0, 0, 0, -1, -1, 1, 1, 0, 0, 1, 1, -1, -1, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 1, 1, -1, -1, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 1, 1, -1, -1, 0, 0, 0, 0]
  | 2 => ![0, 0, -1, 0, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, -1, -1, 0, 1, 0, 1, 0, 1, -1, 1, -1, 1, -1, 1, -2, 0, -1, 1, -1, 1, 0, 2, -1, 1, 0, -1, 1, 0, 1, 0, 0, -1, 0, -1, 0, -1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, -1, 0, -1, 0, -1, 1, 0, 0, -1]
  | 3 => ![0, -1, 1, 0, 1, -1, -1, 1, 1, -1, 0, 0, -1, -2, -1, 1, 2, 1, 1, -1, 0, 0, 1, -1, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 1, 1, -1, -1, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 1, 1, -1, -1, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 1, 1, -1, -1, 0, 0]
  | 4 => ![0, 0, -1, 0, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, -1, -1, 0, 1, 0, 1, 0, 1, 1, -1, 1, -1, 1, -1, 0, -2, 1, -1, 1, -1, 2, 0, 1, -1, -1, 0, 0, 1, 0, 1, -1, 0, -1, 0, -1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, -1, 0, -1, 0, -1, 0, 0, 1, -1, 0]
  | _ => ![1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, 0, 1, 0, 1, 0, 1, 0, 1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 1, -1, 0, -1, 0, -1, 0, 0, 1, 0, 1, 0, 1, -1, 0, 0, -2, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 2, 0]
  ) r

theorem e6TorusElt_conj_e6RootExp (j : Fin 6) (t : ℝˣ) (r : Fin 72) (c : ℝ) :
    e6TorusElt j t * e6RootExp r c * (e6TorusElt j t)⁻¹ =
      e6RootExp r ((t : ℝ) ^ e6TorusRootExp j r * c) := by
  have hchk : ∀ r : Fin 72,
      (e6RootSparse r).all (fun p =>
        h3zornWeight p.1 j - h3zornWeight p.2.1 j == e6TorusRootExp j r) = true :=
    allFin72Bool_sound _ (by fin_cases j <;> decide)
  have hdiag0 : ∀ r : Fin 72, (e6RootSparse r).all (fun p => p.1 != p.2.1) = true :=
    allFin72Bool_sound _ (by decide)
  apply h3zornToMatrix_group_injective
  dsimp only
  rw [e6TorusElt_inv_cb, h3zornToMatrix_mul_group, h3zornToMatrix_mul_group]
  ext a b
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single b]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [h3zornToMatrix_e6TorusElt, h3zornToMatrix_e6TorusElt]
      simp only [↓reduceIte, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]
      rw [h3zornToMatrix_e6RootExp, h3zornToMatrix_e6RootExp]
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul, sparseToMat]
      by_cases hab : a = b
      · subst hab
        have hda : sparseVal (e6RootSparse r) a a = 0 :=
          sparseVal_eq_zero_of_not_mem_cb _ a a (fun p hp ⟨h1, h2⟩ => by
            have hd := List.all_eq_true.mp (hdiag0 r) p hp
            simp only [bne_iff_ne, ne_eq] at hd
            exact hd (h1.trans h2.symm))
        simp only [↓reduceIte]
        change (t : ℝ) ^ h3zornWeight a j *
            (1 + c * (sparseVal (e6RootSparse r) a a : ℝ)) *
            (t : ℝ)⁻¹ ^ h3zornWeight a j =
          1 + (t : ℝ) ^ e6TorusRootExp j r * c * (sparseVal (e6RootSparse r) a a : ℝ)
        rw [hda]
        simp only [Int.cast_zero, mul_zero, add_zero, mul_one]
        rw [inv_zpow, ← zpow_neg, ← zpow_add₀ t.ne_zero, add_neg_cancel, zpow_zero]
      · simp only [hab, ↓reduceIte]
        change (t : ℝ) ^ h3zornWeight a j *
            (0 + c * (sparseVal (e6RootSparse r) a b : ℝ)) *
            (t : ℝ)⁻¹ ^ h3zornWeight b j =
          0 + (t : ℝ) ^ e6TorusRootExp j r * c * (sparseVal (e6RootSparse r) a b : ℝ)
        by_cases hsp : sparseVal (e6RootSparse r) a b = 0
        · rw [hsp, Int.cast_zero]; ring
        · obtain ⟨p, hp, rfl, rfl⟩ := exists_mem_of_sparseVal_ne_zero (e6RootSparse r) a b hsp
          have hw : h3zornWeight p.1 j - h3zornWeight p.2.1 j = e6TorusRootExp j r := by
            have hc := List.all_eq_true.mp (hchk r) p hp
            simpa [beq_iff_eq] using hc
          rw [zero_add, zero_add, inv_zpow, ← zpow_neg]
          have hpow : (t : ℝ) ^ h3zornWeight p.1 j * (t : ℝ) ^ (-h3zornWeight p.2.1 j) =
              (t : ℝ) ^ e6TorusRootExp j r := by
            rw [← zpow_add₀ t.ne_zero, ← sub_eq_add_neg, hw]
          calc (t : ℝ) ^ h3zornWeight p.1 j * (c * (sparseVal (e6RootSparse r) p.1 p.2.1 : ℝ)) *
                (t : ℝ) ^ (-h3zornWeight p.2.1 j)
              = ((t : ℝ) ^ h3zornWeight p.1 j * (t : ℝ) ^ (-h3zornWeight p.2.1 j)) * c *
                  (sparseVal (e6RootSparse r) p.1 p.2.1 : ℝ) := by ring
            _ = (t : ℝ) ^ e6TorusRootExp j r * c *
                  (sparseVal (e6RootSparse r) p.1 p.2.1 : ℝ) := by
              rw [hpow]
    · intro k _ hka; rw [h3zornToMatrix_e6TorusElt]; simp [hka.symm]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  · intro k _ hkb; rw [h3zornToMatrix_e6TorusElt]; simp [hkb]
  · intro hb; exact absurd (Finset.mem_univ b) hb

private theorem e6Torus_conj_posUnipotent (t u : h3zornReducedStructureGroup)
    (ht : t ∈ e6Torus) (hu : u ∈ e6PosUnipotent) :
    t * u * t⁻¹ ∈ e6PosUnipotent := by
  let S_t : Set h3zornReducedStructureGroup :=
    { x | ∃ (j : Fin 6) (s : ℝˣ), x = e6TorusElt j s }
  have hconj_gen : ∀ (x : h3zornReducedStructureGroup) (_ : x ∈ S_t) (v : h3zornReducedStructureGroup),
      v ∈ e6PosUnipotent → x * v * x⁻¹ ∈ e6PosUnipotent := by
    rintro _ ⟨j, s, rfl⟩ v hv
    let S_u : Set h3zornReducedStructureGroup :=
      { y | ∃ r : Fin 72, e6IsPosRoot r = true ∧ ∃ c : ℝ, y = e6RootExp r c }
    refine subgroup_closure_symm_induction S_u
      (by rintro _ ⟨r, hpos, c, rfl⟩; exact ⟨r, hpos, -c, e6RootExp_inv_cb r c⟩)
      (fun w => e6TorusElt j s * w * (e6TorusElt j s)⁻¹ ∈ e6PosUnipotent)
      (by simp [e6PosUnipotent.one_mem])
      (by
        rintro _ ⟨r, hpos, c, rfl⟩
        rw [e6TorusElt_conj_e6RootExp]
        exact Subgroup.subset_closure ⟨r, hpos, _, rfl⟩)
      (by
        intro y z hy hz
        have hmul : e6TorusElt j s * (y * z) * (e6TorusElt j s)⁻¹ =
            (e6TorusElt j s * y * (e6TorusElt j s)⁻¹) *
              (e6TorusElt j s * z * (e6TorusElt j s)⁻¹) := by group
        rw [hmul]
        exact e6PosUnipotent.mul_mem hy hz)
      v hv
  refine subgroup_closure_symm_induction S_t
    (by rintro _ ⟨j, s, rfl⟩; exact ⟨j, s⁻¹, e6TorusElt_inv_cb j s⟩)
    (fun x => ∀ v ∈ e6PosUnipotent, x * v * x⁻¹ ∈ e6PosUnipotent)
    (by intro v hv; simpa using hv)
    (fun x hx v hv => hconj_gen x hx v hv)
    (by
      intro x y hx hy v hv
      have hmul : (x * y) * v * (x * y)⁻¹ = x * (y * v * y⁻¹) * x⁻¹ := by group
      rw [hmul]
      exact hx _ (hy v hv))
    t ht u hu

/-- Borel factorization `B = T * U⁺`. -/
theorem e6Borel_eq_torus_mul_posUnipotent (g : h3zornReducedStructureGroup) :
    g ∈ e6Borel ↔ ∃ t ∈ e6Torus, ∃ u ∈ e6PosUnipotent, g = t * u := by
  constructor
  · intro hg
    let M : Subgroup h3zornReducedStructureGroup :=
      { carrier := { x | ∃ t ∈ e6Torus, ∃ u ∈ e6PosUnipotent, x = t * u }
        one_mem' := ⟨1, e6Torus.one_mem, 1, e6PosUnipotent.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨t₁, ht₁, u₁, hu₁, rfl⟩ ⟨t₂, ht₂, u₂, hu₂, rfl⟩
          refine ⟨t₁ * t₂, e6Torus.mul_mem ht₁ ht₂,
            (t₂⁻¹ * u₁ * t₂) * u₂, e6PosUnipotent.mul_mem ?_ hu₂, ?_⟩
          · have hconj : t₂⁻¹ * u₁ * t₂ = t₂⁻¹ * u₁ * (t₂⁻¹)⁻¹ := by simp
            rw [hconj]
            exact e6Torus_conj_posUnipotent t₂⁻¹ u₁ (e6Torus.inv_mem ht₂) hu₁
          · group
        inv_mem' := by
          rintro _ ⟨t, ht, u, hu, rfl⟩
          refine ⟨t⁻¹, e6Torus.inv_mem ht, t * u⁻¹ * t⁻¹,
            e6Torus_conj_posUnipotent t u⁻¹ ht (e6PosUnipotent.inv_mem hu), ?_⟩
          group }
    have hle : e6Borel ≤ M := by
      dsimp only [e6Borel]
      rw [Subgroup.closure_le]
      rintro x (hx | hx)
      · exact ⟨x, hx, 1, e6PosUnipotent.one_mem, by simp⟩
      · exact ⟨1, e6Torus.one_mem, x, hx, by simp⟩
    exact hle hg
  · rintro ⟨t, ht, u, hu, rfl⟩
    exact e6Borel.mul_mem
      (Subgroup.subset_closure (Set.mem_union_left _ ht))
      (Subgroup.subset_closure (Set.mem_union_right _ hu))

/-- Disjointness of Borel and opposite unipotent subgroup: `B ∩ U⁻ = ⊥`. -/
theorem e6Borel_inf_negUnipotent_eq_bot : e6Borel ⊓ e6NegUnipotent = ⊥ := by
  rw [eq_bot_iff]
  intro g ⟨hgb, hgn⟩
  change g = 1
  obtain ⟨t, ht, u, hu, rfl⟩ := (e6Borel_eq_torus_mul_posUnipotent g).mp hgb
  have ht_one : t = 1 := by
    apply h3zornToMatrix_group_injective
    change h3zornToMatrix t.1.toLinearMap = h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ))
    rw [_root_.map_one]
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq]
      have hdiag1 := (e6NegUnipotent_triangular (t * u) hgn).2 a a rfl
      simp only [↓reduceIte] at hdiag1
      rw [h3zornToMatrix_mul_group, Matrix.mul_apply, Finset.sum_eq_single a] at hdiag1
      · have hu1 := (e6PosUnipotent_triangular u hu).2 a a rfl
        simp only [↓reduceIte] at hu1
        rw [hu1, mul_one] at hdiag1
        exact hdiag1
      · intro k _ hka; rw [e6Torus_diag t ht a k hka.symm, zero_mul]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    · rw [Matrix.one_apply_ne hab]
      exact e6Torus_diag t ht a b hab
  rw [ht_one, one_mul] at hgn ⊢
  have hmem : u ∈ e6PosUnipotent ⊓ e6NegUnipotent := ⟨hu, hgn⟩
  rw [e6PosUnipotent_inf_negUnipotent_eq_bot] at hmem
  exact hmem

private theorem e6WeylElt_one_mul_self (i : Fin 6) :
    e6WeylElt i 1 * e6WeylElt i 1 = e6TorusElt i (-1) := by
  apply h3zornToMatrix_group_injective
  dsimp only
  rw [h3zornToMatrix_mul_group, h3zornToMatrix_e6WeylOne]
  have hsq : sparseToMat (sparseMul (weylOneSparseMat i) (weylOneSparseMat i)) =
      Matrix.diagonal (fun k => if h3zornWeight k i = 0 then (1 : ℤ) else -1) := by
    have hchk : ∀ r c : Fin 27,
        sparseVal (sparseMul (weylOneSparseMat i) (weylOneSparseMat i)) r c =
          if r = c then (if h3zornWeight r i = 0 then (1 : ℤ) else -1) else 0 := by
      have h0 : (List.finRange 27).all (fun r => (List.finRange 27).all (fun c =>
          sparseVal (sparseMul (weylOneSparseMat i) (weylOneSparseMat i)) r c ==
            if r == c then (if h3zornWeight r i == 0 then (1 : ℤ) else -1) else 0)) = true := by
        fin_cases i <;> decide
      simp only [List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at h0
      exact fun r c => by simpa using h0 r c
    ext r c
    change sparseVal (sparseMul (weylOneSparseMat i) (weylOneSparseMat i)) r c = _
    rw [hchk r c]
    by_cases hrc : r = c
    · subst hrc; simp
    · simp [hrc]
  ext a b
  rw [Matrix.mul_apply]
  have h1 := congrArg (fun M : Matrix (Fin 27) (Fin 27) ℤ => (M a b : ℝ))
    ((sparseToMat_mul (weylOneSparseMat i) (weylOneSparseMat i)).symm.trans hsq)
  rw [Matrix.mul_apply, Int.cast_sum] at h1
  simp only [Int.cast_mul] at h1
  rw [h3zornToMatrix_e6TorusElt]
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte, Matrix.map_apply, Units.val_zpow_eq_zpow_val]
    rw [h1, Matrix.diagonal_apply_eq]
    rcases h3zornWeight_values_cb a i with hm1 | h0 | h1w <;> simp [*]
  · simp only [hab, ↓reduceIte, Matrix.map_apply]
    rw [h1]; simp [hab]

private theorem e6WeylElt_one_inv (i : Fin 6) :
    (e6WeylElt i 1)⁻¹ = e6WeylElt i 1 * e6TorusElt i (-1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, e6WeylElt_one_mul_self]
  apply h3zornToMatrix_group_injective
  dsimp only
  rw [h3zornToMatrix_mul_group]
  change h3zornToMatrix (e6TorusElt i (-1)).1.toLinearMap *
      h3zornToMatrix (e6TorusElt i (-1)).1.toLinearMap =
    h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ))
  rw [_root_.map_one]
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [h3zornToMatrix_e6TorusElt, h3zornToMatrix_e6TorusElt]
    simp only [↓reduceIte, Units.val_zpow_eq_zpow_val]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq]
      rcases h3zornWeight_values_cb a i with hm1 | h0 | h1 <;> simp [*]
    · rw [Matrix.one_apply_ne hab]; simp [hab]
  · intro k _ hka; rw [h3zornToMatrix_e6TorusElt]; simp [hka.symm]
  · intro ha; exact absurd (Finset.mem_univ a) ha

private def e6WeylPermRow (i : Fin 6) : Fin 72 → Fin 72 :=
  match i.val with
  | 0 => ![58, 60, 62, 3, 4, 5, 68, 66, 8, 9, 10, 64, 12, 13, 14, 15, 16, 17, 63, 61, 65, 59, 67, 69, 55, 25, 43, 27, 45, 29, 47, 31, 32, 48, 34, 50, 36, 52, 38, 40, 39, 41, 42, 26, 44, 28, 46, 30, 33, 49, 35, 51, 37, 53, 54, 24, 71, 57, 0, 21, 1, 19, 2, 18, 11, 20, 7, 22, 6, 23, 70, 56]
  | 1 => ![1, 0, 2, 4, 3, 5, 6, 11, 12, 13, 14, 7, 8, 9, 10, 16, 15, 17, 18, 21, 22, 19, 20, 23, 24, 25, 28, 29, 26, 27, 30, 31, 34, 35, 32, 33, 36, 37, 38, 39, 40, 41, 44, 45, 42, 43, 46, 47, 50, 51, 48, 49, 52, 53, 54, 55, 56, 57, 60, 61, 58, 59, 62, 63, 66, 67, 64, 65, 68, 69, 70, 71]
  | 2 => ![0, 1, 25, 3, 4, 24, 6, 27, 8, 26, 10, 29, 12, 28, 14, 33, 35, 39, 18, 32, 20, 34, 22, 38, 5, 2, 9, 7, 13, 11, 37, 31, 19, 15, 21, 16, 36, 30, 23, 17, 40, 68, 67, 43, 65, 45, 46, 56, 48, 60, 50, 58, 71, 53, 63, 55, 47, 57, 51, 59, 49, 61, 62, 54, 64, 44, 66, 42, 41, 69, 70, 52]
  | 3 => ![0, 2, 1, 3, 5, 4, 7, 6, 9, 8, 10, 11, 15, 16, 17, 12, 13, 14, 19, 18, 20, 21, 23, 22, 24, 25, 26, 27, 30, 31, 28, 29, 32, 33, 36, 37, 34, 35, 38, 39, 40, 41, 42, 43, 46, 47, 44, 45, 48, 49, 52, 53, 50, 51, 54, 55, 56, 57, 58, 59, 62, 63, 60, 61, 64, 65, 68, 69, 66, 67, 70, 71]
  | 4 => ![0, 1, 24, 3, 4, 25, 6, 26, 8, 27, 10, 28, 12, 29, 14, 32, 34, 38, 18, 33, 20, 35, 22, 39, 2, 5, 7, 9, 11, 13, 30, 36, 15, 19, 16, 21, 31, 37, 17, 23, 69, 41, 42, 66, 44, 64, 57, 47, 61, 49, 59, 51, 52, 70, 54, 62, 56, 46, 58, 50, 60, 48, 55, 63, 45, 65, 43, 67, 68, 40, 53, 71]
  | _ => ![59, 61, 63, 3, 4, 5, 69, 67, 8, 9, 10, 65, 12, 13, 14, 15, 16, 17, 62, 60, 64, 58, 66, 68, 24, 54, 26, 42, 28, 44, 30, 46, 49, 33, 51, 35, 53, 37, 41, 39, 40, 38, 27, 43, 29, 45, 31, 47, 48, 32, 50, 34, 52, 36, 25, 55, 56, 70, 21, 0, 19, 1, 18, 2, 20, 11, 22, 7, 23, 6, 57, 71]

private def e6WeylPerm (i : Fin 6) (r : Fin 72) : Fin 72 := e6WeylPermRow i r

private def e6WeylSign (i : Fin 6) (r : Fin 72) : ℤ :=
  (match i.val with
  | 0 => ![1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, 1, 1, -1, 1, -1, -1, -1, 1, -1, -1, -1, -1, 1, -1, -1, -1, 1, -1]
  | 1 => ![-1, 1, 1, -1, 1, 1, 1, -1, -1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1]
  | 2 => ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, 1, 1, -1, 1, -1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1, 1, 1, -1, 1, 1, -1]
  | 3 => ![1, -1, 1, 1, -1, 1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1]
  | 4 => ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, -1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, -1, 1, 1, -1, 1, 1, 1, -1, 1, 1, 1, -1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1]
  | _ => ![1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, -1, -1, -1, 1, -1, -1, -1, -1, -1, -1, 1, -1, -1, -1, 1]
  ) r

private def e6NegRoot : Fin 72 → Fin 72 :=
  ![20, 22, 23, 10, 14, 17, 18, 19, 12, 15, 3, 21, 8, 16, 4, 9, 13, 5, 6, 7, 0, 11, 1, 2, 39, 38, 33, 32, 35, 34, 37, 36, 27, 26, 29, 28, 31, 30, 25, 24, 55, 54, 49, 48, 51, 50, 53, 52, 43, 42, 45, 44, 47, 46, 41, 40, 71, 70, 65, 64, 67, 66, 69, 68, 59, 58, 61, 60, 63, 62, 57, 56]

private def e6WeylConjPred (i : Fin 6) (r : Fin 72) : Bool :=
  sparseEq (sparseMul (weylOneSparseMat i) (e6RootSparse r))
    (sparseSmul (e6WeylSign i r)
      (sparseMul (e6RootSparse (e6WeylPerm i r)) (weylOneSparseMat i)))

private theorem e6WeylConj_chk0 : ∀ r : Fin 72, e6WeylConjPred 0 r = true :=
  allFin72_by9 _ (by intro k; fin_cases k <;> decide)
private theorem e6WeylConj_chk1 : ∀ r : Fin 72, e6WeylConjPred 1 r = true :=
  allFin72_by9 _ (by intro k; fin_cases k <;> decide)
private theorem e6WeylConj_chk2 : ∀ r : Fin 72, e6WeylConjPred 2 r = true :=
  allFin72_by9 _ (by intro k; fin_cases k <;> decide)
private theorem e6WeylConj_chk3 : ∀ r : Fin 72, e6WeylConjPred 3 r = true :=
  allFin72_by9 _ (by intro k; fin_cases k <;> decide)
private theorem e6WeylConj_chk4 : ∀ r : Fin 72, e6WeylConjPred 4 r = true :=
  allFin72_by9 _ (by intro k; fin_cases k <;> decide)
private theorem e6WeylConj_chk5 : ∀ r : Fin 72, e6WeylConjPred 5 r = true :=
  allFin72_by9 _ (by intro k; fin_cases k <;> decide)

theorem e6WeylElt_one_conj_e6RootExp (i : Fin 6) (r : Fin 72) (c : ℝ) :
    e6WeylElt i 1 * e6RootExp r c * (e6WeylElt i 1)⁻¹ =
      e6RootExp (e6WeylPerm i r) ((e6WeylSign i r : ℝ) * c) := by
  have hchk : sparseEq (sparseMul (weylOneSparseMat i) (e6RootSparse r))
      (sparseSmul (e6WeylSign i r)
        (sparseMul (e6RootSparse (e6WeylPerm i r)) (weylOneSparseMat i))) = true := by
    fin_cases i
    · exact e6WeylConj_chk0 r
    · exact e6WeylConj_chk1 r
    · exact e6WeylConj_chk2 r
    · exact e6WeylConj_chk3 r
    · exact e6WeylConj_chk4 r
    · exact e6WeylConj_chk5 r
  have hm_int := sparseToMat_eq_of_sparseEq hchk
  rw [sparseToMat_mul, sparseToMat_smul, sparseToMat_mul] at hm_int
  have hconj : h3zornToMatrix (e6WeylElt i 1).1.toLinearMap *
      h3zornToMatrix (e6RootExp r c).1.toLinearMap =
      h3zornToMatrix (e6RootExp (e6WeylPerm i r) ((e6WeylSign i r : ℝ) * c)).1.toLinearMap *
        h3zornToMatrix (e6WeylElt i 1).1.toLinearMap := by
    rw [h3zornToMatrix_e6WeylOne, h3zornToMatrix_e6RootExp, h3zornToMatrix_e6RootExp]
    simp only [mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have hm_r : (sparseToMat (weylOneSparseMat i)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (e6RootSparse r)).map Int.cast =
        (e6WeylSign i r : ℝ) •
          ((sparseToMat (e6RootSparse (e6WeylPerm i r))).map (Int.cast : ℤ → ℝ) *
            (sparseToMat (weylOneSparseMat i)).map Int.cast) := by
      ext a b
      have hrc := congrArg (fun M : Matrix (Fin 27) (Fin 27) ℤ => (M a b : ℝ)) hm_int
      simpa [Matrix.mul_apply, Matrix.smul_apply] using hrc
    rw [hm_r, smul_smul, mul_comm c (e6WeylSign i r : ℝ)]
  apply mul_inv_eq_of_eq_mul
  apply h3zornToMatrix_group_injective
  dsimp only
  rw [h3zornToMatrix_mul_group, h3zornToMatrix_mul_group]
  exact hconj

private def e6RootDist : Fin 72 → ℕ :=
  ![4, 5, 6, 10, 9, 8, 5, 4, 1, 2, 11, 3, 0, 1, 10, 1, 0, 9, 4, 3, 5, 2, 6, 7, 7, 7, 3, 3, 2, 2, 1, 1, 2, 2, 1, 1, 0, 0, 8, 8, 7, 7, 4, 4, 3, 3, 2, 2, 3, 3, 2, 2, 1, 1, 6, 6, 1, 1, 3, 3, 4, 4, 5, 5, 4, 4, 5, 5, 6, 6, 0, 0]

private def e6RootPredI : Fin 72 → Fin 6 :=
  ![5, 5, 5, 1, 3, 4, 3, 4, 1, 3, 1, 4, 0, 3, 3, 3, 0, 4, 3, 4, 5, 4, 5, 5, 4, 5, 2, 4, 3, 4, 2, 4, 4, 2, 4, 3, 0, 0, 5, 4, 4, 2, 5, 1, 5, 3, 5, 2, 1, 5, 3, 5, 2, 5, 2, 4, 0, 5, 5, 4, 5, 4, 5, 3, 4, 5, 4, 5, 3, 5, 0, 0]

private def e6RootPredP : Fin 72 → Fin 72 :=
  ![59, 61, 63, 4, 5, 25, 7, 26, 12, 8, 14, 28, 12, 16, 17, 12, 16, 38, 19, 33, 64, 35, 66, 68, 2, 54, 9, 9, 30, 13, 37, 36, 15, 15, 16, 37, 36, 37, 41, 23, 69, 68, 27, 45, 29, 47, 31, 56, 50, 32, 52, 34, 71, 36, 63, 62, 71, 70, 21, 50, 19, 48, 18, 61, 45, 11, 43, 7, 66, 6, 70, 71]

/-- **Simple-Generator Closure Theorem (`G = ⟨x_i(c), y_i(c)⟩`)**:
all 72 root exponentials lie in `e6SimpleClosure`, so `e6ChevalleySubgroup = e6SimpleClosure`. -/
theorem e6ChevalleySubgroup_eq_simpleClosure : e6ChevalleySubgroup = e6SimpleClosure := by
  apply le_antisymm
  · rw [e6ChevalleySubgroup, Subgroup.closure_le]
    rintro _ ⟨r, c, rfl⟩
    have hstep : ∀ (i : Fin 6) (r₀ : Fin 72),
        (∀ x : ℝ, e6RootExp r₀ x ∈ e6SimpleClosure) →
        ∀ x : ℝ, e6RootExp (e6WeylPerm i r₀) x ∈ e6SimpleClosure := by
      intro i r₀ hr₀ x
      have hsign : e6WeylSign i r₀ = 1 ∨ e6WeylSign i r₀ = -1 := by
        have hchk : ∀ r : Fin 72,
            ((e6WeylSign i r == 1) || (e6WeylSign i r == -1)) = true :=
          allFin72Bool_sound _ (by fin_cases i <;> decide)
        simpa [Bool.or_eq_true, beq_iff_eq] using hchk r₀
      have hmul_s : ((e6WeylSign i r₀ : ℝ) * ((e6WeylSign i r₀ : ℝ) * x)) = x := by
        rcases hsign with hs | hs <;> simp [hs]
      have hw_mem : e6WeylElt i 1 ∈ e6SimpleClosure := by
        refine e6SimpleClosure.mul_mem (e6SimpleClosure.mul_mem ?_ ?_) ?_
        · exact Subgroup.subset_closure (Set.mem_union_left _ ⟨i, 1, rfl⟩)
        · exact Subgroup.subset_closure (Set.mem_union_right _ ⟨i, -1, rfl⟩)
        · exact Subgroup.subset_closure (Set.mem_union_left _ ⟨i, 1, rfl⟩)
      have hc := e6WeylElt_one_conj_e6RootExp i r₀ ((e6WeylSign i r₀ : ℝ) * x)
      rw [hmul_s] at hc
      rw [← hc]
      exact e6SimpleClosure.mul_mem (e6SimpleClosure.mul_mem hw_mem (hr₀ _))
        (e6SimpleClosure.inv_mem hw_mem)
    have hchk : ∀ r₀ : Fin 72,
        (if e6RootDist r₀ == 0 then
          (List.finRange 6).any (fun i => r₀ == eSimpleIdx i)
        else
          decide (e6RootDist (e6RootPredP r₀) < e6RootDist r₀) &&
            (e6WeylPerm (e6RootPredI r₀) (e6RootPredP r₀) == r₀)) = true :=
      allFin72Bool_sound _ (by decide)
    have hdist : ∀ d : ℕ, ∀ r₀ : Fin 72, e6RootDist r₀ = d →
        ∀ x : ℝ, e6RootExp r₀ x ∈ e6SimpleClosure := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
        intro r₀ hd x
        have hr := hchk r₀
        by_cases hd0 : e6RootDist r₀ = 0
        · simp only [hd0, beq_self_eq_true, ↓reduceIte, List.any_eq_true, List.mem_finRange,
            beq_iff_eq, true_and] at hr
          rcases hr with ⟨i, rfl⟩
          rw [← e6SimpleX_eq_rootExp]
          exact Subgroup.subset_closure (Set.mem_union_left _ ⟨i, x, rfl⟩)
        · have hbf : (e6RootDist r₀ == 0) = false := by simp [hd0]
          simp only [hbf, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
            beq_iff_eq] at hr
          rcases hr with ⟨hlt, hperm⟩
          rw [← hperm]
          exact hstep (e6RootPredI r₀) (e6RootPredP r₀)
            (ih (e6RootDist (e6RootPredP r₀)) (hd ▸ hlt) (e6RootPredP r₀) rfl) x
    exact hdist (e6RootDist r) r rfl c
  · rw [e6SimpleClosure, Subgroup.closure_le]
    rintro _ (⟨i, c, rfl⟩ | ⟨i, c, rfl⟩)
    · exact e6SimpleX_mem_chevalley i c
    · exact e6SimpleY_mem_chevalley i c

private def e6WeylTorusStep (i j : Fin 6) : ℤ :=
  if i = j then -2 else
    if (match i.val, j.val with
      | 0, 2 | 2, 0 | 1, 3 | 3, 1 | 2, 3 | 3, 2 | 3, 4 | 4, 3 | 4, 5 | 5, 4 => true
      | _, _ => false) then 1 else 0

private theorem e6WeylElt_one_conj_torus (i j : Fin 6) (t : ℝˣ) :
    e6WeylElt i 1 * e6TorusElt j t * (e6WeylElt i 1)⁻¹ ∈ e6Torus := by
  have heq : e6WeylElt i 1 * e6TorusElt j t * (e6WeylElt i 1)⁻¹ =
      e6TorusElt j t * e6TorusElt i (t ^ e6WeylTorusStep i j) := by
    have hchk : (List.finRange 6).all (fun i => (List.finRange 6).all (fun j =>
        (weylOneSparseMat i).all (fun p =>
          h3zornWeight p.2.1 j == h3zornWeight p.1 j + e6WeylTorusStep i j * h3zornWeight p.1 i))) =
          true := by
      decide
    simp only [List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at hchk
    apply mul_inv_eq_of_eq_mul
    apply h3zornToMatrix_group_injective
    dsimp only
    rw [h3zornToMatrix_mul_group, h3zornToMatrix_mul_group, h3zornToMatrix_mul_group]
    ext a b
    rw [Matrix.mul_apply]
    conv_rhs => rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single a]
      · rw [Matrix.mul_apply, Finset.sum_eq_single a]
        · rw [h3zornToMatrix_e6TorusElt, h3zornToMatrix_e6TorusElt, h3zornToMatrix_e6TorusElt]
          simp only [↓reduceIte, Units.val_zpow_eq_zpow_val]
          have hw : h3zornToMatrix (e6WeylElt i 1).1.toLinearMap a b =
              (sparseVal (weylOneSparseMat i) a b : ℝ) := by
            rw [h3zornToMatrix_e6WeylOne, Matrix.map_apply]; rfl
          rw [hw]
          by_cases hmem : ∃ p ∈ weylOneSparseMat i, p.1 = a ∧ p.2.1 = b
          · rcases hmem with ⟨p, hp, rfl, rfl⟩
            have hstep := hchk i j p hp
            have hpow : (t : ℝ) ^ h3zornWeight p.2.1 j =
                (t : ℝ) ^ h3zornWeight p.1 j *
                  ((t : ℝ) ^ e6WeylTorusStep i j) ^ h3zornWeight p.1 i := by
              rw [← zpow_mul, ← zpow_add₀ t.ne_zero, hstep]
            rw [hpow]; ring
          · rw [sparseVal_eq_zero_of_not_mem_cb (weylOneSparseMat i) a b
                (fun p hp hpe => hmem ⟨p, hp, hpe⟩),
              Int.cast_zero, zero_mul, mul_zero]
        · intro m _ hma; rw [h3zornToMatrix_e6TorusElt]; simp [hma.symm]
        · intro ha; exact absurd (Finset.mem_univ a) ha
      · intro k _ hka
        apply mul_eq_zero_of_left
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun m _ => ?_
        by_cases ham : a = m
        · subst ham; apply mul_eq_zero_of_right; rw [h3zornToMatrix_e6TorusElt]; simp [hka.symm]
        · apply mul_eq_zero_of_left; rw [h3zornToMatrix_e6TorusElt]; simp [ham]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    · intro k _ hkb
      rw [h3zornToMatrix_e6TorusElt]; simp [hkb]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  rw [heq]
  exact e6Torus.mul_mem (Subgroup.subset_closure ⟨j, t, rfl⟩) (Subgroup.subset_closure ⟨i, _, rfl⟩)

private theorem e6WeylElt_one_conj_e6Torus (i : Fin 6) (t : h3zornReducedStructureGroup)
    (ht : t ∈ e6Torus) : e6WeylElt i 1 * t * (e6WeylElt i 1)⁻¹ ∈ e6Torus := by
  let S : Set h3zornReducedStructureGroup := { x | ∃ (j : Fin 6) (s : ℝˣ), x = e6TorusElt j s }
  refine subgroup_closure_symm_induction S
    (by rintro _ ⟨j, s, rfl⟩; exact ⟨j, s⁻¹, e6TorusElt_inv_cb j s⟩)
    (fun t => e6WeylElt i 1 * t * (e6WeylElt i 1)⁻¹ ∈ e6Torus)
    (by simp [e6Torus.one_mem])
    (by rintro _ ⟨j, s, rfl⟩; exact e6WeylElt_one_conj_torus i j s)
    (by
      intro x y hx hy
      have hmul : e6WeylElt i 1 * (x * y) * (e6WeylElt i 1)⁻¹ =
          (e6WeylElt i 1 * x * (e6WeylElt i 1)⁻¹) * (e6WeylElt i 1 * y * (e6WeylElt i 1)⁻¹) := by
        group
      rw [hmul]
      exact e6Torus.mul_mem hx hy)
    t ht

private def e6CommRootRow (i : Fin 6) : Fin 72 → Fin 72 :=
  match i.val with
  | 0 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63, 61, 0, 59, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 50, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => ![1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 49, 0, 0, 0, 0, 0, 0, 60, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => ![0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 35, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 19, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 0, 58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 52]
  | 3 => ![0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 51, 0, 0, 0, 0, 0, 0, 62, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 4 => ![0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 34, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 19, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 0, 59, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 53, 0]
  | _ => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 60, 0, 58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 0, 51, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]

private def e6CommRoot (i : Fin 6) (r : Fin 72) : Fin 72 := e6CommRootRow i r

private def e6CommSign (i : Fin 6) (r : Fin 72) : ℤ :=
  (match i.val with
  | 0 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => ![-1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1]
  | 3 => ![0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 4 => ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0]
  | _ => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0]
  ) r

private theorem e6SimpleX_conj_posUnipotentExcept (i : Fin 6) (c : ℝ)
    (u : h3zornReducedStructureGroup) (hu : u ∈ e6PosUnipotentExcept i) :
    e6SimpleX i c * u * (e6SimpleX i c)⁻¹ ∈ e6PosUnipotentExcept i := by
  have hchk : ∀ r : Fin 72,
      (if e6IsPosRoot r && !(r == eSimpleIdx i) then
        if e6CommSign i r == 0 then
          sparseEq (sparseMul (e6SimpleESparse i) (e6RootSparse r))
            (sparseMul (e6RootSparse r) (e6SimpleESparse i))
        else
          e6IsPosRoot (e6CommRoot i r) && !(e6CommRoot i r == eSimpleIdx i) &&
            sparseEq (sparseComm (e6SimpleESparse i) (e6RootSparse r))
              (sparseSmul (e6CommSign i r) (e6RootSparse (e6CommRoot i r))) &&
            sparseZeroCheck (sparseMul (e6SimpleESparse i)
              (sparseMul (e6RootSparse r) (e6SimpleESparse i))) &&
            sparseZeroCheck (sparseMul (e6RootSparse r) (e6RootSparse (e6CommRoot i r)))
      else true) = true :=
    allFin72Bool_sound _ (by fin_cases i <;> decide)
  let S : Set h3zornReducedStructureGroup :=
    { x | ∃ r : Fin 72, e6IsPosRoot r = true ∧ r ≠ eSimpleIdx i ∧ ∃ a : ℝ, x = e6RootExp r a }
  refine subgroup_closure_symm_induction S
    (by rintro _ ⟨r, hpos, hne, a, rfl⟩; exact ⟨r, hpos, hne, -a, e6RootExp_inv_cb r a⟩)
    (fun w => e6SimpleX i c * w * (e6SimpleX i c)⁻¹ ∈ e6PosUnipotentExcept i)
    (by simp [(e6PosUnipotentExcept i).one_mem])
    ?_ ?_ u hu
  · rintro _ ⟨r, hpos, hne, a, rfl⟩
    have hr := hchk r
    have hcond : (e6IsPosRoot r && !(r == eSimpleIdx i)) = true := by
      simp [hpos, hne]
    simp only [hcond, ↓reduceIte] at hr
    by_cases hcs : e6CommSign i r = 0
    · have hcz : (e6CommSign i r == 0) = true := by simp [hcs]
      simp only [hcz, ↓reduceIte] at hr
      have hm := sparseToMat_eq_of_sparseEq hr
      rw [sparseToMat_mul, sparseToMat_mul] at hm
      have heq : e6SimpleX i c * e6RootExp r a * (e6SimpleX i c)⁻¹ = e6RootExp r a := by
        rw [e6SimpleX_eq_rootExp]
        apply mul_inv_eq_of_eq_mul
        apply h3zornToMatrix_group_injective
        dsimp only
        rw [h3zornToMatrix_mul_group, h3zornToMatrix_mul_group,
          h3zornToMatrix_e6RootExp, h3zornToMatrix_e6RootExp]
        simp only [mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul]
        have hEr : (sparseToMat (e6RootSparse (eSimpleIdx i))).map (Int.cast : ℤ → ℝ) *
            (sparseToMat (e6RootSparse r)).map Int.cast =
            (sparseToMat (e6RootSparse r)).map Int.cast *
              (sparseToMat (e6RootSparse (eSimpleIdx i))).map Int.cast := by
          ext p q
          have hpq := congrArg (fun M : Matrix (Fin 27) (Fin 27) ℤ => (M p q : ℝ)) hm
          simpa [Matrix.mul_apply, e6SimpleESparse] using hpq
        rw [hEr, add_assoc, add_assoc, smul_smul, smul_smul, mul_comm a c]; abel_nf
      rw [heq]
      exact Subgroup.subset_closure ⟨r, hpos, hne, a, rfl⟩
    · have hcz : (e6CommSign i r == 0) = false := by simp [hcs]
      simp only [hcz, Bool.false_eq_true, ↓reduceIte] at hr
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hr
      rcases hr with ⟨⟨⟨⟨hp_pos, hp_ne⟩, hm_comm⟩, hm_ere⟩, hm_rrp⟩
      have hm1 := sparseToMat_eq_of_sparseEq hm_comm
      have hm2 := sparseToMat_eq_zero_of_sparseZeroCheck hm_ere
      have hm3 := sparseToMat_eq_zero_of_sparseZeroCheck hm_rrp
      simp only [sparseComm, sparseToMat_sub, sparseToMat_mul, sparseToMat_smul] at hm1 hm2 hm3
      have heq : e6SimpleX i c * e6RootExp r a * (e6SimpleX i c)⁻¹ =
          e6RootExp r a * e6RootExp (e6CommRoot i r) ((e6CommSign i r : ℝ) * c * a) := by
        rw [e6SimpleX_eq_rootExp, e6RootExp_inv_cb]
        apply h3zornToMatrix_group_injective
        dsimp only
        rw [h3zornToMatrix_mul_group, h3zornToMatrix_mul_group, h3zornToMatrix_mul_group,
          h3zornToMatrix_e6RootExp, h3zornToMatrix_e6RootExp,
          h3zornToMatrix_e6RootExp, h3zornToMatrix_e6RootExp]
        have hEi2 : (sparseToMat (e6RootSparse (eSimpleIdx i))).map (Int.cast : ℤ → ℝ) *
            (sparseToMat (e6RootSparse (eSimpleIdx i))).map Int.cast = 0 := by
          have h2 := h3zornToMatrix_e6RootVec (eSimpleIdx i)
          have hsq : ((e6RootVec (eSimpleIdx i)).1 : Module.End ℝ (H3Zorn ℝ)) *
              (e6RootVec (eSimpleIdx i)).1 = 0 := by
            rw [← sq]; exact e6RootVec_sq_zero (eSimpleIdx i)
          have hmsq := congrArg h3zornToMatrix hsq
          rwa [_root_.map_mul, map_zero, h2] at hmsq
        have h_comm_r : (sparseToMat (e6RootSparse (eSimpleIdx i))).map (Int.cast : ℤ → ℝ) *
            (sparseToMat (e6RootSparse r)).map Int.cast -
            (sparseToMat (e6RootSparse r)).map Int.cast *
              (sparseToMat (e6RootSparse (eSimpleIdx i))).map Int.cast =
            (e6CommSign i r : ℝ) • (sparseToMat (e6RootSparse (e6CommRoot i r))).map Int.cast := by
          ext p q
          have hpq := congrArg (fun M : Matrix (Fin 27) (Fin 27) ℤ => (M p q : ℝ)) hm1
          simpa [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, e6SimpleESparse] using hpq
        have h_ere_r : (sparseToMat (e6RootSparse (eSimpleIdx i))).map (Int.cast : ℤ → ℝ) *
            ((sparseToMat (e6RootSparse r)).map Int.cast *
              (sparseToMat (e6RootSparse (eSimpleIdx i))).map Int.cast) = 0 := by
          ext p q
          have hpq := congrArg (fun M : Matrix (Fin 27) (Fin 27) ℤ => (M p q : ℝ)) hm2
          simpa [Matrix.mul_apply, e6SimpleESparse] using hpq
        have h_rrp_r : (sparseToMat (e6RootSparse r)).map (Int.cast : ℤ → ℝ) *
            (sparseToMat (e6RootSparse (e6CommRoot i r))).map Int.cast = 0 := by
          ext p q
          have hpq := congrArg (fun M : Matrix (Fin 27) (Fin 27) ℤ => (M p q : ℝ)) hm3
          simpa [Matrix.mul_apply] using hpq
        let Mi := (sparseToMat (e6RootSparse (eSimpleIdx i))).map (Int.cast : ℤ → ℝ)
        let Mr := (sparseToMat (e6RootSparse r)).map (Int.cast : ℤ → ℝ)
        let Mp := (sparseToMat (e6RootSparse (e6CommRoot i r))).map (Int.cast : ℤ → ℝ)
        change (1 + c • Mi) * (1 + a • Mr) * (1 + (-c) • Mi) =
          (1 + a • Mr) * (1 + ((e6CommSign i r : ℝ) * c * a) • Mp)
        have hLHS : (1 + c • Mi) * (1 + a • Mr) * (1 + (-c) • Mi) =
            1 + a • Mr + (c * a) • (Mi * Mr - Mr * Mi) := by
          have h1 : (c • Mi) * ((-c) • Mi) = 0 := by
            rw [Matrix.mul_smul, Matrix.smul_mul, hEi2, smul_zero, smul_zero]
          have h2 : (c * a) • (Mi * Mr) * ((-c) • Mi) = 0 := by
            rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h_ere_r, smul_zero, smul_zero]
          have h3 : (a • Mr) * ((-c) • Mi) = -((c * a) • (Mr * Mi)) := by
            rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← neg_smul]
            congr 1; ring
          have h4 : (1 + c • Mi) * (1 + a • Mr) =
              1 + c • Mi + a • Mr + (c * a) • (Mi * Mr) := by
            simp only [add_mul, mul_add, one_mul, mul_one, Matrix.mul_smul, Matrix.smul_mul,
              smul_smul]
            rw [show (a * c) • (Mi * Mr) = (c * a) • (Mi * Mr) by rw [mul_comm]]
            abel_nf
          rw [h4, mul_add, mul_one, add_mul, add_mul, add_mul, one_mul, h1, h2, h3]
          simp only [add_zero, neg_smul, smul_sub]
          abel
        have hRHS : (1 + a • Mr) * (1 + ((e6CommSign i r : ℝ) * c * a) • Mp) =
            1 + a • Mr + ((e6CommSign i r : ℝ) * c * a) • Mp := by
          simp only [add_mul, mul_add, one_mul, mul_one, Matrix.mul_smul, Matrix.smul_mul,
            smul_smul]
          rw [h_rrp_r, smul_zero, add_zero]
        rw [hLHS, hRHS, h_comm_r, smul_smul]
        rw [show c * a * (e6CommSign i r : ℝ) = (e6CommSign i r : ℝ) * c * a by ring]
      rw [heq]
      exact (e6PosUnipotentExcept i).mul_mem
        (Subgroup.subset_closure ⟨r, hpos, hne, a, rfl⟩)
        (Subgroup.subset_closure ⟨e6CommRoot i r, hp_pos, hp_ne, _, rfl⟩)
  · intro x y hx hy
    have hmul : e6SimpleX i c * (x * y) * (e6SimpleX i c)⁻¹ =
        (e6SimpleX i c * x * (e6SimpleX i c)⁻¹) * (e6SimpleX i c * y * (e6SimpleX i c)⁻¹) := by
      group
    rw [hmul]
    exact (e6PosUnipotentExcept i).mul_mem hx hy

private theorem e6PosUnipotent_factor_simpleX (i : Fin 6) (u : h3zornReducedStructureGroup)
    (hu : u ∈ e6PosUnipotent) :
    ∃ u_rest ∈ e6PosUnipotentExcept i, ∃ a : ℝ, u = u_rest * e6SimpleX i a := by
  let S : Set h3zornReducedStructureGroup :=
    { x | ∃ r : Fin 72, e6IsPosRoot r = true ∧ ∃ c : ℝ, x = e6RootExp r c }
  refine subgroup_closure_symm_induction S
    (by rintro _ ⟨r, hpos, c, rfl⟩; exact ⟨r, hpos, -c, e6RootExp_inv_cb r c⟩)
    (fun u => ∃ u_rest ∈ e6PosUnipotentExcept i, ∃ a : ℝ, u = u_rest * e6SimpleX i a)
    ⟨1, (e6PosUnipotentExcept i).one_mem, 0, by
      rw [e6SimpleX_eq_rootExp, e6RootExp_zero_cb, mul_one]⟩
    ?_ ?_ u hu
  · rintro _ ⟨r, hpos, c, rfl⟩
    by_cases hri : r = eSimpleIdx i
    · subst hri
      exact ⟨1, (e6PosUnipotentExcept i).one_mem, c, by rw [one_mul, e6SimpleX_eq_rootExp]⟩
    · exact ⟨e6RootExp r c, Subgroup.subset_closure ⟨r, hpos, hri, c, rfl⟩, 0, by
        rw [e6SimpleX_eq_rootExp, e6RootExp_zero_cb, mul_one]⟩
  · rintro _ _ ⟨u₁, hu₁, a₁, rfl⟩ ⟨u₂, hu₂, a₂, rfl⟩
    refine ⟨u₁ * (e6SimpleX i a₁ * u₂ * (e6SimpleX i a₁)⁻¹),
      (e6PosUnipotentExcept i).mul_mem hu₁ (e6SimpleX_conj_posUnipotentExcept i a₁ u₂ hu₂),
      a₁ + a₂, ?_⟩
    have hmul : e6SimpleX i a₁ * e6SimpleX i a₂ = e6SimpleX i (a₁ + a₂) := by
      rw [e6SimpleX_eq_rootExp, e6SimpleX_eq_rootExp, e6SimpleX_eq_rootExp, e6RootExp_mul_cb]
    calc (u₁ * e6SimpleX i a₁) * (u₂ * e6SimpleX i a₂)
        = (u₁ * (e6SimpleX i a₁ * u₂ * (e6SimpleX i a₁)⁻¹)) * (e6SimpleX i a₁ * e6SimpleX i a₂) := by
          group
      _ = (u₁ * (e6SimpleX i a₁ * u₂ * (e6SimpleX i a₁)⁻¹)) * e6SimpleX i (a₁ + a₂) := by
          rw [hmul]

private theorem e6WeylElt_one_conj_posUnipotentExcept (i : Fin 6)
    (u : h3zornReducedStructureGroup) (hu : u ∈ e6PosUnipotentExcept i) :
    e6WeylElt i 1 * u * (e6WeylElt i 1)⁻¹ ∈ e6PosUnipotent := by
  have hchk : ∀ r : Fin 72,
      (if e6IsPosRoot r && !(r == eSimpleIdx i) then
        e6IsPosRoot (e6WeylPerm i r)
      else true) = true :=
    allFin72Bool_sound _ (by fin_cases i <;> decide)
  let S : Set h3zornReducedStructureGroup :=
    { x | ∃ r : Fin 72, e6IsPosRoot r = true ∧ r ≠ eSimpleIdx i ∧ ∃ a : ℝ, x = e6RootExp r a }
  refine subgroup_closure_symm_induction S
    (by rintro _ ⟨r, hpos, hne, a, rfl⟩; exact ⟨r, hpos, hne, -a, e6RootExp_inv_cb r a⟩)
    (fun w => e6WeylElt i 1 * w * (e6WeylElt i 1)⁻¹ ∈ e6PosUnipotent)
    (by simp [e6PosUnipotent.one_mem])
    (by
      rintro _ ⟨r, hpos, hne, a, rfl⟩
      have hr := hchk r
      have hcond : (e6IsPosRoot r && !(r == eSimpleIdx i)) = true := by simp [hpos, hne]
      simp only [hcond, ↓reduceIte] at hr
      rw [e6WeylElt_one_conj_e6RootExp]
      exact Subgroup.subset_closure ⟨e6WeylPerm i r, hr, _, rfl⟩)
    (by
      intro x y hx hy
      have hmul : e6WeylElt i 1 * (x * y) * (e6WeylElt i 1)⁻¹ =
          (e6WeylElt i 1 * x * (e6WeylElt i 1)⁻¹) * (e6WeylElt i 1 * y * (e6WeylElt i 1)⁻¹) := by
        group
      rw [hmul]
      exact e6PosUnipotent.mul_mem hx hy)
    u hu

private theorem e6WeylElt_one_mul_simpleX_eq (i : Fin 6) (a : ℝ) (ha : a ≠ 0) :
    e6WeylElt i 1 * e6SimpleX i a =
      e6SimpleX i (-a⁻¹) * e6TorusElt i (-(Units.mk0 a ha)⁻¹) * e6SimpleY i a⁻¹ := by
  have hw_unfold : ∀ (s : ℝˣ) (v : H3Zorn ℝ),
      (e6WeylElt i s).1 v =
        (e6SimpleX i (s : ℝ)).1 ((e6SimpleY i (-((s⁻¹ : ℝˣ) : ℝ))).1
          ((e6SimpleX i (s : ℝ)).1 v)) := fun _ _ => rfl
  have h1s : -(((1 : ℝˣ)⁻¹ : ℝˣ) : ℝ) = -1 := by norm_num
  have h1r : ((1 : ℝˣ) : ℝ) = 1 := rfl
  have hs1 : (1 : ℝ) ≠ 0 := by norm_num
  have hbasis : ∀ k : Fin 27,
      (e6WeylElt i 1).1 ((e6SimpleX i a).1 (h3ZornBasis k)) =
        (e6SimpleX i (-a⁻¹)).1 ((e6TorusElt i (-(Units.mk0 a ha)⁻¹)).1
          ((e6SimpleY i a⁻¹).1 (h3ZornBasis k))) := by
    intro k
    rcases h3zornWeight_values_cb k i with hm1 | h0 | h1
    · have hF : (e6SimpleF i).1 (h3ZornBasis k) = 0 :=
        simpleF_kill_of_weight_nonpos_cb i k (Or.inr hm1)
      have hFE : (e6SimpleF i).1 ((e6SimpleE i).1 (h3ZornBasis k)) = h3ZornBasis k := by
        have hc := e6Simple_comm_apply_cb i (h3ZornBasis k)
        rw [hF, map_zero, zero_sub, e6SimpleH_apply_basis, hm1, Int.cast_neg, Int.cast_one] at hc
        change -((e6SimpleF i).1 ((e6SimpleE i).1 (h3ZornBasis k))) = (-1 : ℝ) • h3ZornBasis k at hc
        simpa using congrArg Neg.neg hc
      have hw_k : (e6WeylElt i 1).1 (h3ZornBasis k) = (e6SimpleE i).1 (h3ZornBasis k) := by
        rw [hw_unfold, h1r, h1s]
        have hloc := weyl_on_lowest_like_cb i 1 hs1 (h3ZornBasis k) hF hFE
        simpa [neg_inv] using hloc
      let u := (e6SimpleE i).1 (h3ZornBasis k)
      have hEu : (e6SimpleE i).1 u = 0 := e6SimpleE_sq_apply_cb i (h3ZornBasis k)
      have hEFu : (e6SimpleE i).1 ((e6SimpleF i).1 u) = u := by dsimp [u]; rw [hFE]
      have hw_u : (e6WeylElt i 1).1 u = -(h3ZornBasis k) := by
        rw [hw_unfold, h1r, h1s]
        have hloc := weyl_on_highest_like_cb i 1 hs1 u hEu hEFu
        simpa [u, hFE] using hloc
      have hL : (e6WeylElt i 1).1 ((e6SimpleX i a).1 (h3ZornBasis k)) =
          u + (-a) • h3ZornBasis k := by
        change (e6WeylElt i 1).1 (h3ZornBasis k + a • (e6SimpleE i).1 (h3ZornBasis k)) = _
        rw [map_add, map_smul, hw_k, hw_u]
        change u + a • (-h3ZornBasis k) = u + (-a) • h3ZornBasis k
        module
      have hR : (e6SimpleX i (-a⁻¹)).1 ((e6TorusElt i (-(Units.mk0 a ha)⁻¹)).1
          ((e6SimpleY i a⁻¹).1 (h3ZornBasis k))) = u + (-a) • h3ZornBasis k := by
        have hy : (e6SimpleY i a⁻¹).1 (h3ZornBasis k) = h3ZornBasis k := by
          change h3ZornBasis k + a⁻¹ • (e6SimpleF i).1 (h3ZornBasis k) = h3ZornBasis k
          rw [hF, smul_zero, add_zero]
        rw [hy, e6TorusElt_apply_basis, hm1, zpow_neg_one, Units.val_inv_eq_inv_val,
          Units.val_neg, Units.val_inv_eq_inv_val, Units.val_mk0, inv_neg, inv_inv]
        change (e6SimpleX i (-a⁻¹)).1 (((-a) : ℝ) • h3ZornBasis k) = u + (-a) • h3ZornBasis k
        rw [map_smul]
        change (-a) • (h3ZornBasis k + (-a⁻¹) • u) = u + (-a) • h3ZornBasis k
        rw [smul_add, smul_smul, show (-a) * (-a⁻¹) = 1 by field_simp [ha], one_smul]
        module
      rw [hL, hR]
    · have hE : (e6SimpleE i).1 (h3ZornBasis k) = 0 :=
        simpleE_kill_of_weight_nonneg_cb i k (Or.inl h0)
      have hF : (e6SimpleF i).1 (h3ZornBasis k) = 0 :=
        simpleF_kill_of_weight_nonpos_cb i k (Or.inl h0)
      have hx_a : (e6SimpleX i a).1 (h3ZornBasis k) = h3ZornBasis k := by
        change h3ZornBasis k + a • (e6SimpleE i).1 (h3ZornBasis k) = h3ZornBasis k
        rw [hE, smul_zero, add_zero]
      have hx_mi : (e6SimpleX i (-a⁻¹)).1 (h3ZornBasis k) = h3ZornBasis k := by
        change h3ZornBasis k + (-a⁻¹) • (e6SimpleE i).1 (h3ZornBasis k) = h3ZornBasis k
        rw [hE, smul_zero, add_zero]
      have hy_i : (e6SimpleY i a⁻¹).1 (h3ZornBasis k) = h3ZornBasis k := by
        change h3ZornBasis k + a⁻¹ • (e6SimpleF i).1 (h3ZornBasis k) = h3ZornBasis k
        rw [hF, smul_zero, add_zero]
      have hw0 : (e6WeylElt i 1).1 (h3ZornBasis k) = h3ZornBasis k := by
        rw [hw_unfold, h1r, h1s]
        have hx1 : (e6SimpleX i 1).1 (h3ZornBasis k) = h3ZornBasis k := by
          change h3ZornBasis k + (1 : ℝ) • (e6SimpleE i).1 (h3ZornBasis k) = _
          rw [hE, smul_zero, add_zero]
        have hy1 : (e6SimpleY i (-1)).1 (h3ZornBasis k) = h3ZornBasis k := by
          change h3ZornBasis k + (-1 : ℝ) • (e6SimpleF i).1 (h3ZornBasis k) = _
          rw [hF, smul_zero, add_zero]
        rw [hx1, hy1, hx1]
      rw [hx_a, hw0, hy_i, e6TorusElt_apply_basis, h0, zpow_zero, Units.val_one, one_smul, hx_mi]
    · have hE : (e6SimpleE i).1 (h3ZornBasis k) = 0 :=
        simpleE_kill_of_weight_nonneg_cb i k (Or.inr h1)
      have hEF : (e6SimpleE i).1 ((e6SimpleF i).1 (h3ZornBasis k)) = h3ZornBasis k := by
        have hc := e6Simple_comm_apply_cb i (h3ZornBasis k)
        rw [hE, map_zero, sub_zero, e6SimpleH_apply_basis, h1, Int.cast_one, one_smul] at hc
        exact hc
      have hw_k : (e6WeylElt i 1).1 (h3ZornBasis k) = -(e6SimpleF i).1 (h3ZornBasis k) := by
        rw [hw_unfold, h1r, h1s]
        have hloc := weyl_on_highest_like_cb i 1 hs1 (h3ZornBasis k) hE hEF
        simpa [neg_inv] using hloc
      have hx_a : (e6SimpleX i a).1 (h3ZornBasis k) = h3ZornBasis k := by
        change h3ZornBasis k + a • (e6SimpleE i).1 (h3ZornBasis k) = _
        rw [hE, smul_zero, add_zero]
      have hL : (e6WeylElt i 1).1 ((e6SimpleX i a).1 (h3ZornBasis k)) =
          -(e6SimpleF i).1 (h3ZornBasis k) := by
        rw [hx_a, hw_k]
      let u := (e6SimpleF i).1 (h3ZornBasis k)
      have hw_u : (e6SimpleE i).1 u = h3ZornBasis k := hEF
      have hR : (e6SimpleX i (-a⁻¹)).1 ((e6TorusElt i (-(Units.mk0 a ha)⁻¹)).1
          ((e6SimpleY i a⁻¹).1 (h3ZornBasis k))) = -u := by
        have hy : (e6SimpleY i a⁻¹).1 (h3ZornBasis k) = h3ZornBasis k + a⁻¹ • u := rfl
        rw [hy, map_add, map_smul, e6TorusElt_apply_basis, h1, zpow_one]
        have hu_wt : (e6TorusElt i (-(Units.mk0 a ha)⁻¹)).1 u = (-a) • u := by
          have hwt : u =
              ∑ m : Fin 27, ((h3zornToMatrix (e6SimpleF i).1) m k) • h3ZornBasis m := by
            rw [← h3ZornBasis.sum_repr u]
            refine Finset.sum_congr rfl fun m _ => ?_
            congr 1; exact (h3zornToMatrix_apply (e6SimpleF i).1 m k).symm
          have hchk_f : (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
              if h3zornWeight k i == 1 then
                (List.finRange 27).all (fun m =>
                  (sparseVal (e6SimpleFSparse i) m k == 0) || (h3zornWeight m i == -1))
              else true)) = true := by decide
          simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk_f
          have hfi := hchk_f i k
          have hcond : (h3zornWeight k i == 1) = true := by simp [h1]
          simp only [hcond, ↓reduceIte] at hfi
          simp only [List.all_eq_true, List.mem_finRange, Bool.or_eq_true, beq_iff_eq,
            true_implies] at hfi
          change (e6TorusElt i (-(Units.mk0 a ha)⁻¹)).1 u = (-a) • u
          rw [hwt, map_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_smul, e6TorusElt_apply_basis]
          by_cases hzm : sparseVal (e6SimpleFSparse i) m k = 0
          · have hmz : ((h3zornToMatrix (e6SimpleF i).1) m k) = 0 := by
              rw [h3zornToMatrix_e6SimpleF]; change ((sparseVal _ m k : ℤ) : ℝ) = 0
              rw [hzm, Int.cast_zero]
            rw [hmz, zero_smul, zero_smul, smul_zero]
          · have hwm : h3zornWeight m i = -1 := (hfi m).resolve_left hzm
            rw [hwm, zpow_neg_one, Units.val_inv_eq_inv_val, Units.val_neg,
              Units.val_inv_eq_inv_val, Units.val_mk0, inv_neg, inv_inv]
            change _ = (-a) • (((h3zornToMatrix (e6SimpleF i).1) m k) • h3ZornBasis m)
            rw [smul_comm]
        rw [hu_wt, Units.val_neg, Units.val_inv_eq_inv_val]
        have ha1 : (-(Units.mk0 a ha : ℝ)⁻¹) = -a⁻¹ := rfl
        have hx_k : (e6SimpleX i (-a⁻¹)).1 (h3ZornBasis k) = h3ZornBasis k := by
          change h3ZornBasis k + (-a⁻¹) • (e6SimpleE i).1 (h3ZornBasis k) = h3ZornBasis k
          rw [hE, smul_zero, add_zero]
        have hx_u : (e6SimpleX i (-a⁻¹)).1 u = u + (-a⁻¹) • h3ZornBasis k := by
          change u + (-a⁻¹) • (e6SimpleE i).1 u = _; rw [hw_u]
        rw [ha1, map_add, map_smul, map_smul, map_smul, hx_k, hx_u]
        rw [smul_smul, show a⁻¹ * (-a) = -1 by field_simp [ha]]
        module
      rw [hL, hR]
  have hmul_app : ∀ (A B : h3zornReducedStructureGroup) (v : H3Zorn ℝ),
      (A * B).1 v = A.1 (B.1 v) := fun _ _ _ => rfl
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply h3ZornBasis.ext
  intro k
  change (e6WeylElt i 1 * e6SimpleX i a).1 (h3ZornBasis k) =
    (e6SimpleX i (-a⁻¹) * e6TorusElt i (-(Units.mk0 a ha)⁻¹) * e6SimpleY i a⁻¹).1 (h3ZornBasis k)
  rw [hmul_app, hmul_app, hmul_app]
  exact hbasis k

private theorem e6Pos_or_neg_root :
    ∀ r : Fin 72, e6IsPosRoot r = true ∨ e6IsPosRoot (e6NegRoot r) = true := by
  have hchk := allFin72Bool_sound
    (fun r => e6IsPosRoot r || e6IsPosRoot (e6NegRoot r)) (by decide)
  intro r
  simpa [Bool.or_eq_true] using hchk r

private theorem e6WeylElt_one_conj_simpleX (i : Fin 6) (c : ℝ) :
    e6WeylElt i 1 * e6SimpleX i c * (e6WeylElt i 1)⁻¹ = e6SimpleY i (-c) := by
  have hchk : (List.finRange 6).all (fun i =>
      (e6WeylPerm i (eSimpleIdx i) == fSimpleIdx i) &&
      (e6WeylSign i (eSimpleIdx i) == -(fSimpleSign i))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, beq_iff_eq,
    true_implies] at hchk
  rw [e6SimpleX_eq_rootExp, e6WeylElt_one_conj_e6RootExp, (hchk i).1, (hchk i).2,
    e6SimpleY_eq_rootExp]
  congr 1
  simp only [Int.cast_neg]
  ring

private theorem e6WeylSubgroup_conj_root_coupled (w : h3zornReducedStructureGroup)
    (hw : w ∈ e6WeylSubgroup) :
    ∀ r : Fin 72, ∃ r' : Fin 72,
      (∃ s₁ : ℝ, (s₁ = 1 ∨ s₁ = -1) ∧
        ∀ c : ℝ, w⁻¹ * e6RootExp r c * w = e6RootExp r' (s₁ * c)) ∧
      (∃ s₂ : ℝ, (s₂ = 1 ∨ s₂ = -1) ∧
        ∀ c : ℝ, w⁻¹ * e6RootExp (e6NegRoot r) c * w = e6RootExp (e6NegRoot r') (s₂ * c)) := by
  have hneg_perm : ∀ j : Fin 6, ∀ r : Fin 72,
      e6WeylPerm j (e6NegRoot r) = e6NegRoot (e6WeylPerm j r) := by
    intro j
    have hchk := allFin72Bool_sound
      (fun r => e6WeylPerm j (e6NegRoot r) == e6NegRoot (e6WeylPerm j r))
      (by fin_cases j <;> decide)
    intro r; simpa [beq_iff_eq] using hchk r
  have hsign_pm : ∀ j : Fin 6, ∀ r : Fin 72,
      e6WeylSign j r = 1 ∨ e6WeylSign j r = -1 := by
    intro j
    have hchk := allFin72Bool_sound
      (fun r => (e6WeylSign j r == 1) || (e6WeylSign j r == -1))
      (by fin_cases j <;> decide)
    intro r; simpa [Bool.or_eq_true, beq_iff_eq] using hchk r
  let S : Set h3zornReducedStructureGroup :=
    { x | ∃ j : Fin 6, x = e6WeylElt j 1 ∨ x = (e6WeylElt j 1)⁻¹ }
  refine subgroup_closure_symm_induction S
    (by
      rintro _ ⟨j, rfl | rfl⟩
      · exact ⟨j, Or.inr rfl⟩
      · exact ⟨j, Or.inl (inv_inv _)⟩)
    (fun w => ∀ r : Fin 72, ∃ r' : Fin 72,
      (∃ s₁ : ℝ, (s₁ = 1 ∨ s₁ = -1) ∧
        ∀ c : ℝ, w⁻¹ * e6RootExp r c * w = e6RootExp r' (s₁ * c)) ∧
      (∃ s₂ : ℝ, (s₂ = 1 ∨ s₂ = -1) ∧
        ∀ c : ℝ, w⁻¹ * e6RootExp (e6NegRoot r) c * w = e6RootExp (e6NegRoot r') (s₂ * c)))
    ?_ ?_ ?_ w (by
      refine Subgroup.closure_mono ?_ hw
      rintro _ ⟨j, rfl⟩
      exact ⟨j, Or.inl rfl⟩)
  · intro r
    exact ⟨r, ⟨1, Or.inl rfl, fun c => by simp⟩, ⟨1, Or.inl rfl, fun c => by simp⟩⟩
  · rintro _ ⟨j, rfl | rfl⟩ r
    · have ht1_sq : e6TorusElt j (-1) * e6TorusElt j (-1) = 1 := by
        have h : (e6TorusElt j (-1))⁻¹ = e6TorusElt j (-1) := by
          rw [e6TorusElt_inv_cb]; congr 1
        calc e6TorusElt j (-1) * e6TorusElt j (-1)
            = e6TorusElt j (-1) * (e6TorusElt j (-1))⁻¹ := by rw [h]
          _ = 1 := mul_inv_cancel _
      have hwinv_left : (e6WeylElt j 1)⁻¹ = e6TorusElt j (-1) * e6WeylElt j 1 := by
        apply inv_eq_of_mul_eq_one_left
        rw [mul_assoc, e6WeylElt_one_mul_self, ht1_sq]
      have hw_from_inv : e6WeylElt j 1 = (e6WeylElt j 1)⁻¹ * e6TorusElt j (-1) := by
        rw [e6WeylElt_one_inv, mul_assoc, ht1_sq, mul_one]
      have hconj_inv : ∀ r₀ : Fin 72,
          ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ c : ℝ,
            (e6WeylElt j 1)⁻¹ * e6RootExp r₀ c * e6WeylElt j 1 =
              e6RootExp (e6WeylPerm j r₀) (s * c) := by
        intro r₀
        have hz_pm : ∀ z : ℤ, ((-1 : ℝ) ^ z) = 1 ∨ ((-1 : ℝ) ^ z) = -1 := by
          intro z
          rcases Int.even_or_odd z with ⟨k, rfl⟩ | ⟨k, rfl⟩
          · left
            rw [← two_mul, zpow_mul, show ((-1 : ℝ) ^ (2 : ℤ)) = 1 by norm_num, one_zpow]
          · right
            rw [zpow_add₀ (by norm_num), zpow_mul,
              show ((-1 : ℝ) ^ (2 : ℤ)) = 1 by norm_num, one_zpow, one_mul, zpow_one]
        rcases hz_pm (e6TorusRootExp j (e6WeylPerm j r₀)) with hp_t | hp_t
        · refine ⟨1 * (e6WeylSign j r₀ : ℝ), ?_, fun c => ?_⟩
          · rcases hsign_pm j r₀ with h | h <;> simp [h]
          · have hassoc : (e6WeylElt j 1)⁻¹ * e6RootExp r₀ c * e6WeylElt j 1 =
                e6TorusElt j (-1) * (e6WeylElt j 1 * e6RootExp r₀ c * (e6WeylElt j 1)⁻¹) *
                  (e6TorusElt j (-1))⁻¹ := by
              have hinvt : (e6TorusElt j (-1))⁻¹ = e6TorusElt j (-1) := by
                rw [e6TorusElt_inv_cb]; congr 1
              calc (e6WeylElt j 1)⁻¹ * e6RootExp r₀ c * e6WeylElt j 1
                  = (e6TorusElt j (-1) * e6WeylElt j 1) * e6RootExp r₀ c *
                      ((e6WeylElt j 1)⁻¹ * e6TorusElt j (-1)) := by
                    conv_lhs => lhs; lhs; rw [hwinv_left]
                    conv_lhs => rhs; rw [hw_from_inv]
                _ = e6TorusElt j (-1) * (e6WeylElt j 1 * e6RootExp r₀ c * (e6WeylElt j 1)⁻¹) *
                      (e6TorusElt j (-1))⁻¹ := by
                    rw [hinvt]; group
            rw [hassoc, e6WeylElt_one_conj_e6RootExp, e6TorusElt_conj_e6RootExp]
            change e6RootExp (e6WeylPerm j r₀)
                ((-1 : ℝ) ^ e6TorusRootExp j (e6WeylPerm j r₀) * ((e6WeylSign j r₀ : ℝ) * c)) = _
            rw [hp_t]
            congr 1; ring
        · refine ⟨(-1) * (e6WeylSign j r₀ : ℝ), ?_, fun c => ?_⟩
          · rcases hsign_pm j r₀ with h | h <;> simp [h]
          · have hassoc : (e6WeylElt j 1)⁻¹ * e6RootExp r₀ c * e6WeylElt j 1 =
                e6TorusElt j (-1) * (e6WeylElt j 1 * e6RootExp r₀ c * (e6WeylElt j 1)⁻¹) *
                  (e6TorusElt j (-1))⁻¹ := by
              have hinvt : (e6TorusElt j (-1))⁻¹ = e6TorusElt j (-1) := by
                rw [e6TorusElt_inv_cb]; congr 1
              calc (e6WeylElt j 1)⁻¹ * e6RootExp r₀ c * e6WeylElt j 1
                  = (e6TorusElt j (-1) * e6WeylElt j 1) * e6RootExp r₀ c *
                      ((e6WeylElt j 1)⁻¹ * e6TorusElt j (-1)) := by
                    conv_lhs => lhs; lhs; rw [hwinv_left]
                    conv_lhs => rhs; rw [hw_from_inv]
                _ = e6TorusElt j (-1) * (e6WeylElt j 1 * e6RootExp r₀ c * (e6WeylElt j 1)⁻¹) *
                      (e6TorusElt j (-1))⁻¹ := by
                    rw [hinvt]; group
            rw [hassoc, e6WeylElt_one_conj_e6RootExp, e6TorusElt_conj_e6RootExp]
            change e6RootExp (e6WeylPerm j r₀)
                ((-1 : ℝ) ^ e6TorusRootExp j (e6WeylPerm j r₀) * ((e6WeylSign j r₀ : ℝ) * c)) = _
            rw [hp_t]
            congr 1; ring
      obtain ⟨s₁, hs₁, hrx₁⟩ := hconj_inv r
      obtain ⟨s₂, hs₂, hrn₂⟩ := hconj_inv (e6NegRoot r)
      refine ⟨e6WeylPerm j r, ⟨s₁, hs₁, hrx₁⟩, ⟨s₂, hs₂, fun c => ?_⟩⟩
      rw [← hneg_perm j r]
      exact hrn₂ c
    · refine ⟨e6WeylPerm j r, ⟨(e6WeylSign j r : ℝ), ?_, fun c => ?_⟩,
        ⟨(e6WeylSign j (e6NegRoot r) : ℝ), ?_, fun c => ?_⟩⟩
      · rcases hsign_pm j r with h | h <;> [left; right] <;> simp [h]
      · simp only [inv_inv]
        exact e6WeylElt_one_conj_e6RootExp j r c
      · rcases hsign_pm j (e6NegRoot r) with h | h <;> [left; right] <;> simp [h]
      · simp only [inv_inv, ← hneg_perm j r]
        exact e6WeylElt_one_conj_e6RootExp j (e6NegRoot r) c
  · intro x y hx hy r
    obtain ⟨r₁, ⟨s₁, hs₁, hrx₁⟩, ⟨t₁, ht₁, hrn₁⟩⟩ := hx r
    obtain ⟨r₂, ⟨s₂, hs₂, hrx₂⟩, ⟨t₂, ht₂, hrn₂⟩⟩ := hy r₁
    refine ⟨r₂, ⟨s₂ * s₁, ?_, fun c => ?_⟩, ⟨t₂ * t₁, ?_, fun c => ?_⟩⟩
    · rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> norm_num
    · have hmul : (x * y)⁻¹ * e6RootExp r c * (x * y) =
          y⁻¹ * (x⁻¹ * e6RootExp r c * x) * y := by group
      rw [hmul, hrx₁ c, hrx₂ (s₁ * c), mul_assoc]
    · rcases ht₁ with rfl | rfl <;> rcases ht₂ with rfl | rfl <;> norm_num
    · have hmul : (x * y)⁻¹ * e6RootExp (e6NegRoot r) c * (x * y) =
          y⁻¹ * (x⁻¹ * e6RootExp (e6NegRoot r) c * x) * y := by group
      rw [hmul, hrn₁ c, hrn₂ (t₁ * c), mul_assoc]

/-- **Native Signed Bruhat Decomposition (`G = B * W * B`)** inside `Str₀(H₃(𝕆_s))`. -/
theorem e6Bruhat_decomposition (g : h3zornReducedStructureGroup) :
    ∃ b₁ ∈ e6Borel, ∃ w ∈ e6WeylSubgroup, ∃ b₂ ∈ e6Borel, g = b₁ * w * b₂ := by
  have hneg_simp : (List.finRange 6).all (fun i =>
      e6NegRoot (eSimpleIdx i) == fSimpleIdx i) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at hneg_simp
  let InBWB (z : h3zornReducedStructureGroup) : Prop :=
    ∃ b₁ ∈ e6Borel, ∃ w ∈ e6WeylSubgroup, ∃ b₂ ∈ e6Borel, z = b₁ * w * b₂
  have hx_mul : ∀ (i : Fin 6) (c : ℝ) (z : h3zornReducedStructureGroup),
      InBWB z → InBWB (e6SimpleX i c * z) := by
    rintro i c _ ⟨b₁, hb₁, w, hw, b₂, hb₂, rfl⟩
    have hxc : e6SimpleX i c ∈ e6Borel := by
      have hpos : e6IsPosRoot (eSimpleIdx i) = true := by
        have hchk : (List.finRange 6).all (fun i => e6IsPosRoot (eSimpleIdx i)) = true := by decide
        simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
        exact hchk i
      rw [e6SimpleX_eq_rootExp]
      exact Subgroup.subset_closure (Set.mem_union_right _
        (Subgroup.subset_closure ⟨eSimpleIdx i, hpos, c, rfl⟩))
    exact ⟨e6SimpleX i c * b₁, e6Borel.mul_mem hxc hb₁, w, hw, b₂, hb₂, by group⟩
  have hw_mul : ∀ (i : Fin 6) (z : h3zornReducedStructureGroup),
      InBWB z → InBWB (e6WeylElt i 1 * z) := by
    rintro i _ ⟨b₁, hb₁, w, hw, b₂, hb₂, rfl⟩
    obtain ⟨t, ht, u, hu, rfl⟩ := (e6Borel_eq_torus_mul_posUnipotent b₁).mp hb₁
    obtain ⟨u_rest, hu_rest, a, rfl⟩ := e6PosUnipotent_factor_simpleX i u hu
    have hwt : e6WeylElt i 1 * t * (e6WeylElt i 1)⁻¹ ∈ e6Borel :=
      Subgroup.subset_closure (Set.mem_union_left _ (e6WeylElt_one_conj_e6Torus i t ht))
    have hwu : e6WeylElt i 1 * u_rest * (e6WeylElt i 1)⁻¹ ∈ e6Borel :=
      Subgroup.subset_closure (Set.mem_union_right _
        (e6WeylElt_one_conj_posUnipotentExcept i u_rest hu_rest))
    let b_tu := (e6WeylElt i 1 * t * (e6WeylElt i 1)⁻¹) *
      (e6WeylElt i 1 * u_rest * (e6WeylElt i 1)⁻¹)
    have hbtu_mem : b_tu ∈ e6Borel := e6Borel.mul_mem hwt hwu
    have hpref : e6WeylElt i 1 * (t * (u_rest * e6SimpleX i a) * w * b₂) =
        b_tu * (e6WeylElt i 1 * e6SimpleX i a * w) * b₂ := by
      dsimp [b_tu]; group
    obtain ⟨r', ⟨s₁, _, hrx₁⟩, ⟨s₂, _, hrn₂⟩⟩ :=
      e6WeylSubgroup_conj_root_coupled w hw (eSimpleIdx i)
    by_cases hpos : e6IsPosRoot r' = true
    · refine ⟨b_tu, hbtu_mem, e6WeylElt i 1 * w,
        e6WeylSubgroup.mul_mem (Subgroup.subset_closure ⟨i, rfl⟩) hw,
        (w⁻¹ * e6SimpleX i a * w) * b₂, e6Borel.mul_mem ?_ hb₂, ?_⟩
      · rw [e6SimpleX_eq_rootExp, hrx₁ a]
        exact Subgroup.subset_closure (Set.mem_union_right _
          (Subgroup.subset_closure ⟨r', hpos, _, rfl⟩))
      · rw [hpref]; group
    · by_cases ha : a = 0
      · subst ha
        have hx0 : e6SimpleX i 0 = 1 := by rw [e6SimpleX_eq_rootExp, e6RootExp_zero_cb]
        refine ⟨b_tu, hbtu_mem, e6WeylElt i 1 * w,
          e6WeylSubgroup.mul_mem (Subgroup.subset_closure ⟨i, rfl⟩) hw, b₂, hb₂, ?_⟩
        rw [hpref, hx0, mul_one]
      · have hx_b : e6SimpleX i (-a⁻¹) ∈ e6Borel := by
          have hps : e6IsPosRoot (eSimpleIdx i) = true := by
            have hchk : (List.finRange 6).all (fun i => e6IsPosRoot (eSimpleIdx i)) = true := by
              decide
            simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
            exact hchk i
          rw [e6SimpleX_eq_rootExp]
          exact Subgroup.subset_closure (Set.mem_union_right _
            (Subgroup.subset_closure ⟨eSimpleIdx i, hps, -a⁻¹, rfl⟩))
        have ht_b : e6TorusElt i (-(Units.mk0 a ha)⁻¹) ∈ e6Borel :=
          Subgroup.subset_closure (Set.mem_union_left _ (Subgroup.subset_closure ⟨i, _, rfl⟩))
        have hy_w : w⁻¹ * e6SimpleY i a⁻¹ * w ∈ e6Borel := by
          rw [e6SimpleY_eq_rootExp, ← hneg_simp i]
          rw [hrn₂ ((fSimpleSign i : ℝ) * a⁻¹)]
          have hpos_nr : e6IsPosRoot (e6NegRoot r') = true :=
            (e6Pos_or_neg_root r').resolve_left hpos
          exact Subgroup.subset_closure (Set.mem_union_right _
            (Subgroup.subset_closure ⟨e6NegRoot r', hpos_nr, _, rfl⟩))
        refine ⟨b_tu * (e6SimpleX i (-a⁻¹) * e6TorusElt i (-(Units.mk0 a ha)⁻¹)),
          e6Borel.mul_mem hbtu_mem (e6Borel.mul_mem hx_b ht_b),
          w, hw, (w⁻¹ * e6SimpleY i a⁻¹ * w) * b₂, e6Borel.mul_mem hy_w hb₂, ?_⟩
        rw [hpref, e6WeylElt_one_mul_simpleX_eq i a ha]
        group
  have hwinv_mul : ∀ (i : Fin 6) (z : h3zornReducedStructureGroup),
      InBWB z → InBWB ((e6WeylElt i 1)⁻¹ * z) := by
    intro i z hz
    have ht1_sq : e6TorusElt i (-1) * e6TorusElt i (-1) = 1 := by
      have h : (e6TorusElt i (-1))⁻¹ = e6TorusElt i (-1) := by rw [e6TorusElt_inv_cb]; congr 1
      calc e6TorusElt i (-1) * e6TorusElt i (-1)
          = e6TorusElt i (-1) * (e6TorusElt i (-1))⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel _
    have hwinv_left : (e6WeylElt i 1)⁻¹ = e6TorusElt i (-1) * e6WeylElt i 1 := by
      apply inv_eq_of_mul_eq_one_left
      rw [mul_assoc, e6WeylElt_one_mul_self, ht1_sq]
    rw [hwinv_left, mul_assoc]
    obtain ⟨b₁, hb₁, w, hw, b₂, hb₂, hzw⟩ := hw_mul i z hz
    have ht_b : e6TorusElt i (-1) ∈ e6Borel :=
      Subgroup.subset_closure (Set.mem_union_left _ (Subgroup.subset_closure ⟨i, -1, rfl⟩))
    exact ⟨e6TorusElt i (-1) * b₁, e6Borel.mul_mem ht_b hb₁, w, hw, b₂, hb₂, by rw [hzw]; group⟩
  have hy_mul : ∀ (i : Fin 6) (c : ℝ) (z : h3zornReducedStructureGroup),
      InBWB z → InBWB (e6SimpleY i c * z) := by
    intro i c z hz
    have hy_eq : e6SimpleY i c = e6WeylElt i 1 * e6SimpleX i (-c) * (e6WeylElt i 1)⁻¹ := by
      rw [e6WeylElt_one_conj_simpleX, neg_neg]
    rw [hy_eq, mul_assoc, mul_assoc]
    exact hw_mul i _ (hx_mul i (-c) _ (hwinv_mul i z hz))
  have hg_sc : g ∈ e6SimpleClosure := by
    rw [← e6ChevalleySubgroup_eq_simpleClosure, e6ChevalleySubgroup_eq_top]
    trivial
  let S_sc : Set h3zornReducedStructureGroup :=
    { x | ∃ (i : Fin 6) (c : ℝ), x = e6SimpleX i c } ∪
      { x | ∃ (i : Fin 6) (c : ℝ), x = e6SimpleY i c }
  have hact : ∀ x ∈ e6SimpleClosure, ∀ z, InBWB z → InBWB (x * z) := by
    refine subgroup_closure_symm_induction S_sc ?_ (fun x => ∀ z, InBWB z → InBWB (x * z))
      (fun z hz => by simpa using hz) ?_ ?_
    · rintro _ (⟨i, c, rfl⟩ | ⟨i, c, rfl⟩)
      · left; exact ⟨i, -c, by rw [e6SimpleX_eq_rootExp, e6RootExp_inv_cb, e6SimpleX_eq_rootExp]⟩
      · right; refine ⟨i, -c, ?_⟩
        rw [e6SimpleY_eq_rootExp, e6RootExp_inv_cb, e6SimpleY_eq_rootExp]
        congr 1; ring
    · rintro _ (⟨i, c, rfl⟩ | ⟨i, c, rfl⟩) z hz
      · exact hx_mul i c z hz
      · exact hy_mul i c z hz
    · intro x y hx hy z hz
      rw [mul_assoc]
      exact hx _ (hy z hz)
  have h1 : InBWB 1 := ⟨1, e6Borel.one_mem, 1, e6WeylSubgroup.one_mem, 1, e6Borel.one_mem, by simp⟩
  dsimp only [InBWB] at hact
  have hres := hact g hg_sc 1 h1
  rw [mul_one] at hres
  exact hres

end PartCNativeBruhat

end InfoGeometry.Algebra


