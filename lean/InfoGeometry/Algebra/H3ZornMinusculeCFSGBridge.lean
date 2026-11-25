/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornE6RootSystem
import InfoGeometry.Algebra.H3ZornStructureGroup
import InfoGeometry.Exceptional.CFSGPort.ChevalleyWeyl
import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootGroupsTorus

/-!
# Minuscule 27D & Adjoint 78D Bridge Between `H3Zorn ℝ` (`Str₀(H₃(𝕆_s))`) and `CFSGPort.Chevalley .E6`

Connects the native split Albert Jordan algebra `H3Zorn ℝ` (`E₆(6) = Str₀(H₃(𝕆_s))` and
`𝔢₆(6) = h3zornCubicStabilizer`) with the `CFSGPort.Chevalley` Chevalley–Steinberg layer:

1. **Square-zero exponential theorem**: any `X ∈ h3zornCubicStabilizer` with `X.1 ^ 2 = 0`
   exponentiates to `1 + c • X.1 ∈ h3zornReducedStructureGroup ≤ StructureGroup ℝ (H3Zorn ℝ)`.
2. **All 72 root subgroups & Chevalley group**: injective homomorphisms
   `h3zornRootSubgroupHom (r : Fin 72) : Multiplicative ℝ →* h3zornReducedStructureGroup`
   and the generated subgroup `h3zornChevalleyE6 ≤ h3zornReducedStructureGroup`.
3. **Weyl & torus elements**: `h3zornWeylElt i t` satisfying all E₆ Coxeter braid and
   commutation relations, and `h3zornTorusElt i t` acting diagonally on `h3ZornBasis k` by
   `t ^ (h3zornWeight k i)`.
4. **27D Minuscule weight alignment**: explicit `Equiv.Perm (Fin 27)` aligning
   `h3zornWeight` with the 27 weights decoded from `CFSGPort` minuscule `e6Data.weights`.
5. **78D Adjoint bridge**: `h3zornChevalleyEquiv : RootModule .E6 ℝ ≃ₗ[ℝ] h3zornCubicStabilizer`
   mapping `hVec .E6 ℝ i ↦ e6SimpleH i` and `rootVec .E6 ℝ (e6RootCoord r) ↦ e6RootVec r`,
   intertwining `CFSGPort.Chevalley.torusElt .E6 ℝ i t` with `h3zornAdjointAction (h3zornTorusElt i t)`,
   and satisfying the exact degree-2 adjoint exponential law for `h3zornSimpleX i c`
   (noting that `CFSGPort.Chevalley.xOp` uses unsigned `(τ.cartan j i).natAbs` on `hVec j`,
   whereas the signed adjoint representation on `h3zornCubicStabilizer` uses signed
   `Tag.cartan .E6 j i`).
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Exceptional.CFSGPort.Chevalley

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

section ScalarHelpers

private theorem sqZero_cubic_scalar_kill {a b c : ℝ}
    (h1 : a + b + c = 0) (hm1 : a - b + c = 0) (ha : a = 0) :
    b = 0 ∧ c = 0 := by
  have hsum : a + c = 0 := by linarith [h1, hm1]
  have hc : c = 0 := by linarith [hsum, ha]
  have hb : b = 0 := by linarith [h1, hc, ha]
  exact ⟨hb, hc⟩

private theorem normCubic_line_coeffs_zero (n c : ℝ) :
    n + c * 0 + c ^ 2 * 0 + c ^ 3 * 0 = n := by ring

private theorem mul_neg_self_eq_neg_sq (c : ℝ) : c * (-c) = -(c ^ 2) := by ring

private theorem zpow_neg_mul_self (t : ℝˣ) (a : ℤ) :
    ((t : ℝ) ^ (-a)) * ((t : ℝ) ^ a) = 1 := by
  have ht : (t : ℝ) ≠ 0 := t.ne_zero
  rw [← zpow_add₀ ht, neg_add_cancel, zpow_zero]

private theorem zpow_neg_mul_add (t : ℝˣ) (a b : ℤ) :
    ((t : ℝ) ^ (-a)) * ((t : ℝ) ^ (a + b)) = (t : ℝ) ^ b := by
  have ht : (t : ℝ) ≠ 0 := t.ne_zero
  rw [← zpow_add₀ ht]
  congr 1
  omega

private theorem two_mul_half_sq (c : ℝ) : -((c : ℝ) ^ 2) = (c ^ 2 / 2) * (-2 : ℝ) := by ring

private theorem unit_neg_inv_mul (t : ℝˣ) : -(-(t⁻¹ : ℝˣ) : ℝ) * (t : ℝ) = 1 := by
  have ht : (t : ℝ) ≠ 0 := t.ne_zero
  rw [neg_neg, Units.val_inv_eq_inv_val, inv_mul_cancel₀ ht]

private theorem neg_neg_inv_val (t : ℝˣ) : -(-((t⁻¹ : ℝˣ) : ℝ)) = ((t⁻¹ : ℝˣ) : ℝ) := by ring

private theorem neg_inv_val_neg_one : (-(((-1 : ℝˣ)⁻¹ : ℝˣ) : ℝ)) = 1 := by norm_num

private theorem neg_neg_one_val_mul (t : ℝˣ) : (-1 : ℝ) * (-(t⁻¹ : ℝˣ) : ℝ) = ((t⁻¹ : ℝˣ) : ℝ) := by
  ring

end ScalarHelpers

section SquareZeroExponential

/-- Operator exponential `1 + c • X` for `X ∈ h3zornCubicStabilizer`. -/
def sqZeroExpEnd (X : h3zornCubicStabilizer) (c : ℝ) : Module.End ℝ (H3Zorn ℝ) :=
  (1 : Module.End ℝ (H3Zorn ℝ)) + c • (X.1 : Module.End ℝ (H3Zorn ℝ))

theorem sqZeroExpEnd_apply (X : h3zornCubicStabilizer) (c : ℝ) (x : H3Zorn ℝ) :
    sqZeroExpEnd X c x = x + c • X.1 x := by
  simp [sqZeroExpEnd]

theorem sqZeroExpEnd_zero (X : h3zornCubicStabilizer) :
    sqZeroExpEnd X 0 = (1 : Module.End ℝ (H3Zorn ℝ)) := by
  simp [sqZeroExpEnd]

theorem sqZeroExpEnd_mul (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (a b : ℝ) :
    sqZeroExpEnd X a * sqZeroExpEnd X b = sqZeroExpEnd X (a + b) := by
  dsimp [sqZeroExpEnd]
  have hxx : (X.1 : Module.End ℝ (H3Zorn ℝ)) * (X.1 : Module.End ℝ (H3Zorn ℝ)) = 0 := by
    simpa [sq] using hsq
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    hxx, smul_zero, add_zero]
  rw [add_smul, add_assoc]

/-- Linear equivalence `exp(c X) = 1 + c • X` on `H3Zorn ℝ` for square-zero `X`. -/
def sqZeroExpEquiv (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ :=
  LinearEquiv.ofLinearMap
    (sqZeroExpEnd X c)
    (sqZeroExpEnd X (-c))
    (by
      change sqZeroExpEnd X c * sqZeroExpEnd X (-c) = 1
      rw [sqZeroExpEnd_mul X hsq, add_neg_cancel, sqZeroExpEnd_zero])
    (by
      change sqZeroExpEnd X (-c) * sqZeroExpEnd X c = 1
      rw [sqZeroExpEnd_mul X hsq, neg_add_cancel, sqZeroExpEnd_zero])

@[simp] theorem sqZeroExpEquiv_toLinearMap (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    (sqZeroExpEquiv X hsq c).toLinearMap = sqZeroExpEnd X c := rfl

@[simp] theorem sqZeroExpEquiv_symm_toLinearMap (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    (sqZeroExpEquiv X hsq c).symm.toLinearMap = sqZeroExpEnd X (-c) := rfl

@[simp] theorem sqZeroExpEquiv_apply (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) (x : H3Zorn ℝ) :
    sqZeroExpEquiv X hsq c x = x + c • X.1 x :=
  sqZeroExpEnd_apply X c x

theorem sqZeroExp_mem_reducedStructureGroup (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    sqZeroExpEquiv X hsq c ∈ h3zornReducedStructureGroup := by
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
  rw [sqZeroExpEquiv_apply, normCubic_line, htr x, hcross_zero, hnorm_y]
  exact normCubic_line_coeffs_zero (normCubic x) c

/-- Group element `exp(c X)` inside `h3zornReducedStructureGroup` (`Str₀(H₃(𝕆_s))`). -/
def sqZeroExp (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    h3zornReducedStructureGroup :=
  ⟨sqZeroExpEquiv X hsq c, sqZeroExp_mem_reducedStructureGroup X hsq c⟩

@[simp] theorem sqZeroExp_coe (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (c : ℝ) :
    ((sqZeroExp X hsq c).1 : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) = sqZeroExpEquiv X hsq c := rfl

theorem sqZeroExp_zero (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) :
    sqZeroExp X hsq 0 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact sqZeroExpEnd_zero X

theorem sqZeroExp_mul (X : h3zornCubicStabilizer)
    (hsq : (X.1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0) (a b : ℝ) :
    sqZeroExp X hsq a * sqZeroExp X hsq b = sqZeroExp X hsq (a + b) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact sqZeroExpEnd_mul X hsq a b

end SquareZeroExponential

section RootSubgroupsAndChevalleyGroup

/-- One-parameter root subgroup homomorphism `ℝ⁺ →* Str₀(H₃(𝕆_s))` for each of the 72 E₆ roots. -/
def h3zornRootSubgroupHom (r : Fin 72) :
    Multiplicative ℝ →* h3zornReducedStructureGroup where
  toFun x := sqZeroExp (e6RootVec r) (e6RootVec_sq_zero r) (Multiplicative.toAdd x)
  map_one' := sqZeroExp_zero (e6RootVec r) (e6RootVec_sq_zero r)
  map_mul' x y := by
    simp only [toAdd_mul]
    exact (sqZeroExp_mul (e6RootVec r) (e6RootVec_sq_zero r) _ _).symm

theorem h3zornRootSubgroupHom_injective (r : Fin 72) :
    Function.Injective (h3zornRootSubgroupHom r) := by
  intro x y hxy
  apply Multiplicative.toAdd.injective
  by_contra hne
  have hsub : Multiplicative.toAdd x - Multiplicative.toAdd y ≠ 0 := sub_ne_zero.mpr hne
  have hlin : (h3zornRootSubgroupHom r x).1.toLinearMap =
      (h3zornRootSubgroupHom r y).1.toLinearMap :=
    congrArg (fun g : h3zornReducedStructureGroup => g.1.toLinearMap) hxy
  have hdiff : (Multiplicative.toAdd x - Multiplicative.toAdd y) •
      (e6RootVec r).1 = (0 : Module.End ℝ (H3Zorn ℝ)) := by
    have h0 := sub_eq_zero.mpr hlin
    simpa [h3zornRootSubgroupHom, sqZeroExpEnd, sub_smul] using h0
  have hz := (smul_eq_zero.mp hdiff).resolve_left hsub
  exact e6RootVec_ne_zero r (Subtype.ext hz)

/-- The E₆ Chevalley subgroup of `Str₀(H₃(𝕆_s))` generated by all 72 root subgroups. -/
def h3zornChevalleyE6 : Subgroup h3zornReducedStructureGroup :=
  Subgroup.closure
    (Set.range fun p : Fin 72 × ℝ => h3zornRootSubgroupHom p.1 (Multiplicative.ofAdd p.2))

theorem h3zornChevalleyE6_le_reducedStructureGroup :
    h3zornChevalleyE6 ≤ (⊤ : Subgroup h3zornReducedStructureGroup) :=
  le_top

theorem h3zornChevalleyE6_le_StructureGroup_comap :
    h3zornChevalleyE6 ≤ (StructureGroup ℝ (H3Zorn ℝ)).comap h3zornReducedStructureGroup.subtype :=
  fun g _ => h3zorn_similitude_imp_mem_StructureGroup g.1 1 (fun x => by simpa using g.2 x)

/-- Simple positive root element `x_i(c) = exp(c • E_i) ∈ Str₀(H₃(𝕆_s))`. -/
def h3zornSimpleX (i : Fin 6) (c : ℝ) : h3zornReducedStructureGroup :=
  sqZeroExp (e6RootVec (eSimpleIdx i)) (e6RootVec_sq_zero (eSimpleIdx i)) c

theorem e6SimpleF_sq_zero (i : Fin 6) :
    ((e6SimpleF i).1 : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0 := by
  have hsq := e6RootVec_sq_zero (fSimpleIdx i)
  rw [sq] at hsq
  change ((fSimpleSign i : ℝ) • (e6RootVec (fSimpleIdx i)).1) ^ 2 = 0
  rw [sq, smul_mul_assoc, mul_smul_comm, smul_smul, hsq, smul_zero]

/-- Simple negative root element `y_i(c) = exp(c • F_i) ∈ Str₀(H₃(𝕆_s))`. -/
def h3zornSimpleY (i : Fin 6) (c : ℝ) : h3zornReducedStructureGroup :=
  sqZeroExp (e6SimpleF i) (e6SimpleF_sq_zero i) c

theorem h3zornSimpleX_mem_chevalleyE6 (i : Fin 6) (c : ℝ) :
    h3zornSimpleX i c ∈ h3zornChevalleyE6 :=
  Subgroup.subset_closure ⟨(eSimpleIdx i, c), rfl⟩

theorem h3zornSimpleY_mem_chevalleyE6 (i : Fin 6) (c : ℝ) :
    h3zornSimpleY i c ∈ h3zornChevalleyE6 := by
  have hmem : h3zornRootSubgroupHom (fSimpleIdx i)
      (Multiplicative.ofAdd ((fSimpleSign i : ℝ) * c)) ∈ h3zornChevalleyE6 :=
    Subgroup.subset_closure ⟨(fSimpleIdx i, (fSimpleSign i : ℝ) * c), rfl⟩
  have heq : h3zornSimpleY i c =
      h3zornRootSubgroupHom (fSimpleIdx i) (Multiplicative.ofAdd ((fSimpleSign i : ℝ) * c)) := by
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    change (1 : Module.End ℝ (H3Zorn ℝ)) + c • ((fSimpleSign i : ℝ) • (e6RootVec (fSimpleIdx i)).1) =
      (1 : Module.End ℝ (H3Zorn ℝ)) + ((fSimpleSign i : ℝ) * c) • (e6RootVec (fSimpleIdx i)).1
    rw [smul_smul, mul_comm]
  rwa [heq]

end RootSubgroupsAndChevalleyGroup

section WeylAndTorus

/-- Weyl element `w_i(t) = x_i(t) y_i(-t⁻¹) x_i(t) ∈ h3zornChevalleyE6`. -/
def h3zornWeylElt (i : Fin 6) (t : ℝˣ) : h3zornReducedStructureGroup :=
  h3zornSimpleX i t * h3zornSimpleY i (-(t⁻¹ : ℝˣ)) * h3zornSimpleX i t

theorem h3zornWeylElt_mem_chevalleyE6 (i : Fin 6) (t : ℝˣ) :
    h3zornWeylElt i t ∈ h3zornChevalleyE6 :=
  Subgroup.mul_mem _
    (Subgroup.mul_mem _ (h3zornSimpleX_mem_chevalleyE6 i t)
      (h3zornSimpleY_mem_chevalleyE6 i _))
    (h3zornSimpleX_mem_chevalleyE6 i t)

private def sparseId27 : SparseMat27 :=
  (List.finRange 27).map fun i => (i, i, 1)

private theorem sparseToMat_sparseId27 :
    sparseToMat sparseId27 = (1 : Matrix (Fin 27) (Fin 27) ℤ) := by
  ext i j
  change sparseVal ((List.finRange 27).map fun k => (k, k, 1)) i j = if i = j then 1 else 0
  have hsingle : ∀ (l : List (Fin 27)) (hl : l.Nodup),
      sparseVal (l.map fun k => (k, k, 1)) i j =
        if i = j ∧ i ∈ l then 1 else 0 := by
    intro l hl
    induction l with
    | nil => simp [sparseVal]
    | cons a l ih =>
      rcases List.nodup_cons.mp hl with ⟨ha, hl'⟩
      simp only [List.map_cons, sparseVal, ih hl', List.mem_cons]
      by_cases hai : a = i <;> by_cases haj : a = j
      · subst hai
        subst haj
        simp [ha]
      · have hij : i ≠ j := fun h => haj (hai.trans h)
        have hba : (a == i && a == j) = false := by simp [beq_false_of_ne haj]
        simp [hba, hij]
      · have hba : (a == i && a == j) = false := by simp [beq_false_of_ne hai]
        have hni : i ≠ a := Ne.symm hai
        simp [hba, hni]
      · have hba : (a == i && a == j) = false := by simp [beq_false_of_ne hai]
        have hni : i ≠ a := Ne.symm hai
        simp [hba, hni]
  simpa [List.mem_finRange] using hsingle (List.finRange 27) (List.nodup_finRange 27)

private def insertEntry (r c : Fin 27) (v : ℤ) : SparseMat27 → SparseMat27
  | [] => if v == 0 then [] else [(r, c, v)]
  | (r', c', v') :: t =>
      if r == r' && c == c' then
        let s := v + v'
        if s == 0 then t else (r', c', s) :: t
      else (r', c', v') :: insertEntry r c v t

private theorem sparseVal_nil (i j : Fin 27) : sparseVal [] i j = 0 := rfl

private theorem sparseVal_cons (r c : Fin 27) (v : ℤ) (t : SparseMat27) (i j : Fin 27) :
    sparseVal ((r, c, v) :: t) i j =
      (if r == i && c == j then v else 0) + sparseVal t i j := rfl

private theorem sparseVal_insertEntry (r c : Fin 27) (v : ℤ) (s : SparseMat27) (i j : Fin 27) :
    sparseVal (insertEntry r c v s) i j =
      (if r = i ∧ c = j then v else 0) + sparseVal s i j := by
  induction s with
  | nil =>
    dsimp only [insertEntry]
    by_cases hv : (v == 0) = true
    · have hv0 : v = 0 := beq_iff_eq.mp hv
      simp only [hv, ↓reduceIte, sparseVal_nil, add_zero]
      split_ifs <;> simp [hv0]
    · have hv' : (v == 0) = false := Bool.eq_false_iff.mpr hv
      simp only [hv', Bool.false_eq_true, ↓reduceIte, sparseVal_cons, sparseVal_nil, add_zero]
      by_cases hrc : r = i ∧ c = j
      · rcases hrc with ⟨rfl, rfl⟩; simp
      · have hne : (r == i && c == j) = false := by
          simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
          exact not_and_or.mp hrc
        simp [hrc, hne]
  | cons p t ih =>
    rcases p with ⟨r', c', v'⟩
    dsimp only [insertEntry]
    by_cases hmatch : (r == r' && c == c') = true
    · have hrc' : r = r' ∧ c = c' := by
        simpa [Bool.and_eq_true, beq_iff_eq] using hmatch
      rcases hrc' with ⟨rfl, rfl⟩
      simp only [hmatch, ↓reduceIte]
      by_cases hs : (v + v' == 0) = true
      · have hs0 : v + v' = 0 := beq_iff_eq.mp hs
        simp only [hs, ↓reduceIte, sparseVal_cons]
        by_cases hri : r = i ∧ c = j
        · rcases hri with ⟨rfl, rfl⟩
          simp
          omega
        · have hne : (r == i && c == j) = false := by
            simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
            exact not_and_or.mp hri
          simp [hri, hne]
      · have hs' : (v + v' == 0) = false := Bool.eq_false_iff.mpr hs
        simp only [hs', Bool.false_eq_true, ↓reduceIte, sparseVal_cons]
        by_cases hri : r = i ∧ c = j
        · rcases hri with ⟨rfl, rfl⟩
          simp
          omega
        · have hne : (r == i && c == j) = false := by
            simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
            exact not_and_or.mp hri
          simp [hri, hne]
    · have hm' : (r == r' && c == c') = false := Bool.eq_false_iff.mpr hmatch
      simp only [hm', Bool.false_eq_true, ↓reduceIte, sparseVal_cons, ih]
      exact add_left_comm _ _ _

private def sparseCoalesce : SparseMat27 → SparseMat27
  | [] => []
  | (r, c, v) :: t => insertEntry r c v (sparseCoalesce t)

private theorem sparseVal_coalesce (s : SparseMat27) (i j : Fin 27) :
    sparseVal (sparseCoalesce s) i j = sparseVal s i j := by
  induction s with
  | nil => rfl
  | cons p t ih =>
    rcases p with ⟨r, c, v⟩
    simp only [sparseCoalesce, sparseVal_insertEntry, sparseVal_cons, ih]
    by_cases hrc : r = i ∧ c = j
    · rcases hrc with ⟨rfl, rfl⟩; simp
    · have hne : (r == i && c == j) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        exact not_and_or.mp hrc
      simp [hrc, hne]

private theorem sparseToMat_coalesce (s : SparseMat27) :
    sparseToMat (sparseCoalesce s) = sparseToMat s := by
  ext i j
  exact sparseVal_coalesce s i j

private def weylOneSparse (i : Fin 6) : SparseMat27 :=
  sparseCoalesce (sparseMul (sparseAdd sparseId27 (e6SimpleESparse i))
    (sparseCoalesce (sparseMul (sparseSub sparseId27 (e6SimpleFSparse i))
      (sparseAdd sparseId27 (e6SimpleESparse i)))))

private theorem h3zornToMatrix_weylOne (i : Fin 6) :
    h3zornToMatrix (((h3zornWeylElt i 1).1 : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ).toLinearMap) =
      (sparseToMat (weylOneSparse i)).map Int.cast := by
  have h1m : h3zornToMatrix (1 : Module.End ℝ (H3Zorn ℝ)) = 1 := _root_.map_one h3zornToMatrix
  have hx : h3zornToMatrix (h3zornSimpleX i 1).1.toLinearMap =
      ((sparseToMat (sparseAdd sparseId27 (e6SimpleESparse i))).map Int.cast) := by
    change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + (1 : ℝ) • (e6SimpleE i).1) = _
    rw [one_smul, map_add, h1m, h3zornToMatrix_e6SimpleE, sparseToMat_add, sparseToMat_sparseId27]
    ext r c
    by_cases h : r = c <;> simp [h]
  have hy : h3zornToMatrix (h3zornSimpleY i (-1)).1.toLinearMap =
      ((sparseToMat (sparseSub sparseId27 (e6SimpleFSparse i))).map Int.cast) := by
    change h3zornToMatrix ((1 : Module.End ℝ (H3Zorn ℝ)) + (-1 : ℝ) • (e6SimpleF i).1) = _
    rw [neg_one_smul, ← sub_eq_add_neg, map_sub, h1m,
      h3zornToMatrix_e6SimpleF, sparseToMat_sub, sparseToMat_sparseId27]
    ext r c
    by_cases h : r = c <;> simp [h]
  have hm : ((h3zornWeylElt i 1).1 : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ).toLinearMap =
      (h3zornSimpleX i 1).1.toLinearMap *
        ((h3zornSimpleY i (-1)).1.toLinearMap * (h3zornSimpleX i 1).1.toLinearMap) := by
    simp [h3zornWeylElt, mul_assoc]
  rw [hm, map_mul, map_mul, hx, hy, weylOneSparse,
    sparseToMat_coalesce, sparseToMat_mul, sparseToMat_coalesce, sparseToMat_mul]
  ext r c
  simp [Matrix.mul_apply]

private theorem weyl_comm_of_sparse {i j : Fin 6}
    (hsp : sparseEq (sparseMul (weylOneSparse i) (weylOneSparse j))
      (sparseMul (weylOneSparse j) (weylOneSparse i)) = true) :
    h3zornWeylElt i 1 * h3zornWeylElt j 1 = h3zornWeylElt j 1 * h3zornWeylElt i 1 := by
  have hm := sparseToMat_eq_of_sparseEq hsp
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply h3zornToMatrix.injective
  change h3zornToMatrix ((h3zornWeylElt i 1).1.toLinearMap * (h3zornWeylElt j 1).1.toLinearMap) =
    h3zornToMatrix ((h3zornWeylElt j 1).1.toLinearMap * (h3zornWeylElt i 1).1.toLinearMap)
  rw [map_mul, map_mul, h3zornToMatrix_weylOne i, h3zornToMatrix_weylOne j]
  ext r c
  have hrc := congrFun (congrFun hm r) c
  simp only [sparseToMat_mul] at hrc
  simpa [Matrix.mul_apply] using congrArg (Int.cast : ℤ → ℝ) hrc

private theorem weyl_braid_of_sparse {i j : Fin 6}
    (hsp : sparseEq
      (sparseMul (weylOneSparse i) (sparseCoalesce (sparseMul (weylOneSparse j) (weylOneSparse i))))
      (sparseMul (weylOneSparse j) (sparseCoalesce (sparseMul (weylOneSparse i) (weylOneSparse j)))) = true) :
    h3zornWeylElt i 1 * h3zornWeylElt j 1 * h3zornWeylElt i 1 =
      h3zornWeylElt j 1 * h3zornWeylElt i 1 * h3zornWeylElt j 1 := by
  have hm := sparseToMat_eq_of_sparseEq hsp
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply h3zornToMatrix.injective
  have hmul : ∀ a b : h3zornReducedStructureGroup,
      ((a * b).1 : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ).toLinearMap = a.1.toLinearMap * b.1.toLinearMap :=
    fun _ _ => rfl
  rw [hmul, hmul, hmul, hmul, mul_assoc, mul_assoc,
    map_mul, map_mul, map_mul, map_mul,
    h3zornToMatrix_weylOne i, h3zornToMatrix_weylOne j]
  ext r c
  have hrc := congrFun (congrFun hm r) c
  simp only [sparseToMat_mul, sparseToMat_coalesce] at hrc
  simpa [Matrix.mul_apply, Matrix.mul_assoc] using congrArg (Int.cast : ℤ → ℝ) hrc

/-- Explicit non-commutativity witness for `sparseToMat (weylOneSparse 0)` and `sparseToMat (weylOneSparse 2)`. -/
theorem sparseToMat_weylOne_noncomm_witness :
    sparseToMat (weylOneSparse 0) * sparseToMat (weylOneSparse 2) ≠
      sparseToMat (weylOneSparse 2) * sparseToMat (weylOneSparse 0) := by
  intro heq
  have h09 := congrFun (congrFun heq 0) 9
  change (∑ k : Fin 27, sparseVal (weylOneSparse 0) 0 k * sparseVal (weylOneSparse 2) k 9) =
    (∑ k : Fin 27, sparseVal (weylOneSparse 2) 0 k * sparseVal (weylOneSparse 0) k 9) at h09
  rw [← sparseVal_mul, ← sparseVal_mul] at h09
  have hvL : sparseVal (sparseMul (weylOneSparse 0) (weylOneSparse 2)) 0 9 = 0 := by decide
  have hvR : sparseVal (sparseMul (weylOneSparse 2) (weylOneSparse 0)) 0 9 = -1 := by decide
  rw [hvL, hvR] at h09
  omega

theorem weylOne_matrix27_int_noncomm_witness :
    ∃ A B : Matrix (Fin 27) (Fin 27) ℤ, A * B ≠ B * A :=
  ⟨sparseToMat (weylOneSparse 0), sparseToMat (weylOneSparse 2), sparseToMat_weylOne_noncomm_witness⟩

/-- Explicit non-commutativity witness for adjacent E₆ Weyl elements. -/
theorem h3zornWeylElt_noncomm_witness :
    h3zornWeylElt 0 1 * h3zornWeylElt 2 1 ≠ h3zornWeylElt 2 1 * h3zornWeylElt 0 1 := by
  intro heq
  have hm := congrArg (fun g : h3zornReducedStructureGroup => h3zornToMatrix g.1.toLinearMap) heq
  change h3zornToMatrix ((h3zornWeylElt 0 1).1.toLinearMap * (h3zornWeylElt 2 1).1.toLinearMap) =
    h3zornToMatrix ((h3zornWeylElt 2 1).1.toLinearMap * (h3zornWeylElt 0 1).1.toLinearMap) at hm
  rw [map_mul, map_mul, h3zornToMatrix_weylOne 0, h3zornToMatrix_weylOne 2] at hm
  have hmul : ∀ (a b : SparseMat27),
      (sparseToMat a).map (Int.cast : ℤ → ℝ) * (sparseToMat b).map (Int.cast : ℤ → ℝ) =
        (sparseToMat (sparseMul a b)).map (Int.cast : ℤ → ℝ) := by
    intro a b
    rw [sparseToMat_mul]
    ext r c
    simp only [Matrix.mul_apply, Matrix.map_apply, Int.cast_sum, Int.cast_mul]
  rw [hmul, hmul] at hm
  have hm09 := congrFun (congrFun hm 0) 9
  simp only [Matrix.map_apply, sparseToMat] at hm09
  have hvL : sparseVal (sparseMul (weylOneSparse 0) (weylOneSparse 2)) 0 9 = 0 := by decide
  have hvR : sparseVal (sparseMul (weylOneSparse 2) (weylOneSparse 0)) 0 9 = -1 := by decide
  rw [hvL, hvR] at hm09
  norm_num at hm09

/-- E₆ Coxeter braid relations on the simple Weyl reflections `w_i(1)` in `Str₀(H₃(𝕆_s))`. -/

theorem h3zornWeylElt_braid_0_2 :
    h3zornWeylElt 0 1 * h3zornWeylElt 2 1 * h3zornWeylElt 0 1 =
      h3zornWeylElt 2 1 * h3zornWeylElt 0 1 * h3zornWeylElt 2 1 :=
  weyl_braid_of_sparse (by decide)

theorem h3zornWeylElt_braid_1_3 :
    h3zornWeylElt 1 1 * h3zornWeylElt 3 1 * h3zornWeylElt 1 1 =
      h3zornWeylElt 3 1 * h3zornWeylElt 1 1 * h3zornWeylElt 3 1 :=
  weyl_braid_of_sparse (by decide)

theorem h3zornWeylElt_braid_2_3 :
    h3zornWeylElt 2 1 * h3zornWeylElt 3 1 * h3zornWeylElt 2 1 =
      h3zornWeylElt 3 1 * h3zornWeylElt 2 1 * h3zornWeylElt 3 1 :=
  weyl_braid_of_sparse (by decide)

theorem h3zornWeylElt_braid_3_4 :
    h3zornWeylElt 3 1 * h3zornWeylElt 4 1 * h3zornWeylElt 3 1 =
      h3zornWeylElt 4 1 * h3zornWeylElt 3 1 * h3zornWeylElt 4 1 :=
  weyl_braid_of_sparse (by decide)

theorem h3zornWeylElt_braid_4_5 :
    h3zornWeylElt 4 1 * h3zornWeylElt 5 1 * h3zornWeylElt 4 1 =
      h3zornWeylElt 5 1 * h3zornWeylElt 4 1 * h3zornWeylElt 5 1 :=
  weyl_braid_of_sparse (by decide)

theorem h3zornWeylElt_comm_0_1 :
    h3zornWeylElt 0 1 * h3zornWeylElt 1 1 =
      h3zornWeylElt 1 1 * h3zornWeylElt 0 1 :=
  weyl_comm_of_sparse (by decide)

theorem h3zornWeylElt_comm_0_3 :
    h3zornWeylElt 0 1 * h3zornWeylElt 3 1 =
      h3zornWeylElt 3 1 * h3zornWeylElt 0 1 :=
  weyl_comm_of_sparse (by decide)

theorem h3zornWeylElt_comm_0_4 :
    h3zornWeylElt 0 1 * h3zornWeylElt 4 1 =
      h3zornWeylElt 4 1 * h3zornWeylElt 0 1 :=
  weyl_comm_of_sparse (by decide)

theorem h3zornWeylElt_comm_0_5 :
    h3zornWeylElt 0 1 * h3zornWeylElt 5 1 =
      h3zornWeylElt 5 1 * h3zornWeylElt 0 1 :=
  weyl_comm_of_sparse (by decide)

theorem h3zornWeylElt_comm_1_2 :
    h3zornWeylElt 1 1 * h3zornWeylElt 2 1 =
      h3zornWeylElt 2 1 * h3zornWeylElt 1 1 :=
  weyl_comm_of_sparse (by decide)

theorem h3zornWeylElt_comm_1_4 :
    h3zornWeylElt 1 1 * h3zornWeylElt 4 1 =
      h3zornWeylElt 4 1 * h3zornWeylElt 1 1 :=
  weyl_comm_of_sparse (by decide)

theorem h3zornWeylElt_comm_1_5 :
    h3zornWeylElt 1 1 * h3zornWeylElt 5 1 =
      h3zornWeylElt 5 1 * h3zornWeylElt 1 1 :=
  weyl_comm_of_sparse (by decide)

theorem h3zornWeylElt_comm_2_4 :
    h3zornWeylElt 2 1 * h3zornWeylElt 4 1 =
      h3zornWeylElt 4 1 * h3zornWeylElt 2 1 :=
  weyl_comm_of_sparse (by decide)

theorem h3zornWeylElt_comm_2_5 :
    h3zornWeylElt 2 1 * h3zornWeylElt 5 1 =
      h3zornWeylElt 5 1 * h3zornWeylElt 2 1 :=
  weyl_comm_of_sparse (by decide)

theorem h3zornWeylElt_comm_3_5 :
    h3zornWeylElt 3 1 * h3zornWeylElt 5 1 =
      h3zornWeylElt 5 1 * h3zornWeylElt 3 1 :=
  weyl_comm_of_sparse (by decide)

/-- Torus element `h_i(t) = w_i(t) w_i(-1) ∈ h3zornChevalleyE6`. -/
def h3zornTorusElt (i : Fin 6) (t : ℝˣ) : h3zornReducedStructureGroup :=
  h3zornWeylElt i t * h3zornWeylElt i (-1)

theorem h3zornTorusElt_mem_chevalleyE6 (i : Fin 6) (t : ℝˣ) :
    h3zornTorusElt i t ∈ h3zornChevalleyE6 :=
  Subgroup.mul_mem _ (h3zornWeylElt_mem_chevalleyE6 i t) (h3zornWeylElt_mem_chevalleyE6 i (-1))

private theorem minuscule_weight_dichotomy (i : Fin 6) (k : Fin 27) :
    h3zornWeight k i = -1 ∨ h3zornWeight k i = 0 ∨ h3zornWeight k i = 1 := by
  have h : (List.finRange 6).all (fun i => (List.finRange 27).all (fun k =>
      decide (h3zornWeight k i = -1 ∨ h3zornWeight k i = 0 ∨ h3zornWeight k i = 1))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at h
  exact h i k

private theorem simpleE_kill_of_weight_nonneg (i : Fin 6) (k : Fin 27)
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
  have hz : ∀ r : Fin 27, ((h3zornToMatrix (e6SimpleE i).1) r k) • h3ZornBasis r = 0 := by
    intro r; rw [hzero r, zero_smul]
  rw [hrep]
  exact Finset.sum_eq_zero fun r _ => hz r

private theorem simpleF_kill_of_weight_nonpos (i : Fin 6) (k : Fin 27)
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
  have hz : ∀ r : Fin 27, ((h3zornToMatrix (e6SimpleF i).1) r k) • h3ZornBasis r = 0 := by
    intro r; rw [hzero r, zero_smul]
  rw [hrep]
  exact Finset.sum_eq_zero fun r _ => hz r

private theorem e6SimpleE_sq_apply (i : Fin 6) (v : H3Zorn ℝ) :
    (e6SimpleE i).1 ((e6SimpleE i).1 v) = 0 := by
  have h0 := LinearMap.ext_iff.mp (e6RootVec_sq_zero (eSimpleIdx i)) v
  change (e6RootVec (eSimpleIdx i)).1 ((e6RootVec (eSimpleIdx i)).1 v) = 0
  simpa [sq, Module.End.mul_apply] using h0

private theorem e6SimpleF_sq_apply (i : Fin 6) (v : H3Zorn ℝ) :
    (e6SimpleF i).1 ((e6SimpleF i).1 v) = 0 := by
  have h0 := LinearMap.ext_iff.mp (e6SimpleF_sq_zero i) v
  simpa [sq, Module.End.mul_apply] using h0

private theorem e6Simple_comm_apply (i : Fin 6) (v : H3Zorn ℝ) :
    (e6SimpleE i).1 ((e6SimpleF i).1 v) - (e6SimpleF i).1 ((e6SimpleE i).1 v) =
      (e6SimpleH i).1 v := by
  have hbr := congrArg (fun x : h3zornCubicStabilizer => x.1 v) (e6Simple_bracket_EF_same i)
  exact hbr

private theorem weyl_on_highest_like (i : Fin 6) (s : ℝ) (hs : s ≠ 0) (v : H3Zorn ℝ)
    (hE : (e6SimpleE i).1 v = 0)
    (hEF : (e6SimpleE i).1 ((e6SimpleF i).1 v) = v) :
    ((h3zornSimpleX i s).1 * (h3zornSimpleY i (-s⁻¹)).1 * (h3zornSimpleX i s).1) v =
      (-s⁻¹) • (e6SimpleF i).1 v := by
  change (h3zornSimpleX i s).1 ((h3zornSimpleY i (-s⁻¹)).1 ((h3zornSimpleX i s).1 v)) = _
  have hEE : (e6RootVec (eSimpleIdx i)).1 = (e6SimpleE i).1 := rfl
  have h1 : (h3zornSimpleX i s).1 v = v := by
    change v + s • (e6RootVec (eSimpleIdx i)).1 v = v
    rw [hEE, hE, smul_zero, add_zero]
  have h2 : (h3zornSimpleY i (-s⁻¹)).1 v = v + (-s⁻¹) • (e6SimpleF i).1 v := rfl
  have h3 : (h3zornSimpleX i s).1 (v + (-s⁻¹) • (e6SimpleF i).1 v) = (-s⁻¹) • (e6SimpleF i).1 v := by
    change v + (-s⁻¹) • (e6SimpleF i).1 v +
      s • (e6RootVec (eSimpleIdx i)).1 (v + (-s⁻¹) • (e6SimpleF i).1 v) = _
    rw [hEE, map_add, map_smul, hE, hEF, zero_add, smul_smul,
      show s * (-s⁻¹) = -1 by rw [mul_neg, mul_inv_cancel₀ hs], neg_one_smul]
    module
  rw [h1, h2, h3]

private theorem weyl_on_lowest_like (i : Fin 6) (s : ℝ) (hs : s ≠ 0) (v : H3Zorn ℝ)
    (hF : (e6SimpleF i).1 v = 0)
    (hFE : (e6SimpleF i).1 ((e6SimpleE i).1 v) = v) :
    ((h3zornSimpleX i s).1 * (h3zornSimpleY i (-s⁻¹)).1 * (h3zornSimpleX i s).1) v =
      s • (e6SimpleE i).1 v := by
  change (h3zornSimpleX i s).1 ((h3zornSimpleY i (-s⁻¹)).1 ((h3zornSimpleX i s).1 v)) = _
  have hEE : (e6RootVec (eSimpleIdx i)).1 = (e6SimpleE i).1 := rfl
  have h1 : (h3zornSimpleX i s).1 v = v + s • (e6SimpleE i).1 v := rfl
  have h2 : (h3zornSimpleY i (-s⁻¹)).1 (v + s • (e6SimpleE i).1 v) = s • (e6SimpleE i).1 v := by
    change v + s • (e6SimpleE i).1 v + (-s⁻¹) • (e6SimpleF i).1 (v + s • (e6SimpleE i).1 v) = _
    rw [map_add, map_smul, hF, hFE, zero_add, smul_smul,
      show (-s⁻¹) * s = -1 by rw [neg_mul, inv_mul_cancel₀ hs], neg_one_smul]
    module
  have h3 : (h3zornSimpleX i s).1 (s • (e6SimpleE i).1 v) = s • (e6SimpleE i).1 v := by
    change s • (e6SimpleE i).1 v + s • (e6RootVec (eSimpleIdx i)).1 (s • (e6SimpleE i).1 v) = _
    rw [hEE, map_smul, e6SimpleE_sq_apply, smul_zero, smul_zero, add_zero]
  rw [h1, h2, h3]

/-- Exact diagonal weight action of `h3zornTorusElt i t` on the 27 basis vectors `h3ZornBasis k`. -/
theorem h3zornTorusElt_apply_basis (i : Fin 6) (t : ℝˣ) (k : Fin 27) :
    (h3zornTorusElt i t).1 (h3ZornBasis k) = ((t ^ h3zornWeight k i : ℝˣ) : ℝ) • h3ZornBasis k := by
  have hm : ((h3zornTorusElt i t).1 : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) =
      (h3zornWeylElt i t).1 * (h3zornWeylElt i (-1)).1 := rfl
  change ((h3zornWeylElt i t).1 ((h3zornWeylElt i (-1)).1 (h3ZornBasis k))) = _
  have hw_unfold : ∀ (s : ℝˣ) (v : H3Zorn ℝ),
      (h3zornWeylElt i s).1 v =
        ((h3zornSimpleX i s).1 * (h3zornSimpleY i (-((s⁻¹ : ℝˣ) : ℝ))).1 *
          (h3zornSimpleX i s).1) v := fun _ _ => rfl
  rcases minuscule_weight_dichotomy i k with hm1 | h0 | h1
  · have hF : (e6SimpleF i).1 (h3ZornBasis k) = 0 :=
      simpleF_kill_of_weight_nonpos i k (Or.inr hm1)
    have hFE : (e6SimpleF i).1 ((e6SimpleE i).1 (h3ZornBasis k)) = h3ZornBasis k := by
      have hc := e6Simple_comm_apply i (h3ZornBasis k)
      rw [hF, map_zero, zero_sub, e6SimpleH_apply_basis, hm1, Int.cast_neg, Int.cast_one] at hc
      change -((e6SimpleF i).1 ((e6SimpleE i).1 (h3ZornBasis k))) = (-1 : ℝ) • h3ZornBasis k at hc
      have hneg := congrArg Neg.neg hc
      simpa using hneg
    have h1_res : (h3zornWeylElt i (-1)).1 (h3ZornBasis k) = -(e6SimpleE i).1 (h3ZornBasis k) := by
      rw [hw_unfold]
      have hs : ((-1 : ℝˣ) : ℝ) ≠ 0 := by norm_num
      have hloc := weyl_on_lowest_like i (-1) hs (h3ZornBasis k) hF hFE
      simpa [neg_inv_val_neg_one] using hloc
    let u := (e6SimpleE i).1 (h3ZornBasis k)
    have hEu : (e6SimpleE i).1 u = 0 := e6SimpleE_sq_apply i (h3ZornBasis k)
    have hEFu : (e6SimpleE i).1 ((e6SimpleF i).1 u) = u := by
      dsimp [u]
      rw [hFE]
    have ht_res : (h3zornWeylElt i t).1 u = (-((t⁻¹ : ℝˣ) : ℝ)) • (h3ZornBasis k) := by
      rw [hw_unfold]
      have hloc := weyl_on_highest_like i (t : ℝ) t.ne_zero u hEu hEFu
      rw [Units.val_inv_eq_inv_val]
      simpa [u, hFE] using hloc
    rw [h1_res, map_neg, ht_res, hm1, zpow_neg_one, Units.val_inv_eq_inv_val]
    module
  · have hE : (e6SimpleE i).1 (h3ZornBasis k) = 0 :=
      simpleE_kill_of_weight_nonneg i k (Or.inl h0)
    have hF : (e6SimpleF i).1 (h3ZornBasis k) = 0 :=
      simpleF_kill_of_weight_nonpos i k (Or.inl h0)
    have hfix : ∀ (s : ℝˣ), (h3zornWeylElt i s).1 (h3ZornBasis k) = h3ZornBasis k := by
      intro s
      rw [hw_unfold]
      change (h3zornSimpleX i s).1 ((h3zornSimpleY i (-((s⁻¹ : ℝˣ) : ℝ))).1
        ((h3zornSimpleX i s).1 (h3ZornBasis k))) = h3ZornBasis k
      simp only [h3zornSimpleX, h3zornSimpleY, sqZeroExp_coe, sqZeroExpEquiv_apply]
      have hEE : (e6RootVec (eSimpleIdx i)).1 (h3ZornBasis k) = 0 := hE
      rw [hEE, smul_zero, add_zero, hF, smul_zero, add_zero, hEE, smul_zero, add_zero]
    rw [hfix (-1), hfix t, h0, zpow_zero, Units.val_one, one_smul]
  · have hE : (e6SimpleE i).1 (h3ZornBasis k) = 0 :=
      simpleE_kill_of_weight_nonneg i k (Or.inr h1)
    have hEF : (e6SimpleE i).1 ((e6SimpleF i).1 (h3ZornBasis k)) = h3ZornBasis k := by
      have hc := e6Simple_comm_apply i (h3ZornBasis k)
      rw [hE, map_zero, sub_zero, e6SimpleH_apply_basis, h1] at hc
      simpa using hc
    have h1_res : (h3zornWeylElt i (-1)).1 (h3ZornBasis k) = (e6SimpleF i).1 (h3ZornBasis k) := by
      rw [hw_unfold]
      have hs : ((-1 : ℝˣ) : ℝ) ≠ 0 := by norm_num
      have hloc := weyl_on_highest_like i (-1) hs (h3ZornBasis k) hE hEF
      simpa [neg_inv_val_neg_one] using hloc
    let u := (e6SimpleF i).1 (h3ZornBasis k)
    have hFu : (e6SimpleF i).1 u = 0 := e6SimpleF_sq_apply i (h3ZornBasis k)
    have hFEu : (e6SimpleF i).1 ((e6SimpleE i).1 u) = u := by
      dsimp [u]
      rw [hEF]
    have ht_res : (h3zornWeylElt i t).1 u = (t : ℝ) • h3ZornBasis k := by
      rw [hw_unfold]
      have hloc := weyl_on_lowest_like i (t : ℝ) t.ne_zero u hFu hFEu
      simpa [u, hEF] using hloc
    rw [h1_res, ht_res, h1, zpow_one]

theorem h3zornTorusElt_symm_apply_basis (i : Fin 6) (t : ℝˣ) (k : Fin 27) :
    (h3zornTorusElt i t).1.symm (h3ZornBasis k) =
      ((t : ℝ) ^ (-h3zornWeight k i)) • h3ZornBasis k := by
  rw [LinearEquiv.symm_apply_eq, map_smul, h3zornTorusElt_apply_basis, smul_smul,
    Units.val_zpow_eq_zpow_val, zpow_neg_mul_self, one_smul]

end WeylAndTorus

section MinusculeWeightAlignment

/-- Weight table from `CFSG.LieType.Steinberg.Minuscule.e6Data.weights` in `CertInputs.lean`. -/
def cfsgMinusculeWeightCode : List ℕ :=

  [1366, 1380, 1413, 1561, 1617, 2137, 2193, 345, 2341, 401, 2374, 549, 2388, 582, 1125, 596, 1158, 1172, 1306, 1320, 1362, 1376, 1353, 1409, 1557, 2133, 341]


/-- Decoded Bourbaki weight vector `((code / 4^i % 4) : ℤ) - 1` matching `MinData.wt`. -/
def cfsgMinusculeWeight (k : Fin 27) (i : Fin 6) : ℤ :=
  ((cfsgMinusculeWeightCode.getD k.val 0 / 4 ^ i.val % 4 : ℕ) : ℤ) - 1

/-- Explicit index permutation matching `perm_to_min` mapping CFSG minuscule indices `0..26`
to `h3ZornBasis` indices `0..26`. -/
def permToMinusculeFun (k : Fin 27) : Fin 27 :=
  match k.val with

  | 0 => 3

  | 1 => 18

  | 2 => 22

  | 3 => 21

  | 4 => 20

  | 5 => 15

  | 6 => 16

  | 7 => 7

  | 8 => 17

  | 9 => 8

  | 10 => 26

  | 11 => 9

  | 12 => 2

  | 13 => 0

  | 14 => 1

  | 15 => 19

  | 16 => 6

  | 17 => 14

  | 18 => 5

  | 19 => 13

  | 20 => 4

  | 21 => 12

  | 22 => 23

  | 23 => 24

  | 24 => 25

  | 25 => 11

  | 26 => 10

  | _ => 0


def permToMinuscule : Equiv.Perm (Fin 27) :=
  Equiv.ofBijective permToMinusculeFun
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨by
        intro a b h
        have hc : (List.finRange 27).all (fun a => (List.finRange 27).all (fun b =>
            if permToMinusculeFun a == permToMinusculeFun b then a == b else true)) = true := by
          decide
        simp only [List.all_eq_true, List.mem_finRange, true_implies] at hc
        have hab := hc a b
        have heq : (permToMinusculeFun a == permToMinusculeFun b) = true := beq_iff_eq.mpr h
        rw [heq] at hab
        exact beq_iff_eq.mp hab,
       rfl⟩)

/-- **27D Minuscule Weight Alignment**: `h3zornWeight` on `H3Zorn ℝ` coincides up to the
explicit permutation `permToMinuscule` with the decoded `CFSG` minuscule `e6Data.weights`. -/
theorem h3zornWeight_perm_eq_cfsgMinusculeWeight (k : Fin 27) (i : Fin 6) :
    h3zornWeight (permToMinuscule k) i = cfsgMinusculeWeight k i := by
  have h : (List.finRange 27).all (fun k => (List.finRange 6).all (fun i =>
      h3zornWeight (permToMinusculeFun k) i == cfsgMinusculeWeight k i)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h k i

theorem h3zorn_highestWeight_eq :
    (fun i : Fin 6 => cfsgMinusculeWeight 0 i) = ![1, 0, 0, 0, 0, 0] := by
  ext i; fin_cases i <;> decide

theorem h3zorn_lowestWeight_eq :
    (fun i : Fin 6 => cfsgMinusculeWeight 26 i) = ![0, 0, 0, 0, 0, -1] := by
  ext i; fin_cases i <;> decide

end MinusculeWeightAlignment

section Adjoint78DBridge

/-- Explicit 78-dimensional linear isomorphism between `CFSGPort.Chevalley.RootModule .E6 ℝ`
and `h3zornCubicStabilizer` (`𝔢₆(6)`), sending `hVec .E6 ℝ i ↦ e6SimpleH i` and
`rootVec .E6 ℝ (e6RootCoord r) ↦ e6RootVec r`. -/
def h3zornChevalleyEquiv :
    RootModule .E6 ℝ ≃ₗ[ℝ] h3zornCubicStabilizer :=
  (Finsupp.domLCongr (R := ℝ) (Equiv.sumCongr (Equiv.refl (Fin 6)) e6RootEquiv.symm)).trans
    e6ChevalleyBasis.repr.symm

theorem h3zornChevalleyEquiv_hVec (i : Fin 6) :
    h3zornChevalleyEquiv (hVec .E6 ℝ i) = e6SimpleH i := by
  have hsing : (Finsupp.domLCongr (R := ℝ) (Equiv.sumCongr (Equiv.refl (Fin 6)) e6RootEquiv.symm))
      (hVec .E6 ℝ i) = Finsupp.single (Sum.inl i) (1 : ℝ) :=
    Finsupp.domLCongr_single (R := ℝ)
      (Equiv.sumCongr (Equiv.refl (Fin 6)) e6RootEquiv.symm) (Sum.inl (i : Fin Tag.E6.rank)) (1 : ℝ)
  change e6ChevalleyBasis.repr.symm
    ((Finsupp.domLCongr (R := ℝ) (Equiv.sumCongr (Equiv.refl (Fin 6)) e6RootEquiv.symm))
      (hVec .E6 ℝ i)) = e6SimpleH i
  rw [hsing, Module.Basis.repr_symm_single_one, e6ChevalleyBasis_inl]

theorem h3zornChevalleyEquiv_rootVec (r : Fin 72) :
    h3zornChevalleyEquiv (rootVec .E6 ℝ (e6RootCoord r)) = e6RootVec r := by
  have hroot : rootVec .E6 ℝ (e6RootCoord r) =
      Finsupp.single (Sum.inr (e6RootEquiv r)) 1 := by
    rw [rootVec_eq_single_of_isRoot (e6RootCoord_isRoot r)]
    rfl
  have hsing : (Finsupp.domLCongr (R := ℝ) (Equiv.sumCongr (Equiv.refl (Fin 6)) e6RootEquiv.symm))
      (rootVec .E6 ℝ (e6RootCoord r)) = Finsupp.single (Sum.inr r) (1 : ℝ) := by
    have hs := Finsupp.domLCongr_single (R := ℝ)
      (Equiv.sumCongr (Equiv.refl (Fin 6)) e6RootEquiv.symm)
      (Sum.inr (e6RootEquiv r) : Label .E6) (1 : ℝ)
    have hdom : (Equiv.sumCongr (Equiv.refl (Fin 6)) e6RootEquiv.symm)
        (Sum.inr (e6RootEquiv r) : Label .E6) = Sum.inr r :=
      congrArg Sum.inr (e6RootEquiv.symm_apply_apply r)
    rw [hroot]
    exact hs.trans (congrArg (fun k => Finsupp.single k (1 : ℝ)) hdom)
  change e6ChevalleyBasis.repr.symm
    ((Finsupp.domLCongr (R := ℝ) (Equiv.sumCongr (Equiv.refl (Fin 6)) e6RootEquiv.symm))
      (rootVec .E6 ℝ (e6RootCoord r))) = e6RootVec r
  rw [hsing, Module.Basis.repr_symm_single_one, e6ChevalleyBasis_inr]

/-- Adjoint Lie-algebra conjugation action of `Str₀(H₃(𝕆_s))` on `h3zornCubicStabilizer`. -/
def h3zornAdjointAction (g : h3zornReducedStructureGroup) :
    h3zornCubicStabilizer ≃ₗ⁅ℝ⁆ h3zornCubicStabilizer :=
  h3zornCubicStabilizerLieEquivOfNormSimilitude g.1 1 (fun x => by simpa using g.2 x)

@[simp] theorem h3zornAdjointAction_coe (g : h3zornReducedStructureGroup)
    (Y : h3zornCubicStabilizer) :
    ((h3zornAdjointAction g Y).1 : Module.End ℝ (H3Zorn ℝ)) =
      g.1.toLinearMap * Y.1 * g.1.symm.toLinearMap := rfl

private theorem h3zornTorusElt_apply_of_eigenvector (i : Fin 6) (t : ℝˣ) (μ : ℤ)
    (z : H3Zorn ℝ) (hz : (e6SimpleH i).1 z = (μ : ℝ) • z) :
    (h3zornTorusElt i t).1 z = ((t : ℝ) ^ μ) • z := by
  have hrep := h3ZornBasis.sum_repr z
  have hcoord : ∀ a : Fin 27, h3ZornBasis.repr z a ≠ 0 → h3zornWeight a i = μ := by
    intro a ha
    have hact : (e6SimpleH i).1 z =
        ∑ k : Fin 27, (h3ZornBasis.repr z k * (h3zornWeight k i : ℝ)) • h3ZornBasis k := by
      conv_lhs => rw [← hrep, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, e6SimpleH_apply_basis, smul_smul]
    have hrhs : (μ : ℝ) • z =
        ∑ k : Fin 27, (h3ZornBasis.repr z k * (μ : ℝ)) • h3ZornBasis k := by
      conv_lhs => rw [← hrep, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, mul_comm]
    have heq := hact.symm.trans (hz.trans hrhs)
    have hc := congrArg (fun v => h3ZornBasis.repr v a) heq
    simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hc
    have hmul : h3ZornBasis.repr z a * ((h3zornWeight a i : ℝ) - (μ : ℝ)) = 0 := by
      have := sub_eq_zero.mpr hc
      rw [← mul_sub] at this
      exact this
    have hsub := (mul_eq_zero.mp hmul).resolve_left ha
    exact Int.cast_injective (sub_eq_zero.mp hsub)
  conv_lhs => rw [← hrep, map_sum]
  conv_rhs => rw [← hrep, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, h3zornTorusElt_apply_basis, smul_smul, smul_smul]
  by_cases ha : h3ZornBasis.repr z a = 0
  · simp [ha]
  · rw [hcoord a ha, Units.val_zpow_eq_zpow_val, mul_comm]

theorem h3zornAdjointAction_torusElt_hVec (i j : Fin 6) (t : ℝˣ) :
    h3zornAdjointAction (h3zornTorusElt i t) (e6SimpleH j) = e6SimpleH j := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rw [h3zornAdjointAction_coe, Module.End.mul_apply, Module.End.mul_apply]
  simp only [LinearEquiv.coe_toLinearMap]
  rw [← h3ZornBasis.sum_repr x, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, map_smul, map_smul]
  congr 1
  rw [h3zornTorusElt_symm_apply_basis, map_smul, e6SimpleH_apply_basis, smul_smul,
    map_smul, h3zornTorusElt_apply_basis, smul_smul, Units.val_zpow_eq_zpow_val]
  have hpow : ((t : ℝ) ^ (-h3zornWeight k i)) * (h3zornWeight k j : ℝ) * (t ^ h3zornWeight k i : ℝ) =
      (h3zornWeight k j : ℝ) := by
    rw [mul_right_comm, zpow_neg_mul_self, one_mul]
  rw [hpow]

theorem h3zornAdjointAction_torusElt_rootVec (i : Fin 6) (t : ℝˣ) (r : Fin 72) :
    h3zornAdjointAction (h3zornTorusElt i t) (e6RootVec r) =
      ((t ^ rootEigenvalue i r : ℝˣ) : ℝ) • e6RootVec r := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rw [SetLike.val_smul, LinearMap.smul_apply, h3zornAdjointAction_coe,
    Module.End.mul_apply, Module.End.mul_apply]
  simp only [LinearEquiv.coe_toLinearMap]
  rw [← h3ZornBasis.sum_repr x, map_sum, map_sum, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, map_smul, map_smul, smul_comm ((t ^ rootEigenvalue i r : ℝˣ) : ℝ)]
  congr 1
  rw [h3zornTorusElt_symm_apply_basis, map_smul, map_smul]
  let z := (e6RootVec r).1 (h3ZornBasis k)
  have hz : (e6SimpleH i).1 z = ((h3zornWeight k i + rootEigenvalue i r : ℤ) : ℝ) • z := by
    have hbr := congrArg (fun op : h3zornCubicStabilizer => op.1 (h3ZornBasis k))
      (e6RootVec_bracket_H i r)
    change (e6SimpleH i).1 ((e6RootVec r).1 (h3ZornBasis k)) -
        (e6RootVec r).1 ((e6SimpleH i).1 (h3ZornBasis k)) =
      (rootEigenvalue i r : ℝ) • z at hbr
    rw [e6SimpleH_apply_basis, map_smul] at hbr
    have hadd := eq_add_of_sub_eq hbr
    rw [Int.cast_add, add_smul]
    simpa [z, add_comm] using hadd
  rw [h3zornTorusElt_apply_of_eigenvector i t (h3zornWeight k i + rootEigenvalue i r) z hz,
    smul_smul, zpow_neg_mul_add, Units.val_zpow_eq_zpow_val]

/-- **78D Adjoint Torus Intertwining Theorem**: `h3zornChevalleyEquiv` intertwines the
abstract Chevalley torus `CFSGPort.Chevalley.torusElt .E6 ℝ i t` on `RootModule .E6 ℝ`
with the native adjoint action of `h3zornTorusElt i t ∈ Str₀(H₃(𝕆_s))` on `h3zornCubicStabilizer`. -/
theorem h3zornChevalleyEquiv_torusElt (i : Fin 6) (t : ℝˣ) (v : RootModule .E6 ℝ) :
    h3zornChevalleyEquiv ((torusElt .E6 ℝ i t : Module.End ℝ (RootModule .E6 ℝ)) v) =
      h3zornAdjointAction (h3zornTorusElt i t) (h3zornChevalleyEquiv v) := by
  have hsingle : ∀ (b : Label .E6),
      h3zornChevalleyEquiv
          ((torusElt .E6 ℝ i t : Module.End ℝ (RootModule .E6 ℝ)) (Finsupp.single b 1)) =
        h3zornAdjointAction (h3zornTorusElt i t)
          (h3zornChevalleyEquiv (Finsupp.single b 1)) := by
    intro b
    have hts : (torusElt .E6 ℝ i t : Module.End ℝ (RootModule .E6 ℝ)) (Finsupp.single b 1) =
        ((t ^ (∑ j, Tag.cartan .E6 i j * b.latticeWeight j) : ℝˣ) : ℝ) • Finsupp.single b 1 :=
      torusElt_single_eq (τ := .E6) (R := ℝ) (i : Fin Tag.E6.rank) t b
    rw [hts]
    rcases b with j | α
    · simp only [Label.latticeWeight, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zpow_zero,
        Units.val_one, one_smul]
      have hj : h3zornChevalleyEquiv (Finsupp.single (Sum.inl j) (1 : ℝ)) = e6SimpleH j :=
        h3zornChevalleyEquiv_hVec j
      have htor : h3zornAdjointAction (h3zornTorusElt i t) (e6SimpleH j) = e6SimpleH j :=
        h3zornAdjointAction_torusElt_hVec i j t
      rw [hj, htor]
    · let r : Fin 72 := e6RootEquiv.symm α
      have hEqRoot : h3zornChevalleyEquiv (Finsupp.single (Sum.inr α) (1 : ℝ)) = e6RootVec r := by
        have hs := Finsupp.domLCongr_single (R := ℝ)
          (Equiv.sumCongr (Equiv.refl (Fin 6)) e6RootEquiv.symm)
          (Sum.inr α : Label .E6) (1 : ℝ)
        have hdom : (Equiv.sumCongr (Equiv.refl (Fin 6)) e6RootEquiv.symm)
            (Sum.inr α : Label .E6) = Sum.inr r := rfl
        have h1 : (Finsupp.domLCongr (R := ℝ) (Equiv.sumCongr (Equiv.refl (Fin 6)) e6RootEquiv.symm))
            (Finsupp.single (Sum.inr α : Label .E6) (1 : ℝ)) = Finsupp.single (Sum.inr r) (1 : ℝ) :=
          hs.trans (congrArg (fun k => Finsupp.single k (1 : ℝ)) hdom)
        exact (congrArg e6ChevalleyBasis.repr.symm h1).trans
          ((Module.Basis.repr_symm_single_one e6ChevalleyBasis (Sum.inr r)).trans
            (e6ChevalleyBasis_inr r))
      have hcoord : α.1 = e6RootCoord r :=
        (congrArg Subtype.val (e6RootEquiv.apply_symm_apply α)).symm
      have hexp : (∑ j : Fin Tag.E6.rank, Tag.cartan .E6 i j *
          Label.latticeWeight (Sum.inr α) j) = rootEigenvalue i r := by
        change (∑ j : Fin 6, Tag.cartan .E6 i j * α.1 j) =
          ∑ j : Fin 6, Tag.cartan .E6 i j * e6RootCoord r j
        rw [hcoord]
      have htor : h3zornAdjointAction (h3zornTorusElt i t) (e6RootVec r) =
          ((t ^ rootEigenvalue i r : ℝˣ) : ℝ) • e6RootVec r :=
        h3zornAdjointAction_torusElt_rootVec i t r
      rw [map_smul, hEqRoot, hexp, htor]
  rw [← Finsupp.sum_single v, Finsupp.sum, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hsc : Finsupp.single b (v b) = v b • Finsupp.single b 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsc, map_smul, map_smul, map_smul, map_smul, hsingle b]

/-- **Exact Degree-2 Adjoint Exponential Law**: on the full 78D `h3zornCubicStabilizer`,
conjugation by `h3zornSimpleX i c` equals `Id + c • ad(e6SimpleE i) + (c²/2) • ad(e6SimpleE i)²`.
(Note: `CFSGPort.Chevalley.xOp` uses unsigned `(τ.cartan j i).natAbs` on `hVec j`, whereas the
true Lie-algebraic Chevalley exponential acts with signed `Tag.cartan .E6 j i`.) -/
theorem h3zornAdjointAction_simpleX (i : Fin 6) (c : ℝ) (Y : h3zornCubicStabilizer) :
    h3zornAdjointAction (h3zornSimpleX i c) Y =
      Y + c • ⁅e6SimpleE i, Y⁆ + (c ^ 2 / 2) • ⁅e6SimpleE i, ⁅e6SimpleE i, Y⁆⁆ := by
  apply Subtype.ext
  let E : Module.End ℝ (H3Zorn ℝ) := (e6SimpleE i).1
  have hE2 : E * E = 0 := by
    change (e6RootVec (eSimpleIdx i)).1 * (e6RootVec (eSimpleIdx i)).1 = 0
    rw [← sq]
    exact e6RootVec_sq_zero (eSimpleIdx i)
  change (1 + c • E) * Y.1 * (1 + (-c) • E) =
    Y.1 + c • (E * Y.1 - Y.1 * E) +
      (c ^ 2 / 2) • (E * (E * Y.1 - Y.1 * E) - (E * Y.1 - Y.1 * E) * E)
  have hEEY : E * (E * Y.1) = 0 := by rw [← mul_assoc, hE2, zero_mul]
  have hYEE : Y.1 * E * E = 0 := by rw [mul_assoc, hE2, mul_zero]
  have had2 : E * (E * Y.1 - Y.1 * E) - (E * Y.1 - Y.1 * E) * E =
      (-2 : ℝ) • (E * (Y.1 * E)) := by
    simp only [mul_sub, sub_mul, hEEY, hYEE, zero_sub, sub_zero, mul_assoc]
    module
  have hconj : (1 + c • E) * Y.1 * (1 + (-c) • E) =
      Y.1 + c • (E * Y.1 - Y.1 * E) + (-(c ^ 2)) • (E * (Y.1 * E)) := by
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      smul_add, smul_smul, mul_assoc]
    rw [mul_comm (-c) c, mul_neg_self_eq_neg_sq c, neg_smul]
    module
  rw [had2, smul_smul, ← two_mul_half_sq c]
  exact hconj

end Adjoint78DBridge

end InfoGeometry.Algebra
