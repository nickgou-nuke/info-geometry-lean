import InfoGeometry.Lie.CanonicalZornCartanRootReflections
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2WeylDihedralEquiv
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Coxeter relations for the native G₂ Cartan reflections

This is a thin owner-level facade over the verified native reflection
identities.  It deliberately stays on `TracelessWeight`; it does not identify
this carrier with the paired Cartan/parameter subgroup.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CoxeterRelations

open InfoGeometry.Lie.CanonicalZornCartanRootReflections
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

abbrev Cartan := TracelessWeight

def g2CoxeterMatrix : CoxeterMatrix (Fin 2) := CoxeterMatrix.G₂

@[simp] theorem g2CoxeterMatrix_diag (i : Fin 2) :
    g2CoxeterMatrix i i = 1 := by
  fin_cases i <;> rfl

@[simp] theorem g2CoxeterMatrix_off_diag (i j : Fin 2) (h : i ≠ j) :
    g2CoxeterMatrix i j = 6 := by
  fin_cases i <;> fin_cases j <;> simp_all [g2CoxeterMatrix, CoxeterMatrix.G₂]

def shortGenerator : Cartan →ₗ[ℝ] Cartan := shortReflectionOnCartan

def longGenerator : Cartan →ₗ[ℝ] Cartan := longReflectionOnCartan

theorem shortGenerator_sq :
    shortGenerator.comp shortGenerator = LinearMap.id := by
  exact shortReflectionOnCartan_sq

theorem longGenerator_sq :
    longGenerator.comp longGenerator = LinearMap.id := by
  exact longReflectionOnCartan_sq

def shortReflectionEquiv : Cartan ≃ₗ[ℝ] Cartan :=
  LinearEquiv.ofInvolutive shortGenerator (by
    intro x
    exact congrArg (fun f => f x) shortGenerator_sq)

def longReflectionEquiv : Cartan ≃ₗ[ℝ] Cartan :=
  LinearEquiv.ofInvolutive longGenerator (by
    intro x
    exact congrArg (fun f => f x) longGenerator_sq)

def g2ReflectionEquivalents : Fin 2 → Cartan ≃ₗ[ℝ] Cartan
  | 0 => shortReflectionEquiv
  | 1 => longReflectionEquiv

@[simp] theorem shortReflectionEquiv_toLinearMap :
    shortReflectionEquiv.toLinearMap = shortGenerator := by
  rfl

@[simp] theorem longReflectionEquiv_toLinearMap :
    longReflectionEquiv.toLinearMap = longGenerator := by
  rfl

theorem shortReflectionEquiv_mul_longReflectionEquiv_toLinearMap :
    (shortReflectionEquiv * longReflectionEquiv).toLinearMap =
      shortGenerator.comp longGenerator := by
  rfl

theorem shortReflectionEquiv_sq : shortReflectionEquiv ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro x
  exact congrArg (fun f => f x) shortGenerator_sq

theorem longReflectionEquiv_sq : longReflectionEquiv ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro x
  exact congrArg (fun f => f x) longGenerator_sq

def cartanWeylSubgroup : Subgroup (Cartan ≃ₗ[ℝ] Cartan) :=
  Subgroup.closure ({shortReflectionEquiv, longReflectionEquiv} :
    Set (Cartan ≃ₗ[ℝ] Cartan))

theorem shortReflectionEquiv_mem_cartanWeylSubgroup :
    shortReflectionEquiv ∈ cartanWeylSubgroup := by
  exact Subgroup.subset_closure (by simp)

theorem longReflectionEquiv_mem_cartanWeylSubgroup :
    longReflectionEquiv ∈ cartanWeylSubgroup := by
  exact Subgroup.subset_closure (by simp)

def g2ReflectionGenerators : Fin 2 → cartanWeylSubgroup
  | 0 => ⟨shortReflectionEquiv, shortReflectionEquiv_mem_cartanWeylSubgroup⟩
  | 1 => ⟨longReflectionEquiv, longReflectionEquiv_mem_cartanWeylSubgroup⟩

def coxeterRotation : Cartan ≃ₗ[ℝ] Cartan :=
  shortReflectionEquiv * longReflectionEquiv

def coxeterRotationPower (k : ZMod 6) : cartanWeylSubgroup :=
  ⟨coxeterRotation ^ k.val, Subgroup.pow_mem cartanWeylSubgroup
    (Subgroup.mul_mem cartanWeylSubgroup
      shortReflectionEquiv_mem_cartanWeylSubgroup
      longReflectionEquiv_mem_cartanWeylSubgroup) _⟩

def reflectionNormalForm (k : ZMod 6) : cartanWeylSubgroup :=
  ⟨shortReflectionEquiv * coxeterRotation ^ k.val,
    Subgroup.mul_mem cartanWeylSubgroup
      shortReflectionEquiv_mem_cartanWeylSubgroup
      (Subgroup.pow_mem cartanWeylSubgroup
        (Subgroup.mul_mem cartanWeylSubgroup
          shortReflectionEquiv_mem_cartanWeylSubgroup
          longReflectionEquiv_mem_cartanWeylSubgroup) _)⟩

def dihedralNormalForm : DihedralGroup 6 → cartanWeylSubgroup
  | .r k => coxeterRotationPower k
  | .sr k => reflectionNormalForm k

@[simp] theorem dihedralNormalForm_r (k : ZMod 6) :
    dihedralNormalForm (.r k) = coxeterRotationPower k := rfl

@[simp] theorem dihedralNormalForm_sr (k : ZMod 6) :
    dihedralNormalForm (.sr k) = reflectionNormalForm k := rfl

@[simp] theorem coxeterRotationPower_zero :
    coxeterRotationPower 0 = 1 := by
  apply Subtype.ext
  simp [coxeterRotationPower]

theorem coxeterRotationPower_add_of_lt (i j : ZMod 6)
    (h : i.val + j.val < 6) :
    coxeterRotationPower (i + j) =
      coxeterRotationPower i * coxeterRotationPower j := by
  apply Subtype.ext
  simp only [coxeterRotationPower, coxeterRotation, ZMod.val_add]
  rw [Nat.mod_eq_of_lt h, pow_add]
  rfl

theorem reflectionNormalForm_mul_coxeterRotationPower_of_lt (i j : ZMod 6)
    (h : i.val + j.val < 6) :
    reflectionNormalForm i * coxeterRotationPower j =
      reflectionNormalForm (i + j) := by
  apply Subtype.ext
  simp only [reflectionNormalForm, coxeterRotationPower, coxeterRotation,
    ZMod.val_add]
  rw [Nat.mod_eq_of_lt h, pow_add]
  rfl

@[simp] theorem reflectionNormalForm_zero :
    reflectionNormalForm 0 =
      ⟨shortReflectionEquiv, shortReflectionEquiv_mem_cartanWeylSubgroup⟩ := by
  apply Subtype.ext
  simp [reflectionNormalForm]

@[simp] theorem dihedralNormalForm_r_zero :
    dihedralNormalForm (.r 0) = 1 := by
  exact coxeterRotationPower_zero

@[simp] theorem dihedralNormalForm_sr_zero :
    dihedralNormalForm (.sr 0) =
      ⟨shortReflectionEquiv, shortReflectionEquiv_mem_cartanWeylSubgroup⟩ := by
  exact reflectionNormalForm_zero

theorem shortReflectionEquiv_longReflectionEquiv_braid :
    (shortReflectionEquiv * longReflectionEquiv) ^ 3 =
      (longReflectionEquiv * shortReflectionEquiv) ^ 3 := by
  apply LinearEquiv.ext
  intro x
  change ((shortGenerator.comp longGenerator) ^ 3) x =
    ((longGenerator.comp shortGenerator) ^ 3) x
  exact congrArg (fun f : Cartan →ₗ[ℝ] Cartan => f x)
    nativeCartanReflectionsOnCartan_braid

theorem shortReflectionEquiv_longReflectionEquiv_order_six :
    (shortReflectionEquiv * longReflectionEquiv) ^ 6 = 1 := by
  let q := shortReflectionEquiv * longReflectionEquiv
  have hs : shortReflectionEquiv⁻¹ = shortReflectionEquiv := by
    apply (inv_eq_iff_mul_eq_one).2
    exact shortReflectionEquiv_sq
  have hl : longReflectionEquiv⁻¹ = longReflectionEquiv := by
    apply (inv_eq_iff_mul_eq_one).2
    exact longReflectionEquiv_sq
  have hqinv : q⁻¹ = longReflectionEquiv * shortReflectionEquiv := by
    simp [q, mul_inv_rev, hs, hl]
  have hq3 : q ^ 3 = (q⁻¹) ^ 3 := by
    simpa [q, hqinv] using shortReflectionEquiv_longReflectionEquiv_braid
  calc
    q ^ 6 = q ^ 3 * q ^ 3 := by rw [← pow_add]
    _ = q ^ 3 * (q⁻¹) ^ 3 := by rw [hq3]
    _ = 1 := by
      have h := congrArg (fun x => x ^ 3) (mul_inv_cancel q)
      change (q * q⁻¹) ^ 3 = 1 at h
      exact (Commute.mul_pow (Commute.inv_right (Commute.refl q)) 3).symm ▸ h

theorem shortGenerator_longGenerator_braid :
    (shortGenerator.comp longGenerator) ^ 3 =
      (longGenerator.comp shortGenerator) ^ 3 := by
  exact nativeCartanReflectionsOnCartan_braid

theorem shortGenerator_longGenerator_order_six :
    (shortGenerator.comp longGenerator) ^ 6 = LinearMap.id := by
  exact nativeCartanReflectionsOnCartan_order_six

theorem longReflectionEquiv_shortReflectionEquiv_order_six :
    (longReflectionEquiv * shortReflectionEquiv) ^ 6 = 1 := by
  have h := shortReflectionEquiv_longReflectionEquiv_order_six
  have hi : ((shortReflectionEquiv * longReflectionEquiv)⁻¹) ^ 6 = 1 := by
    rw [inv_pow, h, inv_one]
  simpa [mul_inv_rev] using hi

theorem g2ReflectionGenerators_isLiftable :
    g2CoxeterMatrix.IsLiftable g2ReflectionGenerators := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [g2ReflectionGenerators] using shortReflectionEquiv_sq
  · simpa [g2ReflectionGenerators, g2CoxeterMatrix] using
      shortReflectionEquiv_longReflectionEquiv_order_six
  · simpa [g2ReflectionGenerators, g2CoxeterMatrix] using
      longReflectionEquiv_shortReflectionEquiv_order_six
  · simpa [g2ReflectionGenerators] using longReflectionEquiv_sq

noncomputable def g2CoxeterToCartanHom :
    g2CoxeterMatrix.Group →* cartanWeylSubgroup :=
  g2CoxeterMatrix.toCoxeterSystem.lift
    ⟨g2ReflectionGenerators, g2ReflectionGenerators_isLiftable⟩

@[simp] theorem g2CoxeterToCartanHom_apply_simple (i : Fin 2) :
    g2CoxeterToCartanHom (g2CoxeterMatrix.simple i) =
      g2ReflectionGenerators i := by
  exact CoxeterSystem.lift_apply_simple
    g2CoxeterMatrix.toCoxeterSystem
    g2ReflectionGenerators_isLiftable i

theorem g2CoxeterToCartanHom_surjective :
    Function.Surjective g2CoxeterToCartanHom := by
  intro x
  rcases @Subgroup.closure_induction (Cartan ≃ₗ[ℝ] Cartan) _
    {shortReflectionEquiv, longReflectionEquiv}
    (fun g _ => ∃ a, (g2CoxeterToCartanHom a).1 = g)
    (by
      intro g hg
      rcases hg with rfl | rfl
      · exact ⟨g2CoxeterMatrix.simple 0, by
          exact congrArg Subtype.val
            (g2CoxeterToCartanHom_apply_simple 0)⟩
      · exact ⟨g2CoxeterMatrix.simple 1, by
          exact congrArg Subtype.val
            (g2CoxeterToCartanHom_apply_simple 1)⟩)
    (by exact ⟨1, rfl⟩)
    (by
      intro g h _ _ hg hh
      rcases hg with ⟨a, ha⟩
      rcases hh with ⟨b, hb⟩
      exact ⟨a * b, by simp [ha, hb]⟩)
    (by
      intro g _ hg
      rcases hg with ⟨a, ha⟩
      exact ⟨a⁻¹, by simp [ha]⟩)
    x.1 x.2 with ⟨a, ha⟩
  exact ⟨a, Subtype.ext ha⟩

/- The canonical quotient map to the rank-two dihedral presentation.  The
   images of the two simple generators are the two reflections `sr 0` and
   `sr 1`; their product is the rotation `r 1`. -/
noncomputable def g2CoxeterToDihedralHom :
    g2CoxeterMatrix.Group →* DihedralGroup 6 := by
  let f : Fin 2 → DihedralGroup 6
    | 0 => .sr 0
    | 1 => .sr 1
  refine PresentedGroup.toGroup (f := f) ?_
  intro rel hrel
  rcases hrel with ⟨⟨i, j⟩, rfl⟩
  fin_cases i <;> fin_cases j
  · simp [CoxeterMatrix.relation, f]
  · simp [CoxeterMatrix.relation, f]
    convert (DihedralGroup.r_one_pow_n (n := 6)) using 1
  · simp [CoxeterMatrix.relation, f]
    convert (DihedralGroup.r_one_pow_n (n := 6)) using 1
  · simp [CoxeterMatrix.relation, f]

@[simp] theorem g2CoxeterToDihedralHom_apply_simple (i : Fin 2) :
    g2CoxeterToDihedralHom (g2CoxeterMatrix.simple i) =
      match i with
      | 0 => .sr 0
      | 1 => .sr 1 := by
  fin_cases i
  · simp only [CoxeterMatrix.simple, g2CoxeterToDihedralHom,
      PresentedGroup.toGroup]
    rfl
  · simp only [CoxeterMatrix.simple, g2CoxeterToDihedralHom,
      PresentedGroup.toGroup]
    rfl

theorem g2CoxeterToDihedralHom_surjective :
    Function.Surjective g2CoxeterToDihedralHom := by
  intro x
  cases x with
  | r k =>
      refine ⟨(g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val, ?_⟩
      rw [map_pow]
      simp [DihedralGroup.sr_mul_sr, DihedralGroup.r_pow]
  | sr k =>
      refine ⟨g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val, ?_⟩
      rw [map_mul, map_pow]
      simp [DihedralGroup.sr_mul_sr, DihedralGroup.r_pow]

theorem g2Coxeter_generated_by_simple :
    Subgroup.closure (Set.range (g2CoxeterMatrix.simple : Fin 2 →
      g2CoxeterMatrix.Group)) = ⊤ := by
  exact PresentedGroup.closure_range_of g2CoxeterMatrix.relationsSet

theorem g2Coxeter_simple_product_order_six :
    (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ 6 = 1 := by
  simpa [g2CoxeterMatrix] using
    (CoxeterSystem.simple_mul_simple_pow
      g2CoxeterMatrix.toCoxeterSystem 0 1)

theorem g2Coxeter_simple_product_power_add (i j : ZMod 6) :
    (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ (i + j).val =
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ i.val *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ j.val := by
  have hmod : (i + j).val ≡ i.val + j.val [MOD 6] := by
    simp [Nat.ModEq, ZMod.val_add, Nat.add_mod]
  simpa [pow_add] using
    (pow_eq_pow_of_modEq hmod g2Coxeter_simple_product_order_six)

theorem g2Coxeter_simple_product_power_neg (k : ZMod 6) :
    (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ (-k).val =
      ((g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have hmod : (-k).val + k.val ≡ 0 [MOD 6] := by
    have h := congrArg ZMod.val (neg_add_cancel k)
    change ((-k).val + k.val) % 6 = 0
    exact h
  have hpow := pow_eq_pow_of_modEq hmod
    g2Coxeter_simple_product_order_six
  rw [pow_add] at hpow
  calc
    (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ (-k).val =
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ (-k).val *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val :=
          by
            have hcomm : Commute
                ((g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val)
                ((g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ (-k).val) :=
              (Commute.refl
                (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1)).pow_pow
                k.val (-k).val
            exact hcomm.eq
    _ = 1 := hpow

theorem g2Coxeter_simple_zero_conj_rotation :
    g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) *
          g2CoxeterMatrix.simple 0 =
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1)⁻¹ := by
  have hs := CoxeterSystem.simple_sq g2CoxeterMatrix.toCoxeterSystem 0
  have ht := CoxeterSystem.simple_sq g2CoxeterMatrix.toCoxeterSystem 1
  have hs' : g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 0 = 1 := by
    simpa [pow_two] using hs
  have ht' : g2CoxeterMatrix.simple 1 * g2CoxeterMatrix.simple 1 = 1 := by
    simpa [pow_two] using ht
  have hi0 : (g2CoxeterMatrix.simple 0)⁻¹ = g2CoxeterMatrix.simple 0 := by
    exact CoxeterSystem.inv_simple g2CoxeterMatrix.toCoxeterSystem 0
  have hi1 : (g2CoxeterMatrix.simple 1)⁻¹ = g2CoxeterMatrix.simple 1 := by
    exact CoxeterSystem.inv_simple g2CoxeterMatrix.toCoxeterSystem 1
  calc
    g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) *
          g2CoxeterMatrix.simple 0 =
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 0) *
        g2CoxeterMatrix.simple 1 * g2CoxeterMatrix.simple 0 := by
          simp [mul_assoc]
    _ = g2CoxeterMatrix.simple 1 * g2CoxeterMatrix.simple 0 := by
      rw [hs']
      simp
    _ = (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1)⁻¹ := by
      simp [mul_inv_rev, hi0, hi1]

theorem g2Coxeter_simple_zero_mul_rotation :
    g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) =
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1)⁻¹ *
        g2CoxeterMatrix.simple 0 := by
  have hs := CoxeterSystem.simple_sq g2CoxeterMatrix.toCoxeterSystem 0
  have hs' : g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 0 = 1 := by
    simpa [pow_two] using hs
  have h := g2Coxeter_simple_zero_conj_rotation
  calc
    g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) =
      (g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) *
          g2CoxeterMatrix.simple 0) *
            g2CoxeterMatrix.simple 0 := by
          simp [mul_assoc, hs']
    _ = (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1)⁻¹ *
          g2CoxeterMatrix.simple 0 := by
            rw [h]

theorem g2Coxeter_rotation_pow_mul_simple_zero (n : ℕ) :
    (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ n *
        g2CoxeterMatrix.simple 0 =
      g2CoxeterMatrix.simple 0 *
        ((g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1)⁻¹) ^ n := by
  have hs := CoxeterSystem.simple_sq g2CoxeterMatrix.toCoxeterSystem 0
  have hs' : g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 0 = 1 := by
    simpa [pow_two] using hs
  have hstep :
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) *
          g2CoxeterMatrix.simple 0 =
        g2CoxeterMatrix.simple 0 *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1)⁻¹ := by
    calc
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) *
          g2CoxeterMatrix.simple 0 =
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 0) *
          ((g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) *
            g2CoxeterMatrix.simple 0) := by simp [mul_assoc, hs']
      _ = g2CoxeterMatrix.simple 0 *
          (g2CoxeterMatrix.simple 0 *
            (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) *
              g2CoxeterMatrix.simple 0) := by simp [mul_assoc]
      _ = g2CoxeterMatrix.simple 0 *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1)⁻¹ := by
            rw [g2Coxeter_simple_zero_conj_rotation]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_assoc, hstep, ← mul_assoc, ih]
      simp [pow_succ, mul_assoc]

theorem g2Coxeter_rotation_pow_mul_simple_one (n : ℕ) :
    (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ n *
        g2CoxeterMatrix.simple 1 =
      g2CoxeterMatrix.simple 0 *
        ((g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1)⁻¹) ^ n *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) := by
  have hs := CoxeterSystem.simple_sq g2CoxeterMatrix.toCoxeterSystem 0
  have hs' : g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 0 = 1 := by
    simpa [pow_two] using hs
  have hsc : g2CoxeterMatrix.simple 0 *
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) =
      g2CoxeterMatrix.simple 1 := by
    rw [← mul_assoc, hs', one_mul]
  calc
    (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ n *
        g2CoxeterMatrix.simple 1 =
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ n *
        (g2CoxeterMatrix.simple 0 *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1)) := by
            rw [hsc]
    _ = ((g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ n *
        g2CoxeterMatrix.simple 0) *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) := by
            simp [mul_assoc]
    _ = (g2CoxeterMatrix.simple 0 *
        ((g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1)⁻¹) ^ n) *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) := by
            rw [g2Coxeter_rotation_pow_mul_simple_zero]
    _ = g2CoxeterMatrix.simple 0 *
        ((g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1)⁻¹) ^ n *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) := by
            simp [mul_assoc]

theorem g2Coxeter_rotation_power_mul_simple_zero_normal_form (k : ZMod 6) :
    ∃ j : ZMod 6,
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val *
          g2CoxeterMatrix.simple 0 =
        g2CoxeterMatrix.simple 0 *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ j.val := by
  refine ⟨-k, ?_⟩
  rw [g2Coxeter_rotation_pow_mul_simple_zero, inv_pow]
  rw [← g2Coxeter_simple_product_power_neg k]

theorem g2Coxeter_rotation_power_mul_simple_one_normal_form (k : ZMod 6) :
    ∃ j : ZMod 6,
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val *
          g2CoxeterMatrix.simple 1 =
        g2CoxeterMatrix.simple 0 *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ j.val := by
  refine ⟨1 - k, ?_⟩
  rw [g2Coxeter_rotation_pow_mul_simple_one, inv_pow]
  rw [← g2Coxeter_simple_product_power_neg k]
  have h := g2Coxeter_simple_product_power_add (-k) 1
  have h' :
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^
          (-k + 1).val =
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ (-k).val *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) := by
    simpa [pow_one] using h
  calc
    g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ (-k).val *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) =
      g2CoxeterMatrix.simple 0 *
        ((g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ (-k).val *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1)) := by
            simp [mul_assoc]
    _ = g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ (-k + 1).val := by
          rw [h']
    _ = g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ (1 - k).val := by
          have hk : 1 - k = -k + 1 := by abel
          rw [hk]

theorem g2Coxeter_normal_form_mul_simple_zero
    {x : g2CoxeterMatrix.Group}
    (hx : (∃ k : ZMod 6, x =
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val) ∨
      (∃ k : ZMod 6, x = g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val)) :
    (∃ k : ZMod 6, x * g2CoxeterMatrix.simple 0 =
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val) ∨
      (∃ k : ZMod 6, x * g2CoxeterMatrix.simple 0 = g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val) := by
  rcases hx with hx | hx
  · obtain ⟨k, rfl⟩ := hx
    right
    exact g2Coxeter_rotation_power_mul_simple_zero_normal_form k
  · obtain ⟨k, rfl⟩ := hx
    left
    obtain ⟨j, hj⟩ := g2Coxeter_rotation_power_mul_simple_zero_normal_form k
    refine ⟨j, ?_⟩
    rw [mul_assoc, hj]
    have hs := CoxeterSystem.simple_sq g2CoxeterMatrix.toCoxeterSystem 0
    have hs' : g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 0 = 1 := by
      simpa [pow_two] using hs
    rw [← mul_assoc, hs', one_mul]

theorem g2Coxeter_normal_form_mul_simple_one
    {x : g2CoxeterMatrix.Group}
    (hx : (∃ k : ZMod 6, x =
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val) ∨
      (∃ k : ZMod 6, x = g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val)) :
    (∃ k : ZMod 6, x * g2CoxeterMatrix.simple 1 =
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val) ∨
      (∃ k : ZMod 6, x * g2CoxeterMatrix.simple 1 = g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val) := by
  rcases hx with hx | hx
  · obtain ⟨k, rfl⟩ := hx
    right
    exact g2Coxeter_rotation_power_mul_simple_one_normal_form k
  · obtain ⟨k, rfl⟩ := hx
    obtain ⟨j, hj⟩ := g2Coxeter_rotation_power_mul_simple_one_normal_form k
    left
    refine ⟨j, ?_⟩
    rw [mul_assoc, hj]
    have hs := CoxeterSystem.simple_sq g2CoxeterMatrix.toCoxeterSystem 0
    have hs' : g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 0 = 1 := by
      simpa [pow_two] using hs
    rw [← mul_assoc, hs', one_mul]

theorem g2Coxeter_normal_form (w : g2CoxeterMatrix.Group) :
    (∃ k : ZMod 6, w =
      (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val) ∨
      (∃ k : ZMod 6, w = g2CoxeterMatrix.simple 0 *
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val) := by
  apply g2CoxeterMatrix.toCoxeterSystem.simple_induction_right w
  · exact Or.inl ⟨0, by simp⟩
  · intro x i hx
    fin_cases i
    · exact g2Coxeter_normal_form_mul_simple_zero hx
    · exact g2Coxeter_normal_form_mul_simple_one hx

theorem cartanWeylSubgroup_normal_form
    (x : cartanWeylSubgroup) :
    (∃ k : ZMod 6, x = coxeterRotationPower k) ∨
      (∃ k : ZMod 6, x = reflectionNormalForm k) := by
  rcases g2CoxeterToCartanHom_surjective x with ⟨a, ha⟩
  rcases g2Coxeter_normal_form a with h | h
  · rcases h with ⟨k, hk⟩
    left
    refine ⟨k, ?_⟩
    apply Subtype.ext
    rw [← ha, hk]
    simp [coxeterRotationPower, coxeterRotation, g2ReflectionGenerators]
  · rcases h with ⟨k, hk⟩
    right
    refine ⟨k, ?_⟩
    apply Subtype.ext
    rw [← ha, hk]
    simp [reflectionNormalForm, coxeterRotation, g2ReflectionGenerators]

theorem dihedralNormalForm_surjective :
    Function.Surjective dihedralNormalForm := by
  intro x
  rcases cartanWeylSubgroup_normal_form x with h | h
  · rcases h with ⟨k, hk⟩
    refine ⟨.r k, ?_⟩
    simpa using hk.symm
  · rcases h with ⟨k, hk⟩
    refine ⟨.sr k, ?_⟩
    simpa using hk.symm

theorem g2CoxeterToDihedralHom_injective :
    Function.Injective g2CoxeterToDihedralHom := by
  intro x y hxy
  rcases g2Coxeter_normal_form x with hx | hx <;>
    rcases g2Coxeter_normal_form y with hy | hy
  · obtain ⟨k, rfl⟩ := hx
    obtain ⟨l, rfl⟩ := hy
    have hkl : k = l := by
      apply ZMod.val_injective 6
      have hmap' : DihedralGroup.r k = DihedralGroup.r l := by
        rw [map_pow, map_pow, map_mul,
          g2CoxeterToDihedralHom_apply_simple 0,
          g2CoxeterToDihedralHom_apply_simple 1] at hxy
        simpa [DihedralGroup.sr_mul_sr, DihedralGroup.r_pow] using hxy
      simpa using congrArg ZMod.val (DihedralGroup.r.inj hmap')
    simp [hkl]
  · obtain ⟨k, rfl⟩ := hx
    obtain ⟨l, rfl⟩ := hy
    have hfalse := congrArg (fun z => match z with
      | DihedralGroup.r _ => True
      | DihedralGroup.sr _ => False) hxy
    simp at hfalse
  · obtain ⟨k, rfl⟩ := hx
    obtain ⟨l, rfl⟩ := hy
    have hfalse := congrArg (fun z => match z with
      | DihedralGroup.r _ => False
      | DihedralGroup.sr _ => True) hxy
    simp at hfalse
  · obtain ⟨k, rfl⟩ := hx
    obtain ⟨l, rfl⟩ := hy
    have hkl : k = l := by
      apply ZMod.val_injective 6
      have hmap' : DihedralGroup.sr k = DihedralGroup.sr l := by
        rw [map_mul, map_pow, map_mul,
          g2CoxeterToDihedralHom_apply_simple 0,
          g2CoxeterToDihedralHom_apply_simple 1] at hxy
        simpa [DihedralGroup.sr_mul_sr, DihedralGroup.r_pow] using hxy
      simpa using congrArg ZMod.val (DihedralGroup.sr.inj hmap')
    simp [hkl]

noncomputable def g2CoxeterToDihedralEquiv :
    g2CoxeterMatrix.Group ≃* DihedralGroup 6 :=
  MulEquiv.ofBijective g2CoxeterToDihedralHom
    ⟨g2CoxeterToDihedralHom_injective, g2CoxeterToDihedralHom_surjective⟩

noncomputable def dihedralToCartanHom :
    DihedralGroup 6 →* cartanWeylSubgroup :=
  g2CoxeterToCartanHom.comp g2CoxeterToDihedralEquiv.symm.toMonoidHom

theorem g2CoxeterToCartanHom_factorization (w : g2CoxeterMatrix.Group) :
    g2CoxeterToCartanHom w =
      dihedralToCartanHom (g2CoxeterToDihedralEquiv w) := by
  simp [dihedralToCartanHom]

theorem dihedralNormalForm_eq_dihedralToCartanHom (d : DihedralGroup 6) :
    dihedralNormalForm d = dihedralToCartanHom d := by
  cases d with
  | r k =>
    have hk : g2CoxeterToDihedralEquiv.symm (.r k) =
        (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val := by
      apply g2CoxeterToDihedralEquiv.injective
      rw [g2CoxeterToDihedralEquiv.apply_symm_apply]
      change .r k = g2CoxeterToDihedralHom
        ((g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val)
      rw [map_pow, map_mul, g2CoxeterToDihedralHom_apply_simple]
      simp [DihedralGroup.sr_mul_sr, DihedralGroup.r_pow]
    simp [dihedralNormalForm, coxeterRotationPower, coxeterRotation,
      dihedralToCartanHom, hk, g2CoxeterToCartanHom_apply_simple,
      g2ReflectionGenerators]
  | sr k =>
    have hk : g2CoxeterToDihedralEquiv.symm (.sr k) =
        g2CoxeterMatrix.simple 0 *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val := by
      apply g2CoxeterToDihedralEquiv.injective
      rw [g2CoxeterToDihedralEquiv.apply_symm_apply]
      change .sr k = g2CoxeterToDihedralHom
        (g2CoxeterMatrix.simple 0 *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val)
      rw [map_mul, map_pow, map_mul,
        g2CoxeterToDihedralHom_apply_simple]
      simp [DihedralGroup.sr_mul_sr, DihedralGroup.r_pow]
    simp [dihedralNormalForm, reflectionNormalForm, coxeterRotation,
      dihedralToCartanHom, hk, g2CoxeterToCartanHom_apply_simple,
      g2ReflectionGenerators]

@[simp] theorem dihedralToCartanHom_sr_zero :
    dihedralToCartanHom (.sr 0) =
      ⟨shortReflectionEquiv, shortReflectionEquiv_mem_cartanWeylSubgroup⟩ := by
  rw [← dihedralNormalForm_eq_dihedralToCartanHom]
  exact dihedralNormalForm_sr_zero

@[simp] theorem dihedralToCartanHom_sr_one :
    dihedralToCartanHom (.sr 1) =
      ⟨shortReflectionEquiv * coxeterRotation,
        Subgroup.mul_mem cartanWeylSubgroup
          shortReflectionEquiv_mem_cartanWeylSubgroup
          (Subgroup.mul_mem cartanWeylSubgroup
            shortReflectionEquiv_mem_cartanWeylSubgroup
            longReflectionEquiv_mem_cartanWeylSubgroup)⟩ := by
  rw [← dihedralNormalForm_eq_dihedralToCartanHom]
  rfl

theorem dihedralToCartanHom_surjective :
    Function.Surjective dihedralToCartanHom := by
  intro x
  rcases dihedralNormalForm_surjective x with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  rw [← dihedralNormalForm_eq_dihedralToCartanHom]
  exact hd

noncomputable def g2CoxeterToWeylSubgroupHom :
    g2CoxeterMatrix.Group →*
      InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.weylG2Subgroup :=
  InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylMulEquiv.toMonoidHom.comp
    g2CoxeterToDihedralHom

@[simp] theorem g2CoxeterToWeylSubgroupHom_apply_simple (i : Fin 2) :
    g2CoxeterToWeylSubgroupHom (g2CoxeterMatrix.simple i) =
      InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylMulEquiv
      (match i with
        | 0 => DihedralGroup.sr 0
        | 1 => DihedralGroup.sr 1) := by
  fin_cases i <;>
    simp [g2CoxeterToWeylSubgroupHom,
      g2CoxeterToDihedralHom_apply_simple]

theorem g2CoxeterToWeylSubgroupHom_surjective :
    Function.Surjective g2CoxeterToWeylSubgroupHom := by
  intro w
  obtain ⟨d, hd⟩ :=
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylMulEquiv.surjective w
  obtain ⟨c, hc⟩ := g2CoxeterToDihedralHom_surjective d
  refine ⟨c, ?_⟩
  change InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.dihedralWeylMulEquiv
      (g2CoxeterToDihedralHom c) = w
  rw [hc, hd]

end InfoGeometry.Lie.CanonicalZornG2CoxeterRelations
