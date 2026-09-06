import InfoGeometry.Lie.CanonicalZornCartanRootReflections
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

end InfoGeometry.Lie.CanonicalZornG2CoxeterRelations
