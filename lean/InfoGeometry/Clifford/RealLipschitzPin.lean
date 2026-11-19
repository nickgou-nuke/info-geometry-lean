/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.LipschitzWittRieszPrimary

/-!
# The mixed-signature real Pin group inside the Lipschitz group

Mathlib's `pinGroup Q` uses the Clifford-star normalization that, for its
vector generators, requires `Q v = -1`. That is appropriate for a negative
unit normal, but it excludes positive-norm normals in an indefinite quadratic
space. This file gives the real norm-`±1` Pin convention as a subgroup of the
already defined Lipschitz group and transports its action using the existing
twisted-conjugation homomorphism.

This is a repository extension using Mathlib's Clifford algebra; it does not
modify the pinned Mathlib sources.
-/

noncomputable section

namespace InfoGeometry.Clifford.RealLipschitzPin

open InfoGeometry.Clifford.LipschitzWittRieszPrimary

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)

/- The two real unit spinor norms, `+1` and `-1`. -/
def realUnitSigns : Subgroup ℝˣ where
  carrier := {u | (u : ℝ) = 1 ∨ (u : ℝ) = -1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    all_goals change ((a * b : ℝˣ) : ℝ) = 1 ∨ ((a * b : ℝˣ) : ℝ) = -1
    all_goals (simp only [Units.val_mul, ha, hb]; norm_num)
  inv_mem' := by
    intro a ha
    rcases ha with ha | ha
    · left
      change ((a⁻¹ : ℝˣ) : ℝ) = 1
      simp [ha]
    · right
      change ((a⁻¹ : ℝˣ) : ℝ) = -1
      simp [ha]

/- The real Pin subgroup consists of Lipschitz units with spinor norm `±1`.
It includes normalized vector generators of either quadratic sign. -/
def mixedPinGroup : Subgroup (lipschitzGroup Q) :=
  (realUnitSigns).comap (lipschitzSpinorNormHom Q)

@[simp] theorem mem_mixedPinGroup (g : lipschitzGroup Q) :
    g ∈ mixedPinGroup Q ↔
      (lipschitzSpinorNormHom Q g : ℝ) = 1 ∨
        (lipschitzSpinorNormHom Q g : ℝ) = -1 := Iff.rfl

/-- The mixed-signature Pin action is the restriction of the Lipschitz action. -/
def mixedPinToIsometryHom : mixedPinGroup Q →* Q.IsometryEquiv Q where
  toFun g := lipschitzGroupToIsometryHom Q g.1
  map_one' := map_one (lipschitzGroupToIsometryHom Q)
  map_mul' g h := map_mul (lipschitzGroupToIsometryHom Q) g.1 h.1

/-- The Lipschitz-group generator represented by a non-isotropic Clifford vector. -/
noncomputable def vectorLipschitz (v : M) [Invertible (Q v)] : lipschitzGroup Q :=
  let u : (CliffordAlgebra Q)ˣ :=
    ⟨CliffordAlgebra.ι Q v, CliffordAlgebra.ι Q (⅟(Q v) • v),
      by
        rw [map_smul, mul_smul_comm, CliffordAlgebra.ι_sq_scalar,
          Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul],
      by
        rw [map_smul, smul_mul_assoc, CliffordAlgebra.ι_sq_scalar,
          Algebra.algebraMap_eq_smul_one, smul_smul, invOf_mul_self, one_smul]⟩
  ⟨u, Subgroup.subset_closure ⟨v, rfl⟩⟩

@[simp] theorem vectorLipschitz_spinorNorm (v : M) [Invertible (Q v)] :
    (lipschitzSpinorNormHom Q (vectorLipschitz Q v) : ℝ) = Q v := by
  simpa [vectorLipschitz] using lipschitzSpinorNormHom_ι Q v

/-- A vector normalized to either quadratic sign is in the mixed Pin group. -/
def unitNormVector (v : M) (hv : Q v = 1 ∨ Q v = -1)
    [Invertible (Q v)] : mixedPinGroup Q := by
  refine ⟨vectorLipschitz Q v, ?_⟩
  rw [mem_mixedPinGroup, vectorLipschitz_spinorNorm]
  exact hv

/-- A vector of quadratic value `+1` is a mixed-Pin generator, in addition to
Mathlib's existing negative-unit generator. -/
def positiveUnitVector (v : M) (hv : Q v = 1)
    [Invertible (Q v)] : mixedPinGroup Q :=
  unitNormVector Q v (Or.inl hv)

/-- The twisted action of a positive-unit vector generator is the reflection in
its normal. -/
theorem positiveUnitVector_action (v : M) (hv : Q v = 1)
    [Invertible (Q v)] (x : M) :
    mixedPinToIsometryHom Q (positiveUnitVector Q v hv) x =
      realQuadraticReflection Q v (by rw [hv]; norm_num) x := by
  change lipschitzGroupToIsometryHom Q (positiveUnitVector Q v hv).1 x = _
  rw [show (positiveUnitVector Q v hv).1 = vectorLipschitz Q v by
    simp [positiveUnitVector, unitNormVector]
    ]
  have hrepr := (lipschitzGroupToIsometryHom_ι_eq_reflection Q v).1 x
  have hcoef : ⅟(Q v) * QuadraticMap.polar (⇑Q) v x =
      QuadraticMap.polar (⇑Q) x v / Q v := by
    rw [QuadraticMap.polar_comm, invOf_eq_inv, div_eq_mul_inv]
    ring
  rw [hcoef] at hrepr
  simpa [vectorLipschitz, hv] using hrepr

/-- The norm of an arbitrary anisotropic real vector can be normalized to one
of the two real Pin signs by scaling with `sqrt |Q v|`. -/
noncomputable def normalizeReflectionVector (v : M) : M :=
  (Real.sqrt |Q v|)⁻¹ • v

theorem normalizeReflectionVector_quadratic (v : M) (hv : Q v ≠ 0) :
    Q (normalizeReflectionVector Q v) = 1 ∨
      Q (normalizeReflectionVector Q v) = -1 := by
  have hroot : (Real.sqrt |Q v|) ^ 2 = |Q v| :=
    Real.sq_sqrt (abs_nonneg (Q v))
  have hscale : ((Real.sqrt |Q v|)⁻¹) ^ 2 = |Q v|⁻¹ := by
    have hsqrt : Real.sqrt |Q v| ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (abs_pos.mpr hv))
    field_simp [hsqrt]
    exact hroot.symm
  have hq : Q (normalizeReflectionVector Q v) =
      ((Real.sqrt |Q v|)⁻¹) ^ 2 * Q v := by
    rw [normalizeReflectionVector, QuadraticMap.map_smul]
    simp only [smul_eq_mul, pow_two]
  rw [hq, hscale]
  rcases lt_or_gt_of_ne hv with hneg | hposQ
  · right
    rw [abs_of_neg hneg]
    field_simp
  · left
    rw [abs_of_pos hposQ]
    field_simp

/-- A normalized vector of either sign acts as its orthogonal reflection. -/
theorem unitNormVector_action (v : M) (hv : Q v = 1 ∨ Q v = -1)
    [Invertible (Q v)] (x : M) :
    mixedPinToIsometryHom Q (unitNormVector Q v hv) x =
      realQuadraticReflection Q v (by rcases hv with h | h <;> rw [h] <;> norm_num) x := by
  change lipschitzGroupToIsometryHom Q (unitNormVector Q v hv).1 x = _
  change lipschitzGroupToIsometryHom Q (vectorLipschitz Q v) x = _
  have hrepr := (lipschitzGroupToIsometryHom_ι_eq_reflection Q v).1 x
  have hcoef : ⅟(Q v) * QuadraticMap.polar (⇑Q) v x =
      QuadraticMap.polar (⇑Q) x v / Q v := by
    rw [QuadraticMap.polar_comm, invOf_eq_inv, div_eq_mul_inv]
    ring
  rw [hcoef] at hrepr
  simpa [vectorLipschitz] using hrepr

/-- Every anisotropic real reflection lifts through the mixed-signature Pin
action. Normalization handles both signs of the quadratic value. -/
theorem mixedPin_reflection_lift (v : M) (hv : Q v ≠ 0) :
    ∃ g : mixedPinGroup Q,
      mixedPinToIsometryHom Q g = realQuadraticReflectionIsometry Q v hv := by
  let w := normalizeReflectionVector Q v
  have hw : Q w = 1 ∨ Q w = -1 := normalizeReflectionVector_quadratic Q v hv
  have hw0 : Q w ≠ 0 := by
    rcases hw with h | h <;> rw [h] <;> norm_num
  letI : Invertible (Q w) := invertibleOfNonzero hw0
  let g := unitNormVector Q w hw
  have hc : (Real.sqrt |Q v|)⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (abs_pos.mpr hv)))
  have hreflect : realQuadraticReflection Q w
      (by rcases hw with h | h <;> rw [h] <;> norm_num) =
      realQuadraticReflection Q v hv := by
    simpa [w, normalizeReflectionVector] using
      InfoGeometry.Clifford.LipschitzVectorAction.realQuadraticReflection_smul
        Q (Real.sqrt |Q v|)⁻¹ v hv hc
  refine ⟨g, ?_⟩
  apply DFunLike.ext
  intro x
  rw [unitNormVector_action, hreflect]
  rfl

/-- Under the orthogonal-spanning hypotheses used by Cartan--Dieudonné, the
mixed Pin action is onto the full quadratic-isometry group. -/
theorem mixedPinToIsometryHom_surjective_of_orthogonal_spanning
    {ι : Type*} [Fintype ι] (b : ι → M)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤)
    (hQ : ∀ i, Q (b i) ≠ 0)
    (horth : ∀ {i j}, i ≠ j → QuadraticMap.polar (⇑Q) (b i) (b j) = 0) :
    Function.Surjective (mixedPinToIsometryHom Q) := by
  classical
  let ρ := mixedPinToIsometryHom Q
  have hgen : realQuadraticReflectionSubgroup Q ≤ ρ.range := by
    change Subgroup.closure (realQuadraticReflectionSet Q) ≤ ρ.range
    rw [Subgroup.closure_le]
    intro f hf
    rcases hf with ⟨v, hv, rfl⟩
    obtain ⟨g, hg⟩ := mixedPin_reflection_lift Q v hv
    exact ⟨g, by
      apply DFunLike.ext
      intro x
      exact congrArg (fun e : Q.IsometryEquiv Q => e x) hg⟩
  have htop : realQuadraticReflectionSubgroup Q = ⊤ :=
    realQuadraticReflectionSubgroup_eq_top_of_orthogonal_spanning
      Q b hspan hQ horth
  have hrange : ρ.range = ⊤ := by
    apply top_unique
    rw [← htop]
    exact hgen
  intro f
  have hf : f ∈ ρ.range := by rw [hrange]; simp
  rcases hf with ⟨g, rfl⟩
  exact ⟨g, rfl⟩

end InfoGeometry.Clifford.RealLipschitzPin
