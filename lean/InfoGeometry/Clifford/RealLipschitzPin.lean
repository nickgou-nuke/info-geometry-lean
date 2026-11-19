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

/-- The two real unit spinor norms, `+1` and `-1`. -/
def realUnitSigns : Subgroup ℝˣ where
  carrier := {u | (u : ℝ) = 1 ∨ (u : ℝ) = -1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp [ha, hb]
  inv_mem' := by
    intro a ha
    rcases ha with ha | ha
    · left
      apply Units.ext
      simp [ha]
    · right
      apply Units.ext
      simp [ha]

/-- The real Pin subgroup consists of Lipschitz units with spinor norm `±1`.
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
  map_mul' := map_mul (lipschitzGroupToIsometryHom Q)

/-- A vector of quadratic value `+1` is a mixed-Pin generator, in addition to
Mathlib's existing negative-unit generator. -/
def positiveUnitVector (v : M) (hv : Q v = 1) : mixedPinGroup Q := by
  classical
  let _ : Invertible (Q v) := by rw [hv]; infer_instance
  let u : (CliffordAlgebra Q)ˣ :=
    (CliffordAlgebra.isUnit_ι_of_isUnit Q
      ⟨Units.mk0 (Q v) (by rw [hv]; norm_num), rfl⟩).unit
  let g : lipschitzGroup Q := ⟨u, Subgroup.subset_closure ⟨v, by
    exact (CliffordAlgebra.isUnit_ι_of_isUnit Q
      ⟨Units.mk0 (Q v) (by rw [hv]; norm_num), rfl⟩).unit_spec.symm⟩⟩
  have hnorm : (lipschitzSpinorNormHom Q g : ℝ) = 1 := by
    simpa [g, u] using lipschitzSpinorNormHom_ι Q v
  exact ⟨g, Or.inl hnorm⟩

/-- The twisted action of a positive-unit vector generator is the reflection in
its normal. -/
theorem positiveUnitVector_action (v : M) (hv : Q v = 1) (x : M) :
    mixedPinToIsometryHom Q (positiveUnitVector Q v hv) x =
      realQuadraticReflection Q v (by rw [hv]; norm_num) x := by
  classical
  let _ : Invertible (Q v) := by rw [hv]; infer_instance
  let u : (CliffordAlgebra Q)ˣ :=
    (CliffordAlgebra.isUnit_ι_of_isUnit Q
      ⟨Units.mk0 (Q v) (by rw [hv]; norm_num), rfl⟩).unit
  let g : lipschitzGroup Q := ⟨u, Subgroup.subset_closure ⟨v, by
    exact (CliffordAlgebra.isUnit_ι_of_isUnit Q
      ⟨Units.mk0 (Q v) (by rw [hv]; norm_num), rfl⟩).unit_spec.symm⟩⟩
  change lipschitzGroupToIsometryHom Q (positiveUnitVector Q v hv).1 x = _
  change lipschitzGroupToIsometryHom Q g x = _
  have hrepr := (lipschitzGroupToIsometryHom_ι_eq_reflection Q v).1 x
  simpa [g, u, hv, realQuadraticReflection_apply] using hrepr

end InfoGeometry.Clifford.RealLipschitzPin
