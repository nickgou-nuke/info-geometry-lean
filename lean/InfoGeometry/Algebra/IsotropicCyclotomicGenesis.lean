/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic.NoncommRing

/-! # Isotropic generation of orthogonal idempotents

Start from square-zero elements rather than assuming a Peirce idempotent.
Orthogonal products arise unconditionally; idempotency requires the explicit
regular-pair equations.
-/

namespace InfoGeometry.Algebra.IsotropicCyclotomicGenesis

variable {B : Type*} [Ring B]

/-- An associative-ring submodule is product-isotropic when every ordered
product of two of its elements vanishes. This is stronger than nullness for
a quadratic form, and is the precise space-level hypothesis used for
orthogonality of round-trip operator corners. -/
def ProductIsotropicSubmodule (U : Submodule ℤ B) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, x * y = 0

def defect (x : B) : B := x * x - x
def cornerPlus (u v : B) : B := u * v
def cornerMinus (u v : B) : B := v * u
def cornerUnit (u v : B) : B := u * v + v * u
def isotropicSum (u v : B) : B := u + v
def isotropicDifference (u v : B) : B := u - v
def root3 (u v : B) : B := u - v - u * v
def root6 (u v : B) : B := u * v - u + v
def relativePhi3 (V x : B) : B := x * x + x + V
def relativePhi4 (V x : B) : B := x * x + V
def relativePhi6 (V x : B) : B := x * x - x + V

/-- Two product-isotropic submodules produce mutually annihilating
round-trip products. The four entries may vary independently, so this is a
space-level result rather than only the diagonal case `uv` against `vu`. -/
theorem product_isotropic_submodules_round_trip_orthogonality
    (U V : Submodule ℤ B)
    (hU : ProductIsotropicSubmodule U)
    (hV : ProductIsotropicSubmodule V)
    {u₁ u₂ : B} (hu₁ : u₁ ∈ U) (hu₂ : u₂ ∈ U)
    {v₁ v₂ : B} (hv₁ : v₁ ∈ V) (hv₂ : v₂ ∈ V) :
    (u₁ * v₁) * (v₂ * u₂) = 0 ∧
    (v₂ * u₂) * (u₁ * v₁) = 0 := by
  constructor
  · calc
      (u₁ * v₁) * (v₂ * u₂) = u₁ * (v₁ * v₂) * u₂ := by noncomm_ring
      _ = 0 := by rw [hV v₁ hv₁ v₂ hv₂]; noncomm_ring
  · calc
      (v₂ * u₂) * (u₁ * v₁) = v₂ * (u₂ * u₁) * v₁ := by noncomm_ring
      _ = 0 := by rw [hU u₂ hu₂ u₁ hu₁]; noncomm_ring

/-- Specializing the submodule theorem to a single pair recovers the
orthogonality law for its two ordered round trips. -/
theorem product_isotropic_pair_round_trips_orthogonal
    (U V : Submodule ℤ B)
    (hU : ProductIsotropicSubmodule U)
    (hV : ProductIsotropicSubmodule V)
    {u : B} (hu : u ∈ U) {v : B} (hv : v ∈ V) :
    (u * v) * (v * u) = 0 ∧ (v * u) * (u * v) = 0 := by
  exact product_isotropic_submodules_round_trip_orthogonality U V hU hV hu hu hv hv

theorem isotropic_products_and_defects (u v : B)
    (hu : u * u = 0) (hv : v * v = 0) :
    cornerPlus u v * cornerMinus u v = 0 ∧
    cornerMinus u v * cornerPlus u v = 0 ∧
    defect u = -u ∧ defect (defect u) = u := by
  have h₁ : u * v * (v * u) = 0 := by
    calc
      u * v * (v * u) = u * (v * v) * u := by noncomm_ring
      _ = 0 := by rw [hv]; simp
  have h₂ : v * u * (u * v) = 0 := by
    calc
      v * u * (u * v) = v * (u * u) * v := by noncomm_ring
      _ = 0 := by rw [hu]; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [cornerPlus, cornerMinus] using h₁
  · simpa [cornerMinus, cornerPlus] using h₂
  · simp [defect, hu]
  · simp [defect, hu]

/-- A regular isotropic pair generates complementary orthogonal idempotents. -/
theorem regular_pair_generates_orthogonal_idempotents (u v : B)
    (hu : u * u = 0) (hv : v * v = 0)
    (hregU : u * v * u = u) (hregV : v * u * v = v) :
    defect (cornerPlus u v) = 0 ∧
    defect (cornerMinus u v) = 0 ∧
    defect (cornerUnit u v) = 0 ∧
    cornerPlus u v * cornerMinus u v = 0 ∧
    cornerMinus u v * cornerPlus u v = 0 := by
  have hp : cornerPlus u v * cornerPlus u v = cornerPlus u v := by
    dsimp [cornerPlus]
    calc
      u * v * (u * v) = (u * v * u) * v := by noncomm_ring
      _ = u * v := by rw [hregU]
  have hm : cornerMinus u v * cornerMinus u v = cornerMinus u v := by
    dsimp [cornerMinus]
    calc
      v * u * (v * u) = (v * u * v) * u := by noncomm_ring
      _ = v * u := by rw [hregV]
  have hpm : cornerPlus u v * cornerMinus u v = 0 :=
    (isotropic_products_and_defects u v hu hv).1
  have hmp : cornerMinus u v * cornerPlus u v = 0 :=
    (isotropic_products_and_defects u v hu hv).2.1
  have hV : cornerUnit u v * cornerUnit u v = cornerUnit u v := by
    dsimp [cornerUnit]
    calc
      (u * v + v * u) * (u * v + v * u) =
          u * v * (u * v) + u * v * (v * u) +
            (v * u) * (u * v) + v * u * (v * u) := by noncomm_ring
      _ = u * v + v * u := by
        rw [show u * v * (u * v) = u * v by simpa [cornerPlus] using hp,
          show u * v * (v * u) = 0 by simpa [cornerPlus, cornerMinus] using hpm,
          show v * u * (u * v) = 0 by simpa [cornerMinus, cornerPlus] using hmp,
          show v * u * (v * u) = v * u by simpa [cornerMinus] using hm]
        simp
  refine ⟨?_, ?_, ?_, hpm, hmp⟩
  · change cornerPlus u v * cornerPlus u v - cornerPlus u v = 0
    rw [hp, sub_self]
  · change cornerMinus u v * cornerMinus u v - cornerMinus u v = 0
    rw [hm, sub_self]
  · change cornerUnit u v * cornerUnit u v - cornerUnit u v = 0
    rw [hV, sub_self]

/-- Square-zero generators whose anticommutator is the ambient unit are
mutually von Neumann regular. This derives the regularity hypotheses needed
by `regular_pair_generates_orthogonal_idempotents`; it does not assume a
pre-existing idempotent or Peirce cut. -/
theorem normalized_square_zero_pair_is_mutually_regular (u v : B)
    (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) :
    u * v * u = u ∧ v * u * v = v := by
  constructor
  · calc
      u * v * u = u * (u * v + v * u) - (u * u) * v := by noncomm_ring
      _ = u := by rw [hunit, hu]; noncomm_ring
  · calc
      v * u * v = v * (u * v + v * u) - (v * v) * u := by noncomm_ring
      _ = v := by rw [hunit, hv]; noncomm_ring

/-- A normalized square-zero pair generates complementary orthogonal
idempotents without a pre-existing cut. The regularity equations needed by
the general theorem are consequences of the anticommutator normalization. -/
theorem normalized_square_zero_pair_generates_orthogonal_idempotents
    (u v : B) (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) :
    cornerPlus u v * cornerPlus u v = cornerPlus u v ∧
    cornerMinus u v * cornerMinus u v = cornerMinus u v ∧
    cornerPlus u v * cornerMinus u v = 0 ∧
    cornerMinus u v * cornerPlus u v = 0 ∧
    cornerPlus u v + cornerMinus u v = 1 := by
  obtain ⟨hregU, hregV⟩ :=
    normalized_square_zero_pair_is_mutually_regular u v hu hv hunit
  obtain ⟨hPlus, hMinus, _, hOrthPlus, hOrthMinus⟩ :=
    regular_pair_generates_orthogonal_idempotents u v hu hv hregU hregV
  refine ⟨?_, ?_, hOrthPlus, hOrthMinus, ?_⟩
  · exact sub_eq_zero.mp hPlus
  · exact sub_eq_zero.mp hMinus
  · simpa [cornerPlus, cornerMinus] using hunit

/-- The sum of the square-zero generators squares to the generated corner unit. -/
theorem isotropic_sum_square (u v : B)
    (hu : u * u = 0) (hv : v * v = 0) :
    isotropicSum u v * isotropicSum u v = cornerUnit u v := by
  dsimp [isotropicSum, cornerUnit]
  noncomm_ring [hu, hv]

/-- Reassociate the two regular-pair equations into the right-nested forms
needed for rewriting ordered products. -/
theorem regular_pair_right_nested_forms (u v : B)
    (hregU : u * v * u = u) (hregV : v * u * v = v) :
    u * (v * u) = u ∧ v * (u * v) = v := by
  constructor
  · simpa only [mul_assoc] using hregU
  · simpa only [mul_assoc] using hregV

/-- Off the regular locus, both relative cyclotomic evaluations have the
same ordered remainder: the two regularity defects and the defect of `uv`. -/
theorem relative_cyclotomic_off_shell_remainder (u v : B)
    (hu : u * u = 0) (hv : v * v = 0) :
    relativePhi3 (cornerUnit u v) (root3 u v) =
        (u - u * v * u) - (v - v * u * v) + defect (cornerPlus u v) ∧
    relativePhi6 (cornerUnit u v) (root6 u v) =
        (u - u * v * u) - (v - v * u * v) + defect (cornerPlus u v) := by
  constructor <;>
    dsimp [relativePhi3, relativePhi6, cornerUnit, root3, root6,
      defect, cornerPlus] <;>
    noncomm_ring [hu, hv, ← mul_assoc u u, ← mul_assoc v v]

/-- The difference of two square-zero generators squares to the negative
of the corner unit. -/
theorem isotropic_difference_square (u v : B)
    (hu : u * u = 0) (hv : v * v = 0) :
    isotropicDifference u v * isotropicDifference u v = -cornerUnit u v := by
  dsimp [isotropicDifference, cornerUnit]
  noncomm_ring [hu, hv]

/-- The relative third and sixth cyclotomic equations close on a mutually
regular square-zero pair. The constant term is the generated corner unit. -/
theorem regular_pair_relative_cyclotomic_roots (u v : B)
    (hu : u * u = 0) (hv : v * v = 0)
    (hregU : u * v * u = u) (hregV : v * u * v = v) :
    relativePhi3 (cornerUnit u v) (root3 u v) = 0 ∧
    relativePhi4 (cornerUnit u v) (isotropicDifference u v) = 0 ∧
    relativePhi6 (cornerUnit u v) (root6 u v) = 0 := by
  obtain ⟨hregU', hregV'⟩ := regular_pair_right_nested_forms u v hregU hregV
  simp only [relativePhi3, relativePhi4, relativePhi6, cornerUnit,
    root3, root6, isotropicDifference]
  refine ⟨?_, ?_, ?_⟩ <;>
    noncomm_ring [hu, hv, ← mul_assoc u u, ← mul_assoc v v,
      hregU, hregV, hregU', hregV']

/-- Under mutual regularity, the two nilpotents are recovered by the
idempotents generated from their ordered products. -/
theorem regular_pair_localizes_generators (u v : B)
    (hregU : u * v * u = u) (hregV : v * u * v = v) :
    cornerPlus u v * u * cornerMinus u v = u ∧
    cornerMinus u v * v * cornerPlus u v = v := by
  obtain ⟨hregU', hregV'⟩ := regular_pair_right_nested_forms u v hregU hregV
  constructor <;> dsimp [cornerPlus, cornerMinus] <;>
    noncomm_ring [hregU, hregV, hregU', hregV']

/-- The normalized generators are recovered in the two directed Peirce
corners of the idempotents they generate. -/
theorem normalized_square_zero_pair_localizes_generators
    (u v : B) (hu : u * u = 0) (hv : v * v = 0)
    (hunit : u * v + v * u = 1) :
    cornerPlus u v * u * cornerMinus u v = u ∧
    cornerMinus u v * v * cornerPlus u v = v := by
  obtain ⟨hregU, hregV⟩ :=
    normalized_square_zero_pair_is_mutually_regular u v hu hv hunit
  exact regular_pair_localizes_generators u v hregU hregV

/-- The third-root candidate has cube equal to the generated corner unit. -/
theorem regular_pair_third_root_cube (u v : B)
    (hu : u * u = 0) (hv : v * v = 0)
    (hregU : u * v * u = u) (hregV : v * u * v = v) :
    root3 u v * root3 u v * root3 u v = cornerUnit u v := by
  obtain ⟨hregU', hregV'⟩ := regular_pair_right_nested_forms u v hregU hregV
  dsimp [root3, cornerUnit]
  noncomm_ring [hu, hv, ← mul_assoc u u, ← mul_assoc v v,
    hregU, hregV, hregU', hregV']

/-- The fourth-root candidate has fourth power equal to the generated corner
unit. -/
theorem regular_pair_fourth_root_fourth_power (u v : B)
    (hu : u * u = 0) (hv : v * v = 0)
    (hregU : u * v * u = u) (hregV : v * u * v = v) :
    isotropicDifference u v * isotropicDifference u v *
      isotropicDifference u v * isotropicDifference u v = cornerUnit u v := by
  have hDiff := isotropic_difference_square u v hu hv
  have hUnitDefect := (regular_pair_generates_orthogonal_idempotents
    u v hu hv hregU hregV).2.2.1
  have hUnit : cornerUnit u v * cornerUnit u v = cornerUnit u v :=
    sub_eq_zero.mp hUnitDefect
  calc
    isotropicDifference u v * isotropicDifference u v *
        isotropicDifference u v * isotropicDifference u v =
      (isotropicDifference u v * isotropicDifference u v) *
        (isotropicDifference u v * isotropicDifference u v) := by noncomm_ring
    _ = (-cornerUnit u v) * (-cornerUnit u v) := by rw [hDiff]
    _ = cornerUnit u v := by noncomm_ring [hUnit]

/-- The sixth-root candidate has cube equal to the negative corner unit. -/
theorem regular_pair_sixth_root_cube (u v : B)
    (hu : u * u = 0) (hv : v * v = 0)
    (hregU : u * v * u = u) (hregV : v * u * v = v) :
    root6 u v * root6 u v * root6 u v = -cornerUnit u v := by
  obtain ⟨hregU', hregV'⟩ := regular_pair_right_nested_forms u v hregU hregV
  dsimp [root6, cornerUnit]
  noncomm_ring [hu, hv, ← mul_assoc u u, ← mul_assoc v v,
    hregU, hregV, hregU', hregV']

/-- The first idempotency defect of the sixth root is the negative of the
emergent corner unit; its negative is idempotent. -/
theorem sixth_root_defect_generates_idempotent (u v : B)
    (hu : u * u = 0) (hv : v * v = 0)
    (hregU : u * v * u = u) (hregV : v * u * v = v) :
    defect (root6 u v) = -cornerUnit u v ∧
    defect (-defect (root6 u v)) = 0 := by
  obtain ⟨hregU', hregV'⟩ := regular_pair_right_nested_forms u v hregU hregV
  have hPlus : cornerPlus u v * cornerPlus u v = cornerPlus u v := by
    dsimp [cornerPlus]
    noncomm_ring [hu, hv, ← mul_assoc u u, ← mul_assoc v v,
      hregU, hregV, hregU', hregV']
  have hMinus : cornerMinus u v * cornerMinus u v = cornerMinus u v := by
    dsimp [cornerMinus]
    noncomm_ring [hu, hv, ← mul_assoc u u, ← mul_assoc v v,
      hregU, hregV, hregU', hregV']
  have hOrth := isotropic_products_and_defects u v hu hv
  have hUnit : cornerUnit u v * cornerUnit u v = cornerUnit u v := by
    dsimp [cornerUnit, cornerPlus, cornerMinus]
    noncomm_ring [hu, hv, ← mul_assoc u u, ← mul_assoc v v,
      hregU, hregV, hregU', hregV']
  have hRoot : defect (root6 u v) = -cornerUnit u v := by
    dsimp [defect, root6, cornerUnit]
    noncomm_ring [hu, hv, ← mul_assoc u u, ← mul_assoc v v,
      hregU, hregV, hregU', hregV']
  refine ⟨hRoot, ?_⟩
  rw [hRoot]
  dsimp [defect]
  noncomm_ring [hUnit]

/-- Applying the defect twice to the sixth root yields twice the emergent
corner unit, distinguishing this iterate from the idempotent negative defect. -/
theorem sixth_root_defect_second_iterate (u v : B)
    (hu : u * u = 0) (hv : v * v = 0)
    (hregU : u * v * u = u) (hregV : v * u * v = v) :
    defect (defect (root6 u v)) = 2 • cornerUnit u v := by
  have hRoot := (sixth_root_defect_generates_idempotent
    u v hu hv hregU hregV).1
  have hUnitDefect := (regular_pair_generates_orthogonal_idempotents
    u v hu hv hregU hregV).2.2.1
  have hUnit : cornerUnit u v * cornerUnit u v = cornerUnit u v :=
    sub_eq_zero.mp hUnitDefect
  rw [hRoot]
  dsimp [defect]
  noncomm_ring [hUnit]

/-- The isotropic sum implements the local quadratic Galois swap on the
third-root candidate. This is a sandwich identity on the generated corner,
not a global automorphism of the ambient ring. -/
theorem isotropic_sum_galois_sandwich (u v : B)
    (hu : u * u = 0) (hv : v * v = 0)
    (hregU : u * v * u = u) (hregV : v * u * v = v) :
    isotropicSum u v * root3 u v * isotropicSum u v =
      root3 u v * root3 u v := by
  obtain ⟨hregU', hregV'⟩ := regular_pair_right_nested_forms u v hregU hregV
  dsimp [isotropicSum, root3]
  noncomm_ring [hu, hv, ← mul_assoc u u, ← mul_assoc v v,
    hregU, hregV, hregU', hregV']

/-- The same sandwich swaps the quadratic conjugate back to the third root. -/
theorem isotropic_sum_galois_round_trip (u v : B)
    (hu : u * u = 0) (hv : v * v = 0)
    (hregU : u * v * u = u) (hregV : v * u * v = v) :
    isotropicSum u v * (root3 u v * root3 u v) * isotropicSum u v =
      root3 u v := by
  obtain ⟨hregU', hregV'⟩ := regular_pair_right_nested_forms u v hregU hregV
  dsimp [isotropicSum, root3]
  noncomm_ring [hu, hv, ← mul_assoc u u, ← mul_assoc v v,
    hregU, hregV, hregU', hregV']

end InfoGeometry.Algebra.IsotropicCyclotomicGenesis
