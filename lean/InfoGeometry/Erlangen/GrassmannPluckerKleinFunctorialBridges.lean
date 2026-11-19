/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.ErlangenProgramMobiusLieAndContact
import InfoGeometry.Projective.PluckerLinearComplex
import InfoGeometry.Projective.PluckerMatrixAction

/-!
# Functorial Grassmann–Plücker–Klein bridges

The existing owners prove pointwise identities between Grassmann's exterior
algebra, Plücker's line coordinates, and Klein's Erlangen groups. This module
adds the *functorial* statements that Klein's 1872 programme asks for: maps
between the carriers that intertwine the group actions and respect
composition.

## Bridge C — linear complexes as a contravariant `GL₄` functor

A linear complex `C : Plucker6 R` determines the alternating Grassmann form
`complexForm C` with Pfaffian `kleinQ C` (`complexMatrix_det`). Congruence
`M ↦ Aᵀ M A` defines `complexCongr A C`, and we prove:

* `complexForm_complexCongr`: the pulled-back complex is the complex of
  lines `x ∧ y` such that `A x ∧ A y` lies in `C` (Klein §4, *Abbildung*);
* `complexCongr_one`, `complexCongr_mul`: a contravariant monoid action;
* `polar_complexCongr`: `complexCongr A` is the adjoint of Plücker's
  second-compound action `transform A` under Klein's polar pairing;
* `kleinQ_complexCongr`: the Pfaffian is a relative invariant of weight
  `det A` (Klein's quadric equation as Grassmann's Pfaffian);
* `finrank_ker_complexForm_complexCongr`: for `A ∈ GL₄`, the Grassmann radical
  of the form (Darboux rank) is invariant, so Plücker's general/special
  dichotomy is a `GL₄`-invariant classification (Klein Note VI).

## Bridge B — Lie sphere group to Möbius group on Grassmann circle space

Lie's oriented circles live in `ℝ⁵` with the `(3,2)` form `lieBilin`;
Grassmann's circle space is `ℝ⁴` with `circleBilin`. The projection
`lieToGrassmannCircleProj` kills the radial axis `e₄`. Klein's §2 principle
(adjoin a configuration and pass to its stabilizer) is realized as a monoid
homomorphism `lieMobiusToCircleHom` from the stabilizer of `e₄` inside the
`lieBilin` isometries to the endomorphisms of circle space:

* `circleReduce_naturality`: the projection intertwines the two actions;
* `circleReduce_preserves_circleBilin`: the image lies in `O(circleBilin)`;
* `circleReduce_preserves_tangency`, `isSyncyclic4_map`: Grassmann tangency and
  the exterior syncyclicity criterion are transported;
* `lieMobius_preserves_points` versus `lieRadiusDil_not_lieMobius`: points
  (radius zero) form a body (*Körper*) for the stabilizer but not for Lie's
  full group, which contains the radius dilations (Klein §§5, 7).

## Scope

Finite-dimensional linear algebra over a commutative ring (or `ℝ` for the
circle bridge). No claim is made about the full orthogonal groups beyond the
stated stabilizer, nor about surjectivity of `lieMobiusToCircleHom`.
-/

noncomputable section

namespace InfoGeometry.Erlangen.GrassmannPluckerKleinFunctorialBridges

open Matrix
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.PluckerMatrixAction
open InfoGeometry.Projective.PluckerLinearComplex
open InfoGeometry.Canonical.Pfaffian
open InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
open InfoGeometry.Erlangen.ErlangenProgramMobiusLieAndContact

/-! ## Bridge C: linear complexes under congruence -/

section LinearComplexCongruence

variable {R : Type*} [CommRing R]

/-- Read the six complex coordinates back from an alternating `4 × 4` matrix,
inverting `complexMatrix`. -/
def complexOfMatrix (M : Matrix (Fin 4) (Fin 4) R) : Plucker6 R where
  p01 := M 2 3
  p02 := -M 1 3
  p03 := M 1 2
  p12 := M 0 3
  p13 := -M 0 2
  p23 := M 0 1

@[simp] theorem complexOfMatrix_complexMatrix (C : Plucker6 R) :
    complexOfMatrix (complexMatrix C) = C := by
  apply Plucker6.ext <;> simp [complexOfMatrix, complexMatrix, skew4]

/-- Pull back a linear complex along a point transformation `A` by congruence
of its alternating Grassmann matrix. -/
def complexCongr (A : Matrix (Fin 4) (Fin 4) R) (C : Plucker6 R) : Plucker6 R :=
  complexOfMatrix (Aᵀ * complexMatrix C * A)

/-- The congruence of an alternating matrix is again alternating, so no
information is lost when reading it back as a complex. -/
theorem complexMatrix_complexCongr (A : Matrix (Fin 4) (Fin 4) R) (C : Plucker6 R) :
    complexMatrix (complexCongr A C) = Aᵀ * complexMatrix C * A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexCongr, complexOfMatrix, complexMatrix, skew4, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring

/-- **Abbildung for complexes.** The pulled-back complex contains the line
`x ∧ y` exactly when `C` contains the line `A x ∧ A y`. -/
theorem complexForm_complexCongr (A : Matrix (Fin 4) (Fin 4) R) (C : Plucker6 R)
    (x y : Fin 4 → R) :
    complexForm (complexCongr A C) x y = complexForm C (A *ᵥ x) (A *ᵥ y) := by
  simp only [complexForm, Matrix.toBilin'_apply', complexMatrix_complexCongr,
    ← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_transpose]

@[simp] theorem complexCongr_one (C : Plucker6 R) :
    complexCongr (1 : Matrix (Fin 4) (Fin 4) R) C = C := by
  simp [complexCongr]

/-- Congruence is a contravariant action: pulling back along `A * B` is
pulling back along `A`, then along `B`. -/
theorem complexCongr_mul (A B : Matrix (Fin 4) (Fin 4) R) (C : Plucker6 R) :
    complexCongr (A * B) C = complexCongr B (complexCongr A C) := by
  conv_rhs => rw [complexCongr, complexMatrix_complexCongr]
  rw [complexCongr, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- **Adjointness.** Under Klein's polar pairing, pulling back a complex by
congruence is the transpose of Plücker's second-compound action on lines. -/
theorem polar_complexCongr (A : Matrix (Fin 4) (Fin 4) R) (C P : Plucker6 R) :
    Plucker6.polar (complexCongr A C) P = Plucker6.polar C (transform A P) := by
  -- Both sides are scalars in `R`; after expanding coordinates this is a
  -- polynomial identity in the entries of `A`, `C`, and `P`.
  have hscalar : Plucker6.polar (complexCongr A C) P = Plucker6.polar C (transform A P) := by
    rw [Plucker6.polar_formula, Plucker6.polar_formula]
    simp [complexCongr, complexOfMatrix, complexMatrix, skew4, transform, coordinates,
      secondCompound, coordinatePair, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring
  exact hscalar

/-- **Pfaffian covariance.** Klein's quadric form, read as the Pfaffian of
Grassmann's alternating form, is a relative invariant of weight `det A`. -/
theorem kleinQ_complexCongr (A : Matrix (Fin 4) (Fin 4) R) (C : Plucker6 R) :
    Plucker6.kleinQ (complexCongr A C) = A.det * Plucker6.kleinQ C := by
  have h12 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h32 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := by decide
  rw [Matrix.det_succ_row_zero]
  simp [Plucker6.kleinQ, complexCongr, complexOfMatrix, complexMatrix, skew4,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_three,
    h12, h22, h32]
  ring

end LinearComplexCongruence

section DarbouxRank

variable {K : Type*} [Field K]

/-- For an invertible point transformation, the radical of the pulled-back
form is the preimage of the radical of the original form. -/
theorem ker_complexForm_complexCongr (A : Matrix (Fin 4) (Fin 4) K) (hA : IsUnit A.det)
    (C : Plucker6 K) :
    LinearMap.ker (complexForm (complexCongr A C)) =
      (LinearMap.ker (complexForm C)).comap (Matrix.toLin' A) := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Matrix.toLin'_apply]
  constructor
  · intro hx
    refine LinearMap.ext fun z => ?_
    have hz : A *ᵥ (A⁻¹ *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
    have := LinearMap.congr_fun hx (A⁻¹ *ᵥ z)
    rw [complexForm_complexCongr, hz] at this
    simpa using this
  · intro hx
    refine LinearMap.ext fun y => ?_
    rw [complexForm_complexCongr, hx]
    simp

/-- **Darboux rank is a `GL₄` invariant.** The dimension of the Grassmann
radical of a linear complex does not change under invertible point
transformations. -/
theorem finrank_ker_complexForm_complexCongr (A : Matrix (Fin 4) (Fin 4) K)
    (hA : IsUnit A.det) (C : Plucker6 K) :
    Module.finrank K (LinearMap.ker (complexForm (complexCongr A C))) =
      Module.finrank K (LinearMap.ker (complexForm C)) := by
  let hInv : Invertible A := Matrix.invertibleOfIsUnitDet A hA
  let e : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) := Matrix.toLinearEquiv' A hInv
  have hmap : LinearMap.ker (complexForm (complexCongr A C)) =
      (LinearMap.ker (complexForm C)).map (e.symm : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) := by
    rw [ker_complexForm_complexCongr A hA C]
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨Matrix.toLin' A x, hx, by
        change e.symm (e x) = x
        exact e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change e (e.symm y) ∈ _
      rwa [e.apply_symm_apply]
  rw [hmap, LinearEquiv.finrank_map_eq]

/-- **Plücker's general/special dichotomy is invariant (Klein Note VI).**
Under an invertible point transformation, a complex is general (nondegenerate
Grassmann form, nonzero Pfaffian) exactly when its pullback is. -/
theorem complexCongr_general_iff (A : Matrix (Fin 4) (Fin 4) K) (hA : IsUnit A.det)
    (C : Plucker6 K) :
    (complexForm (complexCongr A C)).Nondegenerate ↔ (complexForm C).Nondegenerate := by
  rw [complexForm_nondegenerate_iff, complexForm_nondegenerate_iff, kleinQ_complexCongr]
  exact ⟨fun h hC => h (by rw [hC, mul_zero]),
    fun h hC => h ((mul_eq_zero.mp hC).resolve_left hA.ne_zero)⟩

end DarbouxRank

/-! ## Bridge B: Lie sphere group to Möbius group on circle space -/

section LieToMobius

/-- The radial axis of Lie's sphere space, adjoined as Klein's fundamental
configuration. -/
def lieRadialAxis : Fin 5 → ℝ := Pi.single 4 1

theorem lieBilin_radialAxis_right (u : Fin 5 → ℝ) :
    lieBilin u lieRadialAxis = -u 4 := by
  simp [lieBilin, lieRadialAxis]

theorem lieToGrassmannCircleProj_radialAxis :
    lieToGrassmannCircleProj lieRadialAxis = 0 := by
  ext i
  fin_cases i <;> simp [lieToGrassmannCircleProj, lieRadialAxis]

/-- A linear section of the projection, landing in the hyperplane
orthogonal to the radial axis. -/
def circleToLieSection : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun w := ![(w 0 + w 3) / 2, (w 0 - w 3) / 2, w 1, w 2, 0]
  map_add' u v := by ext i; fin_cases i <;> (simp; try ring)
  map_smul' c u := by ext i; fin_cases i <;> (simp; try ring)

theorem lieToGrassmannCircleProj_section (w : Fin 4 → ℝ) :
    lieToGrassmannCircleProj (circleToLieSection w) = w := by
  ext i
  fin_cases i <;>
    (simp [lieToGrassmannCircleProj, circleToLieSection]; try ring)

theorem section_lieToGrassmannCircleProj (u : Fin 5 → ℝ) :
    circleToLieSection (lieToGrassmannCircleProj u) = u - u 4 • lieRadialAxis := by
  ext i
  fin_cases i <;>
    (simp [lieToGrassmannCircleProj, circleToLieSection, lieRadialAxis];
      try ring)

/-- `lieBilin` isometries fixing the radial axis: Klein's stabilizer of the
adjoined configuration inside Lie's sphere group. -/
def IsLieMobius (g : Module.End ℝ (Fin 5 → ℝ)) : Prop :=
  (∀ u v, lieBilin (g u) (g v) = lieBilin u v) ∧ g lieRadialAxis = lieRadialAxis

/-- The stabilizer is a submonoid of the endomorphism monoid. -/
def lieMobiusStabilizer : Submonoid (Module.End ℝ (Fin 5 → ℝ)) where
  carrier := {g | IsLieMobius g}
  one_mem' := ⟨fun _ _ => rfl, rfl⟩
  mul_mem' := by
    intro g h hg hh
    refine ⟨fun u v => ?_, ?_⟩
    · simp only [Module.End.mul_apply, hg.1, hh.1]
    · simp only [Module.End.mul_apply, hh.2, hg.2]

/-- Stabilizer elements preserve the radius coordinate. -/
theorem IsLieMobius.apply_four {g : Module.End ℝ (Fin 5 → ℝ)} (hg : IsLieMobius g)
    (w : Fin 5 → ℝ) : (g w) 4 = w 4 := by
  have h := hg.1 w lieRadialAxis
  rw [hg.2, lieBilin_radialAxis_right, lieBilin_radialAxis_right] at h
  exact neg_inj.mp h

/-- **Points form a body for the stabilizer (Klein §5).** Zero-radius vectors
are carried to zero-radius vectors. -/
theorem lieMobius_preserves_points {g : Module.End ℝ (Fin 5 → ℝ)} (hg : IsLieMobius g)
    (u : Fin 5 → ℝ) (hu : u 4 = 0) : (g u) 4 = 0 := by
  rw [hg.apply_four, hu]

/-- **Lie's group is strictly larger (Klein §7).** The radius dilation
preserves `lieBilin` but does not stabilize the radial axis. -/
theorem lieRadiusDil_not_lieMobius (t : ℝ) (ht : t ≠ 0) :
    (∀ u v, lieBilin (Matrix.toLin' (lieRadiusDilMatrix t) u)
        (Matrix.toLin' (lieRadiusDilMatrix t) v) = lieBilin u v) ∧
      ¬ IsLieMobius (Matrix.toLin' (lieRadiusDilMatrix t)) := by
  refine ⟨fun u v => by
    simpa [Matrix.toLin'_apply] using lieRadiusDilMatrix_preserves_lieBilin t u v, ?_⟩
  rintro ⟨-, h⟩
  have h0 : (lieRadiusDilMatrix t *ᵥ lieRadialAxis) 0 = lieRadialAxis 0 := by
    simpa only [Matrix.toLin'_apply] using congrFun h 0
  simp [lieRadiusDilMatrix, lieRadialAxis, Matrix.mulVec, dotProduct,
    Fin.sum_univ_five] at h0
  exact ht (by simpa using h0)

/-- The induced endomorphism of Grassmann's circle space. -/
def circleReduce (g : Module.End ℝ (Fin 5 → ℝ)) : Module.End ℝ (Fin 4 → ℝ) :=
  lieToGrassmannCircleProj ∘ₗ g ∘ₗ circleToLieSection

/-- **Naturality.** The projection to circle space intertwines `g` with its
reduction whenever `g` fixes the radial axis. -/
theorem circleReduce_naturality {g : Module.End ℝ (Fin 5 → ℝ)}
    (hg : g lieRadialAxis = lieRadialAxis) (u : Fin 5 → ℝ) :
    lieToGrassmannCircleProj (g u) = circleReduce g (lieToGrassmannCircleProj u) := by
  simp only [circleReduce, LinearMap.comp_apply, section_lieToGrassmannCircleProj,
    map_sub, map_smul, hg, lieToGrassmannCircleProj_radialAxis, smul_zero, sub_zero]

/-- The reduction of a stabilizer element is a `circleBilin` isometry, i.e.
lies in the Möbius group `O(circleBilin)`. -/
theorem circleReduce_preserves_circleBilin {g : Module.End ℝ (Fin 5 → ℝ)}
    (hg : IsLieMobius g) (x y : Fin 4 → ℝ) :
    circleBilin (circleReduce g x) (circleReduce g y) = circleBilin x y := by
  have hx : circleToLieSection x 4 = 0 := by simp [circleToLieSection]
  have hy : circleToLieSection y 4 = 0 := by simp [circleToLieSection]
  conv_rhs => rw [← lieToGrassmannCircleProj_section x, ← lieToGrassmannCircleProj_section y]
  simp only [circleReduce, LinearMap.comp_apply, circleBilin_lieToGrassmannProj, hg.1,
    hg.apply_four]

theorem circleReduce_one : circleReduce 1 = 1 :=
  LinearMap.ext fun x => lieToGrassmannCircleProj_section x

theorem circleReduce_mul {g h : Module.End ℝ (Fin 5 → ℝ)}
    (hg : g lieRadialAxis = lieRadialAxis) :
    circleReduce (g * h) = circleReduce g * circleReduce h := by
  refine LinearMap.ext fun x => ?_
  change lieToGrassmannCircleProj (g (h (circleToLieSection x))) =
    circleReduce g (lieToGrassmannCircleProj (h (circleToLieSection x)))
  exact circleReduce_naturality hg _

/-- **Klein §2 as a functor.** Reduction to circle space is a monoid
homomorphism out of the stabilizer of the radial axis. -/
def lieMobiusToCircleHom : lieMobiusStabilizer →* Module.End ℝ (Fin 4 → ℝ) where
  toFun g := circleReduce g.1
  map_one' := circleReduce_one
  map_mul' g _ := circleReduce_mul g.2.2

theorem lieMobiusToCircleHom_preserves_circleBilin (g : lieMobiusStabilizer)
    (x y : Fin 4 → ℝ) :
    circleBilin (lieMobiusToCircleHom g x) (lieMobiusToCircleHom g y) = circleBilin x y :=
  circleReduce_preserves_circleBilin g.2 x y

/-- Grassmann circle tangency is transported by every reduced stabilizer
element. -/
theorem circleReduce_preserves_tangency {g : Module.End ℝ (Fin 5 → ℝ)}
    (hg : IsLieMobius g) (u v : Fin 4 → ℝ) :
    IsCircleTangent (circleReduce g u) (circleReduce g v) ↔ IsCircleTangent u v := by
  simp only [IsCircleTangent, circleReduce_preserves_circleBilin hg]

/-- Grassmann's exterior syncyclicity criterion is natural for every linear
map of circle space, in particular for the reduced stabilizer. -/
theorem isSyncyclic4_map (f : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) {C₁ C₂ C₃ C₄ : Fin 4 → ℝ}
    (h : IsSyncyclic4 C₁ C₂ C₃ C₄) :
    IsSyncyclic4 (f C₁) (f C₂) (f C₃) (f C₄) := by
  unfold IsSyncyclic4 at h ⊢
  have hm := ExteriorAlgebra.map_apply_ιMulti (R := ℝ) f ![C₁, C₂, C₃, C₄]
  rw [h, map_zero] at hm
  have hcomp : (f ∘ ![C₁, C₂, C₃, C₄]) = ![f C₁, f C₂, f C₃, f C₄] := by
    ext i : 1
    fin_cases i <;> rfl
  rw [← hcomp, ← hm]

/-- The Lie circle of center `(a, b)` and signed radius `r` is sent by any
stabilizer element to a vector whose Grassmann image is the reduced image of
Grassmann's circle `circleVec a b r`. -/
theorem circleReduce_circleVec {g : Module.End ℝ (Fin 5 → ℝ)}
    (hg : IsLieMobius g) (a b r : ℝ) :
    lieToGrassmannCircleProj (g (lieCircleVec a b r)) =
      circleReduce g (circleVec a b r) := by
  rw [circleReduce_naturality hg.2, lieToGrassmannCircleProj_circleVec]

end LieToMobius

end InfoGeometry.Erlangen.GrassmannPluckerKleinFunctorialBridges
