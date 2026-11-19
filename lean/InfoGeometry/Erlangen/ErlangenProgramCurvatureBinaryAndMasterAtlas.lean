/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Erlangen.ErlangenProgramGroupHierarchyAndPrincipal
import InfoGeometry.Erlangen.ErlangenProgramTransferHesseAndBodies
import InfoGeometry.Erlangen.ErlangenProgramMobiusLieAndContact
import InfoGeometry.Canonical.OperatorErlangenGaloisConnection
import InfoGeometry.Projective.PluckerRayAxisAndDyname
import InfoGeometry.Projective.PluckerCongruenceCylindroidAndRegulus
import InfoGeometry.Projective.PluckerQuadraticComplexAndSurfaces
import InfoGeometry.Projective.PluckerKummerQuarticAndMasterAtlas

/-!
# Erlangen Program (§10, Concluding Remarks, Notes VI–VII): Curvature, Binary Syzygies, Trilogy

This module formalizes Archetypes `EK₈` and `EK₉` of Felix Klein's 1872 *Erlangen Program*
(`0807.3161v1 (1).pdf`, pp. 18–26), together with **Grassmann–Plücker–Klein Bridge II**,
the complete `9`-node Erlangen causal poset, `klein_erlangen_1872_master_synthesis`, and
the unified **`grassmann_plucker_klein_trilogy_synthesis`**:

1. **Projective Metric, Note VI Curvature Dichotomy, & Bridge II (`§10.1`, `Note VI`, pp. 18, 23–24)**:
   * Polar reflection `quadricPolarReflect B c x = B c c • x - (2 * B c x) • c`, preserving any
     symmetric bilinear pairing `B` up to `(B c c)²` (`quadricPolarReflect_preserves_bilin`),
     squaring to `(B c c)² • x` (`quadricPolarReflect_involutive_scale`), and separating
     nondegenerate constant nonzero curvature (`B c c ≠ 0`) from parabolic zero-curvature
     collapse (`B c c = 0`, `noteVI_quadric_chord_dichotomy`).
   * **Bridge II (`klein_noteVI_plucker_line_space_bridge`)**: connects Note VI's projective line-
     space metric directly to Plücker's null-system polarity `conjugatePolar C P` (`C.kleinQ ≠ 0`
     vs special complex `C.kleinQ = 0`) and the tangential quadratic complex
     `secondCompound G` (`quadric_tangent_secondCompound_symm`) together with the universal
     Kummer focal factorization `universal_kummer_w_sq_factorization`.
2. **Note VII Binary Form Syzygies & Regular Tetrahedron (`§5`, `Note VII`, pp. 7–8, 24–25)**:
   * General **Cayley Binary Cubic Syzygy** `Q² + 4 Δ³ - R f² = 0` (`cayley_binary_cubic_syzygy`)
     and canonical evaluation at `u³ - v³` (`cayley_binary_cubic_canonical`).
   * General **Cayley Binary Quartic Syzygy** `T² + 4 H³ - i H f² + j f³ = 0`
     (`cayley_binary_quartic_syzygy`).
   * **Tetrahedral Sphere Axis-Bisection Theorem** (`noteVII_tetrahedral_sphere_axis_bisection`):
     opposite-edge midpoints of the `V₄`-tetrahedron `(±x, ±y, ±z)` lie on the coordinate `V₄`
     axes, and for `x = y = z = c`, `r_sphere² = 3 * r_midpoint²`.
3. **Concluding Remarks Galois Bridge, Klein–Lie `[17]` `W`-Curves, & Footnote 37 Spinors (`pp. 18–20`)**:
   * Instantiates `OperatorErlangenFixedPoints.subgroup_le_fixingSubgroup_iff` alongside
     `InvariantGeometry.IsGeometricInvariant` (`erlangen_galois_subgroup_observable_bridge`).
   * Explicit commuting `3 × 3` matrix families for Klein–Lie `[17]` inside noncommutative
     `Matrix (Fin 3) (Fin 3) R` (`matrix3_erlangen_noncomm`), plus Hamilton quaternion `2`-to-`1`
     homomorphic double cover of `SO(3)` (`quatRotMatrix_mul`, `quatRotMatrix_neg`,
     `quatRotMatrix_orthog`, `quatRotMatrix_det`).
4. **Master Causal Poset `EK₉` & Unified Grassmann–Plücker–Klein Trilogy (`1862 ↔ 1868 ↔ 1872`)**:
   * `9`-node bitmask `PartialOrder ErlangenProgramArchetype`, incomparability witnesses,
     `klein_erlangen_1872_master_synthesis`, and `grassmann_plucker_klein_trilogy_synthesis`.
-/

namespace InfoGeometry.Erlangen.ErlangenProgramCurvatureBinaryAndMasterAtlas

open InfoGeometry.Erlangen.InvariantGeometry
open InfoGeometry.Erlangen.ErlangenProgramGroupHierarchyAndPrincipal
open InfoGeometry.Erlangen.ErlangenProgramTransferHesseAndBodies
open InfoGeometry.Erlangen.ErlangenProgramMobiusLieAndContact
open InfoGeometry.Canonical.OperatorErlangenFixedPoints
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.PluckerMatrixAction
open InfoGeometry.Projective.PluckerRayAxisAndDyname
open InfoGeometry.Projective.PluckerCongruenceCylindroidAndRegulus
open InfoGeometry.Projective.PluckerQuadraticComplexAndSurfaces
open InfoGeometry.Projective.PluckerKummerQuarticAndMasterAtlas
open Matrix

/-! ## 1. Projective Metric, Note VI Curvature Dichotomy, & Bridge II (§10.1, Note VI) -/

section ProjectiveMetricAndNoteVI

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Cayley–Klein polar reflection relative to pole `c` with bilinear form `B` (`§10.1`, `Note VI`). -/
def quadricPolarReflect (B : M →ₗ[R] M →ₗ[R] R) (c x : M) : M :=
  B c c • x - (2 * B c x) • c

/-- Cayley–Klein symmetric chord / area invariant `(B x x)(B y y) - (B x y)²`. -/
def cayleyKleinChord (B : M →ₗ[R] M →ₗ[R] R) (x y : M) : R :=
  B x x * B y y - B x y ^ 2

theorem quadricPolarReflect_preserves_bilin (B : M →ₗ[R] M →ₗ[R] R)
    (hsymm : ∀ u v : M, B u v = B v u) (c x y : M) :
    B (quadricPolarReflect B c x) (quadricPolarReflect B c y) = B c c ^ 2 * B x y := by
  have hlinL : ∀ u v w : M, ∀ α β : R, B (α • u - β • v) w = α * B u w - β * B v w := by
    intro u v w α β
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have hlinR : ∀ u v w : M, ∀ α β : R, B u (α • v - β • w) = α * B u v - β * B u w := by
    intro u v w α β
    simp only [map_sub, map_smul, smul_eq_mul]
  dsimp [quadricPolarReflect]
  rw [hlinL, hlinR, hlinR, hsymm x c]
  ring

theorem quadricPolarReflect_involutive_scale (B : M →ₗ[R] M →ₗ[R] R) (c x : M) :
    quadricPolarReflect B c (quadricPolarReflect B c x) = B c c ^ 2 • x := by
  have hlinR : ∀ u v w : M, ∀ α β : R, B u (α • v - β • w) = α * B u v - β * B u w := by
    intro u v w α β
    simp only [map_sub, map_smul, smul_eq_mul]
  dsimp [quadricPolarReflect]
  rw [hlinR]
  calc
    B c c • (B c c • x - (2 * B c x) • c) -
        (2 * (B c c * B c x - 2 * B c x * B c c)) • c
        = (B c c ^ 2) • x - (2 * (B c c * B c x)) • c +
            (2 * (B c c * B c x)) • c := by
          rw [smul_sub, smul_smul, smul_smul, sub_eq_add_neg, sub_eq_add_neg,
            ← neg_smul, ← neg_smul, add_assoc, ← add_smul]
          have hs1 : B c c * B c c = B c c ^ 2 := by ring
          have hs2 : -(B c c * (2 * B c x)) + -(2 * (B c c * B c x - 2 * B c x * B c c)) =
              -(2 * (B c c * B c x)) + (2 * (B c c * B c x)) := by ring
          rw [hs1, hs2, add_smul, ← add_assoc, neg_smul, ← sub_eq_add_neg]
    _ = B c c ^ 2 • x := by
          rw [sub_add_cancel]

/-- **`Note VI` Cayley–Klein Curvature Dichotomy (`pp. 18, 23–24`)**:
1. Under polar reflection `quadricPolarReflect B c`, `cayleyKleinChord` scales uniformly by `(B c c)⁴`.
2. Along any ray `x + t • c` through `c`, `cayleyKleinChord B (x + t • c) x = t² * cayleyKleinChord B c x`.
3. Nondegenerate constant nonzero curvature (`B c c ≠ 0`) vs isotropic zero-curvature parabolic
   collapse (`B c c = 0`), where reflection collapses onto `c` and the chord reduces to `-(B c x)²`. -/
theorem noteVI_quadric_chord_dichotomy (B : M →ₗ[R] M →ₗ[R] R)
    (hsymm : ∀ u v : M, B u v = B v u) (c x y : M) (t : R) :
    (cayleyKleinChord B (quadricPolarReflect B c x) (quadricPolarReflect B c y) =
        B c c ^ 4 * cayleyKleinChord B x y) ∧
      (cayleyKleinChord B (x + t • c) x = t ^ 2 * cayleyKleinChord B c x) ∧
      (B c c = 0 →
        quadricPolarReflect B c x = -(2 * B c x) • c ∧
          quadricPolarReflect B c (quadricPolarReflect B c x) = 0 ∧
          cayleyKleinChord B c x = -(B c x) ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [cayleyKleinChord]
    rw [quadricPolarReflect_preserves_bilin B hsymm c x x,
        quadricPolarReflect_preserves_bilin B hsymm c y y,
        quadricPolarReflect_preserves_bilin B hsymm c x y]
    ring
  · have haddL : ∀ u v w : M, B (u + t • v) w = B u w + t * B v w := fun u v w => by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    have haddR : ∀ u v w : M, B u (v + t • w) = B u v + t * B u w := fun u v w => by
      simp only [map_add, map_smul, smul_eq_mul]
    dsimp [cayleyKleinChord]
    rw [haddL, haddL, haddR, haddR, hsymm x c]
    ring
  · intro h0
    refine ⟨?_, ?_, ?_⟩
    · simp [quadricPolarReflect, h0]
    · rw [quadricPolarReflect_involutive_scale, h0]
      simp
    · simp [cayleyKleinChord, h0]

/-- **Grassmann–Plücker–Klein Bridge II (`§10.1`, `Note VI`, `pp. 23–24`)**:
Connects projective line-space metric determination (constant vs zero curvature) to Plücker's
null-system conjugacy and tangential quadratic complexes:
1. A non-special linear complex `C` (`C.kleinQ ≠ 0`) defines a nondegenerate line-space polarity
   preserving the Klein quadric (`conjugatePolar_involutive_up_to_scale`, `conjugatePolar_kleinQ`),
   whereas an axis complex on the Klein quadric (`C.kleinQ = 0`) undergoes parabolic collapse
   onto the special complex `C` (`zero` square = zero curvature).
2. For any symmetric point quadric `G : Matrix (Fin 4) (Fin 4) R`, the Cayley–Klein chord agrees
   identically with Plücker's `secondCompound G` evaluation on `rayPlucker x y`, whose singular
   focal locus satisfies `universal_kummer_w_sq_factorization`. -/
theorem klein_noteVI_plucker_line_space_bridge
    (C P : Plucker6 ℝ) (G : Matrix (Fin 4) (Fin 4) ℝ) (hG : G.IsSymm)
    (x y : Fin 4 → ℝ) (k : Fin 4) :
    ((conjugatePolar C (conjugatePolar C P) = Plucker6.scale (C.kleinQ ^ 2) P) ∧
      ((conjugatePolar C P).kleinQ = C.kleinQ ^ 2 * P.kleinQ) ∧
      (C.kleinQ ≠ 0 → C.kleinQ ^ 2 ≠ 0) ∧
      (C.kleinQ = 0 →
        conjugatePolar C P = (Plucker6.scale (C.polar P) C).add (Plucker6.scale 0 P) ∧
          conjugatePolar C (conjugatePolar C P) = Plucker6.scale 0 P)) ∧
      (coordinates (rayPlucker x y) ⬝ᵥ (secondCompound G *ᵥ coordinates (rayPlucker x y)) =
        (x ⬝ᵥ (G *ᵥ x)) * (y ⬝ᵥ (G *ᵥ y)) - (x ⬝ᵥ (G *ᵥ y)) ^ 2) ∧
      ((coneChartMatrix (secondCompound G) x k).det =
        (x k) ^ 2 * kummerSingularQuartic (secondCompound G) x) := by
  refine ⟨⟨conjugatePolar_involutive_up_to_scale C P, conjugatePolar_kleinQ C P, ?_, ?_⟩,
      quadric_tangent_secondCompound_symm G hG x y,
      universal_kummer_w_sq_factorization (secondCompound G) x k⟩
  · exact fun hne => pow_ne_zero 2 hne
  · intro h0
    refine ⟨?_, ?_⟩
    · rw [conjugatePolar_eq, h0, neg_zero]
    · rw [conjugatePolar_involutive_up_to_scale, h0, zero_pow (by norm_num)]

end ProjectiveMetricAndNoteVI

/-! ## 2. Note VII: Binary Form Syzygies (Cayley) & Regular Tetrahedral Sphere (§5, Note VII) -/

section BinaryFormsAndTetrahedron

/-- Classical binary cubic form `a₀ u³ + 3 a₁ u² v + 3 a₂ u v² + a₃ v³` (`Note VII`, p. 24). -/
def binCubic {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ u v : R) : R :=
  a₀ * u ^ 3 + 3 * a₁ * u ^ 2 * v + 3 * a₂ * u * v ^ 2 + a₃ * v ^ 3

/-- Normalized Hessian quadratic covariant `Δ` of a binary cubic. -/
def binCubicHessian {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ u v : R) : R :=
  (a₀ * a₂ - a₁ ^ 2) * u ^ 2 + (a₀ * a₃ - a₁ * a₂) * u * v + (a₁ * a₃ - a₂ ^ 2) * v ^ 2

/-- Normalized Jacobian cubic covariant `Q` of a binary cubic. -/
def binCubicJacobian {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ u v : R) : R :=
  (a₀ ^ 2 * a₃ - 3 * a₀ * a₁ * a₂ + 2 * a₁ ^ 3) * u ^ 3 +
    3 * (a₀ * a₁ * a₃ - 2 * a₀ * a₂ ^ 2 + a₁ ^ 2 * a₂) * u ^ 2 * v +
    3 * (-a₀ * a₂ * a₃ + 2 * a₁ ^ 2 * a₃ - a₁ * a₂ ^ 2) * u * v ^ 2 +
    (-a₀ * a₃ ^ 2 + 3 * a₁ * a₂ * a₃ - 2 * a₂ ^ 3) * v ^ 3

/-- Discriminant `R` of a binary cubic (`Note VII`, p. 24). -/
def binCubicDiscriminant {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ : R) : R :=
  (a₀ * a₃ - a₁ * a₂) ^ 2 - 4 * (a₀ * a₂ - a₁ ^ 2) * (a₁ * a₃ - a₂ ^ 2)

/-- **Cayley's Binary Cubic Syzygy (`Note VII`, pp. 24–25)**: `Q² + 4 Δ³ - R f² = 0`. -/
theorem cayley_binary_cubic_syzygy {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ u v : R) :
    binCubicJacobian a₀ a₁ a₂ a₃ u v ^ 2 +
      4 * binCubicHessian a₀ a₁ a₂ a₃ u v ^ 3 -
      binCubicDiscriminant a₀ a₁ a₂ a₃ * binCubic a₀ a₁ a₂ a₃ u v ^ 2 = 0 := by
  dsimp [binCubicJacobian, binCubicHessian, binCubicDiscriminant, binCubic]
  ring

theorem cayley_binary_cubic_canonical {R : Type*} [CommRing R] (u v : R) :
    binCubic (1 : R) 0 0 (-1) u v = u ^ 3 - v ^ 3 ∧
      binCubicHessian (1 : R) 0 0 (-1) u v = -(u * v) ∧
      binCubicJacobian (1 : R) 0 0 (-1) u v = -(u ^ 3 + v ^ 3) ∧
      binCubicDiscriminant (1 : R) 0 0 (-1) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (dsimp [binCubic, binCubicHessian, binCubicJacobian, binCubicDiscriminant]; ring)

/-- Classical binary quartic form `a₀ u⁴ + 4 a₁ u³ v + 6 a₂ u² v² + 4 a₃ u v³ + a₄ v⁴` (`Note VII`). -/
def binQuartic {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ a₄ u v : R) : R :=
  a₀ * u ^ 4 + 4 * a₁ * u ^ 3 * v + 6 * a₂ * u ^ 2 * v ^ 2 + 4 * a₃ * u * v ^ 3 + a₄ * v ^ 4

/-- Equianharmonic invariant `i = a₀ a₄ - 4 a₁ a₃ + 3 a₂²` of a binary quartic. -/
def quarticInvI {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ a₄ : R) : R :=
  a₀ * a₄ - 4 * a₁ * a₃ + 3 * a₂ ^ 2

/-- Catalecticant invariant `j` of a binary quartic. -/
def quarticInvJ {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ a₄ : R) : R :=
  a₀ * a₂ * a₄ + 2 * a₁ * a₂ * a₃ - a₀ * a₃ ^ 2 - a₄ * a₁ ^ 2 - a₂ ^ 3

/-- Normalized Hessian quartic covariant `H` of a binary quartic. -/
def binQuarticHessian {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ a₄ u v : R) : R :=
  (a₀ * a₂ - a₁ ^ 2) * u ^ 4 +
    (2 * a₀ * a₃ - 2 * a₁ * a₂) * u ^ 3 * v +
    (a₀ * a₄ + 2 * a₁ * a₃ - 3 * a₂ ^ 2) * u ^ 2 * v ^ 2 +
    (2 * a₁ * a₄ - 2 * a₂ * a₃) * u * v ^ 3 +
    (a₂ * a₄ - a₃ ^ 2) * v ^ 4

/-- Normalized Jacobian sextic covariant `T` of a binary quartic. -/
def binQuarticSexticCovariant {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ a₄ u v : R) : R :=
  (a₀ ^ 2 * a₃ - 3 * a₀ * a₁ * a₂ + 2 * a₁ ^ 3) * u ^ 6 +
    (a₀ ^ 2 * a₄ + 2 * a₀ * a₁ * a₃ - 9 * a₀ * a₂ ^ 2 + 6 * a₁ ^ 2 * a₂) * u ^ 5 * v +
    (5 * a₀ * a₁ * a₄ - 15 * a₀ * a₂ * a₃ + 10 * a₁ ^ 2 * a₃) * u ^ 4 * v ^ 2 +
    (-10 * a₀ * a₃ ^ 2 + 10 * a₁ ^ 2 * a₄) * u ^ 3 * v ^ 3 +
    (-5 * a₀ * a₃ * a₄ + 15 * a₁ * a₂ * a₄ - 10 * a₁ * a₃ ^ 2) * u ^ 2 * v ^ 4 +
    (-a₀ * a₄ ^ 2 - 2 * a₁ * a₃ * a₄ + 9 * a₂ ^ 2 * a₄ - 6 * a₂ * a₃ ^ 2) * u * v ^ 5 +
    (-a₁ * a₄ ^ 2 + 3 * a₂ * a₃ * a₄ - 2 * a₃ ^ 3) * v ^ 6

/-- **Cayley's Binary Quartic Syzygy (`Note VII`, pp. 24–25)**: `T² + 4 H³ - i H f² + j f³ = 0`. -/
theorem cayley_binary_quartic_syzygy {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ a₄ u v : R) :
    binQuarticSexticCovariant a₀ a₁ a₂ a₃ a₄ u v ^ 2 +
      4 * binQuarticHessian a₀ a₁ a₂ a₃ a₄ u v ^ 3 -
      quarticInvI a₀ a₁ a₂ a₃ a₄ * binQuarticHessian a₀ a₁ a₂ a₃ a₄ u v *
        binQuartic a₀ a₁ a₂ a₃ a₄ u v ^ 2 +
      quarticInvJ a₀ a₁ a₂ a₃ a₄ * binQuartic a₀ a₁ a₂ a₃ a₄ u v ^ 3 = 0 := by
  dsimp [binQuarticSexticCovariant, binQuarticHessian, quarticInvI, quarticInvJ, binQuartic]
  ring

/-- **Klein's `Note VII` Tetrahedral Sphere & Coordinate-Axis Bisection Theorem (`§5`, `Note VII`, p. 25)**:
Given any `V₄`-tetrahedron `(x, y, z), (x, -y, -z), (-x, y, -z), (-x, -y, z)`:
1. All four vertices lie on the sphere `v ⬝ᵥ v = x² + y² + z²`, with equal pairwise squared edges
   when `x = y = z = c`.
2. Opposite-edge midpoints lie strictly on the three coordinate axes fixed by `V₄` involutions:
   `m₀₁ = ![x, 0, 0]`, `m₂₃ = ![-x, 0, 0]`, `m₀₂ = ![0, y, 0]`, `m₁₃ = ![0, -y, 0]`,
   `m₀₃ = ![0, 0, z]`, `m₁₂ = ![0, 0, -z]`.
3. For a regular tetrahedron (`x = y = z = c`), vertex squared distance `3 c²` equals `3` times the
   edge-midpoint axis distance `c²` (`Note VII`, octant-bisecting sphere points). -/
theorem noteVII_tetrahedral_sphere_axis_bisection (x y z c : ℝ) :
    let v₀ : Fin 3 → ℝ := ![x, y, z]
    let v₁ : Fin 3 → ℝ := ![x, -y, -z]
    let v₂ : Fin 3 → ℝ := ![-x, y, -z]
    let v₃ : Fin 3 → ℝ := ![-x, -y, z]
    (v₀ ⬝ᵥ v₀ = x ^ 2 + y ^ 2 + z ^ 2 ∧
      v₁ ⬝ᵥ v₁ = x ^ 2 + y ^ 2 + z ^ 2 ∧
      v₂ ⬝ᵥ v₂ = x ^ 2 + y ^ 2 + z ^ 2 ∧
      v₃ ⬝ᵥ v₃ = x ^ 2 + y ^ 2 + z ^ 2) ∧
    (((1 / 2 : ℝ) • (v₀ + v₁) = ![x, 0, 0]) ∧
      ((1 / 2 : ℝ) • (v₂ + v₃) = ![-x, 0, 0]) ∧
      ((1 / 2 : ℝ) • (v₀ + v₂) = ![0, y, 0]) ∧
      ((1 / 2 : ℝ) • (v₁ + v₃) = ![0, -y, 0]) ∧
      ((1 / 2 : ℝ) • (v₀ + v₃) = ![0, 0, z]) ∧
      ((1 / 2 : ℝ) • (v₁ + v₂) = ![0, 0, -z])) ∧
    (let w₀ : Fin 3 → ℝ := ![c, c, c]
     let w₁ : Fin 3 → ℝ := ![c, -c, -c]
     let w₂ : Fin 3 → ℝ := ![-c, c, -c]
     let m := (1 / 2 : ℝ) • (w₀ + w₁)
     w₀ ⬝ᵥ w₀ = 3 * (m ⬝ᵥ m) ∧
       (w₀ - w₁) ⬝ᵥ (w₀ - w₁) = (w₀ - w₂) ⬝ᵥ (w₀ - w₂) ∧
       (w₀ - w₁) ⬝ᵥ (w₀ - w₁) = 8 * c ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (simp [dotProduct, Fin.sum_univ_three]; ring)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (ext i; fin_cases i <;> (simp; try ring))
  · refine ⟨?_, ?_, ?_⟩ <;>
      (simp [dotProduct, Fin.sum_univ_three]; try ring)

end BinaryFormsAndTetrahedron

/-! ## 3. Concluding Remarks: Galois Bridge, Klein–Lie [17], & Footnote 37 Spinors -/

section GaloisLie17AndSpinors

/-- Non-commutativity witness for `Matrix (Fin 3) (Fin 3) R`. -/
theorem matrix3_erlangen_noncomm {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 3) (Fin 3) R, A * B ≠ B * A := by
  refine ⟨Matrix.of (fun i j => if i = 0 ∧ j = 1 then 1 else 0),
          Matrix.of (fun i j => if i = 1 ∧ j = 0 then 1 else 0), ?_⟩
  intro h
  have h00 := congrArg (fun M => M 0 0) h
  simp [Matrix.mul_apply] at h00

/-- **Concluding Remarks Galois Bridge (`p. 19`)**:
Pairs the operator–observable Galois connection `subgroup_le_fixingSubgroup_iff`
(`OperatorErlangenFixedPoints`) with `IsGeometricInvariant` monotonicity along subgroups. -/
theorem erlangen_galois_subgroup_observable_bridge
    {G A M : Type*} [Group G] [Semiring A] [MulSemiringAction G A] [MulAction G M]
    (H K : Subgroup G) (hHK : H ≤ K) (S T : Set A) (hST : S ⊆ T)
    (P : M → Prop) :
    ((H ≤ fixingSubgroup (G := G) (A := A) S ↔
        S ⊆ fixedPointSet (G := G) (A := A) H) ∧
      fixingSubgroup (G := G) (A := A) T ≤ fixingSubgroup (G := G) (A := A) S ∧
      fixedPointSet (G := G) (A := A) K ⊆ fixedPointSet (G := G) (A := A) H ∧
      (IsGeometricInvariant K M P → IsGeometricInvariant H M P)) := by
  refine ⟨subgroup_le_fixingSubgroup_iff, fixingSubgroup_antitone hST,
    fixedPointSet_antitone hHK, ?_⟩
  exact fun hP => isGeometricInvariant_mono_subgroup hHK hP

/-- Diagonal `3 × 3` commuting linear-group family corresponding to Klein–Lie's general-position
`W`-curve / cross-ratio projective group (`§3`, `Footnote 13`, `Ref. [17]`). -/
def wCurveDiagMatrix {R : Type*} [CommRing R] (a b c : R) : Matrix (Fin 3) (Fin 3) R :=
  ![ ![a, 0, 0], ![0, b, 0], ![0, 0, c] ]

/-- Unipotent affine translation/shear `3 × 3` commuting matrix family (`Ref. [17]`). -/
def wCurveUnipMatrix {R : Type*} [CommRing R] (u v : R) : Matrix (Fin 3) (Fin 3) R :=
  ![ ![1, u, v], ![0, 1, 0], ![0, 0, 1] ]

theorem wCurveDiagMatrix_mul_comm {R : Type*} [CommRing R]
    (a₁ b₁ c₁ a₂ b₂ c₂ : R) :
    wCurveDiagMatrix a₁ b₁ c₁ * wCurveDiagMatrix a₂ b₂ c₂ =
        wCurveDiagMatrix (a₁ * a₂) (b₁ * b₂) (c₁ * c₂) ∧
      wCurveDiagMatrix a₁ b₁ c₁ * wCurveDiagMatrix a₂ b₂ c₂ =
        wCurveDiagMatrix a₂ b₂ c₂ * wCurveDiagMatrix a₁ b₁ c₁ := by
  have hmul : ∀ x₁ y₁ z₁ x₂ y₂ z₂ : R,
      wCurveDiagMatrix x₁ y₁ z₁ * wCurveDiagMatrix x₂ y₂ z₂ =
        wCurveDiagMatrix (x₁ * x₂) (y₁ * y₂) (z₁ * z₂) := by
    intro x₁ y₁ z₁ x₂ y₂ z₂
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> (simp [wCurveDiagMatrix]; try ring)
  refine ⟨hmul a₁ b₁ c₁ a₂ b₂ c₂, ?_⟩
  rw [hmul a₁ b₁ c₁ a₂ b₂ c₂, hmul a₂ b₂ c₂ a₁ b₁ c₁,
    mul_comm a₁ a₂, mul_comm b₁ b₂, mul_comm c₁ c₂]

theorem wCurveUnipMatrix_add_comm {R : Type*} [CommRing R] (u₁ v₁ u₂ v₂ : R) :
    wCurveUnipMatrix u₁ v₁ * wCurveUnipMatrix u₂ v₂ =
        wCurveUnipMatrix (u₁ + u₂) (v₁ + v₂) ∧
      wCurveUnipMatrix u₁ v₁ * wCurveUnipMatrix u₂ v₂ =
        wCurveUnipMatrix u₂ v₂ * wCurveUnipMatrix u₁ v₁ := by
  have hmul : ∀ x₁ y₁ x₂ y₂ : R,
      wCurveUnipMatrix x₁ y₁ * wCurveUnipMatrix x₂ y₂ =
        wCurveUnipMatrix (x₁ + x₂) (y₁ + y₂) := by
    intro x₁ y₁ x₂ y₂
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> (simp [wCurveUnipMatrix]; try ring)
  refine ⟨hmul u₁ v₁ u₂ v₂, ?_⟩
  rw [hmul u₁ v₁ u₂ v₂, hmul u₂ v₂ u₁ v₁, add_comm u₁ u₂, add_comm v₁ v₂]

/-- **Footnote 37 (`p. 19`) Quaternion / Spinor Double Cover of `SO(3)`**:
Maps a quaternion `q = (q₀, q₁, q₂, q₃)` to its orthogonal `3 × 3` matrix representation `q v q̄`. -/
def quatRotMatrix {R : Type*} [CommRing R] (q₀ q₁ q₂ q₃ : R) : Matrix (Fin 3) (Fin 3) R :=
  ![ ![q₀ ^ 2 + q₁ ^ 2 - q₂ ^ 2 - q₃ ^ 2, 2 * (q₁ * q₂ - q₀ * q₃), 2 * (q₁ * q₃ + q₀ * q₂)],
     ![2 * (q₁ * q₂ + q₀ * q₃), q₀ ^ 2 - q₁ ^ 2 + q₂ ^ 2 - q₃ ^ 2, 2 * (q₂ * q₃ - q₀ * q₁)],
     ![2 * (q₁ * q₃ - q₀ * q₂), 2 * (q₂ * q₃ + q₀ * q₁), q₀ ^ 2 - q₁ ^ 2 - q₂ ^ 2 + q₃ ^ 2] ]

theorem quatRotMatrix_neg {R : Type*} [CommRing R] (q₀ q₁ q₂ q₃ : R) :
    quatRotMatrix (-q₀) (-q₁) (-q₂) (-q₃) = quatRotMatrix q₀ q₁ q₂ q₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quatRotMatrix]

theorem quatRotMatrix_mul {R : Type*} [CommRing R] (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : R) :
    quatRotMatrix
        (p₀ * q₀ - p₁ * q₁ - p₂ * q₂ - p₃ * q₃)
        (p₀ * q₁ + p₁ * q₀ + p₂ * q₃ - p₃ * q₂)
        (p₀ * q₂ - p₁ * q₃ + p₂ * q₀ + p₃ * q₁)
        (p₀ * q₃ + p₁ * q₂ - p₂ * q₁ + p₃ * q₀) =
      quatRotMatrix p₀ p₁ p₂ p₃ * quatRotMatrix q₀ q₁ q₂ q₃ := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> (simp [quatRotMatrix]; ring)

theorem quatRotMatrix_orthog_of_unit {R : Type*} [CommRing R] (q₀ q₁ q₂ q₃ : R)
    (hunit : q₀ ^ 2 + q₁ ^ 2 + q₂ ^ 2 + q₃ ^ 2 = 1) :
    (quatRotMatrix q₀ q₁ q₂ q₃)ᵀ * quatRotMatrix q₀ q₁ q₂ q₃ = 1 ∧
      (quatRotMatrix q₀ q₁ q₂ q₃).det = 1 := by
  have hnorm : q₀ ^ 2 + q₁ ^ 2 + q₂ ^ 2 + q₃ ^ 2 = 1 := hunit
  have horth : (quatRotMatrix q₀ q₁ q₂ q₃)ᵀ * quatRotMatrix q₀ q₁ q₂ q₃ =
      ((q₀ ^ 2 + q₁ ^ 2 + q₂ ^ 2 + q₃ ^ 2) ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R) := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> (simp [quatRotMatrix]; ring)
  have hdet : (quatRotMatrix q₀ q₁ q₂ q₃).det =
      (q₀ ^ 2 + q₁ ^ 2 + q₂ ^ 2 + q₃ ^ 2) ^ 3 := by
    rw [Matrix.det_fin_three]
    simp [quatRotMatrix]
    ring
  refine ⟨?_, ?_⟩
  · rw [horth, hnorm, one_pow, one_smul]
  · rw [hdet, hnorm, one_pow]

end GaloisLie17AndSpinors

/-! ## 4. Nine-Node Causal Poset & Unified Grassmann–Plücker–Klein Trilogy Synthesis -/

section EpistemicPosetAndTrilogySynthesis

/-- Nine causal mathematical archetypes extracted from Felix Klein's 1872 *Erlangen Program*
(`0807.3161v1 (1).pdf`, `pp. 1–26`). -/
inductive ErlangenProgramArchetype : Type
  | EK1 -- §§1–2, Footnote 8: Transformation groups, dualistic Zˣ grading, Subgroup Adjoining
  | EK2 -- §3, §10.3: Principal Group & Projective Circle-at-Infinity Characterization
  | EK3 -- §§4–5: Transfer Principle, Veronese Conic, Hesse Transference & Bridge I
  | EK4 -- §5, Footnote 23: Klein Bodies (MulAction.orbit) & S₄/V₄ Normal Kernel Countermodel
  | EK5 -- §6, Footnote 26: Reciprocal Radii, Lightcone Lift & Antiholomorphic Countermodel
  | EK6 -- §7, Footnote 31: Lie Sphere Geometry O(3,2) & Grassmann Circle Bridge III
  | EK7 -- §§8–9: Cremona, Contact 5D, Legendre Pullback, Clebsch & Bridge IV (No. 511)
  | EK8 -- §10, Concluding Remarks, Notes VI–VII: Note VI/Plücker Bridge II, Cayley Syzygies, Lie [17], SO(3) Spinor
  | EK9 -- Master Erlangen 1872 Synthesis & Grassmann–Plücker–Klein Trilogy Synthesis
  deriving DecidableEq, Repr

/-- Transitive closure dependency bitmask encoding the nonlinear Erlangen 1872 DAG on `Fin 9`. -/
def erlangenMask : ErlangenProgramArchetype → UInt16
  | .EK1 => 0b000000001
  | .EK2 => 0b000000011 -- ≥ EK1
  | .EK3 => 0b000000101 -- ≥ EK1
  | .EK4 => 0b000001111 -- ≥ EK1, EK2, EK3
  | .EK5 => 0b000010011 -- ≥ EK1, EK2
  | .EK6 => 0b000111111 -- ≥ EK1..EK5
  | .EK7 => 0b001000111 -- ≥ EK1, EK2, EK3
  | .EK8 => 0b011001111 -- ≥ EK1..EK4, EK7
  | .EK9 => 0b111111111 -- ≥ EK1..EK8

instance : LE ErlangenProgramArchetype where
  le a b := (erlangenMask a &&& erlangenMask b) = erlangenMask a

instance (a b : ErlangenProgramArchetype) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable ((erlangenMask a &&& erlangenMask b) = erlangenMask a))

instance : PartialOrder ErlangenProgramArchetype where
  le := (· ≤ ·)
  le_refl a := by cases a <;> decide
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide

theorem erlangen_causal_poset_branching_witnesses :
    (¬ (ErlangenProgramArchetype.EK2 ≤ .EK3) ∧
      ¬ (ErlangenProgramArchetype.EK3 ≤ .EK2)) ∧
    (¬ (ErlangenProgramArchetype.EK5 ≤ .EK7) ∧
      ¬ (ErlangenProgramArchetype.EK7 ≤ .EK5)) ∧
    (¬ (ErlangenProgramArchetype.EK6 ≤ .EK8) ∧
      ¬ (ErlangenProgramArchetype.EK8 ≤ .EK6)) := by
  decide

theorem erlangen_all_reach_master (a : ErlangenProgramArchetype) :
    a ≤ ErlangenProgramArchetype.EK9 := by
  cases a <;> decide

/-- **Master Erlangen 1872 Synthesis (`EK₉`)**:
Unifies all eight Erlangen archetypes: Footnote 8 infinite-semigroup countermodel, principal
circle-at-infinity characterization, Veronese conic `symSq2` covariance, Footnote 23 `S₄/V₄`
body countermodel, Footnote 26 inversion countermodel, Lie `O(3,2)` radius dilation, Legendre
contact pullback, Note VII Cayley binary cubic/quartic syzygies, and Footnote 37 `SU(2) → SO(3)`. -/
theorem klein_erlangen_1872_master_synthesis :
    (¬ ∃ inv : ℕ → ℕ, inv ∘ natShift 1 = id ∧ natShift 1 ∘ inv = id) ∧
    (∀ (A : Matrix (Fin 4) (Fin 4) ℝ), A 0 0 ≠ 0 → ∀ (μ : ℝ), μ ≠ 0 →
      (((A 0 1 = 0 ∧ A 0 2 = 0 ∧ A 0 3 = 0) ∧
        (∀ y : Fin 3 → ℝ,
          let w := A *ᵥ ![0, y 0, y 1, y 2]
          w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 = μ ^ 2 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2))) ↔
      ∃ (Q : Matrix (Fin 3) (Fin 3) ℝ) (t : Fin 3 → ℝ),
        Qᵀ * Q = 1 ∧ A = projSimilarityMatrix (A 0 0) μ Q t)) ∧
    (∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 3 → ℝ),
      conicQuadric (symSq2 M *ᵥ x) = M.det ^ 2 * conicQuadric x) ∧
    (orbitActionKernel (Equiv.Perm (Fin 4)) doublePair0).Normal ∧
      (∀ y ∈ MulAction.orbit (Equiv.Perm (Fin 4)) doublePair0, s4V4Witness • y = y) ∧
    (¬ ∃ a b c d : ℂ, ∀ z : ℂ, z ≠ 0 →
      (starRingEnd ℂ z)⁻¹ = (a * z + b) / (c * z + d)) ∧
    (∀ (t : ℝ) (u v : Fin 5 → ℝ),
      lieBilin (lieRadiusDilMatrix t *ᵥ u) (lieRadiusDilMatrix t *ᵥ v) = lieBilin u v) ∧
    (∀ (e δ : Fin 5 → ℝ),
      contactOneForm (legendreContact e) (legendreContactDiff e δ) = -contactOneForm e δ) ∧
    (∀ a₀ a₁ a₂ a₃ u v : ℝ,
      binCubicJacobian a₀ a₁ a₂ a₃ u v ^ 2 + 4 * binCubicHessian a₀ a₁ a₂ a₃ u v ^ 3 -
        binCubicDiscriminant a₀ a₁ a₂ a₃ * binCubic a₀ a₁ a₂ a₃ u v ^ 2 = 0) ∧
    (∀ a₀ a₁ a₂ a₃ a₄ u v : ℝ,
      binQuarticSexticCovariant a₀ a₁ a₂ a₃ a₄ u v ^ 2 +
        4 * binQuarticHessian a₀ a₁ a₂ a₃ a₄ u v ^ 3 -
        quarticInvI a₀ a₁ a₂ a₃ a₄ * binQuarticHessian a₀ a₁ a₂ a₃ a₄ u v *
          binQuartic a₀ a₁ a₂ a₃ a₄ u v ^ 2 +
        quarticInvJ a₀ a₁ a₂ a₃ a₄ * binQuartic a₀ a₁ a₂ a₃ a₄ u v ^ 3 = 0) ∧
    (∀ q₀ q₁ q₂ q₃ : ℝ, q₀ ^ 2 + q₁ ^ 2 + q₂ ^ 2 + q₃ ^ 2 = 1 →
      (quatRotMatrix q₀ q₁ q₂ q₃)ᵀ * quatRotMatrix q₀ q₁ q₂ q₃ = 1 ∧
        (quatRotMatrix q₀ q₁ q₂ q₃).det = 1) := by
  refine ⟨klein_footnote8_infinite_semigroup_countermodel.2.2.2,
    projective_circleAtInfinity_stabilizer_iff_similarity3, conicQuadric_symSq2,
    klein_footnote23_s4_v4_countermodel.1, klein_footnote23_s4_v4_countermodel.2.2.2,
    klein_footnote26_inversion_not_holomorphic_mobius,
    lieRadiusDilMatrix_preserves_lieBilin, contactOneForm_legendre_pullback,
    cayley_binary_cubic_syzygy, cayley_binary_quartic_syzygy, ?_⟩
  exact fun q₀ q₁ q₂ q₃ hu => quatRotMatrix_orthog_of_unit q₀ q₁ q₂ q₃ hu

/-- **Unified Grassmann (1862) ↔ Plücker (1868/1869) ↔ Klein (1872) Trilogy Synthesis**:
Joint kernel-checked bridge theorem connecting all four cross-work bridges across the
*Ausdehnungslehre*, *Neue Geometrie des Raumes*, and *Erlangen Program*:
1. **Bridge I (Senary Exterior / Line / Split `O(3,3)` Unification)**:
   Grassmann alternating `2`-blades `grassmannBladeToPlucker` carry Plücker's `15`-minor
   ray–axis coincidence (`ray_axis_minors_eq_of_four_incidences`), `GL₄` `secondCompound`
   covariance, Klein's `det` relative invariance, and `SO(3,3)` split-senary form.
2. **Bridge II (`Note VI` Projective Line-Space Curvature ↔ Plücker Complex & Kummer Focal Surface)**:
   Adjoining a linear complex `C` separates nondegenerate nonzero-curvature polarities
   (`C.kleinQ ≠ 0`) from parabolic collapse (`C.kleinQ = 0`), while `secondCompound G` identifies
   the Cayley–Klein point-quadric chord with the Kummer focal locus (`universal_kummer_w_sq_factorization`).
3. **Bridge III (Lie `5D` Sphere Space `O(3,2)` → Grassmann `4D` Circle Space `O(1,3)`)**:
   Radius-dilating `O(3,2)` maps project cleanly to `circleVec` and characterize unoriented
   Grassmann circle tangency (`IsCircleTangent`) as signed-radius Lie orthogonality.
4. **Bridge IV (Klein–Lie `5D` Contact `ω ∧ Ω²` ↔ Grassmann `No. 511` Pfaffian Filtration)**:
   Strict `5D` contact nondegeneracy (`volCoord b (ω * Ω²) = -2 ≠ 0`) under Legendre involution
   sits right above Grassmann `No. 511` (`pfaffJetOneForm u α * pfaffJetTwoForm β α ^ 2 = 0`). -/
theorem grassmann_plucker_klein_trilogy_synthesis :
    ((∀ (x y u v : Fin 4 → ℝ),
      (∑ k, u k * x k = 0) → (∑ k, u k * y k = 0) →
      (∑ k, v k * x k = 0) → (∑ k, v k * y k = 0) →
      ∀ i j, grassmannBladeToPlucker ℝ ![x, y] i *
          coordinates (axisAsRayPlucker u v) j =
        grassmannBladeToPlucker ℝ ![x, y] j *
          coordinates (axisAsRayPlucker u v) i) ∧
      (∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (P : Plucker6 ℝ),
        (transform A P).kleinQ = A.det * P.kleinQ)) ∧
    (∀ (C P : Plucker6 ℝ) (G : Matrix (Fin 4) (Fin 4) ℝ), G.IsSymm →
      ∀ (x y : Fin 4 → ℝ) (k : Fin 4),
        conjugatePolar C (conjugatePolar C P) = Plucker6.scale (C.kleinQ ^ 2) P ∧
        (coordinates (rayPlucker x y) ⬝ᵥ (secondCompound G *ᵥ coordinates (rayPlucker x y)) =
          (x ⬝ᵥ (G *ᵥ x)) * (y ⬝ᵥ (G *ᵥ y)) - (x ⬝ᵥ (G *ᵥ y)) ^ 2) ∧
        (coneChartMatrix (secondCompound G) x k).det =
          (x k) ^ 2 * kummerSingularQuartic (secondCompound G) x) ∧
    ((∀ (a b r t : ℝ),
        lieToGrassmannCircleProj (lieCircleVec a b r) =
          InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace.circleVec a b r ∧
        lieBilin (lieRadiusDilMatrix t *ᵥ lieCircleVec a b r)
            (lieRadiusDilMatrix t *ᵥ lieCircleVec a b r) = 0) ∧
      (∀ a₁ b₁ r₁ a₂ b₂ r₂ : ℝ,
        InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace.IsCircleTangent
            (InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace.circleVec a₁ b₁ r₁)
            (InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace.circleVec a₂ b₂ r₂) ↔
          lieBilin (lieCircleVec a₁ b₁ r₁) (lieCircleVec a₂ b₂ r₂) = 0 ∨
            lieBilin (lieCircleVec a₁ b₁ r₁) (lieCircleVec a₂ b₂ (-r₂)) = 0)) ∧
    (∀ (p q : ℝ) (e δ : Fin 5 → ℝ),
      contactOneForm (legendreContact e) (legendreContactDiff e δ) = -contactOneForm e δ ∧
      (let b := Pi.basisFun ℝ (Fin 5)
       let ι := ExteriorAlgebra.ι ℝ
       let ω := ι (b 2) - p • ι (b 0) - q • ι (b 1)
       let Ω := ι (b 3) * ι (b 0) + ι (b 4) * ι (b 1)
       InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow.volCoord b (ω * Ω ^ 2) = -2 ∧
       ω * Ω ^ 2 ≠ 0) ∧
      (∀ (M : Type) [AddCommGroup M] [Module ℝ M] (u : Fin 2 → ℝ) (α β : Fin 2 → M),
        InfoGeometry.Canonical.GrassmannPfaffianDarbouxAlgebra.pfaffJetOneForm u α *
          InfoGeometry.Canonical.GrassmannPfaffianDarbouxAlgebra.pfaffJetTwoForm β α ^ 2 = 0)) := by
  have hsen := @grassmann_plucker_senary_unification.{0, 0} ℝ _
  refine ⟨⟨hsen.1, hsen.2.1⟩,
    ?_, ⟨?_, grassmann_tangency_iff_signed_lie_orthogonality⟩, ?_⟩
  · intro C P G hG x y k
    have hbr := klein_noteVI_plucker_line_space_bridge C P G hG x y k
    exact ⟨hbr.1.1, hbr.2.1, hbr.2.2⟩
  · intro a b r t
    refine ⟨lieToGrassmannCircleProj_circleVec a b r, ?_⟩
    rw [lieRadiusDilMatrix_preserves_lieBilin, lieCircleVec_isNull]
  · intro p q e δ
    have hpf := grassmann_pfaff_contact5 p q
    exact ⟨contactOneForm_legendre_pullback e δ, hpf.1, hpf.2⟩

end EpistemicPosetAndTrilogySynthesis

end InfoGeometry.Erlangen.ErlangenProgramCurvatureBinaryAndMasterAtlas
