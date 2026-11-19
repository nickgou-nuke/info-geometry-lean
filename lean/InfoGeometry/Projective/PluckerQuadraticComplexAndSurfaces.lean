/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.PluckerRayAxisAndDyname
import InfoGeometry.Projective.PluckerQuadraticComplex

/-!
# Quadratic Complexes, Ternary Splitting, Central Parallelepiped, and Quadric Tangents

This module formalizes Archetypes `PL₆` (`Abth. I, Complexe 2. Grades §§1–7, Nos. 149–233`) and
`PL₇` (`Abth. II §§1–3, Nos. 234–290`) of Julius Plücker's *Neue Geometrie des Raumes*
(`Liniengeometriev1.pdf`, pp. 153–274):

* Dimension count of the space of quadratic complexes (`symmMat6Submodule`, `symmMat6EquivFin21`,
  `finrank_symmMat6 = 21`, `finrank_quadraticComplexQuotient = 20`, hence `19` inhomogeneous
  constants, `No. 149`, `p. 153`), and Klein-ambiguity invariance of cones/conics.
* Ternary conic splitting criterion (`Eqs. (6.37)–(6.39)`, `ternary_double_line_factorization`,
  `ternary_rank2_schur_splitting`) and meridian double-line multiplicity / degree law
  (`2*n*(n-1)`, `n*(n-1)`, `Nos. 225–233`).
* Central Parallelepiped opposite vertices `G` and `H` (`Nos. 240–244`, `pp. 228–231`), true
  midpoint `(G + H) / 2`, and `[countermodel_found]` `eq121_printed_omits_factor_two` documenting
  that printed `Eq. (1.21)` (`p. 230`) omits the factor `1/2`.
* Exact `secondCompound` identity (`quadric_tangent_secondCompound_identity`) showing the complex of
  lines tangent to a point quadric `xᵀ G x = 0` is given by `Pᵀ (C₂ G) P = (xᵀ G x)(yᵀ G y) - (xᵀ G y)²`
  (`Nos. 251–274`).
-/

namespace InfoGeometry.Projective.PluckerQuadraticComplexAndSurfaces

open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.PluckerMatrixAction
open InfoGeometry.Projective.PluckerAffineScrew
open InfoGeometry.Projective.PluckerRayAxisAndDyname
open Matrix

section SpaceOfQuadraticComplexes

/-- Submodule of symmetric `6 × 6` matrices representing homogeneous quadratic forms on `K⁶`. -/
def symmMat6Submodule (R : Type*) [CommRing R] :
    Submodule R (Matrix (Fin 6) (Fin 6) R) where
  carrier := {S | S.IsSymm}
  zero_mem' := by simp [Matrix.IsSymm]
  add_mem' {A B} hA hB := by
    change (A + B)ᵀ = A + B
    rw [Matrix.transpose_add, hA, hB]
  smul_mem' c {A} hA := by
    change (c • A)ᵀ = c • A
    rw [Matrix.transpose_smul, hA]

private def symm6From21 {R : Type*} (v : Fin 21 → R) : Matrix (Fin 6) (Fin 6) R :=
  ![ ![v 0,  v 1,  v 2,  v 3,  v 4,  v 5],
     ![v 1,  v 6,  v 7,  v 8,  v 9,  v 10],
     ![v 2,  v 7,  v 11, v 12, v 13, v 14],
     ![v 3,  v 8,  v 12, v 15, v 16, v 17],
     ![v 4,  v 9,  v 13, v 16, v 18, v 19],
     ![v 5,  v 10, v 14, v 17, v 19, v 20] ]

private lemma symm6From21_isSymm {R : Type*} (v : Fin 21 → R) :
    (symm6From21 v).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private def symm6To21 {R : Type*} (S : Matrix (Fin 6) (Fin 6) R) : Fin 21 → R :=
  ![ S 0 0, S 0 1, S 0 2, S 0 3, S 0 4, S 0 5,
     S 1 1, S 1 2, S 1 3, S 1 4, S 1 5,
     S 2 2, S 2 3, S 2 4, S 2 5,
     S 3 3, S 3 4, S 3 5,
     S 4 4, S 4 5,
     S 5 5 ]

/-- Explicit `R`-linear isomorphism between symmetric `6 × 6` matrices and `Fin 21 → R`
(`21` quadratic coefficients on Plücker coordinates, `Plücker No. 149`). -/
def symmMat6EquivFin21 (R : Type*) [CommRing R] :
    symmMat6Submodule R ≃ₗ[R] (Fin 21 → R) where
  toFun S := symm6To21 S.1
  invFun v := ⟨symm6From21 v, symm6From21_isSymm v⟩
  map_add' A B := by
    ext k; fin_cases k <;> rfl
  map_smul' c A := by
    ext k; fin_cases k <;> rfl
  left_inv S := by
    ext i j
    have hSymm : S.1.IsSymm := S.2
    have hS : ∀ a b : Fin 6, S.1 a b = S.1 b a := fun a b =>
      (congrFun (congrFun hSymm a) b).symm
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact hS _ _
  right_inv v := by
    ext k; fin_cases k <;> rfl

theorem finrank_symmMat6 (K : Type*) [Field K] :
    Module.finrank K (symmMat6Submodule K) = 21 := by
  rw [(symmMat6EquivFin21 K).finrank_eq, Module.finrank_fin_fun]

/-- Symmetric `6 × 6` matrix `((1/2) * polarDotMatrix)` representing `P.kleinQ` as a quadratic form
over `ℝ` (hence `K` of char `≠ 2`). -/
noncomputable def kleinSymmMatrix : symmMat6Submodule ℝ :=
  ⟨((2 : ℝ)⁻¹) • polarDotMatrix, by
    change (((2 : ℝ)⁻¹) • (polarDotMatrix : Matrix (Fin 6) (Fin 6) ℝ))ᵀ =
      ((2 : ℝ)⁻¹) • polarDotMatrix
    rw [Matrix.transpose_smul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩

theorem kleinSymmMatrix_ne_zero : kleinSymmMatrix ≠ 0 := by
  intro h
  have h05 : kleinSymmMatrix.1 0 5 = (0 : Matrix (Fin 6) (Fin 6) ℝ) 0 5 := by
    rw [h]; rfl
  change ((2 : ℝ)⁻¹) * (polarDotMatrix : Matrix (Fin 6) (Fin 6) ℝ) 0 5 = 0 at h05
  have hval : (polarDotMatrix : Matrix (Fin 6) (Fin 6) ℝ) 0 5 = 1 := rfl
  rw [hval] at h05
  norm_num at h05

private lemma smul_mat_mulVec {R : Type*} [CommRing R] (c : R)
    (A : Matrix (Fin 6) (Fin 6) R) (v : Fin 6 → R) :
    (c • A) *ᵥ v = c • (A *ᵥ v) := by
  ext i
  change (c • A i) ⬝ᵥ v = c * (A i ⬝ᵥ v)
  exact smul_dotProduct c (A i) v

theorem kleinSymmMatrix_eval_eq (P : KleinQuadric.Plucker6 ℝ) :
    coordinates P ⬝ᵥ (kleinSymmMatrix.1 *ᵥ coordinates P) = P.kleinQ := by
  have hpol : P.polar P = 2 * P.kleinQ := by
    simp [Plucker6.polar, Plucker6.add, Plucker6.kleinQ]; ring
  have hvec := polar_eq_vec_dot_mulVec P P
  rw [hpol] at hvec
  change coordinates P ⬝ᵥ (((2 : ℝ)⁻¹ • polarDotMatrix) *ᵥ coordinates P) = P.kleinQ
  rw [smul_mat_mulVec, dotProduct_smul, ← hvec, smul_eq_mul]
  ring

/-- The quotient space of symmetric `6 × 6` quadratic complex forms modulo the Klein quadric has
vector dimension `20` (yielding `19` inhomogeneous complex constants, `No. 149`, `p. 153`). -/
theorem finrank_quadraticComplexQuotient :
    Module.finrank ℝ (symmMat6Submodule ℝ ⧸ Submodule.span ℝ {kleinSymmMatrix}) = 20 := by
  have hadd := Submodule.finrank_quotient_add_finrank (Submodule.span ℝ {kleinSymmMatrix})
  have hspan : Module.finrank ℝ (Submodule.span ℝ {kleinSymmMatrix}) = 1 :=
    finrank_span_singleton kleinSymmMatrix_ne_zero
  have htot := finrank_symmMat6 ℝ
  omega

/-- Evaluation of a symmetric `6 × 6` quadratic complex matrix on a Plücker 6-vector. -/
def quadraticComplexEval {R : Type*} [CommRing R]
    (S : Matrix (Fin 6) (Fin 6) R) (P : KleinQuadric.Plucker6 R) : R :=
  coordinates P ⬝ᵥ (S *ᵥ coordinates P)

/-- Two quadratic complex matrices differing by a multiple of the Klein quadratic form determine the
exact same complex equation on all real rays (`P.IsKlein`) (`No. 150`). -/
theorem quadraticComplexEval_add_klein_eq (S : Matrix (Fin 6) (Fin 6) ℝ) (c : ℝ)
    (P : KleinQuadric.Plucker6 ℝ) (hP : P.IsKlein) :
    quadraticComplexEval (S + c • kleinSymmMatrix.1) P = quadraticComplexEval S P := by
  simp only [quadraticComplexEval, Matrix.add_mulVec, dotProduct_add,
    smul_mat_mulVec, dotProduct_smul, kleinSymmMatrix_eval_eq]
  rw [Plucker6.IsKlein] at hP
  rw [hP, smul_zero, add_zero]

theorem cone_quadratic_invariant_under_klein (S : Matrix (Fin 6) (Fin 6) ℝ) (c : ℝ)
    (x y : Fin 4 → ℝ) :
    quadraticComplexEval (S + c • kleinSymmMatrix.1) (rayPlucker x y) =
      quadraticComplexEval S (rayPlucker x y) :=
  quadraticComplexEval_add_klein_eq S c (rayPlucker x y) (rayPlucker_kleinQ x y)

theorem conic_quadratic_invariant_under_klein (S : Matrix (Fin 6) (Fin 6) ℝ) (c : ℝ)
    (u v : Fin 4 → ℝ) :
    quadraticComplexEval (S + c • kleinSymmMatrix.1) (axisAsRayPlucker u v) =
      quadraticComplexEval S (axisAsRayPlucker u v) :=
  quadraticComplexEval_add_klein_eq S c (axisAsRayPlucker u v) (axisAsRayPlucker_kleinQ u v)

end SpaceOfQuadraticComplexes

section TernarySplittingAndComplexSurfaces

/-- Symmetric `3 × 3` ternary conic matrix `symm3 a b c f g h = [[a, h, g], [h, b, f], [g, f, c]]`. -/
def symm3 {R : Type*} (a b c f g h : R) : Matrix (Fin 3) (Fin 3) R :=
  ![ ![a, h, g],
     ![h, b, f],
     ![g, f, c] ]

/-- Double-line cofactor factorization (`Plücker Abth. I §6, Eqs. (6.37)–(6.39)`, `pp. 207–212`):
when all `2 × 2` minors vanish (`a*b = h²`, `a*c = g²`, `a*f = g*h`), scaling by `a` factors the
ternary conic into an exact square `(a x + h y + g z)²`. -/
theorem ternary_double_line_factorization {R : Type*} [CommRing R]
    (a b c f g h x y z : R)
    (hab : a * b = h ^ 2) (hac : a * c = g ^ 2) (haf : a * f = g * h) :
    a * (![x, y, z] ⬝ᵥ (symm3 a b c f g h *ᵥ ![x, y, z])) =
      (a * x + h * y + g * z) ^ 2 := by
  have hQ : ![x, y, z] ⬝ᵥ (symm3 a b c f g h *ᵥ ![x, y, z]) =
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + 2 * h * x * y + 2 * g * x * z + 2 * f * y * z := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, symm3]
    change x * (a * x + h * y + g * z) + y * (h * x + b * y + f * z) +
      z * (g * x + f * y + c * z) = _
    ring
  rw [hQ]
  linear_combination y ^ 2 * hab + z ^ 2 * hac + 2 * y * z * haf

/-- Rank-2 ternary conic splitting identity (`§6`, `pp. 207–212`):
`(a*b - h²) * a * Q(x,y,z) = (a*b - h²)*(a x + h y + g z)² + ((a*b - h²) y + (a*f - g*h) z)² + a * det M * z²`.
Hence whenever `det (symm3 a b c f g h) = 0` and `a*b - h² = -u²`, the ternary conic factors as
a product of two linear forms! -/
theorem ternary_rank2_schur_identity {R : Type*} [CommRing R]
    (a b c f g h x y z : R) :
    let M := symm3 a b c f g h
    (a * b - h ^ 2) * a * (![x, y, z] ⬝ᵥ (M *ᵥ ![x, y, z])) =
      (a * b - h ^ 2) * (a * x + h * y + g * z) ^ 2 +
        ((a * b - h ^ 2) * y + (a * f - g * h) * z) ^ 2 +
        a * M.det * z ^ 2 := by
  intro M
  have hQ : ![x, y, z] ⬝ᵥ (M *ᵥ ![x, y, z]) =
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + 2 * h * x * y + 2 * g * x * z + 2 * f * y * z := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, M, symm3]
    change x * (a * x + h * y + g * z) + y * (h * x + b * y + f * z) +
      z * (g * x + f * y + c * z) = _
    ring
  have hdet : M.det = a * (b * c - f * f) - h * (h * c - g * f) + g * (h * f - g * b) := by
    rw [Matrix.det_fin_three]
    dsimp only [M, symm3]
    change a * b * c - a * f * f - h * h * c + h * f * g + g * h * f - g * b * g = _
    ring
  rw [hQ, hdet]
  ring

theorem ternary_conic_splits_two_lines {R : Type*} [CommRing R]
    (a b c f g h u x y z : R)
    (hdet : (symm3 a b c f g h).det = 0)
    (hneg : a * b - h ^ 2 = -(u ^ 2)) :
    (a * b - h ^ 2) * a * (![x, y, z] ⬝ᵥ (symm3 a b c f g h *ᵥ ![x, y, z])) =
      (((a * b - h ^ 2) * y + (a * f - g * h) * z) - u * (a * x + h * y + g * z)) *
      (((a * b - h ^ 2) * y + (a * f - g * h) * z) + u * (a * x + h * y + g * z)) := by
  have hsch := ternary_rank2_schur_identity a b c f g h x y z
  dsimp only at hsch
  rw [hdet, mul_zero, zero_mul, add_zero, hneg] at hsch
  rw [hneg] at *
  rw [hsch]
  ring

/-- Order and class of Plücker's complex surface for a degree-`n` complex (`§7, Nos. 225–233`,
`pp. 212–218`). -/
def complexSurfaceOrder (n : ℕ) : ℕ := 2 * n * (n - 1)

/-- Multiplicity of a meridian/equatorial double line on a degree-`n` complex surface. -/
def complexSurfaceDoubleLineMultiplicity (n : ℕ) : ℕ := n * (n - 1)

theorem complexSurfaceOrder_eq_two_mul_doubleLine (n : ℕ) :
    complexSurfaceOrder n = 2 * complexSurfaceDoubleLineMultiplicity n := by
  dsimp [complexSurfaceOrder, complexSurfaceDoubleLineMultiplicity]
  ring

theorem complexSurface_quadratic_degrees :
    complexSurfaceOrder 2 = 4 ∧ complexSurfaceDoubleLineMultiplicity 2 = 2 := by
  decide

/-- Meridian quartic surface equation around its double line (`y = 0, z = 0`): every term carries
degree `≥ 2` in `(y, z)`, so the line `y = z = 0` vanishes identically to multiplicity `≥ 2`
even when `(x, w)` varies arbitrarily (`Nos. 220–228`). -/
def meridianQuartic {R : Type*} [Ring R]
    (p20 p11 p02 q20 q11 q02 r20 r11 r02 : Fin 4 → R) : (Fin 4 → R) → R :=
  fun pt =>
    let x := pt 0; let y := pt 1; let z := pt 2; let w := pt 3
    let qA := p20 0 * x ^ 2 + p11 0 * x * w + p02 0 * w ^ 2
    let qB := q20 0 * x ^ 2 + q11 0 * x * w + q02 0 * w ^ 2
    let qC := r20 0 * x ^ 2 + r11 0 * x * w + r02 0 * w ^ 2
    qA * y ^ 2 + 2 * qB * y * z + qC * z ^ 2

theorem meridianQuartic_vanishes_on_double_line {R : Type*} [CommRing R]
    (p20 p11 p02 q20 q11 q02 r20 r11 r02 : Fin 4 → R) (x w t : R) :
    meridianQuartic p20 p11 p02 q20 q11 q02 r20 r11 r02 ![x, t, t * 0, w] =
      t ^ 2 * (p20 0 * x ^ 2 + p11 0 * x * w + p02 0 * w ^ 2) := by
  dsimp only [meridianQuartic]
  have hx0 : ![x, t, t * 0, w] 0 = x := rfl
  have hx1 : ![x, t, t * 0, w] 1 = t := rfl
  have hx2 : ![x, t, t * 0, w] 2 = t * 0 := rfl
  have hx3 : ![x, t, t * 0, w] 3 = w := rfl
  rw [hx0, hx1, hx2, hx3]
  ring

end TernarySplittingAndComplexSurfaces

section CentralParallelepipedAndTangentComplex

/-- Opposite vertex `G = (R/F, T/D, P/E)` of Plücker's Central Parallelepiped for a quadratic
complex (`Abth. II §1, Eq. (1.19)`, `p. 229`). -/
noncomputable def parallelepipedVertexG (D E F R T P : ℝ) : Vec3 :=
  ![R / F, T / D, P / E]

/-- Opposite vertex `H = (-U/E, -Q/F, -S/D)` of the Central Parallelepiped (`Eq. (1.20)`, `p. 229`). -/
noncomputable def parallelepipedVertexH (D E F Q S U : ℝ) : Vec3 :=
  ![-U / E, -Q / F, -S / D]

/-- True Euclidean center of the Central Parallelepiped, equal to `(G + H) / 2`. -/
noncomputable def centralParallelepipedCenter (D E F Q R S T U P : ℝ) : Vec3 :=
  ((2 : ℝ)⁻¹) • (parallelepipedVertexG D E F R T P + parallelepipedVertexH D E F Q S U)

theorem centralParallelepipedCenter_eq (D E F Q R S T U P : ℝ)
    (hD : D ≠ 0) (hE : E ≠ 0) (hF : F ≠ 0) :
    centralParallelepipedCenter D E F Q R S T U P =
      ![(E * R - F * U) / (2 * E * F),
        (F * T - D * Q) / (2 * D * F),
        (D * P - E * S) / (2 * D * E)] := by
  ext i
  fin_cases i <;>
    simp only [centralParallelepipedCenter, parallelepipedVertexG, parallelepipedVertexH,
      Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  · change 2⁻¹ * (R / F + -U / E) = (E * R - F * U) / (2 * E * F)
    field_simp [hE, hF]; ring
  · change 2⁻¹ * (T / D + -Q / F) = (F * T - D * Q) / (2 * D * F)
    field_simp [hD, hF]; ring
  · change 2⁻¹ * (P / E + -S / D) = (D * P - E * S) / (2 * D * E)
    field_simp [hD, hE]; ring

/-- Plücker's printed `Eq. (1.21)` (`Liniengeometriev1.pdf`, `p. 230`), which omits the factor `2`
in all three denominators. -/
noncomputable def printedEq121 (D E F Q R S T U P : ℝ) : Vec3 :=
  ![(E * R - F * U) / (E * F),
    -(D * Q - F * T) / (D * F),
    (D * P - E * S) / (D * E)]

/-- `[countermodel_found]` **Historical erratum in Plücker `Eq. (1.21)` (`p. 230`)**:
The printed formula equals twice the true Central Parallelepiped center `(G + H)/2`, giving a
concrete non-matching value `![2, 0, 0] ≠ ![1, 0, 0]` at `D=E=F=1, R=2, Q=S=T=U=P=0`. -/
theorem eq121_printed_omits_factor_two (D E F Q R S T U P : ℝ)
    (hD : D ≠ 0) (hE : E ≠ 0) (hF : F ≠ 0) :
    printedEq121 D E F Q R S T U P =
      (2 : ℝ) • centralParallelepipedCenter D E F Q R S T U P := by
  rw [centralParallelepipedCenter_eq D E F Q R S T U P hD hE hF]
  ext i
  fin_cases i <;> simp only [printedEq121, Pi.smul_apply, smul_eq_mul]
  · change (E * R - F * U) / (E * F) = 2 * ((E * R - F * U) / (2 * E * F))
    field_simp [hE, hF]
  · change -(D * Q - F * T) / (D * F) = 2 * ((F * T - D * Q) / (2 * D * F))
    field_simp [hD, hF]; ring
  · change (D * P - E * S) / (D * E) = 2 * ((D * P - E * S) / (2 * D * E))
    field_simp [hD, hE]

theorem eq121_countermodel_witness :
    printedEq121 1 1 1 0 2 0 0 0 0 ≠ centralParallelepipedCenter 1 1 1 0 2 0 0 0 0 := by
  intro h
  have h0 := congrFun h 0
  have hp0 : printedEq121 1 1 1 0 2 0 0 0 0 0 = 2 := by
    simp [printedEq121]
  have hc0 : centralParallelepipedCenter 1 1 1 0 2 0 0 0 0 0 = 1 := by
    simp [centralParallelepipedCenter, parallelepipedVertexG, parallelepipedVertexH]
  rw [hp0, hc0] at h0
  norm_num at h0

private lemma quadric_tangent_secondCompound_scalar {R : Type*} [CommRing R]
    (g00 g01 g02 g03 g10 g11 g12 g13 g20 g21 g22 g23 g30 g31 g32 g33
     x0 x1 x2 x3 y0 y1 y2 y3 : R) :
    let p01 := x0 * y1 - x1 * y0
    let p02 := x0 * y2 - x2 * y0
    let p03 := x0 * y3 - x3 * y0
    let p12 := x1 * y2 - x2 * y1
    let p13 := x1 * y3 - x3 * y1
    let p23 := x2 * y3 - x3 * y2
    p01 * ((g00 * g11 - g01 * g10) * p01 + (g00 * g12 - g02 * g10) * p02 +
           (g00 * g13 - g03 * g10) * p03 + (g01 * g12 - g02 * g11) * p12 +
           (g01 * g13 - g03 * g11) * p13 + (g02 * g13 - g03 * g12) * p23) +
    p02 * ((g00 * g21 - g01 * g20) * p01 + (g00 * g22 - g02 * g20) * p02 +
           (g00 * g23 - g03 * g20) * p03 + (g01 * g22 - g02 * g21) * p12 +
           (g01 * g23 - g03 * g21) * p13 + (g02 * g23 - g03 * g22) * p23) +
    p03 * ((g00 * g31 - g01 * g30) * p01 + (g00 * g32 - g02 * g30) * p02 +
           (g00 * g33 - g03 * g30) * p03 + (g01 * g32 - g02 * g31) * p12 +
           (g01 * g33 - g03 * g31) * p13 + (g02 * g33 - g03 * g32) * p23) +
    p12 * ((g10 * g21 - g11 * g20) * p01 + (g10 * g22 - g12 * g20) * p02 +
           (g10 * g23 - g13 * g20) * p03 + (g11 * g22 - g12 * g21) * p12 +
           (g11 * g23 - g13 * g21) * p13 + (g12 * g23 - g13 * g22) * p23) +
    p13 * ((g10 * g31 - g11 * g30) * p01 + (g10 * g32 - g12 * g30) * p02 +
           (g10 * g33 - g13 * g30) * p03 + (g11 * g32 - g12 * g31) * p12 +
           (g11 * g33 - g13 * g31) * p13 + (g12 * g33 - g13 * g32) * p23) +
    p23 * ((g20 * g31 - g21 * g30) * p01 + (g20 * g32 - g22 * g30) * p02 +
           (g20 * g33 - g23 * g30) * p03 + (g21 * g32 - g22 * g31) * p12 +
           (g21 * g33 - g23 * g31) * p13 + (g22 * g33 - g23 * g32) * p23) =
      (x0 * (g00 * x0 + g01 * x1 + g02 * x2 + g03 * x3) +
       x1 * (g10 * x0 + g11 * x1 + g12 * x2 + g13 * x3) +
       x2 * (g20 * x0 + g21 * x1 + g22 * x2 + g23 * x3) +
       x3 * (g30 * x0 + g31 * x1 + g32 * x2 + g33 * x3)) *
      (y0 * (g00 * y0 + g01 * y1 + g02 * y2 + g03 * y3) +
       y1 * (g10 * y0 + g11 * y1 + g12 * y2 + g13 * y3) +
       y2 * (g20 * y0 + g21 * y1 + g22 * y2 + g23 * y3) +
       y3 * (g30 * y0 + g31 * y1 + g32 * y2 + g33 * y3)) -
      (x0 * (g00 * y0 + g01 * y1 + g02 * y2 + g03 * y3) +
       x1 * (g10 * y0 + g11 * y1 + g12 * y2 + g13 * y3) +
       x2 * (g20 * y0 + g21 * y1 + g22 * y2 + g23 * y3) +
       x3 * (g30 * y0 + g31 * y1 + g32 * y2 + g33 * y3)) *
      (y0 * (g00 * x0 + g01 * x1 + g02 * x2 + g03 * x3) +
       y1 * (g10 * x0 + g11 * x1 + g12 * x2 + g13 * x3) +
       y2 * (g20 * x0 + g21 * x1 + g22 * x2 + g23 * x3) +
       y3 * (g30 * x0 + g31 * x1 + g32 * x2 + g33 * x3)) := by
  ring

/-- Tangential quadratic complex of a point quadric (`Plücker Abth. II §2, Nos. 251–274`,
`pp. 239–250`): for any `4 × 4` matrix `G`, `(rayPlucker x y)ᵀ (C₂ G) (rayPlucker x y) =
(xᵀ G x)(yᵀ G y) - (xᵀ G y)(yᵀ G x)`. -/
theorem quadric_tangent_secondCompound_identity {R : Type*} [CommRing R]
    (G : Matrix (Fin 4) (Fin 4) R) (x y : Fin 4 → R) :
    coordinates (rayPlucker x y) ⬝ᵥ (secondCompound G *ᵥ coordinates (rayPlucker x y)) =
      (x ⬝ᵥ (G *ᵥ x)) * (y ⬝ᵥ (G *ᵥ y)) - (x ⬝ᵥ (G *ᵥ y)) * (y ⬝ᵥ (G *ᵥ x)) := by
  have hs := quadric_tangent_secondCompound_scalar
    (G 0 0) (G 0 1) (G 0 2) (G 0 3) (G 1 0) (G 1 1) (G 1 2) (G 1 3)
    (G 2 0) (G 2 1) (G 2 2) (G 2 3) (G 3 0) (G 3 1) (G 3 2) (G 3 3)
    (x 0) (x 1) (x 2) (x 3) (y 0) (y 1) (y 2) (y 3)
  simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_six, Fin.sum_univ_four,
    coordinates, rayPlucker, secondCompound, coordinatePair] using hs

theorem quadric_tangent_secondCompound_symm {R : Type*} [CommRing R]
    (G : Matrix (Fin 4) (Fin 4) R) (hG : G.IsSymm) (x y : Fin 4 → R) :
    coordinates (rayPlucker x y) ⬝ᵥ (secondCompound G *ᵥ coordinates (rayPlucker x y)) =
      (x ⬝ᵥ (G *ᵥ x)) * (y ⬝ᵥ (G *ᵥ y)) - (x ⬝ᵥ (G *ᵥ y)) ^ 2 := by
  rw [quadric_tangent_secondCompound_identity, sq]
  have hxy : y ⬝ᵥ (G *ᵥ x) = x ⬝ᵥ (G *ᵥ y) := by
    calc
      y ⬝ᵥ (G *ᵥ x) = (y ᵥ* G) ⬝ᵥ x := Matrix.dotProduct_mulVec y G x
      _ = (y ᵥ* Gᵀ) ⬝ᵥ x := by rw [hG]
      _ = (G *ᵥ y) ⬝ᵥ x := by rw [Matrix.vecMul_transpose]
      _ = x ⬝ᵥ (G *ᵥ y) := dotProduct_comm _ _
  rw [hxy]

/-- Non-commutativity witness for the `4 × 4` homogeneous point carrier `Matrix (Fin 4) (Fin 4) R`. -/
theorem matrix4_noncomm {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 4) (Fin 4) R, A * B ≠ B * A := by
  refine ⟨Matrix.of (fun i j => if i = 0 ∧ j = 1 then 1 else 0),
          Matrix.of (fun i j => if i = 1 ∧ j = 0 then 1 else 0), ?_⟩
  intro h
  have h00 := congrArg (fun M => M 0 0) h
  simp [Matrix.mul_apply] at h00

end CentralParallelepipedAndTangentComplex

end InfoGeometry.Projective.PluckerQuadraticComplexAndSurfaces
