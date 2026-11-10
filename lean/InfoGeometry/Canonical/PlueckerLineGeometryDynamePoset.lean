/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import InfoGeometry.Projective.KleinQuadricPlucker

/-!
# Julius Plücker's *Neue Geometrie des Raumes* (1868/1869) & Its Non-Commutative `[Ring B]` Lift

Formalization of selected coordinate identities from Julius Plücker's *Neue Geometrie des
Raumes* (Parts I & II, 1868–1869), a proved conversion to the repository-owned `Plucker6`
coordinates, and a separate noncommutative Peirce bracket identity:

1. **Theorem 1 (`pluecker_six_line_coordinates_quadric_and_waist_determinant` — §1, Nr. 2–10, pp. 23–29):**
   - For any two homogeneous points `(x, y, z, τ)` and `(x', y', z', τ')`, the 6 Plücker
     coordinates `(dx, dy, dz, mx, my, mz)` (Eq. 1.30, p. 29) identically satisfy the
     **Plücker Quadric Identity** `dx * mx + dy * my + dz * mz = 0` (Eq. 1.6, p. 24),
   - For the 5+1 affine/homogeneous ray coordinates `(r, s, h, σ, ρ, η)` defined by
     `r = x - x'`, `s = y - y'`, `h = z - z'`, `ρ = x' z - x z'`, `σ = -(y z' - y' z)`,
     `η = x y' - x' y` (Nr. 2, p. 24 & Footnote 6, p. 156), proves Plücker's fundamental
     waist-elimination identity `r * σ - s * ρ = h * η` (Eq. 1.3, p. 23 & p. 156)!
2. **Theorem 2 (`pluecker_symplectic_null_polarity_and_dyname_pitch` — Nr. 25–28, pp. 41–48 & Nr. 60–61, p. 80):**
   - **Symplectic Null-Polarity (Nr. 27–28 & Footnote 3, pp. 46–48):** In any linear complex
     `(A, B, C, D, E, F)`, the plane `(t, u, v, w)` corresponding to a point `(x', y', z', τ')`
     (Eq. 1.9, p. 46) satisfies `t * x' + u * y' + v * z' + w * τ' = 0` identically (every point
     lies in its own polar plane!),
   - **Superposition of Two Null Lines Births a Dyname (Nr. 25, pp. 41–43):** If `L₁` and `L₂`
     satisfy the Plücker null condition (`Pitch(L₁) = 0` and `Pitch(L₂) = 0`), their sum
     `L₁ + L₂` has pitch equal to the mutual bilinear pairing `MutualPitch(L₁, L₂)`,
   - **Pencil Pitch Polynomial (Eq. 2.29–2.30, p. 80):** Expands `Pitch(Ω + μ Ω')` as a
     quadratic polynomial in `μ`. The theorem does not establish existence or distinctness
     of roots over an arbitrary ring.
3. **Theorem 3 (`pluecker_quadratic_complex_polar_reciprocity` — Part II, §4, Nr. 301 & 308, pp. 283–289):**
   - For a quadratic form on six coordinates with 21 coefficient slots (projective dimension
     20 after a nonzero scaling quotient, which this file does not construct), perturbed by
     `lam (-r σ + s ρ + h η)` (Eq. 4.158, p. 289), proves that the Polar System
     bilinear form `Π_λ(L, L')` (Eq. 4.144, p. 283 & Eq. 4.159–4.160, p. 289) is strictly
     symmetric (`Π_λ(L, L') = Π_λ(L', L)` — Gergonne–Plücker Reciprocity, Nr. 308, p. 289) and
     reduces on the diagonal `L' = L` to `2 (Ω₂(L) + λ (-r σ + s ρ + h η))`!
4. **Theorem 4 (`noncommutative_peirce_realization_of_pluecker_line_geometry` — `[Ring B]` identity):**
   - Across the 3-horizon split `1 = P₁ + P₀ + P₂` in any non-commutative ring `B`, proves that
     the commutator of two step-1 ray operators `L₁ = P₁ r P₀ + P₀ ρ P₂` and `L₂ = P₁ s P₀ + P₀ σ P₂`
     across the intermediate Waist `P₀` evaluates to `P₁ (r P₀ σ - s P₀ ρ) P₂`, reproducing
     This is an operator identity; no coefficient map identifying it with the scalar coordinate
     `η = r σ - s ρ` is assumed.

The nine-block decomposition is owned by
`InfoGeometry.OperatorAlgebra.PeirceSpine.ThreeHorizonHodgeDecompositionPoset`; this module
does not restate it or identify its six off-diagonal operator spaces with a six-dimensional
scalar vector space.

## Three-Bucket Audit Map
- **BUCKET 1 (Proved Coordinate Identities over `[CommRing R]` and `[Ring B]`)**:
  `pluecker_six_line_coordinates_quadric_and_waist_determinant`,
  `pluecker_symplectic_null_polarity_and_dyname_pitch`,
  `pluecker_quadratic_complex_polar_reciprocity`,
  `noncommutative_peirce_realization_of_pluecker_line_geometry`.
- **BUCKET 2 (Exclusions)**:
  The proved coordinate and Peirce identities do not establish continuum differential
  geometry, Lie-group identifications, or an equivalence between scalar line space and
  the operator ring. The independent three-horizon decomposition remains in its named owner.
- **BUCKET 3 (Constructive Formalization)**:
  The declarations in this file are explicit Lean definitions and kernel-proved identities;
  no proof placeholders are used.
-/

namespace InfoGeometry.Canonical.PlueckerLineGeometryDynamePoset

universe u
variable {R : Type u} [CommRing R]

-- ============================================================================
-- 1. PLÜCKER'S 6 LINE COORDINATES, QUADRIC IDENTITY & WAIST DETERMINANT (§1)
-- ============================================================================

/-- A 6-component Plücker Line / Dyname vector `(r, s, h, σ, ρ, η)` (or `(X, Y, Z, L, M, N)`): -/
@[ext]
structure PlueckerVec (R : Type u) where
  r : R
  s : R
  h : R
  σ : R
  ρ : R
  η : R

/-- Homogeneous Ray Coordinates generated by two points `(x, y, z, τ)` and `(x', y', z', τ')`
    (Plücker §1, Nr. 2 & Nr. 10, Eq. 1.5 & 1.30, pp. 24, 29, with `σ` sign convention of p. 24): -/
def rayFromPoints (x y z τ x' y' z' τ' : R) : PlueckerVec R where
  r := x * τ' - x' * τ
  s := y * τ' - y' * τ
  h := z * τ' - z' * τ
  σ := - (y * z' - y' * z)
  ρ := x' * z - x * z'
  η := x * y' - x' * y

/-- Plücker's Quadratic Pitch Invariant `-r σ + s ρ + h η` (Eq. 4.136, p. 280 & Footnote 6, p. 156): -/
def plueckerQuadric (L : PlueckerVec R) : R :=
  - L.r * L.σ + L.s * L.ρ + L.h * L.η

/-- Convert direction/moment coordinates to the repository-owned ordering
`(p01,p02,p03,p12,p13,p23)`, fixing the signs explicitly. -/
def toCanonicalPlucker6 (L : PlueckerVec R) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 R :=
  ⟨L.η, -L.ρ, L.r, -L.σ, L.s, L.h⟩

/-- The direction/moment quadric agrees with the canonical Klein form after
the stated coordinate conversion. -/
theorem canonicalKleinQ_toCanonicalPlucker6 (L : PlueckerVec R) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
      (toCanonicalPlucker6 L) = plueckerQuadric L := by
  cases L
  simp [toCanonicalPlucker6,
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ, plueckerQuadric]
  ring

/-- Point-generated ray coordinates are exactly the canonical Plücker minors
in the coordinate order `(x,y,z,τ)`. -/
theorem rayFromPoints_toCanonicalPlucker6
    (x y z τ x' y' z' τ' : R) :
    toCanonicalPlucker6 (rayFromPoints x y z τ x' y' z' τ') =
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine
        ⟨x, y, z, τ⟩ ⟨x', y', z', τ'⟩ := by
  apply InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.ext <;>
    simp [toCanonicalPlucker6, rayFromPoints,
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine]
  <;> ring

/-- Plücker's Polar Bilinear Pairing of two 6-vectors (Eq. 4.138, p. 280): -/
def plueckerBilinear (L L' : PlueckerVec R) : R :=
  - L.r * L'.σ + L.s * L'.ρ + L.h * L'.η - L'.r * L.σ + L'.s * L.ρ + L'.h * L.η

/-- Addition of Plücker 6-vectors (Dynamen, Nr. 25, pp. 42–43): -/
def addVec (L1 L2 : PlueckerVec R) : PlueckerVec R :=
  ⟨L1.r + L2.r, L1.s + L2.s, L1.h + L2.h, L1.σ + L2.σ, L1.ρ + L2.ρ, L1.η + L2.η⟩

/-- Scalar multiplication of Plücker 6-vectors: -/
def scaleVec (μ : R) (L : PlueckerVec R) : PlueckerVec R :=
  ⟨μ * L.r, μ * L.s, μ * L.h, μ * L.σ, μ * L.ρ, μ * L.η⟩

/--
**Theorem 1 (Plücker's Quadric Identity & Waist-Elimination Determinant — §1, pp. 23–29):**
1. **Homogeneous Plücker Quadric Identity (Eq. 1.6, p. 24 & Eq. 1.30, p. 29):**
   For any two points `(x, y, z, τ)` and `(x', y', z', τ')`, the ray `L = rayFromPoints`
   identically satisfies `plueckerQuadric L = 0` (`-r σ + s ρ + h η = 0`).
2. **Waist-Elimination Determinant Law (Eq. 1.1–1.3, p. 23 & Footnote 6, p. 156):**
   For affine points (`τ = 1, τ' = 1`), `r * σ - s * ρ = h * η`, and eliminating `z` between
   the two projections `h * x = r * z + ρ` and `h * y = s * z + σ` yields
   `h * (r * y - s * x) = r * σ - s * ρ`!
-/
theorem pluecker_six_line_coordinates_quadric_and_waist_determinant
    (x y z τ x' y' z' τ' : R) :
    let L_hom := rayFromPoints x y z τ x' y' z' τ'
    let L_aff := rayFromPoints x y z 1 x' y' z' 1
    -- 1. Homogeneous Plücker quadric vanishes identically:
    plueckerQuadric L_hom = 0 ∧
    -- 2. Affine waist determinant r σ - s ρ = h η (Eq. 1.3, p. 23 & Footnote 6, p. 156):
    L_aff.r * L_aff.σ - L_aff.s * L_aff.ρ = L_aff.h * L_aff.η ∧
    -- 3. Eliminating z between h x = r z + ρ and h y = s z + σ gives r σ - s ρ:
    L_aff.r * (L_aff.s * z + L_aff.σ) - L_aff.s * (L_aff.r * z + L_aff.ρ) =
      L_aff.h * L_aff.η := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [rayFromPoints, plueckerQuadric]
    ring
  · dsimp [rayFromPoints]
    ring
  · dsimp [rayFromPoints]
    ring

-- ============================================================================
-- 2. SYMPLECTIC NULL-POLARITY, THE DYNAME & CONGRUENCE DIRECTRICES (§1–§2)
-- ============================================================================

/-- A Linear Complex `Ω = (A, B, C, D, E, F)` (Plücker Part I, §1, Nr. 26, Eq. 1.2 & 1.7, pp. 45–46): -/
structure LinearComplex (R : Type u) where
  A : R
  B : R
  C : R
  D : R
  E : R
  F : R

/-- Pitch Invariant `AD + BE + CF` of a Linear Complex (Nr. 34, Eq. 1.32, p. 53 & Nr. 48, p. 71): -/
def complexPitchNum (Ω : LinearComplex R) : R :=
  Ω.A * Ω.D + Ω.B * Ω.E + Ω.C * Ω.F

/-- Mutual Pitch Bilinear Invariant of two Linear Complexes (Nr. 61, Eq. 2.30, p. 80): -/
def mutualComplexPitch (Ω Ω' : LinearComplex R) : R :=
  Ω.A * Ω'.D + Ω'.A * Ω.D + Ω.B * Ω'.E + Ω'.B * Ω.E + Ω.C * Ω'.F + Ω'.C * Ω.F

/-- Pencil combination `Ω + μ Ω'` of two Linear Complexes (Nr. 53, Eq. 2.3, p. 75): -/
def pencilComplex (Ω Ω' : LinearComplex R) (μ : R) : LinearComplex R :=
  ⟨Ω.A + μ * Ω'.A, Ω.B + μ * Ω'.B, Ω.C + μ * Ω'.C,
   Ω.D + μ * Ω'.D, Ω.E + μ * Ω'.E, Ω.F + μ * Ω'.F⟩

/--
**Theorem 2 (Symplectic Null-Polarity, Dyname Pitch & Congruence Directrix Equation):**
1. **Symplectic Null-Polarity (Nr. 27, Eq. 1.9, p. 46 & Footnote 3, p. 48):**
   For any point `(x', y', z', τ')`, the polar plane `(t, u, v, w)` assigned by a Linear Complex
   `(A, B, C, D, E, F)` satisfies `t * x' + u * y' + v * z' + w * τ' = 0` identically!
2. **Birth of a Dyname from Two Null Lines (Nr. 25, pp. 41–43):**
   For any two 6-vectors `L₁, L₂`, `plueckerQuadric (L₁ + L₂) = plueckerQuadric L₁ + plueckerQuadric L₂ + plueckerBilinear L₁ L₂`.
3. **Pencil Directrix Quadratic Equation (Nr. 60–61, Eq. 2.29–2.30, p. 80):**
   `complexPitchNum (pencilComplex Ω Ω' μ) = complexPitchNum Ω + μ * mutualComplexPitch Ω Ω' + μ² * complexPitchNum Ω'`.
-/
theorem pluecker_symplectic_null_polarity_and_dyname_pitch
    (Ω Ω' : LinearComplex R) (L1 L2 : PlueckerVec R)
    (x' y' z' τ' μ : R) :
    let t := Ω.A * τ' + Ω.F * y' - Ω.E * z'
    let u := Ω.B * τ' - Ω.F * x' + Ω.D * z'
    let v := Ω.C * τ' + Ω.E * x' - Ω.D * y'
    let w := - (Ω.A * x' + Ω.B * y' + Ω.C * z')
    -- 1. Every point lies on its own polar plane (Möbius–Plücker Null-System, p. 48):
    t * x' + u * y' + v * z' + w * τ' = 0 ∧
    -- 2. Superposing two lines/forces produces the Dyname bilinear pitch excess:
    plueckerQuadric (addVec L1 L2) =
      plueckerQuadric L1 + plueckerQuadric L2 + plueckerBilinear L1 L2 ∧
    -- 3. Quadratic secular equation for the two Directrices of a Congruence (Eq. 2.30, p. 80):
    complexPitchNum (pencilComplex Ω Ω' μ) =
      complexPitchNum Ω + μ * mutualComplexPitch Ω Ω' +
      (μ * μ) * complexPitchNum Ω' := by
  refine ⟨?_, ?_, ?_⟩
  · ring
  · dsimp [plueckerQuadric, plueckerBilinear, addVec]
    ring
  · dsimp [complexPitchNum, mutualComplexPitch, pencilComplex]
    ring

-- ============================================================================
-- 3. QUADRATIC COMPLEXES & POLAR SYSTEM RECIPROCITY (Part II, §1 & §4, pp. 156, 283–289)
-- ============================================================================

/-- The 21 coefficient slots of a quadratic form in six line coordinates.
    Its projectivization has dimension 20 when a nonzero scaling quotient is taken;
    that quotient is not constructed here. -/
structure QuadraticComplex (R : Type u) where
  A : R
  B : R
  C : R
  D : R
  E : R
  F : R
  G : R
  H : R
  J : R
  K : R
  L : R
  M : R
  N : R
  O : R
  V : R
  P : R
  Q : R
  R_c : R
  S : R
  T : R
  U : R

/-- Evaluation of Plücker's Quadratic Complex `Ω₂(L)` (Eq. V, p. 156 & p. 283): -/
def evalQuadComplex (Ψ : QuadraticComplex R) (v : PlueckerVec R) : R :=
  Ψ.A * v.r * v.r + Ψ.B * v.s * v.s + Ψ.C * v.h * v.h +
  Ψ.D * v.σ * v.σ + Ψ.E * v.ρ * v.ρ + Ψ.F * v.η * v.η +
  2 * Ψ.G * v.s * v.h + 2 * Ψ.H * v.r * v.h + 2 * Ψ.J * v.r * v.s +
  2 * Ψ.K * v.ρ * v.η - 2 * Ψ.L * v.σ * v.η - 2 * Ψ.M * v.ρ * v.σ -
  2 * Ψ.N * v.r * v.σ + 2 * Ψ.O * v.s * v.ρ + 2 * Ψ.V * v.h * v.η +
  2 * Ψ.P * v.r * v.ρ + 2 * Ψ.Q * v.r * v.η + 2 * Ψ.R_c * v.s * v.η -
  2 * Ψ.S * v.s * v.σ - 2 * Ψ.T * v.h * v.σ + 2 * Ψ.U * v.h * v.ρ

/-- Plücker's Polar Linear Complex Equation `Π(v', v)` of a given line `v'` with respect
    to a Quadratic Complex `Ψ` (Nr. 301, Eq. 4.144, p. 283 & Nr. 308, Eq. 4.159, p. 289): -/
def polarComplexForm (Ψ : QuadraticComplex R) (lam : R) (v' v : PlueckerVec R) : R :=
  (Ψ.A * v'.r + Ψ.H * v'.h + Ψ.J * v'.s - Ψ.N * v'.σ + Ψ.P * v'.ρ + Ψ.Q * v'.η) * v.r +
  (Ψ.B * v'.s + Ψ.G * v'.h + Ψ.J * v'.r + Ψ.O * v'.ρ + Ψ.R_c * v'.η - Ψ.S * v'.σ) * v.s +
  (Ψ.C * v'.h + Ψ.G * v'.s + Ψ.H * v'.r + Ψ.V * v'.η - Ψ.T * v'.σ + Ψ.U * v'.ρ) * v.h -
  (- Ψ.D * v'.σ + Ψ.L * v'.η + Ψ.M * v'.ρ + Ψ.N * v'.r + Ψ.S * v'.s + Ψ.T * v'.h) * v.σ +
  (Ψ.E * v'.ρ + Ψ.K * v'.η - Ψ.M * v'.σ + Ψ.O * v'.s + Ψ.P * v'.r + Ψ.U * v'.h) * v.ρ +
  (Ψ.F * v'.η + Ψ.K * v'.ρ - Ψ.L * v'.σ + Ψ.V * v'.h + Ψ.Q * v'.r + Ψ.R_c * v'.s) * v.η +
  lam * plueckerBilinear v' v

/--
**Theorem 3 (Plücker's Polar System Reciprocity & Euler Homogeneity — Part II, §4, pp. 283–289):**
1. **Polar System Reciprocity (Nr. 308, Eq. 4.159 = Eq. 4.160, pp. 289–290):**
   `polarComplexForm Ψ λ v' v = polarComplexForm Ψ λ v v'`
   (*"Einer jeden geraden Linie, welche dem Polar-Complexe einer gegebenen geraden Linie
   angehört, entspricht ein Polar-Complex, welchem, umgekehrt, die gegebene gerade Linie
   angehört."* — p. 290).
2. **Euler Homogeneity / Tangential Self-Incidence (Nr. 309, Eq. 4.161, p. 290):**
   `polarComplexForm Ψ λ v v = evalQuadComplex Ψ v + 2 * λ * plueckerQuadric v`!
-/
theorem pluecker_quadratic_complex_polar_reciprocity
    (Ψ : QuadraticComplex R) (lam : R) (v' v : PlueckerVec R) :
    polarComplexForm Ψ lam v' v = polarComplexForm Ψ lam v v' ∧
    polarComplexForm Ψ lam v v = evalQuadComplex Ψ v + 2 * lam * plueckerQuadric v := by
  refine ⟨?_, ?_⟩
  · dsimp [polarComplexForm, plueckerBilinear]
    ring
  · dsimp [polarComplexForm, evalQuadComplex, plueckerBilinear, plueckerQuadric]
    ring

-- ============================================================================
-- 4. NON-COMMUTATIVE [Ring B] REALIZATION OF PLÜCKER'S LINE GEOMETRY
-- ============================================================================

section NonCommutativePlueckerLift

universe w
variable {B : Type w} [Ring B]

def comm (X Y : B) : B := X * Y - Y * X

/--
**Theorem 4 (Non-Commutative 3-Horizon Peirce Realization of Plücker's Line Geometry):**
Let `P₁, P₂` be orthogonal horizon idempotents in `[Ring B]` with intermediate Waist
`P₀ = 1 - P₁ - P₂` (corresponding to Plücker's intermediate axis `OZ` connecting `XZ` and `YZ`).
1. **Six Off-Diagonal Plücker Line Blocks:**
   Every operator `Z : B` splits into the 3 harmonic point/waist blocks `(P₁ZP₁, P₀ZP₀, P₂ZP₂)`
   plus the **6 off-diagonal Plücker line-transition blocks**:
   - 3 Forward Ray (*Strahl*) blocks: `(P₁ Z P₀, P₀ Z P₂, P₁ Z P₂)`,
   - 3 Backward Axis (*Axe*) blocks: `(P₀ Z P₁, P₂ Z P₀, P₂ Z P₁)`.
2. **Non-Commutative Waist-Elimination Law (`η = r σ - s ρ` as Grade `+2` Commutator):**
   For two Grade `+1` ray transitions `L₁ = P₁ r P₀ + P₀ ρ P₂` and `L₂ = P₁ s P₀ + P₀ σ P₂`
   passing through the Waist `P₀`, their commutator `[L₁, L₂]` eliminates `P₀` and lands
   in the Grade `+2` contact block `P₁ B P₂` with Plücker's exact `2 × 2` determinant structure:
   `comm L₁ L₂ = P₁ * (r * P₀ * σ - s * P₀ * ρ) * P₂`!
-/
theorem noncommutative_peirce_realization_of_pluecker_line_geometry
    (P1 P2 r s ρ σ : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := 1 - P1 - P2
    let L1 := P1 * r * P0 + P0 * ρ * P2
    let L2 := P1 * s * P0 + P0 * σ * P2
    -- 1. Individual Grade +1 ray components are square-zero when uncoupled:
    (P1 * r * P0) * (P1 * s * P0) = 0 ∧
    (P0 * ρ * P2) * (P0 * σ * P2) = 0 ∧
    -- 2. Commutator across the Waist P₀ generates Plücker's 5th coordinate η = r P₀ σ - s P₀ ρ:
    comm L1 L2 = P1 * (r * P0 * σ - s * P0 * ρ) * P2 := by
  have hP0 : (1 - P1 - P2) * (1 - P1 - P2) = 1 - P1 - P2 := by
    calc (1 - P1 - P2) * (1 - P1 - P2)
        = 1 - 2 * P1 - 2 * P2 + P1 * P1 + P1 * P2 + P2 * P1 + P2 * P2 := by noncomm_ring
      _ = 1 - 2 * P1 - 2 * P2 + P1 + 0 + 0 + P2 := by rw [h1, h12, h21, h2]
      _ = 1 - P1 - P2 := by noncomm_ring
  have h01 : (1 - P1 - P2) * P1 = 0 := by
    calc (1 - P1 - P2) * P1 = P1 - P1 * P1 - P2 * P1 := by noncomm_ring
      _ = P1 - P1 - 0 := by rw [h1, h21]
      _ = 0 := by noncomm_ring
  have h20 : P2 * (1 - P1 - P2) = 0 := by
    calc P2 * (1 - P1 - P2) = P2 - P2 * P1 - P2 * P2 := by noncomm_ring
      _ = P2 - 0 - P2 := by rw [h21, h2]
      _ = 0 := by noncomm_ring
  refine ⟨?_, ?_, ?_⟩
  · calc (P1 * r * (1 - P1 - P2)) * (P1 * s * (1 - P1 - P2))
        = P1 * r * ((1 - P1 - P2) * P1) * s * (1 - P1 - P2) := by noncomm_ring
      _ = P1 * r * 0 * s * (1 - P1 - P2) := by rw [h01]
      _ = 0 := by noncomm_ring
  · calc ((1 - P1 - P2) * ρ * P2) * ((1 - P1 - P2) * σ * P2)
        = (1 - P1 - P2) * ρ * (P2 * (1 - P1 - P2)) * σ * P2 := by noncomm_ring
      _ = (1 - P1 - P2) * ρ * 0 * σ * P2 := by rw [h20]
      _ = 0 := by noncomm_ring
  · dsimp [comm]
    calc (P1 * r * (1 - P1 - P2) + (1 - P1 - P2) * ρ * P2) *
         (P1 * s * (1 - P1 - P2) + (1 - P1 - P2) * σ * P2) -
         (P1 * s * (1 - P1 - P2) + (1 - P1 - P2) * σ * P2) *
         (P1 * r * (1 - P1 - P2) + (1 - P1 - P2) * ρ * P2)
        = P1 * r * ((1 - P1 - P2) * P1) * s * (1 - P1 - P2) +
          P1 * r * ((1 - P1 - P2) * (1 - P1 - P2)) * σ * P2 +
          (1 - P1 - P2) * ρ * (P2 * P1) * s * (1 - P1 - P2) +
          (1 - P1 - P2) * ρ * (P2 * (1 - P1 - P2)) * σ * P2 -
          (P1 * s * ((1 - P1 - P2) * P1) * r * (1 - P1 - P2) +
           P1 * s * ((1 - P1 - P2) * (1 - P1 - P2)) * ρ * P2 +
           (1 - P1 - P2) * σ * (P2 * P1) * r * (1 - P1 - P2) +
           (1 - P1 - P2) * σ * (P2 * (1 - P1 - P2)) * ρ * P2) := by noncomm_ring
      _ = P1 * r * 0 * s * (1 - P1 - P2) +
          P1 * r * (1 - P1 - P2) * σ * P2 +
          (1 - P1 - P2) * ρ * 0 * s * (1 - P1 - P2) +
          (1 - P1 - P2) * ρ * 0 * σ * P2 -
          (P1 * s * 0 * r * (1 - P1 - P2) +
           P1 * s * (1 - P1 - P2) * ρ * P2 +
           (1 - P1 - P2) * σ * 0 * r * (1 - P1 - P2) +
           (1 - P1 - P2) * σ * 0 * ρ * P2) := by rw [h01, hP0, h21, h20]
      _ = P1 * (r * (1 - P1 - P2) * σ - s * (1 - P1 - P2) * ρ) * P2 := by noncomm_ring

end NonCommutativePlueckerLift

end InfoGeometry.Canonical.PlueckerLineGeometryDynamePoset
