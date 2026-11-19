/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.PluckerKummerQuarticAndMasterAtlas
import InfoGeometry.Projective.PluckerComplexPencil
import InfoGeometry.Projective.GrassmannSubspaceShadowsResultantAndHadamard
import InfoGeometry.Canonical.GrassmannPfaffianSyzygyAndNormalForms
import InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms
import InfoGeometry.Canonical.GrassmannianCartanInteroperability
import InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv
import Mathlib.RingTheory.Grassmannian

/-!
# Triadic Unification: Plücker Line Geometry, Grassmann *Ausdehnungslehre*, & Klein's *Erlangen Program*

This synthesis module constructs explicit, kernel-checked theorem bridges across the three
interconnected nineteenth-century pillars requested in this repository:

1. **Julius Plücker** (*Neue Geometrie des Raumes*, `PL₁`–`PL₉`): ray/axis `Plucker6` coordinates,
   linear complex alternating matrix `complexMatrix C` (`det = kleinQ C ^ 2`), singular/special
   directrices, and `V₄`-symmetric Kummer quartics.
2. **Hermann Grassmann** (*Die Ausdehnungslehre*, 1862, `GA₁`–`GA₃₁`): `ExteriorAlgebra`
   progressive multiplication, basis-free Poincaré/Hodge duality `hodge`, regressive meet,
   exterior resultant (`No. 136`), Lorentzian circle space `circleBilin` of signature `(1, 3)`
   (`Note 97`), and Lie–Darboux–Pfaffian symplectic bounds (`No. 503`).
3. **Felix Klein** (*Erlangen Program*, 1872, `EK₁`–`EK₁₀`): transformation groups, dualistic
   correlations (`kleinHodgeDual`), Hesse transference (`hessePairPoint`), Möbius `(n + 1, 1)`
   lightcone, Lie `(n + 1, 2)` sphere contact geometry (`lieQuadricBilin`, `laguerreShift`),
   `(2n + 1)` Legendrian contact duality (`legendreContact`), and `V₄` tetrahedral/quartic
   covariant syzygies.

## Triadic Bridges Established Here
* **`PGK₁`**: Canonical exterior embedding `pluckerToExterior2 : Plucker6 R → Λ² R⁴` identifying
  `ι u * ι v = pluckerToExterior2 (Vec4.wedge u v)`, 4-fold exterior wedge `P ∧ Q = polar P Q • vol₄`,
  and exact equality between Grassmann's Hodge star `hodge (Pi.basisFun K (Fin 4))` and Klein's
  correlation duality `kleinHodgeDual`.
* **`PGK₂`**: Exact 2-to-1 double-cover equivalence between Grassmann's unoriented circle tangency
  (`IsCircleTangent`, `circleBilin`) and Lie–Klein's oriented `(3, 2)` sphere tangency
  (`lieQuadricBilin 2`, up to orientation reversal `±r₂`), plus the 3-tier `GL(4)` / `O(3,1)` /
  `O(3,2)` separation theorem (`note97_syncyclic_vs_moebius_tangency` + `laguerreShift`).
* **`PGK₃`**: Unification of Grassmann–Darboux Pfaffian top squares (`P ∧ P = 2 * kleinQ P • vol₄`),
  Plücker linear complex determinants (`(complexMatrix C).det = (kleinQ C) ^ 2`), special directrix
  existence (`PL₃`), Grassmann–Lie isotropic bounds (`No. 503`), and Klein's `n`-dimensional
  Legendrian contact transformation (`§9`).
* **`PGK₄` & `EK₁₀`**: Linear-pencil resultant bridge (`Grassmann No. 136` ↔ `hesseDiscForm`),
  Plücker–Klein `V₄` quartic bridge (`canonicalKummerQuartic_group_invariant` ↔ `kleinTetraVertex`),
  10-node non-linear `PartialOrder KleinErlangenArchetype` DAG, and
  `plucker_grassmann_klein_grand_synthesis`.
-/

noncomputable section

open InfoGeometry.Projective.ExteriorRegressive
open InfoGeometry.Projective.ExteriorBladeIncidence
open InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow
open InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
open InfoGeometry.Projective.GrassmannSubspaceShadowsResultantAndHadamard
open InfoGeometry.Canonical.GrassmannPfaffianSyzygyAndNormalForms
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.PluckerLinearComplex
open InfoGeometry.Projective.PluckerComplexPencil
open InfoGeometry.Projective.PluckerKummerQuarticAndMasterAtlas
open InfoGeometry.Projective.KleinErlangenProgramGroupsAndProjectiveTransfer
open InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms
open InfoGeometry.Projective.KleinCrossRatioInvariant
open InfoGeometry.Canonical.GrassmannianCartanInteroperability
open InfoGeometry.Projective.ExteriorKleinFrameSurjection
open InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient
open InfoGeometry.Projective.ExteriorKleinProjective
open InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open scoped Matrix Quaternion LinearAlgebra.Projectivization

namespace InfoGeometry.Canonical.PluckerGrassmannKleinUnifiedSynthesis

/-! ## 0. Non-Commutativity Ground Witness (T16) -/

/-- Closed `2 × 2` integer matrix non-commutativity ground witness. -/
theorem pgkUnified_mat2_not_commute :
    ∃ a b : Matrix (Fin 2) (Fin 2) ℤ, a * b ≠ b * a :=
  kleinErlangenGroups_mat2_not_commute

/-- Closed `ExteriorAlgebra ℝ (Fin 2 → ℝ)` non-commuting 1-vector product witness. -/
theorem pgkUnified_ext1_not_commute :
    ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 2) 0) *
        ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 2) 1) ≠
      ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 2) 1) *
        ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 2) 0) :=
  grassmann_wave4_mod1_noncommutative_witness

/-! ## 1. `PGK₁`: Grassmann `Λ R⁴` ↔ Plücker `Plucker6` ↔ Klein Hodge `O(3,3)` Duality -/

section ExteriorPluckerKleinDuality

section CommRing

variable {R : Type*} [CommRing R]

/-- Standard basis vector `eᵢ ∈ R⁴`. -/
def e4 (i : Fin 4) : Fin 4 → R :=
  Pi.single i (1 : R)

/-- Embed homogeneous `Vec4 R` into `Fin 4 → R`. -/
def vec4ToFin4 (u : Vec4 R) : Fin 4 → R :=
  ![u.x0, u.x1, u.x2, u.x3]

private theorem vec4ToFin4_eq (u : Vec4 R) :
    vec4ToFin4 u = u.x0 • e4 0 + u.x1 • e4 1 + u.x2 • e4 2 + u.x3 • e4 3 := by
  ext i
  fin_cases i <;> simp [vec4ToFin4, e4]

/-- Elementary exterior 2-vector `eᵢ ∧ eⱼ` in `ExteriorAlgebra R (Fin 4 → R)`. -/
def e4Pair (i j : Fin 4) : ExteriorAlgebra R (Fin 4 → R) :=
  ExteriorAlgebra.ι R (e4 i) * ExteriorAlgebra.ι R (e4 j)

/-- Top exterior 4-vector `e₀ ∧ e₁ ∧ e₂ ∧ e₃`. -/
def extVol4 : ExteriorAlgebra R (Fin 4 → R) :=
  ExteriorAlgebra.ι R (e4 0) * ExteriorAlgebra.ι R (e4 1) *
    ExteriorAlgebra.ι R (e4 2) * ExteriorAlgebra.ι R (e4 3)

/-- Explicit linear injection `Plucker6 R → ExteriorAlgebra R (Fin 4 → R)` mapping the 6 Plücker
coordinates `(p01, p02, p03, p12, p13, p23)` to their exterior bivector. -/
def pluckerToExterior2 (P : Plucker6 R) : ExteriorAlgebra R (Fin 4 → R) :=
  P.p01 • e4Pair 0 1 + P.p02 • e4Pair 0 2 + P.p03 • e4Pair 0 3 +
    P.p12 • e4Pair 1 2 + P.p13 • e4Pair 1 3 + P.p23 • e4Pair 2 3

private theorem e4_sq (i : Fin 4) :
    ExteriorAlgebra.ι R (e4 (R := R) i) * ExteriorAlgebra.ι R (e4 (R := R) i) = 0 :=
  ExteriorAlgebra.ι_sq_zero _

private theorem e4_swap (i j : Fin 4) :
    ExteriorAlgebra.ι R (e4 (R := R) j) * ExteriorAlgebra.ι R (e4 (R := R) i) =
      -(ExteriorAlgebra.ι R (e4 (R := R) i) * ExteriorAlgebra.ι R (e4 (R := R) j)) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

private theorem e4_swap_mid (a i j b : Fin 4) :
    ExteriorAlgebra.ι R (e4 (R := R) a) * ExteriorAlgebra.ι R (e4 (R := R) j) *
        ExteriorAlgebra.ι R (e4 (R := R) i) * ExteriorAlgebra.ι R (e4 (R := R) b) =
      -(ExteriorAlgebra.ι R (e4 (R := R) a) * ExteriorAlgebra.ι R (e4 (R := R) i) *
        ExteriorAlgebra.ι R (e4 (R := R) j) * ExteriorAlgebra.ι R (e4 (R := R) b)) := by
  calc
    ExteriorAlgebra.ι R (e4 a) * ExteriorAlgebra.ι R (e4 j) *
        ExteriorAlgebra.ι R (e4 i) * ExteriorAlgebra.ι R (e4 b) =
        ExteriorAlgebra.ι R (e4 a) * (ExteriorAlgebra.ι R (e4 j) * ExteriorAlgebra.ι R (e4 i)) *
          ExteriorAlgebra.ι R (e4 b) := by simp only [mul_assoc]
    _ = ExteriorAlgebra.ι R (e4 a) * (-(ExteriorAlgebra.ι R (e4 i) * ExteriorAlgebra.ι R (e4 j))) *
          ExteriorAlgebra.ι R (e4 b) := by rw [e4_swap i j]
    _ = -(ExteriorAlgebra.ι R (e4 a) * ExteriorAlgebra.ι R (e4 i) *
          ExteriorAlgebra.ι R (e4 j) * ExteriorAlgebra.ι R (e4 b)) := by
      simp only [mul_neg, neg_mul, mul_assoc]

private theorem e4Pair_01_23 :
    e4Pair (R := R) 0 1 * e4Pair 2 3 = extVol4 := by
  simp only [e4Pair, extVol4, mul_assoc]

private theorem e4Pair_02_13 :
    e4Pair (R := R) 0 2 * e4Pair 1 3 = -extVol4 := by
  simp only [e4Pair, extVol4]
  calc
    ExteriorAlgebra.ι R (e4 0) * ExteriorAlgebra.ι R (e4 2) *
        (ExteriorAlgebra.ι R (e4 1) * ExteriorAlgebra.ι R (e4 3)) =
        ExteriorAlgebra.ι R (e4 0) * ExteriorAlgebra.ι R (e4 2) *
          ExteriorAlgebra.ι R (e4 1) * ExteriorAlgebra.ι R (e4 3) := by simp only [mul_assoc]
    _ = -extVol4 := e4_swap_mid 0 1 2 3

private theorem e4Pair_03_12 :
    e4Pair (R := R) 0 3 * e4Pair 1 2 = extVol4 := by
  simp only [e4Pair, extVol4]
  calc
    ExteriorAlgebra.ι R (e4 0) * ExteriorAlgebra.ι R (e4 3) *
        (ExteriorAlgebra.ι R (e4 1) * ExteriorAlgebra.ι R (e4 2)) =
        ExteriorAlgebra.ι R (e4 0) * (ExteriorAlgebra.ι R (e4 3) * ExteriorAlgebra.ι R (e4 1)) *
          ExteriorAlgebra.ι R (e4 2) := by simp only [mul_assoc]
    _ = -(ExteriorAlgebra.ι R (e4 0) * ExteriorAlgebra.ι R (e4 1) *
          ExteriorAlgebra.ι R (e4 3) * ExteriorAlgebra.ι R (e4 2)) := by
      rw [e4_swap 1 3]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = -(-(ExteriorAlgebra.ι R (e4 0) * ExteriorAlgebra.ι R (e4 1) *
          ExteriorAlgebra.ι R (e4 2) * ExteriorAlgebra.ι R (e4 3))) := by
      congr 1
      calc
        ExteriorAlgebra.ι R (e4 0) * ExteriorAlgebra.ι R (e4 1) *
            ExteriorAlgebra.ι R (e4 3) * ExteriorAlgebra.ι R (e4 2) =
            (ExteriorAlgebra.ι R (e4 0) * ExteriorAlgebra.ι R (e4 1)) *
              (ExteriorAlgebra.ι R (e4 3) * ExteriorAlgebra.ι R (e4 2)) := by simp only [mul_assoc]
        _ = (ExteriorAlgebra.ι R (e4 0) * ExteriorAlgebra.ι R (e4 1)) *
              (-(ExteriorAlgebra.ι R (e4 2) * ExteriorAlgebra.ι R (e4 3))) := by rw [e4_swap 2 3]
        _ = -(ExteriorAlgebra.ι R (e4 0) * ExteriorAlgebra.ι R (e4 1) *
              ExteriorAlgebra.ι R (e4 2) * ExteriorAlgebra.ι R (e4 3)) := by
          simp only [mul_neg, mul_assoc]
    _ = extVol4 := neg_neg _

private theorem e4Pair_23_01 :
    e4Pair (R := R) 2 3 * e4Pair 0 1 = extVol4 := by
  have hc : e4Pair (R := R) 2 3 ∈ ⋀[R]^2 (Fin 4 → R) := by
    have h23 : e4Pair (R := R) 2 3 = ExteriorAlgebra.ιMulti R 2 ![e4 2, e4 3] := by
      rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
        ExteriorAlgebra.ιMulti_zero_apply, mul_one]
      rfl
    rw [h23]
    exact ExteriorAlgebra.ιMulti_range R 2 ⟨![e4 2, e4 3], rfl⟩
  rw [exteriorPower_two_mul_comm hc (e4Pair 0 1), e4Pair_01_23]

private theorem e4Pair_13_02 :
    e4Pair (R := R) 1 3 * e4Pair 0 2 = -extVol4 := by
  have hc : e4Pair (R := R) 1 3 ∈ ⋀[R]^2 (Fin 4 → R) := by
    have h13 : e4Pair (R := R) 1 3 = ExteriorAlgebra.ιMulti R 2 ![e4 1, e4 3] := by
      rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
        ExteriorAlgebra.ιMulti_zero_apply, mul_one]
      rfl
    rw [h13]
    exact ExteriorAlgebra.ιMulti_range R 2 ⟨![e4 1, e4 3], rfl⟩
  rw [exteriorPower_two_mul_comm hc (e4Pair 0 2), e4Pair_02_13]

private theorem e4Pair_12_03 :
    e4Pair (R := R) 1 2 * e4Pair 0 3 = extVol4 := by
  have hc : e4Pair (R := R) 1 2 ∈ ⋀[R]^2 (Fin 4 → R) := by
    have h12 : e4Pair (R := R) 1 2 = ExteriorAlgebra.ιMulti R 2 ![e4 1, e4 2] := by
      rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
        ExteriorAlgebra.ιMulti_zero_apply, mul_one]
      rfl
    rw [h12]
    exact ExteriorAlgebra.ιMulti_range R 2 ⟨![e4 1, e4 2], rfl⟩
  rw [exteriorPower_two_mul_comm hc (e4Pair 0 3), e4Pair_03_12]

private theorem e4_mul_zero_of_eq_left {a b c : Fin 4} (h : a = b ∨ a = c) :
    ExteriorAlgebra.ι R (e4 (R := R) a) *
        (ExteriorAlgebra.ι R (e4 (R := R) b) * ExteriorAlgebra.ι R (e4 (R := R) c)) = 0 := by
  rcases h with rfl | rfl
  · rw [← mul_assoc, e4_sq, zero_mul]
  · rw [e4_swap a b, mul_neg, ← mul_assoc, e4_sq, zero_mul, neg_zero]

private theorem e4_mul_pair_zero {a b c d : Fin 4}
    (h : a = c ∨ a = d ∨ b = c ∨ b = d) :
    e4Pair (R := R) a b * e4Pair c d = 0 := by
  simp only [e4Pair, mul_assoc]
  rcases h with rfl | rfl | rfl | rfl
  · rw [← mul_assoc (ExteriorAlgebra.ι R (e4 b)), e4_swap a b]
    simp only [neg_mul, mul_neg, ← mul_assoc]
    rw [e4_sq, zero_mul, zero_mul, neg_zero]
  · rw [e4_swap a c, mul_neg, mul_neg, ← mul_assoc (ExteriorAlgebra.ι R (e4 b)), e4_swap a b]
    simp only [neg_mul, mul_neg, neg_neg, ← mul_assoc]
    rw [e4_sq, zero_mul, zero_mul]
  · rw [e4_mul_zero_of_eq_left (Or.inl rfl), mul_zero]
  · rw [e4_mul_zero_of_eq_left (Or.inr rfl), mul_zero]

/-- **`PGK₁` Part 1 (Grassmann Progressive Product = Plücker Ray Coordinates)**:
for ANY `u, v : Vec4 R` over ANY `[CommRing R]`, `ι (vec4ToFin4 u) * ι (vec4ToFin4 v) =
pluckerToExterior2 (Vec4.wedge u v)`. -/
theorem ι_vec4_mul_ι_vec4 (u v : Vec4 R) :
    ExteriorAlgebra.ι R (vec4ToFin4 u) * ExteriorAlgebra.ι R (vec4ToFin4 v) =
      pluckerToExterior2 (Vec4.wedge u v) := by
  rw [vec4ToFin4_eq u, vec4ToFin4_eq v]
  simp only [map_add, map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  have hdiag : ∀ i : Fin 4,
      ExteriorAlgebra.ι R (e4 (R := R) i) * ExteriorAlgebra.ι R (e4 (R := R) i) = 0 :=
    fun i => e4_sq i
  have hrev : ∀ i j : Fin 4,
      ExteriorAlgebra.ι R (e4 (R := R) j) * ExteriorAlgebra.ι R (e4 (R := R) i) =
        -(ExteriorAlgebra.ι R (e4 (R := R) i) * ExteriorAlgebra.ι R (e4 (R := R) j)) :=
    fun i j => e4_swap i j
  rw [hdiag 0, hdiag 1, hdiag 2, hdiag 3,
    hrev 0 1, hrev 0 2, hrev 0 3, hrev 1 2, hrev 1 3, hrev 2 3]
  simp only [smul_zero, add_zero, zero_add, smul_neg, pluckerToExterior2, e4Pair, Vec4.wedge]
  module

/-- **`PGK₁` Part 2 (Grassmann 4-Fold Wedge = Plücker Incidence = Klein Polar Form)**:
over ANY `[CommRing R]`, `pluckerToExterior2 P * pluckerToExterior2 Q = (Plucker6.polar P Q) • extVol4`. -/
theorem pluckerToExterior2_mul_pluckerToExterior2 (P Q : Plucker6 R) :
    pluckerToExterior2 P * pluckerToExterior2 Q = (Plucker6.polar P Q) • extVol4 := by
  dsimp [pluckerToExterior2]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [e4Pair_01_23, e4Pair_02_13, e4Pair_03_12, e4Pair_12_03, e4Pair_13_02, e4Pair_23_01]
  repeat rw [e4_mul_pair_zero (by decide)]
  simp only [smul_zero, add_zero, zero_add, smul_neg, smul_smul, Plucker6.polar_formula]
  module

theorem extVol4_eq_ιMulti_basisFun :
    extVol4 (R := R) = ExteriorAlgebra.ιMulti R 4 (Pi.basisFun R (Fin 4)) := by
  have hb : ∀ k : Fin 4, Pi.basisFun R (Fin 4) k = e4 k := fun k => by
    ext j
    simp [Pi.basisFun_apply, e4, Pi.single_apply, eq_comm]
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  simp only [extVol4, Matrix.vecTail, Function.comp_apply, hb, mul_assoc]
  rfl

end CommRing

section FieldHodge

variable {K : Type*} [Field K]

private theorem basisFun4_pair {i j : Fin 4} (hij : i < j) :
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra {i, j} = e4Pair i j := by
  let b := Pi.basisFun K (Fin 4)
  let s : Finset (Fin 4) := {i, j}
  have hcard : s.card = 2 := Finset.card_pair hij.ne
  rw [ExteriorAlgebra.basis_apply_ofCard b hcard]
  let g := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hcard)
  have hg_mem : ∀ k : Fin 2, g k ∈ s := fun k =>
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ (g k)).1 ⟨k, rfl⟩
  have hg_lt : g 0 < g 1 := g.strictMono (by decide)
  have hm0 : g 0 = i ∨ g 0 = j := by simpa [s] using hg_mem 0
  have hm1 : g 1 = i ∨ g 1 = j := by simpa [s] using hg_mem 1
  have hg0 : g 0 = i := by
    rcases hm0 with h | h <;> rcases hm1 with h' | h' <;> omega
  have hg1 : g 1 = j := by
    rcases hm0 with h | h <;> rcases hm1 with h' | h' <;> omega
  have hb : ∀ k : Fin 4, b k = e4 k := fun k => by
    ext r
    simp [b, Pi.basisFun_apply, e4, Pi.single_apply, eq_comm]
  change ExteriorAlgebra.ιMulti K 2 (fun k => b (g k)) = e4Pair i j
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  have hsucc : (Fin.succ 0 : Fin 2) = 1 := rfl
  simp only [Matrix.vecTail, Function.comp_apply, hsucc, hg0, hg1, hb, e4Pair]

private theorem extVol4_eq_volume_basisFun :
    extVol4 (R := K) = volume (Pi.basisFun K (Fin 4)) := by
  let b := Pi.basisFun K (Fin 4)
  let g := Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofCard (Finset.card_fin 4))
  have hg_lt : ∀ {a c : Fin 4}, a < c → g a < g c := fun h => g.strictMono h
  have hlt01 : g 0 < g 1 := hg_lt (by decide)
  have hlt12 : g 1 < g 2 := hg_lt (by decide)
  have hlt23 : g 2 < g 3 := hg_lt (by decide)
  have hb3 : (g 3).val < 4 := (g 3).isLt
  have hg0 : g 0 = 0 := Fin.ext (by omega)
  have hg1 : g 1 = 1 := Fin.ext (by omega)
  have hg2 : g 2 = 2 := Fin.ext (by omega)
  have hg3 : g 3 = 3 := Fin.ext (by omega)
  have hfun : (fun i : Fin 4 => b (g i)) = b := by
    funext ⟨i, hi⟩
    interval_cases i
    · exact congrArg b hg0
    · exact congrArg b hg1
    · exact congrArg b hg2
    · exact congrArg b hg3
  have heq : b.ExteriorAlgebra Finset.univ = ExteriorAlgebra.ιMulti K 4 b := by
    rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_fin 4)]
    change ExteriorAlgebra.ιMulti K 4 (fun i => b (g i)) = ExteriorAlgebra.ιMulti K 4 b
    rw [hfun]
  rw [extVol4_eq_ιMulti_basisFun, volume]
  exact heq.symm

/-- **`PGK₁` Part 3 (Grassmann Hodge Star `GA₂` = Klein Correlation Duality `EK₄`)**:
for every `P : Plucker6 K` over ANY field `K`, Grassmann's Hodge star `hodge (Pi.basisFun K (Fin 4))`
equals Klein's `kleinHodgeDual` on the embedded exterior bivector. -/
theorem hodge_pluckerToExterior2_eq_kleinHodgeDual (P : Plucker6 K) :
    hodge (Pi.basisFun K (Fin 4)) (pluckerToExterior2 P) =
      pluckerToExterior2 (kleinHodgeDual P) := by
  let b := Pi.basisFun K (Fin 4)
  have hunit : ∀ (s sc : Finset (Fin 4)) (c : K),
      sc = sᶜ → b.ExteriorAlgebra s * b.ExteriorAlgebra sc = c • volume b →
        (orientationUnit (K := K) s : K) = c := fun s sc c hsc hmul => by
    have hbc := basis_mul_compl b s
    rw [← hsc, hmul] at hbc
    exact (smul_left_injective K (volume_ne_zero b) hbc).symm
  have h01 : e4Pair (R := K) 0 1 = b.ExteriorAlgebra {0, 1} := (basisFun4_pair (by decide)).symm
  have h02 : e4Pair (R := K) 0 2 = b.ExteriorAlgebra {0, 2} := (basisFun4_pair (by decide)).symm
  have h03 : e4Pair (R := K) 0 3 = b.ExteriorAlgebra {0, 3} := (basisFun4_pair (by decide)).symm
  have h12 : e4Pair (R := K) 1 2 = b.ExteriorAlgebra {1, 2} := (basisFun4_pair (by decide)).symm
  have h13 : e4Pair (R := K) 1 3 = b.ExteriorAlgebra {1, 3} := (basisFun4_pair (by decide)).symm
  have h23 : e4Pair (R := K) 2 3 = b.ExteriorAlgebra {2, 3} := (basisFun4_pair (by decide)).symm
  have hs01 : hodge b (e4Pair 0 1) = e4Pair 2 3 := by
    rw [h01, hodge_basis]
    have hc : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
    have hu : (orientationUnit (K := K) {0, 1} : K) = 1 :=
      hunit {0, 1} {2, 3} 1 hc.symm (by
        rw [← h01, ← h23, e4Pair_01_23, one_smul, extVol4_eq_volume_basisFun])
    rw [hu, one_smul, hc, ← h23]
  have hs02 : hodge b (e4Pair 0 2) = -e4Pair 1 3 := by
    rw [h02, hodge_basis]
    have hc : ({0, 2} : Finset (Fin 4))ᶜ = {1, 3} := by decide
    have hu : (orientationUnit (K := K) {0, 2} : K) = -1 :=
      hunit {0, 2} {1, 3} (-1) hc.symm (by
        rw [← h02, ← h13, e4Pair_02_13, neg_one_smul, extVol4_eq_volume_basisFun])
    rw [hu, neg_one_smul, hc, ← h13]
  have hs03 : hodge b (e4Pair 0 3) = e4Pair 1 2 := by
    rw [h03, hodge_basis]
    have hc : ({0, 3} : Finset (Fin 4))ᶜ = {1, 2} := by decide
    have hu : (orientationUnit (K := K) {0, 3} : K) = 1 :=
      hunit {0, 3} {1, 2} 1 hc.symm (by
        rw [← h03, ← h12, e4Pair_03_12, one_smul, extVol4_eq_volume_basisFun])
    rw [hu, one_smul, hc, ← h12]
  have hs12 : hodge b (e4Pair 1 2) = e4Pair 0 3 := by
    rw [h12, hodge_basis]
    have hc : ({1, 2} : Finset (Fin 4))ᶜ = {0, 3} := by decide
    have hu : (orientationUnit (K := K) {1, 2} : K) = 1 :=
      hunit {1, 2} {0, 3} 1 hc.symm (by
        rw [← h12, ← h03, e4Pair_12_03, one_smul, extVol4_eq_volume_basisFun])
    rw [hu, one_smul, hc, ← h03]
  have hs13 : hodge b (e4Pair 1 3) = -e4Pair 0 2 := by
    rw [h13, hodge_basis]
    have hc : ({1, 3} : Finset (Fin 4))ᶜ = {0, 2} := by decide
    have hu : (orientationUnit (K := K) {1, 3} : K) = -1 :=
      hunit {1, 3} {0, 2} (-1) hc.symm (by
        rw [← h13, ← h02, e4Pair_13_02, neg_one_smul, extVol4_eq_volume_basisFun])
    rw [hu, neg_one_smul, hc, ← h02]
  have hs23 : hodge b (e4Pair 2 3) = e4Pair 0 1 := by
    rw [h23, hodge_basis]
    have hc : ({2, 3} : Finset (Fin 4))ᶜ = {0, 1} := by decide
    have hu : (orientationUnit (K := K) {2, 3} : K) = 1 :=
      hunit {2, 3} {0, 1} 1 hc.symm (by
        rw [← h23, ← h01, e4Pair_23_01, one_smul, extVol4_eq_volume_basisFun])
    rw [hu, one_smul, hc, ← h01]
  dsimp [pluckerToExterior2, kleinHodgeDual]
  dsimp only [b] at hs01 hs02 hs03 hs12 hs13 hs23
  simp only [map_add, map_smul, hs01, hs02, hs03, hs12, hs13, hs23]
  module

end FieldHodge

end ExteriorPluckerKleinDuality

/-! ## 2. `PGK₂`: Grassmann Circle Space `PGL(4)` ↔ Klein Möbius `O(3,1)` ↔ Lie `O(3,2)` -/

section CircleMoebiusLieBridge

/-- **`PGK₂` Part 1 (2-to-1 Oriented/Unoriented Circle Tangency Double Cover)**:
Grassmann's unoriented circle tangency `IsCircleTangent (circleVec c₁x c₁y r₁) (circleVec c₂x c₂y r₂)`
(`GA₁₂`) holds IF AND ONLY IF Lie's oriented `(3, 2)` sphere quadric pairing (`EK₇`) vanishes
for either `(c₂, r₂)` or its orientation reversal `(c₂, -r₂)`. -/
theorem grassmann_circleTangent_iff_lie_double_cover (c₁ c₂ : Fin 2 → ℝ) (r₁ r₂ : ℝ) :
    IsCircleTangent (circleVec (c₁ 0) (c₁ 1) r₁) (circleVec (c₂ 0) (c₂ 1) r₂) ↔
      lieQuadricBilin 2 (lieSphereVec 2 c₁ r₁) (lieSphereVec 2 c₂ r₂) = 0 ∨
        lieQuadricBilin 2 (lieSphereVec 2 c₁ r₁) (lieSphereVec 2 c₂ (-r₂)) = 0 := by
  have h1 := grassmann_no396_double_distance (c₁ 0) (c₁ 1) (c₁ 0) (c₁ 1) r₁
    (c₁ 0) (c₁ 1) r₁ (c₂ 0) (c₂ 1) r₂
  have h2 := grassmann_no396_double_distance (c₂ 0) (c₂ 1) (c₂ 0) (c₂ 1) r₂
    (c₂ 0) (c₂ 1) r₂ (c₂ 0) (c₂ 1) r₂
  have hl1 := (klein_sec7_lie_sphere_quadric_and_tangency c₁ c₂ r₁ r₂).2.1
  have hl2 := (klein_sec7_lie_sphere_quadric_and_tangency c₁ c₂ r₁ (-r₂)).2.1
  have hl1_eq : (∑ i : Fin 2, (c₁ i - c₂ i) ^ 2) - (r₁ - r₂) ^ 2 =
      ((c₁ 0 - c₂ 0) ^ 2 + (c₁ 1 - c₂ 1) ^ 2 - r₁ ^ 2 - r₂ ^ 2 + 2 * r₁ * r₂) := by
    rw [Fin.sum_univ_two]
    ring
  have hl2_eq : (∑ i : Fin 2, (c₁ i - c₂ i) ^ 2) - (r₁ - -r₂) ^ 2 =
      ((c₁ 0 - c₂ 0) ^ 2 + (c₁ 1 - c₂ 1) ^ 2 - r₁ ^ 2 - r₂ ^ 2 - 2 * r₁ * r₂) := by
    rw [Fin.sum_univ_two]
    ring
  have htan : IsCircleTangent (circleVec (c₁ 0) (c₁ 1) r₁) (circleVec (c₂ 0) (c₂ 1) r₂) ↔
      ((c₁ 0 - c₂ 0) ^ 2 + (c₁ 1 - c₂ 1) ^ 2 - r₁ ^ 2 - r₂ ^ 2 + 2 * r₁ * r₂) *
        ((c₁ 0 - c₂ 0) ^ 2 + (c₁ 1 - c₂ 1) ^ 2 - r₁ ^ 2 - r₂ ^ 2 - 2 * r₁ * r₂) = 0 := by
    unfold IsCircleTangent
    rw [h1.2.2, h1.2.1, h2.2.1]
    have hp : (((c₁ 0 - c₂ 0) ^ 2 + (c₁ 1 - c₂ 1) ^ 2 - r₁ ^ 2 - r₂ ^ 2) ^ 2 =
          -2 * r₁ ^ 2 * (-2 * r₂ ^ 2)) ↔
        (((c₁ 0 - c₂ 0) ^ 2 + (c₁ 1 - c₂ 1) ^ 2 - r₁ ^ 2 - r₂ ^ 2) ^ 2 - 4 * r₁ ^ 2 * r₂ ^ 2 = 0) := by
      constructor
      · intro h; linarith
      · intro h; linarith
    have hfac : ((c₁ 0 - c₂ 0) ^ 2 + (c₁ 1 - c₂ 1) ^ 2 - r₁ ^ 2 - r₂ ^ 2) ^ 2 - 4 * r₁ ^ 2 * r₂ ^ 2 =
        ((c₁ 0 - c₂ 0) ^ 2 + (c₁ 1 - c₂ 1) ^ 2 - r₁ ^ 2 - r₂ ^ 2 + 2 * r₁ * r₂) *
          ((c₁ 0 - c₂ 0) ^ 2 + (c₁ 1 - c₂ 1) ^ 2 - r₁ ^ 2 - r₂ ^ 2 - 2 * r₁ * r₂) := by ring
    rw [hp, hfac]
  rw [htan, mul_eq_zero]
  constructor
  · rintro (ha | hb)
    · left
      rw [hl1_eq] at hl1
      linarith
    · right
      rw [hl2_eq] at hl2
      linarith
  · rintro (ha | hb)
    · left
      rw [ha, mul_zero] at hl1
      rw [hl1_eq] at hl1
      exact hl1.symm
    · right
      rw [hb, mul_zero] at hl2
      rw [hl2_eq] at hl2
      exact hl2.symm

/-- **`PGK₂` Part 2 (Three-Tier Geometry Hierarchy: Grassmann `PGL(4)` / Möbius `O(3,1)` / Lie `O(3,2)`)**:
1. `GL(4, ℝ)` preserves syncyclicity of circles yet can break unoriented circle tangency (`GA₁₂`).
2. `O(circleBilin)` (Möbius inversion) preserves unoriented circle tangency and zero-radius points (`EK₆`).
3. `O(lieQuadricBilin 2)` (Lie contact transformations, incl. `laguerreShift`) preserves oriented
   tangency and maps zero-radius points to nonzero-radius circles (`EK₇`). -/
theorem pgk2_circle_moebius_lie_three_tier_bridge :
    (∀ (T : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (C₁ C₂ C₃ C₄ : Fin 4 → ℝ),
      IsSyncyclic4 (T C₁) (T C₂) (T C₃) (T C₄) ↔ IsSyncyclic4 C₁ C₂ C₃ C₄) ∧
      (∃ (T : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (u v : Fin 4 → ℝ),
        IsCircleTangent u v ∧ ¬ IsCircleTangent (T u) (T v)) ∧
      (∀ (T : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ)),
        (∀ u v, lieQuadricBilin 2 (T u) (T v) = lieQuadricBilin 2 u v) →
          ∀ c₁ c₂ r₁ r₂,
            lieQuadricBilin 2 (T (lieSphereVec 2 c₁ r₁)) (T (lieSphereVec 2 c₂ r₂)) = 0 ↔
            IsOrientedSphereTangent c₁ r₁ c₂ r₂) ∧
      (∀ t : ℝ, ∀ u v : Fin 5 → ℝ,
        lieQuadricBilin 2 (laguerreShift 2 t u) (laguerreShift 2 t v) = lieQuadricBilin 2 u v) ∧
      (lieSphereVec 2 0 0 ⟨4, by omega⟩ = 0 ∧ laguerreShift 2 1 (lieSphereVec 2 0 0) ⟨4, by omega⟩ = 1) := by
  refine ⟨note97_syncyclic_vs_moebius_tangency.1, note97_syncyclic_vs_moebius_tangency.2.2, ?_, ?_, ?_⟩
  · intro T hT c₁ c₂ r₁ r₂
    rw [hT]
    exact (klein_sec7_lie_sphere_quadric_and_tangency c₁ c₂ r₁ r₂).2.2.symm
  · intro t u v
    exact (klein_sec7_laguerre_shift_theorems 2 0 t u v 0 0).2.2.1
  · exact (klein_sec7_laguerre_shift_theorems 2 0 1 0 0 0 0).2.2.2.2

end CircleMoebiusLieBridge

/-! ## 3. `PGK₃`: Grassmann Darboux–Pfaffian ↔ Plücker Linear Complex ↔ Klein Line/Contact -/

section PfaffianPluckerKleinContact

/-- **`PGK₃` (Grassmann Pfaffian Square = Plücker Discriminant = Klein Line/Contact Dimension)**:
1. `pluckerToExterior2 C * pluckerToExterior2 C = (2 * kleinQ C) • extVol4`.
2. `(complexMatrix C).det = (kleinQ C) ^ 2` (`PL₁`) and nondegeneracy iff `kleinQ C ≠ 0` (`EK₂/PL₃`).
3. Every isotropic subspace of Grassmann–Lie `canonicalSymplecticForm K n` has `2 * finrank W ≤ 2 * n`,
   matching the `n`-dimensional Legendrian contact manifolds preserved by Klein's `legendreContact n`. -/
theorem pgk3_pfaffian_plucker_klein_contact_bridge {R : Type*} [CommRing R]
    (C : Plucker6 R) (K : Type*) [Field K] (n : ℕ) (W : Submodule K (Fin (2 * n) → K))
    (hW : ∀ x ∈ W, ∀ y ∈ W, canonicalSymplecticForm K n x y = 0) :
    (pluckerToExterior2 C * pluckerToExterior2 C = (2 * Plucker6.kleinQ C) • extVol4) ∧
      ((complexMatrix C).det = (Plucker6.kleinQ C) ^ 2) ∧
      (2 * Module.finrank K W ≤ 2 * n) ∧
      (∀ w dw : ContactJetSpace n R,
        legendreContact n (legendreContact n w) = w ∧
        contactOneForm n (legendreContact n w) (dLegendreContact n w dw) = -contactOneForm n w dw) := by
  refine ⟨?_, complexMatrix_det C,
    Nat.mul_le_mul_left 2 (lie_no503_canonical_symplectic_assembly K n W hW).1, ?_⟩
  · have hp := pluckerToExterior2_mul_pluckerToExterior2 C C
    have hpol : Plucker6.polar C C = 2 * Plucker6.kleinQ C := by
      simp [Plucker6.polar_formula, Plucker6.kleinQ]
      ring
    rwa [hpol] at hp
  · intro w dw
    have hc := klein_sec9_contact_legendre_unification n w dw 0 0 0 0 (fun _ => 0) 0 0
      (differentiableAt_const 0) 0 (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      0 (by simp) 0 0
    exact ⟨hc.2.2.2.1, hc.2.2.2.2.1⟩

end PfaffianPluckerKleinContact

/-! ## 4. `PGK₄` & `EK₁₀`: Exterior Resultant ↔ Hesse Transference, `V₄` Quartic, & Causal Poset -/

section ResultantHesseKummerAndMasterSynthesis

private theorem sylvester_two_lin_det {K : Type*} [Field K] (u₁ v₁ u₂ v₂ : K) :
    (Pi.basisFun K (Fin 2)).det
        (sylvesterColumns (Polynomial.C v₁ + Polynomial.C u₁ * Polynomial.X)
          (Polynomial.C v₂ + Polynomial.C u₂ * Polynomial.X) 1 1) =
      u₁ * v₂ - u₂ * v₁ := by
  let f := Polynomial.C v₁ + Polynomial.C u₁ * Polynomial.X
  let g := Polynomial.C v₂ + Polynomial.C u₂ * Polynomial.X
  let b := Pi.basisFun K (Fin 2)
  rw [Module.Basis.det_apply]
  have hmat : b.toMatrix (sylvesterColumns f g 1 1) = Matrix.of ![![v₂, v₁], ![u₂, u₁]] := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    fin_cases i <;> fin_cases j <;>
      simp [sylvesterColumns, polyTruncVec, f, g, Fin.addCases]
  rw [hmat, Matrix.det_fin_two]
  dsimp
  ring

/-- **`PGK₄` Part 1 (Grassmann Exterior Resultant `GA₂₇` ↔ Hesse Transference `EK₄`)**:
for any two linear binary forms `u₁ X + v₁` and `u₂ X + v₂` (`u₁, u₂ ≠ 0`) over `[Field K]`,
their Grassmann exterior resultant vanishes IF AND ONLY IF they fail to be coprime IF AND ONLY IF
Hesse's transferred quadratic point `hessePairPoint u₁ v₁ u₂ v₂` lies on the discriminant conic
`hesseDiscForm P = 0`. -/
theorem pgk4_exterior_resultant_iff_hesseDisc {K : Type*} [Field K]
    (u₁ v₁ u₂ v₂ : K) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) :
    let f : Polynomial K := Polynomial.C v₁ + Polynomial.C u₁ * Polynomial.X
    let g : Polynomial K := Polynomial.C v₂ + Polynomial.C u₂ * Polynomial.X
    (ExteriorAlgebra.ιMulti K (1 + 1) (sylvesterColumns f g 1 1) = 0 ↔
      hesseDiscForm (hessePairPoint u₁ v₁ u₂ v₂) = 0) ∧
    (¬ IsCoprime f g ↔ hesseDiscForm (hessePairPoint u₁ v₁ u₂ v₂) = 0) := by
  intro f g
  have hfdeg : f.natDegree = 1 := by
    have hX : (Polynomial.C u₁ * Polynomial.X).natDegree = 1 := by
      exact Polynomial.natDegree_C_mul_X u₁ hu₁
    dsimp only [f]
    rw [add_comm]
    have hdegC : (Polynomial.C v₁ : Polynomial K).natDegree = 0 := Polynomial.natDegree_C v₁
    have hlt : (Polynomial.C v₁ : Polynomial K).natDegree < (Polynomial.C u₁ * Polynomial.X).natDegree := by
      omega
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, hX]
  have hgdeg : g.natDegree = 1 := by
    have hX : (Polynomial.C u₂ * Polynomial.X).natDegree = 1 := by
      exact Polynomial.natDegree_C_mul_X u₂ hu₂
    dsimp only [g]
    rw [add_comm]
    have hdegC : (Polynomial.C v₂ : Polynomial K).natDegree = 0 := Polynomial.natDegree_C v₂
    have hlt : (Polynomial.C v₂ : Polynomial K).natDegree < (Polynomial.C u₂ * Polynomial.X).natDegree := by
      omega
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, hX]
  let b := Pi.basisFun K (Fin 2)
  have hι : ExteriorAlgebra.ιMulti K (1 + 1) (sylvesterColumns f g 1 1) =
      (u₁ * v₂ - u₂ * v₁) • b.ExteriorAlgebra Finset.univ := by
    have hdet := ιMulti_eq_det_smul_volume b (sylvesterColumns f g 1 1)
    change ExteriorAlgebra.ιMulti K 2 (sylvesterColumns f g 1 1) = _
    rw [hdet, sylvester_two_lin_det u₁ v₁ u₂ v₂]
  have hhd : hesseDiscForm (hessePairPoint u₁ v₁ u₂ v₂) = -(u₁ * v₂ - u₂ * v₁) ^ 2 :=
    (hesse_transference_theorems (1 : Matrix (Fin 2) (Fin 2) K) u₁ v₁ u₂ v₂ 0 0).2.2.1
  have hhd0 : hesseDiscForm (hessePairPoint u₁ v₁ u₂ v₂) = 0 ↔ u₁ * v₂ - u₂ * v₁ = 0 := by
    rw [hhd, neg_eq_zero, sq_eq_zero_iff]
  have hmain : ExteriorAlgebra.ιMulti K (1 + 1) (sylvesterColumns f g 1 1) = 0 ↔
      hesseDiscForm (hessePairPoint u₁ v₁ u₂ v₂) = 0 := by
    rw [hι, smul_eq_zero, hhd0]
    refine ⟨fun h => h.resolve_right (b.ExteriorAlgebra.ne_zero Finset.univ), fun h => Or.inl h⟩
  refine ⟨hmain, ?_⟩
  have hf_ne : f ≠ 0 := fun hf0 => by rw [hf0, Polynomial.natDegree_zero] at hfdeg; omega
  have hg136 := (grassmann_no136_exterior_resultant_eq_zero_iff f g).1
  rw [hfdeg, hgdeg] at hg136
  rw [← hmain, hg136]
  exact ⟨fun h => ⟨Or.inl hf_ne, h⟩, fun h => h.2⟩

/-- **`PGK₄` Part 2 (Plücker `V₄`-Symmetric Kummer Quartic ↔ Klein `V₄` Spherical Tetrahedron)**:
both Plücker's 10-monomial `canonicalKummerQuartic` (`PL₈`) and Klein's equal-edge symmetrical
tetrahedron `kleinTetraVertex` (`EK₉`, underlying the binary quartic syzygetic pencil) are
exact `V₄`-symmetric quartic/spherical configurations. -/
theorem pgk4_plucker_kummer_klein_tetrahedron_v4_bridge {R : Type*} [CommRing R]
    (A B C D : R) (g : Fin 4 × Fin 4) (q : Fin 4 → R) (x y z μ u v : R) :
    canonicalKummerQuartic A B C D (kummerGroupAct g q) = canonicalKummerQuartic A B C D q ∧
      (∀ k : Fin 4, (kleinTetraVertex x y z k 0) ^ 2 + (kleinTetraVertex x y z k 1) ^ 2 +
        (kleinTetraVertex x y z k 2) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2) ∧
      (quarticSexticT (1 : R) 0 μ 0 1 u v = (1 - 9 * μ ^ 2) * u * v * (u ^ 4 - v ^ 4)) :=
  ⟨canonicalKummerQuartic_group_invariant A B C D g q,
   (klein_noteVII_symmetrical_tetrahedron x y z).1,
   (klein_noteVII_binary_quartic_syzygy_and_pencil 1 0 μ 0 1 μ u v 0 0 0 0 0 0 0 0).2.2.2.1⟩

/-- The 10 mathematical archetypes (`EK₁`–`EK₁₀`) extracted from Felix Klein's 1872 *Erlangen
Program* (`0807.3161v1`), culminating in `EK10` (the Triadic Plücker–Grassmann–Klein Synthesis). -/
inductive KleinErlangenArchetype : Type
  | EK1  -- Transformation groups & 1893 Footnote 8 infinite-set inverse requirement (§1)
  | EK2  -- Dualistic correlations, Principal Group, & Cayley–Klein absolute (§1, §3)
  | EK3  -- Subgroup adjoining, `Abbildung` transfer, Body orbit normal-core kernel (§2, §4, §5)
  | EK4  -- Veronese conic transfer, Hesse transference, Plücker–Klein Hodge duality (§4, §5, Note V)
  | EK5  -- Sharp 3-transitivity of `PGL(2)` & Note VI boundary collapse (§10.1, Note VI)
  | EK6  -- Stereographic `(n+1, 1)` lightcone & Footnote 26 anti-holomorphic separation (§6)
  | EK7  -- Lie `(n+1, 2)` sphere geometry & Laguerre radius-shift group (§7, Fn. 29/31)
  | EK8  -- Cremona involution, `fderiv` linearization, `(2n+1)` Legendrian & Legendre (§8–9)
  | EK9  -- Quaternion `SO(3)`, binary cubic/quartic syzygies, & `V₄` tetrahedron (Fn. 37, Note VII)
  | EK10 -- Unified Plücker–Grassmann–Klein Erlangen Causal Atlas (`PGK₁`–`PGK₄`)
  deriving DecidableEq, Repr

/-- Exact transitive dependency bitmask on the 10 Erlangen archetypes. -/
def kleinMask : KleinErlangenArchetype → UInt16
  | .EK1  => 0b0000000001
  | .EK2  => 0b0000000011 -- ≥ EK1
  | .EK3  => 0b0000000101 -- ≥ EK1
  | .EK4  => 0b0000001111 -- ≥ EK1, EK2, EK3
  | .EK5  => 0b0000011111 -- ≥ EK1..EK4
  | .EK6  => 0b0000101111 -- ≥ EK1..EK4
  | .EK7  => 0b0001101111 -- ≥ EK1..EK4, EK6
  | .EK8  => 0b0010000111 -- ≥ EK1, EK2, EK3
  | .EK9  => 0b0100001111 -- ≥ EK1..EK4
  | .EK10 => 0b1111111111 -- ≥ EK1..EK9

instance : LE KleinErlangenArchetype where
  le a b := (kleinMask a &&& kleinMask b) = kleinMask a

instance (a b : KleinErlangenArchetype) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable ((kleinMask a &&& kleinMask b) = kleinMask a))

instance : PartialOrder KleinErlangenArchetype where
  le := (· ≤ ·)
  le_refl a := by cases a <;> decide
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide

/-- Explicit non-linear branching witnesses in the Erlangen Program DAG (`EK2/EK3`, `EK5/EK7`,
`EK7/EK8`, `EK8/EK9` are pairwise incomparable). -/
theorem klein_causal_poset_branching_witnesses :
    (¬ (KleinErlangenArchetype.EK2 ≤ .EK3) ∧ ¬ (KleinErlangenArchetype.EK3 ≤ .EK2)) ∧
      (¬ (KleinErlangenArchetype.EK5 ≤ .EK7) ∧ ¬ (KleinErlangenArchetype.EK7 ≤ .EK5)) ∧
      (¬ (KleinErlangenArchetype.EK7 ≤ .EK8) ∧ ¬ (KleinErlangenArchetype.EK8 ≤ .EK7)) ∧
      (¬ (KleinErlangenArchetype.EK8 ≤ .EK9) ∧ ¬ (KleinErlangenArchetype.EK9 ≤ .EK8)) := by
  decide

theorem klein_all_reach_master (a : KleinErlangenArchetype) :
    a ≤ KleinErlangenArchetype.EK10 := by
  cases a <;> decide

/-- **Grand Plücker–Grassmann–Klein Master Synthesis (`EK₁₀`)**:
assembles all ten Erlangen archetypes (`EK₁`–`EK₁₀`) together with the four Triadic Bridges
(`PGK₁`–`PGK₄`) into a single constructive kernel-checked theorem over native Mathlib. -/
theorem plucker_grassmann_klein_grand_synthesis {R K : Type*} [CommRing R] [Field K]
    (C : Plucker6 K) (u₁ v₁ u₂ v₂ : K) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (a₀ a₁ a₂ a₃ a₄ μ x y z : R) (w dw : ContactJetSpace 3 R)
    (q v : ℍ[ℝ]) (hq : q.normSq = 1) (hv : v.re = 0) :
    (∃ f : Equiv.Perm ℤ, f ∈ posShiftSet ∧ f⁻¹ ∉ posShiftSet) ∧
      (∀ (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (_ha : M 0 0 ≠ 0),
        ((∀ j : Fin n, M 0 j.succ = 0) ∧
          ∃ r : ℝˣ, ∀ vec : Fin n → ℝ,
            ∑ i : Fin n, (M *ᵥ Fin.cons (0 : ℝ) vec) i.succ ^ 2 =
              (r : ℝ) ^ 2 * ∑ i : Fin n, (vec i) ^ 2) ↔
        ∃ g : EuclideanSimilarity n, ∀ vec : Fin n → ℝ,
          M *ᵥ Fin.cons (1 : ℝ) vec = M 0 0 • Fin.cons (1 : ℝ) (g • vec)) ∧
      (hodge (Pi.basisFun K (Fin 4)) (pluckerToExterior2 C) =
        pluckerToExterior2 (kleinHodgeDual C)) ∧
      (pluckerToExterior2 C * pluckerToExterior2 C = (2 * Plucker6.kleinQ C) • extVol4) ∧
      ((complexMatrix C).det = (Plucker6.kleinQ C) ^ 2) ∧
      (∀ P₁ P₂ P₄ : HomPoint2 K, HomPoint2.crossNum P₁ P₂ P₁ P₄ = 0) ∧
      (∀ c₁ c₂ : Fin 2 → ℝ, ∀ r₁ r₂ : ℝ,
        IsCircleTangent (circleVec (c₁ 0) (c₁ 1) r₁) (circleVec (c₂ 0) (c₂ 1) r₂) ↔
          lieQuadricBilin 2 (lieSphereVec 2 c₁ r₁) (lieSphereVec 2 c₂ r₂) = 0 ∨
            lieQuadricBilin 2 (lieSphereVec 2 c₁ r₁) (lieSphereVec 2 c₂ (-r₂)) = 0) ∧
      (contactOneForm 3 (legendreContact 3 w) (dLegendreContact 3 w dw) =
        -contactOneForm 3 w dw) ∧
      ((quatConjRot q v).re = 0 ∧ (quatConjRot q v).normSq = v.normSq) ∧
      ((cubicJacobian a₀ a₁ a₂ a₃ x y) ^ 2 + 4 * (cubicHessian a₀ a₁ a₂ a₃ x y) ^ 3 =
        cubicDiscriminant a₀ a₁ a₂ a₃ * (binaryCubic a₀ a₁ a₂ a₃ x y) ^ 2) ∧
      ((quarticSexticT a₀ a₁ a₂ a₃ a₄ x y) ^ 2 =
        -4 * (quarticHessian a₀ a₁ a₂ a₃ a₄ x y) ^ 3 +
          quarticInvI a₀ a₁ a₂ a₃ a₄ * quarticHessian a₀ a₁ a₂ a₃ a₄ x y *
            (binaryQuartic a₀ a₁ a₂ a₃ a₄ x y) ^ 2 -
          quarticInvJ a₀ a₁ a₂ a₃ a₄ * (binaryQuartic a₀ a₁ a₂ a₃ a₄ x y) ^ 3) ∧
      (¬ IsCoprime (Polynomial.C v₁ + Polynomial.C u₁ * Polynomial.X)
          (Polynomial.C v₂ + Polynomial.C u₂ * Polynomial.X) ↔
        hesseDiscForm (hessePairPoint u₁ v₁ u₂ v₂) = 0) ∧
      (canonicalKummerQuartic a₀ a₁ a₂ a₃ (![x, y, z, μ]) =
        canonicalKummerQuartic a₀ a₁ a₂ a₃ (kummerGroupAct (2, 1) ![x, y, z, μ])) := by
  refine ⟨klein_fn8_infinite_perm_countermodel.2.2.2,
    fun n M ha => klein_sec3_principal_group_iff_spherical_absolute M ha,
    hodge_pluckerToExterior2_eq_kleinHodgeDual C,
    ?_, complexMatrix_det C,
    fun P₁ P₂ P₄ => (klein_noteVI_boundary_collapse_and_pole_metric P₁ P₂ P₄).1,
    grassmann_circleTangent_iff_lie_double_cover,
    ?_,
    ⟨(klein_fn37_quaternion_so3_action q 1 1 v hq hv).1,
      (klein_fn37_quaternion_so3_action q 1 1 v hq hv).2.1⟩,
    (klein_noteVII_binary_cubic_syzygy a₀ a₁ a₂ a₃ x y).1,
    (klein_noteVII_binary_quartic_syzygy_and_pencil a₀ a₁ a₂ a₃ a₄ μ x y 0 0 0 0 0 0 0 0).1,
    (pgk4_exterior_resultant_iff_hesseDisc u₁ v₁ u₂ v₂ hu₁ hu₂).2,
    (canonicalKummerQuartic_group_invariant a₀ a₁ a₂ a₃ (2, 1) ![x, y, z, μ]).symm⟩
  · have hp := pluckerToExterior2_mul_pluckerToExterior2 C C
    have hpol : Plucker6.polar C C = 2 * Plucker6.kleinQ C := by
      simp [Plucker6.polar_formula, Plucker6.kleinQ]
      ring
    rwa [hpol] at hp
  · have hc := klein_sec9_contact_legendre_unification 3 w dw 0 0 0 0 (fun _ => 0) 0 0
      (differentiableAt_const 0) 0 (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      0 (by simp) 0 0
    exact hc.2.2.2.2.1

end ResultantHesseKummerAndMasterSynthesis

/-! ## 5. `PGK₅`: Exact 5-Carrier Plücker–Grassmann–Klein Pentagon Equivalence (`Gr(2,4)`/`KleinLocus`/`G(2,V;ℝ)`/`ℙBivector4`) -/

section GrassmannianPentagonClosure

/-- Full-rank `2 × 4` real matrix chart (linearly independent rows in `Vec4`). -/
abbrev FullRankMatrix24 : Type :=
  { C : Matrix (Fin 2) (Fin 4) ℝ //
    LinearIndependent ℝ (grassmannianRowExteriorVec4 C) }

/-- Map `I4` index back to `Fin 4`. -/
private def i4ToFin4 : InfoGeometry.Canonical.FierzKleinFoundation.I4 → Fin 4
  | .t => 0
  | .x => 1
  | .y => 2
  | .z => 3

/-- Standard closed T17 inhabitant for `FullRankMatrix24`: rows `(e₀, e₁)`. -/
def stdFullRankMatrix24 : FullRankMatrix24 :=
  ⟨!![(1 : ℝ), 0, 0, 0; 0, 1, 0, 0], by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 := congrFun hc InfoGeometry.Canonical.FierzKleinFoundation.I4.t
    have h1 := congrFun hc InfoGeometry.Canonical.FierzKleinFoundation.I4.x
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
      grassmannianRowExteriorVec4, smul_eq_mul] at h0 h1
    simp at h0 h1
    rcases i with ⟨i, hi⟩
    interval_cases i
    · exact h0
    · exact h1⟩

/-- Explicit T16 noncommutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem pgk5_gl2_matrix_noncommutative :
    ∃ a b : Matrix (Fin 2) (Fin 2) ℝ, a * b ≠ b * a := by
  refine ⟨!![1, 1; 0, 1], !![1, 0; 1, 1], fun hEq => ?_⟩
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hEq
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

private lemma rowExterior_i4ToFin4 (C : Matrix (Fin 2) (Fin 4) ℝ) (i : Fin 2) (j : Fin 4) :
    grassmannianRowExteriorVec4 C i (match j with | 0 => .t | 1 => .x | 2 => .y | 3 => .z) = C i j := by
  fin_cases j <;> rfl

private lemma rowExterior_left_mul (A : Matrix (Fin 2) (Fin 2) ℝ) (C : Matrix (Fin 2) (Fin 4) ℝ)
    (i : Fin 2) :
    grassmannianRowExteriorVec4 (A * C) i =
      ∑ j : Fin 2, A i j • grassmannianRowExteriorVec4 C j := by
  ext k
  cases k <;> simp [grassmannianRowExteriorVec4, Matrix.mul_apply, Fin.sum_univ_two]

/-- Left `GL(2, ℝ)` equivalence on full-rank `2 × 4` matrices: two charts represent the same
plane iff they lie in the same left `GL(2, ℝ)` orbit. -/
def fullRankMatrix24Setoid : Setoid FullRankMatrix24 where
  r C₁ C₂ := ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) * C₁.1 = C₂.1
  iseqv :=
    { refl := fun _ => ⟨1, by simp⟩
      symm := fun ⟨g, hg⟩ => ⟨g⁻¹, by
        rw [← hg, ← Matrix.mul_assoc]
        simp⟩
      trans := fun ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ => ⟨g₂ * g₁, by
        rw [Units.val_mul, Matrix.mul_assoc, hg₁, hg₂]⟩ }

abbrev FullRankMatrix24Quotient : Type := Quotient fullRankMatrix24Setoid

private lemma span_rowExterior_eq_span_iff (C₁ C₂ : FullRankMatrix24) :
    grassmannianMatrixToRealTwoPlane C₁.1 C₁.2 =
        grassmannianMatrixToRealTwoPlane C₂.1 C₂.2 ↔
      ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) * C₁.1 = C₂.1 := by
  constructor
  · intro hspan
    have hsp :
        Submodule.span ℝ (Set.range (grassmannianRowExteriorVec4 C₁.1)) =
          Submodule.span ℝ (Set.range (grassmannianRowExteriorVec4 C₂.1)) :=
      congrArg Subtype.val hspan
    let b₁ : Module.Basis (Fin 2) ℝ (Submodule.span ℝ (Set.range (grassmannianRowExteriorVec4 C₁.1))) :=
      Module.Basis.span C₁.2
    let b₂ : Module.Basis (Fin 2) ℝ (Submodule.span ℝ (Set.range (grassmannianRowExteriorVec4 C₂.1))) :=
      Module.Basis.span C₂.2
    let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
      b₁.coord j ⟨grassmannianRowExteriorVec4 C₂.1 i, by
        rw [hsp]
        exact Submodule.subset_span (Set.mem_range_self i)⟩
    let B : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
      b₂.coord j ⟨grassmannianRowExteriorVec4 C₁.1 i, by
        rw [← hsp]
        exact Submodule.subset_span (Set.mem_range_self i)⟩
    have hArow (i : Fin 2) :
        grassmannianRowExteriorVec4 C₂.1 i = ∑ j : Fin 2, A i j • grassmannianRowExteriorVec4 C₁.1 j := by
      have hr := congrArg Subtype.val (b₁.sum_repr ⟨grassmannianRowExteriorVec4 C₂.1 i, by
        rw [hsp]; exact Submodule.subset_span (Set.mem_range_self i)⟩).symm
      rw [Submodule.coe_sum] at hr
      refine hr.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [Submodule.coe_smul_of_tower]
      dsimp [A, b₁, Module.Basis.coord]
      rw [Module.Basis.span_apply]
    have hBrow (i : Fin 2) :
        grassmannianRowExteriorVec4 C₁.1 i = ∑ j : Fin 2, B i j • grassmannianRowExteriorVec4 C₂.1 j := by
      have hr := congrArg Subtype.val (b₂.sum_repr ⟨grassmannianRowExteriorVec4 C₁.1 i, by
        rw [← hsp]; exact Submodule.subset_span (Set.mem_range_self i)⟩).symm
      rw [Submodule.coe_sum] at hr
      refine hr.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [Submodule.coe_smul_of_tower]
      dsimp [B, b₂, Module.Basis.coord]
      rw [Module.Basis.span_apply]
    have hAC : A * C₁.1 = C₂.1 := by
      ext i k
      have hk := congrFun (hArow i) (match k with | 0 => .t | 1 => .x | 2 => .y | 3 => .z)
      fin_cases k <;> simp [A, Matrix.mul_apply, Fin.sum_univ_two, grassmannianRowExteriorVec4] at hk ⊢ <;>
        linarith [hk]
    have hBC : B * C₂.1 = C₁.1 := by
      ext i k
      have hk := congrFun (hBrow i) (match k with | 0 => .t | 1 => .x | 2 => .y | 3 => .z)
      fin_cases k <;> simp [B, Matrix.mul_apply, Fin.sum_univ_two, grassmannianRowExteriorVec4] at hk ⊢ <;>
        linarith [hk]
    have hBA : B * A = 1 := by
      ext i k
      have hi1 : grassmannianRowExteriorVec4 ((B * A) * C₁.1) i =
          grassmannianRowExteriorVec4 C₁.1 i := by
        rw [Matrix.mul_assoc, hAC, hBC]
      rw [rowExterior_left_mul] at hi1
      have hdiff : ∑ j : Fin 2, ((B * A) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) •
          grassmannianRowExteriorVec4 C₁.1 j = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, sub_eq_zero]
        rw [hi1]
        fin_cases i <;> simp [Matrix.one_apply]
      have hcoef := (Fintype.linearIndependent_iff.mp C₁.2) _ hdiff k
      exact sub_eq_zero.mp hcoef
    have hAB : A * B = 1 := by
      ext i k
      have hi2 : grassmannianRowExteriorVec4 ((A * B) * C₂.1) i =
          grassmannianRowExteriorVec4 C₂.1 i := by
        rw [Matrix.mul_assoc, hBC, hAC]
      rw [rowExterior_left_mul] at hi2
      have hdiff : ∑ j : Fin 2, ((A * B) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) •
          grassmannianRowExteriorVec4 C₂.1 j = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, sub_eq_zero]
        rw [hi2]
        fin_cases i <;> simp [Matrix.one_apply]
      have hcoef := (Fintype.linearIndependent_iff.mp C₂.2) _ hdiff k
      exact sub_eq_zero.mp hcoef
    exact ⟨⟨A, B, hAB, hBA⟩, hAC⟩
  · rintro ⟨g, hg⟩
    apply Subtype.ext
    change Submodule.span ℝ (Set.range (grassmannianRowExteriorVec4 C₁.1)) =
      Submodule.span ℝ (Set.range (grassmannianRowExteriorVec4 C₂.1))
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : C₁.1 = ((↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℝ)) * C₂.1 := by
        rw [← hg, ← Matrix.mul_assoc]
        simp
      have hrow : grassmannianRowExteriorVec4 C₁.1 i =
          ∑ j : Fin 2, (↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) i j • grassmannianRowExteriorVec4 C₂.1 j := by
        rw [← rowExterior_left_mul, ← h1]
      rw [hrow]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hrow : grassmannianRowExteriorVec4 C₂.1 i =
          ∑ j : Fin 2, (g : Matrix (Fin 2) (Fin 2) ℝ) i j • grassmannianRowExteriorVec4 C₁.1 j := by
        rw [← rowExterior_left_mul, hg]
      rw [hrow]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

/-- Map from full-rank `2 × 4` matrices modulo left `GL(2, ℝ)` row operations to real two-planes. -/
noncomputable def fullRankMatrix24QuotientToRealTwoPlane :
    FullRankMatrix24Quotient → RealTwoPlane :=
  Quotient.lift (fun C : FullRankMatrix24 => grassmannianMatrixToRealTwoPlane C.1 C.2)
    (fun C₁ C₂ h => (span_rowExterior_eq_span_iff C₁ C₂).mpr h)

/-- Canonical equivalence `(FullRankMatrix24 / GL₂(ℝ)) ≃ RealTwoPlane`: closes the matrix-chart
orbit quotient gap documented in `GrassmannianCartanInteroperability`. -/
noncomputable def fullRankMatrix24QuotientEquivRealTwoPlane :
    FullRankMatrix24Quotient ≃ RealTwoPlane :=
  Equiv.ofBijective fullRankMatrix24QuotientToRealTwoPlane
    ⟨by
      refine Quotient.ind₂ fun C₁ C₂ h => ?_
      exact Quotient.sound ((span_rowExterior_eq_span_iff C₁ C₂).mp h),
     by
      intro P
      obtain ⟨uv, huv⟩ := frameSpan_surjective P
      let C : Matrix (Fin 2) (Fin 4) ℝ := Matrix.of fun i j =>
        uv.1 i (match j with | 0 => .t | 1 => .x | 2 => .y | 3 => .z)
      have hvec : grassmannianRowExteriorVec4 C = uv.1 := by
        ext i k
        cases k <;> rfl
      have hli : LinearIndependent ℝ (grassmannianRowExteriorVec4 C) := by
        rw [hvec]
        exact nondegenerateExteriorFrame_linearIndependent uv
      refine ⟨Quotient.mk fullRankMatrix24Setoid ⟨C, hli⟩, ?_⟩
      change grassmannianMatrixToRealTwoPlane C hli = P
      apply Subtype.ext
      change Submodule.span ℝ (Set.range (grassmannianRowExteriorVec4 C)) = P.1
      rw [hvec]
      exact congrArg Subtype.val huv⟩

@[simp] theorem fullRankMatrix24QuotientEquivRealTwoPlane_mk (C : FullRankMatrix24) :
    fullRankMatrix24QuotientEquivRealTwoPlane (Quotient.mk fullRankMatrix24Setoid C) =
      grassmannianMatrixToRealTwoPlane C.1 C.2 :=
  rfl

private lemma finrank_vec4_eq_four :
    Module.finrank ℝ InfoGeometry.Canonical.FierzKleinFoundation.Vec4 = 4 := by
  change Module.finrank ℝ (InfoGeometry.Canonical.FierzKleinFoundation.I4 → ℝ) = 4
  rw [Module.finrank_pi]
  rfl

/-- Canonical equivalence between native `RealTwoPlane` (two-dimensional subspaces of `Vec4`) and
Mathlib's Grothendieck Grassmannian `Module.Grassmannian ℝ Vec4 2` (`G(2, Vec4; ℝ)`). -/
noncomputable def realTwoPlaneEquivMathlibGrassmannian :
    RealTwoPlane ≃ Module.Grassmannian ℝ InfoGeometry.Canonical.FierzKleinFoundation.Vec4 2 where
  toFun P :=
    { toSubmodule := P.1
      finite_quotient := inferInstance
      projective_quotient := inferInstance
      rankAtStalk_eq := fun p => by
        have hsum := Submodule.finrank_quotient_add_finrank P.1
        rw [finrank_vec4_eq_four, P.2] at hsum
        have h2 : Module.finrank ℝ (InfoGeometry.Canonical.FierzKleinFoundation.Vec4 ⧸ P.1) = 2 := by
          omega
        simp [Module.rankAtStalk_eq_finrank_of_free, h2] }
  invFun G :=
    ⟨G.toSubmodule, by
      have hfree := G.rankAtStalk_eq ⟨⊥, Ideal.isPrime_bot⟩
      simp only [Module.rankAtStalk_eq_finrank_of_free] at hfree
      have hsum := Submodule.finrank_quotient_add_finrank G.toSubmodule
      have h2 : Module.finrank ℝ (InfoGeometry.Canonical.FierzKleinFoundation.Vec4 ⧸ G.toSubmodule) = 2 := by
        simpa using hfree
      rw [finrank_vec4_eq_four, h2] at hsum
      omega⟩
  left_inv P := Subtype.ext rfl
  right_inv G := Module.Grassmannian.ext rfl

@[simp] theorem realTwoPlaneEquivMathlibGrassmannian_toSubmodule (P : RealTwoPlane) :
    (realTwoPlaneEquivMathlibGrassmannian P).toSubmodule = P.1 :=
  rfl

/-- Projective Klein quadric predicate directly on `ℙ ℝ Bivector4`. -/
def ProjectiveIsKleinFormZero : ℙ ℝ InfoGeometry.Canonical.FierzKleinFoundation.Bivector4 → Prop :=
  Projectivization.lift
    (f := fun P : { P : InfoGeometry.Canonical.FierzKleinFoundation.Bivector4 // P ≠ 0 } =>
      InfoGeometry.Canonical.FierzKleinFoundation.kleinForm P.1 = 0)
    (fun X Y c hXY => by
      apply propext
      have hc : c ≠ 0 := fun hc0 => by
        rw [hc0, zero_smul] at hXY
        exact X.2 hXY
      have hscaled : InfoGeometry.Canonical.FierzKleinFoundation.kleinForm (c • Y.1) =
          c ^ 2 * InfoGeometry.Canonical.FierzKleinFoundation.kleinForm Y.1 := by
        simp only [InfoGeometry.Canonical.FierzKleinFoundation.kleinForm]
        change (c * Y.1.p01) * (c * Y.1.p23) -
            (c * Y.1.p02) * (c * Y.1.p13) +
            (c * Y.1.p03) * (c * Y.1.p12) =
          c ^ 2 * (Y.1.p01 * Y.1.p23 - Y.1.p02 * Y.1.p13 + Y.1.p03 * Y.1.p12)
        ring
      rw [hXY, hscaled, mul_eq_zero, sq_eq_zero_iff]
      simp [hc])

/-- Projective Klein quadric subtype in `ℙ ℝ Bivector4`. -/
abbrev ProjectivePluckerQuadricLocus : Type :=
  { p : ℙ ℝ InfoGeometry.Canonical.FierzKleinFoundation.Bivector4 //
    ProjectiveIsKleinFormZero p }

@[simp] theorem projectiveIsKleinFormZero_mk_iff
    (P : InfoGeometry.Canonical.FierzKleinFoundation.Bivector4) (hP : P ≠ 0) :
    ProjectiveIsKleinFormZero (Projectivization.mk ℝ P hP) ↔
      InfoGeometry.Canonical.FierzKleinFoundation.kleinForm P = 0 := by
  simp [ProjectiveIsKleinFormZero, Projectivization.lift_mk]

/-- Embedding of `KleinQuadricPlucker.Plucker6 ℝ` into `Bivector4` matching exact Plücker minor order. -/
def bivector4OfPlucker6
    (P : InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 ℝ) :
    InfoGeometry.Canonical.FierzKleinFoundation.Bivector4 where
  p01 := P.p01
  p02 := P.p02
  p03 := P.p03
  p12 := P.p12
  p13 := P.p13
  p23 := P.p23

private lemma kleinForm_bivector4OfPlucker6
    (P : InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 ℝ) :
    InfoGeometry.Canonical.FierzKleinFoundation.kleinForm (bivector4OfPlucker6 P) =
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ P := rfl

private lemma exteriorBivectorLinearEquiv_rowFrame (C : FullRankMatrix24) :
    exteriorBivectorLinearEquiv
        (exteriorPower.ιMulti ℝ 2 (grassmannianRowsExteriorFrame C.1 C.2).1) =
      bivector4OfPlucker6 (plucker6OfMatrix C.1) := by
  have hvec : (grassmannianRowsExteriorFrame C.1 C.2).1 =
      ![grassmannianRowExteriorVec4 C.1 0, grassmannianRowExteriorVec4 C.1 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec, exteriorBivectorLinearEquiv_ιMulti]
  apply InfoGeometry.Canonical.FierzKleinFoundation.Bivector4.ext <;>
    simp [InfoGeometry.Canonical.FierzKleinFoundation.wedgeVec4, bivector4OfPlucker6,
      plucker6OfMatrix, grassmannianRowExteriorVec4,
      InfoGeometry.Canonical.AmplituhedronBCFW.pluckerMinor]

/-- Canonical equivalence between the projective exterior Klein locus `KleinLocus ⊆ ℙ ℝ (⋀² Vec4)`
and the coordinate projective Plücker quadric `ProjectivePluckerQuadricLocus ⊆ ℙ ℝ Bivector4`,
induced directly by `ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv`. -/
noncomputable def kleinLocusEquivProjectivePluckerQuadric :
    KleinLocus ≃ ProjectivePluckerQuadricLocus where
  toFun p :=
    ⟨Projectivization.map exteriorBivectorLinearEquiv.toLinearMap
        exteriorBivectorLinearEquiv.injective p.1, by
      rcases p with ⟨q, hq⟩
      induction q using Projectivization.ind with
      | _ X hX =>
        rw [isKlein_mk_iff] at hq
        rw [Projectivization.map_mk, projectiveIsKleinFormZero_mk_iff]
        exact hq⟩
  invFun q :=
    ⟨Projectivization.map exteriorBivectorLinearEquiv.symm.toLinearMap
        exteriorBivectorLinearEquiv.symm.injective q.1, by
      rcases q with ⟨p, hp⟩
      induction p using Projectivization.ind with
      | _ P hP =>
        rw [projectiveIsKleinFormZero_mk_iff] at hp
        rw [Projectivization.map_mk, isKlein_mk_iff]
        change InfoGeometry.Canonical.FierzKleinFoundation.kleinForm
          (exteriorBivectorLinearEquiv (exteriorBivectorLinearEquiv.symm P)) = 0
        simpa using hp⟩
  left_inv p := by
    rcases p with ⟨q, hq⟩
    apply Subtype.ext
    induction q using Projectivization.ind with
    | _ X hX => simp [Projectivization.map_mk]
  right_inv q := by
    rcases q with ⟨p, hp⟩
    apply Subtype.ext
    induction p using Projectivization.ind with
    | _ P hP => simp [Projectivization.map_mk]

/-- **Master 5-Carrier Plücker–Grassmann–Klein Pentagon Theorem (`PGK₅`)**:
Unifies all five repository carriers of `Gr(2,4)` into one strictly commuting equivalence diagram:
1. `FullRankMatrix24Quotient` (2×4 matrix charts modulo left `GL(2, ℝ)` row operations);
2. `RealTwoPlane` (native 2D subspaces `{ P ≤ Vec4 // finrank = 2 }`);
3. `Module.Grassmannian ℝ Vec4 2` (Mathlib's scheme-oriented `G(2, Vec4; ℝ)`);
4. `KleinLocus` (projectivized decomposable rays in `ℙ ℝ (⋀² Vec4)`);
5. `ProjectivePluckerQuadricLocus` (projectivized `2 × 2` Plücker minor vectors `[plucker6OfMatrix C]`
   in `ℙ ℝ Bivector4` satisfying `kleinForm = 0`). -/
theorem pluckerGrassmannKlein_pentagon_commutes (C : FullRankMatrix24) :
    let qMat : FullRankMatrix24Quotient := Quotient.mk fullRankMatrix24Setoid C
    let P : RealTwoPlane := grassmannianMatrixToRealTwoPlane C.1 C.2
    let hMinorNe : bivector4OfPlucker6 (plucker6OfMatrix C.1) ≠ 0 := by
      rw [← exteriorBivectorLinearEquiv_rowFrame C]
      exact (exteriorBivectorLinearEquiv.map_ne_zero_iff).mpr
        (grassmannianRowsExteriorFrame C.1 C.2).2
    fullRankMatrix24QuotientEquivRealTwoPlane qMat = P ∧
      realTwoPlaneEquivMathlibGrassmannian P =
        ⟨P.1, inferInstance, inferInstance, fun _ => by
          have hs := Submodule.finrank_quotient_add_finrank P.1
          rw [finrank_vec4_eq_four, P.2] at hs
          have h2 : Module.finrank ℝ (InfoGeometry.Canonical.FierzKleinFoundation.Vec4 ⧸ P.1) = 2 := by
            omega
          simp [Module.rankAtStalk_eq_finrank_of_free, h2]⟩ ∧
      realTwoPlaneEquivKleinLocus P =
        frameToKleinLocus (grassmannianRowsExteriorFrame C.1 C.2) ∧
      (kleinLocusEquivProjectivePluckerQuadric (realTwoPlaneEquivKleinLocus P)).1 =
        Projectivization.mk ℝ (bivector4OfPlucker6 (plucker6OfMatrix C.1)) hMinorNe ∧
      InfoGeometry.Canonical.FierzKleinFoundation.kleinForm
        (bivector4OfPlucker6 (plucker6OfMatrix C.1)) = 0 := by
  dsimp only
  have hkl := grassmannianMatrixToKleinLocus_eq_rowFrame C.1 C.2
  have hMinorEq := exteriorBivectorLinearEquiv_rowFrame C
  have hMinorNe : bivector4OfPlucker6 (plucker6OfMatrix C.1) ≠ 0 := by
    rw [← hMinorEq]
    exact (exteriorBivectorLinearEquiv.map_ne_zero_iff).mpr
      (grassmannianRowsExteriorFrame C.1 C.2).2
  refine ⟨rfl, rfl, hkl, ?_, ?_⟩
  · rw [hkl]
    change Projectivization.map exteriorBivectorLinearEquiv.toLinearMap
        exteriorBivectorLinearEquiv.injective
        (Projectivization.mk ℝ _ (grassmannianRowsExteriorFrame C.1 C.2).2) =
      Projectivization.mk ℝ (bivector4OfPlucker6 (plucker6OfMatrix C.1)) hMinorNe
    rw [Projectivization.map_mk]
    congr 1
  · rw [kleinForm_bivector4OfPlucker6]
    exact kleinQ_plucker6OfMatrix C.1

end GrassmannianPentagonClosure

end InfoGeometry.Canonical.PluckerGrassmannKleinUnifiedSynthesis
