/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.Solvable
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Tactic.FinCases
import InfoGeometry.Topology.V4RootSystem

/-!
# Felix Klein's Icosahedral Group $A_5 \hookrightarrow \mathrm{PSU}(2)$, Quintic Obstruction, and Modular $j$-Invariant

This owner module formalizes the classical Felix Klein Erlangen architecture connecting:

1. **The Binary Icosahedral Group $2I \subset \mathrm{SU}(2)$ and Classical $A_5 \hookrightarrow \mathrm{PSU}(2)$**:
   Explicit unit-quaternion realization in `SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ` over the
   golden ratio `Real.goldenRatio`, quotiented by the central sign group `{1, -1}` to form `PSU2`.
   Conjugation on Klein's five inscribed octahedron/cube frames `cubeFrame : Fin 5 → Set Mat2C`
   establishes an explicit isomorphism `alternatingGroup (Fin 5) ≃* icosahedralPSU2Subgroup`
   and injective embedding `kleinIcosahedralPSU2Embedding : alternatingGroup (Fin 5) →* PSU2`.
2. **Klein's Homogeneous Icosahedral Polynomial Invariants & $1728$ Syzygy**:
   Constructs `kleinIcosahedralVertexF` (degree 12), `kleinIcosahedralFaceH` (degree 20), and
   `kleinIcosahedralEdgeT` (degree 30), proves their homogeneous scaling laws and Klein's exact
   icosahedral syzygy `T² + H³ = 1728 f⁵`, and defines the rational ratio
   `kleinBinaryFormRatio`. Its scaling invariance is proved; invariance under the embedded
   icosahedral group is not established here.
3. **Quintic Radical Unsolvability (`AbelRuffini`) & Icosahedral / Tschirnhaus Reduction**:
   Proves `¬ Group.IsSolvable (alternatingGroup (Fin 5))` from `alternatingGroup.isSimpleGroup_five`,
   transfers unsolvability to `icosahedralPSU2Subgroup`, connects to Mathlib's `solvableByRad`
   (`quintic_galois_A5_not_solvableByRad`), and formalizes Tschirnhaus quartic-term depression
   and a binary-form ratio identity. A separate Brioschi-form owner proves a
   quintic root identity from the displayed forms; its identification with the
   actual icosahedral representation and an arbitrary input quintic remains open.
4. **The Modular $j$-Invariant on $\mathbb{H}$**:
   Defines `jInvariant (z : ℍ) := E₄ z ^ 3 / discriminant z` and its normalization
   `normalizedJInvariant := jInvariant / 1728`,
   proves nowhere-vanishing denominator (`discriminant_ne_zero`), full $\mathrm{SL}(2, \mathbb{Z})$
   modular invariance (`T`, `S`, and arbitrary `γ : SL(2, ℤ)`), the `j(z) - 1728 = E₆(z)² / Δ(z)`
   identity, exact elliptic point values `j(i) = 1728` and `j(ρ) = 0`, holomorphicity (`MDiff`),
   and non-constancy / failure to be a holomorphic weight-0 modular form. For each `n`, every
   level-one modular form of weight `12 * n`, divided by `Δ^n`, has a unique polynomial expression
   in `j` of degree at most `n`. The modular-curve Hauptmodul theorem in its full form (meromorphic
   extension at the cusp and generation of the level-one function field) is not established here.

No `sorry`, `admit`, `native_decide`, or custom axioms are used.
-/

noncomputable section

namespace InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ

open Complex Matrix UpperHalfPlane ModularForm ModularFormClass SlashInvariantForm CongruenceSubgroup
open InfoGeometry.MetaCompiler
open scoped MatrixGroups Manifold

/-! ## Section 1: Pure Scalar Quaternion, Golden-Ratio, and `ℝ³` Rotation Algebra -/

private def qMul0 (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) : ℝ :=
  a₁ * a₂ - b₁ * b₂ - c₁ * c₂ - d₁ * d₂

private def qMul1 (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) : ℝ :=
  a₁ * b₂ + b₁ * a₂ + c₁ * d₂ - d₁ * c₂

private def qMul2 (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) : ℝ :=
  a₁ * c₂ - b₁ * d₂ + c₁ * a₂ + d₁ * b₂

private def qMul3 (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) : ℝ :=
  a₁ * d₂ + b₁ * c₂ - c₁ * b₂ + d₁ * a₂

private def qConjX (a b c d x y z : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) * x + 2 * (b * c - a * d) * y + 2 * (b * d + a * c) * z

private def qConjY (a b c d x y z : ℝ) : ℝ :=
  2 * (b * c + a * d) * x + (a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2) * y + 2 * (c * d - a * b) * z

private def qConjZ (a b c d x y z : ℝ) : ℝ :=
  2 * (b * d - a * c) * x + 2 * (c * d + a * b) * y + (a ^ 2 - b ^ 2 - c ^ 2 + d ^ 2) * z

private lemma qConjX_neg_x (a b c d : ℝ) :
    qConjX a b c d (-1) 0 0 = -qConjX a b c d 1 0 0 := by
  simp [qConjX]

private lemma qConjY_neg_x (a b c d : ℝ) :
    qConjY a b c d (-1) 0 0 = -qConjY a b c d 1 0 0 := by
  simp [qConjY]

private lemma qConjZ_neg_x (a b c d : ℝ) :
    qConjZ a b c d (-1) 0 0 = -qConjZ a b c d 1 0 0 := by
  simp [qConjZ]

private lemma qConjX_neg_y (a b c d : ℝ) :
    qConjX a b c d 0 (-1) 0 = -qConjX a b c d 0 1 0 := by
  simp [qConjX]

private lemma qConjY_neg_y (a b c d : ℝ) :
    qConjY a b c d 0 (-1) 0 = -qConjY a b c d 0 1 0 := by
  simp [qConjY]

private lemma qConjZ_neg_y (a b c d : ℝ) :
    qConjZ a b c d 0 (-1) 0 = -qConjZ a b c d 0 1 0 := by
  simp [qConjZ]

private lemma qConjX_neg_z (a b c d : ℝ) :
    qConjX a b c d 0 0 (-1) = -qConjX a b c d 0 0 1 := by
  simp [qConjX]

private lemma qConjY_neg_z (a b c d : ℝ) :
    qConjY a b c d 0 0 (-1) = -qConjY a b c d 0 0 1 := by
  simp [qConjY]

private lemma qConjZ_neg_z (a b c d : ℝ) :
    qConjZ a b c d 0 0 (-1) = -qConjZ a b c d 0 0 1 := by
  simp [qConjZ]

private lemma qMul_norm_sq (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ)
    (h₁ : a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2 + d₁ ^ 2 = 1)
    (h₂ : a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2 + d₂ ^ 2 = 1) :
    (qMul0 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) ^ 2 + (qMul1 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) ^ 2 +
    (qMul2 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) ^ 2 + (qMul3 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) ^ 2 = 1 := by
  have heuler :
      (qMul0 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) ^ 2 + (qMul1 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) ^ 2 +
      (qMul2 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) ^ 2 + (qMul3 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) ^ 2 =
      (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2 + d₁ ^ 2) * (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2 + d₂ ^ 2) := by
    simp only [qMul0, qMul1, qMul2, qMul3]
    ring
  rw [heuler, h₁, h₂, mul_one]

private lemma qMul_neg_norm_sq (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    a ^ 2 + (-b) ^ 2 + (-c) ^ 2 + (-d) ^ 2 = 1 := by
  linarith [h, show (-b) ^ 2 = b ^ 2 by ring,
    show (-c) ^ 2 = c ^ 2 by ring, show (-d) ^ 2 = d ^ 2 by ring]

private lemma qConj_scalar_part_zero (a b c d x y z : ℝ) :
    qMul0 (qMul0 a b c d 0 x y z) (qMul1 a b c d 0 x y z)
      (qMul2 a b c d 0 x y z) (qMul3 a b c d 0 x y z) a (-b) (-c) (-d) = 0 := by
  simp only [qMul0, qMul1, qMul2, qMul3]
  ring

private lemma qConj_vec1 (a b c d x y z : ℝ) :
    qMul1 (qMul0 a b c d 0 x y z) (qMul1 a b c d 0 x y z)
      (qMul2 a b c d 0 x y z) (qMul3 a b c d 0 x y z) a (-b) (-c) (-d) =
    qConjX a b c d x y z := by
  simp only [qMul0, qMul1, qMul2, qMul3, qConjX]
  ring

private lemma qConj_vec2 (a b c d x y z : ℝ) :
    qMul2 (qMul0 a b c d 0 x y z) (qMul1 a b c d 0 x y z)
      (qMul2 a b c d 0 x y z) (qMul3 a b c d 0 x y z) a (-b) (-c) (-d) =
    qConjY a b c d x y z := by
  simp only [qMul0, qMul1, qMul2, qMul3, qConjY]
  ring

private lemma qConj_vec3 (a b c d x y z : ℝ) :
    qMul3 (qMul0 a b c d 0 x y z) (qMul1 a b c d 0 x y z)
      (qMul2 a b c d 0 x y z) (qMul3 a b c d 0 x y z) a (-b) (-c) (-d) =
    qConjZ a b c d x y z := by
  simp only [qMul0, qMul1, qMul2, qMul3, qConjZ]
  ring

private lemma complex_quat_mul_00 (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) :
    ((a₁ : ℂ) + b₁ * Complex.I) * (a₂ + b₂ * Complex.I) +
      (c₁ + d₁ * Complex.I) * (-c₂ + d₂ * Complex.I) =
    (qMul0 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℂ) +
      (qMul1 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℂ) * Complex.I := by
  simp only [qMul0, qMul1]
  apply Complex.ext <;> simp <;> ring

private lemma complex_quat_mul_01 (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) :
    ((a₁ : ℂ) + b₁ * Complex.I) * (c₂ + d₂ * Complex.I) +
      (c₁ + d₁ * Complex.I) * (a₂ - b₂ * Complex.I) =
    (qMul2 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℂ) +
      (qMul3 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℂ) * Complex.I := by
  simp only [qMul2, qMul3]
  apply Complex.ext <;> simp <;> ring

private lemma complex_quat_mul_10 (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) :
    (-(c₁ : ℂ) + d₁ * Complex.I) * (a₂ + b₂ * Complex.I) +
      (a₁ - b₁ * Complex.I) * (-c₂ + d₂ * Complex.I) =
    -(qMul2 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℂ) +
      (qMul3 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℂ) * Complex.I := by
  simp only [qMul2, qMul3]
  apply Complex.ext <;> simp <;> ring

private lemma complex_quat_mul_11 (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) :
    (-(c₁ : ℂ) + d₁ * Complex.I) * (c₂ + d₂ * Complex.I) +
      (a₁ - b₁ * Complex.I) * (a₂ - b₂ * Complex.I) =
    (qMul0 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℂ) -
      (qMul1 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℂ) * Complex.I := by
  simp only [qMul0, qMul1]
  apply Complex.ext <;> simp <;> ring

private lemma complex_quat_det (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    ((a : ℂ) + b * Complex.I) * (a - b * Complex.I) -
      (c + d * Complex.I) * (-c + d * Complex.I) = 1 := by
  have hc : ((a : ℂ) + b * Complex.I) * (a - b * Complex.I) -
      (c + d * Complex.I) * (-c + d * Complex.I) =
      ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℝ) : ℂ) := by
    calc
      ((a : ℂ) + b * Complex.I) * (a - b * Complex.I) -
          (c + d * Complex.I) * (-c + d * Complex.I)
          = (a : ℂ) ^ 2 - b ^ 2 * Complex.I ^ 2 + c ^ 2 - d ^ 2 * Complex.I ^ 2 := by ring
      _ = ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℝ) : ℂ) := by
        rw [Complex.I_sq]; push_cast; ring
  rw [hc, h, Complex.ofReal_one]

private lemma complex_quat_star_00 (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    ((a : ℂ) + b * Complex.I) * star ((a : ℂ) + b * Complex.I) +
      (c + d * Complex.I) * star (c + d * Complex.I) = 1 := by
  have hs : ((a : ℂ) + b * Complex.I) * star ((a : ℂ) + b * Complex.I) +
      (c + d * Complex.I) * star (c + d * Complex.I) =
      ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℝ) : ℂ) := by
    calc
      ((a : ℂ) + b * Complex.I) * star ((a : ℂ) + b * Complex.I) +
          (c + d * Complex.I) * star (c + d * Complex.I)
          = ((a : ℂ) + b * Complex.I) * (a - b * Complex.I) +
              (c + d * Complex.I) * (c - d * Complex.I) := by simp [sub_eq_add_neg]
      _ = (a : ℂ) ^ 2 - b ^ 2 * Complex.I ^ 2 + c ^ 2 - d ^ 2 * Complex.I ^ 2 := by ring
      _ = ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℝ) : ℂ) := by
        rw [Complex.I_sq]; push_cast; ring
  rw [hs, h, Complex.ofReal_one]

private lemma complex_quat_star_01 (a b c d : ℝ) :
    ((a : ℂ) + b * Complex.I) * star (-(c : ℂ) + d * Complex.I) +
      (c + d * Complex.I) * star (a - b * Complex.I) = 0 := by
  calc
    ((a : ℂ) + b * Complex.I) * star (-(c : ℂ) + d * Complex.I) +
        (c + d * Complex.I) * star (a - b * Complex.I)
        = ((a : ℂ) + b * Complex.I) * (-c - d * Complex.I) +
            (c + d * Complex.I) * (a + b * Complex.I) := by simp [sub_eq_add_neg]
    _ = 0 := by ring

private lemma complex_quat_star_10 (a b c d : ℝ) :
    (-(c : ℂ) + d * Complex.I) * star ((a : ℂ) + b * Complex.I) +
      (a - b * Complex.I) * star (c + d * Complex.I) = 0 := by
  calc
    (-(c : ℂ) + d * Complex.I) * star ((a : ℂ) + b * Complex.I) +
        (a - b * Complex.I) * star (c + d * Complex.I)
        = (-(c : ℂ) + d * Complex.I) * (a - b * Complex.I) +
            (a - b * Complex.I) * (c - d * Complex.I) := by simp [sub_eq_add_neg]
    _ = 0 := by ring

private lemma complex_quat_star_11 (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    (-(c : ℂ) + d * Complex.I) * star (-(c : ℂ) + d * Complex.I) +
      (a - b * Complex.I) * star (a - b * Complex.I) = 1 := by
  have hs : (-(c : ℂ) + d * Complex.I) * star (-(c : ℂ) + d * Complex.I) +
      (a - b * Complex.I) * star (a - b * Complex.I) =
      ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℝ) : ℂ) := by
    calc
      (-(c : ℂ) + d * Complex.I) * star (-(c : ℂ) + d * Complex.I) +
          (a - b * Complex.I) * star (a - b * Complex.I)
          = (-(c : ℂ) + d * Complex.I) * (-c - d * Complex.I) +
              (a - b * Complex.I) * (a + b * Complex.I) := by simp [sub_eq_add_neg]
      _ = (a : ℂ) ^ 2 - b ^ 2 * Complex.I ^ 2 + c ^ 2 - d ^ 2 * Complex.I ^ 2 := by ring
      _ = ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℝ) : ℂ) := by
        rw [Complex.I_sq]; push_cast; ring
  rw [hs, h, Complex.ofReal_one]

private lemma icosianA_norm_sq :
    (Real.goldenRatio / 2) ^ 2 + ((Real.goldenRatio - 1) / 2) ^ 2 + (1 / 2 : ℝ) ^ 2 + 0 ^ 2 = 1 := by
  have hphi : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  nlinarith [hphi]

private lemma icosianA2_norm_sq :
    ((Real.goldenRatio - 1) / 2) ^ 2 + (1 / 2 : ℝ) ^ 2 + (Real.goldenRatio / 2) ^ 2 + 0 ^ 2 = 1 := by
  linarith [icosianA_norm_sq]

private lemma icosianA3_norm_sq :
    ((1 - Real.goldenRatio) / 2) ^ 2 + (1 / 2 : ℝ) ^ 2 + (Real.goldenRatio / 2) ^ 2 + 0 ^ 2 = 1 := by
  have h1 : ((1 - Real.goldenRatio) / 2) ^ 2 = ((Real.goldenRatio - 1) / 2) ^ 2 := by ring
  linarith [icosianA2_norm_sq, h1]

private lemma icosianA4_norm_sq :
    (-Real.goldenRatio / 2) ^ 2 + ((Real.goldenRatio - 1) / 2) ^ 2 + (1 / 2 : ℝ) ^ 2 + 0 ^ 2 = 1 := by
  have h1 : (-Real.goldenRatio / 2) ^ 2 = (Real.goldenRatio / 2) ^ 2 := by ring
  linarith [icosianA_norm_sq, h1]

private lemma icosianB_norm_sq : (0 : ℝ) ^ 2 + 0 ^ 2 + 1 ^ 2 + 0 ^ 2 = 1 := by norm_num

private lemma icosianAB_norm_sq :
    (-1 / 2 : ℝ) ^ 2 + 0 ^ 2 + (Real.goldenRatio / 2) ^ 2 + ((Real.goldenRatio - 1) / 2) ^ 2 = 1 := by
  linarith [icosianA_norm_sq, show (-1 / 2 : ℝ) ^ 2 = (1 / 2 : ℝ) ^ 2 by ring]

private lemma icosianAB2_norm_sq :
    (-1 / 2 : ℝ) ^ 2 + 0 ^ 2 + (-Real.goldenRatio / 2) ^ 2 + ((1 - Real.goldenRatio) / 2) ^ 2 = 1 := by
  linarith [icosianA_norm_sq, show (-1 / 2 : ℝ) ^ 2 = (1 / 2 : ℝ) ^ 2 by ring,
    show (-Real.goldenRatio / 2) ^ 2 = (Real.goldenRatio / 2) ^ 2 by ring,
    show ((1 - Real.goldenRatio) / 2) ^ 2 = ((Real.goldenRatio - 1) / 2) ^ 2 by ring]

private lemma hurwitz_norm_sq_scalar (p q r s : ℝ) (h : p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 = 4) :
    (p / 2) ^ 2 + (q / 2) ^ 2 + (r / 2) ^ 2 + (s / 2) ^ 2 = 1 := by
  linarith [h, show (p / 2) ^ 2 + (q / 2) ^ 2 + (r / 2) ^ 2 + (s / 2) ^ 2 =
    (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) / 4 by ring]

private lemma icosian_step1_scalars :
    qMul0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = (Real.goldenRatio - 1) / 2 ∧
    qMul1 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = 1 / 2 ∧
    qMul2 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = Real.goldenRatio / 2 ∧
    qMul3 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = 0 := by
  have hphi : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [qMul0, qMul1, qMul2, qMul3]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals nlinarith [hphi, hsqrt5,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

private lemma icosian_step2_scalars :
    qMul0 ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = (1 - Real.goldenRatio) / 2 ∧
    qMul1 ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = 1 / 2 ∧
    qMul2 ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = Real.goldenRatio / 2 ∧
    qMul3 ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = 0 := by
  have hphi : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [qMul0, qMul1, qMul2, qMul3]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals nlinarith [hphi, hsqrt5,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

private lemma icosian_step3_scalars :
    qMul0 ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = -Real.goldenRatio / 2 ∧
    qMul1 ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = (Real.goldenRatio - 1) / 2 ∧
    qMul2 ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = 1 / 2 ∧
    qMul3 ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = 0 := by
  have hphi : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [qMul0, qMul1, qMul2, qMul3]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals nlinarith [hphi, hsqrt5,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

private lemma icosian_step4_scalars :
    qMul0 (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = -1 ∧
    qMul1 (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = 0 ∧
    qMul2 (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = 0 ∧
    qMul3 (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0
      (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 = 0 := by
  have hphi : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [qMul0, qMul1, qMul2, qMul3]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals nlinarith [hphi, hsqrt5,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

private lemma icosianAB_step1_scalars :
    qMul0 (-1 / 2) 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2)
      (-1 / 2) 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) = -1 / 2 ∧
    qMul1 (-1 / 2) 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2)
      (-1 / 2) 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) = 0 ∧
    qMul2 (-1 / 2) 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2)
      (-1 / 2) 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) = -Real.goldenRatio / 2 ∧
    qMul3 (-1 / 2) 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2)
      (-1 / 2) 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) = (1 - Real.goldenRatio) / 2 := by
  have hphi : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  simp only [qMul0, qMul1, qMul2, qMul3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -(1 / 2 : ℝ) * hphi
  · ring
  · ring
  · ring

private lemma icosianAB_step2_scalars :
    qMul0 (-1 / 2) 0 (-Real.goldenRatio / 2) ((1 - Real.goldenRatio) / 2)
      (-1 / 2) 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) = 1 ∧
    qMul1 (-1 / 2) 0 (-Real.goldenRatio / 2) ((1 - Real.goldenRatio) / 2)
      (-1 / 2) 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) = 0 ∧
    qMul2 (-1 / 2) 0 (-Real.goldenRatio / 2) ((1 - Real.goldenRatio) / 2)
      (-1 / 2) 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) = 0 ∧
    qMul3 (-1 / 2) 0 (-Real.goldenRatio / 2) ((1 - Real.goldenRatio) / 2)
      (-1 / 2) 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) = 0 := by
  have hphi : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  simp only [qMul0, qMul1, qMul2, qMul3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (1 / 2 : ℝ) * hphi
  · ring
  · ring
  · ring

private lemma icosian_BA_coset_scalars :
    (qMul0 ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 (1 / 2) (1 / 2) (1 / 2) (-1 / 2) =
        qMul0 0 0 1 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 ∧
     qMul1 ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 (1 / 2) (1 / 2) (1 / 2) (-1 / 2) =
        qMul1 0 0 1 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 ∧
     qMul2 ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 (1 / 2) (1 / 2) (1 / 2) (-1 / 2) =
        qMul2 0 0 1 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 ∧
     qMul3 ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 (1 / 2) (1 / 2) (1 / 2) (-1 / 2) =
        qMul3 0 0 1 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0) ∧
    (qMul0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 (-1 / 2) (1 / 2) (1 / 2) (-1 / 2) =
        qMul0 0 0 1 0 ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 ∧
     qMul1 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 (-1 / 2) (1 / 2) (1 / 2) (-1 / 2) =
        qMul1 0 0 1 0 ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 ∧
     qMul2 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 (-1 / 2) (1 / 2) (1 / 2) (-1 / 2) =
        qMul2 0 0 1 0 ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 ∧
     qMul3 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 (-1 / 2) (1 / 2) (1 / 2) (-1 / 2) =
        qMul3 0 0 1 0 ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0) ∧
    (qMul0 (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 (1 / 2) (1 / 2) (1 / 2) (1 / 2) =
        qMul0 0 0 1 0 ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0 ∧
     qMul1 (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 (1 / 2) (1 / 2) (1 / 2) (1 / 2) =
        qMul1 0 0 1 0 ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0 ∧
     qMul2 (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 (1 / 2) (1 / 2) (1 / 2) (1 / 2) =
        qMul2 0 0 1 0 ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0 ∧
     qMul3 (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 (1 / 2) (1 / 2) (1 / 2) (1 / 2) =
        qMul3 0 0 1 0 ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0) ∧
    (qMul0 ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0 (-1 / 2) (1 / 2) (1 / 2) (1 / 2) =
        qMul0 0 0 1 0 (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 ∧
     qMul1 ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0 (-1 / 2) (1 / 2) (1 / 2) (1 / 2) =
        qMul1 0 0 1 0 (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 ∧
     qMul2 ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0 (-1 / 2) (1 / 2) (1 / 2) (1 / 2) =
        qMul2 0 0 1 0 (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 ∧
     qMul3 ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0 (-1 / 2) (1 / 2) (1 / 2) (1 / 2) =
        qMul3 0 0 1 0 (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0) := by
  simp only [qMul0, qMul1, qMul2, qMul3]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> ring

/-! ## Section 2: `SU(2)`, `PSU(2)`, and Klein's Five Inscribed Cubes -/

abbrev Mat2C : Type := Matrix (Fin 2) (Fin 2) ℂ
abbrev SU2 : Type := Matrix.specialUnitaryGroup (Fin 2) ℂ

private lemma ext_mat2C {A B : Mat2C}
    (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

def quatToMat (a b c d : ℝ) : Mat2C :=
  !![(a : ℂ) + b * Complex.I, c + d * Complex.I;
    -c + d * Complex.I, a - b * Complex.I]

def quatImToMat (x y z : ℝ) : Mat2C := quatToMat 0 x y z

lemma quatToMat_injective_tuple {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ}
    (h : quatToMat a₁ b₁ c₁ d₁ = quatToMat a₂ b₂ c₂ d₂) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ ∧ d₁ = d₂ := by
  have h00 := congrArg (fun M : Mat2C => M 0 0) h
  have h01 := congrArg (fun M : Mat2C => M 0 1) h
  simp only [quatToMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01
  have h00re := congrArg Complex.re h00
  have h00im := congrArg Complex.im h00
  have h01re := congrArg Complex.re h01
  have h01im := congrArg Complex.im h01
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, zero_add] at h00re h00im h01re h01im
  exact ⟨h00re, h00im, h01re, h01im⟩

lemma quatImToMat_injective {x₁ y₁ z₁ x₂ y₂ z₂ : ℝ}
    (h : quatImToMat x₁ y₁ z₁ = quatImToMat x₂ y₂ z₂) :
    x₁ = x₂ ∧ y₁ = y₂ ∧ z₁ = z₂ := by
  have ht := quatToMat_injective_tuple h
  exact ⟨ht.2.1, ht.2.2.1, ht.2.2.2⟩

lemma quatToMat_mul (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) :
    quatToMat a₁ b₁ c₁ d₁ * quatToMat a₂ b₂ c₂ d₂ =
      quatToMat (qMul0 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) (qMul1 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂)
        (qMul2 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) (qMul3 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) := by
  apply ext_mat2C
  · simp [quatToMat, Matrix.mul_apply, Fin.sum_univ_two, complex_quat_mul_00]
  · simp [quatToMat, Matrix.mul_apply, Fin.sum_univ_two, complex_quat_mul_01]
  · simp [quatToMat, Matrix.mul_apply, Fin.sum_univ_two, complex_quat_mul_10]
  · simp [quatToMat, Matrix.mul_apply, Fin.sum_univ_two, complex_quat_mul_11]

lemma quatToMat_mem_SU2 {a b c d : ℝ} (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    quatToMat a b c d ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    apply ext_mat2C
    · simpa [quatToMat, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two] using
        complex_quat_star_00 a b c d h
    · simpa [quatToMat, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two] using
        complex_quat_star_01 a b c d
    · simpa [quatToMat, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two] using
        complex_quat_star_10 a b c d
    · simpa [quatToMat, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two] using
        complex_quat_star_11 a b c d h
  · simpa [quatToMat, Matrix.det_fin_two] using complex_quat_det a b c d h

def quatToSU2 (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) : SU2 :=
  ⟨quatToMat a b c d, quatToMat_mem_SU2 h⟩

lemma quatToSU2_eq_of_eq {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ}
    {h₁ : a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2 + d₁ ^ 2 = 1}
    {h₂ : a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2 + d₂ ^ 2 = 1}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) (hd : d₁ = d₂) :
    quatToSU2 a₁ b₁ c₁ d₁ h₁ = quatToSU2 a₂ b₂ c₂ d₂ h₂ := by
  subst ha; subst hb; subst hc; subst hd
  rfl

@[simp] lemma quatToSU2_coe (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    (quatToSU2 a b c d h : Mat2C) = quatToMat a b c d := rfl

lemma quatToSU2_mul (a₁ b₁ c₁ d₁ : ℝ) (h₁ : a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2 + d₁ ^ 2 = 1)
    (a₂ b₂ c₂ d₂ : ℝ) (h₂ : a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2 + d₂ ^ 2 = 1) :
    quatToSU2 a₁ b₁ c₁ d₁ h₁ * quatToSU2 a₂ b₂ c₂ d₂ h₂ =
      quatToSU2 (qMul0 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) (qMul1 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂)
        (qMul2 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂) (qMul3 a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂)
        (qMul_norm_sq a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ h₁ h₂) := by
  ext1
  exact quatToMat_mul a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂

lemma quatToSU2_inv (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    (quatToSU2 a b c d h)⁻¹ =
      quatToSU2 a (-b) (-c) (-d) (qMul_neg_norm_sq a b c d h) := by
  apply inv_eq_of_mul_eq_one_right
  rw [quatToSU2_mul]
  ext1
  simp only [quatToSU2_coe, Submonoid.coe_one]
  have hn0 : qMul0 a b c d a (-b) (-c) (-d) = 1 := by
    simp only [qMul0]
    linarith [h]
  have hn1 : qMul1 a b c d a (-b) (-c) (-d) = 0 := by simp only [qMul1]; linarith [h]
  have hn2 : qMul2 a b c d a (-b) (-c) (-d) = 0 := by simp only [qMul2]; linarith [h]
  have hn3 : qMul3 a b c d a (-b) (-c) (-d) = 0 := by simp only [qMul3]; linarith [h]
  rw [hn0, hn1, hn2, hn3]
  apply ext_mat2C <;> simp [quatToMat]

lemma quatToSU2_one : quatToSU2 1 0 0 0 (by norm_num) = 1 := by
  ext1
  apply ext_mat2C <;> simp [quatToMat]

def negOneSU2 : SU2 := quatToSU2 (-1) 0 0 0 (by norm_num)

lemma negOneSU2_coe : (negOneSU2 : Mat2C) = -(1 : Mat2C) := by
  apply ext_mat2C <;> simp [negOneSU2, quatToMat]

lemma negOneSU2_mul (g : SU2) : negOneSU2 * g = g * negOneSU2 := by
  ext1
  simp [negOneSU2_coe]

lemma negOneSU2_sq : negOneSU2 * negOneSU2 = 1 := by
  ext1
  simp [negOneSU2_coe]

def su2QuatI : SU2 := quatToSU2 0 1 0 0 (by norm_num)
def su2QuatJ : SU2 := quatToSU2 0 0 1 0 (by norm_num)
def su2QuatK : SU2 := quatToSU2 0 0 0 1 (by norm_num)

def matQuatI : Mat2C := quatToMat 0 1 0 0
def matQuatJ : Mat2C := quatToMat 0 0 1 0

/-- Explicit T16 non-commutativity witness on `Mat2C := Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem matQuatI_mul_matQuatJ_ne : matQuatI * matQuatJ ≠ matQuatJ * matQuatI := by
  intro h
  have h01 := congrArg (fun M : Mat2C => M 0 1) h
  simp only [matQuatI, matQuatJ, quatToMat] at h01
  norm_num at h01
  have him := congrArg Complex.im h01
  norm_num at him

/-- Explicit T16 non-commutativity witness on `Mat2C := Matrix (Fin 2) (Fin 2) ℂ` and `SU2`. -/
theorem su2_quaternion_noncommutative :
    (su2QuatI : Mat2C) * (su2QuatJ : Mat2C) ≠ (su2QuatJ : Mat2C) * (su2QuatI : Mat2C) ∧
    su2QuatI * su2QuatJ ≠ su2QuatJ * su2QuatI := by
  have hij : (su2QuatI : Mat2C) * (su2QuatJ : Mat2C) ≠ (su2QuatJ : Mat2C) * (su2QuatI : Mat2C) := by
    change matQuatI * matQuatJ ≠ matQuatJ * matQuatI
    exact matQuatI_mul_matQuatJ_ne
  refine ⟨hij, ?_⟩
  intro h
  exact hij (congrArg Subtype.val h)

def su2SignSet : Subgroup SU2 where
  carrier := { g : SU2 | g = 1 ∨ g = negOneSU2 }
  mul_mem' := by
    rintro x y (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul negOneSU2)
    · exact Or.inr (mul_one negOneSU2)
    · exact Or.inl negOneSU2_sq
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro x (rfl | rfl)
    · exact Or.inl inv_one
    · refine Or.inr (inv_eq_of_mul_eq_one_right negOneSU2_sq)

instance instNormalSu2SignSet : su2SignSet.Normal where
  conj_mem := by
    rintro n (rfl | rfl) g
    · exact Or.inl (by simp)
    · refine Or.inr ?_
      rw [← negOneSU2_mul g, mul_assoc, mul_inv_cancel, mul_one]

abbrev PSU2 : Type := SU2 ⧸ su2SignSet

def conjMat (g : SU2) (X : Mat2C) : Mat2C := (g : Mat2C) * X * (g⁻¹ : SU2)

lemma conjMat_mul (g h : SU2) (X : Mat2C) :
    conjMat (g * h) X = conjMat g (conjMat h X) := by
  simp only [conjMat, Submonoid.coe_mul, _root_.mul_inv_rev]
  simp only [mul_assoc]

lemma conjMat_one (X : Mat2C) : conjMat 1 X = X := by
  simp [conjMat]

lemma conjMat_negOne (X : Mat2C) : conjMat negOneSU2 X = X := by
  have hinv : (negOneSU2⁻¹ : SU2) = negOneSU2 := inv_eq_of_mul_eq_one_right negOneSU2_sq
  simp [conjMat, hinv, negOneSU2_coe]

lemma conjMat_signSet {n : SU2} (hn : n ∈ su2SignSet) (X : Mat2C) : conjMat n X = X := by
  rcases hn with rfl | rfl
  · exact conjMat_one X
  · exact conjMat_negOne X

lemma conjMat_quatToSU2_im (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) (x y z : ℝ) :
    conjMat (quatToSU2 a b c d h) (quatImToMat x y z) =
      quatImToMat (qConjX a b c d x y z) (qConjY a b c d x y z) (qConjZ a b c d x y z) := by
  simp only [conjMat, quatToSU2_inv, quatToSU2_coe, quatImToMat]
  rw [quatToMat_mul, quatToMat_mul, qConj_scalar_part_zero, qConj_vec1, qConj_vec2, qConj_vec3]

/-! ## Section 3: Binary Icosahedral Generators `2I ⊂ SU2`, Hurwitz Normalizer `2T`, and `A₅ ≃* I` -/

def icosianGenA : SU2 :=
  quatToSU2 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 icosianA_norm_sq

def icosianGenA2 : SU2 :=
  quatToSU2 ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 icosianA2_norm_sq

def icosianGenA3 : SU2 :=
  quatToSU2 ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0 icosianA3_norm_sq

def icosianGenA4 : SU2 :=
  quatToSU2 (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 icosianA4_norm_sq

def icosianGenB : SU2 := su2QuatJ

lemma icosianGenA_pow_two : icosianGenA ^ 2 = icosianGenA2 := by
  rw [sq, icosianGenA, quatToSU2_mul, icosianGenA2]
  ext1
  have ⟨h0, h1, h2, h3⟩ := icosian_step1_scalars
  simp only [quatToSU2_coe, h0, h1, h2, h3]

lemma icosianGenA_pow_three : icosianGenA ^ 3 = icosianGenA3 := by
  rw [pow_succ, icosianGenA_pow_two, icosianGenA2, icosianGenA, quatToSU2_mul, icosianGenA3]
  ext1
  have ⟨h0, h1, h2, h3⟩ := icosian_step2_scalars
  simp only [quatToSU2_coe, h0, h1, h2, h3]

lemma icosianGenA_pow_four : icosianGenA ^ 4 = icosianGenA4 := by
  rw [pow_succ, icosianGenA_pow_three, icosianGenA3, icosianGenA, quatToSU2_mul, icosianGenA4]
  ext1
  have ⟨h0, h1, h2, h3⟩ := icosian_step3_scalars
  simp only [quatToSU2_coe, h0, h1, h2, h3]

theorem icosianGenA_pow_five : icosianGenA ^ 5 = negOneSU2 := by
  rw [pow_succ, icosianGenA_pow_four, icosianGenA4, icosianGenA, quatToSU2_mul, negOneSU2]
  ext1
  have ⟨h0, h1, h2, h3⟩ := icosian_step4_scalars
  simp only [quatToSU2_coe, h0, h1, h2, h3]

theorem icosianGenB_sq : icosianGenB ^ 2 = negOneSU2 := by
  rw [sq, icosianGenB, su2QuatJ, quatToSU2_mul, negOneSU2]
  ext1
  simp only [quatToSU2_coe, qMul0, qMul1, qMul2, qMul3]
  norm_num

theorem icosianGenAB_cube : (icosianGenA * icosianGenB) ^ 3 = 1 := by
  have hAB : icosianGenA * icosianGenB =
      quatToSU2 (-1 / 2) 0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) icosianAB_norm_sq := by
    rw [icosianGenA, icosianGenB, su2QuatJ, quatToSU2_mul]
    ext1
    have hq0 : qMul0 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 0 1 0 = -1 / 2 := by
      simp only [qMul0]; ring
    have hq1 : qMul1 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 0 1 0 = 0 := by
      simp only [qMul1]; ring
    have hq2 : qMul2 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 0 1 0 = Real.goldenRatio / 2 := by
      simp only [qMul2]; ring
    have hq3 : qMul3 (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 0 1 0 = (Real.goldenRatio - 1) / 2 := by
      simp only [qMul3]; ring
    simp only [quatToSU2_coe, hq0, hq1, hq2, hq3]
  have hAB2 : (icosianGenA * icosianGenB) ^ 2 =
      quatToSU2 (-1 / 2) 0 (-Real.goldenRatio / 2) ((1 - Real.goldenRatio) / 2) icosianAB2_norm_sq := by
    rw [sq, hAB, quatToSU2_mul]
    ext1
    have ⟨h0, h1, h2, h3⟩ := icosianAB_step1_scalars
    simp only [quatToSU2_coe, h0, h1, h2, h3]
  rw [pow_succ, hAB2, hAB, quatToSU2_mul, ← quatToSU2_one]
  ext1
  have ⟨h0, h1, h2, h3⟩ := icosianAB_step2_scalars
  simp only [quatToSU2_coe, h0, h1, h2, h3]

/-- Hurwitz integral/half-integral binary tetrahedral subgroup `2T ⊂ SU(2)` of order 24. -/
private def IsHurwitz24Tuple (p q r s : ℤ) : Prop :=
  p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 = 4 ∧
    ((Even p ∧ Even q ∧ Even r ∧ Even s) ∨ (Odd p ∧ Odd q ∧ Odd r ∧ Odd s))

private lemma int_sq_mod_four (a : ℤ) :
    (Even a → a ^ 2 % 4 = 0) ∧ (Odd a → a ^ 2 % 4 = 1) := by
  constructor
  · rintro ⟨k, rfl⟩
    have : (k + k) ^ 2 = 4 * (k ^ 2) := by ring
    omega
  · rintro ⟨k, rfl⟩
    have : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
    omega

private lemma isHurwitz24Tuple_of_sum_sq_eq_four {p q r s : ℤ}
    (h : p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 = 4) : IsHurwitz24Tuple p q r s := by
  refine ⟨h, ?_⟩
  have hp := int_sq_mod_four p
  have hq := int_sq_mod_four q
  have hr := int_sq_mod_four r
  have hs := int_sq_mod_four s
  rcases Int.even_or_odd p with hpe | hpo <;>
    rcases Int.even_or_odd q with hqe | hqo <;>
    rcases Int.even_or_odd r with hre | hro <;>
    rcases Int.even_or_odd s with hse | hso
  · exact Or.inl ⟨hpe, hqe, hre, hse⟩
  · exfalso; have := hp.1 hpe; have := hq.1 hqe; have := hr.1 hre; have := hs.2 hso; omega
  · exfalso; have := hp.1 hpe; have := hq.1 hqe; have := hr.2 hro; have := hs.1 hse; omega
  · exfalso; have := hp.1 hpe; have := hq.1 hqe; have := hr.2 hro; have := hs.2 hso; omega
  · exfalso; have := hp.1 hpe; have := hq.2 hqo; have := hr.1 hre; have := hs.1 hse; omega
  · exfalso; have := hp.1 hpe; have := hq.2 hqo; have := hr.1 hre; have := hs.2 hso; omega
  · exfalso; have := hp.1 hpe; have := hq.2 hqo; have := hr.2 hro; have := hs.1 hse; omega
  · exfalso; have := hp.1 hpe; have := hq.2 hqo; have := hr.2 hro; have := hs.2 hso; omega
  · exfalso; have := hp.2 hpo; have := hq.1 hqe; have := hr.1 hre; have := hs.1 hse; omega
  · exfalso; have := hp.2 hpo; have := hq.1 hqe; have := hr.1 hre; have := hs.2 hso; omega
  · exfalso; have := hp.2 hpo; have := hq.1 hqe; have := hr.2 hro; have := hs.1 hse; omega
  · exfalso; have := hp.2 hpo; have := hq.1 hqe; have := hr.2 hro; have := hs.2 hso; omega
  · exfalso; have := hp.2 hpo; have := hq.2 hqo; have := hr.1 hre; have := hs.1 hse; omega
  · exfalso; have := hp.2 hpo; have := hq.2 hqo; have := hr.1 hre; have := hs.2 hso; omega
  · exfalso; have := hp.2 hpo; have := hq.2 hqo; have := hr.2 hro; have := hs.1 hse; omega
  · exact Or.inr ⟨hpo, hqo, hro, hso⟩

private lemma isHurwitz24Tuple_mul {p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ : ℤ}
    (h₁ : IsHurwitz24Tuple p₁ q₁ r₁ s₁) (h₂ : IsHurwitz24Tuple p₂ q₂ r₂ s₂) :
    ∃ p₃ q₃ r₃ s₃ : ℤ,
      2 * p₃ = p₁ * p₂ - q₁ * q₂ - r₁ * r₂ - s₁ * s₂ ∧
      2 * q₃ = p₁ * q₂ + q₁ * p₂ + r₁ * s₂ - s₁ * r₂ ∧
      2 * r₃ = p₁ * r₂ - q₁ * s₂ + r₁ * p₂ + s₁ * q₂ ∧
      2 * s₃ = p₁ * s₂ + q₁ * r₂ - r₁ * q₂ + s₁ * p₂ ∧
      IsHurwitz24Tuple p₃ q₃ r₃ s₃ := by
  have hparity :
      Even (p₁ * p₂ - q₁ * q₂ - r₁ * r₂ - s₁ * s₂) ∧
      Even (p₁ * q₂ + q₁ * p₂ + r₁ * s₂ - s₁ * r₂) ∧
      Even (p₁ * r₂ - q₁ * s₂ + r₁ * p₂ + s₁ * q₂) ∧
      Even (p₁ * s₂ + q₁ * r₂ - r₁ * q₂ + s₁ * p₂) := by
    rcases h₁.2 with ⟨⟨a₁, rfl⟩, ⟨b₁, rfl⟩, ⟨c₁, rfl⟩, ⟨d₁, rfl⟩⟩ |
      ⟨⟨a₁, rfl⟩, ⟨b₁, rfl⟩, ⟨c₁, rfl⟩, ⟨d₁, rfl⟩⟩ <;>
      rcases h₂.2 with ⟨⟨a₂, rfl⟩, ⟨b₂, rfl⟩, ⟨c₂, rfl⟩, ⟨d₂, rfl⟩⟩ |
        ⟨⟨a₂, rfl⟩, ⟨b₂, rfl⟩, ⟨c₂, rfl⟩, ⟨d₂, rfl⟩⟩
    · exact ⟨⟨(a₁ + a₁) * a₂ - (b₁ + b₁) * b₂ - (c₁ + c₁) * c₂ - (d₁ + d₁) * d₂, by ring⟩,
        ⟨(a₁ + a₁) * b₂ + (b₁ + b₁) * a₂ + (c₁ + c₁) * d₂ - (d₁ + d₁) * c₂, by ring⟩,
        ⟨(a₁ + a₁) * c₂ - (b₁ + b₁) * d₂ + (c₁ + c₁) * a₂ + (d₁ + d₁) * b₂, by ring⟩,
        ⟨(a₁ + a₁) * d₂ + (b₁ + b₁) * c₂ - (c₁ + c₁) * b₂ + (d₁ + d₁) * a₂, by ring⟩⟩
    · exact ⟨⟨a₁ * (2 * a₂ + 1) - b₁ * (2 * b₂ + 1) - c₁ * (2 * c₂ + 1) - d₁ * (2 * d₂ + 1), by ring⟩,
        ⟨a₁ * (2 * b₂ + 1) + b₁ * (2 * a₂ + 1) + c₁ * (2 * d₂ + 1) - d₁ * (2 * c₂ + 1), by ring⟩,
        ⟨a₁ * (2 * c₂ + 1) - b₁ * (2 * d₂ + 1) + c₁ * (2 * a₂ + 1) + d₁ * (2 * b₂ + 1), by ring⟩,
        ⟨a₁ * (2 * d₂ + 1) + b₁ * (2 * c₂ + 1) - c₁ * (2 * b₂ + 1) + d₁ * (2 * a₂ + 1), by ring⟩⟩
    · exact ⟨⟨(2 * a₁ + 1) * a₂ - (2 * b₁ + 1) * b₂ - (2 * c₁ + 1) * c₂ - (2 * d₁ + 1) * d₂, by ring⟩,
        ⟨(2 * a₁ + 1) * b₂ + (2 * b₁ + 1) * a₂ + (2 * c₁ + 1) * d₂ - (2 * d₁ + 1) * c₂, by ring⟩,
        ⟨(2 * a₁ + 1) * c₂ - (2 * b₁ + 1) * d₂ + (2 * c₁ + 1) * a₂ + (2 * d₁ + 1) * b₂, by ring⟩,
        ⟨(2 * a₁ + 1) * d₂ + (2 * b₁ + 1) * c₂ - (2 * c₁ + 1) * b₂ + (2 * d₁ + 1) * a₂, by ring⟩⟩
    · exact ⟨⟨2 * a₁ * a₂ + a₁ + a₂ - (2 * b₁ * b₂ + b₁ + b₂) - (2 * c₁ * c₂ + c₁ + c₂) -
          (2 * d₁ * d₂ + d₁ + d₂) - 1, by ring⟩,
        ⟨2 * a₁ * b₂ + a₁ + b₂ + (2 * b₁ * a₂ + b₁ + a₂) + (2 * c₁ * d₂ + c₁ + d₂) -
          (2 * d₁ * c₂ + d₁ + c₂) + 1, by ring⟩,
        ⟨2 * a₁ * c₂ + a₁ + c₂ - (2 * b₁ * d₂ + b₁ + d₂) + (2 * c₁ * a₂ + c₁ + a₂) +
          (2 * d₁ * b₂ + d₁ + b₂) + 1, by ring⟩,
        ⟨2 * a₁ * d₂ + a₁ + d₂ + (2 * b₁ * c₂ + b₁ + c₂) - (2 * c₁ * b₂ + c₁ + b₂) +
          (2 * d₁ * a₂ + d₁ + a₂) + 1, by ring⟩⟩
  obtain ⟨p₃, hp3⟩ := hparity.1
  obtain ⟨q₃, hq3⟩ := hparity.2.1
  obtain ⟨r₃, hr3⟩ := hparity.2.2.1
  obtain ⟨s₃, hs3⟩ := hparity.2.2.2
  have hp3' : 2 * p₃ = p₁ * p₂ - q₁ * q₂ - r₁ * r₂ - s₁ * s₂ := by omega
  have hq3' : 2 * q₃ = p₁ * q₂ + q₁ * p₂ + r₁ * s₂ - s₁ * r₂ := by omega
  have hr3' : 2 * r₃ = p₁ * r₂ - q₁ * s₂ + r₁ * p₂ + s₁ * q₂ := by omega
  have hs3' : 2 * s₃ = p₁ * s₂ + q₁ * r₂ - r₁ * q₂ + s₁ * p₂ := by omega
  have hsum : p₃ ^ 2 + q₃ ^ 2 + r₃ ^ 2 + s₃ ^ 2 = 4 := by
    have heuler :
        (2 * p₃) ^ 2 + (2 * q₃) ^ 2 + (2 * r₃) ^ 2 + (2 * s₃) ^ 2 =
        (p₁ ^ 2 + q₁ ^ 2 + r₁ ^ 2 + s₁ ^ 2) * (p₂ ^ 2 + q₂ ^ 2 + r₂ ^ 2 + s₂ ^ 2) := by
      rw [hp3', hq3', hr3', hs3']
      ring
    rw [h₁.1, h₂.1] at heuler
    linarith
  exact ⟨p₃, q₃, r₃, s₃, hp3', hq3', hr3', hs3', isHurwitz24Tuple_of_sum_sq_eq_four hsum⟩

private lemma hurwitz_qMul_div_two {p₁ q₁ r₁ s₁ p₂ q₂ r₂ s₂ p₃ q₃ r₃ s₃ : ℤ}
    (hp3 : 2 * p₃ = p₁ * p₂ - q₁ * q₂ - r₁ * r₂ - s₁ * s₂)
    (hq3 : 2 * q₃ = p₁ * q₂ + q₁ * p₂ + r₁ * s₂ - s₁ * r₂)
    (hr3 : 2 * r₃ = p₁ * r₂ - q₁ * s₂ + r₁ * p₂ + s₁ * q₂)
    (hs3 : 2 * s₃ = p₁ * s₂ + q₁ * r₂ - r₁ * q₂ + s₁ * p₂) :
    qMul0 (p₁ / 2 : ℝ) (q₁ / 2) (r₁ / 2) (s₁ / 2) (p₂ / 2) (q₂ / 2) (r₂ / 2) (s₂ / 2) = p₃ / 2 ∧
    qMul1 (p₁ / 2 : ℝ) (q₁ / 2) (r₁ / 2) (s₁ / 2) (p₂ / 2) (q₂ / 2) (r₂ / 2) (s₂ / 2) = q₃ / 2 ∧
    qMul2 (p₁ / 2 : ℝ) (q₁ / 2) (r₁ / 2) (s₁ / 2) (p₂ / 2) (q₂ / 2) (r₂ / 2) (s₂ / 2) = r₃ / 2 ∧
    qMul3 (p₁ / 2 : ℝ) (q₁ / 2) (r₁ / 2) (s₁ / 2) (p₂ / 2) (q₂ / 2) (r₂ / 2) (s₂ / 2) = s₃ / 2 := by
  have hp3r : (2 * p₃ : ℝ) = p₁ * p₂ - q₁ * q₂ - r₁ * r₂ - s₁ * s₂ := by exact_mod_cast hp3
  have hq3r : (2 * q₃ : ℝ) = p₁ * q₂ + q₁ * p₂ + r₁ * s₂ - s₁ * r₂ := by exact_mod_cast hq3
  have hr3r : (2 * r₃ : ℝ) = p₁ * r₂ - q₁ * s₂ + r₁ * p₂ + s₁ * q₂ := by exact_mod_cast hr3
  have hs3r : (2 * s₃ : ℝ) = p₁ * s₂ + q₁ * r₂ - r₁ * q₂ + s₁ * p₂ := by exact_mod_cast hs3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [qMul0, qMul1, qMul2, qMul3] <;> linarith

private lemma isHurwitz24Tuple_neg_im {p q r s : ℤ} (h : IsHurwitz24Tuple p q r s) :
    IsHurwitz24Tuple p (-q) (-r) (-s) := by
  apply isHurwitz24Tuple_of_sum_sq_eq_four
  have hq : (-q) ^ 2 = q ^ 2 := by ring
  have hr : (-r) ^ 2 = r ^ 2 := by ring
  have hs : (-s) ^ 2 = s ^ 2 := by ring
  linarith [h.1, hq, hr, hs]

private def hurwitz24Subgroup : Subgroup SU2 where
  carrier := { g : SU2 | ∃ p q r s : ℤ, ∃ h : IsHurwitz24Tuple p q r s,
    g = quatToSU2 (p / 2 : ℝ) (q / 2 : ℝ) (r / 2 : ℝ) (s / 2 : ℝ)
      (hurwitz_norm_sq_scalar p q r s (by exact_mod_cast h.1)) }
  one_mem' := by
    refine ⟨2, 0, 0, 0, isHurwitz24Tuple_of_sum_sq_eq_four (by norm_num), ?_⟩
    ext1
    apply ext_mat2C <;> simp [quatToMat]
  mul_mem' := by
    rintro x y ⟨p₁, q₁, r₁, s₁, h₁, rfl⟩ ⟨p₂, q₂, r₂, s₂, h₂, rfl⟩
    obtain ⟨p₃, q₃, r₃, s₃, hp3, hq3, hr3, hs3, h₃⟩ := isHurwitz24Tuple_mul h₁ h₂
    refine ⟨p₃, q₃, r₃, s₃, h₃, ?_⟩
    rw [quatToSU2_mul]
    ext1
    obtain ⟨hc0, hc1, hc2, hc3⟩ := hurwitz_qMul_div_two hp3 hq3 hr3 hs3
    simp only [quatToSU2_coe, hc0, hc1, hc2, hc3]
  inv_mem' := by
    rintro x ⟨p, q, r, s, h, rfl⟩
    refine ⟨p, -q, -r, -s, isHurwitz24Tuple_neg_im h, ?_⟩
    rw [quatToSU2_inv]
    apply quatToSU2_eq_of_eq rfl <;> simp only [Int.cast_neg, neg_div]

private lemma negOneSU2_mem_hurwitz24 : negOneSU2 ∈ hurwitz24Subgroup := by
  refine ⟨-2, 0, 0, 0, isHurwitz24Tuple_of_sum_sq_eq_four (by norm_num), ?_⟩
  apply quatToSU2_eq_of_eq <;> norm_num

private lemma icosianGenB_mem_hurwitz24 : icosianGenB ∈ hurwitz24Subgroup := by
  refine ⟨0, 0, 2, 0, isHurwitz24Tuple_of_sum_sq_eq_four (by norm_num), ?_⟩
  apply quatToSU2_eq_of_eq <;> norm_num

private lemma hurwitzHalf_mem_hurwitz24 {p q r s : ℤ} (h : p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 = 4) :
    quatToSU2 (p / 2 : ℝ) (q / 2 : ℝ) (r / 2 : ℝ) (s / 2 : ℝ)
      (hurwitz_norm_sq_scalar p q r s (by exact_mod_cast h)) ∈ hurwitz24Subgroup :=
  ⟨p, q, r, s, isHurwitz24Tuple_of_sum_sq_eq_four h, rfl⟩

/-- Klein's base octahedron (the six coordinate axes `{±i, ±j, ±k}` of a cube). -/
def baseOctahedronSet : Set Mat2C :=
  { quatImToMat 1 0 0, quatImToMat (-1) 0 0,
    quatImToMat 0 1 0, quatImToMat 0 (-1) 0,
    quatImToMat 0 0 1, quatImToMat 0 0 (-1) }

private lemma signed_unit_axis_sq_dichotomy (u v w : ℝ)
    (hu : u = 0) (hv : v ^ 2 + w ^ 2 = 1) (hvw : v * w = 0) :
    (u = 0 ∧ v = 1 ∧ w = 0) ∨ (u = 0 ∧ v = -1 ∧ w = 0) ∨
    (u = 0 ∧ v = 0 ∧ w = 1) ∨ (u = 0 ∧ v = 0 ∧ w = -1) := by
  rcases mul_eq_zero.mp hvw with rfl | rfl
  · rw [zero_pow (by norm_num), zero_add, sq_eq_one_iff] at hv
    rcases hv with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨hu, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hu, rfl, rfl⟩))
  · rw [zero_pow (by norm_num), add_zero, sq_eq_one_iff] at hv
    rcases hv with rfl | rfl
    · exact Or.inl ⟨hu, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨hu, rfl, rfl⟩)

private lemma int_sum_sq_one_cases (a b c d : ℤ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    (a ^ 2 = 1 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨
    (a = 0 ∧ b ^ 2 = 1 ∧ c = 0 ∧ d = 0) ∨
    (a = 0 ∧ b = 0 ∧ c ^ 2 = 1 ∧ d = 0) ∨
    (a = 0 ∧ b = 0 ∧ c = 0 ∧ d ^ 2 = 1) := by
  have ha0 : 0 ≤ a ^ 2 := sq_nonneg a
  have hb0 : 0 ≤ b ^ 2 := sq_nonneg b
  have hc0 : 0 ≤ c ^ 2 := sq_nonneg c
  have hd0 : 0 ≤ d ^ 2 := sq_nonneg d
  rcases eq_or_lt_of_le ha0 with ha | ha
  · have ha' : a ^ 2 = 0 := ha.symm
    rcases eq_or_lt_of_le hb0 with hb | hb
    · have hb' : b ^ 2 = 0 := hb.symm
      rcases eq_or_lt_of_le hc0 with hc | hc
      · have hc' : c ^ 2 = 0 := hc.symm
        have hd1 : d ^ 2 = 1 := by linear_combination h - ha' - hb' - hc'
        exact Or.inr (Or.inr (Or.inr ⟨sq_eq_zero_iff.mp ha', sq_eq_zero_iff.mp hb',
          sq_eq_zero_iff.mp hc', hd1⟩))
      · have hc1 : c ^ 2 = 1 := by omega
        have hd1 : d ^ 2 = 0 := by omega
        exact Or.inr (Or.inr (Or.inl ⟨sq_eq_zero_iff.mp ha', sq_eq_zero_iff.mp hb',
          hc1, sq_eq_zero_iff.mp hd1⟩))
    · have hb1 : b ^ 2 = 1 := by omega
      have hc1 : c ^ 2 = 0 := by omega
      have hd1 : d ^ 2 = 0 := by omega
      exact Or.inr (Or.inl ⟨sq_eq_zero_iff.mp ha', hb1, sq_eq_zero_iff.mp hc1, sq_eq_zero_iff.mp hd1⟩)
  · have ha1 : a ^ 2 = 1 := by omega
    have hb1 : b ^ 2 = 0 := by omega
    have hc1 : c ^ 2 = 0 := by omega
    have hd1 : d ^ 2 = 0 := by omega
    exact Or.inl ⟨ha1, sq_eq_zero_iff.mp hb1, sq_eq_zero_iff.mp hc1, sq_eq_zero_iff.mp hd1⟩

private lemma odd_int_sq_ge_one {m : ℤ} (hm : Odd m) : 1 ≤ m ^ 2 := by
  rcases hm with ⟨k, rfl⟩
  have hk : 0 ≤ k * (k + 1) := by
    rcases le_total 0 k with h | h
    · positivity
    · rcases eq_or_lt_of_le h with rfl | hneg
      · simp
      · exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt hneg) (by omega)
  nlinarith [hk]

private lemma hurwitz_conj_im_mem_base (p q r s : ℤ) (h : IsHurwitz24Tuple p q r s)
    (x y z : ℝ) (hxyz : (x = 1 ∧ y = 0 ∧ z = 0) ∨ (x = -1 ∧ y = 0 ∧ z = 0) ∨
      (x = 0 ∧ y = 1 ∧ z = 0) ∨ (x = 0 ∧ y = -1 ∧ z = 0) ∨
      (x = 0 ∧ y = 0 ∧ z = 1) ∨ (x = 0 ∧ y = 0 ∧ z = -1)) :
    let u := qConjX (p / 2 : ℝ) (q / 2 : ℝ) (r / 2 : ℝ) (s / 2 : ℝ) x y z
    let v := qConjY (p / 2 : ℝ) (q / 2 : ℝ) (r / 2 : ℝ) (s / 2 : ℝ) x y z
    let w := qConjZ (p / 2 : ℝ) (q / 2 : ℝ) (r / 2 : ℝ) (s / 2 : ℝ) x y z
    (u = 1 ∧ v = 0 ∧ w = 0) ∨ (u = -1 ∧ v = 0 ∧ w = 0) ∨
    (u = 0 ∧ v = 1 ∧ w = 0) ∨ (u = 0 ∧ v = -1 ∧ w = 0) ∨
    (u = 0 ∧ v = 0 ∧ w = 1) ∨ (u = 0 ∧ v = 0 ∧ w = -1) := by
  dsimp only
  rcases h.2 with ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩, ⟨d, rfl⟩⟩ | ⟨hp, hq, hr, hs⟩
  · have hsum : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 := by linarith [h.1]
    have ha : ((a + a : ℤ) : ℝ) / 2 = (a : ℝ) := by push_cast; ring
    have hb : ((b + b : ℤ) : ℝ) / 2 = (b : ℝ) := by push_cast; ring
    have hc : ((c + c : ℤ) : ℝ) / 2 = (c : ℝ) := by push_cast; ring
    have hd : ((d + d : ℤ) : ℝ) / 2 = (d : ℝ) := by push_cast; ring
    rw [ha, hb, hc, hd]
    rcases int_sum_sq_one_cases a b c d hsum with
      ⟨hsq, rfl, rfl, rfl⟩ | ⟨rfl, hsq, rfl, rfl⟩ | ⟨rfl, rfl, hsq, rfl⟩ | ⟨rfl, rfl, rfl, hsq⟩ <;>
      rcases sq_eq_one_iff.mp hsq with hval | hval <;> rw [hval] <;>
      rcases hxyz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [qConjX, qConjY, qConjZ]
  · have hp1 := odd_int_sq_ge_one hp
    have hq1 := odd_int_sq_ge_one hq
    have hr1 := odd_int_sq_ge_one hr
    have hs1 := odd_int_sq_ge_one hs
    have hsum4 : p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 = 4 := h.1
    have hp_sq_int : p ^ 2 = 1 := by nlinarith [hsum4, hq1, hr1, hs1]
    have hq_sq_int : q ^ 2 = 1 := by nlinarith [hsum4, hp1, hr1, hs1]
    have hr_sq_int : r ^ 2 = 1 := by nlinarith [hsum4, hp1, hq1, hs1]
    have hs_sq_int : s ^ 2 = 1 := by nlinarith [hsum4, hp1, hq1, hr1]
    rcases sq_eq_one_iff.mp hp_sq_int with hpval | hpval <;>
      rcases sq_eq_one_iff.mp hq_sq_int with hqval | hqval <;>
      rcases sq_eq_one_iff.mp hr_sq_int with hrval | hrval <;>
      rcases sq_eq_one_iff.mp hs_sq_int with hsval | hsval <;>
      rcases hxyz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      norm_num [qConjX, qConjY, qConjZ, hpval, hqval, hrval, hsval]

private lemma hurwitz_conj_base_subset {t : SU2} (ht : t ∈ hurwitz24Subgroup) :
    conjMat t '' baseOctahedronSet ⊆ baseOctahedronSet := by
  rintro _ ⟨X, hX, rfl⟩
  rcases ht with ⟨p, q, r, s, h, rfl⟩
  have hx : ∃ x y z : ℝ, X = quatImToMat x y z ∧
      ((x = 1 ∧ y = 0 ∧ z = 0) ∨ (x = -1 ∧ y = 0 ∧ z = 0) ∨
       (x = 0 ∧ y = 1 ∧ z = 0) ∨ (x = 0 ∧ y = -1 ∧ z = 0) ∨
       (x = 0 ∧ y = 0 ∧ z = 1) ∨ (x = 0 ∧ y = 0 ∧ z = -1)) := by
    simp only [baseOctahedronSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, 0, 0, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨-1, 0, 0, rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
    · exact ⟨0, 1, 0, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩
    · exact ⟨0, -1, 0, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))⟩
    · exact ⟨0, 0, 1, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))⟩
    · exact ⟨0, 0, -1, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))⟩
  rcases hx with ⟨x, y, z, rfl, hxyz⟩
  rw [conjMat_quatToSU2_im]
  rcases hurwitz_conj_im_mem_base p q r s h x y z hxyz with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    simp [baseOctahedronSet, h1, h2, h3]

private lemma hurwitz_conj_base_eq {t : SU2} (ht : t ∈ hurwitz24Subgroup) :
    conjMat t '' baseOctahedronSet = baseOctahedronSet := by
  refine Set.Subset.antisymm (hurwitz_conj_base_subset ht) ?_
  intro X hX
  have htinv := hurwitz_conj_base_subset (hurwitz24Subgroup.inv_mem ht)
  have hY : conjMat t⁻¹ X ∈ baseOctahedronSet := htinv ⟨X, hX, rfl⟩
  refine ⟨conjMat t⁻¹ X, hY, ?_⟩
  rw [← conjMat_mul, mul_inv_cancel, conjMat_one]

/-- Klein's five inscribed octahedron/cube frames `C₀, …, C₄` rotated by `icosianGenA^k`. -/
def cubeFrame (m : Fin 5) : Set Mat2C :=
  conjMat (icosianGenA ^ m.val) '' baseOctahedronSet

lemma cubeFrame_zero : cubeFrame 0 = baseOctahedronSet := by
  simp [cubeFrame, conjMat_one]

private def permA5 : Equiv.Perm (Fin 5) := Fin.cycleRange 4
private def permB5 : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 3 4

private lemma permA5_apply (m : Fin 5) : permA5 m = ⟨(m.val + 1) % 5, Nat.mod_lt _ (by norm_num)⟩ := by
  fin_cases m <;> decide

private lemma permB5_vals :
    permB5 0 = 0 ∧ permB5 1 = 2 ∧ permB5 2 = 1 ∧ permB5 3 = 4 ∧ permB5 4 = 3 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

private lemma conjMat_A_cubeFrame (m : Fin 5) :
    conjMat icosianGenA '' cubeFrame m = cubeFrame (permA5 m) := by
  have hpow : conjMat icosianGenA '' cubeFrame m =
      conjMat (icosianGenA ^ (m.val + 1)) '' baseOctahedronSet := by
    rw [cubeFrame, ← Set.image_comp]
    congr 1
    funext X
    change conjMat icosianGenA (conjMat (icosianGenA ^ m.val) X) =
      conjMat (icosianGenA ^ (m.val + 1)) X
    rw [← conjMat_mul, ← pow_succ']
  rw [hpow]
  fin_cases m
  · rfl
  · rfl
  · rfl
  · rfl
  · change conjMat (icosianGenA ^ (4 + 1)) '' baseOctahedronSet = cubeFrame (permA5 4)
    rw [show 4 + 1 = 5 by norm_num, icosianGenA_pow_five,
      show permA5 4 = 0 by decide, cubeFrame_zero]
    ext Y
    simp [Set.mem_image, conjMat_negOne]

private lemma icosian_BA_coset_factor (m : Fin 5) :
    ∃ t : SU2, t ∈ hurwitz24Subgroup ∧ icosianGenB * icosianGenA ^ m.val =
      icosianGenA ^ (permB5 m).val * t := by
  fin_cases m
  · refine ⟨icosianGenB, icosianGenB_mem_hurwitz24, by simp [permB5_vals]⟩
  · refine ⟨quatToSU2 ((1 : ℤ) / 2 : ℝ) ((1 : ℤ) / 2 : ℝ) ((1 : ℤ) / 2 : ℝ) ((-1 : ℤ) / 2 : ℝ)
        (by norm_num),
      hurwitzHalf_mem_hurwitz24 (p := 1) (q := 1) (r := 1) (s := -1) (by norm_num), ?_⟩
    change icosianGenB * icosianGenA ^ 1 = icosianGenA ^ 2 * _
    rw [pow_one, icosianGenA_pow_two, icosianGenB, su2QuatJ, icosianGenA, icosianGenA2,
      quatToSU2_mul, quatToSU2_mul]
    have hc := icosian_BA_coset_scalars.1
    apply quatToSU2_eq_of_eq <;> push_cast <;> [exact hc.1.symm; exact hc.2.1.symm;
      exact hc.2.2.1.symm; exact hc.2.2.2.symm]
  · refine ⟨quatToSU2 ((-1 : ℤ) / 2 : ℝ) ((1 : ℤ) / 2 : ℝ) ((1 : ℤ) / 2 : ℝ) ((-1 : ℤ) / 2 : ℝ)
        (by norm_num),
      hurwitzHalf_mem_hurwitz24 (p := -1) (q := 1) (r := 1) (s := -1) (by norm_num), ?_⟩
    change icosianGenB * icosianGenA ^ 2 = icosianGenA ^ 1 * _
    rw [icosianGenA_pow_two, pow_one, icosianGenB, su2QuatJ, icosianGenA2, icosianGenA,
      quatToSU2_mul, quatToSU2_mul]
    have hc := icosian_BA_coset_scalars.2.1
    apply quatToSU2_eq_of_eq <;> push_cast <;> [exact hc.1.symm; exact hc.2.1.symm;
      exact hc.2.2.1.symm; exact hc.2.2.2.symm]
  · refine ⟨quatToSU2 ((1 : ℤ) / 2 : ℝ) ((1 : ℤ) / 2 : ℝ) ((1 : ℤ) / 2 : ℝ) ((1 : ℤ) / 2 : ℝ)
        (by norm_num),
      hurwitzHalf_mem_hurwitz24 (p := 1) (q := 1) (r := 1) (s := 1) (by norm_num), ?_⟩
    change icosianGenB * icosianGenA ^ 3 = icosianGenA ^ 4 * _
    rw [icosianGenA_pow_three, icosianGenA_pow_four, icosianGenB, su2QuatJ, icosianGenA3,
      icosianGenA4, quatToSU2_mul, quatToSU2_mul]
    have hc := icosian_BA_coset_scalars.2.2.1
    apply quatToSU2_eq_of_eq <;> push_cast <;> [exact hc.1.symm; exact hc.2.1.symm;
      exact hc.2.2.1.symm; exact hc.2.2.2.symm]
  · refine ⟨quatToSU2 ((-1 : ℤ) / 2 : ℝ) ((1 : ℤ) / 2 : ℝ) ((1 : ℤ) / 2 : ℝ) ((1 : ℤ) / 2 : ℝ)
        (by norm_num),
      hurwitzHalf_mem_hurwitz24 (p := -1) (q := 1) (r := 1) (s := 1) (by norm_num), ?_⟩
    change icosianGenB * icosianGenA ^ 4 = icosianGenA ^ 3 * _
    rw [icosianGenA_pow_four, icosianGenA_pow_three, icosianGenB, su2QuatJ, icosianGenA4,
      icosianGenA3, quatToSU2_mul, quatToSU2_mul]
    have hc := icosian_BA_coset_scalars.2.2.2
    apply quatToSU2_eq_of_eq <;> push_cast <;> [exact hc.1.symm; exact hc.2.1.symm;
      exact hc.2.2.1.symm; exact hc.2.2.2.symm]

private lemma conjMat_B_cubeFrame (m : Fin 5) :
    conjMat icosianGenB '' cubeFrame m = cubeFrame (permB5 m) := by
  obtain ⟨t, ht, hBA⟩ := icosian_BA_coset_factor m
  rw [cubeFrame, ← Set.image_comp]
  have hcomp : conjMat icosianGenB ∘ conjMat (icosianGenA ^ m.val) =
      conjMat (icosianGenA ^ (permB5 m).val) ∘ conjMat t := by
    funext X
    change conjMat icosianGenB (conjMat (icosianGenA ^ m.val) X) =
      conjMat (icosianGenA ^ (permB5 m).val) (conjMat t X)
    rw [← conjMat_mul, ← conjMat_mul, hBA]
  rw [hcomp, Set.image_comp, hurwitz_conj_base_eq ht]
  rfl

private def icosahedralCosetUnion : Set SU2 :=
  { g : SU2 | ∃ (m : Fin 5) (t : SU2), t ∈ hurwitz24Subgroup ∧ g = icosianGenA ^ m.val * t }

def binaryIcosahedralGroup : Subgroup SU2 :=
  Subgroup.closure {icosianGenA, icosianGenB}

private lemma icosianGenA_inv_eq : icosianGenA⁻¹ = icosianGenA ^ 4 * negOneSU2 := by
  apply inv_eq_of_mul_eq_one_right
  calc
    icosianGenA * (icosianGenA ^ 4 * negOneSU2)
        = (icosianGenA * icosianGenA ^ 4) * negOneSU2 := (mul_assoc _ _ _).symm
    _ = icosianGenA ^ 5 * negOneSU2 := by rw [← pow_succ']
    _ = negOneSU2 * negOneSU2 := by rw [icosianGenA_pow_five]
    _ = 1 := negOneSU2_sq

private lemma icosianGenB_inv_eq : icosianGenB⁻¹ = icosianGenB * negOneSU2 := by
  apply inv_eq_of_mul_eq_one_right
  calc
    icosianGenB * (icosianGenB * negOneSU2) = icosianGenB ^ 2 * negOneSU2 := by rw [sq, mul_assoc]
    _ = negOneSU2 * negOneSU2 := by rw [icosianGenB_sq]
    _ = 1 := negOneSU2_sq

private lemma icosianGenA_mul_coset {g : SU2} (hg : g ∈ icosahedralCosetUnion) :
    icosianGenA * g ∈ icosahedralCosetUnion := by
  rcases hg with ⟨m, t, ht, rfl⟩
  fin_cases m
  · exact ⟨1, t, ht, by simp⟩
  · exact ⟨2, t, ht, by simp [pow_succ', mul_assoc]⟩
  · exact ⟨3, t, ht, by simp [pow_succ', mul_assoc]⟩
  · exact ⟨4, t, ht, by simp [pow_succ', mul_assoc]⟩
  · refine ⟨0, negOneSU2 * t, hurwitz24Subgroup.mul_mem negOneSU2_mem_hurwitz24 ht, ?_⟩
    simp only [Fin.val_zero, pow_zero, one_mul]
    calc
      icosianGenA * (icosianGenA ^ (4 : Fin 5).val * t)
          = (icosianGenA * icosianGenA ^ 4) * t := (mul_assoc _ _ _).symm
      _ = icosianGenA ^ 5 * t := by rw [← pow_succ']
      _ = negOneSU2 * t := by rw [icosianGenA_pow_five]

private lemma icosianGenB_mul_coset {g : SU2} (hg : g ∈ icosahedralCosetUnion) :
    icosianGenB * g ∈ icosahedralCosetUnion := by
  rcases hg with ⟨m, t, ht, rfl⟩
  obtain ⟨u, hu, hBA⟩ := icosian_BA_coset_factor m
  refine ⟨permB5 m, u * t, hurwitz24Subgroup.mul_mem hu ht, ?_⟩
  calc
    icosianGenB * (icosianGenA ^ m.val * t)
        = (icosianGenB * icosianGenA ^ m.val) * t := (mul_assoc _ _ _).symm
    _ = (icosianGenA ^ (permB5 m).val * u) * t := by rw [hBA]
    _ = icosianGenA ^ (permB5 m).val * (u * t) := mul_assoc _ _ _

private lemma binaryIcosahedralGroup_subset_cosetUnion :
    (binaryIcosahedralGroup : Set SU2) ⊆ icosahedralCosetUnion := by
  let stab : Subgroup SU2 :=
    { carrier := { x : SU2 | ∀ g ∈ icosahedralCosetUnion,
        x * g ∈ icosahedralCosetUnion ∧ x⁻¹ * g ∈ icosahedralCosetUnion }
      one_mem' := fun g hg => by simpa using hg
      mul_mem' := by
        intro x y hx hy g hg
        refine ⟨?_, ?_⟩
        · have hy1 := (hy g hg).1
          rw [mul_assoc]
          exact (hx (y * g) hy1).1
        · rw [_root_.mul_inv_rev, mul_assoc]
          have hx2 := (hx g hg).2
          exact (hy (x⁻¹ * g) hx2).2
      inv_mem' := by
        intro x hx g hg
        have h := hx g hg
        exact ⟨by simpa using h.2, by simpa [inv_inv] using h.1⟩ }
  have hA : icosianGenA ∈ stab := by
    change ∀ g ∈ icosahedralCosetUnion,
      icosianGenA * g ∈ icosahedralCosetUnion ∧ icosianGenA⁻¹ * g ∈ icosahedralCosetUnion
    intro g hg
    refine ⟨icosianGenA_mul_coset hg, ?_⟩
    rw [icosianGenA_inv_eq]
    rcases hg with ⟨k, s, hs, rfl⟩
    have hm : icosianGenA ^ 4 * negOneSU2 * (icosianGenA ^ k.val * s) =
        icosianGenA * (icosianGenA * (icosianGenA * (icosianGenA * (icosianGenA ^ k.val * (negOneSU2 * s))))) := by
      simp only [pow_succ', pow_zero, one_mul, mul_assoc, negOneSU2_mul]
    rw [hm]
    exact icosianGenA_mul_coset (icosianGenA_mul_coset (icosianGenA_mul_coset
      (icosianGenA_mul_coset ⟨k, negOneSU2 * s, hurwitz24Subgroup.mul_mem negOneSU2_mem_hurwitz24 hs, rfl⟩)))
  have hB : icosianGenB ∈ stab := by
    change ∀ g ∈ icosahedralCosetUnion,
      icosianGenB * g ∈ icosahedralCosetUnion ∧ icosianGenB⁻¹ * g ∈ icosahedralCosetUnion
    intro g hg
    refine ⟨icosianGenB_mul_coset hg, ?_⟩
    rw [icosianGenB_inv_eq]
    rcases hg with ⟨k, s, hs, rfl⟩
    have hm : icosianGenB * negOneSU2 * (icosianGenA ^ k.val * s) =
        icosianGenB * (icosianGenA ^ k.val * (negOneSU2 * s)) := by
      simp only [mul_assoc, negOneSU2_mul]
    rw [hm]
    exact icosianGenB_mul_coset ⟨k, negOneSU2 * s, hurwitz24Subgroup.mul_mem negOneSU2_mem_hurwitz24 hs, rfl⟩
  have hle : binaryIcosahedralGroup ≤ stab := by
    rw [binaryIcosahedralGroup, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hA
    · exact hB
  intro g hg
  have hmem : ∀ s ∈ icosahedralCosetUnion,
      g * s ∈ icosahedralCosetUnion ∧ g⁻¹ * s ∈ icosahedralCosetUnion := hle hg
  have h1 := (hmem 1 ⟨0, 1, hurwitz24Subgroup.one_mem, by simp⟩).1
  simpa using h1

/-! ### Cube Frame Distinctness & Stabilizer Kernel Reduction -/

private lemma q_c1_axis1 :
    qConjX (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 1 0 0 = 1 / 2 ∧
    qConjY (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 1 0 0 = (Real.goldenRatio - 1) / 2 ∧
    qConjZ (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 1 0 0 = -Real.goldenRatio / 2 := by
  have hphi := Real.goldenRatio_sq
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [qConjX, qConjY, qConjZ]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]

private lemma q_c1_axis2 :
    qConjX (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 1 0 = (Real.goldenRatio - 1) / 2 ∧
    qConjY (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 1 0 = Real.goldenRatio / 2 ∧
    qConjZ (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 1 0 = 1 / 2 := by
  have hphi := Real.goldenRatio_sq
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [qConjX, qConjY, qConjZ]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]

private lemma q_c1_axis3 :
    qConjX (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 0 1 = Real.goldenRatio / 2 ∧
    qConjY (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 0 1 = -1 / 2 ∧
    qConjZ (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 0 1 = (Real.goldenRatio - 1) / 2 := by
  have hphi := Real.goldenRatio_sq
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [qConjX, qConjY, qConjZ]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]

private lemma q_c2_axis1 :
    qConjX ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 1 0 0 = (1 - Real.goldenRatio) / 2 ∧
    qConjY ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 1 0 0 = Real.goldenRatio / 2 ∧
    qConjZ ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 1 0 0 = -1 / 2 := by
  have hphi := Real.goldenRatio_sq
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [qConjX, qConjY, qConjZ]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]

private lemma q_c2_axis2 :
    qConjX ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 0 1 0 = Real.goldenRatio / 2 ∧
    qConjY ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 0 1 0 = 1 / 2 ∧
    qConjZ ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 0 1 0 = (Real.goldenRatio - 1) / 2 := by
  have hphi := Real.goldenRatio_sq
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [qConjX, qConjY, qConjZ]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]

private lemma q_c2_axis3 :
    qConjX ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 0 0 1 = 1 / 2 ∧
    qConjY ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 0 0 1 = (1 - Real.goldenRatio) / 2 ∧
    qConjZ ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 0 0 1 = -Real.goldenRatio / 2 := by
  have hphi := Real.goldenRatio_sq
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [qConjX, qConjY, qConjZ]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]

private lemma q_c3_axis1 :
    qConjX ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0 1 0 0 = (1 - Real.goldenRatio) / 2 ∧
    qConjY ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0 1 0 0 = Real.goldenRatio / 2 ∧
    qConjZ ((1 - Real.goldenRatio) / 2) (1 / 2) (Real.goldenRatio / 2) 0 1 0 0 = 1 / 2 := by
  have hphi := Real.goldenRatio_sq
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [qConjX, qConjY, qConjZ]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]

private lemma q_c4_axis1 :
    qConjX (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 1 0 0 = 1 / 2 ∧
    qConjY (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 1 0 0 = (Real.goldenRatio - 1) / 2 ∧
    qConjZ (-Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 1 0 0 = Real.goldenRatio / 2 := by
  have hphi := Real.goldenRatio_sq
  have hsqrt5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [qConjX, qConjY, qConjZ]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]
  · nlinarith [hphi, hsqrt5]

private lemma half_sub_goldenRatio_not_base_x
    (h0 : (1 - Real.goldenRatio) / 2 = 0 ∨
      (1 - Real.goldenRatio) / 2 = 1 ∨
      (1 - Real.goldenRatio) / 2 = -1) : False := by
  rcases h0 with h | h | h <;> linarith [Real.one_lt_goldenRatio, Real.goldenRatio_lt_two]

private lemma cubeFrame_ne_zero_of_pos {m : Fin 5} (hm : m ≠ 0) : cubeFrame m ≠ cubeFrame 0 := by
  intro heq
  rw [cubeFrame_zero] at heq
  have hmem : conjMat (icosianGenA ^ m.val) (quatImToMat 1 0 0) ∈ baseOctahedronSet := by
    rw [← heq]
    refine ⟨quatImToMat 1 0 0, ?_, rfl⟩
    simp [baseOctahedronSet]
  have hf : ∀ {x y z : ℝ}, quatImToMat x y z ∈ baseOctahedronSet → x = 0 ∨ x = 1 ∨ x = -1 := by
    intro x y z hxyz
    simp only [baseOctahedronSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hxyz
    rcases hxyz with h1 | h1 | h1 | h1 | h1 | h1 <;>
      obtain ⟨hx, _, _⟩ := quatImToMat_injective h1 <;>
      simp [hx]
  fin_cases m
  · exact hm rfl
  · simp only [pow_one, icosianGenA, conjMat_quatToSU2_im, q_c1_axis1] at hmem
    rcases hf hmem with h0 | h0 | h0 <;> norm_num at h0
  · simp only [icosianGenA_pow_two, icosianGenA2, conjMat_quatToSU2_im, q_c2_axis1] at hmem
    exact half_sub_goldenRatio_not_base_x (hf hmem)
  · simp only [icosianGenA_pow_three, icosianGenA3, conjMat_quatToSU2_im, q_c3_axis1] at hmem
    exact half_sub_goldenRatio_not_base_x (hf hmem)
  · simp only [icosianGenA_pow_four, icosianGenA4, conjMat_quatToSU2_im, q_c4_axis1] at hmem
    rcases hf hmem with h0 | h0 | h0 <;> norm_num at h0

private lemma conjMat_A_pow_cubeFrame (k : ℕ) (m : Fin 5) :
    conjMat (icosianGenA ^ k) '' cubeFrame m =
      cubeFrame ⟨(m.val + k) % 5, Nat.mod_lt _ (by norm_num)⟩ := by
  induction k generalizing m with
  | zero =>
    simp only [pow_zero, Nat.add_zero]
    have hidx : (⟨m.val % 5, Nat.mod_lt _ (by norm_num)⟩ : Fin 5) = m :=
      Fin.ext (Nat.mod_eq_of_lt m.isLt)
    rw [hidx]
    ext Y
    simp [Set.mem_image, conjMat_one]
  | succ k ih =>
    have hm : conjMat (icosianGenA ^ (k + 1)) =
        conjMat icosianGenA ∘ conjMat (icosianGenA ^ k) := by
      funext X
      change conjMat (icosianGenA ^ (k + 1)) X = conjMat icosianGenA (conjMat (icosianGenA ^ k) X)
      rw [pow_succ', conjMat_mul]
    rw [hm, Set.image_comp, ih m, conjMat_A_cubeFrame, permA5_apply]
    congr 1
    ext
    simp [Nat.add_assoc, Nat.mod_add_mod]

theorem cubeFrame_injective : Function.Injective cubeFrame := by
  intro m₁ m₂ h
  have hshift := congrArg (fun S : Set Mat2C => conjMat (icosianGenA ^ (5 - m₁.val)) '' S) h
  rw [conjMat_A_pow_cubeFrame, conjMat_A_pow_cubeFrame] at hshift
  have hzero : (⟨(m₁.val + (5 - m₁.val)) % 5, Nat.mod_lt _ (by norm_num)⟩ : Fin 5) = 0 := by
    ext
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
    have hle : m₁.val ≤ 5 := le_of_lt m₁.isLt
    omega
  rw [hzero] at hshift
  by_contra hne
  have hm_ne : (⟨(m₂.val + (5 - m₁.val)) % 5, Nat.mod_lt _ (by norm_num)⟩ : Fin 5) ≠ 0 := by
    intro h0
    have hval : (m₂.val + (5 - m₁.val)) % 5 = 0 := congrArg Fin.val h0
    apply hne
    ext
    omega
  exact cubeFrame_ne_zero_of_pos hm_ne hshift.symm

/-! ### Kernel of the 5-Cube Permutation Action & `alternatingGroup (Fin 5) ≃* icosahedralPSU2Subgroup` -/

private def IsC1Vec (x y z : ℝ) : Prop :=
  (x = 1 / 2 ∧ y = (Real.goldenRatio - 1) / 2 ∧ z = -Real.goldenRatio / 2) ∨
  (x = -1 / 2 ∧ y = -(Real.goldenRatio - 1) / 2 ∧ z = Real.goldenRatio / 2) ∨
  (x = (Real.goldenRatio - 1) / 2 ∧ y = Real.goldenRatio / 2 ∧ z = 1 / 2) ∨
  (x = -(Real.goldenRatio - 1) / 2 ∧ y = -Real.goldenRatio / 2 ∧ z = -1 / 2) ∨
  (x = Real.goldenRatio / 2 ∧ y = -1 / 2 ∧ z = (Real.goldenRatio - 1) / 2) ∨
  (x = -Real.goldenRatio / 2 ∧ y = 1 / 2 ∧ z = -(Real.goldenRatio - 1) / 2)

private def IsC2Vec (x y z : ℝ) : Prop :=
  (x = (1 - Real.goldenRatio) / 2 ∧ y = Real.goldenRatio / 2 ∧ z = -1 / 2) ∨
  (x = (Real.goldenRatio - 1) / 2 ∧ y = -Real.goldenRatio / 2 ∧ z = 1 / 2) ∨
  (x = Real.goldenRatio / 2 ∧ y = 1 / 2 ∧ z = (Real.goldenRatio - 1) / 2) ∨
  (x = -Real.goldenRatio / 2 ∧ y = -1 / 2 ∧ z = (1 - Real.goldenRatio) / 2) ∨
  (x = 1 / 2 ∧ y = (1 - Real.goldenRatio) / 2 ∧ z = -Real.goldenRatio / 2) ∨
  (x = -1 / 2 ∧ y = (Real.goldenRatio - 1) / 2 ∧ z = Real.goldenRatio / 2)

private lemma c1_conj_octahedron_isC1Vec {x y z u v w : ℝ}
    (hx1 : qConjX (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 u v w = x)
    (hy1 : qConjY (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 u v w = y)
    (hz1 : qConjZ (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 u v w = z)
    (huvw : (u = 1 ∧ v = 0 ∧ w = 0) ∨ (u = -1 ∧ v = 0 ∧ w = 0) ∨
      (u = 0 ∧ v = 1 ∧ w = 0) ∨ (u = 0 ∧ v = -1 ∧ w = 0) ∨
      (u = 0 ∧ v = 0 ∧ w = 1) ∨ (u = 0 ∧ v = 0 ∧ w = -1)) : IsC1Vec x y z := by
  rw [← hx1, ← hy1, ← hz1]
  rcases huvw with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · left; exact ⟨q_c1_axis1.1, q_c1_axis1.2.1, q_c1_axis1.2.2⟩
  · have hq0 : qConjX (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 (-1) 0 0 = -1 / 2 := by
      calc
        qConjX (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 (-1) 0 0 =
            -qConjX (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 1 0 0 := by
              simp [qConjX]
        _ = -1 / 2 := by rw [q_c1_axis1.1]; norm_num
    have hq1 : qConjY (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 (-1) 0 0 = -(Real.goldenRatio - 1) / 2 := by
      rw [qConjY_neg_x, q_c1_axis1.2.1]
      ring
    have hq2 : qConjZ (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 (-1) 0 0 = Real.goldenRatio / 2 := by
      rw [qConjZ_neg_x, q_c1_axis1.2.2]
      ring
    right; left; exact ⟨hq0, hq1, hq2⟩
  · right; right; left; exact ⟨q_c1_axis2.1, q_c1_axis2.2.1, q_c1_axis2.2.2⟩
  · have hq0 : qConjX (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 (-1) 0 = -(Real.goldenRatio - 1) / 2 := by
      rw [qConjX_neg_y, q_c1_axis2.1]
      ring
    have hq1 : qConjY (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 (-1) 0 = -Real.goldenRatio / 2 := by
      rw [qConjY_neg_y, q_c1_axis2.2.1]
      ring
    have hq2 : qConjZ (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 (-1) 0 = -1 / 2 := by
      rw [qConjZ_neg_y, q_c1_axis2.2.2]
      ring
    right; right; right; left; exact ⟨hq0, hq1, hq2⟩
  · right; right; right; right; left; exact ⟨q_c1_axis3.1, q_c1_axis3.2.1, q_c1_axis3.2.2⟩
  · have hq0 : qConjX (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 0 (-1) = -Real.goldenRatio / 2 := by
      rw [qConjX_neg_z, q_c1_axis3.1]
      ring
    have hq1 : qConjY (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 0 (-1) = 1 / 2 := by
      rw [qConjY_neg_z, q_c1_axis3.2.1]
      ring
    have hq2 : qConjZ (Real.goldenRatio / 2) ((Real.goldenRatio - 1) / 2) (1 / 2) 0 0 0 (-1) = -(Real.goldenRatio - 1) / 2 := by
      rw [qConjZ_neg_z, q_c1_axis3.2.2]
      ring
    right; right; right; right; right; exact ⟨hq0, hq1, hq2⟩

private lemma c2_conj_octahedron_isC2Vec {x y z u v w : ℝ}
    (hx1 : qConjX ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 u v w = x)
    (hy1 : qConjY ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 u v w = y)
    (hz1 : qConjZ ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 u v w = z)
    (huvw : (u = 1 ∧ v = 0 ∧ w = 0) ∨ (u = -1 ∧ v = 0 ∧ w = 0) ∨
      (u = 0 ∧ v = 1 ∧ w = 0) ∨ (u = 0 ∧ v = -1 ∧ w = 0) ∨
      (u = 0 ∧ v = 0 ∧ w = 1) ∨ (u = 0 ∧ v = 0 ∧ w = -1)) : IsC2Vec x y z := by
  rw [← hx1, ← hy1, ← hz1]
  rcases huvw with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · left; exact ⟨q_c2_axis1.1, q_c2_axis1.2.1, q_c2_axis1.2.2⟩
  · have hq0 : qConjX ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 (-1) 0 0 = (Real.goldenRatio - 1) / 2 := by
      rw [qConjX_neg_x, q_c2_axis1.1]
      ring
    have hq1 : qConjY ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 (-1) 0 0 = -Real.goldenRatio / 2 := by
      rw [qConjY_neg_x, q_c2_axis1.2.1]
      ring
    have hq2 : qConjZ ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 (-1) 0 0 = 1 / 2 := by
      rw [qConjZ_neg_x, q_c2_axis1.2.2]
      ring
    right; left; exact ⟨hq0, hq1, hq2⟩
  · right; right; left; exact ⟨q_c2_axis2.1, q_c2_axis2.2.1, q_c2_axis2.2.2⟩
  · have hq0 : qConjX ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 0 (-1) 0 = -Real.goldenRatio / 2 := by
      rw [qConjX_neg_y, q_c2_axis2.1]
      ring
    have hq1 : qConjY ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 0 (-1) 0 = -1 / 2 := by
      rw [qConjY_neg_y, q_c2_axis2.2.1]
      ring
    have hq2 : qConjZ ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 0 (-1) 0 = (1 - Real.goldenRatio) / 2 := by
      rw [qConjZ_neg_y, q_c2_axis2.2.2]
      ring
    right; right; right; left; exact ⟨hq0, hq1, hq2⟩
  · right; right; right; right; left; exact ⟨q_c2_axis3.1, q_c2_axis3.2.1, q_c2_axis3.2.2⟩
  · have hq0 : qConjX ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 0 0 (-1) = -1 / 2 := by
      rw [qConjX_neg_z, q_c2_axis3.1]
      ring
    have hq1 : qConjY ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 0 0 (-1) = (Real.goldenRatio - 1) / 2 := by
      rw [qConjY_neg_z, q_c2_axis3.2.1]
      ring
    have hq2 : qConjZ ((Real.goldenRatio - 1) / 2) (1 / 2) (Real.goldenRatio / 2) 0 0 0 (-1) = Real.goldenRatio / 2 := by
      rw [qConjZ_neg_z, q_c2_axis3.2.2]
      ring
    right; right; right; right; right; exact ⟨hq0, hq1, hq2⟩

private lemma c1_abs_x_cases {x y z : ℝ} (h : quatImToMat x y z ∈ cubeFrame 1) : IsC1Vec x y z := by
  simp only [cubeFrame, Fin.val_one, pow_one] at h
  rcases h with ⟨X, hX, hEq⟩
  have hx : ∃ u v w : ℝ, X = quatImToMat u v w ∧
      ((u = 1 ∧ v = 0 ∧ w = 0) ∨ (u = -1 ∧ v = 0 ∧ w = 0) ∨
       (u = 0 ∧ v = 1 ∧ w = 0) ∨ (u = 0 ∧ v = -1 ∧ w = 0) ∨
       (u = 0 ∧ v = 0 ∧ w = 1) ∨ (u = 0 ∧ v = 0 ∧ w = -1)) := by
    simp only [baseOctahedronSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, 0, 0, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨-1, 0, 0, rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
    · exact ⟨0, 1, 0, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩
    · exact ⟨0, -1, 0, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))⟩
    · exact ⟨0, 0, 1, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))⟩
    · exact ⟨0, 0, -1, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))⟩
  rcases hx with ⟨u, v, w, rfl, huvw⟩
  dsimp only at hEq
  rw [icosianGenA, conjMat_quatToSU2_im] at hEq
  obtain ⟨hx1, hy1, hz1⟩ := quatImToMat_injective hEq
  exact c1_conj_octahedron_isC1Vec hx1 hy1 hz1 huvw

private lemma c2_abs_x_cases {x y z : ℝ} (h : quatImToMat x y z ∈ cubeFrame 2) : IsC2Vec x y z := by
  simp only [cubeFrame, show (2 : Fin 5).val = 2 from rfl, icosianGenA_pow_two] at h
  rcases h with ⟨X, hX, hEq⟩
  have hx : ∃ u v w : ℝ, X = quatImToMat u v w ∧
      ((u = 1 ∧ v = 0 ∧ w = 0) ∨ (u = -1 ∧ v = 0 ∧ w = 0) ∨
       (u = 0 ∧ v = 1 ∧ w = 0) ∨ (u = 0 ∧ v = -1 ∧ w = 0) ∨
       (u = 0 ∧ v = 0 ∧ w = 1) ∨ (u = 0 ∧ v = 0 ∧ w = -1)) := by
    simp only [baseOctahedronSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, 0, 0, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨-1, 0, 0, rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
    · exact ⟨0, 1, 0, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩
    · exact ⟨0, -1, 0, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))⟩
    · exact ⟨0, 0, 1, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))⟩
    · exact ⟨0, 0, -1, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))⟩
  rcases hx with ⟨u, v, w, rfl, huvw⟩
  dsimp only at hEq
  rw [icosianGenA2, conjMat_quatToSU2_im] at hEq
  obtain ⟨hx1, hy1, hz1⟩ := quatImToMat_injective hEq
  exact c2_conj_octahedron_isC2Vec hx1 hy1 hz1 huvw

private lemma not_c1_axis_flip (x y z : ℝ)
    (hx : x = 1 / 2 ∨ x = -1 / 2)
    (h1 : IsC1Vec x y z)
    (hne1 : ¬ (x = 1 / 2 ∧ y = (Real.goldenRatio - 1) / 2 ∧ z = -Real.goldenRatio / 2))
    (hne2 : ¬ (x = -1 / 2 ∧ y = -(Real.goldenRatio - 1) / 2 ∧ z = Real.goldenRatio / 2)) : False := by
  have hphi1 := Real.one_lt_goldenRatio
  have hphi2 := Real.goldenRatio_lt_two
  rcases h1 with h | h | h | h | h | h
  · exact hne1 h
  · exact hne2 h
  · rcases hx with rfl | rfl <;> linarith
  · rcases hx with rfl | rfl <;> linarith
  · rcases hx with rfl | rfl <;> linarith
  · rcases hx with rfl | rfl <;> linarith

private lemma hurwitz_odd_not_stab_c1_c2_pos {q r s : ℝ}
    (hq : q = 1 ∨ q = -1) (hr : r = 1 ∨ r = -1) (hs : s = 1 ∨ s = -1)
    (hc1 : IsC1Vec
      (qConjX (1 / 2) (q / 2) (r / 2) (s / 2) (1 / 2) ((Real.goldenRatio - 1) / 2) (-Real.goldenRatio / 2))
      (qConjY (1 / 2) (q / 2) (r / 2) (s / 2) (1 / 2) ((Real.goldenRatio - 1) / 2) (-Real.goldenRatio / 2))
      (qConjZ (1 / 2) (q / 2) (r / 2) (s / 2) (1 / 2) ((Real.goldenRatio - 1) / 2) (-Real.goldenRatio / 2)))
    (hc2 : IsC2Vec
      (qConjX (1 / 2) (q / 2) (r / 2) (s / 2) ((1 - Real.goldenRatio) / 2) (Real.goldenRatio / 2) (-1 / 2))
      (qConjY (1 / 2) (q / 2) (r / 2) (s / 2) ((1 - Real.goldenRatio) / 2) (Real.goldenRatio / 2) (-1 / 2))
      (qConjZ (1 / 2) (q / 2) (r / 2) (s / 2) ((1 - Real.goldenRatio) / 2) (Real.goldenRatio / 2) (-1 / 2))) :
    False := by
  have hphi1 := Real.one_lt_goldenRatio
  have hphi2 := Real.goldenRatio_lt_two
  rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
  · simp only [qConjX, qConjY, qConjZ] at hc1
    rcases hc1 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> linarith
  · simp only [qConjX, qConjY, qConjZ] at hc1
    rcases hc1 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> linarith
  · simp only [qConjX, qConjY, qConjZ] at hc1
    rcases hc1 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> linarith
  · simp only [qConjX, qConjY, qConjZ] at hc2
    rcases hc2 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> linarith
  · simp only [qConjX, qConjY, qConjZ] at hc2
    rcases hc2 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> linarith
  · simp only [qConjX, qConjY, qConjZ] at hc1
    rcases hc1 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> linarith
  · simp only [qConjX, qConjY, qConjZ] at hc1
    rcases hc1 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> linarith
  · simp only [qConjX, qConjY, qConjZ] at hc1
    rcases hc1 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> linarith

private lemma even_sum_sq_four_imp_one {a b c d : ℤ}
    (h : (a + a) ^ 2 + (b + b) ^ 2 + (c + c) ^ 2 + (d + d) ^ 2 = 4) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 := by
  linarith [h]

private lemma int_double_div_two (m : ℤ) : ((m + m : ℤ) : ℝ) / 2 = (m : ℝ) := by
  push_cast
  ring

private lemma even_imag_unit_not_c1 {a b c d : ℤ}
    (h : (a = 0 ∧ b ^ 2 = 1 ∧ c = 0 ∧ d = 0) ∨
      (a = 0 ∧ b = 0 ∧ c ^ 2 = 1 ∧ d = 0) ∨
      (a = 0 ∧ b = 0 ∧ c = 0 ∧ d ^ 2 = 1))
    (hc1v : IsC1Vec
      (qConjX (((a + a : ℤ) : ℝ) / 2) (((b + b : ℤ) : ℝ) / 2)
        (((c + c : ℤ) : ℝ) / 2) (((d + d : ℤ) : ℝ) / 2)
        (1 / 2) ((Real.goldenRatio - 1) / 2) (-Real.goldenRatio / 2))
      (qConjY (((a + a : ℤ) : ℝ) / 2) (((b + b : ℤ) : ℝ) / 2)
        (((c + c : ℤ) : ℝ) / 2) (((d + d : ℤ) : ℝ) / 2)
        (1 / 2) ((Real.goldenRatio - 1) / 2) (-Real.goldenRatio / 2))
      (qConjZ (((a + a : ℤ) : ℝ) / 2) (((b + b : ℤ) : ℝ) / 2)
        (((c + c : ℤ) : ℝ) / 2) (((d + d : ℤ) : ℝ) / 2)
        (1 / 2) ((Real.goldenRatio - 1) / 2) (-Real.goldenRatio / 2))) : False := by
  have hphi1 := Real.one_lt_goldenRatio
  have hphi2 := Real.goldenRatio_lt_two
  rw [int_double_div_two a, int_double_div_two b, int_double_div_two c, int_double_div_two d] at hc1v
  rcases h with ⟨rfl, hsq, rfl, rfl⟩ | ⟨rfl, rfl, hsq, rfl⟩ | ⟨rfl, rfl, rfl, hsq⟩ <;>
    · rcases sq_eq_one_iff.mp hsq with rfl | rfl <;>
        simp only [Int.cast_one, Int.cast_neg, Int.cast_zero, qConjX, qConjY, qConjZ] at hc1v <;>
        rcases hc1v with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ |
          ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> linarith

private lemma hurwitz_odd_not_stab_c1_c2_neg {q r s : ℝ}
    (hq : q = 1 ∨ q = -1) (hr : r = 1 ∨ r = -1) (hs : s = 1 ∨ s = -1)
    (hc1v : IsC1Vec
      (qConjX ((-1 : ℝ) / 2) (q / 2) (r / 2) (s / 2)
        (1 / 2) ((Real.goldenRatio - 1) / 2) (-Real.goldenRatio / 2))
      (qConjY ((-1 : ℝ) / 2) (q / 2) (r / 2) (s / 2)
        (1 / 2) ((Real.goldenRatio - 1) / 2) (-Real.goldenRatio / 2))
      (qConjZ ((-1 : ℝ) / 2) (q / 2) (r / 2) (s / 2)
        (1 / 2) ((Real.goldenRatio - 1) / 2) (-Real.goldenRatio / 2)))
    (hc2v : IsC2Vec
      (qConjX ((-1 : ℝ) / 2) (q / 2) (r / 2) (s / 2)
        ((1 - Real.goldenRatio) / 2) (Real.goldenRatio / 2) (-1 / 2))
      (qConjY ((-1 : ℝ) / 2) (q / 2) (r / 2) (s / 2)
        ((1 - Real.goldenRatio) / 2) (Real.goldenRatio / 2) (-1 / 2))
      (qConjZ ((-1 : ℝ) / 2) (q / 2) (r / 2) (s / 2)
        ((1 - Real.goldenRatio) / 2) (Real.goldenRatio / 2) (-1 / 2))) : False := by
  have hneg_qConjX : ∀ a b c d x y z : ℝ,
      qConjX (-a) (-b) (-c) (-d) x y z = qConjX a b c d x y z := by
    intros; simp only [qConjX]; ring
  have hneg_qConjY : ∀ a b c d x y z : ℝ,
      qConjY (-a) (-b) (-c) (-d) x y z = qConjY a b c d x y z := by
    intros; simp only [qConjY]; ring
  have hneg_qConjZ : ∀ a b c d x y z : ℝ,
      qConjZ (-a) (-b) (-c) (-d) x y z = qConjZ a b c d x y z := by
    intros; simp only [qConjZ]; ring
  have hq' : -q = 1 ∨ -q = -1 := by rcases hq with h | h <;> [right; left] <;> linarith
  have hr' : -r = 1 ∨ -r = -1 := by rcases hr with h | h <;> [right; left] <;> linarith
  have hs' : -s = 1 ∨ -s = -1 := by rcases hs with h | h <;> [right; left] <;> linarith
  rw [show ((-1 : ℝ) / 2) = -(1 / 2) by ring,
    show (q / 2) = -(-q / 2) by ring,
    show (r / 2) = -(-r / 2) by ring,
    show (s / 2) = -(-s / 2) by ring,
    hneg_qConjX, hneg_qConjY, hneg_qConjZ] at hc1v hc2v
  have hhalf : -(1 / 2 : ℝ) = -1 / 2 := by ring
  rw [hhalf] at hc2v
  exact hurwitz_odd_not_stab_c1_c2_pos hq' hr' hs' hc1v hc2v

private lemma hurwitz_stabilizing_c1_c2_mem_signSet {t : SU2} (ht : t ∈ hurwitz24Subgroup)
    (hc1 : conjMat t '' cubeFrame 1 = cubeFrame 1)
    (hc2 : conjMat t '' cubeFrame 2 = cubeFrame 2) :
    t ∈ su2SignSet := by
  have hv1_in : quatImToMat (1 / 2) ((Real.goldenRatio - 1) / 2) (-Real.goldenRatio / 2) ∈ cubeFrame 1 := by
    refine ⟨quatImToMat 1 0 0, by simp [baseOctahedronSet], ?_⟩
    rw [Fin.val_one, pow_one, icosianGenA, conjMat_quatToSU2_im,
      q_c1_axis1.1, q_c1_axis1.2.1, q_c1_axis1.2.2]
  have hv2_in : quatImToMat ((1 - Real.goldenRatio) / 2) (Real.goldenRatio / 2) (-1 / 2) ∈ cubeFrame 2 := by
    refine ⟨quatImToMat 1 0 0, by simp [baseOctahedronSet], ?_⟩
    rw [show (2 : Fin 5).val = 2 from rfl, icosianGenA_pow_two, icosianGenA2,
      conjMat_quatToSU2_im, q_c2_axis1.1, q_c2_axis1.2.1, q_c2_axis1.2.2]
  have htv1 : conjMat t (quatImToMat (1 / 2) ((Real.goldenRatio - 1) / 2) (-Real.goldenRatio / 2)) ∈
      cubeFrame 1 := by
    rw [← hc1]
    exact ⟨_, hv1_in, rfl⟩
  have htv2 : conjMat t (quatImToMat ((1 - Real.goldenRatio) / 2) (Real.goldenRatio / 2) (-1 / 2)) ∈
      cubeFrame 2 := by
    rw [← hc2]
    exact ⟨_, hv2_in, rfl⟩
  rcases ht with ⟨p, q, r, s, hTup, rfl⟩
  rcases hTup.2 with ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩, ⟨d, rfl⟩⟩ | ⟨hp, hq, hr, hs⟩
  · have hsum : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 := even_sum_sq_four_imp_one hTup.1
    rcases int_sum_sq_one_cases a b c d hsum with
      ⟨hsq, rfl, rfl, rfl⟩ | ⟨rfl, hsq, rfl, rfl⟩ | ⟨rfl, rfl, hsq, rfl⟩ | ⟨rfl, rfl, rfl, hsq⟩
    · rcases sq_eq_one_iff.mp hsq with rfl | rfl
      · exact Or.inl (by
          rw [← quatToSU2_one]
          apply quatToSU2_eq_of_eq <;> norm_num [int_double_div_two])
      · exact Or.inr (by
          rw [negOneSU2]
          apply quatToSU2_eq_of_eq <;> norm_num [int_double_div_two])
    · rw [conjMat_quatToSU2_im] at htv1
      exact False.elim (even_imag_unit_not_c1 (Or.inl ⟨rfl, hsq, rfl, rfl⟩) (c1_abs_x_cases htv1))
    · rw [conjMat_quatToSU2_im] at htv1
      exact False.elim (even_imag_unit_not_c1 (Or.inr (Or.inl ⟨rfl, rfl, hsq, rfl⟩)) (c1_abs_x_cases htv1))
    · rw [conjMat_quatToSU2_im] at htv1
      exact False.elim (even_imag_unit_not_c1 (Or.inr (Or.inr ⟨rfl, rfl, rfl, hsq⟩)) (c1_abs_x_cases htv1))
  · exfalso
    have hp1 := odd_int_sq_ge_one hp
    have hq1 := odd_int_sq_ge_one hq
    have hr1 := odd_int_sq_ge_one hr
    have hs1 := odd_int_sq_ge_one hs
    have hsum4 : p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 = 4 := hTup.1
    have hpsq : p ^ 2 = 1 := by omega
    have hqsq : q ^ 2 = 1 := by omega
    have hrsq : r ^ 2 = 1 := by omega
    have hssq : s ^ 2 = 1 := by omega
    rw [conjMat_quatToSU2_im] at htv1 htv2
    have hc1v := c1_abs_x_cases htv1
    have hc2v := c2_abs_x_cases htv2
    have hp_cases : (p : ℝ) = 1 ∨ (p : ℝ) = -1 := by exact_mod_cast sq_eq_one_iff.mp hpsq
    have hq_cases : (q : ℝ) = 1 ∨ (q : ℝ) = -1 := by exact_mod_cast sq_eq_one_iff.mp hqsq
    have hr_cases : (r : ℝ) = 1 ∨ (r : ℝ) = -1 := by exact_mod_cast sq_eq_one_iff.mp hrsq
    have hs_cases : (s : ℝ) = 1 ∨ (s : ℝ) = -1 := by exact_mod_cast sq_eq_one_iff.mp hssq
    rcases hp_cases with hp' | hp'
    · rw [hp'] at hc1v hc2v
      exact hurwitz_odd_not_stab_c1_c2_pos hq_cases hr_cases hs_cases
        (by simpa [one_div] using hc1v) (by simpa [one_div] using hc2v)
    · rw [hp'] at hc1v hc2v
      exact hurwitz_odd_not_stab_c1_c2_neg hq_cases hr_cases hs_cases hc1v hc2v

/-- The icosahedral subgroup `I ⊂ PSU(2)` obtained as the quotient image of `2I ⊂ SU(2)`. -/
def icosahedralPSU2Subgroup : Subgroup PSU2 :=
  binaryIcosahedralGroup.map (QuotientGroup.mk' su2SignSet)

private lemma permA5_mem_alt5 : permA5 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

private lemma permB5_mem_alt5 : permB5 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

private def permV4 : Equiv.Perm (Fin 5) := permA5 ^ 2 * permB5 * permA5 ^ 3 * permB5 * permA5 ^ 2

set_option maxRecDepth 4096 in
private lemma permB5_sq : permB5 * permB5 = 1 := by
  ext i
  fin_cases i <;> decide

set_option maxRecDepth 4096 in
private lemma permV4_sq : permV4 * permV4 = 1 := by
  ext i
  fin_cases i <;> decide

set_option maxRecDepth 4096 in
private lemma permB5_comm_permV4 : permB5 * permV4 = permV4 * permB5 := by
  ext i
  fin_cases i <;> decide

private lemma permB5_mul_permV4_mul_permB5 :
    permB5 * (permV4 * permB5) = permV4 := by
  calc
    permB5 * (permV4 * permB5) = (permB5 * permV4) * permB5 := by rw [mul_assoc]
    _ = (permV4 * permB5) * permB5 := by rw [permB5_comm_permV4]
    _ = permV4 * (permB5 * permB5) := by rw [mul_assoc]
    _ = permV4 := by rw [permB5_sq, mul_one]

private lemma permV4_mul_permV4_mul_permB5 :
    permV4 * (permV4 * permB5) = permB5 := by
  calc
    permV4 * (permV4 * permB5) = (permV4 * permV4) * permB5 := by rw [mul_assoc]
    _ = permB5 := by rw [permV4_sq, one_mul]

set_option maxRecDepth 4096 in
private lemma permV4_vals :
    permV4 0 = 0 ∧ permV4 1 = 3 ∧ permV4 2 = 4 ∧
      permV4 3 = 1 ∧ permV4 4 = 2 := by
  decide

open InfoGeometry.Topology.V4RootSystem

private def permV4Fun : V4Group → Equiv.Perm (Fin 5)
  | .I => 1
  | .W1 => permB5
  | .W2 => permV4
  | .W12 => permB5 * permV4

private lemma permV4Fun_mul (x y : V4Group) :
    permV4Fun (x * y) = permV4Fun x * permV4Fun y := by
  change permV4Fun (InfoGeometry.Topology.V4RootSystem.v4_mul x y) = _
  cases x <;> cases y <;>
    simp [permV4Fun, InfoGeometry.Topology.V4RootSystem.v4_mul,
      permB5_sq, permV4_sq, permB5_comm_permV4,
      permB5_mul_permV4_mul_permB5, permV4_mul_permV4_mul_permB5,
      mul_assoc]

private def permV4Representation : V4Group →* Equiv.Perm (Fin 5) where
  toFun := permV4Fun
  map_one' := rfl
  map_mul' := permV4Fun_mul

set_option maxRecDepth 4096 in
private lemma permV4Fun_injective : Function.Injective permV4Fun := by
  intro x y h
  cases x <;> cases y <;> try rfl
  all_goals
    have h₁ := congrArg (fun σ : Equiv.Perm (Fin 5) => σ 1) h
    have hB₁ : permB5 1 = 2 := permB5_vals.2.1
    have hB₃ : permB5 3 = 4 := permB5_vals.2.2.2.1
    have hV₁ : permV4 1 = 3 := permV4_vals.2.1
    simp [permV4Fun, hB₁, hB₃, hV₁] at h₁

private lemma permV4Representation_injective :
    Function.Injective permV4Representation := permV4Fun_injective

private lemma closure_permA5_permB5_eq_alt5 :
    Subgroup.closure ({permA5, permB5} : Set (Equiv.Perm (Fin 5))) = alternatingGroup (Fin 5) := by
  let K : Subgroup (Equiv.Perm (Fin 5)) := Subgroup.closure {permA5, permB5}
  have hle : K ≤ alternatingGroup (Fin 5) := by
    rw [Subgroup.closure_le]
    rintro σ (rfl | rfl)
    · exact permA5_mem_alt5
    · exact permB5_mem_alt5
  have hA_mem : permA5 ∈ K := Subgroup.subset_closure (by simp)
  have hB_mem : permB5 ∈ K := Subgroup.subset_closure (by simp)
  have hAB_mem : permA5 * permB5 ∈ K := K.mul_mem hA_mem hB_mem
  have hV_mem : permV4 ∈ K := by
    dsimp [permV4]
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.pow_mem hA_mem 2) hB_mem)
      (K.pow_mem hA_mem 3)) hB_mem) (K.pow_mem hA_mem 2)
  have hBV_mem : permB5 * permV4 ∈ K := K.mul_mem hB_mem hV_mem
  have h5_dvd : 5 ∣ Nat.card K := by
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hord : orderOf (⟨permA5, hA_mem⟩ : K) = 5 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by decide) (by decide)
    simpa [hord] using orderOf_dvd_natCard (⟨permA5, hA_mem⟩ : K)
  have h3_dvd : 3 ∣ Nat.card K := by
    letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hord : orderOf (⟨permA5 * permB5, hAB_mem⟩ : K) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by decide) (by decide)
    simpa [hord] using orderOf_dvd_natCard (⟨permA5 * permB5, hAB_mem⟩ : K)
  let V4 : Subgroup (Equiv.Perm (Fin 5)) := permV4Representation.range
  have hV4_le_K : V4 ≤ K := by
    rintro x ⟨g, rfl⟩
    cases g
    · exact K.one_mem
    · exact hB_mem
    · exact hV_mem
    · exact hBV_mem
  have hV4_card : Nat.card V4 = 4 := by
    classical
    letI : Fintype V4Group := ⟨{.I, .W1, .W2, .W12}, by
      intro x
      cases x <;> simp⟩
    let e : Fin 4 ≃ V4Group :=
      { toFun := fun i => match i with
          | 0 => .I | 1 => .W1 | 2 => .W2 | 3 => .W12
        invFun := fun g => match g with
          | .I => 0 | .W1 => 1 | .W2 => 2 | .W12 => 3
        left_inv := by intro i; fin_cases i <;> rfl
        right_inv := by intro g; cases g <;> rfl }
    let f : V4Group → V4 := fun x => ⟨permV4Representation x, ⟨x, rfl⟩⟩
    have hf : Function.Injective f := by
      intro x y h
      exact permV4Representation_injective (congrArg Subtype.val h)
    have hsurj : Function.Surjective f := by
      intro x
      rcases x.2 with ⟨g, hg⟩
      refine ⟨g, ?_⟩
      apply Subtype.ext
      exact hg
    have he : V4Group ≃ V4 := Equiv.ofBijective f ⟨hf, hsurj⟩
    rw [← Nat.card_congr he]
    rw [Nat.card_eq_fintype_card, ← Fintype.card_congr e, Fintype.card_fin]
  have h4_dvd : 4 ∣ Nat.card K := by
    rw [← hV4_card]
    exact Subgroup.card_dvd_of_le hV4_le_K
  have h15_dvd : 15 ∣ Nat.card K := (show Nat.Coprime 5 3 by norm_num).mul_dvd_of_dvd_of_dvd h5_dvd h3_dvd
  have h60_dvd : 60 ∣ Nat.card K := (show Nat.Coprime 15 4 by norm_num).mul_dvd_of_dvd_of_dvd h15_dvd h4_dvd
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hle_card : Nat.card K ≤ 60 := by
    have hcard60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup]
      norm_num
    rw [← hcard60]
    exact Nat.le_of_dvd (by rw [hcard60]; norm_num) (Subgroup.card_dvd_of_le hle)
  have hcardK : Nat.card (alternatingGroup (Fin 5)) ≤ Nat.card K := by
    have hcard60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup]
      norm_num
    rw [hcard60]
    exact Nat.le_of_dvd hpos h60_dvd
  exact Subgroup.eq_of_le_of_card_ge hle hcardK

private lemma binaryIcosahedralGroup_acts_on_cubes (g : SU2) (hg : g ∈ binaryIcosahedralGroup) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ m : Fin 5, conjMat g '' cubeFrame m = cubeFrame (σ m) := by
  refine Subgroup.closure_induction (p := fun x _ =>
      ∃ σ : Equiv.Perm (Fin 5), ∀ m : Fin 5, conjMat x '' cubeFrame m = cubeFrame (σ m))
    ?_ ?_ ?_ ?_ hg
  · rintro x (rfl | rfl)
    · exact ⟨permA5, conjMat_A_cubeFrame⟩
    · exact ⟨permB5, conjMat_B_cubeFrame⟩
  · exact ⟨1, fun m => by simp [conjMat_one]⟩
  · rintro x y _ _ ⟨σx, hx⟩ ⟨σy, hy⟩
    refine ⟨σx * σy, fun m => ?_⟩
    have hcomp : conjMat (x * y) = conjMat x ∘ conjMat y := by
      funext X; exact conjMat_mul x y X
    rw [hcomp, Set.image_comp, hy m, hx (σy m)]
    rfl
  · rintro x _ ⟨σx, hx⟩
    refine ⟨σx⁻¹, fun m => ?_⟩
    have hsigma : conjMat x '' cubeFrame (σx⁻¹ m) = cubeFrame m := by
      have h1 := hx (σx⁻¹ m)
      have happ : σx (σx⁻¹ m) = m := Equiv.apply_symm_apply σx m
      rw [happ] at h1
      exact h1
    have hcomp2 : conjMat x⁻¹ ∘ conjMat x = id := by
      funext X
      change conjMat x⁻¹ (conjMat x X) = X
      rw [← conjMat_mul, inv_mul_cancel, conjMat_one]
    have hfin := congrArg (fun S => conjMat x⁻¹ '' S) hsigma.symm
    rw [← Set.image_comp, hcomp2, Set.image_id] at hfin
    exact hfin

private lemma conjMat_quotient_wellDefined {g₁ g₂ : SU2}
    (h : (QuotientGroup.mk g₁ : PSU2) = QuotientGroup.mk g₂) (X : Mat2C) :
    conjMat g₁ X = conjMat g₂ X := by
  have hmem : g₁⁻¹ * g₂ ∈ su2SignSet := (QuotientGroup.eq).mp h
  have hEq : g₂ = g₁ * (g₁⁻¹ * g₂) := by group
  rw [hEq, conjMat_mul, conjMat_signSet hmem]

private def su2Perm5Map (g : SU2) (hg : g ∈ binaryIcosahedralGroup) : Equiv.Perm (Fin 5) :=
  Classical.choose (binaryIcosahedralGroup_acts_on_cubes g hg)

private lemma su2Perm5Map_spec (g : SU2) (hg : g ∈ binaryIcosahedralGroup) (m : Fin 5) :
    conjMat g '' cubeFrame m = cubeFrame (su2Perm5Map g hg m) :=
  Classical.choose_spec (binaryIcosahedralGroup_acts_on_cubes g hg) m

private lemma psu2_coset_rep_mem_binaryIcosahedral {q : PSU2} (hq : q ∈ icosahedralPSU2Subgroup) :
    ∃ g : SU2, g ∈ binaryIcosahedralGroup ∧ QuotientGroup.mk g = q :=
  hq

/-- Conjugation on the 5 inscribed cubes induces a group homomorphism `I ⊂ PSU(2) →* S₅`. -/
def icosahedralToPerm5 : icosahedralPSU2Subgroup →* Equiv.Perm (Fin 5) where
  toFun q :=
    su2Perm5Map (Classical.choose (psu2_coset_rep_mem_binaryIcosahedral q.prop))
      (Classical.choose_spec (psu2_coset_rep_mem_binaryIcosahedral q.prop)).1
  map_one' := by
    refine Equiv.ext fun m => cubeFrame_injective ?_
    let g := Classical.choose (psu2_coset_rep_mem_binaryIcosahedral (1 : icosahedralPSU2Subgroup).prop)
    have hg := Classical.choose_spec (psu2_coset_rep_mem_binaryIcosahedral (1 : icosahedralPSU2Subgroup).prop)
    rw [← su2Perm5Map_spec g hg.1 m]
    have hq : QuotientGroup.mk g = (QuotientGroup.mk (1 : SU2) : PSU2) := hg.2
    have hc : conjMat g '' cubeFrame m = conjMat 1 '' cubeFrame m := by
      ext Y
      simp [Set.mem_image, conjMat_quotient_wellDefined hq]
    rw [hc]
    simp [conjMat_one]
  map_mul' q₁ q₂ := by
    refine Equiv.ext fun m => cubeFrame_injective ?_
    let g₁ := Classical.choose (psu2_coset_rep_mem_binaryIcosahedral q₁.prop)
    have hg₁ := Classical.choose_spec (psu2_coset_rep_mem_binaryIcosahedral q₁.prop)
    let g₂ := Classical.choose (psu2_coset_rep_mem_binaryIcosahedral q₂.prop)
    have hg₂ := Classical.choose_spec (psu2_coset_rep_mem_binaryIcosahedral q₂.prop)
    let g₁₂ := Classical.choose (psu2_coset_rep_mem_binaryIcosahedral (q₁ * q₂).prop)
    have hg₁₂ := Classical.choose_spec (psu2_coset_rep_mem_binaryIcosahedral (q₁ * q₂).prop)
    change cubeFrame (su2Perm5Map g₁₂ hg₁₂.1 m) =
      cubeFrame (su2Perm5Map g₁ hg₁.1 (su2Perm5Map g₂ hg₂.1 m))
    rw [← su2Perm5Map_spec g₁₂ hg₁₂.1 m, ← su2Perm5Map_spec g₁ hg₁.1, ← su2Perm5Map_spec g₂ hg₂.1]
    have hq : (QuotientGroup.mk' su2SignSet) g₁₂ =
        (QuotientGroup.mk' su2SignSet) (g₁ * g₂) := by
      calc
        (QuotientGroup.mk' su2SignSet) g₁₂ = (q₁ * q₂ : PSU2) := hg₁₂.2
        _ = (q₁ : PSU2) * (q₂ : PSU2) := rfl
        _ = (QuotientGroup.mk' su2SignSet) g₁ * (QuotientGroup.mk' su2SignSet) g₂ := by
          rw [← hg₁.2, ← hg₂.2]
          exact (map_mul (QuotientGroup.mk' su2SignSet) g₁ g₂).symm
        _ = (QuotientGroup.mk' su2SignSet) (g₁ * g₂) := rfl
    have hc : conjMat g₁₂ '' cubeFrame m = conjMat (g₁ * g₂) '' cubeFrame m := by
      ext Y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨X, hX, hXY⟩
        exact ⟨X, hX, (conjMat_quotient_wellDefined hq X).symm.trans hXY⟩
      · rintro ⟨X, hX, hXY⟩
        exact ⟨X, hX, (conjMat_quotient_wellDefined hq X).trans hXY⟩
    rw [hc, ← Set.image_comp]
    congr 1
    funext X
    exact conjMat_mul g₁ g₂ X

private lemma icosahedralToPerm5_on_gen (g : SU2) (hg : g ∈ binaryIcosahedralGroup)
    (σ : Equiv.Perm (Fin 5)) (hσ : ∀ m : Fin 5, conjMat g '' cubeFrame m = cubeFrame (σ m)) :
    icosahedralToPerm5 ⟨QuotientGroup.mk g, ⟨g, hg, rfl⟩⟩ = σ := by
  refine Equiv.ext fun m => cubeFrame_injective ?_
  let g' := Classical.choose (psu2_coset_rep_mem_binaryIcosahedral ⟨g, hg, rfl⟩)
  have hg' := Classical.choose_spec (psu2_coset_rep_mem_binaryIcosahedral ⟨g, hg, rfl⟩)
  change cubeFrame (su2Perm5Map g' hg'.1 m) = cubeFrame (σ m)
  rw [← su2Perm5Map_spec g' hg'.1 m, ← hσ m]
  ext Y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨X, hX, hXY⟩
    exact ⟨X, hX, (conjMat_quotient_wellDefined hg'.2 X).symm.trans hXY⟩
  · rintro ⟨X, hX, hXY⟩
    exact ⟨X, hX, (conjMat_quotient_wellDefined hg'.2 X).trans hXY⟩

theorem icosahedralToPerm5_injective : Function.Injective icosahedralToPerm5 := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨g, hg, hgq⟩ := q.prop
  have hgcos : g ∈ icosahedralCosetUnion := binaryIcosahedralGroup_subset_cosetUnion hg
  rcases hgcos with ⟨m, t, ht, rfl⟩
  have hfix : ∀ k : Fin 5, conjMat (icosianGenA ^ m.val * t) '' cubeFrame k = cubeFrame k := by
    intro k
    let g' := Classical.choose (psu2_coset_rep_mem_binaryIcosahedral q.prop)
    have hg' := Classical.choose_spec (psu2_coset_rep_mem_binaryIcosahedral q.prop)
    have hqeq : QuotientGroup.mk g' = QuotientGroup.mk (icosianGenA ^ m.val * t) :=
      hg'.2.trans hgq.symm
    have heq_img : conjMat (icosianGenA ^ m.val * t) '' cubeFrame k = conjMat g' '' cubeFrame k := by
      ext Y
      simp [Set.mem_image, conjMat_quotient_wellDefined hqeq.symm]
    rw [heq_img, su2Perm5Map_spec g' hg'.1 k]
    have hval := congrArg (fun σ => σ k) hq
    exact congrArg cubeFrame hval
  have hm0 : m = 0 := by
    have h0 := hfix 0
    have hcomp : conjMat (icosianGenA ^ m.val * t) '' cubeFrame 0 = cubeFrame m := by
      rw [show conjMat (icosianGenA ^ m.val * t) = conjMat (icosianGenA ^ m.val) ∘ conjMat t from
          funext (conjMat_mul _ _), Set.image_comp, cubeFrame_zero, hurwitz_conj_base_eq ht]
      rfl
    rw [hcomp] at h0
    exact cubeFrame_injective h0
  subst hm0
  simp only [Fin.val_zero, pow_zero, one_mul] at hfix hgq
  have ht_sign : t ∈ su2SignSet :=
    hurwitz_stabilizing_c1_c2_mem_signSet ht (hfix 1) (hfix 2)
  ext1
  calc
    (q : PSU2) = QuotientGroup.mk t := hgq.symm
    _ = 1 := (QuotientGroup.eq_one_iff t).mpr ht_sign

theorem icosahedralToPerm5_range_eq_alt5 :
    icosahedralToPerm5.range = alternatingGroup (Fin 5) := by
  have hgenA : icosianGenA ∈ binaryIcosahedralGroup :=
    Subgroup.subset_closure (by simp)
  have hgenB : icosianGenB ∈ binaryIcosahedralGroup :=
    Subgroup.subset_closure (by simp)
  have hA_im : icosahedralToPerm5 ⟨QuotientGroup.mk icosianGenA, ⟨icosianGenA, hgenA, rfl⟩⟩ = permA5 :=
    icosahedralToPerm5_on_gen icosianGenA hgenA permA5 conjMat_A_cubeFrame
  have hB_im : icosahedralToPerm5 ⟨QuotientGroup.mk icosianGenB, ⟨icosianGenB, hgenB, rfl⟩⟩ = permB5 :=
    icosahedralToPerm5_on_gen icosianGenB hgenB permB5 conjMat_B_cubeFrame
  refine le_antisymm ?_ ?_
  · rintro _ ⟨q, rfl⟩
    obtain ⟨g, hg, hgq⟩ := q.prop
    have hperm : icosahedralToPerm5 q ∈ alternatingGroup (Fin 5) := by
      have hc : (⟨QuotientGroup.mk g, ⟨g, hg, rfl⟩⟩ : icosahedralPSU2Subgroup) = q := by
        ext1; exact hgq
      rw [← hc]
      clear hc hgq q
      refine Subgroup.closure_induction (p := fun x hx =>
          icosahedralToPerm5 ⟨QuotientGroup.mk x, ⟨x, hx, rfl⟩⟩ ∈ alternatingGroup (Fin 5))
        ?_ ?_ ?_ ?_ hg
      · rintro x (rfl | rfl)
        · rw [hA_im]; exact permA5_mem_alt5
        · rw [hB_im]; exact permB5_mem_alt5
      · have h1 : (⟨QuotientGroup.mk (1 : SU2), ⟨1, binaryIcosahedralGroup.one_mem, rfl⟩⟩ :
            icosahedralPSU2Subgroup) = 1 := rfl
        rw [h1, map_one]
        exact (alternatingGroup (Fin 5)).one_mem
      · intro x y hx hy ihx ihy
        have hmul : (⟨QuotientGroup.mk (x * y), ⟨x * y, binaryIcosahedralGroup.mul_mem hx hy, rfl⟩⟩ :
            icosahedralPSU2Subgroup) =
            ⟨QuotientGroup.mk x, ⟨x, hx, rfl⟩⟩ * ⟨QuotientGroup.mk y, ⟨y, hy, rfl⟩⟩ := rfl
        rw [hmul, map_mul]
        exact (alternatingGroup (Fin 5)).mul_mem ihx ihy
      · intro x hx ihx
        have hinv : (⟨QuotientGroup.mk x⁻¹, ⟨x⁻¹, binaryIcosahedralGroup.inv_mem hx, rfl⟩⟩ :
            icosahedralPSU2Subgroup) =
            (⟨QuotientGroup.mk x, ⟨x, hx, rfl⟩⟩)⁻¹ := rfl
        rw [hinv, map_inv]
        exact (alternatingGroup (Fin 5)).inv_mem ihx
    exact hperm
  · rw [← closure_permA5_permB5_eq_alt5, Subgroup.closure_le]
    rintro σ (rfl | rfl)
    · exact ⟨⟨QuotientGroup.mk icosianGenA, ⟨icosianGenA, hgenA, rfl⟩⟩, hA_im⟩
    · exact ⟨⟨QuotientGroup.mk icosianGenB, ⟨icosianGenB, hgenB, rfl⟩⟩, hB_im⟩

/-- Explicit isomorphism from the alternating group `A₅` onto Klein's icosahedral subgroup of `PSU(2)`. -/
def kleinIcosahedralMulEquiv : alternatingGroup (Fin 5) ≃* icosahedralPSU2Subgroup :=
  let hom : icosahedralPSU2Subgroup →* alternatingGroup (Fin 5) :=
    { toFun := fun q => ⟨icosahedralToPerm5 q, by
        rw [← icosahedralToPerm5_range_eq_alt5]
        exact ⟨q, rfl⟩⟩
      map_one' := Subtype.ext icosahedralToPerm5.map_one
      map_mul' := fun x y => Subtype.ext (icosahedralToPerm5.map_mul x y) }
  (MulEquiv.ofBijective hom
    ⟨fun x y h => icosahedralToPerm5_injective (congrArg Subtype.val h), fun ⟨σ, hσ⟩ => by
      rw [← icosahedralToPerm5_range_eq_alt5] at hσ
      obtain ⟨q, hq⟩ := hσ
      exact ⟨q, Subtype.ext hq⟩⟩).symm

/-- Classical Felix Klein injective homomorphism `A₅ →* PSU(2)`. -/
def kleinIcosahedralPSU2Embedding : alternatingGroup (Fin 5) →* PSU2 :=
  icosahedralPSU2Subgroup.subtype.comp kleinIcosahedralMulEquiv.toMonoidHom

theorem kleinIcosahedralPSU2Embedding_injective :
    Function.Injective kleinIcosahedralPSU2Embedding :=
  Subtype.coe_injective.comp kleinIcosahedralMulEquiv.injective

/-! ## Section 4: Homogeneous Icosahedral Invariants `(f, H, T)` and Klein's `1728` Syzygy -/

def kleinIcosahedralVertexF {R : Type*} [CommRing R] (z₁ z₂ : R) : R :=
  z₁ * z₂ * (z₁ ^ 10 + 11 * z₁ ^ 5 * z₂ ^ 5 - z₂ ^ 10)

/-- Degree-12 form in the checked standard-generator coordinates.  The middle
coefficient is fixed by the order-four generator together with the order-ten
weight condition; it differs from the source convention above. -/
def kleinIcosahedralStandardVertexF {R : Type*} [CommRing R] (z₁ z₂ : R) : R :=
  z₁ * z₂ * (z₁ ^ 10 - 11 * z₁ ^ 5 * z₂ ^ 5 - z₂ ^ 10)

/-- Degree-20 Klein form in the same basis-adapted coordinates as
`kleinIcosahedralStandardVertexF`. The signs are fixed by invariance under the
owner's standard order-four generator, rather than inherited from the
argument-swapped legacy formula. -/
def kleinIcosahedralStandardFaceH {R : Type*} [CommRing R] (z₁ z₂ : R) : R :=
  -(z₁ ^ 20 + 228 * z₁ ^ 15 * z₂ ^ 5 + 494 * z₁ ^ 10 * z₂ ^ 10 -
    228 * z₁ ^ 5 * z₂ ^ 15 + z₂ ^ 20)

/-- Degree-30 Klein form in the basis-adapted binary coordinates. -/
def kleinIcosahedralStandardEdgeT {R : Type*} [CommRing R] (z₁ z₂ : R) : R :=
  z₁ ^ 30 - 522 * z₁ ^ 25 * z₂ ^ 5 -
    10005 * (z₁ ^ 20 * z₂ ^ 10 + z₁ ^ 10 * z₂ ^ 20) +
    522 * z₁ ^ 5 * z₂ ^ 25 + z₂ ^ 30

/-- The basis-adapted forms satisfy Klein's syzygy with the sign determined
by the normalization of the degree-12 form. This is an algebraic identity;
generator invariance is established separately. -/
theorem kleinIcosahedralStandardForms_syzygy (z₁ z₂ : ℂ) :
    kleinIcosahedralStandardEdgeT z₁ z₂ ^ 2 +
      kleinIcosahedralStandardFaceH z₁ z₂ ^ 3 =
      -1728 * kleinIcosahedralStandardVertexF z₁ z₂ ^ 5 := by
  simp only [kleinIcosahedralStandardEdgeT, kleinIcosahedralStandardFaceH,
    kleinIcosahedralStandardVertexF]
  ring

/-- The corrected standard-coordinate Klein triple is fixed by the diagonal
order-ten generator. This is the generator-compatible counterpart of the
syzygy above; it does not by itself establish invariance under the second
icosahedral generator. -/
theorem kleinIcosahedralStandardForms_invariant_under_diagonal
    (α β : ℂ) (hα5 : α ^ 5 = -1) (hβ5 : β ^ 5 = -1)
    (hαβ : α * β = 1) (z₁ z₂ : ℂ) :
    kleinIcosahedralStandardVertexF
        (α * z₁) (β * z₂) =
      kleinIcosahedralStandardVertexF z₁ z₂ ∧
    kleinIcosahedralStandardFaceH
        (α * z₁) (β * z₂) =
      kleinIcosahedralStandardFaceH z₁ z₂ ∧
    kleinIcosahedralStandardEdgeT
        (α * z₁) (β * z₂) =
      kleinIcosahedralStandardEdgeT z₁ z₂ := by
  have hα10 : α ^ 10 = 1 := by
    calc α ^ 10 = (α ^ 5) ^ 2 := by rw [show 10 = 5 * 2 by norm_num, pow_mul]
      _ = 1 := by rw [hα5]; norm_num
  have hβ10 : β ^ 10 = 1 := by
    calc β ^ 10 = (β ^ 5) ^ 2 := by rw [show 10 = 5 * 2 by norm_num, pow_mul]
      _ = 1 := by rw [hβ5]; norm_num
  have hα20 : α ^ 20 = 1 := by
    calc α ^ 20 = (α ^ 10) ^ 2 := by rw [show 20 = 10 * 2 by norm_num, pow_mul]
      _ = 1 := by rw [hα10]; norm_num
  have hβ20 : β ^ 20 = 1 := by
    calc β ^ 20 = (β ^ 10) ^ 2 := by rw [show 20 = 10 * 2 by norm_num, pow_mul]
      _ = 1 := by rw [hβ10]; norm_num
  have hα30 : α ^ 30 = 1 := by
    calc α ^ 30 = (α ^ 10) ^ 3 := by rw [show 30 = 10 * 3 by norm_num, pow_mul]
      _ = 1 := by rw [hα10]; norm_num
  have hβ30 : β ^ 30 = 1 := by
    calc β ^ 30 = (β ^ 10) ^ 3 := by rw [show 30 = 10 * 3 by norm_num, pow_mul]
      _ = 1 := by rw [hβ10]; norm_num
  have hα15β5 : α ^ 15 * β ^ 5 = 1 := by
    calc α ^ 15 * β ^ 5 = α ^ 10 * (α * β) ^ 5 := by ring
      _ = 1 := by rw [hα10, hαβ]; norm_num
  have hα11β : α ^ 11 * β = 1 := by
    calc α ^ 11 * β = α ^ 10 * (α * β) := by ring
      _ = 1 := by rw [hα10, hαβ]; norm_num
  have hα6β6 : α ^ 6 * β ^ 6 = 1 := by rw [← mul_pow, hαβ]; norm_num
  have hαβ11 : α * β ^ 11 = 1 := by
    calc α * β ^ 11 = (α * β) * β ^ 10 := by ring
      _ = 1 := by rw [hαβ, hβ10]; norm_num
  have hα1β11 : α ^ 1 * β ^ 11 = 1 := by simpa using hαβ11
  have hα5β15 : α ^ 5 * β ^ 15 = 1 := by
    calc α ^ 5 * β ^ 15 = (α * β) ^ 5 * β ^ 10 := by ring
      _ = 1 := by rw [hαβ, hβ10]; norm_num
  have hα25β5 : α ^ 25 * β ^ 5 = 1 := by
    calc α ^ 25 * β ^ 5 = α ^ 20 * (α * β) ^ 5 := by ring
      _ = 1 := by rw [hα20, hαβ]; norm_num
  have hα5β25 : α ^ 5 * β ^ 25 = 1 := by
    calc α ^ 5 * β ^ 25 = (α * β) ^ 5 * β ^ 20 := by ring
      _ = 1 := by rw [hαβ, hβ20]; norm_num
  have hα20β10 : α ^ 20 * β ^ 10 = 1 := by rw [hα20, hβ10]; norm_num
  have hα10β20 : α ^ 10 * β ^ 20 = 1 := by rw [hα10, hβ20]; norm_num
  have hα10β10 : α ^ 10 * β ^ 10 = 1 := by rw [hα10, hβ10]; norm_num
  have hmon (m n : ℕ) (hmn : α ^ m * β ^ n = 1) :
      α ^ m * z₁ ^ m * β ^ n * z₂ ^ n = z₁ ^ m * z₂ ^ n := by
    calc
      α ^ m * z₁ ^ m * β ^ n * z₂ ^ n =
          (α ^ m * β ^ n) * (z₁ ^ m * z₂ ^ n) := by ring
      _ = z₁ ^ m * z₂ ^ n := by rw [hmn]; ring
  have hmonFleft : α * z₁ * β ^ 11 * z₂ ^ 11 = z₁ * z₂ ^ 11 := by
    simpa using hmon 1 11 hα1β11
  have hmonFmiddle : α ^ 6 * z₁ ^ 6 * β ^ 6 * z₂ ^ 6 =
      z₁ ^ 6 * z₂ ^ 6 := hmon 6 6 hα6β6
  have hmonFright : α ^ 11 * z₁ ^ 11 * β * z₂ =
      z₁ ^ 11 * z₂ := by
    have hweight : α ^ 11 * β ^ 1 = 1 := by simpa using hα11β
    simpa using hmon 11 1 hweight
  refine ⟨?_, ?_, ?_⟩
  · simp only [kleinIcosahedralStandardVertexF, mul_pow]
    ring_nf
    rw [hmonFleft, hmonFmiddle, hmonFright]
  · simp only [kleinIcosahedralStandardFaceH, mul_pow]
    ring_nf
    rw [hα20, hβ20, hmon 15 5 hα15β5, hmon 10 10 hα10β10,
      hmon 5 15 hα5β15]
    ring
  · simp only [kleinIcosahedralStandardEdgeT, mul_pow]
    ring_nf
    rw [hα30, hβ30, hmon 25 5 hα25β5, hmon 20 10 hα20β10,
      hmon 10 20 hα10β20, hmon 5 25 hα5β25]
    ring

def kleinIcosahedralFaceH {R : Type*} [CommRing R] (z₁ z₂ : R) : R :=
  -(z₁ ^ 20 + z₂ ^ 20) + 228 * (z₁ ^ 15 * z₂ ^ 5 - z₁ ^ 5 * z₂ ^ 15) - 494 * z₁ ^ 10 * z₂ ^ 10

def kleinIcosahedralEdgeT {R : Type*} [CommRing R] (z₁ z₂ : R) : R :=
  (z₁ ^ 30 + z₂ ^ 30) + 522 * (z₁ ^ 25 * z₂ ^ 5 - z₁ ^ 5 * z₂ ^ 25) -
    10005 * (z₁ ^ 20 * z₂ ^ 10 + z₁ ^ 10 * z₂ ^ 20)

/-- The degree-12 Klein vertex form in the ordered coordinates used by the
literature generator matrices.  The current owner form is this form after
swapping its two arguments; the two conventions are kept explicit so a basis
intertwiner cannot silently identify them. -/
def kleinIcosahedralSourceVertexF (z₁ z₂ : ℂ) : ℂ :=
  kleinIcosahedralVertexF z₂ z₁

/-- The source-ordered degree-20 form in the same binary coordinates as
`kleinIcosahedralSourceVertexF`.  Keeping the argument permutation explicit
prevents the degree-12 form from silently using a different coordinate order
than the rest of Klein's invariant triple. -/
def kleinIcosahedralSourceFaceH (z₁ z₂ : ℂ) : ℂ :=
  kleinIcosahedralFaceH z₂ z₁

/-- The source-ordered degree-30 form in the same binary coordinates as the
source vertex and face forms. -/
def kleinIcosahedralSourceEdgeT (z₁ z₂ : ℂ) : ℂ :=
  kleinIcosahedralEdgeT z₂ z₁

theorem kleinIcosahedralVertexF_source_swap (z₁ z₂ : ℂ) :
    kleinIcosahedralSourceVertexF z₁ z₂ =
      z₁ * z₂ * (-z₁ ^ 10 + 11 * z₁ ^ 5 * z₂ ^ 5 + z₂ ^ 10) := by
  simp [kleinIcosahedralSourceVertexF, kleinIcosahedralVertexF]
  ring

/-- The defining two-dimensional action of `SU2` on binary-form variables. -/
def kleinBinaryAction (g : SU2) (z₁ z₂ : ℂ) : ℂ × ℂ :=
  (((g : Mat2C) 0 0) * z₁ + ((g : Mat2C) 0 1) * z₂,
   ((g : Mat2C) 1 0) * z₁ + ((g : Mat2C) 1 1) * z₂)

/-- The order-four icosahedral generator acts on the binary variables by
`(z₁,z₂) ↦ (z₂,-z₁)`. -/
theorem icosianGenB_kleinBinaryAction (z₁ z₂ : ℂ) :
    kleinBinaryAction icosianGenB z₁ z₂ = (z₂, -z₁) := by
  apply Prod.ext <;>
    simp [kleinBinaryAction, icosianGenB, su2QuatJ, quatToSU2_coe, quatToMat]

private theorem kleinIcosahedralSourceVertexF_act_genB (z₁ z₂ : ℂ) :
    kleinIcosahedralSourceVertexF z₂ (-z₁) = kleinIcosahedralSourceVertexF z₁ z₂ := by
  rw [kleinIcosahedralVertexF_source_swap]
  rw [kleinIcosahedralVertexF_source_swap]
  ring

/-- The source-ordered degree-12 Klein form is fixed by the actual order-four
binary generator.  Keeping this theorem on the source-oriented form exposes
the coordinate convention that the owner form's counterexample detects. -/
theorem kleinIcosahedralSourceVertexF_invariant_under_genB (z₁ z₂ : ℂ) :
    kleinIcosahedralSourceVertexF
        (kleinBinaryAction icosianGenB z₁ z₂).1
        (kleinBinaryAction icosianGenB z₁ z₂).2 =
      kleinIcosahedralSourceVertexF z₁ z₂ := by
  rw [icosianGenB_kleinBinaryAction]
  exact kleinIcosahedralSourceVertexF_act_genB z₁ z₂

/-- The order-ten generator's actual action on binary variables, with coefficients in
the golden quadratic extension. Keeping this action explicit makes subsequent invariant
claims check the chosen matrix convention rather than assuming a projective action. -/
theorem icosianGenA_kleinBinaryAction (z₁ z₂ : ℂ) :
    kleinBinaryAction icosianGenA z₁ z₂ =
      (((Real.goldenRatio / 2 : ℝ) + ((Real.goldenRatio - 1) / 2 : ℝ) * Complex.I) * z₁ +
          (1 / 2 : ℝ) * z₂,
        (-(1 / 2 : ℝ)) * z₁ +
          ((Real.goldenRatio / 2 : ℝ) - ((Real.goldenRatio - 1) / 2 : ℝ) * Complex.I) * z₂) := by
  apply Prod.ext <;>
    simp [kleinBinaryAction, icosianGenA, quatToSU2_coe, quatToMat]

/-! The order-four change-of-basis calculation is recorded independently of
the golden-ratio generator. Its coefficients are derived from the real
parameter below; no coefficient identities are assumed in the matrix theorem. -/

noncomputable def kleinBinaryBasisAlpha : ℝ :=
  (Real.sqrt (Real.goldenRatio ^ 2 + 1) - 1) / Real.goldenRatio

private theorem kleinBinaryBasisAlpha_quadratic_relation :
    Real.goldenRatio * kleinBinaryBasisAlpha ^ 2 +
      2 * kleinBinaryBasisAlpha = Real.goldenRatio := by
  have hφ : Real.goldenRatio ≠ 0 := Real.goldenRatio_pos.ne'
  let q := Real.sqrt (Real.goldenRatio ^ 2 + 1)
  have hq : q ^ 2 = Real.goldenRatio ^ 2 + 1 := by
    dsimp [q]
    rw [Real.sq_sqrt (by positivity)]
  have hqα : Real.goldenRatio * kleinBinaryBasisAlpha = q - 1 := by
    dsimp [q, kleinBinaryBasisAlpha]
    field_simp [hφ]
  have hmul : Real.goldenRatio ^ 2 * kleinBinaryBasisAlpha ^ 2 +
      2 * Real.goldenRatio * kleinBinaryBasisAlpha = Real.goldenRatio ^ 2 := by
    calc Real.goldenRatio ^ 2 * kleinBinaryBasisAlpha ^ 2 +
          2 * Real.goldenRatio * kleinBinaryBasisAlpha
        = (Real.goldenRatio * kleinBinaryBasisAlpha) ^ 2 +
            2 * (Real.goldenRatio * kleinBinaryBasisAlpha) := by ring
      _ = (q - 1) ^ 2 + 2 * (q - 1) := by rw [hqα]
      _ = q ^ 2 - 1 := by ring
      _ = Real.goldenRatio ^ 2 := by rw [hq]; ring
  have hcancel : Real.goldenRatio *
      (Real.goldenRatio * kleinBinaryBasisAlpha ^ 2 +
        2 * kleinBinaryBasisAlpha - Real.goldenRatio) = 0 := by
    nlinarith [hmul]
  rcases mul_eq_zero.mp hcancel with hzero | hrelation
  · exact (hφ hzero).elim
  · linarith

private theorem kleinBinaryBasisAlpha_cartan_relation :
    kleinBinaryBasisAlpha ^ 2 +
      2 * kleinBinaryBasisAlpha * (Real.goldenRatio - 1) = 1 := by
  have hφ : Real.goldenRatio ≠ 0 := Real.goldenRatio_pos.ne'
  have hφmul : Real.goldenRatio * (Real.goldenRatio - 1) = 1 := by
    nlinarith [Real.goldenRatio_sq]
  have hscaled : Real.goldenRatio *
      (kleinBinaryBasisAlpha ^ 2 +
        2 * kleinBinaryBasisAlpha * (Real.goldenRatio - 1) - 1) = 0 := by
    calc Real.goldenRatio *
          (kleinBinaryBasisAlpha ^ 2 +
            2 * kleinBinaryBasisAlpha * (Real.goldenRatio - 1) - 1)
        = Real.goldenRatio * kleinBinaryBasisAlpha ^ 2 +
            2 * kleinBinaryBasisAlpha *
              (Real.goldenRatio * (Real.goldenRatio - 1)) - Real.goldenRatio := by ring
      _ = Real.goldenRatio * kleinBinaryBasisAlpha ^ 2 +
            2 * kleinBinaryBasisAlpha - Real.goldenRatio := by rw [hφmul]; ring
      _ = 0 := by rw [kleinBinaryBasisAlpha_quadratic_relation]; ring
  rcases mul_eq_zero.mp hscaled with hzero | hrelation
  · exact (hφ hzero).elim
  · linarith

noncomputable def kleinBinaryBasisChange : Mat2C :=
  !![(1 : ℂ), -(kleinBinaryBasisAlpha : ℂ) * Complex.I;
    -(kleinBinaryBasisAlpha : ℂ), -Complex.I]

private theorem kleinBinaryBasisChange_det_ne_zero :
    Matrix.det kleinBinaryBasisChange ≠ 0 := by
  have hα : 1 + kleinBinaryBasisAlpha ^ 2 ≠ 0 := by positivity
  have hαc : (1 : ℂ) + (kleinBinaryBasisAlpha : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast hα
  rw [Matrix.det_fin_two]
  simp only [kleinBinaryBasisChange, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have hdet : (1 : ℂ) * (-Complex.I) -
      (-(kleinBinaryBasisAlpha : ℂ) * Complex.I) *
        (-(kleinBinaryBasisAlpha : ℂ)) =
      -Complex.I * ((1 : ℂ) + (kleinBinaryBasisAlpha : ℂ) ^ 2) := by ring
  rw [hdet]
  exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hαc

/-- The displayed intertwiner is a genuine complex matrix basis change. -/
theorem kleinBinaryBasisChange_isUnit : IsUnit kleinBinaryBasisChange := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  exact isUnit_iff_ne_zero.mpr kleinBinaryBasisChange_det_ne_zero

noncomputable def kleinBinaryStandardB_U : ℝ :=
  2 * kleinBinaryBasisAlpha / (1 + kleinBinaryBasisAlpha ^ 2)

noncomputable def kleinBinaryStandardB_V : ℝ :=
  (1 - kleinBinaryBasisAlpha ^ 2) / (1 + kleinBinaryBasisAlpha ^ 2)

noncomputable def kleinBinaryStandardGenB : Mat2C :=
  !![kleinBinaryStandardB_U * Complex.I, kleinBinaryStandardB_V * Complex.I;
    kleinBinaryStandardB_V * Complex.I, -kleinBinaryStandardB_U * Complex.I]

noncomputable def kleinBinaryStandardGenA : Mat2C :=
  !![((Real.goldenRatio / 2 : ℝ) +
      ((Real.goldenRatio - 1 + kleinBinaryBasisAlpha) / 2 : ℝ) * Complex.I), 0;
    0, ((Real.goldenRatio / 2 : ℝ) -
      ((Real.goldenRatio - 1 + kleinBinaryBasisAlpha) / 2 : ℝ) * Complex.I)]

private theorem kleinBinaryStandardA_offDiagonal_relation :
    (1 / 2 : ℝ) - kleinBinaryBasisAlpha *
        ((Real.goldenRatio - 1) / 2) =
      kleinBinaryBasisAlpha *
        ((Real.goldenRatio - 1 + kleinBinaryBasisAlpha) / 2) := by
  nlinarith [kleinBinaryBasisAlpha_cartan_relation]

/-- The order-ten generator is diagonal in the same explicitly changed binary
basis. Its off-diagonal entries reduce to the proved Cartan relation of the
real basis parameter. -/
theorem icosianGenA_binaryBasisIntertwining :
    kleinBinaryBasisChange * (icosianGenA : Mat2C) =
      kleinBinaryStandardGenA * kleinBinaryBasisChange := by
  have h_off := kleinBinaryStandardA_offDiagonal_relation
  simp [Real.goldenRatio] at h_off
  have h00 : (icosianGenA : Mat2C) 0 0 =
      ((Real.goldenRatio / 2 : ℝ) +
        ((Real.goldenRatio - 1) / 2 : ℝ) * Complex.I) := by
    have h := congrArg Prod.fst (icosianGenA_kleinBinaryAction 1 0)
    simpa [kleinBinaryAction] using h
  have h01 : (icosianGenA : Mat2C) 0 1 = (1 / 2 : ℂ) := by
    have h := congrArg Prod.fst (icosianGenA_kleinBinaryAction 0 1)
    simpa [kleinBinaryAction] using h
  have h10 : (icosianGenA : Mat2C) 1 0 = (-(1 / 2 : ℂ)) := by
    have h := congrArg Prod.snd (icosianGenA_kleinBinaryAction 1 0)
    simpa [kleinBinaryAction] using h
  have h11 : (icosianGenA : Mat2C) 1 1 =
      ((Real.goldenRatio / 2 : ℝ) -
        ((Real.goldenRatio - 1) / 2 : ℝ) * Complex.I) := by
    have h := congrArg Prod.snd (icosianGenA_kleinBinaryAction 0 1)
    simpa [kleinBinaryAction] using h
  apply ext_mat2C
  · simp only [kleinBinaryBasisChange, kleinBinaryStandardGenA,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, h00, h10]
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
    · simp [Complex.mul_re, Complex.mul_im] <;> ring
  · simp only [kleinBinaryBasisChange, kleinBinaryStandardGenA,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, h01, h11]
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im, Real.goldenRatio] <;> linarith [h_off]
    · simp [Complex.mul_re, Complex.mul_im] <;> ring
  · simp only [kleinBinaryBasisChange, kleinBinaryStandardGenA,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, h00, h10]
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im, Real.goldenRatio] <;> linarith [h_off]
    · simp [Complex.mul_re, Complex.mul_im] <;> linarith [h_off]
  · simp only [kleinBinaryBasisChange, kleinBinaryStandardGenA,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, h01, h11]
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im] <;> ring
    · simp [Complex.mul_re, Complex.mul_im]

private lemma kleinBinaryBasisDenom_ne_zero :
    1 + kleinBinaryBasisAlpha ^ 2 ≠ 0 := by positivity

/-- In the standard order-four representative, the two real coefficients are
related by the golden ratio.  This is the coefficient identity needed to
reduce its action on homogeneous binary forms to the Cartan relation for the
chosen basis parameter. -/
theorem kleinBinaryStandardB_U_eq_goldenRatio_mul_V :
    kleinBinaryStandardB_U =
      Real.goldenRatio * kleinBinaryStandardB_V := by
  have hα := kleinBinaryBasisAlpha_quadratic_relation
  have hcoef : 2 * kleinBinaryBasisAlpha =
      Real.goldenRatio * (1 - kleinBinaryBasisAlpha ^ 2) := by
    nlinarith [hα]
  dsimp [kleinBinaryStandardB_U, kleinBinaryStandardB_V]
  rw [hcoef]
  ring

/-- The standard order-four coefficients form a unit vector. -/
theorem kleinBinaryStandardB_U_sq_add_V_sq :
    kleinBinaryStandardB_U ^ 2 + kleinBinaryStandardB_V ^ 2 = 1 := by
  have hden : 1 + kleinBinaryBasisAlpha ^ 2 ≠ 0 :=
    kleinBinaryBasisDenom_ne_zero
  dsimp [kleinBinaryStandardB_U, kleinBinaryStandardB_V]
  field_simp [hden]
  ring

private lemma kleinBinaryStandardB_first_coefficient :
    (2 * kleinBinaryBasisAlpha / (1 + kleinBinaryBasisAlpha ^ 2)) -
      ((1 - kleinBinaryBasisAlpha ^ 2) / (1 + kleinBinaryBasisAlpha ^ 2)) *
        kleinBinaryBasisAlpha = kleinBinaryBasisAlpha := by
  have hden := kleinBinaryBasisDenom_ne_zero
  field_simp [hden]
  ring

private lemma kleinBinaryStandardB_second_coefficient :
    (2 * kleinBinaryBasisAlpha / (1 + kleinBinaryBasisAlpha ^ 2)) *
        kleinBinaryBasisAlpha +
      (1 - kleinBinaryBasisAlpha ^ 2) / (1 + kleinBinaryBasisAlpha ^ 2) = 1 := by
  have hden := kleinBinaryBasisDenom_ne_zero
  field_simp [hden]
  ring

/-- The exact order-four generator matrix after the explicit binary-basis
change. The two real coefficient identities are proved above from their
definitions and discharged here over the complex matrix carrier. -/
theorem icosianGenB_binaryBasisIntertwining :
    kleinBinaryBasisChange * (icosianGenB : Mat2C) =
      kleinBinaryStandardGenB * kleinBinaryBasisChange := by
  have h₁ := kleinBinaryStandardB_first_coefficient
  have h₂ := kleinBinaryStandardB_second_coefficient
  have h₁c : (kleinBinaryStandardB_U : ℂ) -
      (kleinBinaryStandardB_V : ℂ) * (kleinBinaryBasisAlpha : ℂ) =
        (kleinBinaryBasisAlpha : ℂ) := by exact_mod_cast h₁
  have h₂c : (kleinBinaryStandardB_U : ℂ) *
      (kleinBinaryBasisAlpha : ℂ) + (kleinBinaryStandardB_V : ℂ) = 1 := by
    exact_mod_cast h₂
  simp only [kleinBinaryStandardB_U, kleinBinaryStandardB_V] at h₁c h₂c
  push_cast at h₁c h₂c
  ring_nf at h₁c h₂c
  have h₁cI : Complex.I * (kleinBinaryBasisAlpha : ℂ) *
      (1 + (kleinBinaryBasisAlpha : ℂ) ^ 2)⁻¹ +
      Complex.I * (kleinBinaryBasisAlpha : ℂ) ^ 3 *
        (1 + (kleinBinaryBasisAlpha : ℂ) ^ 2)⁻¹ =
      Complex.I * (kleinBinaryBasisAlpha : ℂ) := by
    have h := congrArg (fun z : ℂ => Complex.I * z) h₁c
    simpa [mul_add, mul_assoc] using h
  have h₂cI : Complex.I * (kleinBinaryBasisAlpha : ℂ) ^ 2 *
      (1 + (kleinBinaryBasisAlpha : ℂ) ^ 2)⁻¹ +
      Complex.I * (1 + (kleinBinaryBasisAlpha : ℂ) ^ 2)⁻¹ = Complex.I := by
    have h := congrArg (fun z : ℂ => Complex.I * z) h₂c
    simpa [mul_add, mul_assoc] using h
  apply ext_mat2C
  · simp only [kleinBinaryBasisChange, kleinBinaryStandardGenB, kleinBinaryStandardB_U,
      kleinBinaryStandardB_V, icosianGenB, su2QuatJ, quatToSU2_coe,
      quatToMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    ring_nf
    simpa [mul_assoc, mul_comm, mul_left_comm] using h₁cI.symm
  · simp only [kleinBinaryBasisChange, kleinBinaryStandardGenB, kleinBinaryStandardB_U,
      kleinBinaryStandardB_V, icosianGenB,
      su2QuatJ, quatToSU2_coe, quatToMat, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    linear_combination -h₂c
  · simp only [kleinBinaryBasisChange, kleinBinaryStandardGenB, kleinBinaryStandardB_U,
      kleinBinaryStandardB_V, icosianGenB,
      su2QuatJ, quatToSU2_coe, quatToMat, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    ring_nf
    simpa [mul_assoc, mul_comm, mul_left_comm] using h₂cI.symm
  · simp only [kleinBinaryBasisChange, kleinBinaryStandardGenB, kleinBinaryStandardB_U,
      kleinBinaryStandardB_V, icosianGenB,
      su2QuatJ, quatToSU2_coe, quatToMat, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    linear_combination h₁c

/-- The order-ten generator is conjugate to its diagonal representative in
the verified binary basis. The inverse is Lean's matrix nonsingular inverse,
whose two-sided cancellation follows from the determinant nonvanishing proved
for the basis matrix above. -/
theorem icosianGenA_binaryBasisConjugacy :
    kleinBinaryBasisChange * (icosianGenA : Mat2C) *
        kleinBinaryBasisChange⁻¹ = kleinBinaryStandardGenA := by
  have hdetUnit : IsUnit (Matrix.det kleinBinaryBasisChange) :=
    (Matrix.isUnit_iff_isUnit_det kleinBinaryBasisChange).mp kleinBinaryBasisChange_isUnit
  calc
    kleinBinaryBasisChange * (icosianGenA : Mat2C) *
        kleinBinaryBasisChange⁻¹ =
      (kleinBinaryStandardGenA * kleinBinaryBasisChange) *
        kleinBinaryBasisChange⁻¹ := by rw [← icosianGenA_binaryBasisIntertwining]
    _ = kleinBinaryStandardGenA := by
      exact Matrix.mul_nonsing_inv_cancel_right
        (A := kleinBinaryBasisChange) kleinBinaryStandardGenA hdetUnit

/-- The order-four generator's standard representative is obtained by the
same genuine basis conjugation, without assuming an inverse law as a theorem
hypothesis. -/
theorem icosianGenB_binaryBasisConjugacy :
    kleinBinaryBasisChange * (icosianGenB : Mat2C) *
        kleinBinaryBasisChange⁻¹ = kleinBinaryStandardGenB := by
  have hdetUnit : IsUnit (Matrix.det kleinBinaryBasisChange) :=
    (Matrix.isUnit_iff_isUnit_det kleinBinaryBasisChange).mp kleinBinaryBasisChange_isUnit
  calc
    kleinBinaryBasisChange * (icosianGenB : Mat2C) *
        kleinBinaryBasisChange⁻¹ =
      (kleinBinaryStandardGenB * kleinBinaryBasisChange) *
        kleinBinaryBasisChange⁻¹ := by rw [← icosianGenB_binaryBasisIntertwining]
    _ = kleinBinaryStandardGenB := by
      exact Matrix.mul_nonsing_inv_cancel_right
        (A := kleinBinaryBasisChange) kleinBinaryStandardGenB hdetUnit

/-- The linear action of a complex two-by-two matrix on binary-form variables. -/
def kleinBinaryMatrixAction (A : Mat2C) (z : ℂ × ℂ) : ℂ × ℂ :=
  (A 0 0 * z.1 + A 0 1 * z.2, A 1 0 * z.1 + A 1 1 * z.2)

private theorem kleinBinaryMatrixAction_mul (A B : Mat2C) (z : ℂ × ℂ) :
    kleinBinaryMatrixAction (A * B) z =
      kleinBinaryMatrixAction A (kleinBinaryMatrixAction B z) := by
  apply Prod.ext <;>
    simp [kleinBinaryMatrixAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Transport the source-coordinate vertex form into the verified standard
binary basis. This definition uses the actual inverse matrix of the proved
intertwiner, rather than an assumed coordinate substitution. -/
def kleinIcosahedralVertexF_in_standard_basis (z : ℂ × ℂ) : ℂ :=
  let w := kleinBinaryMatrixAction kleinBinaryBasisChange⁻¹ z
  kleinIcosahedralSourceVertexF w.1 w.2

/-- The transported vertex form is invariant under the standard order-four
generator. The proof is the conjugacy calculation on the two-dimensional
operator representation followed by the source-form invariance theorem. -/
theorem kleinIcosahedralVertexF_in_standard_basis_invariant_under_genB
    (z : ℂ × ℂ) :
    kleinIcosahedralVertexF_in_standard_basis
        (kleinBinaryMatrixAction kleinBinaryStandardGenB z) =
      kleinIcosahedralVertexF_in_standard_basis z := by
  let C := kleinBinaryBasisChange
  let G : Mat2C := icosianGenB
  have hCdet : IsUnit (Matrix.det C) :=
    (Matrix.isUnit_iff_isUnit_det C).mp kleinBinaryBasisChange_isUnit
  have hCiC : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hCdet
  have hconj : C * G * C⁻¹ = kleinBinaryStandardGenB := by
    dsimp [C, G]
    exact icosianGenB_binaryBasisConjugacy
  have htransport : C⁻¹ * kleinBinaryStandardGenB = G * C⁻¹ := by
    calc
      C⁻¹ * kleinBinaryStandardGenB = C⁻¹ * (C * G * C⁻¹) := by rw [hconj]
      _ = G * C⁻¹ := by
        calc
          C⁻¹ * (C * G * C⁻¹) = (C⁻¹ * C) * G * C⁻¹ := by noncomm_ring
          _ = G * C⁻¹ := by rw [hCiC]; noncomm_ring
  change kleinIcosahedralSourceVertexF
      (kleinBinaryMatrixAction C⁻¹ (kleinBinaryMatrixAction kleinBinaryStandardGenB z)).1
      (kleinBinaryMatrixAction C⁻¹ (kleinBinaryMatrixAction kleinBinaryStandardGenB z)).2 = _
  rw [← kleinBinaryMatrixAction_mul, htransport, kleinBinaryMatrixAction_mul]
  have hG : ∀ w, kleinBinaryMatrixAction G w = (w.2, -w.1) := by
    intro w
    dsimp [G, kleinBinaryMatrixAction]
    simpa [kleinBinaryAction] using icosianGenB_kleinBinaryAction w.1 w.2
  rw [hG]
  have hInv := kleinIcosahedralSourceVertexF_invariant_under_genB
    (kleinBinaryMatrixAction C⁻¹ z).1 (kleinBinaryMatrixAction C⁻¹ z).2
  rw [icosianGenB_kleinBinaryAction] at hInv
  simpa [kleinIcosahedralVertexF_in_standard_basis] using hInv

private lemma diagonalComplexMatrix_pow (a b : ℂ) (n : ℕ) :
    (!![a, 0; 0, b] : Mat2C) ^ n = !![a ^ n, 0; 0, b ^ n] := by
  induction n with
  | zero => ext i j <;> fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
      rw [pow_succ, ih]
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

/-- The diagonal generator's eigenvalues inherit the order-ten relation from the original
SU(2) generator by the proved basis conjugacy. -/
private lemma kleinBinaryStandardGenA_pow_five :
    kleinBinaryStandardGenA ^ 5 = -(1 : Mat2C) := by
  let C := kleinBinaryBasisChange
  let G : Mat2C := icosianGenA
  let D := kleinBinaryStandardGenA
  have hCdet : IsUnit (Matrix.det C) := by
    exact (Matrix.isUnit_iff_isUnit_det C).mp kleinBinaryBasisChange_isUnit
  have hCC : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hCdet
  have hG5 : G ^ 5 = -(1 : Mat2C) := by
    have h := congrArg (fun g : SU2 => (g : Mat2C)) icosianGenA_pow_five
    simpa [G, negOneSU2_coe] using h
  have hinter : D * C = C * G := by
    dsimp [D, C, G]
    exact icosianGenA_binaryBasisIntertwining.symm
  have hpowers : ∀ n : ℕ, D ^ n * C = C * G ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          D ^ (n + 1) * C = D ^ n * (D * C) := by rw [pow_succ]; noncomm_ring
          _ = D ^ n * (C * G) := by rw [hinter]
          _ = (D ^ n * C) * G := by noncomm_ring
          _ = (C * G ^ n) * G := by rw [ih]
          _ = C * G ^ (n + 1) := by rw [pow_succ]; noncomm_ring
  calc
    D ^ 5 = D ^ 5 * (C * C⁻¹) := by rw [hCC, mul_one]
    _ = (D ^ 5 * C) * C⁻¹ := by noncomm_ring
    _ = (C * G ^ 5) * C⁻¹ := by rw [hpowers 5]
    _ = (C * (-(1 : Mat2C))) * C⁻¹ := by rw [hG5]
    _ = -(1 : Mat2C) := by simp [Matrix.mul_assoc, hCC]

/-- In the verified diagonal binary basis, the fifth power of the order-ten
generator acts as the central spinor involution and its tenth power acts as the
identity on binary variables. This is the concrete `Sym^1` carrier statement
underlying the odd-degree sign law. -/
theorem kleinBinaryStandardGenA_central_power_action (z : ℂ × ℂ) :
    kleinBinaryMatrixAction (kleinBinaryStandardGenA ^ 5) z = (-z.1, -z.2) ∧
    kleinBinaryMatrixAction (kleinBinaryStandardGenA ^ 10) z = z := by
  have h5 : kleinBinaryStandardGenA ^ 5 = -(1 : Mat2C) :=
    kleinBinaryStandardGenA_pow_five
  constructor
  · rw [h5]
    simp [kleinBinaryMatrixAction]
  · have h10 : kleinBinaryStandardGenA ^ 10 = (1 : Mat2C) := by
      calc
        kleinBinaryStandardGenA ^ 10 = (kleinBinaryStandardGenA ^ 5) ^ 2 := by
          rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul]
        _ = (-(1 : Mat2C)) ^ 2 := by rw [h5]
        _ = 1 := by simp
    rw [h10]
    simp [kleinBinaryMatrixAction]

/-- Odd homogeneous binary forms of degree five acquire the central minus sign
after five applications of the diagonal order-ten generator. The homogeneity
law is explicit, so this theorem applies to genuine degree-five forms without
assuming anything about a separate resolvent tuple. -/
theorem kleinBinaryStandardGenA_fifth_power_negates_homogeneousQuintic
    (P : ℂ → ℂ → ℂ)
    (hhom : ∀ (c z₁ z₂ : ℂ), P (c * z₁) (c * z₂) = c ^ 5 * P z₁ z₂)
    (z₁ z₂ : ℂ) :
    P (kleinBinaryMatrixAction (kleinBinaryStandardGenA ^ 5) (z₁, z₂)).1
      (kleinBinaryMatrixAction (kleinBinaryStandardGenA ^ 5) (z₁, z₂)).2 =
        -P z₁ z₂ := by
  rw [(kleinBinaryStandardGenA_central_power_action (z₁, z₂)).1]
  calc
    P (-z₁) (-z₂) = P ((-1 : ℂ) * z₁) ((-1 : ℂ) * z₂) := by simp
    _ = (-1 : ℂ) ^ 5 * P z₁ z₂ := hhom (-1) z₁ z₂
    _ = -P z₁ z₂ := by norm_num

private lemma kleinBinaryStandardGenA_det :
    Matrix.det kleinBinaryStandardGenA = 1 := by
  have hGdet : Matrix.det (icosianGenA : Mat2C) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp icosianGenA.property).2
  have hCdet : IsUnit (Matrix.det kleinBinaryBasisChange) := by
    exact (Matrix.isUnit_iff_isUnit_det kleinBinaryBasisChange).mp
      kleinBinaryBasisChange_isUnit
  have hCC : kleinBinaryBasisChange * kleinBinaryBasisChange⁻¹ = 1 :=
    Matrix.mul_nonsing_inv kleinBinaryBasisChange hCdet
  have hdetCC : Matrix.det kleinBinaryBasisChange *
      Matrix.det kleinBinaryBasisChange⁻¹ = 1 := by
    have h := congrArg Matrix.det hCC
    simpa only [Matrix.det_mul, Matrix.det_one] using h
  rw [← icosianGenA_binaryBasisConjugacy, Matrix.det_mul, Matrix.det_mul]
  calc
    Matrix.det kleinBinaryBasisChange * Matrix.det (icosianGenA : Mat2C) *
        Matrix.det kleinBinaryBasisChange⁻¹ =
      (Matrix.det kleinBinaryBasisChange * Matrix.det kleinBinaryBasisChange⁻¹) *
        Matrix.det (icosianGenA : Mat2C) := by ring
    _ = 1 := by rw [hdetCC, hGdet]; ring

private lemma kleinBinaryStandardGenA_diagonal_relations :
    (kleinBinaryStandardGenA 0 0) ^ 5 = -1 ∧
    (kleinBinaryStandardGenA 1 1) ^ 5 = -1 ∧
    kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1 = 1 := by
  have hpow := kleinBinaryStandardGenA_pow_five
  have hdiag : kleinBinaryStandardGenA =
      !![kleinBinaryStandardGenA 0 0, 0; 0, kleinBinaryStandardGenA 1 1] := by
    apply ext_mat2C <;> simp [kleinBinaryStandardGenA]
  have hpow' := hpow
  rw [hdiag, diagonalComplexMatrix_pow] at hpow'
  have h00 := congrArg (fun M : Mat2C => M 0 0) hpow'
  have h11 := congrArg (fun M : Mat2C => M 1 1) hpow'
  have hdet := kleinBinaryStandardGenA_det
  rw [Matrix.det_fin_two] at hdet
  simp only [kleinBinaryStandardGenA, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hdet
  refine ⟨?_, ?_, ?_⟩
  · simpa using h00
  · simpa using h11
  · simpa [kleinBinaryStandardGenA] using hdet

/-- The basis-adapted degree-12, degree-20, and degree-30 forms are all fixed
by the owner's actual diagonal order-ten generator. This establishes one
generator half of the corrected Klein invariant triple. -/
theorem kleinIcosahedralStandardForms_invariant_under_standardGenA
    (z₁ z₂ : ℂ) :
    kleinIcosahedralStandardVertexF
        (kleinBinaryStandardGenA 0 0 * z₁)
        (kleinBinaryStandardGenA 1 1 * z₂) =
      kleinIcosahedralStandardVertexF z₁ z₂ ∧
    kleinIcosahedralStandardFaceH
        (kleinBinaryStandardGenA 0 0 * z₁)
        (kleinBinaryStandardGenA 1 1 * z₂) =
      kleinIcosahedralStandardFaceH z₁ z₂ ∧
    kleinIcosahedralStandardEdgeT
        (kleinBinaryStandardGenA 0 0 * z₁)
        (kleinBinaryStandardGenA 1 1 * z₂) =
      kleinIcosahedralStandardEdgeT z₁ z₂ := by
  rcases kleinBinaryStandardGenA_diagonal_relations with ⟨hα5, hβ5, hαβ⟩
  exact kleinIcosahedralStandardForms_invariant_under_diagonal
    (kleinBinaryStandardGenA 0 0) (kleinBinaryStandardGenA 1 1)
    hα5 hβ5 hαβ z₁ z₂

/-- Each diagonal eigenvalue of the checked order-ten generator has fifth
power `-1`; this is the scalar central action used by the five-step orbit. -/
theorem kleinBinaryStandardGenA_eigenvalues_fifth_power :
    (kleinBinaryStandardGenA 0 0) ^ 5 = -1 ∧
    (kleinBinaryStandardGenA 1 1) ^ 5 = -1 := by
  exact ⟨kleinBinaryStandardGenA_diagonal_relations.1,
    kleinBinaryStandardGenA_diagonal_relations.2.1⟩

/-- In the diagonalized binary coordinates, the classical degree-12 vertex form is
fixed by the order-ten generator. The eigenvalue identities are derived above from
the proved intertwining and the SU(2) relation, rather than supplied as assumptions. -/
theorem kleinVertexF_invariant_under_standardGenA (z₁ z₂ : ℂ) :
    kleinIcosahedralVertexF
      (kleinBinaryStandardGenA 0 0 * z₁)
      (kleinBinaryStandardGenA 1 1 * z₂) =
    kleinIcosahedralVertexF z₁ z₂ := by
  rcases kleinBinaryStandardGenA_diagonal_relations with ⟨hα5, hβ5, hαβ⟩
  have hα10 : (kleinBinaryStandardGenA 0 0) ^ 10 = 1 := by
    calc
      (kleinBinaryStandardGenA 0 0) ^ 10 =
          ((kleinBinaryStandardGenA 0 0) ^ 5) ^ 2 := by
            rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul]
      _ = (-1 : ℂ) ^ 2 := by rw [hα5]
      _ = 1 := by norm_num
  have hβ10 : (kleinBinaryStandardGenA 1 1) ^ 10 = 1 := by
    calc
      (kleinBinaryStandardGenA 1 1) ^ 10 =
          ((kleinBinaryStandardGenA 1 1) ^ 5) ^ 2 := by
            rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul]
      _ = (-1 : ℂ) ^ 2 := by rw [hβ5]
      _ = 1 := by norm_num
  have hweight₁₁ :
      kleinBinaryStandardGenA 0 0 ^ 11 * kleinBinaryStandardGenA 1 1 = 1 := by
    calc
      kleinBinaryStandardGenA 0 0 ^ 11 * kleinBinaryStandardGenA 1 1 =
          kleinBinaryStandardGenA 0 0 ^ 10 *
            (kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1) := by ring
      _ = 1 := by rw [hα10, hαβ]; ring
  have hweight₆₆ :
      kleinBinaryStandardGenA 0 0 ^ 6 * kleinBinaryStandardGenA 1 1 ^ 6 = 1 := by
    rw [← mul_pow, hαβ]
    norm_num
  have hweight₁₁' :
      kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1 ^ 11 = 1 := by
    calc
      kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1 ^ 11 =
          (kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1) *
            kleinBinaryStandardGenA 1 1 ^ 10 := by ring
      _ = 1 := by rw [hαβ, hβ10]; ring
  have hweight₁₂₁ :
      kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1 *
        kleinBinaryStandardGenA 0 0 ^ 10 = 1 := by
    calc
      _ = kleinBinaryStandardGenA 0 0 ^ 11 * kleinBinaryStandardGenA 1 1 := by ring
      _ = 1 := hweight₁₁
  have hweight₁₂₂ :
      kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1 *
        kleinBinaryStandardGenA 0 0 ^ 5 * kleinBinaryStandardGenA 1 1 ^ 5 = 1 := by
    calc
      _ = kleinBinaryStandardGenA 0 0 ^ 6 * kleinBinaryStandardGenA 1 1 ^ 6 := by ring
      _ = 1 := hweight₆₆
  have hweight₁₂₃ :
      kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1 *
        kleinBinaryStandardGenA 1 1 ^ 10 = 1 := by
    calc
      _ = kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1 ^ 11 := by ring
      _ = 1 := hweight₁₁'
  simp only [kleinIcosahedralVertexF]
  calc
    _ = (kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1 *
          kleinBinaryStandardGenA 0 0 ^ 10) * (z₁ * z₂ * z₁ ^ 10) +
        11 * (kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1 *
          kleinBinaryStandardGenA 0 0 ^ 5 * kleinBinaryStandardGenA 1 1 ^ 5) *
          (z₁ * z₂ * z₁ ^ 5 * z₂ ^ 5) -
        (kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1 *
          kleinBinaryStandardGenA 1 1 ^ 10) * (z₁ * z₂ * z₂ ^ 10) := by ring
    _ = z₁ * z₂ * z₁ ^ 10 + 11 * (z₁ * z₂ * z₁ ^ 5 * z₂ ^ 5) -
        z₁ * z₂ * z₂ ^ 10 := by rw [hweight₁₂₁, hweight₁₂₂, hweight₁₂₃]; ring
    _ = kleinIcosahedralVertexF z₁ z₂ := by simp only [kleinIcosahedralVertexF]; ring

/-- The source-ordered Klein degree-12 form is invariant under the diagonal
order-ten representative. The three monomial weights are consequences of the
proved fifth-power and determinant relations; this does not identify the
source polynomial with the owner's swapped generator convention. -/
theorem kleinIcosahedralSourceVertexF_invariant_under_standardGenA (z₁ z₂ : ℂ) :
    kleinIcosahedralSourceVertexF
        (kleinBinaryStandardGenA 0 0 * z₁)
        (kleinBinaryStandardGenA 1 1 * z₂) =
      kleinIcosahedralSourceVertexF z₁ z₂ := by
  rcases kleinBinaryStandardGenA_diagonal_relations with ⟨hα5, hβ5, hαβ⟩
  have hα10 : (kleinBinaryStandardGenA 0 0) ^ 10 = 1 := by
    calc
      (kleinBinaryStandardGenA 0 0) ^ 10 =
          ((kleinBinaryStandardGenA 0 0) ^ 5) ^ 2 := by
            rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul]
      _ = (-1 : ℂ) ^ 2 := by rw [hα5]
      _ = 1 := by norm_num
  have hβ10 : (kleinBinaryStandardGenA 1 1) ^ 10 = 1 := by
    calc
      (kleinBinaryStandardGenA 1 1) ^ 10 =
          ((kleinBinaryStandardGenA 1 1) ^ 5) ^ 2 := by
            rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul]
      _ = (-1 : ℂ) ^ 2 := by rw [hβ5]
      _ = 1 := by norm_num
  have hweight₁ : (kleinBinaryStandardGenA 0 0) ^ 11 *
      kleinBinaryStandardGenA 1 1 = 1 := by
    calc
      (kleinBinaryStandardGenA 0 0) ^ 11 * kleinBinaryStandardGenA 1 1 =
          (kleinBinaryStandardGenA 0 0) ^ 10 *
            (kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1) := by ring
      _ = 1 := by rw [hα10, hαβ]; ring
  have hweight₂ : (kleinBinaryStandardGenA 0 0) ^ 6 *
      (kleinBinaryStandardGenA 1 1) ^ 6 = 1 := by
    rw [← mul_pow, hαβ]
    norm_num
  have hweight₃ : kleinBinaryStandardGenA 0 0 *
      (kleinBinaryStandardGenA 1 1) ^ 11 = 1 := by
    calc
      kleinBinaryStandardGenA 0 0 * (kleinBinaryStandardGenA 1 1) ^ 11 =
          (kleinBinaryStandardGenA 0 0 * kleinBinaryStandardGenA 1 1) *
            (kleinBinaryStandardGenA 1 1) ^ 10 := by ring
      _ = 1 := by rw [hαβ, hβ10]; ring
  calc
    _ = -((kleinBinaryStandardGenA 0 0) ^ 11 * kleinBinaryStandardGenA 1 1) *
          (z₁ ^ 11 * z₂) +
        11 * ((kleinBinaryStandardGenA 0 0) ^ 6 *
          (kleinBinaryStandardGenA 1 1) ^ 6) * (z₁ ^ 6 * z₂ ^ 6) +
        (kleinBinaryStandardGenA 0 0 * (kleinBinaryStandardGenA 1 1) ^ 11) *
          (z₁ * z₂ ^ 11) := by
            rw [kleinIcosahedralVertexF_source_swap]
            ring
    _ = -(z₁ ^ 11 * z₂) + 11 * (z₁ ^ 6 * z₂ ^ 6) + z₁ * z₂ ^ 11 := by
          rw [hweight₁, hweight₂, hweight₃]
          ring
    _ = kleinIcosahedralSourceVertexF z₁ z₂ := by
          rw [kleinIcosahedralVertexF_source_swap]
          ring

/-- The three classical Klein forms are all invariant under the diagonalized
order-ten generator in the same standard binary coordinates. -/
theorem kleinBinaryForms_invariant_under_standardGenA (z₁ z₂ : ℂ) :
    kleinIcosahedralVertexF
        (kleinBinaryStandardGenA 0 0 * z₁)
        (kleinBinaryStandardGenA 1 1 * z₂) = kleinIcosahedralVertexF z₁ z₂ ∧
    kleinIcosahedralFaceH
        (kleinBinaryStandardGenA 0 0 * z₁)
        (kleinBinaryStandardGenA 1 1 * z₂) = kleinIcosahedralFaceH z₁ z₂ ∧
    kleinIcosahedralEdgeT
        (kleinBinaryStandardGenA 0 0 * z₁)
        (kleinBinaryStandardGenA 1 1 * z₂) = kleinIcosahedralEdgeT z₁ z₂ := by
  let α := kleinBinaryStandardGenA 0 0
  let β := kleinBinaryStandardGenA 1 1
  rcases kleinBinaryStandardGenA_diagonal_relations with ⟨hα5, hβ5, hαβ⟩
  have hα10 : α ^ 10 = 1 := by
    calc
      α ^ 10 = (α ^ 5) ^ 2 := by rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul]
      _ = (-1 : ℂ) ^ 2 := by rw [hα5]
      _ = 1 := by norm_num
  have hβ10 : β ^ 10 = 1 := by
    calc
      β ^ 10 = (β ^ 5) ^ 2 := by rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul]
      _ = (-1 : ℂ) ^ 2 := by rw [hβ5]
      _ = 1 := by norm_num
  have hαβ5 : α ^ 5 * β ^ 5 = 1 := by
    rw [← mul_pow, hαβ]
    norm_num
  have hα20 : α ^ 20 = 1 := by
    calc α ^ 20 = (α ^ 10) ^ 2 := by rw [show (20 : ℕ) = 10 * 2 by norm_num, pow_mul]
      _ = 1 := by rw [hα10]; norm_num
  have hβ20 : β ^ 20 = 1 := by
    calc β ^ 20 = (β ^ 10) ^ 2 := by rw [show (20 : ℕ) = 10 * 2 by norm_num, pow_mul]
      _ = 1 := by rw [hβ10]; norm_num
  have hα30 : α ^ 30 = 1 := by
    calc α ^ 30 = (α ^ 10) ^ 3 := by rw [show (30 : ℕ) = 10 * 3 by norm_num, pow_mul]
      _ = 1 := by rw [hα10]; norm_num
  have hβ30 : β ^ 30 = 1 := by
    calc β ^ 30 = (β ^ 10) ^ 3 := by rw [show (30 : ℕ) = 10 * 3 by norm_num, pow_mul]
      _ = 1 := by rw [hβ10]; norm_num
  have hα15β5 : α ^ 15 * β ^ 5 = 1 := by
    calc α ^ 15 * β ^ 5 = α ^ 10 * (α ^ 5 * β ^ 5) := by ring
      _ = 1 := by rw [hα10, hαβ5]; norm_num
  have hα5β15 : α ^ 5 * β ^ 15 = 1 := by
    calc α ^ 5 * β ^ 15 = (α ^ 5 * β ^ 5) * β ^ 10 := by ring
      _ = 1 := by rw [hαβ5, hβ10]; norm_num
  have hα10β10 : α ^ 10 * β ^ 10 = 1 := by rw [hα10, hβ10]; norm_num
  have hα25β5 : α ^ 25 * β ^ 5 = 1 := by
    calc α ^ 25 * β ^ 5 = α ^ 20 * (α ^ 5 * β ^ 5) := by ring
      _ = 1 := by rw [hα20, hαβ5]; norm_num
  have hα5β25 : α ^ 5 * β ^ 25 = 1 := by
    calc α ^ 5 * β ^ 25 = (α ^ 5 * β ^ 5) * β ^ 20 := by ring
      _ = 1 := by rw [hαβ5, hβ20]; norm_num
  have hα20β10 : α ^ 20 * β ^ 10 = 1 := by rw [hα20, hβ10]; norm_num
  have hα10β20 : α ^ 10 * β ^ 20 = 1 := by rw [hα10, hβ20]; norm_num
  have hF := kleinVertexF_invariant_under_standardGenA z₁ z₂
  have hH : kleinIcosahedralFaceH (α * z₁) (β * z₂) =
      kleinIcosahedralFaceH z₁ z₂ := by
    have ht20 : α ^ 20 * z₁ ^ 20 = z₁ ^ 20 := by rw [hα20]; ring
    have ht02 : β ^ 20 * z₂ ^ 20 = z₂ ^ 20 := by rw [hβ20]; ring
    have ht155 : α ^ 15 * z₁ ^ 15 * β ^ 5 * z₂ ^ 5 = z₁ ^ 15 * z₂ ^ 5 := by
      calc _ = (α ^ 15 * β ^ 5) * (z₁ ^ 15 * z₂ ^ 5) := by ring
        _ = _ := by rw [hα15β5]; ring
    have ht515 : α ^ 5 * z₁ ^ 5 * β ^ 15 * z₂ ^ 15 = z₁ ^ 5 * z₂ ^ 15 := by
      calc _ = (α ^ 5 * β ^ 15) * (z₁ ^ 5 * z₂ ^ 15) := by ring
        _ = _ := by rw [hα5β15]; ring
    have ht1010 : α ^ 10 * z₁ ^ 10 * β ^ 10 * z₂ ^ 10 = z₁ ^ 10 * z₂ ^ 10 := by
      calc _ = (α ^ 10 * β ^ 10) * (z₁ ^ 10 * z₂ ^ 10) := by ring
        _ = _ := by rw [hα10β10]; ring
    simp only [kleinIcosahedralFaceH, mul_pow]
    ring_nf
    rw [ht20, ht02, ht155, ht515, ht1010]
  have hT : kleinIcosahedralEdgeT (α * z₁) (β * z₂) =
      kleinIcosahedralEdgeT z₁ z₂ := by
    have ht30 : α ^ 30 * z₁ ^ 30 = z₁ ^ 30 := by rw [hα30]; ring
    have ht03 : β ^ 30 * z₂ ^ 30 = z₂ ^ 30 := by rw [hβ30]; ring
    have ht255 : α ^ 25 * z₁ ^ 25 * β ^ 5 * z₂ ^ 5 = z₁ ^ 25 * z₂ ^ 5 := by
      calc _ = (α ^ 25 * β ^ 5) * (z₁ ^ 25 * z₂ ^ 5) := by ring
        _ = _ := by rw [hα25β5]; ring
    have ht525 : α ^ 5 * z₁ ^ 5 * β ^ 25 * z₂ ^ 25 = z₁ ^ 5 * z₂ ^ 25 := by
      calc _ = (α ^ 5 * β ^ 25) * (z₁ ^ 5 * z₂ ^ 25) := by ring
        _ = _ := by rw [hα5β25]; ring
    have ht2010 : α ^ 20 * z₁ ^ 20 * β ^ 10 * z₂ ^ 10 = z₁ ^ 20 * z₂ ^ 10 := by
      calc _ = (α ^ 20 * β ^ 10) * (z₁ ^ 20 * z₂ ^ 10) := by ring
        _ = _ := by rw [hα20β10]; ring
    have ht1020 : α ^ 10 * z₁ ^ 10 * β ^ 20 * z₂ ^ 20 = z₁ ^ 10 * z₂ ^ 20 := by
      calc _ = (α ^ 10 * β ^ 20) * (z₁ ^ 10 * z₂ ^ 20) := by ring
        _ = _ := by rw [hα10β20]; ring
    simp only [kleinIcosahedralEdgeT, mul_pow]
    ring_nf
    rw [ht30, ht03, ht255, ht525, ht2010, ht1020]
  exact ⟨by simpa [α, β] using hF, hH, hT⟩

private theorem kleinVertexF_generatorA_evaluation (p : ℂ) (hp : p ^ 2 = p + 1) :
    kleinIcosahedralVertexF (p / 2 + (p - 1) / 2 * Complex.I) (-(1 / 2 : ℂ)) =
      (385 / 4096 - 11 / 256 * p) + (263 / 2048 + 3 / 512 * p) * Complex.I := by
  have hp2 : p ^ 2 = p + 1 := hp
  have hp3 : p ^ 3 = 2 * p + 1 := by
    calc p ^ 3 = p ^ 2 * p := by ring
      _ = (p + 1) * p := by rw [hp2]
      _ = p ^ 2 + p := by ring
      _ = (p + 1) + p := by rw [hp2]
      _ = 2 * p + 1 := by ring
  have hp4 : p ^ 4 = 3 * p + 2 := by
    calc p ^ 4 = p ^ 3 * p := by ring
      _ = (2 * p + 1) * p := by rw [hp3]
      _ = 2 * p ^ 2 + p := by ring
      _ = 2 * (p + 1) + p := by rw [hp2]
      _ = 3 * p + 2 := by ring
  have hp5 : p ^ 5 = 5 * p + 3 := by
    calc p ^ 5 = p ^ 4 * p := by ring
      _ = (3 * p + 2) * p := by rw [hp4]
      _ = 3 * p ^ 2 + 2 * p := by ring
      _ = 3 * (p + 1) + 2 * p := by rw [hp2]
      _ = 5 * p + 3 := by ring
  have hp6 : p ^ 6 = 8 * p + 5 := by
    calc p ^ 6 = p ^ 5 * p := by ring
      _ = (5 * p + 3) * p := by rw [hp5]
      _ = 5 * p ^ 2 + 3 * p := by ring
      _ = 5 * (p + 1) + 3 * p := by rw [hp2]
      _ = 8 * p + 5 := by ring
  have hp7 : p ^ 7 = 13 * p + 8 := by
    calc p ^ 7 = p ^ 6 * p := by ring
      _ = (8 * p + 5) * p := by rw [hp6]
      _ = 8 * p ^ 2 + 5 * p := by ring
      _ = 8 * (p + 1) + 5 * p := by rw [hp2]
      _ = 13 * p + 8 := by ring
  have hp8 : p ^ 8 = 21 * p + 13 := by
    calc p ^ 8 = p ^ 7 * p := by ring
      _ = (13 * p + 8) * p := by rw [hp7]
      _ = 13 * p ^ 2 + 8 * p := by ring
      _ = 13 * (p + 1) + 8 * p := by rw [hp2]
      _ = 21 * p + 13 := by ring
  have hp9 : p ^ 9 = 34 * p + 21 := by
    calc p ^ 9 = p ^ 8 * p := by ring
      _ = (21 * p + 13) * p := by rw [hp8]
      _ = 21 * p ^ 2 + 13 * p := by ring
      _ = 21 * (p + 1) + 13 * p := by rw [hp2]
      _ = 34 * p + 21 := by ring
  have hp10 : p ^ 10 = 55 * p + 34 := by
    calc p ^ 10 = p ^ 9 * p := by ring
      _ = (34 * p + 21) * p := by rw [hp9]
      _ = 34 * p ^ 2 + 21 * p := by ring
      _ = 34 * (p + 1) + 21 * p := by rw [hp2]
      _ = 55 * p + 34 := by ring
  have hp11 : p ^ 11 = 89 * p + 55 := by
    calc p ^ 11 = p ^ 10 * p := by ring
      _ = (55 * p + 34) * p := by rw [hp10]
      _ = 55 * p ^ 2 + 34 * p := by ring
      _ = 55 * (p + 1) + 34 * p := by rw [hp2]
      _ = 89 * p + 55 := by ring
  simp only [kleinIcosahedralVertexF]
  ring_nf
  norm_num [Complex.I_sq, pow_succ]
  rw [hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11]
  ring

private theorem kleinSourceVertexF_generatorA_evaluation (p : ℂ) (hp : p ^ 2 = p + 1) :
    kleinIcosahedralSourceVertexF
        (p / 2 + (p - 1) / 2 * Complex.I) (-(1 / 2 : ℂ)) =
      (-231 / 4096 - 33 / 1024 * p) +
        (-21 / 2048 - 3 / 512 * p) * Complex.I := by
  rw [kleinIcosahedralVertexF_source_swap]
  have hp3 : p ^ 3 = 2 * p + 1 := by
    calc p ^ 3 = p ^ 2 * p := by ring
      _ = (p + 1) * p := by rw [hp]
      _ = p ^ 2 + p := by ring
      _ = 2 * p + 1 := by rw [hp]; ring
  have hp4 : p ^ 4 = 3 * p + 2 := by
    calc p ^ 4 = p ^ 3 * p := by ring
      _ = (2 * p + 1) * p := by rw [hp3]
      _ = 2 * p ^ 2 + p := by ring
      _ = 3 * p + 2 := by rw [hp]; ring
  have hp5 : p ^ 5 = 5 * p + 3 := by
    calc p ^ 5 = p ^ 4 * p := by ring
      _ = (3 * p + 2) * p := by rw [hp4]
      _ = 3 * p ^ 2 + 2 * p := by ring
      _ = 5 * p + 3 := by rw [hp]; ring
  have hp6 : p ^ 6 = 8 * p + 5 := by
    calc p ^ 6 = p ^ 5 * p := by ring
      _ = (5 * p + 3) * p := by rw [hp5]
      _ = 5 * p ^ 2 + 3 * p := by ring
      _ = 8 * p + 5 := by rw [hp]; ring
  have hp7 : p ^ 7 = 13 * p + 8 := by
    calc p ^ 7 = p ^ 6 * p := by ring
      _ = (8 * p + 5) * p := by rw [hp6]
      _ = 8 * p ^ 2 + 5 * p := by ring
      _ = 13 * p + 8 := by rw [hp]; ring
  have hp8 : p ^ 8 = 21 * p + 13 := by
    calc p ^ 8 = p ^ 7 * p := by ring
      _ = (13 * p + 8) * p := by rw [hp7]
      _ = 13 * p ^ 2 + 8 * p := by ring
      _ = 21 * p + 13 := by rw [hp]; ring
  have hp9 : p ^ 9 = 34 * p + 21 := by
    calc p ^ 9 = p ^ 8 * p := by ring
      _ = (21 * p + 13) * p := by rw [hp8]
      _ = 21 * p ^ 2 + 13 * p := by ring
      _ = 34 * p + 21 := by rw [hp]; ring
  have hp10 : p ^ 10 = 55 * p + 34 := by
    calc p ^ 10 = p ^ 9 * p := by ring
      _ = (34 * p + 21) * p := by rw [hp9]
      _ = 34 * p ^ 2 + 21 * p := by ring
      _ = 55 * p + 34 := by rw [hp]; ring
  have hp11 : p ^ 11 = 89 * p + 55 := by
    calc p ^ 11 = p ^ 10 * p := by ring
      _ = (55 * p + 34) * p := by rw [hp10]
      _ = 55 * p ^ 2 + 34 * p := by ring
      _ = 89 * p + 55 := by rw [hp]; ring
  ring_nf
  norm_num [Complex.I_sq, pow_succ]
  rw [hp, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11]
  ring

/-- The printed degree-12 form is not invariant under the currently defined order-ten
generator in the owner’s defining two-dimensional action: the image of `(1,0)` is not a
zero of the form. This records the generator/form mismatch instead of assuming invariance. -/
theorem kleinVertexF_not_invariant_under_icosianGenA :
    kleinIcosahedralVertexF (kleinBinaryAction icosianGenA 1 0).1
        (kleinBinaryAction icosianGenA 1 0).2 ≠
      kleinIcosahedralVertexF 1 0 := by
  rw [icosianGenA_kleinBinaryAction]
  have hφpos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hp : (Real.goldenRatio : ℂ) ^ 2 = Real.goldenRatio + 1 := by
    exact_mod_cast Real.goldenRatio_sq
  have hvalue := kleinVertexF_generatorA_evaluation (Real.goldenRatio : ℂ) hp
  have hvalue' :
      kleinIcosahedralVertexF
          (((Real.goldenRatio / 2 : ℝ) + ((Real.goldenRatio - 1) / 2 : ℝ) * Complex.I) * 1 +
            (1 / 2 : ℝ) * 0)
          ((-(1 / 2 : ℝ)) * 1 +
            ((Real.goldenRatio / 2 : ℝ) - ((Real.goldenRatio - 1) / 2 : ℝ) * Complex.I) * 0) =
        (385 / 4096 - 11 / 256 * Real.goldenRatio : ℝ) +
          (263 / 2048 + 3 / 512 * Real.goldenRatio : ℝ) * Complex.I := by
    simpa [kleinIcosahedralVertexF] using hvalue
  rw [hvalue']
  have himag : 0 < (263 / 2048 + 3 / 512 * Real.goldenRatio : ℝ) := by positivity
  have hne :
      (((385 / 4096 - 11 / 256 * Real.goldenRatio : ℝ) : ℂ) +
        ((263 / 2048 + 3 / 512 * Real.goldenRatio : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro hz
    have him : Complex.im
        (((385 / 4096 - 11 / 256 * Real.goldenRatio : ℝ) : ℂ) +
          ((263 / 2048 + 3 / 512 * Real.goldenRatio : ℝ) : ℂ) * Complex.I) =
        263 / 2048 + 3 / 512 * Real.goldenRatio := by simp
    have := congrArg Complex.im hz
    rw [him] at this
    simp only [Complex.zero_im] at this
    linarith
  simpa [kleinIcosahedralVertexF] using hne

/-- The source-ordered degree-12 form also fails invariance under the actual
order-ten generator.  At `(1,0)`, its image has the exact nonzero value below;
the order-ten eigenvalue law in diagonal coordinates therefore does not
transport this source polynomial to an invariant of the owner's representation. -/
theorem kleinSourceVertexF_not_invariant_under_icosianGenA :
    kleinIcosahedralSourceVertexF
        (kleinBinaryAction icosianGenA 1 0).1
        (kleinBinaryAction icosianGenA 1 0).2 ≠
      kleinIcosahedralSourceVertexF 1 0 := by
  rw [icosianGenA_kleinBinaryAction]
  have hp : (Real.goldenRatio : ℂ) ^ 2 = Real.goldenRatio + 1 := by
    exact_mod_cast Real.goldenRatio_sq
  have hvalue := kleinSourceVertexF_generatorA_evaluation
    (Real.goldenRatio : ℂ) hp
  have hvalue' :
      kleinIcosahedralSourceVertexF
          (((Real.goldenRatio / 2 : ℝ) +
            ((Real.goldenRatio - 1) / 2 : ℝ) * Complex.I) * 1 +
            (1 / 2 : ℝ) * 0)
          ((-(1 / 2 : ℝ)) * 1 +
            ((Real.goldenRatio / 2 : ℝ) -
              ((Real.goldenRatio - 1) / 2 : ℝ) * Complex.I) * 0) =
        (-231 / 4096 - 33 / 1024 * Real.goldenRatio) +
          (-21 / 2048 - 3 / 512 * Real.goldenRatio) * Complex.I := by
    simpa [kleinIcosahedralSourceVertexF] using hvalue
  rw [hvalue']
  have himag : -21 / 2048 - 3 / 512 * Real.goldenRatio < 0 := by
    nlinarith [Real.goldenRatio_pos]
  have hne :
      ((-231 / 4096 - 33 / 1024 * Real.goldenRatio : ℝ) : ℂ) +
        ((-21 / 2048 - 3 / 512 * Real.goldenRatio : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro hz
    have him : (-21 / 2048 - 3 / 512 * Real.goldenRatio : ℝ) = 0 := by
      simpa using congrArg Complex.im hz
    exact (ne_of_lt himag) him
  simpa [kleinIcosahedralSourceVertexF, kleinIcosahedralVertexF] using hne

private theorem kleinBinaryForms_act_genB (z₁ z₂ : ℂ) :
    kleinIcosahedralVertexF z₂ (-z₁) = kleinIcosahedralVertexF z₁ z₂ ∧
    kleinIcosahedralFaceH z₂ (-z₁) = kleinIcosahedralFaceH z₁ z₂ ∧
    kleinIcosahedralEdgeT z₂ (-z₁) = kleinIcosahedralEdgeT z₁ z₂ := by
  simp only [kleinIcosahedralVertexF, kleinIcosahedralFaceH, kleinIcosahedralEdgeT]
  refine ⟨by ring, by ring, by ring⟩

/-- All three displayed homogeneous forms are fixed by the order-four generator.
This is a generator-level invariance theorem; invariance under the other generator
and hence under the full binary icosahedral group is a separate result. -/
theorem kleinBinaryForms_invariant_under_icosianGenB (z₁ z₂ : ℂ) :
    kleinIcosahedralVertexF (kleinBinaryAction icosianGenB z₁ z₂).1
        (kleinBinaryAction icosianGenB z₁ z₂).2 = kleinIcosahedralVertexF z₁ z₂ ∧
    kleinIcosahedralFaceH (kleinBinaryAction icosianGenB z₁ z₂).1
        (kleinBinaryAction icosianGenB z₁ z₂).2 = kleinIcosahedralFaceH z₁ z₂ ∧
    kleinIcosahedralEdgeT (kleinBinaryAction icosianGenB z₁ z₂).1
        (kleinBinaryAction icosianGenB z₁ z₂).2 = kleinIcosahedralEdgeT z₁ z₂ := by
  rw [icosianGenB_kleinBinaryAction]
  exact kleinBinaryForms_act_genB z₁ z₂

/-- The source-ordered Klein triple uses one coordinate convention and is
fixed by the owner's actual order-four generator.  The formulas are the
argument-swapped forms, so their signs follow from the coordinate change,
not from a separate coefficient convention. -/
theorem kleinSourceBinaryForms_invariant_under_icosianGenB (z₁ z₂ : ℂ) :
    kleinIcosahedralSourceVertexF
        (kleinBinaryAction icosianGenB z₁ z₂).1
        (kleinBinaryAction icosianGenB z₁ z₂).2 =
      kleinIcosahedralSourceVertexF z₁ z₂ ∧
    kleinIcosahedralSourceFaceH
        (kleinBinaryAction icosianGenB z₁ z₂).1
        (kleinBinaryAction icosianGenB z₁ z₂).2 =
      kleinIcosahedralSourceFaceH z₁ z₂ ∧
    kleinIcosahedralSourceEdgeT
        (kleinBinaryAction icosianGenB z₁ z₂).1
        (kleinBinaryAction icosianGenB z₁ z₂).2 =
      kleinIcosahedralSourceEdgeT z₁ z₂ := by
  have hH : kleinIcosahedralSourceFaceH z₂ (-z₁) = kleinIcosahedralSourceFaceH z₁ z₂ := by
    simp [kleinIcosahedralSourceFaceH, kleinIcosahedralFaceH]
    ring
  have hT : kleinIcosahedralSourceEdgeT z₂ (-z₁) = kleinIcosahedralSourceEdgeT z₁ z₂ := by
    simp [kleinIcosahedralSourceEdgeT, kleinIcosahedralEdgeT]
    ring
  refine ⟨kleinIcosahedralSourceVertexF_invariant_under_genB z₁ z₂, ?_, ?_⟩
  · rw [icosianGenB_kleinBinaryAction]
    exact hH
  · rw [icosianGenB_kleinBinaryAction]
    exact hT

private theorem kleinBinaryBasisAlpha_mem_Ioo :
    0 < kleinBinaryBasisAlpha ∧ kleinBinaryBasisAlpha < 1 := by
  have hφ := Real.one_lt_goldenRatio
  have hφpos := Real.goldenRatio_pos
  have hφlt := Real.goldenRatio_lt_two
  have hq2 : Real.sqrt (Real.goldenRatio ^ 2 + 1) ^ 2 =
      Real.goldenRatio ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hqpos : 0 < Real.sqrt (Real.goldenRatio ^ 2 + 1) :=
    Real.sqrt_pos.2 (by positivity)
  have hqgt : 1 < Real.sqrt (Real.goldenRatio ^ 2 + 1) := by
    by_contra h
    have hle : Real.sqrt (Real.goldenRatio ^ 2 + 1) ≤ 1 := le_of_not_gt h
    have hprod := mul_nonneg (sub_nonneg.mpr hle) (by linarith [hqpos])
    nlinarith [hprod, hq2, sq_nonneg Real.goldenRatio]
  have hapos : 0 < kleinBinaryBasisAlpha := by
    dsimp [kleinBinaryBasisAlpha]
    exact div_pos (sub_pos.mpr hqgt) hφpos
  have hrel := kleinBinaryBasisAlpha_cartan_relation
  have hasq : kleinBinaryBasisAlpha ^ 2 < 1 := by
    nlinarith [mul_pos hapos (sub_pos.mpr hφ)]
  constructor
  · exact hapos
  · nlinarith [sq_nonneg (kleinBinaryBasisAlpha - 1)]

/-- The order-four standard representative fails to fix the displayed degree-12
form.  This exact witness prevents promoting the two generator-specific results
to an invariance theorem for the current triple of forms. -/
theorem kleinVertexF_not_invariant_under_standardGenB :
    kleinIcosahedralVertexF
        (kleinBinaryStandardGenB 0 0)
        (kleinBinaryStandardGenB 1 0) ≠
      kleinIcosahedralVertexF 1 0 := by
  let U := kleinBinaryStandardB_U
  let V := kleinBinaryStandardB_V
  have hα := kleinBinaryBasisAlpha_mem_Ioo
  have hden : 0 < 1 + kleinBinaryBasisAlpha ^ 2 := by positivity
  have hV : 0 < V := by
    dsimp [V, kleinBinaryStandardB_V]
    exact div_pos (by nlinarith [hα.2]) hden
  have hUV : V < U := by
    have hrel := kleinBinaryBasisAlpha_cartan_relation
    have hnum : 0 < 2 * kleinBinaryBasisAlpha - 1 + kleinBinaryBasisAlpha ^ 2 := by
      nlinarith [hα.1, hα.2, hrel, Real.goldenRatio_lt_two]
    dsimp [U, V, kleinBinaryStandardB_U, kleinBinaryStandardB_V]
    rw [div_lt_div_iff₀ hden hden]
    nlinarith
  have hU : 0 < U := lt_trans hV hUV
  have hsum5 : 0 < U ^ 4 + U ^ 3 * V + U ^ 2 * V ^ 2 + U * V ^ 3 + V ^ 4 := by
    positivity
  have hpow5 : U ^ 5 - V ^ 5 =
      (U - V) * (U ^ 4 + U ^ 3 * V + U ^ 2 * V ^ 2 + U * V ^ 3 + V ^ 4) := by ring
  have hsum10 : 0 < U ^ 9 + U ^ 8 * V + U ^ 7 * V ^ 2 + U ^ 6 * V ^ 3 +
      U ^ 5 * V ^ 4 + U ^ 4 * V ^ 5 + U ^ 3 * V ^ 6 + U ^ 2 * V ^ 7 +
      U * V ^ 8 + V ^ 9 := by positivity
  have hpow10 : U ^ 10 - V ^ 10 =
      (U - V) * (U ^ 9 + U ^ 8 * V + U ^ 7 * V ^ 2 + U ^ 6 * V ^ 3 +
        U ^ 5 * V ^ 4 + U ^ 4 * V ^ 5 + U ^ 3 * V ^ 6 + U ^ 2 * V ^ 7 +
        U * V ^ 8 + V ^ 9) := by ring
  have hU10 : V ^ 10 < U ^ 10 := by
    rw [← sub_pos, hpow10]
    exact mul_pos (sub_pos.mpr hUV) hsum10
  have hinner : 0 < U ^ 10 + 11 * U ^ 5 * V ^ 5 - V ^ 10 := by
    nlinarith [hU10, mul_pos (by norm_num : 0 < (11 : ℝ))
      (mul_pos (pow_pos hU 5) (pow_pos hV 5))]
  have heval : kleinIcosahedralVertexF (U * Complex.I) (V * Complex.I) =
      ((U * V * (U ^ 10 + 11 * U ^ 5 * V ^ 5 - V ^ 10) : ℝ) : ℂ) := by
    simp only [kleinIcosahedralVertexF, mul_pow]
    have hI5 : Complex.I ^ 5 = Complex.I := by norm_num [Complex.I_sq]
    have hI10 : Complex.I ^ 10 = -1 := by
      calc
        Complex.I ^ 10 = (Complex.I ^ 5) ^ 2 := by norm_num
        _ = Complex.I ^ 2 := by rw [hI5]
        _ = -1 := Complex.I_sq
    simp only [hI5, hI10]
    ring_nf
    rw [Complex.I_sq]
    push_cast
    ring
  have hne : ((U * V * (U ^ 10 + 11 * U ^ 5 * V ^ 5 - V ^ 10) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (mul_pos (mul_pos hU hV) hinner))
  have hcoords : kleinBinaryStandardGenB 0 0 = U * Complex.I ∧
      kleinBinaryStandardGenB 1 0 = V * Complex.I := by
    simp [U, V, kleinBinaryStandardGenB, kleinBinaryStandardB_U,
      kleinBinaryStandardB_V]
  rw [hcoords.1, hcoords.2, heval]
  simpa [kleinIcosahedralVertexF] using hne


theorem kleinIcosahedralVertexF_homog {R : Type*} [CommRing R] (c z₁ z₂ : R) :
    kleinIcosahedralVertexF (c * z₁) (c * z₂) = c ^ 12 * kleinIcosahedralVertexF z₁ z₂ := by
  simp only [kleinIcosahedralVertexF]; ring

theorem kleinIcosahedralFaceH_homog {R : Type*} [CommRing R] (c z₁ z₂ : R) :
    kleinIcosahedralFaceH (c * z₁) (c * z₂) = c ^ 20 * kleinIcosahedralFaceH z₁ z₂ := by
  simp only [kleinIcosahedralFaceH]; ring

theorem kleinIcosahedralEdgeT_homog {R : Type*} [CommRing R] (c z₁ z₂ : R) :
    kleinIcosahedralEdgeT (c * z₁) (c * z₂) = c ^ 30 * kleinIcosahedralEdgeT z₁ z₂ := by
  simp only [kleinIcosahedralEdgeT]; ring

/-- Felix Klein's exact icosahedral polynomial syzygy `T² + H³ = 1728 f⁵`. -/
theorem klein_icosahedral_syzygy_1728 {R : Type*} [CommRing R] (z₁ z₂ : R) :
    kleinIcosahedralEdgeT z₁ z₂ ^ 2 + kleinIcosahedralFaceH z₁ z₂ ^ 3 =
      1728 * kleinIcosahedralVertexF z₁ z₂ ^ 5 := by
  simp only [kleinIcosahedralEdgeT, kleinIcosahedralFaceH, kleinIcosahedralVertexF]
  ring

/-- Klein's degree-60 syzygy in the single source coordinate convention used
by the source-ordered vertex, face, and edge forms. -/
theorem klein_source_icosahedral_syzygy_1728 (z₁ z₂ : ℂ) :
    kleinIcosahedralSourceEdgeT z₁ z₂ ^ 2 +
        kleinIcosahedralSourceFaceH z₁ z₂ ^ 3 =
      1728 * kleinIcosahedralSourceVertexF z₁ z₂ ^ 5 := by
  simpa [kleinIcosahedralSourceEdgeT, kleinIcosahedralSourceFaceH,
    kleinIcosahedralSourceVertexF] using klein_icosahedral_syzygy_1728 z₂ z₁

/-- The source-ordered forms retain their degrees under common scalar
rescaling. These are the three homogeneous laws on the same coordinates. -/
theorem klein_source_icosahedral_forms_homogeneous (c z₁ z₂ : ℂ) :
    kleinIcosahedralSourceVertexF (c * z₁) (c * z₂) =
        c ^ 12 * kleinIcosahedralSourceVertexF z₁ z₂ ∧
    kleinIcosahedralSourceFaceH (c * z₁) (c * z₂) =
        c ^ 20 * kleinIcosahedralSourceFaceH z₁ z₂ ∧
    kleinIcosahedralSourceEdgeT (c * z₁) (c * z₂) =
        c ^ 30 * kleinIcosahedralSourceEdgeT z₁ z₂ := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [kleinIcosahedralSourceVertexF] using
      (kleinIcosahedralVertexF_homog c z₂ z₁)
  · simpa [kleinIcosahedralSourceFaceH] using
      (kleinIcosahedralFaceH_homog c z₂ z₁)
  · simpa [kleinIcosahedralSourceEdgeT] using
      (kleinIcosahedralEdgeT_homog c z₂ z₁)

/-- Rational ratio `-H³/F⁵` of the displayed binary forms. Scaling invariance is proved below;
invariance under the embedded `A₅` action is not asserted. -/
def kleinBinaryFormRatio (z₁ z₂ : ℂ) : ℂ :=
  -(kleinIcosahedralFaceH z₁ z₂ ^ 3) / (kleinIcosahedralVertexF z₁ z₂ ^ 5)

theorem kleinBinaryFormRatio_scale_invariant {c z₁ z₂ : ℂ} (hc : c ≠ 0) :
    kleinBinaryFormRatio (c * z₁) (c * z₂) = kleinBinaryFormRatio z₁ z₂ := by
  simp only [kleinBinaryFormRatio, kleinIcosahedralFaceH_homog, kleinIcosahedralVertexF_homog]
  have hc60 : c ^ 60 ≠ 0 := pow_ne_zero 60 hc
  have h1 : (c ^ 20 * kleinIcosahedralFaceH z₁ z₂) ^ 3 = c ^ 60 * kleinIcosahedralFaceH z₁ z₂ ^ 3 := by ring
  have h2 : (c ^ 12 * kleinIcosahedralVertexF z₁ z₂) ^ 5 = c ^ 60 * kleinIcosahedralVertexF z₁ z₂ ^ 5 := by ring
  rw [h1, h2]
  field_simp [hc60]

theorem kleinBinaryFormRatio_add_1728 {z₁ z₂ : ℂ} (hf : kleinIcosahedralVertexF z₁ z₂ ≠ 0) :
    kleinBinaryFormRatio z₁ z₂ + 1728 =
      kleinIcosahedralEdgeT z₁ z₂ ^ 2 / (kleinIcosahedralVertexF z₁ z₂ ^ 5) := by
  have hf5 : kleinIcosahedralVertexF z₁ z₂ ^ 5 ≠ 0 := pow_ne_zero 5 hf
  have hsyz := klein_icosahedral_syzygy_1728 z₁ z₂
  simp only [kleinBinaryFormRatio]
  field_simp [hf5]
  linear_combination (-1 : ℂ) * hsyz

/-! ## Section 5: Quintic Radical Unsolvability (`AbelRuffini`) and Icosahedral / Tschirnhaus Reduction -/

theorem permA5_permB5_noncomm : permA5 * permB5 ≠ permB5 * permA5 := by
  decide

theorem not_isAbelian_alternatingGroup_five :
    ¬ ∀ x y : alternatingGroup (Fin 5), x * y = y * x := by
  intro hab
  have h := hab ⟨permA5, permA5_mem_alt5⟩ ⟨permB5, permB5_mem_alt5⟩
  exact permA5_permB5_noncomm (congrArg Subtype.val h)

/-- Classical theorem: `A₅` is non-solvable, hence no quintic with Galois group `A₅` is solvable by radicals. -/
theorem not_isSolvable_alternatingGroup_five : ¬ Group.IsSolvable (alternatingGroup (Fin 5)) := by
  intro hsolv
  have hsim : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hder_ne : commutator (alternatingGroup (Fin 5)) ≠ ⊥ := by
    intro hbot
    apply not_isAbelian_alternatingGroup_five
    intro x y
    have hcomm : x * y * x⁻¹ * y⁻¹ = 1 := by
      rw [← Subgroup.mem_bot, ← hbot]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    calc
      x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [hcomm, one_mul]
  have hcomm_top : commutator (alternatingGroup (Fin 5)) = ⊤ :=
    (Subgroup.commutator_normal (⊤ : Subgroup (alternatingGroup (Fin 5))) ⊤).eq_bot_or_eq_top.resolve_left
      hder_ne
  have hstep : ∀ n : ℕ, derivedSeries (alternatingGroup (Fin 5)) n = ⊤ := by
    intro n
    induction n with
    | zero => exact derivedSeries_zero _
    | succ k ih =>
      rw [derivedSeries_succ, ih, Subgroup.commutator_def]
      exact hcomm_top
  obtain ⟨N, hN⟩ := hsolv.solvable
  have htop_bot : (⊤ : Subgroup (alternatingGroup (Fin 5))) = ⊥ := (hstep N).symm.trans hN
  have h1 : (⟨permA5, permA5_mem_alt5⟩ : alternatingGroup (Fin 5)) = 1 := by
    rw [← Subgroup.mem_bot, ← htop_bot]
    exact Subgroup.mem_top _
  exact permA5_permB5_noncomm (by
    have hA : permA5 = 1 := congrArg Subtype.val h1
    rw [hA, one_mul, mul_one])

theorem not_isSolvable_icosahedralPSU2Subgroup : ¬ Group.IsSolvable icosahedralPSU2Subgroup := by
  intro hsolv
  exact not_isSolvable_alternatingGroup_five
    (Group.isSolvable_of_surjective
      (f := kleinIcosahedralMulEquiv.symm.toMonoidHom)
      kleinIcosahedralMulEquiv.symm.surjective)

/-- Galois–Abel–Ruffini link: any irreducible polynomial whose Galois group surjects onto `A₅`
cannot have a root inside `solvableByRad F E`. -/
theorem quintic_galois_A5_not_solvableByRad
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {q : Polynomial F} (hq : Irreducible q) {α : E} (hroot : Polynomial.aeval α q = 0)
    (φ : q.Gal →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ) :
    α ∉ solvableByRad F E := by
  intro hrad
  have hgal : Group.IsSolvable q.Gal := isSolvable_gal_of_irreducible hrad hq hroot
  have ha5 : Group.IsSolvable (alternatingGroup (Fin 5)) :=
    Group.isSolvable_of_surjective (f := φ) hφ
  exact not_isSolvable_alternatingGroup_five ha5

/-- Tschirnhaus depression shift reducing a monic quintic by eliminating the `X⁴` term. -/
def quinticDepressShift {R : Type*} [CommRing R] [Invertible (5 : R)]
    (a₄ a₃ a₂ a₁ a₀ x : R) : R :=
  let y := x - a₄ * ⅟(5 : R)
  y ^ 5 + a₄ * y ^ 4 + a₃ * y ^ 3 + a₂ * y ^ 2 + a₁ * y + a₀

theorem quinticDepressShift_depressed_coeffs {R : Type*} [CommRing R] [Invertible (5 : R)]
    (a₄ a₃ a₂ a₁ a₀ x : R) :
    ∃ p q r s : R, quinticDepressShift a₄ a₃ a₂ a₁ a₀ x = x ^ 5 + p * x ^ 3 + q * x ^ 2 + r * x + s := by
  let c : R := a₄ * ⅟(5 : R)
  have ha4 : a₄ = 5 * c := by
    dsimp [c]
    rw [mul_left_comm, mul_invOf_self, mul_one]
  refine ⟨a₃ - 10 * c ^ 2,
    a₂ - 3 * a₃ * c + 20 * c ^ 3,
    a₁ - 2 * a₂ * c + 3 * a₃ * c ^ 2 - 15 * c ^ 4,
    4 * c ^ 5 - a₃ * c ^ 3 + a₂ * c ^ 2 - a₁ * c + a₀,
    ?_⟩
  simp only [quinticDepressShift]
  change (x - c) ^ 5 + a₄ * (x - c) ^ 4 + a₃ * (x - c) ^ 3 + a₂ * (x - c) ^ 2 + a₁ * (x - c) + a₀ =
    x ^ 5 + (a₃ - 10 * c ^ 2) * x ^ 3 + (a₂ - 3 * a₃ * c + 20 * c ^ 3) * x ^ 2 +
      (a₁ - 2 * a₂ * c + 3 * a₃ * c ^ 2 - 15 * c ^ 4) * x +
      (4 * c ^ 5 - a₃ * c ^ 3 + a₂ * c ^ 2 - a₁ * c + a₀)
  rw [ha4]
  ring

/-- Algebraic relation between the displayed binary-form ratio and `F⁵`. This is not a resolvent
polynomial for a quintic or a root-to-parameter theorem. -/
theorem kleinBinaryFormRatio_relation {z₁ z₂ : ℂ}
    (hf : kleinIcosahedralVertexF z₁ z₂ ≠ 0) :
    kleinIcosahedralFaceH z₁ z₂ ^ 3 +
      kleinBinaryFormRatio z₁ z₂ * kleinIcosahedralVertexF z₁ z₂ ^ 5 = 0 := by
  have hf5 : kleinIcosahedralVertexF z₁ z₂ ^ 5 ≠ 0 := pow_ne_zero 5 hf
  simp only [kleinBinaryFormRatio]
  field_simp [hf5]
  ring

/-! ## Section 6: Modular `j`-Invariant (`E₄³ / Δ`) and normalization `j / 1728` -/

def jInvariant (z : ℍ) : ℂ :=
  ModularForm.E₄ z ^ 3 / ModularForm.discriminant z

def normalizedJInvariant (z : ℍ) : ℂ :=
  jInvariant z / 1728

/-- The numerator of the level-one `j`-invariant has nonzero constant term at
the cusp. Together with Mathlib's exact order-one theorem for the discriminant
q-expansion, this is the formal-series input for a simple pole of `j`; it does
not by itself construct the meromorphic function on the compactified modular
curve. -/
theorem jInvariant_qExpansion_cusp_data :
    (qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) ^ 3).coeff 0 = 1 ∧
    (qExpansion 1 CuspForm.discriminant).order = 1 := by
  constructor
  · have hE₄ : (qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4)).coeff 0 = 1 :=
      EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by norm_num)
    have hE₄' : PowerSeries.constantCoeff
        (qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4)) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE₄
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hE₄']
    norm_num
  · exact ModularForm.discriminant_qExpansion_order

/-- The unit left after removing the first-order zero of the discriminant's
q-expansion. Its constant term is one, so it is the invertible denominator in
the formal Laurent description of `j` at the cusp. -/
private noncomputable def jDiscriminantCuspUnit : (PowerSeries ℂ)ˣ :=
  PowerSeries.Unit_of_divided_by_X_pow_order
    (qExpansion 1 CuspForm.discriminant)

/-- The regular factor in the formal principal-part decomposition
`j(q) = q⁻¹ * jCuspRegularFactor(q)`. -/
private noncomputable def jCuspRegularFactor : PowerSeries ℂ :=
  qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) ^ 3 *
    (↑(jDiscriminantCuspUnit⁻¹) : PowerSeries ℂ)

/-- The `j`-invariant has formal principal part `q⁻¹` with coefficient one:
the discriminant q-expansion factors as `q` times a unit of constant term
one, and the numerator divided by that unit also has constant term one. -/
theorem jInvariant_formal_cusp_principal_part :
    qExpansion 1 CuspForm.discriminant =
      PowerSeries.X * (↑jDiscriminantCuspUnit : PowerSeries ℂ) ∧
    PowerSeries.constantCoeff jCuspRegularFactor = 1 := by
  rcases jInvariant_qExpansion_cusp_data with ⟨hnum, horder⟩
  let Δq : PowerSeries ℂ := qExpansion 1 CuspForm.discriminant
  have hΔne : Δq ≠ 0 := by
    intro hz
    have htop : Δq.order = ⊤ := PowerSeries.order_eq_top.mpr hz
    rw [horder] at htop
    simp at htop
  have hunit : (↑jDiscriminantCuspUnit : PowerSeries ℂ) = Δq.divXPowOrder := by
    exact PowerSeries.Unit_of_divided_by_X_pow_order_nonzero hΔne
  have horderNat : Δq.order.toNat = 1 := by rw [horder]; rfl
  have hfactor : PowerSeries.X * (↑jDiscriminantCuspUnit : PowerSeries ℂ) = Δq := by
    calc
      PowerSeries.X * (↑jDiscriminantCuspUnit : PowerSeries ℂ) =
          PowerSeries.X ^ Δq.order.toNat * Δq.divXPowOrder := by
            rw [horderNat, pow_one, hunit]
      _ = Δq := PowerSeries.X_pow_order_mul_divXPowOrder
  have hΔcoeff : (PowerSeries.coeff 1) Δq = 1 :=
    ModularForm.discriminant_qExpansion_coeff_one
  have hunit0 : PowerSeries.constantCoeff (↑jDiscriminantCuspUnit : PowerSeries ℂ) = 1 := by
    have h := hΔcoeff
    rw [← hfactor] at h
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using h
  have hinv0 : PowerSeries.constantCoeff (↑(jDiscriminantCuspUnit⁻¹) : PowerSeries ℂ) = 1 := by
    have hmul := congrArg PowerSeries.constantCoeff (Units.val_inv jDiscriminantCuspUnit)
    rw [map_mul, hunit0, one_mul] at hmul
    exact hmul
  constructor
  · simpa [Δq] using hfactor.symm
  · have hnum0 : PowerSeries.constantCoeff
        (qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) ^ 3) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hnum
    change PowerSeries.constantCoeff
      (qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4) ^ 3 *
        (↑(jDiscriminantCuspUnit⁻¹) : PowerSeries ℂ)) = 1
    rw [map_mul, hnum0, hinv0]
    norm_num

/-- The regular factor at the cusp is invertible as a formal power series;
its constant coefficient is one by `jInvariant_formal_cusp_principal_part`. -/
theorem jCuspRegularFactor_isUnit : IsUnit jCuspRegularFactor :=
  PowerSeries.isUnit_iff_constantCoeff.mpr
    (by rw [jInvariant_formal_cusp_principal_part.2]; exact isUnit_one)

def modularMatSZ : Matrix (Fin 2) (Fin 2) ℤ := (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ)
def modularMatTZ : Matrix (Fin 2) (Fin 2) ℤ := (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ)

/-- Explicit T16 non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℤ` for `SL(2, ℤ)` generators. -/
theorem modularMatSZ_mul_modularMatTZ_ne :
    modularMatSZ * modularMatTZ ≠ modularMatTZ * modularMatSZ := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  simp [modularMatSZ, modularMatTZ, ModularGroup.S, ModularGroup.T,
    Matrix.mul_apply, Fin.sum_univ_two] at h00

def modularMatSR : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]
def modularMatTR : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

/-- Explicit T16 non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ` for `SL(2, ℝ)` generators. -/
theorem modularMatSR_mul_modularMatTR_ne :
    modularMatSR * modularMatTR ≠ modularMatTR * modularMatSR := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  simp [modularMatSR, modularMatTR, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem jInvariant_denom_ne_zero (z : ℍ) : ModularForm.discriminant z ≠ 0 :=
  ModularForm.discriminant_ne_zero z

private lemma sl2z_denom_cast (γ : SL(2, ℤ)) (z : ℍ) :
    denom (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) z = denom γ z := by
  simp [denom]

/-- Full `SL(2, ℤ)` weight-0 modular invariance of the `j`-invariant: `j(γ • z) = j(z)`. -/
theorem jInvariant_smul (γ : SL(2, ℤ)) (z : ℍ) : jInvariant (γ • z) = jInvariant z := by
  have hmem : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ :=
    MonoidHom.mem_range.mpr ⟨γ, rfl⟩
  have hsmul : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) • z = γ • z := rfl
  have hE4 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hmem z
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hmem z
  rw [hsmul] at hE4 hΔ
  have hdz : denom (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) z ≠ 0 :=
    denom_ne_zero _ _
  have hE4_cube : ModularForm.E₄ (γ • z) ^ 3 =
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) z) ^ (12 : ℤ) *
        ModularForm.E₄ z ^ 3 := by
    rw [hE4, mul_pow, ← _root_.zpow_natCast (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) z ^ (4 : ℤ)) 3,
      ← _root_.zpow_mul]
    norm_num
  have hΔ' : ModularForm.discriminant (γ • z) =
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) z) ^ (12 : ℤ) *
        ModularForm.discriminant z := by
    simpa [CuspForm.coe_discriminant] using hΔ
  have hΔz : ModularForm.discriminant z ≠ 0 := jInvariant_denom_ne_zero z
  have hpow12 : (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) z) ^ (12 : ℤ) ≠ 0 :=
    zpow_ne_zero 12 hdz
  simp only [jInvariant, hE4_cube, hΔ']
  field_simp [hpow12, hΔz]

theorem jInvariant_T_invariant (z : ℍ) : jInvariant (ModularGroup.T • z) = jInvariant z :=
  jInvariant_smul ModularGroup.T z

theorem jInvariant_S_invariant (z : ℍ) : jInvariant (ModularGroup.S • z) = jInvariant z :=
  jInvariant_smul ModularGroup.S z

/-- The classical `1728` discriminant-Eisenstein syzygy for the `j`-invariant:
`j(z) - 1728 = E₆(z)² / Δ(z)`. -/
theorem jInvariant_sub_1728 (z : ℍ) :
    jInvariant z - 1728 = ModularForm.E₆ z ^ 2 / ModularForm.discriminant z := by
  have hΔ : ModularForm.discriminant z ≠ 0 := jInvariant_denom_ne_zero z
  have hrel := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  have h1728 : (1728 : ℂ) * ModularForm.discriminant z =
      ModularForm.E₄ z ^ 3 - ModularForm.E₆ z ^ 2 := by
    rw [hrel]
    ring
  simp only [jInvariant]
  rw [div_sub' hΔ]
  congr 1
  linear_combination (-1 : ℂ) * h1728

private lemma S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  rw [UpperHalfPlane.modular_S_smul]
  ext
  simp [UpperHalfPlane.I]

theorem E₆_apply_I : ModularForm.E₆ UpperHalfPlane.I = 0 := by
  have hmem : (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S : GL (Fin 2) ℝ) ∈ 𝒮ℒ :=
    MonoidHom.mem_range.mpr ⟨ModularGroup.S, rfl⟩
  have hE6 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₆ hmem UpperHalfPlane.I
  have hsmul : (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S : GL (Fin 2) ℝ) •
      UpperHalfPlane.I = UpperHalfPlane.I := S_smul_I
  have hden : denom (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S : GL (Fin 2) ℝ)
      UpperHalfPlane.I = Complex.I := by
    rw [sl2z_denom_cast, ModularGroup.denom_S]
    simp [UpperHalfPlane.I]
  rw [hsmul, hden] at hE6
  have hi6 : Complex.I ^ (6 : ℤ) = -1 := by
    have h6 : Complex.I ^ (6 : ℕ) = -1 := by
      calc
        Complex.I ^ (6 : ℕ) = (Complex.I ^ 2) ^ 3 := by ring
        _ = (-1 : ℂ) ^ 3 := by rw [Complex.I_sq]
        _ = -1 := by norm_num
    rw [← zpow_natCast, show ((6 : ℕ) : ℤ) = 6 from rfl] at h6
    exact h6
  rw [hi6] at hE6
  linear_combination (1 / 2 : ℂ) * hE6

theorem jInvariant_apply_I : jInvariant UpperHalfPlane.I = 1728 := by
  have h := jInvariant_sub_1728 UpperHalfPlane.I
  rw [E₆_apply_I] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div] at h
  exact sub_eq_zero.mp h

theorem normalizedJInvariant_apply_I : normalizedJInvariant UpperHalfPlane.I = 1 := by
  simp [normalizedJInvariant, jInvariant_apply_I]

/-- The elliptic fixed point `ρ = -1/2 + (√3/2) i ∈ ℍ` of order 3 for `S * T`. -/
def ellipticPointRho : ℍ :=
  ⟨((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I, by
    simp [Complex.add_im, Complex.mul_im, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)]⟩

private lemma ellipticPointRho_coe :
    (ellipticPointRho : ℂ) = ((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := rfl

private lemma ellipticPointRho_sq_add_add_one :
    (ellipticPointRho : ℂ) ^ 2 + (ellipticPointRho : ℂ) + 1 = 0 := by
  rw [ellipticPointRho_coe]
  apply Complex.ext
  · calc
      ((((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) ^ 2 +
          (((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) + 1).re
          = (-1 / 2 : ℝ) ^ 2 - (Real.sqrt 3 / 2) ^ 2 + (-1 / 2) + 1 := by
            simp [sq, Complex.add_re, Complex.mul_re]
      _ = 0 := by
            have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
            linarith [hs, show (Real.sqrt 3 / 2) ^ 2 = (Real.sqrt 3) ^ 2 / 4 by ring]
  · simp [sq, Complex.add_im, Complex.mul_im]
    ring

private lemma ST_smul_rho : (ModularGroup.S * ModularGroup.T) • ellipticPointRho = ellipticPointRho := by
  rw [mul_smul, UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_S_smul]
  ext
  simp only [UpperHalfPlane.coe_vadd]
  have hρ : (ellipticPointRho : ℂ) ^ 2 + (ellipticPointRho : ℂ) + 1 = 0 :=
    ellipticPointRho_sq_add_add_one
  have hρ' : (ellipticPointRho : ℂ) ^ 2 + (ellipticPointRho : ℂ) = -1 := by
    calc
      (ellipticPointRho : ℂ) ^ 2 + (ellipticPointRho : ℂ) =
          ((ellipticPointRho : ℂ) ^ 2 + (ellipticPointRho : ℂ) + 1) - 1 := by ring
      _ = -1 := by rw [hρ]; ring
  have hne : ((1 : ℝ) : ℂ) + (ellipticPointRho : ℂ) ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    simp only [ellipticPointRho_coe, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, add_zero, zero_add, mul_one,
      Complex.zero_im] at him
    have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  rw [inv_eq_one_div]
  field_simp [hne]
  calc
    -1 = (ellipticPointRho : ℂ) ^ 2 + ellipticPointRho := hρ'.symm
    _ = ellipticPointRho * (1 + ellipticPointRho) := by
      rw [mul_add, mul_one, pow_two, add_comm]

theorem E₄_apply_rho : ModularForm.E₄ ellipticPointRho = 0 := by
  have hmem : (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T) :
      GL (Fin 2) ℝ) ∈ 𝒮ℒ :=
    MonoidHom.mem_range.mpr ⟨ModularGroup.S * ModularGroup.T, rfl⟩
  have hE4 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hmem ellipticPointRho
  have hsmul : (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T) :
      GL (Fin 2) ℝ) • ellipticPointRho = ellipticPointRho := ST_smul_rho
  have hSTmat : ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![0, -1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ModularGroup.S, ModularGroup.T, Matrix.mul_apply, Fin.sum_univ_two]
  have hST : ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 1 0 : ℝ) = 1 ∧
      ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 1 1 : ℝ) = 1 := by
    constructor <;> rw [hSTmat] <;> norm_num
  have hSTreal : ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T) :
      GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    calc
      ((ModularGroup.S * ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
          (Int.castRingHom ℝ) = (!![0, -1; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ).map
              (Int.castRingHom ℝ) := congrArg
                (fun A : Matrix (Fin 2) (Fin 2) ℤ => A.map (Int.castRingHom ℝ)) hSTmat
      _ = !![0, -1; 1, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
  have hden : denom (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T) :
      GL (Fin 2) ℝ) ellipticPointRho = (ellipticPointRho : ℂ) + 1 := by
    rw [denom]
    have h₁₀ : ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T) :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 1 := by rw [hSTreal]; rfl
    have h₁₁ : ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T) :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by rw [hSTreal]; rfl
    rw [h₁₀, h₁₁]
    simp
  rw [hsmul, hden] at hE4
  have hpow4 : ((ellipticPointRho : ℂ) + 1) ^ (4 : ℤ) ≠ 1 := by
    have hρ : (ellipticPointRho : ℂ) ^ 2 + (ellipticPointRho : ℂ) + 1 = 0 :=
      ellipticPointRho_sq_add_add_one
    have hval : ((ellipticPointRho : ℂ) + 1) ^ (4 : ℤ) = -(ellipticPointRho : ℂ) - 1 := by
      have h1 : ((ellipticPointRho : ℂ) + 1) ^ (4 : ℕ) = -(ellipticPointRho : ℂ) - 1 := by
        linear_combination ((ellipticPointRho : ℂ) ^ 2 + 3 * (ellipticPointRho : ℂ) + 2) * hρ
      rw [← zpow_natCast, show ((4 : ℕ) : ℤ) = 4 from rfl] at h1
      exact h1
    rw [hval]
    intro hEq
    have him := congrArg Complex.im hEq
    simp only [ellipticPointRho_coe, Complex.sub_im, Complex.neg_im, Complex.add_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      mul_zero, add_zero, zero_add, mul_one, Complex.one_im] at him
    have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  have hfac : (1 - ((ellipticPointRho : ℂ) + 1) ^ (4 : ℤ)) * ModularForm.E₄ ellipticPointRho = 0 := by
    linear_combination hE4
  exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr (Ne.symm hpow4))

theorem jInvariant_apply_rho : jInvariant ellipticPointRho = 0 := by
  simp [jInvariant, E₄_apply_rho]

theorem normalizedJInvariant_apply_rho : normalizedJInvariant ellipticPointRho = 0 := by
  simp [normalizedJInvariant, jInvariant_apply_rho]

/-- The `j`-invariant is holomorphic (`MDifferentiable`) everywhere on the upper half-plane `ℍ`. -/
theorem mdifferentiable_jInvariant : MDiff jInvariant := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hE4 : DifferentiableOn ℂ (ModularForm.E₄ ∘ ofComplex) { z : ℂ | 0 < z.im } :=
    UpperHalfPlane.mdifferentiable_iff.mp ModularForm.E₄.holo'
  have hΔ : DifferentiableOn ℂ (ModularForm.discriminant ∘ ofComplex) { z : ℂ | 0 < z.im } :=
    UpperHalfPlane.mdifferentiable_iff.mp CuspForm.discriminant.holo'
  have hEq : Set.EqOn (jInvariant ∘ ofComplex)
      (fun z => (ModularForm.E₄ (ofComplex z)) ^ 3 / ModularForm.discriminant (ofComplex z))
      { z : ℂ | 0 < z.im } := fun z _ => rfl
  refine DifferentiableOn.congr (DifferentiableOn.div (hE4.pow 3) hΔ ?_) hEq
  intro z _
  exact jInvariant_denom_ne_zero (ofComplex z)

theorem jInvariant_nonconstant : ∃ z₁ z₂ : ℍ, jInvariant z₁ ≠ jInvariant z₂ :=
  ⟨ellipticPointRho, UpperHalfPlane.I, by
    rw [jInvariant_apply_rho, jInvariant_apply_I]
    norm_num⟩

/-- Evaluation at `jInvariant` is injective on complex polynomials.  The range
of `jInvariant` is infinite because it is the continuous image of the
preconnected upper half-plane and is nontrivial; a nonzero polynomial cannot
vanish on that range. -/
theorem jInvariant_aeval_injective :
    Function.Injective (fun P : Polynomial ℂ => fun z : ℍ => P.eval (jInvariant z)) := by
  intro P Q hPQ
  have hjcont : Continuous jInvariant := by
    change Continuous (fun z : ℍ =>
      ModularForm.E₄ z ^ 3 / ModularForm.discriminant z)
    exact (ModularFormClass.continuous (ModularForm.E₄ : ModularForm 𝒮ℒ 4)).pow 3 |>.div
      (ModularFormClass.continuous (CuspForm.discriminant : CuspForm 𝒮ℒ 12))
      (fun z => ModularForm.discriminant_ne_zero z)
  have hjrange_nontrivial : (Set.range jInvariant).Nontrivial := by
    obtain ⟨z₁, z₂, hne⟩ := jInvariant_nonconstant
    exact ⟨jInvariant z₁, ⟨z₁, rfl⟩, jInvariant z₂, ⟨z₂, rfl⟩, hne⟩
  have hjrange_infinite : (Set.range jInvariant).Infinite :=
    (isPreconnected_range hjcont).infinite_of_nontrivial hjrange_nontrivial
  have hroots_infinite : {w : ℂ | (P - Q).IsRoot w}.Infinite := by
    apply hjrange_infinite.mono
    rintro w ⟨z, rfl⟩
    change (P - Q).eval (jInvariant z) = 0
    simp [congrFun hPQ z]
  have hsub : P - Q = 0 := Polynomial.eq_zero_of_infinite_isRoot (P - Q) hroots_infinite
  exact sub_eq_zero.mp hsub

/-- Because every weight-0 level-1 holomorphic modular form is constant (`levelOne_weight_zero_const`),
the nonconstant modular function `j` cannot be represented by a holomorphic weight-0 modular form.
This does not prove the separate Hauptmodul theorem on the compactified modular curve. -/
theorem jInvariant_not_modularForm_weight_zero :
    ¬ ∃ F : ModularForm 𝒮ℒ 0, (F : ℍ → ℂ) = jInvariant := by
  rintro ⟨F, hF⟩
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
  have hEq : jInvariant = Function.const ℍ c := hF.symm.trans hc
  obtain ⟨z₁, z₂, hne⟩ := jInvariant_nonconstant
  apply hne
  simp [hEq]

/-- Every level-one modular form of weight `12 * n`, after division by the
`n`th power of the discriminant, is a polynomial in `jInvariant` of degree
at most `n`. This is the generation half of the level-one Hauptmodul
statement; uniqueness of the polynomial representative is a separate claim. -/
theorem exists_poly_jInvariant_of_weight_twelve_mul :
    ∀ (n : ℕ) (g : ModularForm 𝒮ℒ (12 * (n : ℤ))),
      ∃ P : Polynomial ℂ, Polynomial.natDegree P ≤ n ∧
        ∀ z : ℍ, g z / ModularForm.discriminant z ^ n = Polynomial.eval (jInvariant z) P := by
  intro n
  induction n with
  | zero =>
      intro g
      let hg0 : ModularForm 𝒮ℒ 0 := ModularForm.mcast (by norm_num) g
      obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const hg0
      refine ⟨Polynomial.C c, by simp, fun z => ?_⟩
      have hgz : g z = hg0 z := by
        dsimp [hg0]
        exact (ModularForm.mcast_apply (by norm_num) g (z := z)).symm
      have hcz : hg0 z = c := congrFun hc z
      simp [hgz, hcz]
  | succ m ih =>
      intro g
      let c₀ : ℂ := (qExpansion 1 g).coeff 0
      let E4pow : ModularForm 𝒮ℒ (12 * ((m + 1 : ℕ) : ℤ)) :=
        ModularForm.mcast (by push_cast; ring)
          ((ModularForm.E₄ : ModularForm 𝒮ℒ 4).pow (3 * (m + 1)))
      let h : ModularForm 𝒮ℒ (12 * ((m + 1 : ℕ) : ℤ)) := g - c₀ • E4pow
      have hE4_coeff0 : (qExpansion 1 E4pow).coeff 0 = 1 := by
        have hcast : qExpansion 1 E4pow =
            qExpansion 1 ((ModularForm.E₄ : ModularForm 𝒮ℒ 4).pow (3 * (m + 1))) := rfl
        rw [hcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
          PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
        have hE := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) (by norm_num)
        have hE' : PowerSeries.constantCoeff
            (qExpansion 1 (ModularForm.E₄ : ModularForm 𝒮ℒ 4)) = 1 := by
          simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hE
        rw [hE', one_pow]
      have hh0 : (qExpansion 1 h).coeff 0 = 0 := by
        have hsub : qExpansion 1 h = qExpansion 1 g - qExpansion 1 (c₀ • E4pow) :=
          ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL g (c₀ • E4pow)
        have hsmul : qExpansion 1 (c₀ • E4pow) = c₀ • qExpansion 1 E4pow :=
          ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c₀ E4pow
        have hconst : (qExpansion 1 h).coeff 0 = 0 := by
          rw [hsub, hsmul, map_sub, map_smul]
          simp [c₀, hE4_coeff0]
        exact hconst
      let hCusp : CuspForm 𝒮ℒ (12 * ((m + 1 : ℕ) : ℤ)) :=
        ModularForm.toCuspForm h hh0
      let g₁ : ModularForm 𝒮ℒ (12 * (m : ℤ)) :=
        ModularForm.mcast (by push_cast; ring) (CuspForm.discriminantEquiv hCusp)
      obtain ⟨Q, hQdeg, hQeq⟩ := ih g₁
      let P : Polynomial ℂ := Polynomial.C c₀ * Polynomial.X ^ (m + 1) + Q
      have hPdeg : P.natDegree ≤ m + 1 := by
        refine (Polynomial.natDegree_add_le _ _).trans
          (max_le (Polynomial.natDegree_C_mul_X_pow_le c₀ (m + 1))
            (hQdeg.trans (Nat.le_succ m)))
      have hPeq : ∀ z : ℍ,
          g z / ModularForm.discriminant z ^ (m + 1) = Polynomial.eval (jInvariant z) P := by
        intro z
        have hΔne : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
        have hg₁_mul : ModularForm.discriminant z * g₁ z =
            g z - c₀ * (ModularForm.E₄ z ^ 3) ^ (m + 1) := by
          have hm := ModularForm.discriminant_mul_discriminantEquiv_apply hCusp z
          have hg1val : g₁ z = (CuspForm.discriminantEquiv hCusp) z := rfl
          have hpow : E4pow z = (ModularForm.E₄ z) ^ (3 * (m + 1)) := by
            dsimp [E4pow]
            rw [ModularForm.mcast_apply]
            change (((ModularForm.E₄ : ModularForm 𝒮ℒ 4).pow
              (3 * (m + 1)) : ModularForm 𝒮ℒ _) : ℍ → ℂ) z = _
            rw [ModularForm.coe_pow, Pi.pow_apply]
          have hhval : (hCusp : ℍ → ℂ) z =
              g z - c₀ * (ModularForm.E₄ z) ^ (3 * (m + 1)) := by
            change g z - c₀ * E4pow z = _
            rw [hpow]
          rw [hg1val, hm, hhval]
          ring
        have hg₁_val : g₁ z = ModularForm.discriminant z ^ m * Q.eval (jInvariant z) := by
          have hpow_ne : ModularForm.discriminant z ^ m ≠ 0 := pow_ne_zero m hΔne
          exact (div_eq_iff hpow_ne).mp (hQeq z) |>.trans (mul_comm _ _)
        have hg_val : g z = c₀ * (ModularForm.E₄ z ^ 3) ^ (m + 1) +
            ModularForm.discriminant z ^ (m + 1) * Q.eval (jInvariant z) := by
          have h1 : ModularForm.discriminant z * g₁ z =
              ModularForm.discriminant z ^ (m + 1) * Q.eval (jInvariant z) := by
            rw [hg₁_val, pow_succ']
            ring
          calc
            g z = (g z - c₀ * (ModularForm.E₄ z ^ 3) ^ (m + 1)) +
                c₀ * (ModularForm.E₄ z ^ 3) ^ (m + 1) := by ring
            _ = ModularForm.discriminant z * g₁ z +
                c₀ * (ModularForm.E₄ z ^ 3) ^ (m + 1) := by rw [← hg₁_mul]
            _ = ModularForm.discriminant z ^ (m + 1) * Q.eval (jInvariant z) +
                c₀ * (ModularForm.E₄ z ^ 3) ^ (m + 1) := by rw [h1]
            _ = c₀ * (ModularForm.E₄ z ^ 3) ^ (m + 1) +
                ModularForm.discriminant z ^ (m + 1) * Q.eval (jInvariant z) := by ring
        rw [hg_val, add_div, mul_div_assoc, ← div_pow, ← jInvariant,
          mul_div_cancel_left₀ _ (pow_ne_zero (m + 1) hΔne)]
        simp [P]
      exact ⟨P, hPdeg, hPeq⟩

/-- Every level-one modular form of weight `12 * n` has a unique polynomial
representative after division by `Δ^n`. -/
theorem unique_poly_jInvariant_of_weight_twelve_mul (n : ℕ)
    (g : ModularForm 𝒮ℒ (12 * (n : ℤ))) :
    ∃! P : Polynomial ℂ, P.natDegree ≤ n ∧
      ∀ z : ℍ, g z / ModularForm.discriminant z ^ n = Polynomial.eval (jInvariant z) P := by
  obtain ⟨P, hdeg, heq⟩ := exists_poly_jInvariant_of_weight_twelve_mul n g
  refine ⟨P, ⟨hdeg, heq⟩, ?_⟩
  intro Q hQ
  apply jInvariant_aeval_injective
  funext z
  calc
    Polynomial.eval (jInvariant z) Q = g z / ModularForm.discriminant z ^ n :=
      (hQ.2 z).symm
    _ = Polynomial.eval (jInvariant z) P := heq z

/-! ## Section 7: Master Klein Icosahedral, Quintic, & Modular-`j` Synthesis & Archetype -/

def KleinIcosahedralQuinticModularJSynthesis : Prop :=
  ((su2QuatI : Mat2C) * (su2QuatJ : Mat2C) ≠ (su2QuatJ : Mat2C) * (su2QuatI : Mat2C)) ∧
  Function.Injective kleinIcosahedralPSU2Embedding ∧
  ¬ Group.IsSolvable (alternatingGroup (Fin 5)) ∧
  ¬ Group.IsSolvable icosahedralPSU2Subgroup ∧
  (∀ z₁ z₂ : ℂ,
    kleinIcosahedralVertexF
        (kleinBinaryStandardGenA 0 0 * z₁) (kleinBinaryStandardGenA 1 1 * z₂) =
      kleinIcosahedralVertexF z₁ z₂ ∧
    kleinIcosahedralFaceH
        (kleinBinaryStandardGenA 0 0 * z₁) (kleinBinaryStandardGenA 1 1 * z₂) =
      kleinIcosahedralFaceH z₁ z₂ ∧
    kleinIcosahedralEdgeT
        (kleinBinaryStandardGenA 0 0 * z₁) (kleinBinaryStandardGenA 1 1 * z₂) =
      kleinIcosahedralEdgeT z₁ z₂) ∧
  (kleinIcosahedralVertexF
      (kleinBinaryStandardGenB 0 0) (kleinBinaryStandardGenB 1 0) ≠
    kleinIcosahedralVertexF 1 0) ∧
  (∀ z₁ z₂ : ℂ, kleinIcosahedralEdgeT z₁ z₂ ^ 2 + kleinIcosahedralFaceH z₁ z₂ ^ 3 =
    1728 * kleinIcosahedralVertexF z₁ z₂ ^ 5) ∧
  (∀ (γ : SL(2, ℤ)) (z : ℍ), jInvariant (γ • z) = jInvariant z) ∧
  (∀ z : ℍ, jInvariant z - 1728 = ModularForm.E₆ z ^ 2 / ModularForm.discriminant z) ∧
  jInvariant UpperHalfPlane.I = 1728 ∧
  jInvariant ellipticPointRho = 0 ∧
  MDiff jInvariant ∧
  (¬ ∃ F : ModularForm 𝒮ℒ 0, (F : ℍ → ℂ) = jInvariant)

theorem klein_icosahedral_quintic_modular_j_synthesis :
    KleinIcosahedralQuinticModularJSynthesis :=
  ⟨su2_quaternion_noncommutative.1,
   kleinIcosahedralPSU2Embedding_injective,
   not_isSolvable_alternatingGroup_five,
   not_isSolvable_icosahedralPSU2Subgroup,
   kleinBinaryForms_invariant_under_standardGenA,
   kleinVertexF_not_invariant_under_standardGenB,
   fun z₁ z₂ => klein_icosahedral_syzygy_1728 z₁ z₂,
   jInvariant_smul,
   jInvariant_sub_1728,
   jInvariant_apply_I,
   jInvariant_apply_rho,
   mdifferentiable_jInvariant,
   jInvariant_not_modularForm_weight_zero⟩

def kleinIcosahedralQuinticModularJArchetype : TypedArchetype Unit .proved where
  name := `InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ.klein_icosahedral_quintic_modular_j_synthesis
  phase := 5
  claim := fun _ => KleinIcosahedralQuinticModularJSynthesis
  evidence := fun _ => klein_icosahedral_quintic_modular_j_synthesis

#register_archetype kleinIcosahedralQuinticModularJArchetype
#audit_archetype kleinIcosahedralQuinticModularJArchetype

end InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ
