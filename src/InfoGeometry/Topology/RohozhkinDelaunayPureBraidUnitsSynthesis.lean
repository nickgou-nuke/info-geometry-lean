/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.DelaunayFlipMatrix
import InfoGeometry.Topology.RohozhkinPentagonMatrix
import InfoGeometry.Topology.DelaunayPureBraidInvariant
import InfoGeometry.Topology.DelaunayPureBraidRepresentation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Rohozhkin–Delaunay Invertible Matrix-Unit Representation, Appendix A Pentagon Admissibility, and Pure-Braid Subgroup Synthesis

Closes **Rank 5** of the repository's highest-ROI formalization gaps (`docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` §10):

1. **Local Flip Unit Packaging & `4 × 4` Disjoint Slot Unit Homomorphisms (`flipBlockUnit`, `upperLeftUnit2`, `lowerRightUnit2`):**
   Packages every local rational Delaunay flip `flipBlock labels i k j l hik` with its reversed
   inverse `flipBlock labels j l i k hjl` as an explicit element `flipBlockUnit` of `MatrixUnits 2`,
   proves that `upperLeftEmbed2` and `lowerRightEmbed2` respect `1` and `*`, and lifts local flip
   units to commuting `4 × 4` units `upperLeftUnit2 u * lowerRightUnit2 v = lowerRightUnit2 v * upperLeftUnit2 u`.
2. **Invertibility (`IsUnit`) of All Five Appendix A Pentagon Matrices & Word Admissibility (`appendixPentagonContexts_admissible`):**
   Uses determinant multiplicativity (`Matrix.det_mul`, `Matrix.isUnit_iff_isUnit_det`) and the
   Appendix A five-flip product `pentagon_appendix_identity` (`Γ₅ Γ₄ Γ₃ Γ₂ Γ₁ = 1`) to prove that
   each of `pentagonGamma1..5` is invertible (`IsUnit`), and hence that the Appendix A five-flip
   word `⟨appendixPentagonContexts zi zj zk zl zm⟩` satisfies `DelaunayFlipWord.admissible`.
3. **Matrix-Unit Groupoid Evaluation & Pure-Braid Subgroup Restriction (`rohozhkinUnitOfAdmissible`, `rohozhkin_pure_braid_and_pentagon_units_synthesis`):**
   Lifts any admissible flip word `(W, hW)` to `rohozhkinUnitOfAdmissible W hW : RohozhkinMatrixUnits n`,
   proves that `DelaunayEquiv W₁ W₂` implies equality in `RohozhkinMatrixUnits n`, proves that the
   Appendix A pentagon word evaluates to `1 : RohozhkinMatrixUnits 1`, and connects pure-braid
   generator squares `(σ_i)² ∈ RohozhkinPureBraidGroup moving` through `restrictRohozhkinBraidRepresentation`.
-/

noncomputable section

namespace InfoGeometry.Topology.RohozhkinDelaunayPureBraidUnitsSynthesis

open Matrix
open Braid
open InfoGeometry.Topology.Delaunay
open InfoGeometry.Topology.RohozhkinBoundary
open InfoGeometry.Categorical.UniversalArtinBraidRepresentation
open InfoGeometry.Categorical.BraidPermutationQuotient

/-! ===========================================================================
    Section 1: Local Flip `MatrixUnits 2` & `4 × 4` Disjoint Slot Unit Lifts
    =========================================================================== -/

section LocalFlipUnitsAndEmbeddings

/-- Explicit `MatrixUnits 2` packaging of a local rational Delaunay flip block `ik → jl`
with its reversed inverse `jl → ik`. -/
def flipBlockUnit {ι : Type*} (labels : FlipLabels ι)
    (i k j l : ι) (hik : i ≠ k) (hjl : j ≠ l) : MatrixUnits 2 where
  val := flipBlock labels i k j l hik
  inv := flipBlock labels j l i k hjl
  val_inv := flip_inverse_identity labels i k j l hik hjl
  inv_val := flip_inverse_identity labels j l i k hjl hik

@[simp] theorem flipBlockUnit_val {ι : Type*} (labels : FlipLabels ι)
    (i k j l : ι) (hik : i ≠ k) (hjl : j ≠ l) :
    (flipBlockUnit labels i k j l hik hjl : Matrix (Fin 2) (Fin 2) ℚ) =
      flipBlock labels i k j l hik :=
  rfl

@[simp] theorem flipBlockUnit_inv {ι : Type*} (labels : FlipLabels ι)
    (i k j l : ι) (hik : i ≠ k) (hjl : j ≠ l) :
    (flipBlockUnit labels i k j l hik hjl).inv =
      flipBlock labels j l i k hjl :=
  rfl

/-- `upperLeftEmbed2` preserves the identity matrix. -/
@[simp] theorem upperLeftEmbed2_one :
    upperLeftEmbed2 (1 : Matrix (Fin 2) (Fin 2) ℚ) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [upperLeftEmbed2]

/-- `upperLeftEmbed2` preserves matrix multiplication. -/
theorem upperLeftEmbed2_mul (A B : Matrix (Fin 2) (Fin 2) ℚ) :
    upperLeftEmbed2 (A * B) = upperLeftEmbed2 A * upperLeftEmbed2 B := by
  ext a b
  change upperLeftEmbed2 (A * B) a b =
    ∑ k : Fin 4, upperLeftEmbed2 A a k * upperLeftEmbed2 B k b
  rw [Fin.sum_univ_four]
  fin_cases a <;> fin_cases b <;>
    simp [upperLeftEmbed2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `lowerRightEmbed2` preserves the identity matrix. -/
@[simp] theorem lowerRightEmbed2_one :
    lowerRightEmbed2 (1 : Matrix (Fin 2) (Fin 2) ℚ) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [lowerRightEmbed2]

/-- `lowerRightEmbed2` preserves matrix multiplication. -/
theorem lowerRightEmbed2_mul (A B : Matrix (Fin 2) (Fin 2) ℚ) :
    lowerRightEmbed2 (A * B) = lowerRightEmbed2 A * lowerRightEmbed2 B := by
  ext a b
  change lowerRightEmbed2 (A * B) a b =
    ∑ k : Fin 4, lowerRightEmbed2 A a k * lowerRightEmbed2 B k b
  rw [Fin.sum_univ_four]
  fin_cases a <;> fin_cases b <;>
    simp [lowerRightEmbed2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Upper-left block embedding lifted to `MatrixUnits 2 → MatrixUnits 4`. -/
def upperLeftUnit2 (u : MatrixUnits 2) : MatrixUnits 4 where
  val := upperLeftEmbed2 u.val
  inv := upperLeftEmbed2 u.inv
  val_inv := by rw [← upperLeftEmbed2_mul, u.val_inv, upperLeftEmbed2_one]
  inv_val := by rw [← upperLeftEmbed2_mul, u.inv_val, upperLeftEmbed2_one]

/-- Lower-right block embedding lifted to `MatrixUnits 2 → MatrixUnits 4`. -/
def lowerRightUnit2 (v : MatrixUnits 2) : MatrixUnits 4 where
  val := lowerRightEmbed2 v.val
  inv := lowerRightEmbed2 v.inv
  val_inv := by rw [← lowerRightEmbed2_mul, v.val_inv, lowerRightEmbed2_one]
  inv_val := by rw [← lowerRightEmbed2_mul, v.inv_val, lowerRightEmbed2_one]

/-- Disjoint local flip units embedded into `MatrixUnits 4` commute in the unit group. -/
theorem upperLeftUnit2_comm_lowerRightUnit2 (u v : MatrixUnits 2) :
    upperLeftUnit2 u * lowerRightUnit2 v = lowerRightUnit2 v * upperLeftUnit2 u := by
  apply Units.ext
  exact flip_far_commute_embedded_blocks u.val v.val

end LocalFlipUnitsAndEmbeddings

/-! ===========================================================================
    Section 2: Invertibility of All Five Appendix A Pentagon Matrices & Word Admissibility
    =========================================================================== -/

section PentagonAdmissibility

/-- If a 5-fold product of square matrices over a commutative ring equals `1`, then every factor
is a unit (`IsUnit`). -/
theorem isUnit_five_factors_of_mul_eq_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]
    {A₁ A₂ A₃ A₄ A₅ : Matrix n n R}
    (h : A₁ * A₂ * A₃ * A₄ * A₅ = 1) :
    IsUnit A₁ ∧ IsUnit A₂ ∧ IsUnit A₃ ∧ IsUnit A₄ ∧ IsUnit A₅ := by
  have hdet : A₁.det * A₂.det * A₃.det * A₄.det * A₅.det = 1 := by
    calc
      A₁.det * A₂.det * A₃.det * A₄.det * A₅.det =
        (A₁ * A₂ * A₃ * A₄ * A₅).det := by
        simp only [Matrix.det_mul]
      _ = (1 : Matrix n n R).det := by rw [h]
      _ = 1 := Matrix.det_one
  have u_of_mul : ∀ x y : R, x * y = 1 → IsUnit x := fun x y hxy =>
    ⟨⟨x, y, hxy, mul_comm y x ▸ hxy⟩, rfl⟩
  have hu1 : IsUnit A₁.det := u_of_mul A₁.det (A₂.det * A₃.det * A₄.det * A₅.det)
    (by linear_combination hdet)
  have hu2 : IsUnit A₂.det := u_of_mul A₂.det (A₁.det * A₃.det * A₄.det * A₅.det)
    (by linear_combination hdet)
  have hu3 : IsUnit A₃.det := u_of_mul A₃.det (A₁.det * A₂.det * A₄.det * A₅.det)
    (by linear_combination hdet)
  have hu4 : IsUnit A₄.det := u_of_mul A₄.det (A₁.det * A₂.det * A₃.det * A₅.det)
    (by linear_combination hdet)
  have hu5 : IsUnit A₅.det := u_of_mul A₅.det (A₁.det * A₂.det * A₃.det * A₄.det)
    (by linear_combination hdet)
  exact ⟨(Matrix.isUnit_iff_isUnit_det A₁).mpr hu1,
    (Matrix.isUnit_iff_isUnit_det A₂).mpr hu2,
    (Matrix.isUnit_iff_isUnit_det A₃).mpr hu3,
    (Matrix.isUnit_iff_isUnit_det A₄).mpr hu4,
    (Matrix.isUnit_iff_isUnit_det A₅).mpr hu5⟩

/-- All five Appendix A pentagon transport matrices `pentagonGamma1..5` are invertible (`IsUnit`)
under the explicit non-zero denominator hypotheses. -/
theorem pentagonGamma_all_isUnit
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0) :
    IsUnit (pentagonGamma5 zi zj zk zl zm) ∧
    IsUnit (pentagonGamma4 zi zj zk zl zm) ∧
    IsUnit (pentagonGamma3 zi zj zk zl zm) ∧
    IsUnit (pentagonGamma2 zi zj zk zl zm) ∧
    IsUnit (pentagonGamma1 zi zj zk zl zm) :=
  isUnit_five_factors_of_mul_eq_one
    (pentagon_appendix_identity zi zj zk zl zm h_il h_ik h_km h_jm h_jl)

/-- **Theorem 2.1 (`appendixPentagonContexts_admissible`):**
The Appendix A five-flip word `⟨appendixPentagonContexts zi zj zk zl zm⟩ : DelaunayFlipWord 1`
is algebraically admissible (`DelaunayFlipWord.admissible`), i.e. every constituent flip context
in the pentagon cycle has an invertible (`IsUnit`) transport matrix. -/
theorem appendixPentagonContexts_admissible
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0) :
    DelaunayFlipWord.admissible (⟨appendixPentagonContexts zi zj zk zl zm⟩ : DelaunayFlipWord 1) := by
  rcases pentagonGamma_all_isUnit zi zj zk zl zm h_il h_ik h_km h_jm h_jl with
    ⟨hu5, hu4, hu3, hu2, hu1⟩
  intro F hF
  simp only [appendixPentagonContexts, List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl | rfl | rfl
  · exact hu5
  · exact hu4
  · exact hu3
  · exact hu2
  · exact hu1

end PentagonAdmissibility

/-! ===========================================================================
    Section 3: Matrix-Unit Groupoid Evaluation & Pure-Braid Subgroup Synthesis
    =========================================================================== -/

section PureBraidUnitsSynthesis

/-- Lift any admissible Delaunay flip word `(W : DelaunayFlipWord n)` (`hW : W.admissible`) to an
element of `RohozhkinMatrixUnits n = MatrixUnits (rohozhkinDim n)`. -/
def rohozhkinUnitOfAdmissible {n : ℕ} (W : DelaunayFlipWord n) (hW : W.admissible) :
    RohozhkinMatrixUnits n :=
  (rohozhkinMatrix_isUnit_of_admissible W hW).unit

@[simp] theorem rohozhkinUnitOfAdmissible_val {n : ℕ} (W : DelaunayFlipWord n) (hW : W.admissible) :
    (rohozhkinUnitOfAdmissible W hW :
      Matrix (Fin (rohozhkinDim n)) (Fin (rohozhkinDim n)) ℚ) = rohozhkinMatrix W :=
  IsUnit.unit_spec (rohozhkinMatrix_isUnit_of_admissible W hW)

/-- Equivalent admissible flip words (`DelaunayEquiv W₁ W₂`) evaluate to the exact same unit in
`RohozhkinMatrixUnits n`. -/
theorem rohozhkinUnitOfAdmissible_eq_of_equiv {n : ℕ}
    {W₁ W₂ : DelaunayFlipWord n} (hW₁ : W₁.admissible) (hW₂ : W₂.admissible)
    (heq : DelaunayEquiv W₁ W₂) :
    rohozhkinUnitOfAdmissible W₁ hW₁ = rohozhkinUnitOfAdmissible W₂ hW₂ := by
  apply Units.ext
  simp only [rohozhkinUnitOfAdmissible_val]
  exact rohozhkin_invariant_under_equiv heq

/-- Local rational Delaunay flip unit multiplied by its reversed-diagonal inverse equals `1`. -/
theorem flipBlockUnit_mul_symm_eq_one
    {ι : Type*} (labels : FlipLabels ι) (i k j l : ι) (hik : i ≠ k) (hjl : j ≠ l) :
    flipBlockUnit labels i k j l hik hjl * flipBlockUnit labels j l i k hjl hik = 1 := by
  apply Units.ext
  exact flip_inverse_identity labels i k j l hik hjl

/-- The admissible Appendix A five-flip pentagon word evaluates in `RohozhkinMatrixUnits 1` to `1`. -/
theorem rohozhkinUnitOfAdmissible_appendixPentagon_eq_one
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0) (h_ik : zi - zk ≠ 0) (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0) (h_jl : zj - zl ≠ 0) :
    rohozhkinUnitOfAdmissible
      (⟨appendixPentagonContexts zi zj zk zl zm⟩ : DelaunayFlipWord 1)
      (appendixPentagonContexts_admissible zi zj zk zl zm h_il h_ik h_km h_jm h_jl) = 1 := by
  apply Units.ext
  change rohozhkinMatrix ⟨appendixPentagonContexts zi zj zk zl zm⟩ = 1
  have hId := pentagon_appendix_identity zi zj zk zl zm h_il h_ik h_km h_jm h_jl
  simpa [rohozhkinMatrix, rohozhkinMatrixList, appendixPentagonContexts, Matrix.mul_assoc] using hId

/-- The pure-braid restriction `restrictRohozhkinBraidRepresentation` maps every pure generator
square `(σ_idx)²` to `(ρ σ_idx)²`. -/
theorem restrictRohozhkinBraidRepresentation_generatorSquare
    {moving : ℕ}
    (ρ : RohozhkinBraidGroup moving →* RohozhkinMatrixUnits moving)
    (idx : Fin (moving + 2)) :
    restrictRohozhkinBraidRepresentation moving ρ
        ⟨(σ' (moving + 2) idx) ^ 2, generatorSquare_mem_pureBraidSubgroup (moving + 2) idx⟩ =
      (ρ (σ' (moving + 2) idx)) ^ 2 := by
  unfold restrictRohozhkinBraidRepresentation
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_pow]

/-- **Theorem 3.1 (`rohozhkin_pure_braid_and_pentagon_units_synthesis`):**
Master synthesis of the Rohozhkin–Delaunay rational matrix-unit and pure-braid layer:
1. Every local rational flip block `flipBlock labels i k j l hik` lifts to `flipBlockUnit` in
   `MatrixUnits 2` with inverse `flipBlock labels j l i k hjl`,
2. Disjoint local flip units lift via `upperLeftUnit2` and `lowerRightUnit2` to commuting units in
   `MatrixUnits 4`,
3. The Appendix A five-flip pentagon word `W_pent := ⟨appendixPentagonContexts zi zj zk zl zm⟩` is
   admissible (`W_pent.admissible`) and evaluates in `RohozhkinMatrixUnits 1` to `1`,
4. Equivalent admissible flip words (`DelaunayEquiv W₁ W₂`) induce identical units in
   `RohozhkinMatrixUnits n`,
5. For any braid-group representation `ρ : RohozhkinBraidGroup moving →* RohozhkinMatrixUnits moving`
   and generator index `idx : Fin (moving + 2)`, the restricted pure-braid representation
   `restrictRohozhkinBraidRepresentation moving ρ` maps the pure generator square `(σ_idx)²` to
   `(ρ σ_idx)²`. -/
theorem rohozhkin_pure_braid_and_pentagon_units_synthesis
    {ι : Type*} (labels : FlipLabels ι) (i k j l : ι) (hik : i ≠ k) (hjl : j ≠ l)
    (u v : MatrixUnits 2)
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0) (h_ik : zi - zk ≠ 0) (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0) (h_jl : zj - zl ≠ 0)
    {moving : ℕ} {W₁ W₂ : DelaunayFlipWord moving}
    (hW₁ : W₁.admissible) (hW₂ : W₂.admissible) (heq : DelaunayEquiv W₁ W₂)
    (ρ : RohozhkinBraidGroup moving →* RohozhkinMatrixUnits moving)
    (idx : Fin (moving + 2)) :
    let W_pent : DelaunayFlipWord 1 := ⟨appendixPentagonContexts zi zj zk zl zm⟩
    let hPent : W_pent.admissible :=
      appendixPentagonContexts_admissible zi zj zk zl zm h_il h_ik h_km h_jm h_jl
    -- (1) Local flip unit inversion & disjoint 4×4 unit commutativity
    ((flipBlockUnit labels i k j l hik hjl * flipBlockUnit labels j l i k hjl hik = 1) ∧
     upperLeftUnit2 u * lowerRightUnit2 v = lowerRightUnit2 v * upperLeftUnit2 u) ∧
    -- (2) Appendix A pentagon admissibility & trivial evaluation in RohozhkinMatrixUnits 1
    (W_pent.admissible ∧
     rohozhkinUnitOfAdmissible W_pent hPent = 1) ∧
    -- (3) Quotient invariance in RohozhkinMatrixUnits moving
    (rohozhkinUnitOfAdmissible W₁ hW₁ = rohozhkinUnitOfAdmissible W₂ hW₂) ∧
    -- (4) Pure-braid generator-square evaluation
    (restrictRohozhkinBraidRepresentation moving ρ
        ⟨(σ' (moving + 2) idx) ^ 2, generatorSquare_mem_pureBraidSubgroup (moving + 2) idx⟩ =
      (ρ (σ' (moving + 2) idx)) ^ 2) :=
  ⟨⟨flipBlockUnit_mul_symm_eq_one labels i k j l hik hjl,
    upperLeftUnit2_comm_lowerRightUnit2 u v⟩,
   ⟨appendixPentagonContexts_admissible zi zj zk zl zm h_il h_ik h_km h_jm h_jl,
    rohozhkinUnitOfAdmissible_appendixPentagon_eq_one zi zj zk zl zm h_il h_ik h_km h_jm h_jl⟩,
   rohozhkinUnitOfAdmissible_eq_of_equiv hW₁ hW₂ heq,
   restrictRohozhkinBraidRepresentation_generatorSquare ρ idx⟩

/-! ===========================================================================
    Section 4: Elementary Projector & Root Non-Commutativity on `Matrix (Fin d) (Fin d) ℚ`
    =========================================================================== -/

/-- Elementary `2 × 2` projector `E₀₀` over `ℚ`. -/
def elementaryProj2Q : Matrix (Fin 2) (Fin 2) ℚ := !![(1 : ℚ), 0; 0, 0]

/-- Elementary `2 × 2` nilpotent root `E₀₁` over `ℚ`. -/
def elementaryRoot2Q : Matrix (Fin 2) (Fin 2) ℚ := !![(0 : ℚ), 1; 0, 0]

theorem elementaryProj2Q_mul_elementaryRoot2Q_ne :
    elementaryProj2Q * elementaryRoot2Q ≠ elementaryRoot2Q * elementaryProj2Q := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [elementaryProj2Q, elementaryRoot2Q, Matrix.mul_apply, Fin.sum_univ_two] at h01

def elementaryProj3Q : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.of fun a b => if a = 0 ∧ b = 0 then 1 else 0

def elementaryRoot3Q : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.of fun a b => if a = 0 ∧ b = 1 then 1 else 0

theorem elementaryProj3Q_mul_elementaryRoot3Q_ne :
    elementaryProj3Q * elementaryRoot3Q ≠ elementaryRoot3Q * elementaryProj3Q := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [elementaryProj3Q, elementaryRoot3Q, Matrix.mul_apply] at h01

def elementaryProj4Q : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.of fun a b => if a = 0 ∧ b = 0 then 1 else 0

def elementaryRoot4Q : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.of fun a b => if a = 0 ∧ b = 1 then 1 else 0

theorem elementaryProj4Q_mul_elementaryRoot4Q_ne :
    elementaryProj4Q * elementaryRoot4Q ≠ elementaryRoot4Q * elementaryProj4Q := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [elementaryProj4Q, elementaryRoot4Q, Matrix.mul_apply] at h01

end PureBraidUnitsSynthesis

end InfoGeometry.Topology.RohozhkinDelaunayPureBraidUnitsSynthesis
