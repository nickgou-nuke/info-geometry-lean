/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Sp4ContactGrading
import InfoGeometry.Algebra.H3ZornFreudenthalTKK5E8
import InfoGeometry.Algebra.FiveGradedIwasawaNilpotency
import InfoGeometry.Orthogonal.O55ContactGradeDecomposition
import InfoGeometry.Analysis.LieExponentialTraceDeterminant
import InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.NCG.BerezinianSuperdeterminant
import InfoGeometry.OperatorAlgebra.FiniteParitySupertrace
import InfoGeometry.Algebra.Cl11OSp12
import InfoGeometry.Canonical.GreenSchwarzAnomalyInflowBridge
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# 5-Graded Weyl Trace, Super-Jacobi, Lie-Flow Jacobian & Cl(1,1) Krein Space

Formalizes the finite-dimensional algebraic core of Milestone M2 from the source AI Studio
transcript (`cached/aistudio_extracts/aistudio_download_1-GdlLgiKADUPj5kLOhiqP6-a1qQ1bUea/transcript.md`):

* **B1 & B4** (`T01:38-49`, `T03:168-182`, `T10:928-938`, `T33:2362-2365`, `T53:4230-4233`):
  5-graded nilradical `nPlus := g1 ⊔ g2` (connected to `FiveGradedIwasawa.InGrade` /
  `IsFiveGraded`), Weyl trace `Tr_{n+}(ad_E) = dim(g1) + 2 dim(g2)`, positivity for `n+ ≠ ⊥`, and
  concrete subtype-module trace instantiations on `Sp4Contact.Sp` (`2ρ(E) = 4`),
  `O55Contact.O55Lie` (`2ρ(E) = 14`), and `FreudenthalTKK5E8` (`2ρ(E) = 58`).
  - *Transcript conflict note (`T10:937` vs `T66:5188`)*: `T10:937` computes
    `2ρ(E) = dim(g1) + 2 dim(g2) = 4 + 2(1) = 6` for `g_{2(2)}`, whereas `T66:5188` asserts
    `2ρ(E) = 4` and further commits the arithmetic error `1 - 4/(5 + 4) = 5/9 ≠ 23/24` at
    `T66:5189-5190`.
  - *BUCKET 3 boundary*: Equating `2ρ(E)` to QFT `Δa = a_UV - a_IR` (Komargodski–Schwimmer)
    remains unformalized QFT heuristic debt outside Lean.
* **C2** (`T47:3888-3897`, `T53:4245-4250`):
  Lie-flow Jacobian determinant `det(exp(t • ad_E|_{n+})) = exp(t * (dim(g1) + 2 dim(g2)))`
  and instantiations for `Sp4Contact`, `O55Contact`, and `FreudenthalTKK5E8`.
* **B2** (`T65:5025-5071`):
  Bigraded `(k, ε)` supercommutator, graded Super-Jacobi identity, `|a + b| > 2` truncation, and
  concrete `osp(1|2) ⊂ M_3(ℝ)` matrix witness `(ospE, ospQ1, ospP1, ospQ2, ospP2)`.
* **B3** (`T65:5073-5079`):
  Re-exports `MajoranaParaKahlerMaurerCartanSupercolorSynthesis.mcCurvatureTower_flat_iff_source_laws`
  and proves internal direct-sum grade decomposition of `dω + (1/2) [ω, η] = 0` in any 5-graded
  Lie algebra as well as the Cartan `ω = θ + ω₀ + Υ` superbracket equations.
  - *Convention note (`T65:5077` vs `A2`)*: `T65:5077` places `θ ∈ g1` and `Υ ∈ g(-1)`, swapped
    relative to Theme A (`T01:26`, `T03:151`) where `θ ∈ g(-1)` and `Υ ∈ g1`; both yield the same
    grade-0 pairing `[g1, g(-1)] ⊆ g0`.
* **E9_alg** (`T38:2843-2874`):
  Proves matched Levi containment `[g1, g(-1)] ⊆ g0` and `[g2, g(-2)] ⊆ g0`, general
  `[n+, n-] ⊆ g(-1) ⊔ g0 ⊔ g1`, exact 3-graded specialization `[n+, n-] ⊆ g0` when `g(±2) = ⊥`,
  and counter-witnesses in `Sp4Contact.Sp` and `FreudenthalTKK5E8` refuting the unqualified `T38`
  claim `[n+, n-] ⊆ g0` when `g(±2) ≠ ⊥`.
* **F1** (`T21:1497-1500`, `T63:4954-4958`, `T65:5111-5121`):
  2D concrete `Cl(1,1)` realization reusing `Cl11Matrix` (`kreinGamma0 := Eminus`,
  `kreinGamma1 := J1`, `kreinSymmetryJ := Eplus`) and general `Matrix (ι ⊕ ι) (ι ⊕ ι) R` block
  realization reusing `InfoGeometry.NCG.Gamma`.
  - *Convention note (`T21` vs `T65`)*: `T21:1497` uses 4D Dirac `γ⁰ = diag(1,1,-1,-1)` with
    `(γ⁰)² = +I₄`, whereas `T65:5118-5121` uses 2D `Cl(1,1)` `γ⁰ = Eminus` with `(γ⁰)² = -I₂`.
* **F2 & B6** (`T65:5123-5135`, `T66:5157-5165`):
  Krein supertrace cancellation for `Gamma`-odd / off-diagonal operators and balanced block-diagonal
  operators, plus noncommutative block-curvature square `sTr_K(R²) = Tr(R₊²) - Tr(R₋²) = 0`
  linked to `GreenSchwarzAnomalyInflow.anomaly_polynomial_factorization`.
  - *BUCKET 2/3 boundary*: Smooth manifold transgression `dΩ₃(ω) = sTr_K(R ∧ R)` is outside this
    algebraic module.
* **F3** (`T26:1766-1865`):
  Indexed CAR square-zero theorem `{c_i, c_j} = 0 → c_i² = 0` under `[Invertible (2 : R)]`,
  non-vanishing multi-mode `ExteriorAlgebra R (ι → R)` creators, and link to `Cl11OSp12.bdag_sq`.
* **F4** (`T27:1871-1890`, `T29:1937-1988`):
  Arbitrary-signature Clifford reflection `R_u(x) = -u x u⁻¹`, field polar form, and `Pin±` square
  dichotomy (`Q u = 1` vs `Q u = -1`) with concrete `Cl11Matrix.q11` `(1,1)` witnesses.
  - *Convention note (`T29` vs `WittenParityAnomalyBridge` vs Mathlib `pinGroup`)*: `T29:1961-1964`
    labels spatial reflection `R̃² = +1` as `Pin⁺` and `R̃² = -1` as `Pin⁻` (opposite to
    `WittenParityAnomalyBridge` time-reversal convention); in Mathlib `pinGroup Q`, `star (ι Q u) =
    -ι Q u`, so `ι Q u ∈ pinGroup Q` holds for `Q u = -1` while `Q u = +1` lies in `pinGroup (-Q)`.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Algebra.FiveGradedWeylTrace

open scoped Matrix DirectSum
open InfoGeometry.Algebra.FiveGradedIwasawa
open InfoGeometry.Analysis.LieExponentialTraceDeterminant

/-! ## Section 1: B1 & B4 — 5-Graded Nilradical and General Weyl Trace `2ρ(E)` -/

section WeylTraceGeneral

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Positive nilradical `n₊ := g₁ ⊔ g₂` of a `ℤ`-graded Lie algebra. -/
def nPlus (grade : ℤ → Submodule ℝ L) : Submodule ℝ L :=
  grade 1 ⊔ grade 2

/-- Negative nilradical `n₋ := g₋₁ ⊔ g₋₂` of a `ℤ`-graded Lie algebra. -/
def nMinus (grade : ℤ → Submodule ℝ L) : Submodule ℝ L :=
  grade (-1) ⊔ grade (-2)

/-- Bridge between submodule membership with adjoint eigenvalue `k` and `FiveGradedIwasawa.InGrade`. -/
theorem mem_grade_iff_inGrade (E x : L) (k : ℤ) :
    ⁅E, x⁆ = (k : ℝ) • x ↔ InGrade E (k : ℝ) x :=
  Iff.rfl

/-- Connection to `FiveGradedIwasawa.iwasawa_n_sector_nilpotent` for elements of `nPlus`. -/
theorem nPlus_nilpotent_of_isFiveGraded (E : L) [IsFiveGraded E]
    (x1 x2 y1 y2 z1 z2 : L)
    (hx1 : ⁅E, x1⁆ = (1 : ℝ) • x1) (hx2 : ⁅E, x2⁆ = (2 : ℝ) • x2)
    (hy1 : ⁅E, y1⁆ = (1 : ℝ) • y1) (hy2 : ⁅E, y2⁆ = (2 : ℝ) • y2)
    (hz1 : ⁅E, z1⁆ = (1 : ℝ) • z1) (hz2 : ⁅E, z2⁆ = (2 : ℝ) • z2) :
    ⁅⁅x1 + x2, y1 + y2⁆, z1 + z2⁆ = 0 :=
  iwasawa_n_sector_nilpotent E x1 x2 y1 y2 z1 z2 hx1 hx2 hy1 hy2 hz1 hz2

/-- Distinct `ad_E` eigenvalues `1` and `2` force `Disjoint g1 g2`. -/
theorem disjoint_grade_of_ad_eigen {E : L} {g1 g2 : Submodule ℝ L}
    (h1 : ∀ x ∈ g1, ⁅E, x⁆ = (1 : ℝ) • x)
    (h2 : ∀ x ∈ g2, ⁅E, x⁆ = (2 : ℝ) • x) :
    Disjoint g1 g2 := by
  rw [Submodule.disjoint_def]
  intro x hx1 hx2
  have heq : (1 : ℝ) • x = (2 : ℝ) • x := (h1 x hx1).symm.trans (h2 x hx2)
  have hsub : (1 : ℝ) • x - (2 : ℝ) • x = 0 := sub_eq_zero.mpr heq
  rw [one_smul] at hsub
  have hneg : -x = 0 := by
    calc
      -x = x - (2 : ℝ) • x := by module
      _ = 0 := hsub
  exact neg_eq_zero.mp hneg

private noncomputable def nPlusSplit {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (g1 g2 : Submodule ℝ L) (z : ↥(g1 ⊔ g2)) : ↥g1 × ↥g2 :=
  let h := Submodule.mem_sup.mp z.2
  (⟨h.choose, h.choose_spec.1⟩, ⟨h.choose_spec.2.choose, h.choose_spec.2.choose_spec.1⟩)

private theorem nPlusSplit_add {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (g1 g2 : Submodule ℝ L) (z : ↥(g1 ⊔ g2)) :
    ((nPlusSplit g1 g2 z).1 : L) + ((nPlusSplit g1 g2 z).2 : L) = (z : L) :=
  (Submodule.mem_sup.mp z.2).choose_spec.2.choose_spec.2

private theorem nPlusSplit_eq_of_add {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {E : L} (g1 g2 : Submodule ℝ L)
    (h1 : ∀ x ∈ g1, ⁅E, x⁆ = (1 : ℝ) • x)
    (h2 : ∀ x ∈ g2, ⁅E, x⁆ = (2 : ℝ) • x)
    (p : ↥g1 × ↥g2) (z : ↥(g1 ⊔ g2)) (hz : (p.1 : L) + (p.2 : L) = (z : L)) :
    nPlusSplit g1 g2 z = p := by
  have hdisj : Disjoint g1 g2 := disjoint_grade_of_ad_eigen h1 h2
  have hspec := (nPlusSplit_add g1 g2 z).trans hz.symm
  have hdiff : ((nPlusSplit g1 g2 z).1 : L) - (p.1 : L) =
      (p.2 : L) - ((nPlusSplit g1 g2 z).2 : L) := by
    rw [sub_eq_sub_iff_add_eq_add]
    simpa [add_comm] using hspec
  have hz1 : ((nPlusSplit g1 g2 z).1 : L) - (p.1 : L) = 0 :=
    (Submodule.disjoint_def.mp hdisj) _
      (g1.sub_mem (nPlusSplit g1 g2 z).1.2 p.1.2)
      (by rw [hdiff]; exact g2.sub_mem p.2.2 (nPlusSplit g1 g2 z).2.2)
  have hz2 : (p.2 : L) - ((nPlusSplit g1 g2 z).2 : L) = 0 := hdiff.symm.trans hz1
  ext
  · exact sub_eq_zero.mp hz1
  · exact (sub_eq_zero.mp hz2).symm

/-- Canonical direct-sum equivalence `(g₁ × g₂) ≃ₗ[ℝ] (g₁ ⊔ g₂)` inside `L`. -/
def nPlusEquivProd {E : L} (g1 g2 : Submodule ℝ L)
    (h1 : ∀ x ∈ g1, ⁅E, x⁆ = (1 : ℝ) • x)
    (h2 : ∀ x ∈ g2, ⁅E, x⁆ = (2 : ℝ) • x) :
    (↥g1 × ↥g2) ≃ₗ[ℝ] ↥(g1 ⊔ g2) :=
  { toLinearMap :=
      (Submodule.inclusion (le_sup_left : g1 ≤ g1 ⊔ g2)).coprod
        (Submodule.inclusion (le_sup_right : g2 ≤ g1 ⊔ g2))
    invFun := nPlusSplit g1 g2
    left_inv := fun p => nPlusSplit_eq_of_add g1 g2 h1 h2 p _ rfl
    right_inv := fun z => Subtype.ext (nPlusSplit_add g1 g2 z) }

@[simp] theorem nPlusEquivProd_apply {E : L} (g1 g2 : Submodule ℝ L)
    (h1 : ∀ x ∈ g1, ⁅E, x⁆ = (1 : ℝ) • x)
    (h2 : ∀ x ∈ g2, ⁅E, x⁆ = (2 : ℝ) • x)
    (x : ↥g1) (y : ↥g2) :
    ((nPlusEquivProd g1 g2 h1 h2 (x, y) : ↥(g1 ⊔ g2)) : L) = (x : L) + (y : L) :=
  rfl

theorem adE_mapsTo_nPlus (E : L) (g1 g2 : Submodule ℝ L)
    (h1 : ∀ x ∈ g1, ⁅E, x⁆ = (1 : ℝ) • x)
    (h2 : ∀ x ∈ g2, ⁅E, x⁆ = (2 : ℝ) • x) :
    ∀ z ∈ g1 ⊔ g2, (LieAlgebra.ad ℝ L E) z ∈ g1 ⊔ g2 := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
  rw [map_add]
  change ⁅E, x⁆ + ⁅E, y⁆ ∈ g1 ⊔ g2
  rw [h1 x hx, h2 y hy]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (g1.smul_mem 1 hx))
    (Submodule.mem_sup_right (g2.smul_mem 2 hy))

/-- Restriction of `ad_E` to the positive nilradical `n₊ = g₁ ⊔ g₂`. -/
def adEOnNPlus (E : L) (g1 g2 : Submodule ℝ L)
    (h1 : ∀ x ∈ g1, ⁅E, x⁆ = (1 : ℝ) • x)
    (h2 : ∀ x ∈ g2, ⁅E, x⁆ = (2 : ℝ) • x) :
    Module.End ℝ ↥(g1 ⊔ g2) :=
  (LieAlgebra.ad ℝ L E).restrict (adE_mapsTo_nPlus E g1 g2 h1 h2)

theorem adEOnNPlus_conj_prodMap (E : L) (g1 g2 : Submodule ℝ L)
    (h1 : ∀ x ∈ g1, ⁅E, x⁆ = (1 : ℝ) • x)
    (h2 : ∀ x ∈ g2, ⁅E, x⁆ = (2 : ℝ) • x) :
    (nPlusEquivProd g1 g2 h1 h2).symm.conj (adEOnNPlus E g1 g2 h1 h2) =
      LinearMap.prodMap ((1 : ℝ) • (LinearMap.id : Module.End ℝ ↥g1))
        ((2 : ℝ) • (LinearMap.id : Module.End ℝ ↥g2)) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply (nPlusEquivProd g1 g2 h1 h2).injective
  apply Subtype.ext
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  change ⁅E, ((nPlusEquivProd g1 g2 h1 h2 (x, y) : ↥(g1 ⊔ g2)) : L)⁆ =
    (1 : ℝ) • (x : L) + (2 : ℝ) • (y : L)
  rw [nPlusEquivProd_apply, lie_add, h1 x.1 x.2, h2 y.1 y.2]

/-- **Weyl Trace Formula (`B4`)**:
`2ρ(E) = Tr_{n₊}(ad_E) = dim(g₁) + 2 · dim(g₂)` for any finite-dimensional `n₊ = g₁ ⊔ g₂`. -/
theorem weylTrace_nPlus_eq (E : L) (g1 g2 : Submodule ℝ L)
    [Module.Finite ℝ g1] [Module.Finite ℝ g2]
    (h1 : ∀ x ∈ g1, ⁅E, x⁆ = (1 : ℝ) • x)
    (h2 : ∀ x ∈ g2, ⁅E, x⁆ = (2 : ℝ) • x) :
    LinearMap.trace ℝ ↥(g1 ⊔ g2) (adEOnNPlus E g1 g2 h1 h2) =
      (Module.finrank ℝ g1 : ℝ) + 2 * (Module.finrank ℝ g2 : ℝ) := by
  let e : (↥g1 × ↥g2) ≃ₗ[ℝ] ↥(g1 ⊔ g2) := nPlusEquivProd g1 g2 h1 h2
  have htr :
      LinearMap.trace ℝ ↥(g1 ⊔ g2) (adEOnNPlus E g1 g2 h1 h2) =
        LinearMap.trace ℝ (↥g1 × ↥g2) (e.symm.conj (adEOnNPlus E g1 g2 h1 h2)) :=
    (LinearMap.trace_conj' (adEOnNPlus E g1 g2 h1 h2) e.symm).symm
  rw [htr]
  change LinearMap.trace ℝ (↥g1 × ↥g2)
      ((nPlusEquivProd g1 g2 h1 h2).symm.conj (adEOnNPlus E g1 g2 h1 h2)) = _
  rw [adEOnNPlus_conj_prodMap, LinearMap.trace_prodMap', map_smul, map_smul,
    LinearMap.trace_id, LinearMap.trace_id]
  simp [smul_eq_mul]

/-- Strict positivity `2ρ(E) > 0` whenever the positive nilradical `g₁ ⊔ g₂` is nontrivial. -/
theorem weylTrace_nPlus_pos (E : L) (g1 g2 : Submodule ℝ L)
    [Module.Finite ℝ g1] [Module.Finite ℝ g2]
    (h1 : ∀ x ∈ g1, ⁅E, x⁆ = (1 : ℝ) • x)
    (h2 : ∀ x ∈ g2, ⁅E, x⁆ = (2 : ℝ) • x)
    (hne : g1 ⊔ g2 ≠ ⊥) :
    0 < LinearMap.trace ℝ ↥(g1 ⊔ g2) (adEOnNPlus E g1 g2 h1 h2) := by
  rw [weylTrace_nPlus_eq E g1 g2 h1 h2]
  have hne12 : g1 ≠ ⊥ ∨ g2 ≠ ⊥ := by
    by_contra hboth
    push Not at hboth
    apply hne
    rw [hboth.1, hboth.2, bot_sup_eq]
  rcases hne12 with hne1 | hne2
  · have hpos : 0 < Module.finrank ℝ g1 := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hne1)
    have h1r : (0 : ℝ) < (Module.finrank ℝ g1 : ℝ) := by exact_mod_cast hpos
    have h2r : (0 : ℝ) ≤ (Module.finrank ℝ g2 : ℝ) := Nat.cast_nonneg _
    linarith
  · have hpos : 0 < Module.finrank ℝ g2 := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hne2)
    have h1r : (0 : ℝ) ≤ (Module.finrank ℝ g1 : ℝ) := Nat.cast_nonneg _
    have h2r : (0 : ℝ) < (Module.finrank ℝ g2 : ℝ) := by exact_mod_cast hpos
    linarith

end WeylTraceGeneral

/-! ## Section 2: Concrete 5-Graded Instantiations (`Sp4Contact`, `O55Contact`, `FreudenthalTKK5E8`) -/

section ConcreteWeylTraces

/-- Helper for `Sp4Contact.Sp` grade `+1` eigenvalue. -/
theorem sp4_grade_one_eigen :
    ∀ x ∈ InfoGeometry.Algebra.Sp4Contact.grade 1,
      ⁅InfoGeometry.Algebra.Sp4Contact.gradingElement, x⁆ = (1 : ℝ) • x := by
  intro x hx
  simpa using (InfoGeometry.Algebra.Sp4Contact.mem_grade_iff_lie 1 x).mp hx

/-- Helper for `Sp4Contact.Sp` grade `+2` eigenvalue. -/
theorem sp4_grade_two_eigen :
    ∀ x ∈ InfoGeometry.Algebra.Sp4Contact.grade 2,
      ⁅InfoGeometry.Algebra.Sp4Contact.gradingElement, x⁆ = (2 : ℝ) • x := by
  intro x hx
  simpa using (InfoGeometry.Algebra.Sp4Contact.mem_grade_iff_lie 2 x).mp hx

/-- For `Sp4Contact.Sp` (`1 + 2 + 4 + 2 + 1 = 10`), `2ρ(E) = 2 + 2·1 = 4`. -/
theorem sp4_weylTrace_eq_four :
    LinearMap.trace ℝ
        ↥(InfoGeometry.Algebra.Sp4Contact.grade 1 ⊔ InfoGeometry.Algebra.Sp4Contact.grade 2)
        (adEOnNPlus InfoGeometry.Algebra.Sp4Contact.gradingElement
          (InfoGeometry.Algebra.Sp4Contact.grade 1)
          (InfoGeometry.Algebra.Sp4Contact.grade 2)
          sp4_grade_one_eigen sp4_grade_two_eigen) = 4 := by
  rw [weylTrace_nPlus_eq, InfoGeometry.Algebra.Sp4Contact.finrank_grade_one,
    InfoGeometry.Algebra.Sp4Contact.finrank_grade_two]
  norm_num

/-! ### `O55Contact.O55Lie` (`so(5,5)`, `1 + 12 + 19 + 12 + 1 = 45`) -/

section O55Finrank

open InfoGeometry.Orthogonal.O55Contact

/-- Commutation of `blockComponent` with `endCommutator contactEulerEnd`. -/
theorem o55_endCommutator_blockComponent (d : BlockDegree) (A : End55) :
    endCommutator contactEulerEnd (blockComponent d A) =
      blockComponent d (endCommutator contactEulerEnd A) := by
  unfold blockComponent endCommutator
  have ht := (euler_mul_weightProjector d.target).trans (weightProjector_mul_euler d.target).symm
  have hs := (euler_mul_weightProjector d.source).trans (weightProjector_mul_euler d.source).symm
  simp only [mul_sub, sub_mul, mul_assoc]
  rw [← mul_assoc contactEulerEnd (weightProjector d.target), ht,
    mul_assoc (weightProjector d.target) contactEulerEnd, hs]

/-- Any `blockComponent` whose degree differs from the contact grade vanishes. -/
theorem o55_blockComponent_eq_zero_of_ne {k : ℤ} {A : O55Lie}
    (hA : A ∈ realContactGradeSpace k) (d : BlockDegree) (hd : d.contact ≠ k) :
    blockComponent d (A : End55) = 0 := by
  have h1 : endCommutator contactEulerEnd (blockComponent d (A : End55)) =
      (d.contact : ℝ) • blockComponent d (A : End55) := blockComponent_grade d (A : End55)
  have h2 : endCommutator contactEulerEnd (blockComponent d (A : End55)) =
      (k : ℝ) • blockComponent d (A : End55) := by
    rw [o55_endCommutator_blockComponent]
    rw [show endCommutator contactEulerEnd (A : End55) = (k : ℝ) • (A : End55) from hA]
    rw [blockComponent_smul]
  have hsub : ((d.contact : ℝ) - (k : ℝ)) • blockComponent d (A : End55) = 0 := by
    rw [sub_smul (d.contact : ℝ) (k : ℝ) (blockComponent d (A : End55)), ← h1, ← h2, sub_self]
  have hne : (d.contact : ℝ) - (k : ℝ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hd
  exact (smul_eq_zero.mp hsub).resolve_left hne

private theorem o55_vec_eq_sum (x : Vector55) :
    x = ∑ j : Fin 10, x j • coordinateVector j := by
  funext k
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, coordinateVector]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hbk; simp [Ne.symm hbk]
  · intro hk; exact False.elim (hk (Finset.mem_univ k))

private theorem fin_sum_univ_ten {α : Type*} [AddCommMonoid α] (f : Fin 10 → α) :
    ∑ j : Fin 10, f j =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  iterate 10 rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_zero, add_zero]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue]
  abel

private theorem o55_apply_basis_sum (B : End55) (x : Vector55) (i : Fin 10) :
    B x i = ∑ j : Fin 10, x j * B (coordinateVector j) i := by
  conv_lhs => rw [o55_vec_eq_sum x, map_sum]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [smul_eq_mul]

private theorem o55_splitPairing_e0 (y : Vector55) :
    splitPairing y (coordinateVector 0) = y 8 := by
  simpa [dualIndex] using splitPairing_coordinate_right y 8

private theorem o55_splitPairing_e1 (y : Vector55) :
    splitPairing y (coordinateVector 1) = y 9 := by
  simpa [dualIndex] using splitPairing_coordinate_right y 9

private theorem o55_splitPairing_mid (y : Vector55) (m : Fin 6) :
    splitPairing y (coordinateVector ⟨m.val + 2, by omega⟩) =
      if m.val < 3 then y ⟨m.val + 2, by omega⟩ else -y ⟨m.val + 2, by omega⟩ := by
  fin_cases m
  · simpa [dualIndex] using splitPairing_coordinate_right y 2
  · simpa [dualIndex] using splitPairing_coordinate_right y 3
  · simpa [dualIndex] using splitPairing_coordinate_right y 4
  · simpa [dualIndex] using splitPairing_coordinate_right y 5
  · simpa [dualIndex] using splitPairing_coordinate_right y 6
  · simpa [dualIndex] using splitPairing_coordinate_right y 7

private def o55GradeTwoEnd (c : ℝ) : End55 where
  toFun x i := if i = 8 then c * x 1 else if i = 9 then -c * x 0 else 0
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp <;> ring

private theorem o55GradeTwoEnd_isSplitSkew (c : ℝ) : IsSplitSkew (o55GradeTwoEnd c) := by
  intro x y
  simp [splitPairing, o55GradeTwoEnd]
  ring

private theorem o55GradeTwoEnd_isContactGrade (c : ℝ) :
    IsContactGrade 2 ⟨o55GradeTwoEnd c, o55GradeTwoEnd_isSplitSkew c⟩ := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i <;>
    simp [endCommutator_apply, contactEulerEnd_apply, contactWeightR, contactWeight,
      o55GradeTwoEnd] <;> ring

/-- Explicit linear equivalence `realContactGradeSpace 2 ≃ₗ[ℝ] ℝ` for `so(5,5)`. -/
def o55_gradePlusTwoEquiv : realContactGradeSpace 2 ≃ₗ[ℝ] ℝ where
  toFun A := ((A : O55Lie) : End55) (coordinateVector 1) 8
  invFun c := ⟨⟨o55GradeTwoEnd c, o55GradeTwoEnd_isSplitSkew c⟩,
    o55GradeTwoEnd_isContactGrade c⟩
  map_add' A B := by simp
  map_smul' r A := by simp
  left_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    have hA : ((A : O55Lie) : End55) = gradePlusTwoPart ((A : O55Lie) : End55) := by
      have hm2 := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.minus, Weight3.plus⟩ (by decide)
      have hm1a := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.minus, Weight3.zero⟩ (by decide)
      have hm1b := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.zero, Weight3.plus⟩ (by decide)
      have h0a := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.minus, Weight3.minus⟩ (by decide)
      have h0b := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.zero, Weight3.zero⟩ (by decide)
      have h0c := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.plus, Weight3.plus⟩ (by decide)
      have hp1a := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.zero, Weight3.minus⟩ (by decide)
      have hp1b := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.plus, Weight3.zero⟩ (by decide)
      have hdec := endomorphism_grade_decomposition ((A : O55Lie) : End55)
      unfold gradeMinusTwoPart gradeMinusOnePart gradeZeroPart gradePlusOnePart at hdec
      rw [hm2, hm1a, hm1b, h0a, h0b, h0c, hp1a, hp1b] at hdec
      simpa using hdec
    have hcol : ∀ j i : Fin 10,
        (j ≠ 0 ∧ j ≠ 1 ∨ i ≠ 8 ∧ i ≠ 9) →
        ((A : O55Lie) : End55) (coordinateVector j) i = 0 := by
      intro j i hij
      have hbc : ((A : O55Lie) : End55) (coordinateVector j) i =
          gradePlusTwoPart ((A : O55Lie) : End55) (coordinateVector j) i := by
        rw [← hA]
      rw [hbc, gradePlusTwoPart, blockComponent]
      simp only [Module.End.mul_apply, weightProjector_apply]
      rcases hij with ⟨hj0, hj1⟩ | ⟨hi8, hi9⟩
      · have hw : weightOfIndex j ≠ Weight3.minus := by
          fin_cases j <;> first | exact absurd rfl hj0 | exact absurd rfl hj1 | decide
        have hzero : weightProjector Weight3.minus (coordinateVector j) = 0 := by
          funext t
          by_cases ht : t = j
          · subst ht; simp only [weightProjector_apply, hw, ↓reduceIte]; rfl
          · simp only [weightProjector_apply, coordinateVector, ht, ↓reduceIte, ite_self]; rfl
        rw [hzero, map_zero]
        simp only [Pi.zero_apply, ite_self]
      · have hw : weightOfIndex i ≠ Weight3.plus := by
          fin_cases i <;> first | exact absurd rfl hi8 | exact absurd rfl hi9 | decide
        simp only [hw, ↓reduceIte]
    have hrow_zero : ∀ i : Fin 10, i ≠ 8 ∧ i ≠ 9 →
        ((A : O55Lie) : End55) x i = 0 := by
      intro i hi
      rw [o55_apply_basis_sum]
      exact Finset.sum_eq_zero fun j _ => by rw [hcol j i (Or.inr hi), mul_zero]
    have hskew := (A : O55Lie).2
    have h08 : ((A : O55Lie) : End55) (coordinateVector 0) 8 = 0 := by
      have hs := hskew (coordinateVector 0) (coordinateVector 0)
      have h00 := o55_splitPairing_e0 (((A : O55Lie) : End55) (coordinateVector 0))
      have h00' : splitPairing (coordinateVector 0) (((A : O55Lie) : End55) (coordinateVector 0)) =
          ((A : O55Lie) : End55) (coordinateVector 0) 8 :=
        (splitPairing_comm _ _).trans h00
      linarith
    have h19 : ((A : O55Lie) : End55) (coordinateVector 1) 9 = 0 := by
      have hs := hskew (coordinateVector 1) (coordinateVector 1)
      have h11 := o55_splitPairing_e1 (((A : O55Lie) : End55) (coordinateVector 1))
      have h11' : splitPairing (coordinateVector 1) (((A : O55Lie) : End55) (coordinateVector 1)) =
          ((A : O55Lie) : End55) (coordinateVector 1) 9 :=
        (splitPairing_comm _ _).trans h11
      linarith
    have h09 : ((A : O55Lie) : End55) (coordinateVector 0) 9 =
        -((A : O55Lie) : End55) (coordinateVector 1) 8 := by
      have hs := hskew (coordinateVector 0) (coordinateVector 1)
      have ha := o55_splitPairing_e1 (((A : O55Lie) : End55) (coordinateVector 0))
      have hb : splitPairing (coordinateVector 0) (((A : O55Lie) : End55) (coordinateVector 1)) =
          ((A : O55Lie) : End55) (coordinateVector 1) 8 :=
        (splitPairing_comm _ _).trans (o55_splitPairing_e0 _)
      linarith
    funext i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
        i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hrow_zero 0 (by decide)).symm
    · exact (hrow_zero 1 (by decide)).symm
    · exact (hrow_zero 2 (by decide)).symm
    · exact (hrow_zero 3 (by decide)).symm
    · exact (hrow_zero 4 (by decide)).symm
    · exact (hrow_zero 5 (by decide)).symm
    · exact (hrow_zero 6 (by decide)).symm
    · exact (hrow_zero 7 (by decide)).symm
    · symm
      rw [o55_apply_basis_sum ((A : O55Lie) : End55) x 8, fin_sum_univ_ten]
      rw [h08, hcol 2 8 (Or.inl (by decide)), hcol 3 8 (Or.inl (by decide)),
        hcol 4 8 (Or.inl (by decide)), hcol 5 8 (Or.inl (by decide)),
        hcol 6 8 (Or.inl (by decide)), hcol 7 8 (Or.inl (by decide)),
        hcol 8 8 (Or.inl (by decide)), hcol 9 8 (Or.inl (by decide))]
      simp only [o55GradeTwoEnd, LinearMap.coe_mk, AddHom.coe_mk, mul_zero, add_zero, zero_add]
      simp only [ite_true]
      ring
    · symm
      rw [o55_apply_basis_sum ((A : O55Lie) : End55) x 9, fin_sum_univ_ten]
      rw [h09, h19, hcol 2 9 (Or.inl (by decide)), hcol 3 9 (Or.inl (by decide)),
        hcol 4 9 (Or.inl (by decide)), hcol 5 9 (Or.inl (by decide)),
        hcol 6 9 (Or.inl (by decide)), hcol 7 9 (Or.inl (by decide)),
        hcol 8 9 (Or.inl (by decide)), hcol 9 9 (Or.inl (by decide))]
      simp only [o55GradeTwoEnd, LinearMap.coe_mk, AddHom.coe_mk, mul_zero, add_zero, neg_mul]
      simp only [ite_true]
      split_ifs with h98
      · exact absurd h98 (by decide)
      · ring
  right_inv c := by
    simp [o55GradeTwoEnd, coordinateVector]

/-- Exact dimension `dim(g₂) = 1` for `O55Contact.O55Lie`. -/
theorem o55_finrank_grade_two : Module.finrank ℝ (realContactGradeSpace 2) = 1 := by
  rw [o55_gradePlusTwoEquiv.finrank_eq, Module.finrank_self]

private def o55GradeOneEnd (M : Fin 2 → Fin 6 → ℝ) : End55 where
  toFun x i := match i with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => M 0 0 * x 0 + M 1 0 * x 1
    | ⟨3, _⟩ => M 0 1 * x 0 + M 1 1 * x 1
    | ⟨4, _⟩ => M 0 2 * x 0 + M 1 2 * x 1
    | ⟨5, _⟩ => M 0 3 * x 0 + M 1 3 * x 1
    | ⟨6, _⟩ => M 0 4 * x 0 + M 1 4 * x 1
    | ⟨7, _⟩ => M 0 5 * x 0 + M 1 5 * x 1
    | ⟨8, _⟩ => -(M 0 0 * x 2 + M 0 1 * x 3 + M 0 2 * x 4 -
        M 0 3 * x 5 - M 0 4 * x 6 - M 0 5 * x 7)
    | ⟨9, _⟩ => -(M 1 0 * x 2 + M 1 1 * x 3 + M 1 2 * x 4 -
        M 1 3 * x 5 - M 1 4 * x 6 - M 1 5 * x 7)
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp <;> ring

private theorem o55GradeOneEnd_isSplitSkew (M : Fin 2 → Fin 6 → ℝ) :
    IsSplitSkew (o55GradeOneEnd M) := by
  intro x y
  simp [splitPairing, o55GradeOneEnd]
  ring

private theorem o55GradeOneEnd_isContactGrade (M : Fin 2 → Fin 6 → ℝ) :
    IsContactGrade 1 ⟨o55GradeOneEnd M, o55GradeOneEnd_isSplitSkew M⟩ := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i <;>
    simp [endCommutator_apply, contactEulerEnd_apply, contactWeightR, contactWeight,
      o55GradeOneEnd] <;> ring

private def o55OuterIdx : Fin 2 → Fin 10
  | 0 => 0
  | 1 => 1

private def o55MidIdx : Fin 6 → Fin 10
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 6
  | 5 => 7

private def o55PlusIdx : Fin 2 → Fin 10
  | 0 => 8
  | 1 => 9

private theorem o55GradeOneEnd_eval (M : Fin 2 → Fin 6 → ℝ) (j : Fin 2) (m : Fin 6) :
    o55GradeOneEnd M (coordinateVector (o55OuterIdx j)) (o55MidIdx m) = M j m := by
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;>
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    (dsimp only [o55OuterIdx, o55MidIdx, o55GradeOneEnd, LinearMap.coe_mk, AddHom.coe_mk];
     simp [coordinateVector])

private theorem o55_gradeOne_left_inv (A : realContactGradeSpace 1) :
    (⟨⟨o55GradeOneEnd (fun j m => ((A : O55Lie) : End55) (coordinateVector (o55OuterIdx j))
        (o55MidIdx m)),
      o55GradeOneEnd_isSplitSkew _⟩,
      o55GradeOneEnd_isContactGrade _⟩ : realContactGradeSpace 1) = A := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  have hA : ((A : O55Lie) : End55) = gradePlusOnePart ((A : O55Lie) : End55) := by
    have hm2 := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.minus, Weight3.plus⟩ (by decide)
    have hm1a := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.minus, Weight3.zero⟩ (by decide)
    have hm1b := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.zero, Weight3.plus⟩ (by decide)
    have h0a := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.minus, Weight3.minus⟩ (by decide)
    have h0b := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.zero, Weight3.zero⟩ (by decide)
    have h0c := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.plus, Weight3.plus⟩ (by decide)
    have hp2 := o55_blockComponent_eq_zero_of_ne A.2 ⟨Weight3.plus, Weight3.minus⟩ (by decide)
    have hdec := endomorphism_grade_decomposition ((A : O55Lie) : End55)
    unfold gradeMinusTwoPart gradeMinusOnePart gradeZeroPart gradePlusTwoPart at hdec
    rw [hm2, hm1a, hm1b, h0a, h0b, h0c, hp2] at hdec
    simpa using hdec
  have hcomp : ∀ j i : Fin 10,
      ((A : O55Lie) : End55) (coordinateVector j) i =
        gradePlusOnePart ((A : O55Lie) : End55) (coordinateVector j) i := fun j i => by
    rw [← hA]
  have hvan : ∀ j i : Fin 10,
      ¬((weightOfIndex j = Weight3.minus ∧ weightOfIndex i = Weight3.zero) ∨
        (weightOfIndex j = Weight3.zero ∧ weightOfIndex i = Weight3.plus)) →
      ((A : O55Lie) : End55) (coordinateVector j) i = 0 := by
    intro j i hij
    rw [hcomp j i, gradePlusOnePart, LinearMap.add_apply, blockComponent, blockComponent]
    simp only [Module.End.mul_apply]
    have h1 : weightProjector Weight3.zero (((A : O55Lie) : End55)
        (weightProjector Weight3.minus (coordinateVector j))) i = 0 := by
      by_cases hj : weightOfIndex j = Weight3.minus
      · have hi : weightOfIndex i ≠ Weight3.zero := fun h => hij (Or.inl ⟨hj, h⟩)
        simp [weightProjector_apply, hi]
      · have hzero : weightProjector Weight3.minus (coordinateVector j) = 0 := by
          funext t
          by_cases ht : t = j
          · subst ht; simp [hj]
          · simp [coordinateVector, ht]
        rw [hzero, map_zero, map_zero]; rfl
    have h2 : weightProjector Weight3.plus (((A : O55Lie) : End55)
        (weightProjector Weight3.zero (coordinateVector j))) i = 0 := by
      by_cases hj : weightOfIndex j = Weight3.zero
      · have hi : weightOfIndex i ≠ Weight3.plus := fun h => hij (Or.inr ⟨hj, h⟩)
        simp [weightProjector_apply, hi]
      · have hzero : weightProjector Weight3.zero (coordinateVector j) = 0 := by
          funext t
          by_cases ht : t = j
          · subst ht; simp [hj]
          · simp [coordinateVector, ht]
        rw [hzero, map_zero, map_zero]; rfl
    simp [Pi.add_apply, h1, h2]
  have hskew := (A : O55Lie).2
  have hpair_pos : ∀ j : Fin 2, ∀ m : Fin 3,
      ((A : O55Lie) : End55) (coordinateVector (o55MidIdx ⟨m.val, by omega⟩)) (o55PlusIdx j) =
        -((A : O55Lie) : End55) (coordinateVector (o55OuterIdx j))
          (o55MidIdx ⟨m.val, by omega⟩) := by
    intro j m
    have hs := hskew (coordinateVector (o55OuterIdx j))
      (coordinateVector (o55MidIdx ⟨m.val, by omega⟩))
    have h1 := o55_splitPairing_mid (((A : O55Lie) : End55) (coordinateVector (o55OuterIdx j)))
      ⟨m.val, by omega⟩
    have hm : m.val < 3 := m.isLt
    simp only [hm, ↓reduceIte] at h1
    have h1' : splitPairing (((A : O55Lie) : End55) (coordinateVector (o55OuterIdx j)))
        (coordinateVector (o55MidIdx ⟨m.val, by omega⟩)) =
        ((A : O55Lie) : End55) (coordinateVector (o55OuterIdx j))
          (o55MidIdx ⟨m.val, by omega⟩) := by
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl <;> exact h1
    have h2 : splitPairing (coordinateVector (o55OuterIdx j))
        (((A : O55Lie) : End55) (coordinateVector (o55MidIdx ⟨m.val, by omega⟩))) =
        ((A : O55Lie) : End55) (coordinateVector (o55MidIdx ⟨m.val, by omega⟩))
          (o55PlusIdx j) := by
      rw [splitPairing_comm]
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact o55_splitPairing_e0 _
      · exact o55_splitPairing_e1 _
    linarith
  have hpair_neg : ∀ j : Fin 2, ∀ m : Fin 3,
      ((A : O55Lie) : End55) (coordinateVector (o55MidIdx ⟨m.val + 3, by omega⟩))
          (o55PlusIdx j) =
        ((A : O55Lie) : End55) (coordinateVector (o55OuterIdx j))
          (o55MidIdx ⟨m.val + 3, by omega⟩) := by
    intro j m
    have hs := hskew (coordinateVector (o55OuterIdx j))
      (coordinateVector (o55MidIdx ⟨m.val + 3, by omega⟩))
    have h1 := o55_splitPairing_mid (((A : O55Lie) : End55) (coordinateVector (o55OuterIdx j)))
      ⟨m.val + 3, by omega⟩
    have hm : ¬(m.val + 3 < 3) := by omega
    simp only [hm, ↓reduceIte] at h1
    have h1' : splitPairing (((A : O55Lie) : End55) (coordinateVector (o55OuterIdx j)))
        (coordinateVector (o55MidIdx ⟨m.val + 3, by omega⟩)) =
        -((A : O55Lie) : End55) (coordinateVector (o55OuterIdx j))
          (o55MidIdx ⟨m.val + 3, by omega⟩) := by
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl <;> exact h1
    have h2 : splitPairing (coordinateVector (o55OuterIdx j))
        (((A : O55Lie) : End55) (coordinateVector (o55MidIdx ⟨m.val + 3, by omega⟩))) =
        ((A : O55Lie) : End55) (coordinateVector (o55MidIdx ⟨m.val + 3, by omega⟩))
          (o55PlusIdx j) := by
      rw [splitPairing_comm]
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact o55_splitPairing_e0 _
      · exact o55_splitPairing_e1 _
    linarith
  have hrow01 : ∀ i : Fin 10, i = 0 ∨ i = 1 → ((A : O55Lie) : End55) x i = 0 := by
    intro i hi
    rw [o55_apply_basis_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hw : ¬((weightOfIndex j = Weight3.minus ∧ weightOfIndex i = Weight3.zero) ∨
        (weightOfIndex j = Weight3.zero ∧ weightOfIndex i = Weight3.plus)) := by
      rcases hi with rfl | rfl <;> simp [weightOfIndex]
    rw [hvan j i hw, mul_zero]
  funext i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
      i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hrow01 0 (Or.inl rfl)).symm
  · exact (hrow01 1 (Or.inr rfl)).symm
  · symm; rw [o55_apply_basis_sum ((A : O55Lie) : End55) x 2, fin_sum_univ_ten]
    rw [hvan 2 2 (by decide), hvan 3 2 (by decide), hvan 4 2 (by decide),
      hvan 5 2 (by decide), hvan 6 2 (by decide), hvan 7 2 (by decide),
      hvan 8 2 (by decide), hvan 9 2 (by decide)]
    simp only [o55GradeOneEnd, LinearMap.coe_mk, AddHom.coe_mk, mul_zero, add_zero]
    dsimp only [o55OuterIdx, o55MidIdx]; ring
  · symm; rw [o55_apply_basis_sum ((A : O55Lie) : End55) x 3, fin_sum_univ_ten]
    rw [hvan 2 3 (by decide), hvan 3 3 (by decide), hvan 4 3 (by decide),
      hvan 5 3 (by decide), hvan 6 3 (by decide), hvan 7 3 (by decide),
      hvan 8 3 (by decide), hvan 9 3 (by decide)]
    simp only [o55GradeOneEnd, LinearMap.coe_mk, AddHom.coe_mk, mul_zero, add_zero]
    dsimp only [o55OuterIdx, o55MidIdx]; ring
  · symm; rw [o55_apply_basis_sum ((A : O55Lie) : End55) x 4, fin_sum_univ_ten]
    rw [hvan 2 4 (by decide), hvan 3 4 (by decide), hvan 4 4 (by decide),
      hvan 5 4 (by decide), hvan 6 4 (by decide), hvan 7 4 (by decide),
      hvan 8 4 (by decide), hvan 9 4 (by decide)]
    simp only [o55GradeOneEnd, LinearMap.coe_mk, AddHom.coe_mk, mul_zero, add_zero]
    dsimp only [o55OuterIdx, o55MidIdx]; ring
  · symm; rw [o55_apply_basis_sum ((A : O55Lie) : End55) x 5, fin_sum_univ_ten]
    rw [hvan 2 5 (by decide), hvan 3 5 (by decide), hvan 4 5 (by decide),
      hvan 5 5 (by decide), hvan 6 5 (by decide), hvan 7 5 (by decide),
      hvan 8 5 (by decide), hvan 9 5 (by decide)]
    simp only [o55GradeOneEnd, LinearMap.coe_mk, AddHom.coe_mk, mul_zero, add_zero]
    dsimp only [o55OuterIdx, o55MidIdx]; ring
  · symm; rw [o55_apply_basis_sum ((A : O55Lie) : End55) x 6, fin_sum_univ_ten]
    rw [hvan 2 6 (by decide), hvan 3 6 (by decide), hvan 4 6 (by decide),
      hvan 5 6 (by decide), hvan 6 6 (by decide), hvan 7 6 (by decide),
      hvan 8 6 (by decide), hvan 9 6 (by decide)]
    simp only [o55GradeOneEnd, LinearMap.coe_mk, AddHom.coe_mk, mul_zero, add_zero]
    dsimp only [o55OuterIdx, o55MidIdx]; ring
  · symm; rw [o55_apply_basis_sum ((A : O55Lie) : End55) x 7, fin_sum_univ_ten]
    rw [hvan 2 7 (by decide), hvan 3 7 (by decide), hvan 4 7 (by decide),
      hvan 5 7 (by decide), hvan 6 7 (by decide), hvan 7 7 (by decide),
      hvan 8 7 (by decide), hvan 9 7 (by decide)]
    simp only [o55GradeOneEnd, LinearMap.coe_mk, AddHom.coe_mk, mul_zero, add_zero]
    dsimp only [o55OuterIdx, o55MidIdx]; ring
  · symm; rw [o55_apply_basis_sum ((A : O55Lie) : End55) x 8, fin_sum_univ_ten]
    have hp0 : ((A : O55Lie) : End55) (coordinateVector 2) 8 =
        -((A : O55Lie) : End55) (coordinateVector 0) 2 := hpair_pos 0 0
    have hp1 : ((A : O55Lie) : End55) (coordinateVector 3) 8 =
        -((A : O55Lie) : End55) (coordinateVector 0) 3 := hpair_pos 0 1
    have hp2 : ((A : O55Lie) : End55) (coordinateVector 4) 8 =
        -((A : O55Lie) : End55) (coordinateVector 0) 4 := hpair_pos 0 2
    have hn0 : ((A : O55Lie) : End55) (coordinateVector 5) 8 =
        ((A : O55Lie) : End55) (coordinateVector 0) 5 := hpair_neg 0 0
    have hn1 : ((A : O55Lie) : End55) (coordinateVector 6) 8 =
        ((A : O55Lie) : End55) (coordinateVector 0) 6 := hpair_neg 0 1
    have hn2 : ((A : O55Lie) : End55) (coordinateVector 7) 8 =
        ((A : O55Lie) : End55) (coordinateVector 0) 7 := hpair_neg 0 2
    rw [hvan 0 8 (by decide), hvan 1 8 (by decide), hvan 8 8 (by decide), hvan 9 8 (by decide),
      hp0, hp1, hp2, hn0, hn1, hn2]
    simp only [o55GradeOneEnd, LinearMap.coe_mk, AddHom.coe_mk, mul_zero, add_zero, zero_add]
    dsimp only [o55OuterIdx, o55MidIdx]; ring
  · symm; rw [o55_apply_basis_sum ((A : O55Lie) : End55) x 9, fin_sum_univ_ten]
    have hp0 : ((A : O55Lie) : End55) (coordinateVector 2) 9 =
        -((A : O55Lie) : End55) (coordinateVector 1) 2 := hpair_pos 1 0
    have hp1 : ((A : O55Lie) : End55) (coordinateVector 3) 9 =
        -((A : O55Lie) : End55) (coordinateVector 1) 3 := hpair_pos 1 1
    have hp2 : ((A : O55Lie) : End55) (coordinateVector 4) 9 =
        -((A : O55Lie) : End55) (coordinateVector 1) 4 := hpair_pos 1 2
    have hn0 : ((A : O55Lie) : End55) (coordinateVector 5) 9 =
        ((A : O55Lie) : End55) (coordinateVector 1) 5 := hpair_neg 1 0
    have hn1 : ((A : O55Lie) : End55) (coordinateVector 6) 9 =
        ((A : O55Lie) : End55) (coordinateVector 1) 6 := hpair_neg 1 1
    have hn2 : ((A : O55Lie) : End55) (coordinateVector 7) 9 =
        ((A : O55Lie) : End55) (coordinateVector 1) 7 := hpair_neg 1 2
    rw [hvan 0 9 (by decide), hvan 1 9 (by decide), hvan 8 9 (by decide), hvan 9 9 (by decide),
      hp0, hp1, hp2, hn0, hn1, hn2]
    simp only [o55GradeOneEnd, LinearMap.coe_mk, AddHom.coe_mk, mul_zero, add_zero, zero_add]
    dsimp only [o55OuterIdx, o55MidIdx]; ring

/-- Explicit linear equivalence `realContactGradeSpace 1 ≃ₗ[ℝ] (Fin 2 → Fin 6 → ℝ)` for `so(5,5)`. -/
def o55_gradePlusOneEquiv : realContactGradeSpace 1 ≃ₗ[ℝ] (Fin 2 → Fin 6 → ℝ) where
  toFun A j m := ((A : O55Lie) : End55) (coordinateVector (o55OuterIdx j)) (o55MidIdx m)
  invFun M := ⟨⟨o55GradeOneEnd M, o55GradeOneEnd_isSplitSkew M⟩,
    o55GradeOneEnd_isContactGrade M⟩
  map_add' A B := by funext j m; simp
  map_smul' r A := by funext j m; simp
  left_inv := o55_gradeOne_left_inv
  right_inv M := by funext j m; exact o55GradeOneEnd_eval M j m

/-- Exact dimension `dim(g₁) = 12` for `O55Contact.O55Lie`. -/
theorem o55_finrank_grade_one : Module.finrank ℝ (realContactGradeSpace 1) = 12 := by
  rw [o55_gradePlusOneEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp

/-- Helper for `O55Contact.O55Lie` grade `+1` eigenvalue. -/
theorem o55_grade_one_eigen :
    ∀ x ∈ realContactGradeSpace 1, ⁅contactEuler, x⁆ = (1 : ℝ) • x := by
  intro x hx
  apply Subtype.ext
  have hx' : endCommutator contactEulerEnd (x : End55) = ((1 : ℤ) : ℝ) • (x : End55) := hx
  change contactEulerEnd * (x : End55) - (x : End55) * contactEulerEnd = (1 : ℝ) • (x : End55)
  simpa [endCommutator] using hx'

/-- Helper for `O55Contact.O55Lie` grade `+2` eigenvalue. -/
theorem o55_grade_two_eigen :
    ∀ x ∈ realContactGradeSpace 2, ⁅contactEuler, x⁆ = (2 : ℝ) • x := by
  intro x hx
  apply Subtype.ext
  have hx' : endCommutator contactEulerEnd (x : End55) = ((2 : ℤ) : ℝ) • (x : End55) := hx
  change contactEulerEnd * (x : End55) - (x : End55) * contactEulerEnd = (2 : ℝ) • (x : End55)
  simpa [endCommutator] using hx'

/-- For `O55Contact.O55Lie` (`so(5,5)`), `2ρ(E) = 12 + 2·1 = 14`. -/
theorem o55_weylTrace_eq_fourteen :
    LinearMap.trace ℝ
        ↥(realContactGradeSpace 1 ⊔ realContactGradeSpace 2)
        (adEOnNPlus contactEuler (realContactGradeSpace 1) (realContactGradeSpace 2)
          o55_grade_one_eigen o55_grade_two_eigen) = 14 := by
  rw [weylTrace_nPlus_eq, o55_finrank_grade_one, o55_finrank_grade_two]
  norm_num

end O55Finrank

/-! ### `FreudenthalTKK5E8` (`e_{8(8)}`, `1 + 56 + 134 + 56 + 1 = 248`) -/

section E8WeylTrace

/-- Helper for `FreudenthalTKK5E8` grade `+1` eigenvalue. -/
theorem e8_grade_one_eigen :
    ∀ U ∈ gGrade 1, ⁅gradeCenterZ, U⁆ = (1 : ℝ) • U := by
  intro U hU
  obtain ⟨h0, h1, h2, h3, h5⟩ := (mem_gGrade_pos_one_iff U).mp hU
  change bracket5LM (injZeroCenter 1) U = (1 : ℝ) • U
  apply FreudenthalTKK5E8.ext <;>
    simp [injZeroCenter, h0, h1, h2, h3, h5]

/-- Helper for `FreudenthalTKK5E8` grade `+2` eigenvalue. -/
theorem e8_grade_two_eigen :
    ∀ U ∈ gGrade 2, ⁅gradeCenterZ, U⁆ = (2 : ℝ) • U := by
  intro U hU
  obtain ⟨h0, h1, h2, h3, h4⟩ := (mem_gGrade_pos_two_iff U).mp hU
  change bracket5LM (injZeroCenter 1) U = (2 : ℝ) • U
  apply FreudenthalTKK5E8.ext <;>
    simp [injZeroCenter, h0, h1, h2, h3, h4]

/-- For `FreudenthalTKK5E8` (`e_{8(8)}`), `2ρ(Z) = 56 + 2·1 = 58`. -/
theorem e8_weylTrace_eq_fiftyEight :
    LinearMap.trace ℝ ↥(gGrade 1 ⊔ gGrade 2)
        (adEOnNPlus gradeCenterZ (gGrade 1) (gGrade 2) e8_grade_one_eigen e8_grade_two_eigen) =
      58 := by
  rw [weylTrace_nPlus_eq, finrank_gGrade_pos_one, finrank_gGrade_pos_two]
  norm_num

end E8WeylTrace

end ConcreteWeylTraces

/-! ## Section 3: C2 — Lie-Flow Jacobian Determinant `det(exp(t ad_E)) = exp(t · 2ρ(E))` -/

section LieFlowJacobian

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- **Lie-Flow Determinant Identity (`C2`)**:
In any basis `b` of `n₊ = g₁ ⊔ g₂`, `det(exp(t · ad_E|_{n₊})) = exp(t · (dim g₁ + 2 dim g₂))`. -/
theorem lieFlow_det_nPlus_eq_exp_weylTrace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : L) (g1 g2 : Submodule ℝ L)
    [Module.Finite ℝ g1] [Module.Finite ℝ g2]
    (h1 : ∀ x ∈ g1, ⁅E, x⁆ = (1 : ℝ) • x)
    (h2 : ∀ x ∈ g2, ⁅E, x⁆ = (2 : ℝ) • x)
    (b : Module.Basis ι ℝ ↥(g1 ⊔ g2)) (t : ℝ) :
    (lieExponentialPath (LinearMap.toMatrix b b (adEOnNPlus E g1 g2 h1 h2)) t).det =
      Real.exp (t * ((Module.finrank ℝ g1 : ℝ) + 2 * (Module.finrank ℝ g2 : ℝ))) := by
  rw [det_lieExponentialPath, ← LinearMap.trace_eq_matrix_trace ℝ b, weylTrace_nPlus_eq]

/-- Strict volume expansion `det(J_Lie(t)) > 1` for `t > 0` when `n₊ ≠ ⊥`. -/
theorem lieFlow_det_nPlus_gt_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : L) (g1 g2 : Submodule ℝ L)
    [Module.Finite ℝ g1] [Module.Finite ℝ g2]
    (h1 : ∀ x ∈ g1, ⁅E, x⁆ = (1 : ℝ) • x)
    (h2 : ∀ x ∈ g2, ⁅E, x⁆ = (2 : ℝ) • x)
    (hne : g1 ⊔ g2 ≠ ⊥) (b : Module.Basis ι ℝ ↥(g1 ⊔ g2)) {t : ℝ} (ht : 0 < t) :
    1 < (lieExponentialPath (LinearMap.toMatrix b b (adEOnNPlus E g1 g2 h1 h2)) t).det := by
  rw [lieFlow_det_nPlus_eq_exp_weylTrace, Real.one_lt_exp_iff]
  have hpos := weylTrace_nPlus_pos E g1 g2 h1 h2 hne
  rw [weylTrace_nPlus_eq] at hpos
  exact mul_pos ht hpos

/-- `Sp4Contact.Sp` Lie-flow Jacobian determinant `exp(4t)`. -/
theorem sp4_lieFlow_det_nPlus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ ↥(InfoGeometry.Algebra.Sp4Contact.grade 1 ⊔
      InfoGeometry.Algebra.Sp4Contact.grade 2)) (t : ℝ) :
    (lieExponentialPath (LinearMap.toMatrix b b
      (adEOnNPlus InfoGeometry.Algebra.Sp4Contact.gradingElement
        (InfoGeometry.Algebra.Sp4Contact.grade 1)
        (InfoGeometry.Algebra.Sp4Contact.grade 2)
        sp4_grade_one_eigen sp4_grade_two_eigen)) t).det =
      Real.exp (t * 4) := by
  rw [det_lieExponentialPath, ← LinearMap.trace_eq_matrix_trace ℝ b, sp4_weylTrace_eq_four]

/-- `O55Contact.O55Lie` Lie-flow Jacobian determinant `exp(14t)`. -/
theorem o55_lieFlow_det_nPlus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ ↥(InfoGeometry.Orthogonal.O55Contact.realContactGradeSpace 1 ⊔
      InfoGeometry.Orthogonal.O55Contact.realContactGradeSpace 2)) (t : ℝ) :
    (lieExponentialPath (LinearMap.toMatrix b b
      (adEOnNPlus InfoGeometry.Orthogonal.O55Contact.contactEuler
        (InfoGeometry.Orthogonal.O55Contact.realContactGradeSpace 1)
        (InfoGeometry.Orthogonal.O55Contact.realContactGradeSpace 2)
        o55_grade_one_eigen o55_grade_two_eigen)) t).det =
      Real.exp (t * 14) := by
  rw [det_lieExponentialPath, ← LinearMap.trace_eq_matrix_trace ℝ b, o55_weylTrace_eq_fourteen]

/-- `FreudenthalTKK5E8` Lie-flow Jacobian determinant `exp(58t)`. -/
theorem e8_lieFlow_det_nPlus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ ↥(gGrade 1 ⊔ gGrade 2)) (t : ℝ) :
    (lieExponentialPath (LinearMap.toMatrix b b
      (adEOnNPlus gradeCenterZ (gGrade 1) (gGrade 2) e8_grade_one_eigen e8_grade_two_eigen))
        t).det =
      Real.exp (t * 58) := by
  rw [det_lieExponentialPath, ← LinearMap.trace_eq_matrix_trace ℝ b, e8_weylTrace_eq_fiftyEight]

end LieFlowJacobian

/-! ## Section 4: B2 — Bigraded `(k, ε)` Supercommutator, Super-Jacobi, Truncation & `osp(1|2)` -/

section BigradedSuperJacobi

/-- Koszul supercommutator sign `(-1)^(p q)` for boolean parities `p, q : Bool`. -/
def superSign (p q : Bool) : ℝ :=
  if p && q then -1 else 1

/-- Supercommutator `[x, y} := x * y - (-1)^(px py) (y * x)` in any associative `ℝ`-algebra. -/
def superBracket {A : Type*} [Ring A] [Module ℝ A] (px py : Bool) (x y : A) : A :=
  x * y - superSign px py • (y * x)

/-- **Graded Super-Jacobi Identity (`B2`)** in any associative `ℝ`-algebra. -/
theorem superJacobi_assoc {A : Type*} [Ring A] [Module ℝ A]
    [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (px py pz : Bool) (x y z : A) :
    superSign px pz • superBracket px (xor py pz) x (superBracket py pz y z) +
      superSign py px • superBracket py (xor pz px) y (superBracket pz px z x) +
      superSign pz py • superBracket pz (xor px py) z (superBracket px py x y) = 0 := by
  cases px <;> cases py <;> cases pz <;>
    (simp [superBracket, superSign]; noncomm_ring)

/-- Bigraded 5-graded associative superalgebra structure indexed by `(k, ε) ∈ ℤ × Bool`. -/
structure FiveGradedBigraded (A : Type*) [Ring A] [Module ℝ A] where
  grade : ℤ → Bool → Submodule ℝ A
  mul_mem : ∀ {a b : ℤ} {pa pb : Bool} {x y : A},
    x ∈ grade a pa → y ∈ grade b pb → x * y ∈ grade (a + b) (xor pa pb)
  grade_eq_bot_of_outside : ∀ {k : ℤ} (p : Bool), (k < -2 ∨ 2 < k) → grade k p = ⊥

/-- Bigraded superbracket preserves `k`-grade additivity and `ℤ₂`-parity (`xor`). -/
theorem superBracket_mem_add {A : Type*} [Ring A] [Module ℝ A]
    (G : FiveGradedBigraded A) {a b : ℤ} {pa pb : Bool} {x y : A}
    (hx : x ∈ G.grade a pa) (hy : y ∈ G.grade b pb) :
    superBracket pa pb x y ∈ G.grade (a + b) (xor pa pb) := by
  unfold superBracket
  apply Submodule.sub_mem
  · exact G.mul_mem hx hy
  · apply Submodule.smul_mem
    have hyx : y * x ∈ G.grade (b + a) (xor pb pa) := G.mul_mem hy hx
    rwa [add_comm b a, Bool.xor_comm pb pa] at hyx

/-- **5-Graded Truncation (`B2`)**: `[g_a, g_b} = 0` whenever `|a + b| > 2`. -/
theorem superBracket_eq_zero_of_abs_gt_two {A : Type*} [Ring A] [Module ℝ A]
    (G : FiveGradedBigraded A) {a b : ℤ} {pa pb : Bool} {x y : A}
    (hx : x ∈ G.grade a pa) (hy : y ∈ G.grade b pb)
    (hab : a + b < -2 ∨ 2 < a + b) :
    superBracket pa pb x y = 0 := by
  have hmem := superBracket_mem_add G hx hy
  rw [G.grade_eq_bot_of_outside (xor pa pb) hab, Submodule.mem_bot] at hmem
  exact hmem

/-! ### Concrete `osp(1|2) ⊂ M_3(ℝ)` 5-Graded Superalgebra Witness -/

/-- Even grade-0 Cartan element `E ∈ osp(1|2)`. -/
def ospE : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 0; 0, 0, -1]

/-- Odd grade `+1` supercharge `q¹ ∈ osp(1|2)`. -/
def ospQ1 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 2, 0; 0, 0, 2; 0, 0, 0]

/-- Odd grade `-1` supercharge `p₁ ∈ osp(1|2)`. -/
def ospP1 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 1, 0, 0; 0, -1, 0]

/-- Even grade `+2` root vector `q² = [q¹, q¹} ∈ osp(1|2)`. -/
def ospQ2 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 8; 0, 0, 0; 0, 0, 0]

/-- Even grade `-2` root vector `p₂ = [p₁, p₁} ∈ osp(1|2)`. -/
def ospP2 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 0; -2, 0, 0]

theorem ospQ1_ne_zero : ospQ1 ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h
  norm_num [ospQ1] at h01

theorem ospQ2_ne_zero : ospQ2 ≠ 0 := by
  intro h
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 2) h
  norm_num [ospQ2] at h02

theorem osp_superBracket_E_q1 : superBracket false true ospE ospQ1 = ospQ1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [superBracket, superSign, ospE, ospQ1]

theorem osp_superBracket_E_p1 : superBracket false true ospE ospP1 = -ospP1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [superBracket, superSign, ospE, ospP1]

theorem osp_superBracket_q1_p1 : superBracket true true ospQ1 ospP1 = (2 : ℝ) • ospE := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [superBracket, superSign, ospE, ospQ1, ospP1]

theorem osp_superBracket_q1_q1 : superBracket true true ospQ1 ospQ1 = ospQ2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [superBracket, superSign, ospQ1, ospQ2]; try norm_num)

theorem osp_superBracket_p1_p1 : superBracket true true ospP1 ospP1 = ospP2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [superBracket, superSign, ospP1, ospP2]; try norm_num)

theorem osp_superBracket_q1_q2_trunc : superBracket true false ospQ1 ospQ2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [superBracket, superSign, ospQ1, ospQ2]

theorem osp_superBracket_q2_q2_trunc : superBracket false false ospQ2 ospQ2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [superBracket, superSign, ospQ2]

/-- Concrete `(ospE, ospQ1, ospP1)` Super-Jacobi closure in `osp(1|2)`. -/
theorem osp_superJacobi_E_q1_p1 :
    superSign false true • superBracket false (xor true true) ospE (superBracket true true ospQ1 ospP1) +
      superSign true false • superBracket true (xor true false) ospQ1 (superBracket true false ospP1 ospE) +
      superSign true true • superBracket true (xor false true) ospP1 (superBracket false true ospE ospQ1) = 0 :=
  superJacobi_assoc false true true ospE ospQ1 ospP1

end BigradedSuperJacobi

/-! ## Section 5: B3 — Maurer–Cartan 5-Grade Decomposition -/

section MaurerCartanGradeDecomposition

/-- Re-export of the 5-graded Maurer–Cartan curvature tower flatness equivalence from
`MajoranaParaKahlerMaurerCartanSupercolorSynthesis`. -/
theorem mcCurvatureTower_flat_iff_source_laws_bridge {R : Type*} [Ring R]
    (J : InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis.FiveGradedMaurerCartanJet R) :
    InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis.mcCurvatureTower J =
        (0, 0, 0, 0, 0) ↔
      (J.dOmega_m2 + J.br_0_m2 = -J.br_m1_m1_half ∧
       J.dOmega_m1 + J.br_0_m1 = -J.br_p1_m2 ∧
       J.dOmega_0 + J.br_0_0_half = -(J.br_m1_p1 + J.br_m2_p2) ∧
       J.dOmega_p1 + J.br_0_p1 = -J.br_m1_p2 ∧
       J.dOmega_p2 + J.br_0_p2 = -J.br_p1_p1_half) :=
  InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis.mcCurvatureTower_flat_iff_source_laws J

/-- Direct-sum uniqueness on grades `{-2, -1, 0, 1, 2}` in any `GradedLieAlgebra`. -/
theorem graded_five_sum_eq_zero_iff {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (grade : ℤ → Submodule ℝ L) [GradedLieAlgebra grade]
    {x_m2 x_m1 x_0 x_p1 x_p2 : L}
    (hm2 : x_m2 ∈ grade (-2)) (hm1 : x_m1 ∈ grade (-1)) (h0 : x_0 ∈ grade 0)
    (hp1 : x_p1 ∈ grade 1) (hp2 : x_p2 ∈ grade 2) :
    x_m2 + x_m1 + x_0 + x_p1 + x_p2 = 0 ↔
      x_m2 = 0 ∧ x_m1 = 0 ∧ x_0 = 0 ∧ x_p1 = 0 ∧ x_p2 = 0 := by
  constructor
  · intro hsum
    have hdec : DirectSum.decompose grade (x_m2 + x_m1 + x_0 + x_p1 + x_p2) = 0 := by
      rw [hsum, DirectSum.decompose_zero]
    have hcomp : ∀ k : ℤ,
        ((DirectSum.decompose grade (x_m2 + x_m1 + x_0 + x_p1 + x_p2) k : ↥(grade k)) : L) = 0 := by
      intro k
      rw [hdec]
      rfl
    have eval_at : ∀ k : ℤ,
        ((DirectSum.decompose grade (x_m2 + x_m1 + x_0 + x_p1 + x_p2) k : ↥(grade k)) : L) =
          (if k = -2 then x_m2 else 0) + (if k = -1 then x_m1 else 0) +
          (if k = 0 then x_0 else 0) + (if k = 1 then x_p1 else 0) +
          (if k = 2 then x_p2 else 0) := by
      intro k
      have f1 : ∀ {x : L} {i : ℤ}, x ∈ grade i →
          ((DirectSum.decompose grade x k : ↥(grade k)) : L) = if k = i then x else 0 := by
        intro x i hx
        by_cases hki : k = i
        · subst hki; simp [DirectSum.decompose_of_mem_same grade hx]
        · simp [hki, DirectSum.decompose_of_mem_ne grade hx (Ne.symm hki)]
      rw [DirectSum.decompose_add, DirectSum.decompose_add, DirectSum.decompose_add,
        DirectSum.decompose_add]
      simp only [DirectSum.add_apply, Submodule.coe_add]
      rw [f1 hm2, f1 hm1, f1 h0, f1 hp1, f1 hp2]
    have e_m2 := (eval_at (-2)).symm.trans (hcomp (-2))
    have e_m1 := (eval_at (-1)).symm.trans (hcomp (-1))
    have e_0 := (eval_at 0).symm.trans (hcomp 0)
    have e_p1 := (eval_at 1).symm.trans (hcomp 1)
    have e_p2 := (eval_at 2).symm.trans (hcomp 2)
    norm_num at e_m2 e_m1 e_0 e_p1 e_p2
    exact ⟨e_m2, e_m1, e_0, e_p1, e_p2⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    simp

/-- **Internal 5-Graded Cartan Maurer–Cartan Splitting (`B3`)**:
For `ω = θ + ω₀ + Υ` (`θ ∈ grade 1, ω₀ ∈ grade 0, Υ ∈ grade (-1)`) and dual factor
`ω' = θ' + ω₀' + Υ'` (modeling 1-form wedge-bracket signs) with `dω = dΥ + dω₀ + dθ`,
the Maurer–Cartan equation `dω + (1/2) ⁅ω, ω'⁆ = 0` decomposes into exact grade equations:
* Grade `+2`: `(1/2) ⁅θ, θ'⁆ = 0`
* Grade `+1`: `dθ + (1/2) (⁅ω₀, θ'⁆ + ⁅θ, ω₀'⁆) = 0`
* Grade `0`: `dω₀ + (1/2) (⁅ω₀, ω₀'⁆ + ⁅θ, Υ'⁆ + ⁅Υ, θ'⁆) = 0`
* Grade `-1`: `dΥ + (1/2) (⁅ω₀, Υ'⁆ + ⁅Υ, ω₀'⁆) = 0`
* Grade `-2`: `(1/2) ⁅Υ, Υ'⁆ = 0`

Note (`T65:5077` vs `A2`): `T65:5077` places `θ ∈ g1, Υ ∈ g(-1)`, swapped relative to Theme A
(`θ ∈ g(-1), Υ ∈ g1`). Both give the same grade-0 pairing `[g1, g(-1)] ⊆ g0`. -/
theorem maurerCartan_cartanSplit_gradedLie {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (grade : ℤ → Submodule ℝ L) [GradedLieAlgebra grade]
    {θ ω₀ Υ θ' ω₀' Υ' dθ dω₀ dΥ : L}
    (hθ : θ ∈ grade 1) (hω₀ : ω₀ ∈ grade 0) (hΥ : Υ ∈ grade (-1))
    (hθ' : θ' ∈ grade 1) (hω₀' : ω₀' ∈ grade 0) (hΥ' : Υ' ∈ grade (-1))
    (hdθ : dθ ∈ grade 1) (hdω₀ : dω₀ ∈ grade 0) (hdΥ : dΥ ∈ grade (-1)) :
    (dΥ + dω₀ + dθ) + (1 / 2 : ℝ) • ⁅θ + ω₀ + Υ, θ' + ω₀' + Υ'⁆ = 0 ↔
      (1 / 2 : ℝ) • ⁅Υ, Υ'⁆ = 0 ∧
      dΥ + (1 / 2 : ℝ) • (⁅ω₀, Υ'⁆ + ⁅Υ, ω₀'⁆) = 0 ∧
      dω₀ + (1 / 2 : ℝ) • (⁅ω₀, ω₀'⁆ + ⁅θ, Υ'⁆ + ⁅Υ, θ'⁆) = 0 ∧
      dθ + (1 / 2 : ℝ) • (⁅ω₀, θ'⁆ + ⁅θ, ω₀'⁆) = 0 ∧
      (1 / 2 : ℝ) • ⁅θ, θ'⁆ = 0 := by
  have hbr :
      (dΥ + dω₀ + dθ) + (1 / 2 : ℝ) • ⁅θ + ω₀ + Υ, θ' + ω₀' + Υ'⁆ =
        ((1 / 2 : ℝ) • ⁅Υ, Υ'⁆) +
        (dΥ + (1 / 2 : ℝ) • (⁅ω₀, Υ'⁆ + ⁅Υ, ω₀'⁆)) +
        (dω₀ + (1 / 2 : ℝ) • (⁅ω₀, ω₀'⁆ + ⁅θ, Υ'⁆ + ⁅Υ, θ'⁆)) +
        (dθ + (1 / 2 : ℝ) • (⁅ω₀, θ'⁆ + ⁅θ, ω₀'⁆)) +
        ((1 / 2 : ℝ) • ⁅θ, θ'⁆) := by
    simp only [add_lie, lie_add, smul_add]
    abel
  rw [hbr]
  refine graded_five_sum_eq_zero_iff grade ?_ ?_ ?_ ?_ ?_
  · exact Submodule.smul_mem _ _ (SetLike.GradedBracket.bracket_mem hΥ hΥ')
  · exact Submodule.add_mem _ hdΥ (Submodule.smul_mem _ _
      (Submodule.add_mem _ (SetLike.GradedBracket.bracket_mem hω₀ hΥ')
        (by simpa using SetLike.GradedBracket.bracket_mem hΥ hω₀')))
  · exact Submodule.add_mem _ hdω₀ (Submodule.smul_mem _ _
      (Submodule.add_mem _ (Submodule.add_mem _
        (SetLike.GradedBracket.bracket_mem hω₀ hω₀')
        (SetLike.GradedBracket.bracket_mem hθ hΥ'))
        (by simpa using SetLike.GradedBracket.bracket_mem hΥ hθ')))
  · exact Submodule.add_mem _ hdθ (Submodule.smul_mem _ _
      (Submodule.add_mem _ (SetLike.GradedBracket.bracket_mem hω₀ hθ')
        (by simpa using SetLike.GradedBracket.bracket_mem hθ hω₀')))
  · exact Submodule.smul_mem _ _ (SetLike.GradedBracket.bracket_mem hθ hθ')

/-- Superbracket Cartan Maurer–Cartan decomposition (`ω = θ + ω₀ + Υ` with 1-form parity `true`,
so `[ω, ω} = 2 ω²`) matching `T65:5077-5078` (`dθ + [ω₀, θ} = 0` and
`dω₀ + (1/2)[ω₀, ω₀} + [θ, Υ} = 0`) when the grade-`±2` torsion brackets vanish. -/
theorem maurerCartan_cartanSplit_superBracket {A : Type*} [Ring A] [Module ℝ A]
    (θ ω₀ Υ dθ dω₀ dΥ : A)
    (hω : superBracket true true (θ + ω₀ + Υ) (θ + ω₀ + Υ) =
      superBracket true true θ θ + (2 : ℝ) • superBracket true true ω₀ θ +
      (superBracket true true ω₀ ω₀ + (2 : ℝ) • superBracket true true θ Υ) +
      (2 : ℝ) • superBracket true true ω₀ Υ + superBracket true true Υ Υ) :
    (dΥ + dω₀ + dθ) + (1 / 2 : ℝ) • superBracket true true (θ + ω₀ + Υ) (θ + ω₀ + Υ) =
      ((1 / 2 : ℝ) • superBracket true true Υ Υ) +
      (dΥ + superBracket true true ω₀ Υ) +
      (dω₀ + (1 / 2 : ℝ) • superBracket true true ω₀ ω₀ + superBracket true true θ Υ) +
      (dθ + superBracket true true ω₀ θ) +
      ((1 / 2 : ℝ) • superBracket true true θ θ) := by
  rw [hω]
  simp only [smul_add, smul_smul]
  norm_num
  abel

/-- Unconditional superbracket expansion for odd-form Cartan connection `ω = θ + ω₀ + Υ`:
`dω + (1/2)[ω, ω} = (1/2)[Υ, Υ} + (dΥ + [ω₀, Υ}) + (dω₀ + (1/2)[ω₀, ω₀} + [θ, Υ}) + (dθ + [ω₀, θ}) + (1/2)[θ, θ}`. -/
theorem maurerCartan_cartanSplit_superBracket_expand {A : Type*} [Ring A] [Module ℝ A]
    [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (θ ω₀ Υ dθ dω₀ dΥ : A) :
    (dΥ + dω₀ + dθ) + (1 / 2 : ℝ) • superBracket true true (θ + ω₀ + Υ) (θ + ω₀ + Υ) =
      ((1 / 2 : ℝ) • superBracket true true Υ Υ) +
      (dΥ + superBracket true true ω₀ Υ) +
      (dω₀ + (1 / 2 : ℝ) • superBracket true true ω₀ ω₀ + superBracket true true θ Υ) +
      (dθ + superBracket true true ω₀ θ) +
      ((1 / 2 : ℝ) • superBracket true true θ θ) := by
  simp only [superBracket, superSign, Bool.and_self, ↓reduceIte, neg_smul, one_smul, sub_neg_eq_add]
  have hmul : (θ + ω₀ + Υ) * (θ + ω₀ + Υ) =
      θ * θ + ω₀ * θ + Υ * θ + (θ * ω₀ + ω₀ * ω₀ + Υ * ω₀) + (θ * Υ + ω₀ * Υ + Υ * Υ) := by
    noncomm_ring
  have hhalf : ∀ z : A, (1 / 2 : ℝ) • (z + z) = z := fun z => by
    rw [← two_smul ℝ z, smul_smul]
    norm_num
  rw [hmul, hhalf, hhalf (Υ * Υ), hhalf (ω₀ * ω₀), hhalf (θ * θ)]
  abel

end MaurerCartanGradeDecomposition

/-! ## Section 6: E9_alg — Algebraic Levi Bracket `[n₊, n₋]` and 3-Graded vs 5-Graded Boundary -/

section AlgebraicLeviBracket

section GeneralLevi

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
variable (g : ℤ → Submodule ℝ L) [GradedLieAlgebra g]

/-- Matched-grade Levi brackets always land in grade `0`: `[g₁, g₋₁] ⊆ g₀` and `[g₂, g₋₂] ⊆ g₀`. -/
theorem matched_neg_pos_bracket_mem_zero :
    (∀ x ∈ g 1, ∀ y ∈ g (-1), ⁅x, y⁆ ∈ g 0) ∧
      (∀ x ∈ g 2, ∀ y ∈ g (-2), ⁅x, y⁆ ∈ g 0) := by
  constructor
  · intro x hx y hy
    simpa using SetLike.GradedBracket.bracket_mem hx hy
  · intro x hx y hy
    simpa using SetLike.GradedBracket.bracket_mem hx hy

/-- General 5-graded Levi containment: `[n₊, n₋] ⊆ g₋₁ ⊔ g₀ ⊔ g₁`. -/
theorem nPlus_nMinus_bracket_mem_middle {x y : L}
    (hx : x ∈ nPlus g) (hy : y ∈ nMinus g) :
    ⁅x, y⁆ ∈ g (-1) ⊔ g 0 ⊔ g 1 := by
  obtain ⟨x1, hx1, x2, hx2, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.mp hy
  rw [add_lie, lie_add, lie_add]
  have h11 : ⁅x1, y1⁆ ∈ g (-1) ⊔ g 0 ⊔ g 1 :=
    Submodule.mem_sup_left (Submodule.mem_sup_right
      (by simpa using SetLike.GradedBracket.bracket_mem hx1 hy1))
  have h12 : ⁅x1, y2⁆ ∈ g (-1) ⊔ g 0 ⊔ g 1 :=
    Submodule.mem_sup_left (Submodule.mem_sup_left
      (by simpa using SetLike.GradedBracket.bracket_mem hx1 hy2))
  have h21 : ⁅x2, y1⁆ ∈ g (-1) ⊔ g 0 ⊔ g 1 :=
    Submodule.mem_sup_right (by simpa using SetLike.GradedBracket.bracket_mem hx2 hy1)
  have h22 : ⁅x2, y2⁆ ∈ g (-1) ⊔ g 0 ⊔ g 1 :=
    Submodule.mem_sup_left (Submodule.mem_sup_right
      (by simpa using SetLike.GradedBracket.bracket_mem hx2 hy2))
  exact Submodule.add_mem _ (Submodule.add_mem _ h11 h12) (Submodule.add_mem _ h21 h22)

/-- Exact 3-graded specialization: if `g (-2) = ⊥` and `g 2 = ⊥`, then `[n₊, n₋] ⊆ g₀`. -/
theorem nPlus_nMinus_bracket_mem_zero_of_three_graded
    (hm2 : g (-2) = ⊥) (hp2 : g 2 = ⊥) {x y : L}
    (hx : x ∈ nPlus g) (hy : y ∈ nMinus g) :
    ⁅x, y⁆ ∈ g 0 := by
  have hx' : x ∈ g 1 := by
    have hx1 : x ∈ g 1 ⊔ ⊥ := by simpa [nPlus, hp2] using hx
    simpa using hx1
  have hy' : y ∈ g (-1) := by
    have hy1 : y ∈ g (-1) ⊔ ⊥ := by simpa [nMinus, hm2] using hy
    simpa using hy1
  simpa using SetLike.GradedBracket.bracket_mem hx' hy'

end GeneralLevi

/-- Positive Levi witness in `Sp4Contact.Sp`: `[zPlus, zMinus] = gradingElement ∈ grade 0`. -/
theorem sp4_zPlus_zMinus_mem_zero :
    ⁅InfoGeometry.Algebra.Sp4Contact.zPlus, InfoGeometry.Algebra.Sp4Contact.zMinus⁆ ∈
      InfoGeometry.Algebra.Sp4Contact.grade 0 := by
  rw [InfoGeometry.Algebra.Sp4Contact.lie_zPlus_zMinus]
  exact InfoGeometry.Algebra.Sp4Contact.generator_mem_grade 3

/-- Positive Levi witness in `FreudenthalTKK5E8`: `[ePlus2, eMinus2] = gradeCenterZ ∈ gGrade 0`. -/
theorem e8_ePlus2_eMinus2_mem_zero :
    ⁅ePlus2, eMinus2⁆ ∈ gGrade 0 := by
  rw [freudenthalTKK5E8_sl2Triple.lie_e_f]
  rw [mem_gGrade_zero_iff]
  simp [gradeCenterZ, injZeroCenter]

/-- Counter-witness in `Sp4Contact.Sp` refuting unqualified `T38` `[n₊, n₋] ⊆ g₀`:
`u1 ∈ grade 1 ⊆ nPlus`, `zMinus ∈ grade (-2) ⊆ nMinus`, and `[u1, zMinus] ∈ grade (-1) \ grade 0`. -/
theorem sp4_u1_zMinus_not_mem_zero :
    InfoGeometry.Algebra.Sp4Contact.u1 ∈ nPlus InfoGeometry.Algebra.Sp4Contact.grade ∧
      InfoGeometry.Algebra.Sp4Contact.zMinus ∈ nMinus InfoGeometry.Algebra.Sp4Contact.grade ∧
      ⁅InfoGeometry.Algebra.Sp4Contact.u1, InfoGeometry.Algebra.Sp4Contact.zMinus⁆ ∈
        InfoGeometry.Algebra.Sp4Contact.grade (-1) ∧
      ⁅InfoGeometry.Algebra.Sp4Contact.u1, InfoGeometry.Algebra.Sp4Contact.zMinus⁆ ∉
        InfoGeometry.Algebra.Sp4Contact.grade 0 := by
  have hu1 : InfoGeometry.Algebra.Sp4Contact.u1 ∈ InfoGeometry.Algebra.Sp4Contact.grade 1 :=
    InfoGeometry.Algebra.Sp4Contact.generator_mem_grade 7
  have hzm : InfoGeometry.Algebra.Sp4Contact.zMinus ∈ InfoGeometry.Algebra.Sp4Contact.grade (-2) :=
    InfoGeometry.Algebra.Sp4Contact.generator_mem_grade 0
  have hbr : ⁅InfoGeometry.Algebra.Sp4Contact.u1, InfoGeometry.Algebra.Sp4Contact.zMinus⁆ ∈
      InfoGeometry.Algebra.Sp4Contact.grade (-1) := by
    simpa using InfoGeometry.Algebra.Sp4Contact.lie_mem_grade 1 (-2) hu1 hzm
  have hnot0 : ⁅InfoGeometry.Algebra.Sp4Contact.u1, InfoGeometry.Algebra.Sp4Contact.zMinus⁆ ∉
      InfoGeometry.Algebra.Sp4Contact.grade 0 := by
    intro hmem0
    have hdisj : Disjoint (InfoGeometry.Algebra.Sp4Contact.grade (-1))
        (InfoGeometry.Algebra.Sp4Contact.grade 0) :=
      InfoGeometry.Algebra.Sp4Contact.grades_independent.pairwiseDisjoint
        (by decide : (-1 : ℤ) ≠ 0)
    have hz : ⁅InfoGeometry.Algebra.Sp4Contact.u1, InfoGeometry.Algebra.Sp4Contact.zMinus⁆ = 0 :=
      (Submodule.disjoint_def.mp hdisj) _ hbr hmem0
    have hcoord := congrArg (fun X : InfoGeometry.Algebra.Sp4Contact.Sp =>
      (X : InfoGeometry.Algebra.Sp4Contact.Mat) 2 0) hz
    norm_num [InfoGeometry.Algebra.Sp4Contact.u1, InfoGeometry.Algebra.Sp4Contact.zMinus,
      InfoGeometry.Algebra.Sp4Contact.generator, InfoGeometry.Algebra.Sp4Contact.matrixOfCoordinates,
      LieRing.of_associative_ring_bracket, Matrix.mul_apply, Fin.sum_univ_four,
      Pi.single_apply] at hcoord
  exact ⟨Submodule.mem_sup_left hu1, Submodule.mem_sup_right hzm, hbr, hnot0⟩

/-- Counter-witness in `FreudenthalTKK5E8` refuting unqualified `T38` `[n₊, n₋] ⊆ g₀`. -/
theorem e8_p1_m2_not_mem_zero :
    let q : InfoGeometry.Algebra.H3ZornFreudenthal.Charge := ⟨1, 0, 0, 0⟩
    injPlus1 q ∈ nPlus gGrade ∧
      eMinus2 ∈ nMinus gGrade ∧
      ⁅injPlus1 q, eMinus2⁆ ∈ gGrade (-1) ∧
      ⁅injPlus1 q, eMinus2⁆ ∉ gGrade 0 := by
  intro q
  have hq : injPlus1 q ∈ gGrade 1 := ⟨q, rfl⟩
  have hm2 : eMinus2 ∈ gGrade (-2) := ⟨1, rfl⟩
  have hbr : ⁅injPlus1 q, eMinus2⁆ ∈ gGrade (-1) := by
    simpa using gGrade_bracket_mem hq hm2
  have hnot0 : ⁅injPlus1 q, eMinus2⁆ ∉ gGrade 0 := by
    intro h0
    have hm1 : (⁅injPlus1 q, eMinus2⁆).gMinus1 = 0 := ((mem_gGrade_zero_iff _).mp h0).2.1
    have hval : (⁅injPlus1 q, eMinus2⁆).gMinus1 = -q := by
      change (bracket5LM (injPlus1 q) (injMinus2 1)).gMinus1 = -q
      simp [injPlus1, injMinus2]
    have hq0 : q = 0 := neg_eq_zero.mp (hval.symm.trans hm1)
    have ha := congrArg InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge.alpha hq0
    norm_num [q] at ha
  exact ⟨Submodule.mem_sup_left hq, Submodule.mem_sup_right hm2, hbr, hnot0⟩

end AlgebraicLeviBracket

/-! ## Section 7: F1 — `Cl(1,1)` Krein Fundamental Symmetry `J_K = γ⁰γ¹` -/

section KreinFundamentalSymmetry

/-- 2D `Cl(1,1)` Krein generator `γ⁰ = [[0, 1], [-1, 0]]` (`T65:5118`), reusing `Cl11Matrix.Eminus`. -/
abbrev kreinGamma0 : InfoGeometry.Clifford.Cl11Matrix.Mat2 :=
  InfoGeometry.Clifford.Cl11Matrix.Eminus

/-- 2D `Cl(1,1)` Krein generator `γ¹ = [[0, 1], [1, 0]]` (`T65:5119`), reusing `Cl11Matrix.J1`. -/
abbrev kreinGamma1 : InfoGeometry.Clifford.Cl11Matrix.Mat2 :=
  InfoGeometry.Clifford.Cl11Matrix.J1

/-- 2D Krein fundamental symmetry `J_K = diag(1, -1)` (`T65:5115,5121`), reusing `Cl11Matrix.Eplus`. -/
abbrev kreinSymmetryJ : InfoGeometry.Clifford.Cl11Matrix.Mat2 :=
  InfoGeometry.Clifford.Cl11Matrix.Eplus

theorem kreinGamma0_sq : kreinGamma0 * kreinGamma0 = -1 := by
  simpa [kreinGamma0] using InfoGeometry.Clifford.Cl11Matrix.Eminus_sq

theorem kreinGamma1_sq : kreinGamma1 * kreinGamma1 = 1 :=
  InfoGeometry.Clifford.Cl11Matrix.J1_sq

theorem kreinGamma0_gamma1_anticomm :
    kreinGamma0 * kreinGamma1 + kreinGamma1 * kreinGamma0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kreinGamma0, kreinGamma1, InfoGeometry.Clifford.Cl11Matrix.Eminus,
      InfoGeometry.Clifford.Cl11Matrix.J1]

/-- `T65:5121` identity: `γ⁰ γ¹ = J_K` in 2D `Cl(1,1)`. -/
theorem kreinGamma0_mul_gamma1_eq_J : kreinGamma0 * kreinGamma1 = kreinSymmetryJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kreinGamma0, kreinGamma1, kreinSymmetryJ,
      InfoGeometry.Clifford.Cl11Matrix.Eminus, InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eplus, Matrix.mul_apply, Fin.sum_univ_two]

theorem kreinSymmetryJ_sq : kreinSymmetryJ * kreinSymmetryJ = 1 :=
  InfoGeometry.Clifford.Cl11Matrix.Eplus_sq

theorem kreinSymmetryJ_transpose : kreinSymmetryJᵀ = kreinSymmetryJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kreinSymmetryJ, InfoGeometry.Clifford.Cl11Matrix.Eplus]

/-- Noncommutativity witness (`T16`): `γ⁰ γ¹ ≠ γ¹ γ⁰`. -/
theorem kreinGamma0_ne_comm_gamma1 : kreinGamma0 * kreinGamma1 ≠ kreinGamma1 * kreinGamma0 :=
  InfoGeometry.Clifford.Cl11Matrix.J1_mul_Eminus_ne.symm

section BlockKrein

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- General block-matrix `Cl(1,1)` generator `γ⁰` on `H₊ ⊕ H₋`. -/
def blockKreinGamma0 : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks 0 1 (-1) 0

/-- General block-matrix `Cl(1,1)` generator `γ¹` on `H₊ ⊕ H₋`. -/
def blockKreinGamma1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks 0 1 1 0

theorem blockKreinGamma0_sq :
    (blockKreinGamma0 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * blockKreinGamma0 = -1 := by
  unfold blockKreinGamma0
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, add_zero, zero_add]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]

theorem blockKreinGamma1_sq :
    (blockKreinGamma1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * blockKreinGamma1 = 1 := by
  unfold blockKreinGamma1
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]
  rw [Matrix.fromBlocks_one]

theorem blockKreinGamma0_gamma1_anticomm :
    (blockKreinGamma0 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * blockKreinGamma1 +
      blockKreinGamma1 * blockKreinGamma0 = 0 := by
  unfold blockKreinGamma0 blockKreinGamma1
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_add]

/-- General `H₊ ⊕ H₋` chirality identity `γ⁰ γ¹ = InfoGeometry.NCG.Gamma = diag(I, -I)`. -/
theorem blockKreinGamma0_mul_gamma1_eq_Gamma :
    (blockKreinGamma0 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * blockKreinGamma1 =
      InfoGeometry.NCG.Gamma := by
  unfold blockKreinGamma0 blockKreinGamma1 InfoGeometry.NCG.Gamma
  rw [Matrix.fromBlocks_multiply]
  simp

theorem kreinGamma_sq :
    (InfoGeometry.NCG.Gamma : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * InfoGeometry.NCG.Gamma = 1 := by
  unfold InfoGeometry.NCG.Gamma
  rw [Matrix.fromBlocks_multiply]
  simp [← Matrix.fromBlocks_one]

end BlockKrein

end KreinFundamentalSymmetry

/-! ## Section 8: F2 & B6 — Krein Supertrace Cancellation & Green–Schwarz Closure -/

section KreinSupertraceAndGreenSchwarz

section GenericRing

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- **Off-diagonal Krein supertrace cancellation (`F2a`)**:
`sTr_K [[0, B], [C, 0]] = 0` for arbitrary block matrices over any ring `R`. -/
theorem kreinSupertrace_offDiag_eq_zero (B C : Matrix ι ι R) :
    InfoGeometry.NCG.superTrace (Matrix.fromBlocks (0 : Matrix ι ι R) B C 0) = 0 := by
  unfold InfoGeometry.NCG.superTrace
  have hmul :
      Matrix.fromBlocks (1 : Matrix ι ι R) 0 0 (-1) *
          Matrix.fromBlocks (0 : Matrix ι ι R) B C 0 =
        Matrix.fromBlocks 0 B (-C) 0 := by
    rw [Matrix.fromBlocks_multiply]
    simp
  rw [hmul, Matrix.trace]
  rw [Fintype.sum_sum_type]
  simp

/-- **Balanced block-diagonal Krein supertrace cancellation (`F2c`)**:
If `Tr(A₊) = Tr(A₋)`, then `sTr_K(diag(A₊, A₋)) = 0`. -/
theorem kreinSupertrace_balanced_blockDiag_eq_zero (A_pos A_neg : Matrix ι ι R)
    (htr : Matrix.trace A_pos = Matrix.trace A_neg) :
    InfoGeometry.NCG.superTrace (Matrix.fromBlocks A_pos (0 : Matrix ι ι R) 0 A_neg) = 0 := by
  rw [InfoGeometry.NCG.superTrace_blockDiag_eq, htr, sub_self]

/-- **Krein curvature-square supertrace (`B6`)**:
`sTr_K(diag(R₊, R₋)²) = Tr(R₊²) - Tr(R₋²)`. -/
theorem kreinSupertrace_blockDiag_sq (R_pos R_neg : Matrix ι ι R) :
    InfoGeometry.NCG.superTrace ((Matrix.fromBlocks R_pos (0 : Matrix ι ι R) 0 R_neg) ^ 2) =
      Matrix.trace (R_pos ^ 2) - Matrix.trace (R_neg ^ 2) := by
  rw [pow_two, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  simpa [pow_two] using InfoGeometry.NCG.superTrace_blockDiag_eq (R_pos * R_pos) (R_neg * R_neg)

/-- **Algebraic Green–Schwarz Krein Supertrace Closure (`B6`)**:
Whenever `Tr(R₊²) = Tr(R₋²)`, the noncommutative block curvature satisfies `sTr_K(R²) = 0`. -/
theorem green_schwarz_kreinSupertrace_closure (R_pos R_neg : Matrix ι ι R)
    (htr : Matrix.trace (R_pos ^ 2) = Matrix.trace (R_neg ^ 2)) :
    InfoGeometry.NCG.superTrace ((Matrix.fromBlocks R_pos (0 : Matrix ι ι R) 0 R_neg) ^ 2) = 0 := by
  rw [kreinSupertrace_blockDiag_sq, htr, sub_self]

theorem green_schwarz_kreinSupertrace_closure_of_eq (R_pos : Matrix ι ι R) :
    InfoGeometry.NCG.superTrace ((Matrix.fromBlocks R_pos (0 : Matrix ι ι R) 0 R_pos) ^ 2) = 0 :=
  green_schwarz_kreinSupertrace_closure R_pos R_pos rfl

theorem green_schwarz_kreinSupertrace_closure_of_neg (R_pos : Matrix ι ι R) :
    InfoGeometry.NCG.superTrace ((Matrix.fromBlocks R_pos (0 : Matrix ι ι R) 0 (-R_pos)) ^ 2) =
      0 := by
  apply green_schwarz_kreinSupertrace_closure
  simp [pow_two]

end GenericRing

section CommRingSupertrace

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- **Odd-operator Krein supertrace cancellation (`F2b`)**:
If `Gamma * A * Gamma = -A` and `2` is invertible in `R`, then `sTr_K(A) = 0`. -/
theorem kreinSupertrace_eq_zero_of_odd [Invertible (2 : R)]
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) R)
    (hodd : InfoGeometry.NCG.Gamma * A * InfoGeometry.NCG.Gamma = -A) :
    InfoGeometry.NCG.superTrace A = 0 := by
  have hanti : InfoGeometry.NCG.Gamma * A = -(A * InfoGeometry.NCG.Gamma) := by
    calc
      InfoGeometry.NCG.Gamma * A
        = InfoGeometry.NCG.Gamma * A * (InfoGeometry.NCG.Gamma * InfoGeometry.NCG.Gamma) := by
            rw [kreinGamma_sq, Matrix.mul_one]
      _ = (InfoGeometry.NCG.Gamma * A * InfoGeometry.NCG.Gamma) * InfoGeometry.NCG.Gamma := by
            simp only [Matrix.mul_assoc]
      _ = -(A * InfoGeometry.NCG.Gamma) := by
            rw [hodd, Matrix.neg_mul]
  have htr : InfoGeometry.NCG.superTrace A = -InfoGeometry.NCG.superTrace A := by
    calc
      InfoGeometry.NCG.superTrace A
        = Matrix.trace (InfoGeometry.NCG.Gamma * A) := rfl
      _ = Matrix.trace (-(A * InfoGeometry.NCG.Gamma)) := by rw [hanti]
      _ = -Matrix.trace (A * InfoGeometry.NCG.Gamma) := Matrix.trace_neg _
      _ = -Matrix.trace (InfoGeometry.NCG.Gamma * A) := by rw [Matrix.trace_mul_comm]
      _ = -InfoGeometry.NCG.superTrace A := rfl
  have h2 : (2 : R) * InfoGeometry.NCG.superTrace A = 0 := by
    calc
      (2 : R) * InfoGeometry.NCG.superTrace A
        = InfoGeometry.NCG.superTrace A + InfoGeometry.NCG.superTrace A := two_mul _
      _ = InfoGeometry.NCG.superTrace A + -InfoGeometry.NCG.superTrace A := by nth_rw 2 [htr]
      _ = 0 := add_neg_cancel _
  calc
    InfoGeometry.NCG.superTrace A
      = ⅟(2 : R) * ((2 : R) * InfoGeometry.NCG.superTrace A) := by
          rw [← mul_assoc, invOf_mul_self, one_mul]
    _ = 0 := by rw [h2, mul_zero]

/-- Conjugate curvature sheets `R₋ = U * R₊ * U⁻¹` satisfy Green–Schwarz closure. -/
theorem green_schwarz_kreinSupertrace_closure_of_conj (R_pos : Matrix ι ι R)
    (U : (Matrix ι ι R)ˣ) :
    InfoGeometry.NCG.superTrace
        ((Matrix.fromBlocks R_pos (0 : Matrix ι ι R) 0
          ((U : Matrix ι ι R) * R_pos * ((U⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R))) ^ 2) =
      0 := by
  apply green_schwarz_kreinSupertrace_closure
  let Uinv : Matrix ι ι R := ((U⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)
  have hu : Uinv * (U : Matrix ι ι R) = 1 := by
    simp [Uinv]
  have hsq : ((U : Matrix ι ι R) * R_pos * Uinv) ^ 2 =
      (U : Matrix ι ι R) * (R_pos ^ 2) * Uinv := by
    rw [pow_two, pow_two]
    calc
      (U : Matrix ι ι R) * R_pos * Uinv * ((U : Matrix ι ι R) * R_pos * Uinv)
        = (U : Matrix ι ι R) * R_pos * (Uinv * (U : Matrix ι ι R)) * R_pos * Uinv := by
            simp only [Matrix.mul_assoc]
      _ = (U : Matrix ι ι R) * R_pos * 1 * R_pos * Uinv := by rw [hu]
      _ = (U : Matrix ι ι R) * (R_pos * R_pos) * Uinv := by
            simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hsq, Matrix.trace_mul_cycle, hu, Matrix.one_mul]

/-- Compatibility with `GreenSchwarzAnomalyInflow.anomaly_polynomial_factorization`:
for trace scalars `x = Tr(R₊²)` and `y = Tr(R₋²)`, `sTr_K(R²) = x - y`, while the squared
anomaly difference factors as `x² - y² = (x - y)(x + y)`. -/
theorem green_schwarz_anomaly_factorization_link (R_pos R_neg : Matrix ι ι R) :
    let x := Matrix.trace (R_pos ^ 2)
    let y := Matrix.trace (R_neg ^ 2)
    InfoGeometry.NCG.superTrace ((Matrix.fromBlocks R_pos (0 : Matrix ι ι R) 0 R_neg) ^ 2) ^ 2 =
      (x - y) ^ 2 ∧
      x ^ 2 - y ^ 2 = (x - y) * (x + y) := by
  refine ⟨?_, InfoGeometry.Canonical.GreenSchwarzAnomalyInflow.anomaly_polynomial_factorization _ _⟩
  rw [kreinSupertrace_blockDiag_sq]

end CommRingSupertrace

section ParityBridge

/-- Connection between `InfoGeometry.NCG.superTrace` on `Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ` and
`FiniteParitySupertrace.supertrace` with `sign := Sum.elim (fun _ => 1) (fun _ => -1)`. -/
theorem kreinSupertrace_eq_finiteParitySupertrace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    InfoGeometry.NCG.superTrace A =
      InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.supertrace
        (Sum.elim (fun _ : ι => (1 : ℝ)) (fun _ : ι => (-1 : ℝ))) A := by
  have hGamma :
      (InfoGeometry.NCG.Gamma : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) =
        InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.parityOperator
          (Sum.elim (fun _ : ι => (1 : ℝ)) (fun _ : ι => (-1 : ℝ))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [InfoGeometry.NCG.Gamma,
        InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.parityOperator,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply]
    · by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  unfold InfoGeometry.NCG.superTrace InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.supertrace
  change Matrix.trace (InfoGeometry.NCG.Gamma * A) = _
  rw [hGamma]

/-- Parity-odd cancellation routed directly through `FiniteParitySupertrace.supertrace_eq_zero_of_odd`. -/
theorem kreinSupertrace_odd_parity_bridge {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (hodd : InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.IsOdd
      (Sum.elim (fun _ : ι => (1 : ℝ)) (fun _ : ι => (-1 : ℝ))) A) :
    InfoGeometry.NCG.superTrace A = 0 := by
  rw [kreinSupertrace_eq_finiteParitySupertrace]
  exact InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.supertrace_eq_zero_of_odd _ A hodd

end ParityBridge

end KreinSupertraceAndGreenSchwarz

/-! ## Section 9: F3 — Multi-Mode Grassmann / CAR Nilpotency -/

section MultiModeCAR

/-- **General CAR Square-Zero Theorem (`F3`)**:
If `{c_i, c_j} = 0` for all `i, j` in an `R`-module ring with `[Invertible (2 : R)]`,
then `c_i² = 0` for every mode `i`. (Requires `2`-invertibility: false in characteristic `2`.) -/
theorem car_sq_zero_of_anticomm {R A ι : Type*} [Ring R] [Invertible (2 : R)]
    [Ring A] [Module R A] [IsScalarTower R A A]
    (c : ι → A) (hanti : ∀ i j : ι, c i * c j + c j * c i = 0) (i : ι) :
    c i * c i = 0 := by
  have h2 : (2 : R) • (c i * c i) = 0 := by
    calc
      (2 : R) • (c i * c i) = c i * c i + c i * c i := two_smul R (c i * c i)
      _ = 0 := hanti i i
  calc
    c i * c i = (⅟(2 : R) * (2 : R)) • (c i * c i) := by rw [invOf_mul_self, one_smul]
    _ = ⅟(2 : R) • ((2 : R) • (c i * c i)) := by rw [mul_smul]
    _ = 0 := by rw [h2, smul_zero]

/-- Multi-mode Grassmann creation operator `c_i† := ι(e_i)` in `ExteriorAlgebra R (ι → R)`. -/
def grassmannCreator {R ι : Type*} [CommRing R] [DecidableEq ι] (i : ι) :
    ExteriorAlgebra R (ι → R) :=
  ExteriorAlgebra.ι R (Pi.single i (1 : R))

theorem grassmannCreator_anticomm {R ι : Type*} [CommRing R] [DecidableEq ι] (i j : ι) :
    grassmannCreator (R := R) i * grassmannCreator j +
      grassmannCreator j * grassmannCreator i = 0 :=
  ExteriorAlgebra.ι_add_mul_swap _ _

theorem grassmannCreator_sq_zero {R ι : Type*} [CommRing R] [DecidableEq ι] (i : ι) :
    grassmannCreator (R := R) i * grassmannCreator i = 0 :=
  ExteriorAlgebra.ι_sq_zero _

/-- Non-vacuity of multi-mode Grassmann creators whenever `R` is nontrivial. -/
theorem grassmannCreator_ne_zero {R ι : Type*} [CommRing R] [Nontrivial R] [DecidableEq ι]
    (i : ι) :
    grassmannCreator (R := R) i ≠ 0 := by
  rw [grassmannCreator, ne_eq, ExteriorAlgebra.ι_eq_zero_iff]
  intro h0
  have h1 := congrFun h0 i
  simp at h1

/-- Link to the single-mode `Cl(1,1)` fermionic ladder witness in `Cl11OSp12`. -/
theorem cl11_singleMode_car_witness :
    InfoGeometry.Algebra.Cl11OSp12.b * InfoGeometry.Algebra.Cl11OSp12.b = 0 ∧
      InfoGeometry.Algebra.Cl11OSp12.bdag * InfoGeometry.Algebra.Cl11OSp12.bdag = 0 ∧
      InfoGeometry.Algebra.Cl11OSp12.b * InfoGeometry.Algebra.Cl11OSp12.bdag +
        InfoGeometry.Algebra.Cl11OSp12.bdag * InfoGeometry.Algebra.Cl11OSp12.b = 1 :=
  ⟨InfoGeometry.Algebra.Cl11OSp12.b_sq, InfoGeometry.Algebra.Cl11OSp12.bdag_sq,
    InfoGeometry.Algebra.Cl11OSp12.anticomm_bbdag⟩

end MultiModeCAR

/-! ## Section 10: F4 — Arbitrary-Signature Clifford Reflections & `Pin±` Double Covers -/

section CliffordReflectionsAndPin

/-- Cartan–Dieudonné orthogonal reflection `R_u(x) = x - (Q(u)⁻¹ · polar Q u x) • u`. -/
def cliffordReflection {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (u : M) [Invertible (Q u)] (x : M) : M :=
  x - (⅟(Q u) * QuadraticMap.polar Q u x) • u

/-- **Clifford Reflection Conjugation (`F4`)** for arbitrary signature `Q`:
`-(ι Q u * ι Q x * ⅟(ι Q u)) = ι Q (cliffordReflection Q u x)`. -/
theorem clifford_reflection_eq_neg_twisted_conj {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) (u x : M)
    [Invertible (Q u)] [Invertible (CliffordAlgebra.ι Q u)] :
    -(CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q x * ⅟(CliffordAlgebra.ι Q u)) =
      CliffordAlgebra.ι Q (cliffordReflection Q u x) := by
  rw [CliffordAlgebra.ι_mul_ι_mul_invOf_ι]
  rw [← map_neg, neg_sub]
  rfl

/-- Exact field polar form (`T29:1949`): `x - 2 · (⟨u, x⟩ / Q(u)) • u`. -/
theorem cliffordReflection_field_eq {K M : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup M] [Module K M] (Q : QuadraticForm K M) (u x : M) [Invertible (Q u)] :
    cliffordReflection Q u x =
      x - (2 * (QuadraticMap.associatedHom K Q u x / Q u)) • u := by
  have hpol : QuadraticMap.polar Q u x = 2 * QuadraticMap.associatedHom K Q u x := by
    have h := LinearMap.congr_fun
      (LinearMap.congr_fun (QuadraticMap.two_nsmul_associated K Q) u) x
    simpa [QuadraticMap.polarBilin_apply_apply, two_nsmul, two_mul] using h.symm
  unfold cliffordReflection
  rw [hpol, invOf_eq_inv]
  congr 2
  ring

/-- `T29` `Pin⁺` lift (`Q(u) = +1`): `(ι Q u)² = +1` and `⅟(ι Q u) = ι Q u`. -/
theorem pinPlus_reflection_lift_sq {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) (u : M) (hu : Q u = 1) :
    CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q u = 1 ∧
      ∃ _ : Invertible (CliffordAlgebra.ι Q u),
        ⅟(CliffordAlgebra.ι Q u) = CliffordAlgebra.ι Q u := by
  have hsq : CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q u = 1 := by
    rw [CliffordAlgebra.ι_sq_scalar, hu]
    simp
  refine ⟨hsq, ⟨⟨CliffordAlgebra.ι Q u, hsq, hsq⟩, rfl⟩⟩

/-- `T29` `Pin⁻` lift (`Q(u) = -1`): `(ι Q u)² = -1` and `ι Q u ∈ pinGroup Q`.
(Note: in Mathlib `pinGroup Q`, `star (ι Q u) = -ι Q u`, so `star v * v = 1` holds for `Q u = -1`.) -/
theorem pinMinus_reflection_lift_sq_and_mem {R M : Type*} [CommRing R] [StarRing R]
    [TrivialStar R] [NoZeroDivisors R] [CharZero R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (u : M) (hu : Q u = -1) :
    CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q u = -1 ∧
      CliffordAlgebra.ι Q u ∈ _root_.pinGroup Q := by
  have hsq : CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q u = -1 := by
    rw [CliffordAlgebra.ι_sq_scalar, hu]
    simp
  refine ⟨hsq, ?_⟩
  have hQunit : IsUnit (Q u) := by
    rw [hu]
    exact isUnit_one.neg
  let uUnit := (CliffordAlgebra.isUnit_ι_of_isUnit Q hQunit).unit
  have huSpec : (uUnit : CliffordAlgebra Q) = CliffordAlgebra.ι Q u :=
    (CliffordAlgebra.isUnit_ι_of_isUnit Q hQunit).unit_spec
  rw [_root_.pinGroup.mem_iff]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨uUnit, ?_, huSpec⟩
    change uUnit ∈ _root_.lipschitzGroup Q
    unfold _root_.lipschitzGroup
    rw [Subgroup.mem_closure]
    intro S hS
    apply hS
    exact ⟨u, huSpec⟩
  · calc
      star (CliffordAlgebra.ι Q u) * CliffordAlgebra.ι Q u
        = (-CliffordAlgebra.ι Q u) * CliffordAlgebra.ι Q u := by rw [CliffordAlgebra.star_ι]
      _ = -(CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q u) := neg_mul _ _
      _ = -(-1) := by rw [hsq]
      _ = 1 := neg_neg 1
  · calc
      CliffordAlgebra.ι Q u * star (CliffordAlgebra.ι Q u)
        = CliffordAlgebra.ι Q u * (-CliffordAlgebra.ι Q u) := by rw [CliffordAlgebra.star_ι]
      _ = -(CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q u) := mul_neg _ _
      _ = -(-1) := by rw [hsq]
      _ = 1 := neg_neg 1

/-- Concrete `(1, 1)` signature witness reusing `Cl11Matrix.q11`:
both `e₊ = (1, 0)` (`Q = 1`, `Pin⁺` square `+1`) and `e₋ = (0, 1)` (`Q = -1`, `Pin⁻` square `-1`
and `∈ pinGroup q11`) realize `-u x u⁻¹ = ι (cliffordReflection q11 u x)`. -/
theorem cl11_pinPlus_pinMinus_reflection_witness (x : InfoGeometry.Clifford.Cl11Matrix.Vec11) :
    let q := InfoGeometry.Clifford.Cl11Matrix.q11
    let ePos : InfoGeometry.Clifford.Cl11Matrix.Vec11 := (1, 0)
    let eNeg : InfoGeometry.Clifford.Cl11Matrix.Vec11 := (0, 1)
    q ePos = 1 ∧
      q eNeg = -1 ∧
      CliffordAlgebra.ι q ePos * CliffordAlgebra.ι q ePos = 1 ∧
      CliffordAlgebra.ι q eNeg * CliffordAlgebra.ι q eNeg = -1 ∧
      CliffordAlgebra.ι q eNeg ∈ _root_.pinGroup q ∧
      -(CliffordAlgebra.ι q ePos * CliffordAlgebra.ι q x * CliffordAlgebra.ι q ePos) =
        CliffordAlgebra.ι q (x - (2 * x.1) • ePos) ∧
      -(CliffordAlgebra.ι q eNeg * CliffordAlgebra.ι q x * (-CliffordAlgebra.ι q eNeg)) =
        CliffordAlgebra.ι q (x - (2 * x.2) • eNeg) := by
  intro q ePos eNeg
  have hqp : q ePos = 1 := by simp [q, ePos, InfoGeometry.Clifford.Cl11Matrix.q11_apply]
  have hqn : q eNeg = -1 := by simp [q, eNeg, InfoGeometry.Clifford.Cl11Matrix.q11_apply]
  have hp := pinPlus_reflection_lift_sq q ePos hqp
  have hn := pinMinus_reflection_lift_sq_and_mem q eNeg hqn
  let _ : Invertible (q ePos) := ⟨1, by rw [hqp]; ring, by rw [hqp]; ring⟩
  let _ : Invertible (q eNeg) := ⟨-1, by rw [hqn]; ring, by rw [hqn]; ring⟩
  let _ : Invertible (CliffordAlgebra.ι q ePos) := ⟨CliffordAlgebra.ι q ePos, hp.1, hp.1⟩
  let _ : Invertible (CliffordAlgebra.ι q eNeg) :=
    ⟨-CliffordAlgebra.ι q eNeg, by rw [neg_mul, hn.1, neg_neg], by rw [mul_neg, hn.1, neg_neg]⟩
  have hrp := clifford_reflection_eq_neg_twisted_conj q ePos x
  have hrn := clifford_reflection_eq_neg_twisted_conj q eNeg x
  have hrp_val : cliffordReflection q ePos x = x - (2 * x.1) • ePos := by
    unfold cliffordReflection QuadraticMap.polar
    have hinv : ⅟(q ePos) = 1 := rfl
    have hpol : q (ePos + x) - q ePos - q x = 2 * x.1 := by
      simp [q, ePos, InfoGeometry.Clifford.Cl11Matrix.q11_apply]
      ring
    rw [hinv, one_mul, hpol]
  have hrn_val : cliffordReflection q eNeg x = x - (2 * x.2) • eNeg := by
    unfold cliffordReflection QuadraticMap.polar
    have hinv : ⅟(q eNeg) = -1 := rfl
    have hpol : q (eNeg + x) - q eNeg - q x = -2 * x.2 := by
      simp [q, eNeg, InfoGeometry.Clifford.Cl11Matrix.q11_apply]
      ring
    rw [hinv, hpol]
    congr 2
    ring
  have hinv_p : ⅟(CliffordAlgebra.ι q ePos) = CliffordAlgebra.ι q ePos := rfl
  have hinv_n : ⅟(CliffordAlgebra.ι q eNeg) = -CliffordAlgebra.ι q eNeg := rfl
  refine ⟨hqp, hqn, hp.1, hn.1, hn.2, ?_, ?_⟩
  · rw [hinv_p, hrp_val] at hrp
    exact hrp
  · rw [hinv_n, hrn_val] at hrn
    exact hrn

end CliffordReflectionsAndPin

end InfoGeometry.Algebra.FiveGradedWeylTrace
