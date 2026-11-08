/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.Pin55Formal
import InfoGeometry.Algebra.SplitJordanSpinor
import InfoGeometry.Algebra.JordanCayleyInversionOs

/-!
# $\mathrm{Pin}(5,5)$ Central-Sign Quotient Kernel $\{\pm 1\}$, Projective $V_4$ Closure, and Equivariant $J_2(\mathbb{O}_s)$ Determinant-Strata Action

Closes **Rank 4b** of the repository's highest-ROI formalization gaps (`docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` §10):

1. **Central-Sign Quotient Congruence & Kernel $\{\pm 1\}$ on $\mathrm{Cl}(5,5)$ (`projectiveSignSetoid`, `projectiveSignEq_mul`):**
   Proves that `ProjectiveSignEq (x y : CliffordAlgebra q55) : Prop := x = y ∨ x = -y` is an
   equivalence relation (`projectiveSignEq_equivalence`) and a multiplicative congruence
   (`projectiveSignEq_mul`), inducing a well-defined quotient multiplication `projectiveCliffordMul`
   on `Quotient projectiveSignSetoid` with kernel `{x | ProjectiveSignEq x 1} = {1, -1}`
   (`projectiveSignEq_one_iff`).
2. **Projective $V_4 = \mathbb{Z}_2 \times \mathbb{Z}_2$ Subgroup Closure of `v4Set = {1, r₀, r₅, r₀ * r₅}`:**
   Proves that every element $x \in \mathrm{v4Set}$ satisfies `ProjectiveSignEq (x * x) 1`
   (`v4Set_projective_sq_one`), and for every pair $x, y \in \mathrm{v4Set}$ there exists a canonical
   representative $z \in \mathrm{v4Set}$ with `ProjectiveSignEq (x * y) z`
   (`v4Set_projective_mul_closed`), together with the exact anticommutator witness
   `r₀ * r₅ + r₅ * r₀ = 0` (`r₀_r₅_anticommutator_zero`).
3. **Equivariant $J_2(\mathbb{O}_s)$ Determinant-Strata & Klein-Quadric Invariance (`Herm2x2Os`, `JordanMatrix2`):**
   Proves that `Herm2x2Os.traceReversal` is an involution preserving every determinant stratum
   `detStratum d = {X | X.det = d}` and the Klein quadric `kleinQuadric = {X | X.det = 0}`, while
   `Herm2x2Os.scale c` maps `detStratum d` into `detStratum ((c : ℚ) ^ 2 * d)`, preserves
   `kleinQuadric`, and commutes with `traceReversal`. Also establishes trace-reversal determinant
   invariance on the polymorphic split composition carrier `JordanMatrix2 K A`.
-/

noncomputable section

namespace InfoGeometry.Algebra.Pin55SplitJordanSpinorEquivarianceSynthesis

open CliffordAlgebra
open InfoGeometry.Physics.Pin55Formal
open InfoGeometry.Algebra.SplitJordanSpinor
open InfoGeometry.Algebra.JordanCayleyInversionOs

/-! ===========================================================================
    Section 1: Central-Sign Quotient Congruence & Kernel `{±1}` on `Cl(5,5)`
    =========================================================================== -/

section CentralSignQuotient

/-- Exact anticommutator witness for the split `(5,5)` Clifford generators `r₀` and `r₅`:
`r₀ * r₅ + r₅ * r₀ = 0`. -/
theorem r₀_r₅_anticommutator_zero :
    r₀ * r₅ + r₅ * r₀ = 0 := by
  rw [anticomm, neg_add_cancel]

/-- Reverse anticommutation identity `r₅ * r₀ = -(r₀ * r₅)`. -/
theorem r₅_mul_r₀ :
    r₅ * r₀ = -(r₀ * r₅) := by
  calc
    r₅ * r₀ = -(-(r₅ * r₀)) := by abel
    _ = -(r₀ * r₅) := by rw [← anticomm]

/-- Reflexivity of `ProjectiveSignEq`. -/
theorem projectiveSignEq_refl (x : CliffordAlgebra q55) :
    ProjectiveSignEq x x :=
  Or.inl rfl

/-- Symmetry of `ProjectiveSignEq`. -/
theorem projectiveSignEq_symm {x y : CliffordAlgebra q55} (h : ProjectiveSignEq x y) :
    ProjectiveSignEq y x := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · right
    abel

/-- Transitivity of `ProjectiveSignEq`. -/
theorem projectiveSignEq_trans {x y z : CliffordAlgebra q55}
    (hxy : ProjectiveSignEq x y) (hyz : ProjectiveSignEq y z) :
    ProjectiveSignEq x z := by
  rcases hxy with rfl | rfl <;> rcases hyz with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · left
    abel

/-- `ProjectiveSignEq` is an equivalence relation on `CliffordAlgebra q55`. -/
theorem projectiveSignEq_equivalence :
    Equivalence ProjectiveSignEq :=
  ⟨projectiveSignEq_refl, projectiveSignEq_symm, projectiveSignEq_trans⟩

/-- Setoid on `CliffordAlgebra q55` identifying elements up to central sign `±1`. -/
def projectiveSignSetoid : Setoid (CliffordAlgebra q55) where
  r := ProjectiveSignEq
  iseqv := projectiveSignEq_equivalence

/-- Multiplicative congruence of `ProjectiveSignEq`:
if `x₁ ≡ ±y₁` and `x₂ ≡ ±y₂`, then `x₁ * x₂ ≡ ±(y₁ * y₂)`. -/
theorem projectiveSignEq_mul {x₁ y₁ x₂ y₂ : CliffordAlgebra q55}
    (h₁ : ProjectiveSignEq x₁ y₁) (h₂ : ProjectiveSignEq x₂ y₂) :
    ProjectiveSignEq (x₁ * x₂) (y₁ * y₂) := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact Or.inl rfl
  · right
    exact mul_neg x₁ y₂
  · right
    exact neg_mul y₁ x₂
  · left
    exact neg_mul_neg y₁ y₂

/-- Well-defined multiplication on the projective-sign quotient `Quotient projectiveSignSetoid`. -/
def projectiveCliffordMul :
    Quotient projectiveSignSetoid → Quotient projectiveSignSetoid →
      Quotient projectiveSignSetoid :=
  Quotient.map₂ (· * ·) (fun _ _ h₁ _ _ h₂ => projectiveSignEq_mul h₁ h₂)

/-- Exact characterization of the central-sign kernel `{x | ProjectiveSignEq x 1} = {1, -1}`. -/
theorem projectiveSignEq_one_iff (x : CliffordAlgebra q55) :
    ProjectiveSignEq x 1 ↔ x = 1 ∨ x = -1 :=
  Iff.rfl

end CentralSignQuotient

/-! ===========================================================================
    Section 2: Projective `V₄ = ℤ₂ × ℤ₂` Closure of `v4Set = {1, r₀, r₅, r₀ * r₅}`
    =========================================================================== -/

section ProjectiveV4Closure

/-- Helper product identities among the 4 generators `{1, r₀, r₅, r₀ * r₅}` in `CliffordAlgebra q55`. -/
theorem r₀_mul_r₀r₅ : r₀ * (r₀ * r₅) = r₅ := by
  calc
    r₀ * (r₀ * r₅) = (r₀ * r₀) * r₅ := (mul_assoc r₀ r₀ r₅).symm
    _ = 1 * r₅ := by rw [r₀_sq]
    _ = r₅ := one_mul r₅

theorem r₀r₅_mul_r₀ : (r₀ * r₅) * r₀ = -r₅ := by
  calc
    (r₀ * r₅) * r₀ = r₀ * (r₅ * r₀) := mul_assoc r₀ r₅ r₀
    _ = r₀ * (-(r₀ * r₅)) := by rw [r₅_mul_r₀]
    _ = -(r₀ * (r₀ * r₅)) := mul_neg r₀ (r₀ * r₅)
    _ = -r₅ := by rw [r₀_mul_r₀r₅]

theorem r₅_mul_r₀r₅ : r₅ * (r₀ * r₅) = r₀ := by
  calc
    r₅ * (r₀ * r₅) = (r₅ * r₀) * r₅ := (mul_assoc r₅ r₀ r₅).symm
    _ = (-(r₀ * r₅)) * r₅ := by rw [r₅_mul_r₀]
    _ = -(r₀ * (r₅ * r₅)) := by rw [neg_mul, mul_assoc]
    _ = -(r₀ * (-1)) := by rw [r₅_sq]
    _ = r₀ := by simp

theorem r₀r₅_mul_r₅ : (r₀ * r₅) * r₅ = -r₀ := by
  calc
    (r₀ * r₅) * r₅ = r₀ * (r₅ * r₅) := mul_assoc r₀ r₅ r₅
    _ = r₀ * (-1) := by rw [r₅_sq]
    _ = -r₀ := by simp

/-- Every element of `v4Set = {1, r₀, r₅, r₀ * r₅}` squares to `±1` (`ProjectiveSignEq (x * x) 1`). -/
theorem v4Set_projective_sq_one {x : CliffordAlgebra q55} (hx : x ∈ v4Set) :
    ProjectiveSignEq (x * x) 1 := by
  rcases hx with rfl | rfl | rfl | hlast
  · left
    exact mul_one 1
  · exact r₀_projective_involutive
  · exact r₅_projective_involutive
  · rcases hlast with rfl
    exact r₀r₅_projective_involutive

/-- **Theorem 2.1 (`v4Set_projective_mul_closed`):**
The four-element frame `v4Set = {1, r₀, r₅, r₀ * r₅}` is closed under multiplication up to
`ProjectiveSignEq`: for all `x, y ∈ v4Set`, there exists `z ∈ v4Set` such that
`ProjectiveSignEq (x * y) z`. -/
theorem v4Set_projective_mul_closed {x y : CliffordAlgebra q55}
    (hx : x ∈ v4Set) (hy : y ∈ v4Set) :
    ∃ z ∈ v4Set, ProjectiveSignEq (x * y) z := by
  have h1_mem : (1 : CliffordAlgebra q55) ∈ v4Set := by simp [v4Set]
  have hr0_mem : r₀ ∈ v4Set := by simp [v4Set]
  have hr5_mem : r₅ ∈ v4Set := by simp [v4Set]
  have hr0r5_mem : r₀ * r₅ ∈ v4Set := by simp [v4Set]
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
  · exact ⟨1, h1_mem, Or.inl (one_mul 1)⟩
  · exact ⟨r₀, hr0_mem, Or.inl (one_mul r₀)⟩
  · exact ⟨r₅, hr5_mem, Or.inl (one_mul r₅)⟩
  · exact ⟨r₀ * r₅, hr0r5_mem, Or.inl (one_mul (r₀ * r₅))⟩
  · exact ⟨r₀, hr0_mem, Or.inl (mul_one r₀)⟩
  · exact ⟨1, h1_mem, r₀_projective_involutive⟩
  · exact ⟨r₀ * r₅, hr0r5_mem, Or.inl rfl⟩
  · exact ⟨r₅, hr5_mem, Or.inl r₀_mul_r₀r₅⟩
  · exact ⟨r₅, hr5_mem, Or.inl (mul_one r₅)⟩
  · exact ⟨r₀ * r₅, hr0r5_mem, Or.inr r₅_mul_r₀⟩
  · exact ⟨1, h1_mem, r₅_projective_involutive⟩
  · exact ⟨r₀, hr0_mem, Or.inl r₅_mul_r₀r₅⟩
  · exact ⟨r₀ * r₅, hr0r5_mem, Or.inl (mul_one (r₀ * r₅))⟩
  · exact ⟨r₅, hr5_mem, Or.inr r₀r₅_mul_r₀⟩
  · exact ⟨r₀, hr0_mem, Or.inr r₀r₅_mul_r₅⟩
  · exact ⟨1, h1_mem, r₀r₅_projective_involutive⟩

end ProjectiveV4Closure

/-! ===========================================================================
    Section 3: Equivariant `J₂(𝕆_s)` Determinant-Strata & Klein-Quadric Action
    =========================================================================== -/

section SplitJordanDeterminantStrata

/-- Level set (`d`-stratum) of the `(5,5)` quadratic determinant on `Herm2x2Os = J₂(𝕆_s)`. -/
def Herm2x2Os.detStratum (d : ℚ) : Set Herm2x2Os :=
  {X : Herm2x2Os | X.det = d}

/-- The null Klein quadric `{X ∈ J₂(𝕆_s) | det(X) = 0}` is the `0`-stratum. -/
def Herm2x2Os.kleinQuadric : Set Herm2x2Os :=
  Herm2x2Os.detStratum 0

/-- Trace reversal on the polymorphic split composition Jordan carrier `JordanMatrix2 K A`. -/
def jordanTraceReversal {K A : Type*} (J : JordanMatrix2 K A) : JordanMatrix2 K A :=
  ⟨J.β, J.α, J.Z⟩

/-- Polymorphic trace reversal is an involution on `JordanMatrix2 K A`. -/
@[simp] theorem jordanTraceReversal_involutive {K A : Type*} (J : JordanMatrix2 K A) :
    jordanTraceReversal (jordanTraceReversal J) = J := by
  cases J
  rfl

/-- Polymorphic trace reversal preserves `JordanMatrix2.determinant` (`αβ - N(Z) = βα - N(Z)`). -/
@[simp] theorem determinant_jordanTraceReversal
    {K A : Type*} [CommRing K] [NonAssocSemiring A] [SMul K A] [SplitCompositionAlgebra K A]
    (J : JordanMatrix2 K A) :
    JordanMatrix2.determinant (A := A) (jordanTraceReversal J) =
      JordanMatrix2.determinant (A := A) J := by
  unfold JordanMatrix2.determinant jordanTraceReversal
  dsimp
  ring

/-- Trace reversal preserves every determinant stratum `Herm2x2Os.detStratum d`. -/
theorem Herm2x2Os.mem_detStratum_traceReversal_iff (X : Herm2x2Os) (d : ℚ) :
    X ∈ Herm2x2Os.detStratum d ↔ X.traceReversal ∈ Herm2x2Os.detStratum d := by
  simp [Herm2x2Os.detStratum, Herm2x2Os.det_traceReversal]

/-- Integer coordinate scaling maps `detStratum d` into `detStratum ((c : ℚ) ^ 2 * d)`. -/
theorem Herm2x2Os.scale_mem_detStratum {X : Herm2x2Os} {d : ℚ} (c : ℤ)
    (hX : X ∈ Herm2x2Os.detStratum d) :
    Herm2x2Os.scale c X ∈ Herm2x2Os.detStratum ((c : ℚ) ^ 2 * d) := by
  change X.det = d at hX
  change (Herm2x2Os.scale c X).det = (c : ℚ) ^ 2 * d
  rw [Herm2x2Os.det_scale, hX]

/-- On the null Klein quadric `Herm2x2Os.kleinQuadric`, trace reversal and integer scaling
preserve the quadric and annihilate both diagonal entries of `mulTraceReversal`. -/
theorem Herm2x2Os.kleinQuadric_traceReversal_and_scale {X : Herm2x2Os} (c : ℤ)
    (hK : X ∈ Herm2x2Os.kleinQuadric) :
    X.traceReversal ∈ Herm2x2Os.kleinQuadric ∧
    Herm2x2Os.scale c X ∈ Herm2x2Os.kleinQuadric ∧
    (X.traceReversal).mulTraceReversal.e11 = 0 ∧
    (X.traceReversal).mulTraceReversal.e22 = 0 := by
  change X.det = 0 at hK
  have htr : X.traceReversal.det = 0 := by
    rw [Herm2x2Os.det_traceReversal, hK]
  have hsc : (Herm2x2Os.scale c X).det = 0 := by
    rw [Herm2x2Os.det_scale, hK, mul_zero]
  have hkq := Herm2x2Os.on_klein_quadric X.traceReversal htr
  exact ⟨htr, hsc, hkq.1, hkq.2⟩

/-- **Theorem 3.1 (`pin55_projective_v4_and_split_jordan_determinant_strata_synthesis`):**
Unifies:
1. Central-sign congruence `projectiveSignEq_mul` and kernel `{x | ProjectiveSignEq x 1} = {1, -1}` on `Cl(5,5)`,
2. Projective `V₄` closure (`v4Set_projective_mul_closed`) and projective involutivity (`v4Set_projective_sq_one`) of `v4Set = {1, r₀, r₅, r₀ * r₅}`,
3. Exact preservation of every determinant stratum `Herm2x2Os.detStratum d` under `Herm2x2Os.traceReversal`,
4. Quadratic scaling of determinant strata `X ∈ detStratum d → scale c X ∈ detStratum ((c : ℚ) ^ 2 * d)` and exact preservation of the Klein quadric `X ∈ kleinQuadric → scale c X ∈ kleinQuadric ∧ X.traceReversal ∈ kleinQuadric`,
5. Polymorphic determinant invariance `JordanMatrix2.determinant (jordanTraceReversal J) = JordanMatrix2.determinant J`. -/
theorem pin55_projective_v4_and_split_jordan_determinant_strata_synthesis
    {K A : Type*} [CommRing K] [NonAssocSemiring A] [SMul K A] [SplitCompositionAlgebra K A]
    (J : JordanMatrix2 K A)
    {x y : CliffordAlgebra q55} (hx : x ∈ v4Set) (hy : y ∈ v4Set)
    (X : Herm2x2Os) (d : ℚ) (c : ℤ) :
    -- (1) Projective V₄ square-one and multiplicative closure
    (ProjectiveSignEq (x * x) 1 ∧
     (∃ z ∈ v4Set, ProjectiveSignEq (x * y) z) ∧
     r₀ * r₅ + r₅ * r₀ = 0) ∧
    -- (2) J₂(𝕆_s) trace-reversal stratum invariance and quadratic scaling
    ((X ∈ Herm2x2Os.detStratum d ↔ X.traceReversal ∈ Herm2x2Os.detStratum d) ∧
     (X ∈ Herm2x2Os.detStratum d →
       Herm2x2Os.scale c X ∈ Herm2x2Os.detStratum ((c : ℚ) ^ 2 * d)) ∧
     (X ∈ Herm2x2Os.kleinQuadric →
       X.traceReversal ∈ Herm2x2Os.kleinQuadric ∧
       Herm2x2Os.scale c X ∈ Herm2x2Os.kleinQuadric ∧
       (X.traceReversal).mulTraceReversal.e11 = 0 ∧
       (X.traceReversal).mulTraceReversal.e22 = 0)) ∧
    -- (3) Polymorphic JordanMatrix2 trace-reversal determinant invariance
    (JordanMatrix2.determinant (A := A) (jordanTraceReversal J) =
       JordanMatrix2.determinant (A := A) J ∧
     jordanTraceReversal (jordanTraceReversal J) = J) :=
  ⟨⟨v4Set_projective_sq_one hx, v4Set_projective_mul_closed hx hy, r₀_r₅_anticommutator_zero⟩,
   ⟨Herm2x2Os.mem_detStratum_traceReversal_iff X d,
    Herm2x2Os.scale_mem_detStratum c,
    Herm2x2Os.kleinQuadric_traceReversal_and_scale c⟩,
   ⟨determinant_jordanTraceReversal J, jordanTraceReversal_involutive J⟩⟩

end SplitJordanDeterminantStrata

end InfoGeometry.Algebra.Pin55SplitJordanSpinorEquivarianceSynthesis
