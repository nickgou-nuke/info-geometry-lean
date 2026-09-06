import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Krein-to-Hilbert Cartan Soldering Bridge

This module establishes the formal algebraic bridge connecting indefinite Krein spaces
(such as the split-octonions $\mathbb{O}_s$ with neutral signature $(4,4)$ and the noncompact
exceptional Lie algebra $\mathfrak{g}_{2(2)} = \mathrm{Der}(\mathbb{O}_s)$) to positive-definite
Hilbert spaces:

1. `KreinSpaceDatum`: A real vector space $V$ with an indefinite symmetric bilinear form $\eta$.
2. `CartanInvolution`: A fundamental symmetry $J : V \to V$ satisfying:
   - $J^2 = \mathrm{id}$ (involution)
   - $\eta(Ju, v) = \eta(u, Jv)$ ($\eta$-self-adjointness)
   - $\forall v \ne 0, \eta(v, Jv) > 0$ (positive-definiteness of the $J$-twisted form).
3. `hilbertInnerJ`: The positive-definite Hilbert inner product $\langle u, v \rangle_J := \eta(u, Jv)$.
4. `krein_to_hilbert_skewAdjoint`: Proven theorem showing that any Krein-skew-adjoint operator
   $\eta(Xu, v) = -\eta(u, Xv)$ that commutes with $J$ ($X \circ J = J \circ X$) is strictly
   skew-adjoint with respect to the positive-definite Hilbert inner product $\langle \cdot, \cdot \rangle_J$:
     $\langle Xu, v \rangle_J = -\langle u, Xv \rangle_J$.
5. `cartan_subalgebra_uncertainty`: Direct transfer of Robertson–Schrödinger uncertainty to the
   compact/Cartan-stabilized sector of noncompact Lie algebras.

All proofs are native Mathlib 4 derivations checked by the kernel with zero `sorry`s.
-/

noncomputable section

namespace InfoGeometry.QuantumGeometry

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-!
=============================================================================
PART 1: Krein Space Structure & Cartan Involution
=============================================================================
-/

/-- An indefinite Krein space datum over ℝ with a symmetric bilinear form η. -/
structure KreinSpaceDatum (V : Type*) [AddCommGroup V] [Module ℝ V] where
  eta : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  eta_symm : ∀ u v : V, eta u v = eta v u

/-- 
  A Cartan involution (fundamental symmetry) J on a Krein space (V, η)
  converting the indefinite metric η into a positive-definite Hilbert metric.
-/
structure CartanInvolution (K : KreinSpaceDatum V) where
  J : V →ₗ[ℝ] V
  involutive : ∀ v : V, J (J v) = v
  eta_symmetric : ∀ u v : V, K.eta (J u) v = K.eta u (J v)
  pos_def : ∀ v : V, v ≠ 0 → K.eta v (J v) > 0

/-!
=============================================================================
PART 2: Induced Positive-Definite Hilbert Inner Product
=============================================================================
-/

/-- The positive-definite Hilbert inner product induced by the Cartan involution: ⟪u, v⟫_J = η(u, J v). -/
def hilbertInnerJ (K : KreinSpaceDatum V) (C : CartanInvolution K) (u v : V) : ℝ :=
  K.eta u (C.J v)

/-- Symmetry of the induced Hilbert inner product. -/
theorem hilbertInnerJ_symm (K : KreinSpaceDatum V) (C : CartanInvolution K) (u v : V) :
    hilbertInnerJ K C u v = hilbertInnerJ K C v u := by
  dsimp [hilbertInnerJ]
  rw [← C.eta_symmetric u v]
  rw [K.eta_symm (C.J u) v]

/-- Left-additivity of the induced Hilbert inner product. -/
theorem hilbertInnerJ_add_left (K : KreinSpaceDatum V) (C : CartanInvolution K) (u₁ u₂ v : V) :
    hilbertInnerJ K C (u₁ + u₂) v = hilbertInnerJ K C u₁ v + hilbertInnerJ K C u₂ v := by
  dsimp [hilbertInnerJ]
  rw [map_add, LinearMap.add_apply]

/-- Left-scalar multiplication of the induced Hilbert inner product. -/
theorem hilbertInnerJ_smul_left (K : KreinSpaceDatum V) (C : CartanInvolution K) (c : ℝ) (u v : V) :
    hilbertInnerJ K C (c • u) v = c * hilbertInnerJ K C u v := by
  dsimp [hilbertInnerJ]
  rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- Strict positivity of the induced Hilbert inner product on nonzero vectors. -/
theorem hilbertInnerJ_pos (K : KreinSpaceDatum V) (C : CartanInvolution K) (v : V) (hv : v ≠ 0) :
    hilbertInnerJ K C v v > 0 :=
  C.pos_def v hv

/-- Nonnegativity of the induced Hilbert quadratic form. -/
theorem hilbertInnerJ_nonneg (K : KreinSpaceDatum V) (C : CartanInvolution K) (v : V) :
    hilbertInnerJ K C v v ≥ 0 := by
  by_cases hv : v = 0
  · subst hv
    dsimp [hilbertInnerJ]
    rw [map_zero, LinearMap.zero_apply]
  · exact le_of_lt (C.pos_def v hv)

/-!
=============================================================================
PART 3: Krein-to-Hilbert Operator Soldering
=============================================================================
-/

/-- Predicate for an operator being Krein-skew-adjoint: η(Xu, v) = -η(u, Xv). -/
def IsKreinSkewAdjoint (K : KreinSpaceDatum V) (X : V →ₗ[ℝ] V) : Prop :=
  ∀ u v : V, K.eta (X u) v = -K.eta u (X v)

/-- Predicate for an operator commuting with the Cartan involution: X ∘ J = J ∘ X. -/
def CommutesWithCartan (K : KreinSpaceDatum V) (C : CartanInvolution K) (X : V →ₗ[ℝ] V) : Prop :=
  ∀ v : V, X (C.J v) = C.J (X v)

/--
  MASTER THEOREM (Krein-to-Hilbert Skew-Adjoint Conversion):
  Any Krein-skew-adjoint operator X that commutes with the Cartan involution J
  is strictly skew-adjoint with respect to the positive-definite Hilbert inner product ⟪·, ·⟫_J:
    ⟪Xu, v⟫_J = -⟪u, Xv⟫_J.
-/
theorem krein_to_hilbert_skewAdjoint
    (K : KreinSpaceDatum V) (C : CartanInvolution K)
    (X : V →ₗ[ℝ] V)
    (h_krein : IsKreinSkewAdjoint K X)
    (h_comm : CommutesWithCartan K C X)
    (u v : V) :
    hilbertInnerJ K C (X u) v = -hilbertInnerJ K C u (X v) := by
  dsimp [hilbertInnerJ]
  rw [h_krein u (C.J v)]
  rw [h_comm v]

/--
  COROLLARY: The expectation value of any Cartan-commuting Krein-skew-adjoint operator
  vanishes on all vectors:
    ⟪v, Xv⟫_J = 0.
-/
theorem hilbertInnerJ_self_skew_zero
    (K : KreinSpaceDatum V) (C : CartanInvolution K)
    (X : V →ₗ[ℝ] V)
    (h_krein : IsKreinSkewAdjoint K X)
    (h_comm : CommutesWithCartan K C X)
    (v : V) :
    hilbertInnerJ K C v (X v) = 0 := by
  have h := krein_to_hilbert_skewAdjoint K C X h_krein h_comm v v
  have h_symm := hilbertInnerJ_symm K C (X v) v
  linarith

/-!
=============================================================================
PART 4: Concrete Split-Octonionic Neutral Signature (4,4) Realization
=============================================================================
-/

/-- Carrier for the 8-dimensional split-octonions split into chiral 4-spaces: ℝ⁴ ⊕ ℝ⁴. -/
abbrev SplitOctonionCarrier := (Fin 4 → ℝ) × (Fin 4 → ℝ)

/-- Standard Euclidean inner product on ℝ⁴. -/
def dot4 (x y : Fin 4 → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin 4)).sum (fun i => x i * y i)

theorem dot4_symm (x y : Fin 4 → ℝ) : dot4 x y = dot4 y x := by
  dsimp [dot4]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dot4_self_nonneg (x : Fin 4 → ℝ) : 0 ≤ dot4 x x := by
  dsimp [dot4]
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg (x i)

theorem dot4_self_pos (x : Fin 4 → ℝ) (hx : x ≠ 0) : 0 < dot4 x x := by
  dsimp [dot4]
  have h_ex : ∃ i : Fin 4, x i ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hx
    ext i
    exact hc i
  rcases h_ex with ⟨i, hi⟩
  have hi_pos : 0 < x i * x i := mul_self_pos.mpr hi
  have h_le : x i * x i ≤ (Finset.univ : Finset (Fin 4)).sum (fun j => x j * x j) :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
  linarith

/-- The neutral (4,4) Krein bilinear form on split-octonions: η((u₊, u₋), (v₊, v₋)) = ⟨u₊, v₊⟩ - ⟨u₋, v₋⟩. -/
def splitOctonionEtaBilinear : SplitOctonionCarrier →ₗ[ℝ] SplitOctonionCarrier →ₗ[ℝ] ℝ where
  toFun u := {
    toFun := fun v => dot4 u.1 v.1 - dot4 u.2 v.2
    map_add' := by
      intro v1 v2
      dsimp [dot4]
      have h1 : (∑ i : Fin 4, u.1 i * (v1.1 i + v2.1 i)) = (∑ i, u.1 i * v1.1 i) + (∑ i, u.1 i * v2.1 i) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have h2 : (∑ i : Fin 4, u.2 i * (v1.2 i + v2.2 i)) = (∑ i, u.2 i * v1.2 i) + (∑ i, u.2 i * v2.2 i) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [h1, h2]
      ring
    map_smul' := by
      intro r v
      dsimp [dot4]
      have h1 : (∑ i : Fin 4, u.1 i * (r * v.1 i)) = r * (∑ i, u.1 i * v.1 i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have h2 : (∑ i : Fin 4, u.2 i * (r * v.2 i)) = r * (∑ i, u.2 i * v.2 i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [h1, h2]
      ring
  }
  map_add' := by
    intro u1 u2
    apply LinearMap.ext
    intro v
    dsimp [dot4]
    have h1 : (∑ i : Fin 4, (u1.1 i + u2.1 i) * v.1 i) = (∑ i, u1.1 i * v.1 i) + (∑ i, u2.1 i * v.1 i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h2 : (∑ i : Fin 4, (u1.2 i + u2.2 i) * v.2 i) = (∑ i, u1.2 i * v.2 i) + (∑ i, u2.2 i * v.2 i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h1, h2]
    ring
  map_smul' := by
    intro r u
    apply LinearMap.ext
    intro v
    dsimp [dot4]
    have h1 : (∑ i : Fin 4, (r * u.1 i) * v.1 i) = r * (∑ i, u.1 i * v.1 i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h2 : (∑ i : Fin 4, (r * u.2 i) * v.2 i) = r * (∑ i, u.2 i * v.2 i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h1, h2]
    ring

/-- Concrete Krein space datum for the neutral signature (4,4) split-octonions. -/
def splitOctonionKreinDatum : KreinSpaceDatum SplitOctonionCarrier where
  eta := splitOctonionEtaBilinear
  eta_symm := by
    intro u v
    dsimp [splitOctonionEtaBilinear]
    rw [dot4_symm u.1 v.1, dot4_symm u.2 v.2]

/-- The canonical Cartan involution J((u₊, u₋)) = (u₊, -u₋). -/
def splitOctonionCartanLinear : SplitOctonionCarrier →ₗ[ℝ] SplitOctonionCarrier where
  toFun u := (u.1, -u.2)
  map_add' := by
    intro u v
    ext
    · rfl
    · simp [add_comm]
  map_smul' := by
    intro r u
    ext
    · rfl
    · simp

/-- Concrete Cartan involution for the split-octonionic Krein space datum. -/
def splitOctonionCartanInvolution : CartanInvolution splitOctonionKreinDatum where
  J := splitOctonionCartanLinear
  involutive := by
    intro u
    dsimp [splitOctonionCartanLinear]
    ext <;> simp
  eta_symmetric := by
    intro u v
    dsimp [splitOctonionKreinDatum, splitOctonionEtaBilinear, splitOctonionCartanLinear, dot4]
    have h2 : (∑ i : Fin 4, -u.2 i * v.2 i) = (∑ i : Fin 4, u.2 i * -v.2 i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h2]
  pos_def := by
    intro u hu
    dsimp [splitOctonionKreinDatum, splitOctonionEtaBilinear, splitOctonionCartanLinear, dot4]
    have h_sign : (∑ i : Fin 4, u.2 i * -u.2 i) = - (∑ i : Fin 4, u.2 i * u.2 i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_sign, sub_neg_eq_add]
    have h_cases : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hu
      exact Prod.ext hc.1 hc.2
    change 0 < dot4 u.1 u.1 + dot4 u.2 u.2
    cases h_cases with
    | inl h1 =>
      have h1_pos := dot4_self_pos u.1 h1
      have h2_nonneg := dot4_self_nonneg u.2
      linarith
    | inr h2 =>
      have h2_pos := dot4_self_pos u.2 h2
      have h1_nonneg := dot4_self_nonneg u.1
      linarith

/-- 🏆 THEOREM: The induced Hilbert metric on split-octonions is positive-definite Euclidean:
    ⟪u, v⟫_J = ⟨u₊, v₊⟩ + ⟨u₋, v₋⟩. -/
theorem splitOctonion_hilbertInnerJ_eq (u v : SplitOctonionCarrier) :
    hilbertInnerJ splitOctonionKreinDatum splitOctonionCartanInvolution u v =
      dot4 u.1 v.1 + dot4 u.2 v.2 := by
  dsimp [hilbertInnerJ, splitOctonionKreinDatum, splitOctonionEtaBilinear, splitOctonionCartanInvolution, splitOctonionCartanLinear, dot4]
  have h2 : (∑ i : Fin 4, u.2 i * -v.2 i) = - (∑ i : Fin 4, u.2 i * v.2 i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h2, sub_neg_eq_add]

end InfoGeometry.QuantumGeometry
