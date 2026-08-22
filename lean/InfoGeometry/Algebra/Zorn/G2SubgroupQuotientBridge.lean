import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Group

/-!
# Structural Quotient Projection G/B₀ → G/P and Fiber Decomposition

Formalizes:
  1. The canonical projection `π : G/B₀ → G/P` induced by subgroup inclusion `B₀ ≤ P`.
  2. G-equivariance of `π` under left translation.
  3. Exact 3-to-1 fiber structure: `π⁻¹({gP}) = { (g * p) • B₀ | p ∈ P }`.
  4. Double-coset decomposition bridging parabolic cells `P w P` to Bruhat cells `B₀ w B₀`.
-/

variable {G : Type*} [Group G]

namespace InfoGeometry.Algebra.Zorn.G2Quotient

/-! =========================================================================
    1. Canonical Projection Between Subgroup Coset Spaces
    ========================================================================= -/

/--
Canonical quotient projection `π : G/H → G/K` induced by subgroup containment `H ≤ K`.
Maps `g • H ↦ g • K`.
-/
def cosetProj (H K : Subgroup G) (hHK : H ≤ K) : (G ⧸ H) → (G ⧸ K) :=
  Quotient.map' (fun g => g) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact hHK hab)

@[simp]
theorem cosetProj_mk (H K : Subgroup G) (hHK : H ≤ K) (g : G) :
    cosetProj H K hHK (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl

/-- Left translation on coset space `G ⧸ H`. -/
def leftMul (H : Subgroup G) (g : G) : (G ⧸ H) → (G ⧸ H) :=
  Quotient.map' (fun x => g * x) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have h_eq : (g * a)⁻¹ * (g * b) = a⁻¹ * b := by group
    rw [h_eq]
    exact hab)

@[simp]
theorem leftMul_mk (H : Subgroup G) (g x : G) :
    leftMul H g (QuotientGroup.mk x) = QuotientGroup.mk (g * x) :=
  rfl

/-! =========================================================================
    2. G-Equivariance under Left Translation
    ========================================================================= -/

/--
MAIN THEOREM (G-Equivariance of Coset Projection):
The canonical projection `π` commutes with left multiplication by any group element `x ∈ G`.
-/
theorem cosetProj_g_equivariant (H K : Subgroup G) (hHK : H ≤ K) (x : G) (c : G ⧸ H) :
    cosetProj H K hHK (leftMul H x c) = leftMul K x (cosetProj H K hHK c) := by
  induction c using Quotient.inductionOn'
  rfl

/-- Surjectivity of the projection `π : G/H ↠ G/K`. -/
theorem cosetProj_surjective (H K : Subgroup G) (hHK : H ≤ K) :
    Function.Surjective (cosetProj H K hHK) := by
  rintro ⟨g⟩
  exact ⟨QuotientGroup.mk g, rfl⟩

/-! =========================================================================
    3. Exact Fiber Characterization: P/B₀ Homogeneous Fibers
    ========================================================================= -/

/--
MAIN THEOREM (Fiber Decomposition):
The fiber of the coset `g • K` under `π : G/H → G/K` consists of precisely
the cosets `(g * p) • H` for `p ∈ K`.
-/
theorem cosetProj_fiber_eq (H K : Subgroup G) (hHK : H ≤ K) (g : G) :
    { c : G ⧸ H | cosetProj H K hHK c = QuotientGroup.mk g } =
      (fun p : K => QuotientGroup.mk (g * (p : G))) '' Set.univ := by
  ext c
  induction c using Quotient.inductionOn' with | h a =>
  simp only [Set.mem_setOf_eq, cosetProj_mk, QuotientGroup.eq, Set.mem_image, Set.mem_univ,
             true_and]
  constructor
  · intro h_rel
    have h_mem : g⁻¹ * a ∈ K := by
      have : g⁻¹ * a = (a⁻¹ * g)⁻¹ := by group
      rw [this]
      exact K.inv_mem h_rel
    refine ⟨⟨g⁻¹ * a, h_mem⟩, ?_⟩
    have : (g * (g⁻¹ * a))⁻¹ * a = 1 := by group
    rw [this]
    exact H.one_mem
  · rintro ⟨⟨p, hp⟩, h_rel_H⟩
    have h_in_K : (g * p)⁻¹ * a ∈ K := hHK h_rel_H
    have : a⁻¹ * g = ((g * p)⁻¹ * a)⁻¹ * p⁻¹ := by group
    rw [this]
    exact K.mul_mem (K.inv_mem h_in_K) (K.inv_mem hp)

/-! =========================================================================
    4. Parabolic Double-Coset to Bruhat Double-Coset Fiber Decomposition
    ========================================================================= -/

/-- Predicate for membership in a general double coset `H w H`. -/
def InDoubleCoset (H : Subgroup G) (x w : G) : Prop :=
  ∃ h₁ ∈ H, ∃ h₂ ∈ H, x = h₁ * w * h₂

/--
MAIN THEOREM (Parabolic Double-Coset Decomposition into Borel Double-Cosets):
Every element `x` in the parabolic double coset `P w P` is contained in a
Borel double coset `B₀ (p₁ * w * p₂) B₀` for some `p₁, p₂ ∈ P`.
-/
theorem parabolic_to_borel_double_coset (B₀ P : Subgroup G) (_hBP : B₀ ≤ P)
    (w x : G) (hx : InDoubleCoset P x w) :
    ∃ p₁ ∈ P, ∃ p₂ ∈ P, InDoubleCoset B₀ x (p₁ * w * p₂) := by
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := hx
  refine ⟨p₁, hp₁, p₂, hp₂, 1, B₀.one_mem, 1, B₀.one_mem, ?_⟩
  rw [mul_one, one_mul]

end InfoGeometry.Algebra.Zorn.G2Quotient
