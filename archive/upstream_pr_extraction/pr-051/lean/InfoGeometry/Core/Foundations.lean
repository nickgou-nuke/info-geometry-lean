import Mathlib

/-!
# Unified Algebraic Foundations: Exhaustion, Commutants, and Coefficient Extraction

This module formalizes:

1. a subgroup-generated exhaustion principle for left-invariant subsets of a group;
2. the associative regular commutant theorem `L(A)' = R(Aᵐᵒᵖ)` at the level of
   linear endomorphisms;
3. module-valued extraction of the linear coefficient of a polynomial of degree
   at most four from the values at `±1` and `±2`;
4. elementary principal-ideal and idempotent-corner identities.
-/

namespace InfoGeometry.Foundations

/-! ## 1. Subgroup-generated exhaustion -/

section TitsExhaustion

variable {G : Type*} [Group G]

/-- The subgroup of elements whose left translation preserves membership in `U`. -/
def leftStabilizer (U : Set G) : Subgroup G where
  carrier := {g | ∀ x, x ∈ U ↔ g * x ∈ U}
  one_mem' := by
    intro x
    simp
  mul_mem' := by
    intro g₁ g₂ hg₁ hg₂ x
    simpa [mul_assoc] using (hg₂ x).trans (hg₁ (g₂ * x))
  inv_mem' := by
    intro g hg x
    have hx := (hg (g⁻¹ * x)).symm
    simpa [mul_assoc] using hx

@[simp]
theorem mem_leftStabilizer_iff (U : Set G) (g : G) :
    g ∈ leftStabilizer U ↔ ∀ x, x ∈ U ↔ g * x ∈ U :=
  Iff.rfl

/-- If `U` contains `1` and is invariant under a set generating all of `G`,
then `U` is the whole group. -/
theorem tits_exhaustion_of_closure_top
    (U : Set G) (h1 : (1 : G) ∈ U)
    (S : Set G) (h_gen : Subgroup.closure S = ⊤)
    (h_stab : S ⊆ leftStabilizer U) :
    U = Set.univ := by
  have h_top : leftStabilizer U = ⊤ := by
    apply le_antisymm
    · exact le_top
    · rw [← h_gen]
      exact Subgroup.closure_le.2 h_stab
  ext g
  simp only [Set.mem_univ, iff_true]
  have hg : g ∈ leftStabilizer U := by
    rw [h_top]
    exact Subgroup.mem_top g
  rw [mem_leftStabilizer_iff] at hg
  have h_eval := (hg 1).mp h1
  simpa using h_eval

end TitsExhaustion

/-! ## 2. Associative regular commutant -/

section RegularCommutant

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Left regular multiplication `L_a(x) = a * x`. -/
def leftMul (a : A) : Module.End R A where
  toFun := fun x => a * x
  map_add' := by
    intro x y
    simp [left_distrib]
  map_smul' := by
    intro r x
    calc
      a * (r • x) = a * (algebraMap R A r * x) := by
        rw [Algebra.smul_def]
      _ = algebraMap R A r * (a * x) := by
        rw [← mul_assoc, ← (Algebra.commutes r a), mul_assoc]
      _ = r • (a * x) := by
        rw [Algebra.smul_def]

/-- Right regular multiplication `R_b(x) = x * b`. -/
def rightMul (b : A) : Module.End R A where
  toFun := fun x => x * b
  map_add' := by
    intro x y
    simp [right_distrib]
  map_smul' := by
    intro r x
    simp [Algebra.smul_def, mul_assoc]

@[simp]
theorem leftMul_apply (a x : A) : leftMul (R := R) a x = a * x :=
  rfl

@[simp]
theorem rightMul_apply (b x : A) : rightMul (R := R) b x = x * b :=
  rfl

/-- Left and right regular actions commute. -/
theorem leftMul_comm_rightMul (a b : A) :
    (leftMul (R := R) a).comp (rightMul (R := R) b) =
      (rightMul (R := R) b).comp (leftMul (R := R) a) := by
  ext x
  simp [mul_assoc]

/-- Every endomorphism commuting with all left regular multiplications is right
multiplication by its value at `1`. -/
theorem regular_commutant_eq_rightMul
    (T : Module.End R A)
    (hT : ∀ a : A,
      T.comp (leftMul (R := R) a) = (leftMul (R := R) a).comp T) :
    T = rightMul (R := R) (T 1) := by
  apply LinearMap.ext
  intro x
  have h_comm := congrArg (fun F : Module.End R A => F 1) (hT x)
  simpa using h_comm

/-- Faithfulness of the right regular representation. -/
theorem rightMul_injective :
    Function.Injective (rightMul (R := R) (A := A)) := by
  intro a b hab
  have h := congrArg (fun F : Module.End R A => F 1) hab
  simpa using h

end RegularCommutant

/-! ## 3. Four-point extraction of a linear coefficient -/

section LinearExtraction

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Equality of two module-valued polynomials of degree at most four implies
 equality of their linear coefficients.  The proof uses only the evaluations at
 `1`, `-1`, `2`, and `-2`. -/
theorem degree_four_linear_coefficient
    {a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : V}
    (h : ∀ t : ℝ,
      a₀ + t • a₁ + (t ^ 2) • a₂ + (t ^ 3) • a₃ + (t ^ 4) • a₄ =
      b₀ + t • b₁ + (t ^ 2) • b₂ + (t ^ 3) • b₃ + (t ^ 4) • b₄) :
    a₁ = b₁ := by
  let P : ℝ → V := fun t =>
    a₀ + t • a₁ + (t ^ 2) • a₂ + (t ^ 3) • a₃ + (t ^ 4) • a₄
  let Q : ℝ → V := fun t =>
    b₀ + t • b₁ + (t ^ 2) • b₂ + (t ^ 3) • b₃ + (t ^ 4) • b₄
  have hPQ (t : ℝ) : P t = Q t := by
    simpa [P, Q] using h t
  have h_extract_a :
      (8 : ℝ) • (P 1 - P (-1)) - (P 2 - P (-2)) =
        (12 : ℝ) • a₁ := by
    dsimp [P]
    norm_num
    module
  have h_extract_b :
      (8 : ℝ) • (Q 1 - Q (-1)) - (Q 2 - Q (-2)) =
        (12 : ℝ) • b₁ := by
    dsimp [Q]
    norm_num
    module
  have h12 : (12 : ℝ) • a₁ = (12 : ℝ) • b₁ := by
    calc
      (12 : ℝ) • a₁ =
          (8 : ℝ) • (P 1 - P (-1)) - (P 2 - P (-2)) :=
        h_extract_a.symm
      _ = (8 : ℝ) • (Q 1 - Q (-1)) - (Q 2 - Q (-2)) := by
        rw [hPQ 1, hPQ (-1), hPQ 2, hPQ (-2)]
      _ = (12 : ℝ) • b₁ := h_extract_b
  have h_scaled := congrArg (fun v : V => (1 / 12 : ℝ) • v) h12
  norm_num [smul_smul] at h_scaled
  exact h_scaled

end LinearExtraction

/-! ## 4. Principal ideals and corners -/

section IdempotentCorner

variable {A : Type*} [Ring A]

/-- The principal left ideal `Af`. -/
def principalLeftIdeal (f : A) : Set A :=
  {x | ∃ a, x = a * f}

/-- The principal right ideal `fA`. -/
def principalRightIdeal (f : A) : Set A :=
  {x | ∃ a, x = f * a}

/-- The corner carrier `fAf`. -/
def cornerAlgebra (f : A) : Set A :=
  {x | ∃ a, x = f * a * f}

/-- The product of an element of `fA` with an element of `Af` belongs to
`fAf`.  Idempotence of `f` is not needed for this inclusion. -/
theorem right_ideal_mul_left_ideal_in_corner
    (f : A) {phi psi : A}
    (hphi : phi ∈ principalRightIdeal f)
    (hpsi : psi ∈ principalLeftIdeal f) :
    phi * psi ∈ cornerAlgebra f := by
  rcases hphi with ⟨a, rfl⟩
  rcases hpsi with ⟨b, rfl⟩
  refine ⟨a * b, ?_⟩
  simp [mul_assoc]

/-- If `f` is idempotent, right multiplication by `f` fixes every element of
`Af`. -/
theorem idempotent_absorb_left
    (f : A) (hf : f * f = f) {x : A}
    (hx : x ∈ principalLeftIdeal f) :
    x * f = x := by
  rcases hx with ⟨a, rfl⟩
  rw [mul_assoc, hf]

/-- If `f` is idempotent, left multiplication by `f` fixes every element of
`fA`. -/
theorem idempotent_absorb_right
    (f : A) (hf : f * f = f) {x : A}
    (hx : x ∈ principalRightIdeal f) :
    f * x = x := by
  rcases hx with ⟨a, rfl⟩
  rw [← mul_assoc, hf]

end IdempotentCorner

end InfoGeometry.Foundations
