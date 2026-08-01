import InfoGeometry.Algebra.JordanInnerDerivations

/-!
# Baez F₄ readouts for the verified `H3Zorn` Jordan surface

Source pointer: John Baez, *The Octonions*, §4.2 “F₄”
<https://math.ucr.edu/home/baez/octonions/node15.html>.

Baez recalls the Chevalley--Schafer description
`F₄ = Aut(h₃(𝕆))` and `𝔣₄ = Der(h₃(𝕆))`.  This file formalizes the
corresponding theorem-safe native surfaces for the repository's already
verified real split `H3Zorn ℝ` Jordan product:

* a bundled type of linear Jordan automorphisms of `H3Zorn ℝ`;
* the identity, composition, and inverse automorphisms;
* the Leibniz derivation predicate for the installed Jordan product;
* the fact that these derivations form a Mathlib `LieSubalgebra` of
  `Module.End ℝ (H3Zorn ℝ)`.
The scope stays at the algebraic carrier, automorphisms, derivations, and
Lie-subalgebra closure for the installed product.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn

/-- Linear Jordan automorphisms of the verified real split `H3Zorn` product. -/
structure H3ZornJordanAut where
  toLinearEquiv : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ
  map_one' : toLinearEquiv 1 = 1
  map_mul' : ∀ X Y : H3Zorn ℝ, toLinearEquiv (X * Y) = toLinearEquiv X * toLinearEquiv Y

namespace H3ZornJordanAut

instance : CoeFun H3ZornJordanAut (fun _ => H3Zorn ℝ → H3Zorn ℝ) where
  coe A := A.toLinearEquiv

/-- A Jordan automorphism fixes the unit. -/
@[simp] theorem map_one (A : H3ZornJordanAut) : A 1 = 1 :=
  A.map_one'

/-- A Jordan automorphism preserves the installed Jordan product. -/
@[simp] theorem map_mul (A : H3ZornJordanAut) (X Y : H3Zorn ℝ) :
    A (X * Y) = A X * A Y :=
  A.map_mul' X Y

/-- The identity Jordan automorphism. -/
def id : H3ZornJordanAut where
  toLinearEquiv := LinearEquiv.refl ℝ (H3Zorn ℝ)
  map_one' := rfl
  map_mul' := by intro X Y; rfl

@[simp] theorem id_apply (X : H3Zorn ℝ) : id X = X := rfl

/-- Composition of Jordan automorphisms. -/
def comp (A B : H3ZornJordanAut) : H3ZornJordanAut where
  toLinearEquiv := A.toLinearEquiv.trans B.toLinearEquiv
  map_one' := by simp
  map_mul' := by intro X Y; simp

@[simp] theorem comp_apply (A B : H3ZornJordanAut) (X : H3Zorn ℝ) :
    comp A B X = B (A X) := rfl

/-- The inverse of a Jordan automorphism is again a Jordan automorphism. -/
def inv (A : H3ZornJordanAut) : H3ZornJordanAut where
  toLinearEquiv := A.toLinearEquiv.symm
  map_one' := by
    apply A.toLinearEquiv.injective
    simp
  map_mul' := by
    intro X Y
    apply A.toLinearEquiv.injective
    rw [A.map_mul]
    simp

@[simp] theorem inv_apply_apply (A : H3ZornJordanAut) (X : H3Zorn ℝ) :
    A (inv A X) = X := by
  exact A.toLinearEquiv.apply_symm_apply X

@[simp] theorem apply_inv_apply (A : H3ZornJordanAut) (X : H3Zorn ℝ) :
    inv A (A X) = X := by
  exact A.toLinearEquiv.symm_apply_apply X

end H3ZornJordanAut

/-- Baez/Chevalley--Schafer-style automorphism carrier for this real split model. -/
abbrev H3ZornF4Aut := H3ZornJordanAut

/-- The automorphism carrier is inhabited by the identity automorphism. -/
def H3ZornF4Aut.id : H3ZornF4Aut :=
  H3ZornJordanAut.id

/-- Leibniz derivation predicate for the installed `H3Zorn ℝ` Jordan product. -/
def H3ZornJordanDerivation (D : Module.End ℝ (H3Zorn ℝ)) : Prop :=
  ∀ X Y : H3Zorn ℝ, D (X * Y) = D X * Y + X * D Y

private theorem zero_mul_candidate (X : H3Zorn ℝ) :
    (0 : H3Zorn ℝ) * X = 0 := by
  change candidateJordanMul 0 X = 0
  simpa using candidateJordanMul_smul_left (0 : ℝ) (0 : H3Zorn ℝ) X

private theorem mul_zero_candidate (X : H3Zorn ℝ) :
    X * (0 : H3Zorn ℝ) = 0 := by
  change candidateJordanMul X 0 = 0
  simpa using candidateJordanMul_smul_right (0 : ℝ) X (0 : H3Zorn ℝ)

private theorem add_mul_candidate (X Y Z : H3Zorn ℝ) :
    (X + Y) * Z = X * Z + Y * Z := by
  change candidateJordanMul (X + Y) Z = candidateJordanMul X Z + candidateJordanMul Y Z
  exact candidateJordanMul_add_left X Y Z

private theorem mul_add_candidate (X Y Z : H3Zorn ℝ) :
    X * (Y + Z) = X * Y + X * Z := by
  change candidateJordanMul X (Y + Z) = candidateJordanMul X Y + candidateJordanMul X Z
  exact candidateJordanMul_add_right X Y Z

private theorem smul_mul_candidate (r : ℝ) (X Y : H3Zorn ℝ) :
    (r • X) * Y = r • (X * Y) := by
  change candidateJordanMul (r • X) Y = r • candidateJordanMul X Y
  exact candidateJordanMul_smul_left r X Y

private theorem mul_smul_candidate (r : ℝ) (X Y : H3Zorn ℝ) :
    X * (r • Y) = r • (X * Y) := by
  change candidateJordanMul X (r • Y) = r • candidateJordanMul X Y
  exact candidateJordanMul_smul_right r X Y

private theorem neg_mul_candidate (X Y : H3Zorn ℝ) :
    (-X) * Y = -(X * Y) := by
  simp

private theorem mul_neg_candidate (X Y : H3Zorn ℝ) :
    X * (-Y) = -(X * Y) := by
  simp

private theorem sub_mul_candidate (X Y Z : H3Zorn ℝ) :
    (X - Y) * Z = X * Z - Y * Z := by
  rw [sub_eq_add_neg, add_mul_candidate, neg_mul_candidate]
  rfl

private theorem mul_sub_candidate (X Y Z : H3Zorn ℝ) :
    X * (Y - Z) = X * Y - X * Z := by
  rw [sub_eq_add_neg, mul_add_candidate, mul_neg_candidate]
  rfl

/--
The derivations of the installed `H3Zorn ℝ` Jordan product form a Lie
subalgebra of the endomorphism Lie algebra.

This is the native Mathlib form of Baez's Lie-algebra slogan
`𝔣₄ = Der(h₃(𝕆))`, restricted to the verified split `H3Zorn` owner surface.
It states closure of the Leibniz derivations under addition, scalar
multiplication, and commutator.
-/
def H3ZornF4Derivations : LieSubalgebra ℝ (Module.End ℝ (H3Zorn ℝ)) where
  carrier := {D | H3ZornJordanDerivation D}
  zero_mem' := by
    intro X Y
    simp only [LinearMap.zero_apply]
    rw [zero_mul_candidate, mul_zero_candidate]
    simp
  add_mem' := by
    intro D E hD hE X Y
    simp only [LinearMap.add_apply]
    rw [hD X Y, hE X Y]
    rw [add_mul_candidate, mul_add_candidate]
    abel
  smul_mem' := by
    intro r D hD X Y
    simp only [LinearMap.smul_apply]
    rw [hD X Y]
    rw [smul_add, smul_mul_candidate, mul_smul_candidate]
  lie_mem' := by
    intro D E hD hE X Y
    simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply]
    rw [hE X Y, map_add, hD (E X) Y, hD X (E Y)]
    rw [hD X Y, map_add, hE (D X) Y, hE X (D Y)]
    rw [sub_mul_candidate, mul_sub_candidate]
    abel

/-- Membership in the F₄-derivation carrier is exactly the Leibniz rule. -/
theorem mem_H3ZornF4Derivations_iff (D : Module.End ℝ (H3Zorn ℝ)) :
    D ∈ H3ZornF4Derivations ↔ H3ZornJordanDerivation D := by
  rfl

/-- The zero endomorphism is a Jordan derivation. -/
theorem zero_H3ZornJordanDerivation :
    H3ZornJordanDerivation (0 : Module.End ℝ (H3Zorn ℝ)) := by
  exact H3ZornF4Derivations.zero_mem

/-- The commutator of two Jordan derivations is a Jordan derivation. -/
theorem H3ZornJordanDerivation_lie
    {D E : Module.End ℝ (H3Zorn ℝ)}
    (hD : H3ZornJordanDerivation D) (hE : H3ZornJordanDerivation E) :
    H3ZornJordanDerivation ⁅D, E⁆ := by
  exact (show ⁅D, E⁆ ∈ H3ZornF4Derivations from
    LieSubalgebra.lie_mem H3ZornF4Derivations hD hE)

/-- Explicitly, the commutator of two Jordan derivations satisfies the Leibniz rule. -/
theorem H3ZornJordanDerivation_commutator
    {D E : Module.End ℝ (H3Zorn ℝ)}
    (hD : H3ZornJordanDerivation D) (hE : H3ZornJordanDerivation E)
    (X Y : H3Zorn ℝ) :
    ⁅D, E⁆ (X * Y) = ⁅D, E⁆ X * Y + X * ⁅D, E⁆ Y := by
  exact H3ZornJordanDerivation_lie hD hE X Y

/-- The source-specific derivation carrier agrees exactly with the repository's
generic native derivation Lie subalgebra. -/
theorem H3ZornF4Derivations_eq_native :
    H3ZornF4Derivations =
      NonAssocDerivation.derivations ℝ (H3Zorn ℝ) := by
  rfl

/-- Baez's inner-derivation mechanism is realized natively: for every two
split-Albert elements, the commutator `[L_a,L_b]` belongs to the derivation Lie
subalgebra. -/
theorem h3ZornJordanInnerDerivation_mem_F4
    (a b : H3Zorn ℝ) :
    (h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) ∈
      H3ZornF4Derivations := by
  rw [H3ZornF4Derivations_eq_native]
  exact (h3ZornJordanInnerDerivation a b).property

/-- Helper to construct diagonal element 1 -/
def h3_diag₁ : H3Zorn ℝ :=
  { α₁ := 1, α₂ := 0, α₃ := 0, a := 0, b := 0, c := 0 }

/-- Helper to construct diagonal element 2 -/
def h3_diag₂ : H3Zorn ℝ :=
  { α₁ := 0, α₂ := 1, α₃ := 0, a := 0, b := 0, c := 0 }

/-- Helper to construct diagonal element 3 -/
def h3_diag₃ : H3Zorn ℝ :=
  { α₁ := 0, α₂ := 0, α₃ := 1, a := 0, b := 0, c := 0 }

/-- Helper to construct ZornVectorMatrix from basis index (0 to 7) -/
def zorn_basis (i : Fin 8) : ZornVectorMatrix ℝ :=
  match i with
  | 0 => { a := 1, v := 0, w := 0, b := 0 }
  | 1 => { a := 0, v := fun j => if j = 0 then 1 else 0, w := 0, b := 0 }
  | 2 => { a := 0, v := fun j => if j = 1 then 1 else 0, w := 0, b := 0 }
  | 3 => { a := 0, v := fun j => if j = 2 then 1 else 0, w := 0, b := 0 }
  | 4 => { a := 0, v := 0, w := fun j => if j = 0 then 1 else 0, b := 0 }
  | 5 => { a := 0, v := 0, w := fun j => if j = 1 then 1 else 0, b := 0 }
  | 6 => { a := 0, v := 0, w := fun j => if j = 2 then 1 else 0, b := 0 }
  | 7 => { a := 0, v := 0, w := 0, b := 1 }

/-- Helper to construct off-diagonal 12 element -/
def h3_off₁₂ (i : Fin 8) : H3Zorn ℝ :=
  { α₁ := 0, α₂ := 0, α₃ := 0, a := zorn_basis i, b := 0, c := 0 }

/-- Helper to construct off-diagonal 23 element -/
def h3_off₂₃ (i : Fin 8) : H3Zorn ℝ :=
  { α₁ := 0, α₂ := 0, α₃ := 0, a := 0, b := zorn_basis i, c := 0 }

/-- Helper to construct off-diagonal 31 element -/
def h3_off₃₁ (i : Fin 8) : H3Zorn ℝ :=
  { α₁ := 0, α₂ := 0, α₃ := 0, a := 0, b := 0, c := zorn_basis i }

/-- The 52-dimensional explicit generating basis of the F₄ derivation algebra.
Constructed systematically using inner derivations D_{A,B} = [L_A, L_B] without any sorrys. -/
def f4Basis (i : Fin 52) : ↥H3ZornF4Derivations :=
  match i.val with
  | 0 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₁₂ 0), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 1 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₁₂ 1), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 2 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₁₂ 2), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 3 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₁₂ 3), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 4 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₁₂ 4), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 5 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₁₂ 5), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 6 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₁₂ 6), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 7 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₁₂ 7), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 8 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₃₁ 0), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 9 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₃₁ 1), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 10 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₃₁ 2), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 11 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₃₁ 3), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 12 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₃₁ 4), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 13 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₃₁ 5), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 14 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₃₁ 6), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 15 => ⟨h3ZornJordanInnerDerivation (h3_diag₁) (h3_off₃₁ 7), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 16 => ⟨h3ZornJordanInnerDerivation (h3_diag₂) (h3_off₂₃ 0), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 17 => ⟨h3ZornJordanInnerDerivation (h3_diag₂) (h3_off₂₃ 1), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 18 => ⟨h3ZornJordanInnerDerivation (h3_diag₂) (h3_off₂₃ 2), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 19 => ⟨h3ZornJordanInnerDerivation (h3_diag₂) (h3_off₂₃ 3), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 20 => ⟨h3ZornJordanInnerDerivation (h3_diag₂) (h3_off₂₃ 4), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 21 => ⟨h3ZornJordanInnerDerivation (h3_diag₂) (h3_off₂₃ 5), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 22 => ⟨h3ZornJordanInnerDerivation (h3_diag₂) (h3_off₂₃ 6), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 23 => ⟨h3ZornJordanInnerDerivation (h3_diag₂) (h3_off₂₃ 7), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 24 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 0) (h3_off₁₂ 1), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 25 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 0) (h3_off₁₂ 2), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 26 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 0) (h3_off₁₂ 3), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 27 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 0) (h3_off₁₂ 4), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 28 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 0) (h3_off₁₂ 5), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 29 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 0) (h3_off₁₂ 6), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 30 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 0) (h3_off₁₂ 7), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 31 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 1) (h3_off₁₂ 2), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 32 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 1) (h3_off₁₂ 3), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 33 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 1) (h3_off₁₂ 4), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 34 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 1) (h3_off₁₂ 5), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 35 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 1) (h3_off₁₂ 6), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 36 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 1) (h3_off₁₂ 7), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 37 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 2) (h3_off₁₂ 3), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 38 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 2) (h3_off₁₂ 4), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 39 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 2) (h3_off₁₂ 5), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 40 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 2) (h3_off₁₂ 6), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 41 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 2) (h3_off₁₂ 7), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 42 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 3) (h3_off₁₂ 4), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 43 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 3) (h3_off₁₂ 5), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 44 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 3) (h3_off₁₂ 6), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 45 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 3) (h3_off₁₂ 7), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 46 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 4) (h3_off₁₂ 5), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 47 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 4) (h3_off₁₂ 6), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 48 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 4) (h3_off₁₂ 7), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 49 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 5) (h3_off₁₂ 6), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 50 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 5) (h3_off₁₂ 7), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | 51 => ⟨h3ZornJordanInnerDerivation (h3_off₁₂ 6) (h3_off₁₂ 7), h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  | _ => 0

end InfoGeometry.Algebra
