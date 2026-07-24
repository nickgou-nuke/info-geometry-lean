import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Explicit-Half Hodge-Krein Tri-Facet Decomposition

This file formalizes the explicit-half version of the Hodge-Krein tri-facet
projector algebra. Given a linear operator `O` satisfying the cubic law
`O^3 = O` and a scalar `half` satisfying `half + half = 1`, it constructs the
exact, coexact, harmonic, compact-core, and nilpotent-boundary components and
proves their decomposition, idempotence, and mutual annihilation identities.

The file proves the finite algebraic content only. It does not construct a
geometric Hodge Laplacian, differential forms, Krein signatures, or analytic
Hodge representatives.

## Audit Protocol Map
- BUCKET 1: CLOSED FINITE THEOREMS:
  `half_smul_add_self`, `half_smul_sub_neg_self`,
  `half_smul_add_sub_eq_left`, `P_ext_add_P_coext`,
  `tri_facet_sum`, `P_harm_idempotent`, `O_O_P_ext`, `O_P_ext`,
  `O_O_P_coext`, `O_P_coext`, `P_ext_idempotent`,
  `P_coext_idempotent`, `P_harm_P_ext`, `P_harm_P_coext`,
  `P_ext_P_coext`, `P_coext_P_ext`, `O_P_harm`, `O_O_P_harm`,
  `P_ext_P_harm`, `P_coext_P_harm`, `P_core_eq_ext_add_coext`,
  `P_core_add_P_harm`, `P_core_add_P_nil`, `P_core_P_nil`,
  `P_nil_P_core`, `range_eq_ker_sub_id`, `tri_facet_decomposition_equiv`.
- BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES:
  The projector identities are conditional on `half + half = 1` and, where
  needed, the cubic operator law `∀ x, O (O (O x)) = O x`.
- BUCKET 3: OPEN CLOSURE DEBT:
  No geometric or analytic Hodge theorem is asserted in this finite algebraic
  owner.
-/

namespace InfoGeometry.Canonical.HodgeKreinTriFacet

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Exact-sector projector: `P_ext = half * (O^2 + O)`. -/
def P_ext (O : V →ₗ[ℝ] V) (half : ℝ) : V →ₗ[ℝ] V :=
  half • (O.comp O + O)

/-- Coexact-sector projector: `P_coext = half * (O^2 - O)`. -/
def P_coext (O : V →ₗ[ℝ] V) (half : ℝ) : V →ₗ[ℝ] V :=
  half • (O.comp O - O)

/-- Harmonic-sector projector: `P_harm = I - O^2`. -/
def P_harm (O : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  LinearMap.id - O.comp O

/-- Compact-core projector: `P_core = O^2`. -/
def P_core (O : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  O.comp O

/-- Nilpotent-boundary projector: `P_nil = I - O^2`. -/
def P_nil (O : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  LinearMap.id - O.comp O

/-- Scalar half of a doubled vector is the vector. -/
theorem half_smul_add_self (half : ℝ) (h_half : half + half = 1) (x : V) :
    half • (x + x) = x := by
  rw [smul_add, ← add_smul, h_half, one_smul]

/-- Scalar half of `x - (-x)` is the vector. -/
theorem half_smul_sub_neg_self (half : ℝ) (h_half : half + half = 1) (x : V) :
    half • (x - -x) = x := by
  have h : x - -x = x + x := by abel
  rw [h]
  exact half_smul_add_self half h_half x

/-- The two half-scaled `a ± b` components recover `a`. -/
theorem half_smul_add_sub_eq_left
    (half : ℝ)
    (h_half : half + half = 1)
    (a b : V) :
    half • (a + b) + half • (a - b) = a := by
  rw [smul_add, smul_sub]
  have h : half • a + half • b + (half • a - half • b) = half • a + half • a := by
    abel
  rw [h, ← add_smul, h_half, one_smul]

/-- Exact plus coexact equals the compact core `O^2`. -/
theorem P_ext_add_P_coext
    (O : V →ₗ[ℝ] V)
    (half : ℝ)
    (h_half : half + half = 1)
    (x : V) :
    P_ext O half x + P_coext O half x = O (O x) := by
  unfold P_ext P_coext
  dsimp
  exact half_smul_add_sub_eq_left half h_half (O (O x)) (O x)

/-- The tri-facet components sum to the original vector. -/
theorem tri_facet_sum
    (O : V →ₗ[ℝ] V)
    (half : ℝ)
    (h_half : half + half = 1)
    (x : V) :
    P_ext O half x + P_coext O half x + P_harm O x = x := by
  rw [P_ext_add_P_coext O half h_half x]
  unfold P_harm
  dsimp
  abel

/-- The exact projector is fixed by `O^2`. -/
theorem O_O_P_ext
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (half : ℝ)
    (x : V) :
    O (O (P_ext O half x)) = P_ext O half x := by
  unfold P_ext
  dsimp
  rw [map_smul, map_smul, map_add, map_add]
  rw [hO3 (O x), hO3 x]

/-- The exact projector is fixed by `O`. -/
theorem O_P_ext
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (half : ℝ)
    (x : V) :
    O (P_ext O half x) = P_ext O half x := by
  unfold P_ext
  dsimp
  rw [map_smul, map_add, hO3 x, add_comm]

/-- The coexact projector is fixed by `O^2`. -/
theorem O_O_P_coext
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (half : ℝ)
    (x : V) :
    O (O (P_coext O half x)) = P_coext O half x := by
  unfold P_coext
  dsimp
  rw [map_smul, map_smul, map_sub, map_sub]
  rw [hO3 (O x), hO3 x]

/-- The coexact projector lies in the `-1` eigensector of `O`. -/
theorem O_P_coext
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (half : ℝ)
    (x : V) :
    O (P_coext O half x) = -P_coext O half x := by
  unfold P_coext
  dsimp
  rw [map_smul, map_sub, hO3 x]
  have h : O x - O (O x) = -(O (O x) - O x) := by abel
  rw [h, smul_neg]

/-- The harmonic projector is annihilated by `O`. -/
theorem O_P_harm
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    O (P_harm O x) = 0 := by
  unfold P_harm
  dsimp
  rw [map_sub, hO3 x]
  abel

/-- The harmonic projector is annihilated by `O^2`. -/
theorem O_O_P_harm
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    O (O (P_harm O x)) = 0 := by
  rw [O_P_harm O hO3 x, map_zero]

/-- The harmonic projector is idempotent. -/
theorem P_harm_idempotent
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_harm O (P_harm O x) = P_harm O x := by
  change P_harm O x - O (O (P_harm O x)) = P_harm O x
  rw [O_O_P_harm O hO3 x]
  abel

/-- The exact projector is idempotent. -/
theorem P_ext_idempotent
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (half : ℝ)
    (h_half : half + half = 1)
    (x : V) :
    P_ext O half (P_ext O half x) = P_ext O half x := by
  change half •
      (O (O (P_ext O half x)) + O (P_ext O half x)) = P_ext O half x
  rw [O_O_P_ext O hO3 half x, O_P_ext O hO3 half x]
  exact half_smul_add_self half h_half (P_ext O half x)

/-- The coexact projector is idempotent. -/
theorem P_coext_idempotent
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (half : ℝ)
    (h_half : half + half = 1)
    (x : V) :
    P_coext O half (P_coext O half x) = P_coext O half x := by
  change half •
      (O (O (P_coext O half x)) - O (P_coext O half x)) = P_coext O half x
  rw [O_O_P_coext O hO3 half x, O_P_coext O hO3 half x]
  exact half_smul_sub_neg_self half h_half (P_coext O half x)

/-- The harmonic projector annihilates the exact sector. -/
theorem P_harm_P_ext
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (half : ℝ)
    (x : V) :
    P_harm O (P_ext O half x) = 0 := by
  unfold P_harm
  dsimp
  rw [O_O_P_ext O hO3 half x, sub_self]

/-- The harmonic projector annihilates the coexact sector. -/
theorem P_harm_P_coext
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (half : ℝ)
    (x : V) :
    P_harm O (P_coext O half x) = 0 := by
  unfold P_harm
  dsimp
  rw [O_O_P_coext O hO3 half x, sub_self]

/-- The exact projector annihilates the coexact sector. -/
theorem P_ext_P_coext
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (half : ℝ)
    (x : V) :
    P_ext O half (P_coext O half x) = 0 := by
  unfold P_ext
  dsimp
  rw [O_O_P_coext O hO3 half x, O_P_coext O hO3 half x]
  rw [add_neg_cancel, smul_zero]

/-- The coexact projector annihilates the exact sector. -/
theorem P_coext_P_ext
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (half : ℝ)
    (x : V) :
    P_coext O half (P_ext O half x) = 0 := by
  unfold P_coext
  dsimp
  rw [O_O_P_ext O hO3 half x, O_P_ext O hO3 half x]
  rw [sub_self, smul_zero]

/-- The exact projector annihilates the harmonic sector. -/
theorem P_ext_P_harm
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (half : ℝ)
    (x : V) :
    P_ext O half (P_harm O x) = 0 := by
  unfold P_ext
  dsimp
  rw [O_O_P_harm O hO3 x, O_P_harm O hO3 x]
  simp

/-- The coexact projector annihilates the harmonic sector. -/
theorem P_coext_P_harm
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (half : ℝ)
    (x : V) :
    P_coext O half (P_harm O x) = 0 := by
  unfold P_coext
  dsimp
  rw [O_O_P_harm O hO3 x, O_P_harm O hO3 x]
  simp

/-- The compact core is the exact plus coexact sector. -/
theorem P_core_eq_ext_add_coext
    (O : V →ₗ[ℝ] V)
    (half : ℝ)
    (h_half : half + half = 1)
    (x : V) :
    P_core O x = P_ext O half x + P_coext O half x := by
  rw [P_ext_add_P_coext O half h_half x]
  rfl

/-- The compact core and harmonic boundary partition the vector. -/
theorem P_core_add_P_harm (O : V →ₗ[ℝ] V) (x : V) :
    P_core O x + P_harm O x = x := by
  unfold P_core P_harm
  dsimp
  abel

/-- The compact core and nilpotent boundary partition the vector. -/
theorem P_core_add_P_nil (O : V →ₗ[ℝ] V) (x : V) :
    P_core O x + P_nil O x = x := by
  unfold P_core P_nil
  dsimp
  abel

/-- The compact core annihilates the nilpotent boundary. -/
theorem P_core_P_nil
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_core O (P_nil O x) = 0 := by
  unfold P_core P_nil
  dsimp
  rw [map_sub, hO3 x]
  rw [sub_self, map_zero]

/-- The nilpotent boundary annihilates the compact core. -/
theorem P_nil_P_core
    (O : V →ₗ[ℝ] V)
    (hO3 : ∀ x : V, O (O (O x)) = O x)
    (x : V) :
    P_nil O (P_core O x) = 0 := by
  unfold P_nil P_core
  dsimp
  rw [hO3 (O x)]
  abel

/-- Range of an idempotent operator is the kernel of (I - P). -/
theorem range_eq_ker_sub_id {P : V →ₗ[ℝ] V} (hP : P.comp P = P) :
    LinearMap.range P = LinearMap.ker (LinearMap.id - P) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, rfl⟩
    have h1 : P (P y) = P y := by
      have h_comp : (P.comp P) y = P y := by rw [hP]
      exact h_comp
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact h1.symm
  · intro hx
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx
    exact ⟨x, hx.symm⟩

/-- Linear equivalence for the tri-facet direct sum decomposition. -/
def tri_facet_decomposition_equiv
    (O : V →ₗ[ℝ] V) (hO3 : ∀ x : V, O (O (O x)) = O x)
    (half : ℝ) (h_half : half + half = 1) :
    V ≃ₗ[ℝ] (LinearMap.range (P_ext O half) × LinearMap.range (P_coext O half) × LinearMap.range (P_harm O)) where
  toFun x := ⟨⟨P_ext O half x, ⟨x, rfl⟩⟩, ⟨P_coext O half x, ⟨x, rfl⟩⟩, ⟨P_harm O x, ⟨x, rfl⟩⟩⟩
  map_add' x y := by
    ext <;> simp [map_add]
  map_smul' c x := by
    ext <;> simp [map_smul]
  invFun p := p.1.1 + p.2.1 + p.2.2.1
  left_inv x := by
    dsimp
    exact tri_facet_sum O half h_half x
  right_inv p := by
    rcases p with ⟨⟨u1, ⟨x1, rfl⟩⟩, ⟨u2, ⟨x2, rfl⟩⟩, ⟨u3, ⟨x3, rfl⟩⟩⟩
    dsimp
    -- We need to prove that applying the projectors to u1 + u2 + u3 recovers u1, u2, u3 respectively.
    -- First, since u1 = P_ext O half x1, and P_ext is idempotent:
    have hu1 : P_ext O half (P_ext O half x1) = P_ext O half x1 := P_ext_idempotent O hO3 half h_half x1
    -- Similarly for u2, u3:
    have hu2 : P_coext O half (P_coext O half x2) = P_coext O half x2 := P_coext_idempotent O hO3 half h_half x2
    have hu3 : P_harm O (P_harm O x3) = P_harm O x3 := P_harm_idempotent O hO3 x3
    -- And we have pairwise annihilation:
    have h12 : P_ext O half (P_coext O half x2) = 0 := P_ext_P_coext O hO3 half x2
    have h13 : P_ext O half (P_harm O x3) = 0 := P_ext_P_harm O hO3 half x3
    have h21 : P_coext O half (P_ext O half x1) = 0 := P_coext_P_ext O hO3 half x1
    have h23 : P_coext O half (P_harm O x3) = 0 := P_coext_P_harm O hO3 half x3
    have h31 : P_harm O (P_ext O half x1) = 0 := P_harm_P_ext O hO3 half x1
    have h32 : P_harm O (P_coext O half x2) = 0 := P_harm_P_coext O hO3 half x2
    ext
    · simp [map_add, hu1, h12, h13]
    · simp [map_add, hu2, h21, h23]
    · simp [map_add, hu3, h31, h32]

end InfoGeometry.Canonical.HodgeKreinTriFacet
