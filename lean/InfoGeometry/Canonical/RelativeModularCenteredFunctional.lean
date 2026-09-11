import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorModularScoreFunctional

/-!
# InfoGeometry.Canonical.RelativeModularCenteredFunctional

Local-to-inductive modular-centered functional primitives.

This file records the finite-local algebraic shape used by the Cantor/Clifford
workflows:

- a reference linear functional `ref`,
- a density element `Δ`,
- the induced state `state a = ref (Δ * a)`,
- and the centered functional `state - ref = a ↦ ref ((Δ - 1) * a)`
  with `η(1) = 0`.
-/

namespace InfoGeometry.Canonical.RelativeModularCenteredFunctional

noncomputable section

open scoped BigOperators
open Finset
open CantorCylinderLattice
open CantorModularScoreFunctional
section FiniteLocal

variable {A : Type*} [Ring A] [Algebra ℝ A]

/--
A finite-local density-state pair, where `state` is represented via left
multiplication by `density` against a reference linear functional.
-/
structure LocalDensityState where
  ref : A →ₗ[ℝ] ℝ
  density : A
  state : A →ₗ[ℝ] ℝ
  state_eq : ∀ a, state a = ref (density * a)
  norm_ref : ref 1 = 1
  norm_state : state 1 = 1

/-- Centered density (shifted by the unit). -/
def centeredDensity (S : LocalDensityState (A := A)) : A :=
  S.density - 1

/-- Centered functional `η = state - ref`. -/
def centeredFunctional (S : LocalDensityState (A := A)) : A →ₗ[ℝ] ℝ :=
  S.state - S.ref

/-- `η(a)=ref((Δ-1)a)` for all local observables `a`. -/
theorem centeredFunctional_eq_delta_minus_one
    (S : LocalDensityState (A := A)) (a : A) :
    centeredFunctional (A := A) S a = S.ref ((centeredDensity (A := A) S) * a) := by
  calc
    (S.state - S.ref) a = S.state a - S.ref a := rfl
    _ = S.ref (S.density * a) - S.ref a := by simp [S.state_eq]
    _ = S.ref (S.density * a - 1 * a) := by
          rw [← S.ref.map_sub]
          simp
    _ = S.ref ((S.density - 1) * a) := by
          simp [sub_mul]

/-- Centered functional vanishes on the unit: `η(1)=0`. -/
theorem centeredFunctional_one_eq_zero
    (S : LocalDensityState (A := A)) :
    centeredFunctional (A := A) S 1 = 0 := by
  simp [centeredFunctional, S.norm_state, S.norm_ref]

/--
Finite-level projective comparability for two local density states with respect to a
common reference functional.

This encodes the physically relevant finite-ratio relation `Δ₁ = c • Δ₂` while
keeping the absolute normalization out of the picture.
-/
def projectivelyComparable (S₁ S₂ : LocalDensityState (A := A)) : Prop :=
  ∃ c : ℝ, S₁.ref = S₂.ref ∧ S₁.density = c • S₂.density

/-- Projective comparability implies projective state ratio. -/
theorem projectivelyComparable_state_eq
    {S₁ S₂ : LocalDensityState (A := A)}
    (h : projectivelyComparable S₁ S₂) :
    ∃ c : ℝ, ∀ a : A, S₁.state a = c * S₂.state a := by
  rcases h with ⟨c, href, hρ⟩
  refine ⟨c, ?_⟩
  intro a
  rw [S₁.state_eq, S₂.state_eq, hρ, href]
  simp

end FiniteLocal

/--
Compatible local linear-state net over an increasing local algebra tower.
-/
structure CompatibleLocalStateNet (A : ℕ → Type*) where
  ring_A : ∀ n, Ring (A n)
  algebra_A : ∀ n, Algebra ℝ (A n)
  state : ∀ n, A n →ₗ[ℝ] ℝ
  restrict : ∀ n, A (n + 1) →ₗ[ℝ] A n
  compatible : ∀ n (a : A (n + 1)), state (n + 1) a = state n ((restrict n) a)

/--
Compatible centered modular local net extending a reference/ density/centered
total system.
-/
structure CompatibleCenteredModularNet (A : ℕ → Type*) where
  ring_A : ∀ n, Ring (A n)
  algebra_A : ∀ n, Algebra ℝ (A n)
  state : ∀ n, A n →ₗ[ℝ] ℝ
  restrict : ∀ n, A (n + 1) →ₗ[ℝ] A n
  compatible : ∀ n (a : A (n + 1)), state (n + 1) a = state n ((restrict n) a)
  ref : ∀ n, A n →ₗ[ℝ] ℝ
  density : ∀ n, A n
  centered : ∀ n, A n →ₗ[ℝ] ℝ
  centered_eq : ∀ n a,
    letI := ring_A n
    letI := algebra_A n
    centered n a = ref n (((density n) - 1) * a)
  centered_one : ∀ n,
    letI := ring_A n
    letI := algebra_A n
    centered n 1 = 0

/--
If two local functionals are compatible under the same restriction map, then their
pointwise difference is compatible as well.
-/
theorem compatibleSub_of_compatible
    {A : ℕ → Type*}
    (state ref : ∀ n, A n → ℝ)
    (restrict : ∀ n, A (n + 1) → A n)
    (hstate : ∀ n (a : A (n + 1)), state (n + 1) a = state n (restrict n a))
    (href : ∀ n (a : A (n + 1)), ref (n + 1) a = ref n (restrict n a)) :
    ∀ n (a : A (n + 1)), (state (n + 1) a - ref (n + 1) a) =
      (state n (restrict n a) - ref n (restrict n a)) := by
  intro n a
  rw [hstate n a, href n a]

/--
Compatibility of centered differences for compatible linear functionals.
-/
theorem compatibleSub_of_compatibleLinear
    {A : ℕ → Type*} [∀ n, Ring (A n)] [∀ n, Algebra ℝ (A n)]
    (state ref : ∀ n, A n →ₗ[ℝ] ℝ)
    (restrict : ∀ n, A (n + 1) →ₗ[ℝ] A n)
    (hstate : ∀ n (a : A (n + 1)), state (n + 1) a = state n ((restrict n) a))
    (href : ∀ n (a : A (n + 1)), ref (n + 1) a = ref n ((restrict n) a)) :
    ∀ n (a : A (n + 1)), (state (n + 1) a - ref (n + 1) a) =
      (state n ((restrict n) a) - ref n ((restrict n) a)) := by
  intro n a
  rw [hstate n a, href n a]
section CantorLocalPath

/-- First `n` bits of an infinite binary string (as `Fin n → Bool`). -/
def cantorPrefixWord (x : ℕ → Bool) : ∀ n : ℕ, BinaryWord n
  | 0 => fun i => False.elim (Fin.elim0 i)
  | n + 1 => Fin.snoc (cantorPrefixWord x n) (x n)

@[simp] theorem cantorPrefixWord_zero (x : ℕ → Bool) :
    cantorPrefixWord (x := x) 0 = (fun i => False.elim (Fin.elim0 i)) := rfl

@[simp] theorem cantorPrefixWord_succ (x : ℕ → Bool) (n : ℕ) :
    cantorPrefixWord (x := x) (n + 1) = Fin.snoc (cantorPrefixWord (x := x) n) (x n) := by
  rfl

/-- Uniform Bernoulli reference functional on level-`n` observables. -/
def cantorRefFunctional (n : ℕ) : (BinaryWord n → ℝ) →ₗ[ℝ] ℝ where
  toFun f := uniformMean (n := n) f
  map_add' _ _ := by
    simp [uniformMean, mul_add, Finset.sum_add_distrib]
  map_smul' _ _ := by
    simp [uniformMean, mul_sum, mul_assoc, mul_comm]

/-- Point density of a fixed infinite word at level `n`: `Δ_{x,n}`. -/
def cantorPointDensity (x : ℕ → Bool) (n : ℕ) : BinaryWord n → ℝ :=
  fun w => if w = cantorPrefixWord (x := x) n then (Fintype.card (BinaryWord n) : ℝ) else 0

/-- `cantorPointDensity` is the same point spike used by the finite-score API. -/
theorem cantorPointDensity_eq_pointDensity
    (x : ℕ → Bool) (n : ℕ) :
    cantorPointDensity (x := x) n =
      pointDensity (cantorPrefixWord (x := x) n) := by
  funext w
  simp [cantorPointDensity, pointDensity]

/-- Spikes for distinct prefixes are not scalar-identical unless the prefixes agree. -/
theorem cantorPointDensity_smul_eq_prefix_eq
    (x y : ℕ → Bool) (n : ℕ) {c : ℝ}
    (h : cantorPointDensity (x := x) n = c • cantorPointDensity (x := y) n) :
    cantorPrefixWord (x := x) n = cantorPrefixWord (x := y) n := by
  have hcard : (Fintype.card (BinaryWord n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := BinaryWord n)
  have hEval :
      (cantorPointDensity (x := x) n) (cantorPrefixWord (x := x) n)
        = c * (cantorPointDensity (x := y) n) (cantorPrefixWord (x := x) n) := by
    exact congrArg (fun f => f (cantorPrefixWord (x := x) n)) h
  have hEq :
      (Fintype.card (BinaryWord n) : ℝ)
        = c * (if cantorPrefixWord (x := x) n = cantorPrefixWord (x := y) n
            then (Fintype.card (BinaryWord n) : ℝ)
            else 0) := by
    simpa [cantorPointDensity] using hEval
  by_cases hxy : cantorPrefixWord (x := x) n = cantorPrefixWord (x := y) n
  · exact hxy
  · exfalso
    have hzero : (Fintype.card (BinaryWord n) : ℝ) = 0 := by
      simpa [hxy, mul_zero] using hEq
    exact hcard hzero
/-- Point state on level `n`: `φ_n(f)=f(x[:n])`. -/
def cantorPointState (x : ℕ → Bool) (n : ℕ) :
    (BinaryWord n → ℝ) →ₗ[ℝ] ℝ where
  toFun f := f (cantorPrefixWord (x := x) n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Point state is obtained from `ref` by left-multiplying by `Δ_{x,n}`. -/
theorem cantorPointState_state_eq_ref
    (x : ℕ → Bool) (n : ℕ) (a : BinaryWord n → ℝ) :
    cantorPointState (x := x) n a =
      cantorRefFunctional (n := n) (cantorPointDensity (x := x) n * a) := by
  change a (cantorPrefixWord (x := x) n) = cantorRefFunctional (n := n) (cantorPointDensity (x := x) n * a)
  let cardN : ℝ := (Fintype.card (BinaryWord n) : ℝ)
  have hcard : cardN ≠ 0 := by
    dsimp [cardN]
    exact_mod_cast (Fintype.card_ne_zero (α := BinaryWord n))
  have hsum_univ :
      (∑ i ∈ (Finset.univ : Finset (BinaryWord n)),
          (if i = cantorPrefixWord (x := x) n then cardN else 0) * a i) =
        (if cantorPrefixWord (x := x) n = cantorPrefixWord (x := x) n then cardN else 0) *
          a (cantorPrefixWord (x := x) n) := by
    classical
    refine Finset.sum_eq_single (a := cantorPrefixWord (x := x) n)
      (s := (Finset.univ : Finset (BinaryWord n)) )
      (f := fun i : BinaryWord n => (if i = cantorPrefixWord (x := x) n then cardN else 0) * a i) ?_ ?_
    · intro i hi hne
      simp [cardN, hne]
    · intro hnotmem
      simp at hnotmem
    
  have hsum :
      (∑ i : BinaryWord n,
          (if i = cantorPrefixWord (x := x) n then cardN else 0) * a i) =
        cardN * a (cantorPrefixWord (x := x) n) := by
    simpa [Finset.mem_univ, if_pos rfl, cardN] using hsum_univ
  calc
    a (cantorPrefixWord (x := x) n)
        = (cardN⁻¹ * cardN) * a (cantorPrefixWord (x := x) n) := by
            rw [inv_mul_cancel₀ hcard, one_mul]
    _ = cardN⁻¹ * (cardN * a (cantorPrefixWord (x := x) n)) := by
            ring
    _ = cardN⁻¹ * ∑ i : BinaryWord n,
            (if i = cantorPrefixWord (x := x) n then cardN else 0) * a i := by
          rw [hsum]
    _ = cantorRefFunctional (n := n) (cantorPointDensity (x := x) n * a) := by
          rfl

/-- `Δ_{x,n}` is normalized so that `ref` is a state and `state` is normalized. -/
lemma cantorRefFunctional_one (n : ℕ) :
    cantorRefFunctional (n := n) (1 : BinaryWord n → ℝ) = 1 := by
  unfold cantorRefFunctional
  have hcard : (Fintype.card (BinaryWord n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := BinaryWord n)
  have hsum : (∑ i : BinaryWord n, (1 : ℝ)) = (Fintype.card (BinaryWord n) : ℝ) := by
    simp
  calc
    (Fintype.card (BinaryWord n) : ℝ)⁻¹ * (∑ i : BinaryWord n, (1 : ℝ))
        = (Fintype.card (BinaryWord n) : ℝ)⁻¹ * (Fintype.card (BinaryWord n) : ℝ) := by simpa [hsum]
    _ = 1 := by
      have hmul : (Fintype.card (BinaryWord n) : ℝ)⁻¹ * (Fintype.card (BinaryWord n) : ℝ) = 1 := by
        exact inv_mul_cancel₀ hcard
      simpa using hmul

/-- Local state package at level `n` for a fixed boundary word. -/
def cantorPathLocalDensityState (x : ℕ → Bool) (n : ℕ) :
    LocalDensityState (A := BinaryWord n → ℝ) :=
  { ref := cantorRefFunctional (n := n)
    density := cantorPointDensity (x := x) n
    state := cantorPointState (x := x) n
    state_eq := by
      intro a
      simpa [cantorPointDensity] using (cantorPointState_state_eq_ref (x := x) n a)
    norm_ref := by
      simpa using (cantorRefFunctional_one (n := n))
    norm_state := by
      rfl }

/-- The local density state is projectively comparable to itself (ratio `1`). -/
theorem cantorPathLocalDensityState_projectivelyComparable_self
    (x : ℕ → Bool) (n : ℕ) :
    projectivelyComparable (A := BinaryWord n → ℝ)
      (cantorPathLocalDensityState (x := x) n)
      (cantorPathLocalDensityState (x := x) n) := by
  refine ⟨(1 : ℝ), rfl, ?_⟩
  simp

/-- Projective comparability between two point-branch local states fixes the finite
prefix word at that level. -/
theorem cantorPathLocalDensityState_projectivelyComparable_prefix_eq
    (x y : ℕ → Bool) (n : ℕ)
    (h : projectivelyComparable (A := BinaryWord n → ℝ)
      (cantorPathLocalDensityState (x := x) n)
      (cantorPathLocalDensityState (x := y) n)) :
    cantorPrefixWord (x := x) n = cantorPrefixWord (x := y) n := by
  rcases h with ⟨c, href, hρ⟩
  exact cantorPointDensity_smul_eq_prefix_eq (x := x) (y := y) (n := n) (c := c) hρ

/-- Restrict level-`n+1` observables to level `n` along a fixed word branch. -/
def cantorPathRestrict (x : ℕ → Bool) (n : ℕ) :
    (BinaryWord (n + 1) → ℝ) → (BinaryWord n → ℝ) :=
  fun f w => f (Fin.snoc w (x n))

/-- Linear version of the branch restriction. -/
def cantorPathRestrictLinear (x : ℕ → Bool) (n : ℕ) :
    (BinaryWord (n + 1) → ℝ) →ₗ[ℝ] (BinaryWord n → ℝ) where
  toFun := cantorPathRestrict (x := x) n
  map_add' := by
    intro a b
    rfl
  map_smul' := by
    intro c a
    rfl

/-- Compatibility witness for the fixed-word local state family. -/
theorem cantorPathStateCompatible (x : ℕ → Bool) (n : ℕ)
    (a : BinaryWord (n + 1) → ℝ) :
    cantorPointState (x := x) (n + 1) a =
      cantorPointState (x := x) n (cantorPathRestrict (x := x) n a) := by
  simp [cantorPointState, cantorPathRestrict, cantorPrefixWord_succ]

/-- Linearized compatibility witness for the restricted observables. -/
theorem cantorPathStateCompatibleLinear (x : ℕ → Bool) (n : ℕ)
    (a : BinaryWord (n + 1) → ℝ) :
    cantorPointState (x := x) (n + 1) a =
      cantorPointState (x := x) n ((cantorPathRestrictLinear (x := x) n) a) := by
  simp [cantorPathRestrictLinear, cantorPathRestrict, cantorPointState, cantorPrefixWord_succ]

/-- Centered functional identity on each level: `η_n(f)=f(x_n)-μ_n(f)`. -/
theorem cantorPathCentered_eq_eval_sub_uniform
    (x : ℕ → Bool) (n : ℕ) (a : BinaryWord n → ℝ) :
    centeredFunctional (A := BinaryWord n → ℝ) (cantorPathLocalDensityState (x := x) n) a =
      a (cantorPrefixWord (x := x) n) - uniformMean (n := n) a := by
  let S := cantorPathLocalDensityState (x := x) n
  calc
    centeredFunctional (A := BinaryWord n → ℝ) S a
        = S.ref ((S.density - 1) * a) := by
            simpa [S, centeredFunctional_eq_delta_minus_one, centeredDensity]
    _ = S.ref (S.density * a - 1 * a) := by
            simp [sub_mul]
    _ = S.ref (S.density * a) - S.ref (1 * a) := by
            rw [S.ref.map_sub]
    _ = S.state a - uniformMean (n := n) a := by
            have hstate : S.state a = S.ref (S.density * a) := by
              simpa [S] using (S.state_eq a)
            have href : S.ref (1 * a) = uniformMean (n := n) a := by
              change cantorRefFunctional (n := n) (1 * a) = uniformMean (n := n) a
              simp [cantorRefFunctional, one_mul]
            rw [hstate, href]
    _ = a (cantorPrefixWord (x := x) n) - uniformMean (n := n) a := by
            have hstateEval : S.state a = a (cantorPrefixWord (x := x) n) := by
              rfl
            rw [hstateEval]
/-- Rewriting the centered functional as the preexisting finite Cantor score. -/
theorem cantorPathCentered_eq_scoreAt
    (x : ℕ → Bool) (n : ℕ) (a : BinaryWord n → ℝ) :
    centeredFunctional (A := BinaryWord n → ℝ) (cantorPathLocalDensityState (x := x) n) a =
      scoreAt (cantorPrefixWord (x := x) n) a := by
  simpa [scoreAt] using
    (cantorPathCentered_eq_eval_sub_uniform (x := x) (n := n) (a := a))

/-- Rewriting the centered functional as the finite centered-score functional in
`Δ-1` form. -/
theorem cantorPathCentered_eq_scoreAt_delta_sub_one
    (x : ℕ → Bool) (n : ℕ) (a : BinaryWord n → ℝ) :
    centeredFunctional (A := BinaryWord n → ℝ) (cantorPathLocalDensityState (x := x) n) a =
      uniformMean (n := n)
        (fun v => (cantorPointDensity (x := x) n v - 1) * a v) := by
  rw [cantorPathCentered_eq_scoreAt (x := x) (n := n) (a := a)]
  rw [scoreAt_eq_uniformMean_delta_sub_one]
  have hpd := cantorPointDensity_eq_pointDensity (x := x) (n := n)
  simpa [hpd]

/-- Finite-path-compatible centered net for the fixed infinite binary word `x`. -/
def cantorPathCenteredNet (x : ℕ → Bool) :
    CompatibleCenteredModularNet (fun n => BinaryWord n → ℝ) where
  ring_A := fun n => by
    infer_instance
  algebra_A := fun n => by
    infer_instance
  state := fun n => cantorPointState (x := x) n
  restrict := cantorPathRestrictLinear (x := x)
  compatible := cantorPathStateCompatibleLinear (x := x)
  ref := fun n => cantorRefFunctional (n := n)
  density := fun n => cantorPointDensity (x := x) n
  centered := fun n => centeredFunctional (A := BinaryWord n → ℝ) (cantorPathLocalDensityState (x := x) n)
  centered_eq := by
    intro n a
    let S := cantorPathLocalDensityState (x := x) n
    simpa [S, centeredDensity] using
      (centeredFunctional_eq_delta_minus_one (A := BinaryWord n → ℝ) S a)
  centered_one := by
    intro n
    let S := cantorPathLocalDensityState (x := x) n
    simpa [S, centeredDensity] using
      (centeredFunctional_one_eq_zero (A := BinaryWord n → ℝ) S)

/-- Signed local displacement at level `n` is exactly `state - reference`. -/
theorem cantorPathCentered_eq_state_sub_ref
    (x : ℕ → Bool) (n : ℕ) (a : BinaryWord n → ℝ) :
    ((cantorPathCenteredNet (x := x)).centered n) a =
      ((cantorPathCenteredNet (x := x)).state n) a -
      ((cantorPathCenteredNet (x := x)).ref n) a := by
  change centeredFunctional (A := BinaryWord n → ℝ) (cantorPathLocalDensityState (x := x) n) a =
    cantorPointState (x := x) n a - cantorRefFunctional (n := n) a
  simp [centeredFunctional, cantorPathLocalDensityState]

/-- Centered local score is normalized (`η_n(1)=0`). -/
theorem cantorPathCentered_one
    (x : ℕ → Bool) (n : ℕ) :
    ((cantorPathCenteredNet (x := x)).centered n) (1 : BinaryWord n → ℝ) = 0 := by
  simpa [cantorPathCenteredNet] using ((cantorPathCenteredNet (x := x)).centered_one n)

/-- Core displacement form: centered score equals the reference functional of `(Δ - 1) * a`. -/
theorem cantorPathCentered_eq_ref_delta_sub_one
    (x : ℕ → Bool) (n : ℕ) (a : BinaryWord n → ℝ) :
    ((cantorPathCenteredNet (x := x)).centered n) a =
      ((cantorPathCenteredNet (x := x)).ref n)
        (((cantorPathCenteredNet (x := x)).density n - 1) * a) := by
  change centeredFunctional (A := BinaryWord n → ℝ) (cantorPathLocalDensityState (x := x) n) a =
    cantorRefFunctional (n := n) ((cantorPointDensity (x := x) n - 1) * a)
  rw [centeredFunctional_eq_delta_minus_one]
  simp [cantorPathLocalDensityState, centeredDensity]
/-- Rewriting the centered functional as the preexisting finite Cantor score. -/
theorem cantorPathCenteredNet_centered_eq_scoreLinear
    (x : ℕ → Bool) (n : ℕ) (a : BinaryWord n → ℝ) :
    ((cantorPathCenteredNet (x := x)).centered n) a =
      scoreLinear (cantorPrefixWord (x := x) n) a := by
  change centeredFunctional (A := BinaryWord n → ℝ) (cantorPathLocalDensityState (x := x) n) a =
    scoreLinear (cantorPrefixWord (x := x) n) a
  rw [cantorPathCentered_eq_scoreAt (x := x) (n := n) (a := a)]
  rfl

end CantorLocalPath

/-!
Type-III perspective block (finite-level interface).

The global noncommutative construction is modeled here by an abstract local compatibility
scheme: a singular Dirac-type state and a reference state are represented only through
their compatible finite-level restrictions.
-/

section TypeIII_Delta_Interface

/--
Abstract finite-level data for a `Δ - 1` centered extension of a MASA Dirac point.
-/
structure CantorDiracTypeIIIData (r : ∀ n, (BinaryWord (n + 1) → ℝ) →ₗ[ℝ] (BinaryWord n → ℝ)) where
  omega : ∀ n, (BinaryWord n → ℝ) →ₗ[ℝ] ℝ
  phi : ∀ n, (BinaryWord n → ℝ) →ₗ[ℝ] ℝ
  eta : ∀ n, (BinaryWord n → ℝ) →ₗ[ℝ] ℝ
  omega_one : ∀ n, omega n (1 : BinaryWord n → ℝ) = 1
  phi_one : ∀ n, phi n (1 : BinaryWord n → ℝ) = 1
  omega_compatible : ∀ n (a : BinaryWord (n + 1) → ℝ),
    omega (n + 1) a = omega n ((r n) a)
  phi_compatible : ∀ n (a : BinaryWord (n + 1) → ℝ),
    phi (n + 1) a = phi n ((r n) a)
  eta_eq : ∀ n a,
    eta n a = phi n a - omega n a

/-- Centered displacement has vanishing mass in every finite level.
This is the finite echo of `η(1)=0`. -/
theorem cantorDiracTypeIII_eta_one
    {r : ∀ n, (BinaryWord (n + 1) → ℝ) →ₗ[ℝ] (BinaryWord n → ℝ)}
    (S : CantorDiracTypeIIIData r) :
    ∀ n, S.eta n (1 : BinaryWord n → ℝ) = 0 := by
  intro n
  rw [S.eta_eq]
  rw [S.phi_one, S.omega_one]
  ring

/-- If both the singular state and reference are compatible, the centered displacement is compatible.
This is the finite net form of weak-* compatibility of local `η_n = φ_n - ω_n`.
-/
theorem cantorDiracTypeIII_eta_compatible
    {r : ∀ n, (BinaryWord (n + 1) → ℝ) →ₗ[ℝ] (BinaryWord n → ℝ)}
    (S : CantorDiracTypeIIIData r) :
    ∀ n (a : BinaryWord (n + 1) → ℝ),
      S.eta (n + 1) a = S.eta n ((r n) a) := by
  intro n a
  rw [S.eta_eq, S.phi_compatible, S.omega_compatible, S.eta_eq]

end TypeIII_Delta_Interface

-- Mellin-transformed centered scores and the associated Green's-type spectral factor.
-- The finite local states are still projective objects; here we attach a discrete
-- Mellin kernel along the Cantor branching scale and record the induced complexified
-- Green's response to the centered score functional.

/-- Base scaling kernel for the Cantor branching scale (`2`). -/
def cantorMellinKernel (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (1 - s)

/-- Hestenes-style phase axis used by the Cantor Mellin lattice in this file.

    In this development, `Complex.I` plays the bivector/phase-operator role of
    Hestenes geometricized complex analysis. This alias makes that convention
    explicit in Mellin formulas while staying Lean-compatible with the
    `Complex` API.
-/
def cantorPhaseAxis : ℂ := Complex.I

/-- Cantor spectral Dirichlet zeta factor `∑ (2^(1-s))^n`. -/
def cantorSpectralZeta (s : ℂ) : ℂ :=
  ∑' n : ℕ, (cantorMellinKernel s) ^ n

/-- Geometric closed form on the unit-disc region for the kernel. -/
theorem cantorSpectralZeta_eq (s : ℂ) (h : ‖cantorMellinKernel s‖ < 1) :
    cantorSpectralZeta s = (1 : ℂ) / (1 - cantorMellinKernel s) := by
  simpa [one_div] using
    (tsum_geometric_of_norm_lt_one h : (∑' n : ℕ, (cantorMellinKernel s) ^ n) = (1 - cantorMellinKernel s)⁻¹)

/-- Pole-locus of the Cantor Mellin kernel.

`cantorMellinKernel s = 1` iff `s` lies on the period lattice
`1 - n·2πi / log 2`, `n : ℤ`.
-/
theorem cantorMellinKernel_eq_one_iff
    (s : ℂ) :
    cantorMellinKernel s = 1 ↔
      ∃ n : ℤ, s = 1 - (n : ℂ) * (2 * (Real.pi : ℂ) * cantorPhaseAxis) / Complex.log (2 : ℂ) := by
  constructor
  · intro h
    rw [cantorMellinKernel, Complex.cpow_def_of_ne_zero (by norm_num)] at h
    rcases Complex.exp_eq_one_iff.mp h with ⟨n, hn⟩
    have hlog2_ne : (Complex.log (2 : ℂ)) ≠ 0 := by
      simpa [Complex.ofReal_log (show (0:ℝ) ≤ 2 by norm_num)] using
        (show (Real.log 2 : ℂ) ≠ 0 from by
          exact_mod_cast Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num))
    have hs : 1 - s = (n : ℂ) * (2 * (Real.pi : ℂ) * cantorPhaseAxis) / Complex.log (2 : ℂ) := by
      refine (eq_div_iff hlog2_ne).2 ?_
      simpa [mul_assoc, mul_left_comm, mul_comm] using hn
    refine ⟨n, ?_⟩
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - ((n : ℂ) * (2 * (Real.pi : ℂ) * cantorPhaseAxis) / Complex.log (2 : ℂ)) := by
        rw [hs]

  · rintro ⟨n, rfl⟩
    rw [cantorMellinKernel, Complex.cpow_def_of_ne_zero (by norm_num)]
    have hlog2_ne : (Complex.log (2 : ℂ)) ≠ 0 := by
      simpa [Complex.ofReal_log (show (0:ℝ) ≤ 2 by norm_num)] using
        (show (Real.log 2 : ℂ) ≠ 0 from by
          exact_mod_cast Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num))
    have harg : Complex.log (2 : ℂ) * (1 - (1 - (n : ℂ) * (2 * (Real.pi : ℂ) * cantorPhaseAxis) / Complex.log (2 : ℂ)) ) =
        (n : ℂ) * (2 * (Real.pi : ℂ) * cantorPhaseAxis) := by
      have hphase : cantorPhaseAxis = Complex.I := rfl
      have hargI : Complex.log (2 : ℂ) *
          (1 - (1 - (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / Complex.log (2 : ℂ)) ) =
          (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        ring_nf
        field_simp [hlog2_ne]
      calc
        Complex.log (2 : ℂ) *
            (1 - (1 - (n : ℂ) * (2 * (Real.pi : ℂ) * cantorPhaseAxis) / Complex.log (2 : ℂ)) )
            = Complex.log (2 : ℂ) *
            (1 - (1 - (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / Complex.log (2 : ℂ)) ) := by
          simp [hphase]
        _ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hargI
        _ = (n : ℂ) * (2 * (Real.pi : ℂ) * cantorPhaseAxis) := by
          simp [hphase]
    rw [harg]
    have hphase : cantorPhaseAxis = Complex.I := rfl
    exact (Complex.exp_eq_one_iff.mpr ⟨n, by simpa [hphase, mul_assoc, mul_left_comm, mul_comm]⟩)

/-- Hestenes-form lattice characterization of the same pole locus. -/
theorem cantorMellinKernel_eq_one_iff_phaseAxis
    (s : ℂ) :
    cantorMellinKernel s = 1 ↔
      ∃ n : ℤ, s = 1 - (n : ℂ) * (2 * (Real.pi : ℂ) * cantorPhaseAxis) / Complex.log (2 : ℂ) := by
  simpa [cantorPhaseAxis] using cantorMellinKernel_eq_one_iff (s := s)

/-- Exact pole divisor of the Cantor Mellin denominator.
This is the finite-level pole condition `1 - 2^{1-s} = 0`.
-/
theorem cantorMellinDenominator_eq_zero_iff
    (s : ℂ) :
    1 - cantorMellinKernel s = 0 ↔
      ∃ n : ℤ, s = 1 - (n : ℂ) * (2 * (Real.pi : ℂ) * cantorPhaseAxis) / Complex.log (2 : ℂ) := by
  constructor
  · intro h
    have hker : cantorMellinKernel s = 1 := by
      exact (sub_eq_zero.mp h).symm
    exact (cantorMellinKernel_eq_one_iff (s := s)).1 hker
  · rintro ⟨n, hn⟩
    rw [hn]
    have hker : cantorMellinKernel (1 - (n : ℂ) * (2 * (Real.pi : ℂ) * cantorPhaseAxis) / Complex.log (2 : ℂ)) = 1 := by
      have hiff := cantorMellinKernel_eq_one_iff (s := 1 - (n : ℂ) * (2 * (Real.pi : ℂ) * cantorPhaseAxis) / Complex.log (2 : ℂ))
      exact hiff.2 ⟨n, by simp⟩
    simpa [hker]

/-- Reciprocal denominator form for the finite Cantor spectral sum in its convergence domain. -/
theorem cantorSpectralZeta_mul_one_sub_eq_one
    (s : ℂ) (h : ‖cantorMellinKernel s‖ < 1) :
    cantorSpectralZeta s * (1 - cantorMellinKernel s) = 1 := by
  have hne : cantorMellinKernel s ≠ 1 := by
    intro hk
    have hbad : (1 : ℝ) < 1 := by simpa [hk] using h
    have : ¬ (1 : ℝ) < 1 := by norm_num
    exact this hbad
  have hden : (1 - cantorMellinKernel s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  rw [cantorSpectralZeta_eq s h]
  field_simp [hden]

/-- Spectral Green factor is nonzero on the geometric convergence domain. -/
theorem cantorSpectralZeta_ne_zero_of_norm_lt_one
    (s : ℂ) (h : ‖cantorMellinKernel s‖ < 1) :
    cantorSpectralZeta s ≠ 0 := by
  intro hzero
  have hmul := cantorSpectralZeta_mul_one_sub_eq_one (s := s) h
  have hbad : (0 : ℂ) = 1 := by
    calc
      (0 : ℂ) = cantorSpectralZeta s * (1 - cantorMellinKernel s) := by simpa [hzero]
      _ = 1 := hmul
  exact zero_ne_one hbad

/-- Mellin-green transform of a local centered modular score.

This keeps the centered score as the source and scales it by the discrete
Cantor spectral factor.
-/
def localMellinGreen
    {A : Type*} [Ring A] [Algebra ℝ A]
    (S : LocalDensityState (A := A)) (s : ℂ) (a : A) : ℂ :=
  cantorSpectralZeta s * Complex.ofReal (centeredFunctional (A := A) S a)

/-- Centered source term for the local state is recovered from `localMellinGreen`. -/
theorem localMellinGreen_eq_centered
    {A : Type*} [Ring A] [Algebra ℝ A]
    (S : LocalDensityState (A := A)) (s : ℂ) (a : A) :
    localMellinGreen (A := A) S s a =
      cantorSpectralZeta s * Complex.ofReal (S.state a - S.ref a) := by
  simp [localMellinGreen, centeredFunctional]

/-- Levelwise local Mellin-green transform for the Cantor point-path state. -/
def cantorPathLocalMellinGreen
    (x : ℕ → Bool) (n : ℕ) (s : ℂ) (a : BinaryWord n → ℝ) : ℂ :=
  localMellinGreen (A := BinaryWord n → ℝ) (cantorPathLocalDensityState (x := x) n) s a

/-- Cantor path local Mellin-green transform as the finite centered score. -/
theorem cantorPathLocalMellinGreen_eq_scoreAt
    (x : ℕ → Bool) (n : ℕ) (a : BinaryWord n → ℝ) (s : ℂ) :
    cantorPathLocalMellinGreen (x := x) n s a =
      cantorSpectralZeta s * Complex.ofReal
        (scoreAt (cantorPrefixWord (x := x) n) a) := by
  simp [cantorPathLocalMellinGreen, localMellinGreen, cantorPathCentered_eq_scoreAt]

/-- The centered source term still vanishes on the unit for each local Mellin transform. -/
theorem cantorPathLocalMellinGreen_one
    (x : ℕ → Bool) (n : ℕ) (s : ℂ) :
    cantorPathLocalMellinGreen (x := x) n s (1 : BinaryWord n → ℝ) = 0 := by
  unfold cantorPathLocalMellinGreen localMellinGreen
  rw [centeredFunctional_one_eq_zero
    (A := BinaryWord n → ℝ) (S := cantorPathLocalDensityState (x := x) n)]
  simp

end

end InfoGeometry.Canonical.RelativeModularCenteredFunctional
