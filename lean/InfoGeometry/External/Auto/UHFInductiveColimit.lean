import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# UHF Inductive Colimit: Diagonal Cylinder Model

The full UHF inclusion is `M_{2^n} → M_{2^(n+1)}`, `A ↦ A ⊗ I₂`.
The diagonal MASA part is simpler and exactly matches the finite Fock cutoff:

* stage `n` is the algebra of functions on binary words of length `n`;
* the connecting map duplicates along the new bit:
  `f(w₀...wₙ₋₁) ↦ f(w₀...wₙ₋₁)`;
* the inductive colimit is represented concretely by finite-cylinder functions
  on Cantor boundary `ℕ → Bool`.

This file proves the algebraic compatibility and injectivity of the finite
stage maps into the cylinder colimit.  It is the UHF/MASA backbone for the
finite prime-Fock supertrace factors.
-/

noncomputable section

namespace UHFInductiveColimit

/-- Binary words of length `n`. -/
abbrev BitWord (n : ℕ) : Type :=
  Fin n → Bool

/-- Diagonal finite-dimensional algebra at stage `n`. -/
abbrev DiagAlg (n : ℕ) : Type :=
  BitWord n → ℂ

/-- Cantor boundary of the diagonal UHF algebra. -/
abbrev CantorBoundary : Type :=
  ℕ → Bool

/-- Prefix a word of length `n+1` down to length `n`. -/
def prefixSucc (n : ℕ) (w : BitWord (n + 1)) : BitWord n :=
  fun i => w ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩

/-- UHF diagonal connecting map: duplicate over the newly added bit. -/
def diagEmbedSucc (n : ℕ) : DiagAlg n → DiagAlg (n + 1) :=
  fun f w => f (prefixSucc n w)

theorem diagEmbedSucc_apply (n : ℕ) (f : DiagAlg n) (w : BitWord (n + 1)) :
    diagEmbedSucc n f w = f (prefixSucc n w) := rfl

theorem diagEmbedSucc_add (n : ℕ) (f g : DiagAlg n) :
    diagEmbedSucc n (f + g) = diagEmbedSucc n f + diagEmbedSucc n g := by
  ext w
  rfl

theorem diagEmbedSucc_mul (n : ℕ) (f g : DiagAlg n) :
    diagEmbedSucc n (f * g) = diagEmbedSucc n f * diagEmbedSucc n g := by
  ext w
  rfl

theorem diagEmbedSucc_one (n : ℕ) :
    diagEmbedSucc n 1 = (1 : DiagAlg (n + 1)) := by
  ext w
  rfl

theorem diagEmbedSucc_zero (n : ℕ) :
    diagEmbedSucc n 0 = (0 : DiagAlg (n + 1)) := by
  ext w
  rfl

/-- Extend a word by one bit. -/
def extendSucc (n : ℕ) (w : BitWord n) (b : Bool) : BitWord (n + 1) :=
  fun i => if h : i.1 < n then w ⟨i.1, h⟩ else b

theorem prefixSucc_extendSucc (n : ℕ) (w : BitWord n) (b : Bool) :
    prefixSucc n (extendSucc n w b) = w := by
  ext i
  simp [prefixSucc, extendSucc, i.2]

/-- The diagonal connecting map is injective. -/
theorem diagEmbedSucc_injective (n : ℕ) :
    Function.Injective (diagEmbedSucc n) := by
  intro f g hfg
  ext w
  have happ := congrFun hfg (extendSucc n w false)
  simpa [diagEmbedSucc_apply, prefixSucc_extendSucc] using happ

/-- Restrict a boundary point to its first `n` bits. -/
def boundaryPrefix (n : ℕ) (b : CantorBoundary) : BitWord n :=
  fun i => b i.1

/-- Finite-cylinder realization of a stage-`n` diagonal observable. -/
def cylinder (n : ℕ) (f : DiagAlg n) : CantorBoundary → ℂ :=
  fun b => f (boundaryPrefix n b)

theorem cylinder_apply (n : ℕ) (f : DiagAlg n) (b : CantorBoundary) :
    cylinder n f b = f (boundaryPrefix n b) := rfl

theorem boundaryPrefix_succ_eq_prefixSucc
    (n : ℕ) (b : CantorBoundary) :
    prefixSucc n (boundaryPrefix (n + 1) b) = boundaryPrefix n b := by
  ext i
  rfl

/-- Cylinder maps are compatible with the UHF connecting maps. -/
theorem cylinder_compatible_succ (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f := by
  ext b
  simp [cylinder, diagEmbedSucc, boundaryPrefix_succ_eq_prefixSucc]

theorem cylinder_add (n : ℕ) (f g : DiagAlg n) :
    cylinder n (f + g) = cylinder n f + cylinder n g := by
  ext b
  rfl

theorem cylinder_mul (n : ℕ) (f g : DiagAlg n) :
    cylinder n (f * g) = cylinder n f * cylinder n g := by
  ext b
  rfl

theorem cylinder_one (n : ℕ) :
    cylinder n 1 = (1 : CantorBoundary → ℂ) := by
  ext b
  rfl

/-- Finite-cylinder functions: the concrete diagonal UHF inductive colimit. -/
def CylinderColimit : Set (CantorBoundary → ℂ) :=
  Set.range (fun p : Sigma DiagAlg => cylinder p.1 p.2)

theorem cylinder_mem_colimit (n : ℕ) (f : DiagAlg n) :
    cylinder n f ∈ CylinderColimit := by
  exact ⟨⟨n, f⟩, rfl⟩

theorem embedded_cylinder_mem_colimit (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) ∈ CylinderColimit := by
  exact cylinder_mem_colimit (n + 1) (diagEmbedSucc n f)

theorem embedded_cylinder_same_point
    (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f := by
  exact cylinder_compatible_succ n f

/-- Pair a finite Fock graded factor with a diagonal UHF cylinder observable. -/
def constantStageObservable (n : ℕ) (z : ℂ) : DiagAlg n :=
  fun _ => z

theorem constantStageObservable_embed
    (n : ℕ) (z : ℂ) :
    diagEmbedSucc n (constantStageObservable n z) =
      constantStageObservable (n + 1) z := by
  ext w
  rfl

theorem constant_cylinder_compatible
    (n : ℕ) (z : ℂ) :
    cylinder (n + 1)
        (diagEmbedSucc n (constantStageObservable n z))
      =
    cylinder n (constantStageObservable n z) := by
  exact cylinder_compatible_succ n (constantStageObservable n z)

/--
Consolidated UHF/MASA colimit package:
successor embeddings preserve algebra operations, are injective, and finite
Fock constants define compatible cylinder observables in the colimit.
-/
theorem uhf_inductive_colimit_synthesis :
    (∀ n : ℕ, Function.Injective (diagEmbedSucc n)) ∧
    (∀ n : ℕ, ∀ f g : DiagAlg n,
      diagEmbedSucc n (f + g) = diagEmbedSucc n f + diagEmbedSucc n g) ∧
    (∀ n : ℕ, ∀ f g : DiagAlg n,
      diagEmbedSucc n (f * g) = diagEmbedSucc n f * diagEmbedSucc n g) ∧
    (∀ n : ℕ, diagEmbedSucc n 1 = (1 : DiagAlg (n + 1))) ∧
    (∀ n : ℕ, ∀ f : DiagAlg n,
      cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f) ∧
    (∀ n : ℕ, ∀ z : ℂ,
      diagEmbedSucc n (constantStageObservable n z) =
        constantStageObservable (n + 1) z) ∧
    (∀ n : ℕ, ∀ f : DiagAlg n, cylinder n f ∈ CylinderColimit) := by
  exact ⟨diagEmbedSucc_injective,
    diagEmbedSucc_add,
    diagEmbedSucc_mul,
    diagEmbedSucc_one,
    cylinder_compatible_succ,
    constantStageObservable_embed,
    cylinder_mem_colimit⟩

end UHFInductiveColimit

end noncomputable section
