import Mathlib

/-!
# UHF Inductive Colimit Boundary

This module promotes the audited diagonal-MASA/cylinder part of
`external_refs/auto/proofs/UHFInductiveColimit.lean` into the owned
`InfoGeometry` namespace.

## Proof Boundary Audit

Closed finite layer:
* binary words as finite Cantor prefixes;
* the diagonal successor embedding `f ↦ f ∘ prefixSucc`;
* preservation of `0`, `1`, addition, and multiplication;
* injectivity of the successor embedding;
* compatibility of finite-cylinder observables with successor embeddings;
* finite constant observables as compatible cylinder functions.

Deliberately not claimed here:
* a C*-completion of the full UHF algebra;
* a topology or measure on Cantor space;
* a spectral theorem for the diagonal MASA;
* any KMS, thermodynamic, zeta, or holographic interpretation.

The point of the file is the finite algebraic colimit skeleton only.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-- Binary words of length `n`. -/
abbrev BitWord (n : ℕ) : Type :=
  Fin n → Bool

/-- Diagonal finite-dimensional algebra at stage `n`. -/
abbrev DiagAlg (n : ℕ) : Type :=
  BitWord n → ℂ

/-- Cantor boundary carrier for the diagonal cylinder model. -/
abbrev CantorBoundary : Type :=
  ℕ → Bool

/-- Prefix a word of length `n + 1` down to length `n`. -/
def prefixSucc (n : ℕ) (w : BitWord (n + 1)) : BitWord n :=
  fun i => w ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩

/-- Diagonal successor embedding: duplicate over the newly added bit. -/
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

/-- The diagonal successor embedding is injective. -/
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

theorem boundaryPrefix_succ_eq_prefixSucc (n : ℕ) (b : CantorBoundary) :
    prefixSucc n (boundaryPrefix (n + 1) b) = boundaryPrefix n b := by
  ext i
  rfl

/-- Cylinder maps are compatible with the diagonal successor embeddings. -/
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

/-- Finite-cylinder functions: the concrete algebraic diagonal colimit carrier. -/
def CylinderColimit : Set (CantorBoundary → ℂ) :=
  Set.range (fun p : Sigma DiagAlg => cylinder p.1 p.2)

theorem cylinder_mem_colimit (n : ℕ) (f : DiagAlg n) :
    cylinder n f ∈ CylinderColimit := by
  exact ⟨⟨n, f⟩, rfl⟩

theorem embedded_cylinder_mem_colimit (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) ∈ CylinderColimit := by
  exact cylinder_mem_colimit (n + 1) (diagEmbedSucc n f)

theorem embedded_cylinder_same_point (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f := by
  exact cylinder_compatible_succ n f

/-- Constant diagonal observable at a finite stage. -/
def constantStageObservable (n : ℕ) (z : ℂ) : DiagAlg n :=
  fun _ => z

theorem constantStageObservable_embed (n : ℕ) (z : ℂ) :
    diagEmbedSucc n (constantStageObservable n z) =
      constantStageObservable (n + 1) z := by
  ext w
  rfl

theorem constant_cylinder_compatible (n : ℕ) (z : ℂ) :
    cylinder (n + 1) (diagEmbedSucc n (constantStageObservable n z)) =
      cylinder n (constantStageObservable n z) := by
  exact cylinder_compatible_succ n (constantStageObservable n z)

/--
Consolidated diagonal UHF/MASA colimit package: successor embeddings preserve
algebra operations, are injective, and finite constants define compatible
cylinder observables in the algebraic colimit carrier.
-/
theorem diagonal_uhf_colimit_synthesis :
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

end InfoGeometry.Canonical.UHFInductiveColimitBoundary

end noncomputable section
