import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-
# Modular/Krein reflection over a directed tower

This file isolates the commuting-square theorem that the repo has been missing:
if a stagewise reflection `J` commutes with the successor embedding, then it
commutes with every iterated embedding in the directed system.

The statement is deliberately algebraic.  It does not claim analytic Tomita-
Takesaki theory; it packages the finite reflection skeleton used by the
existing modular/Krein/CPT bridges.
-/

noncomputable section

namespace ModularKreinReflectionColimit

/-- A directed tower of additive modules with a reflection operator. -/
structure KreinTower (R : Type*) [Semiring R] where
  stage : ℕ → Type*
  stageAdd : ∀ n, AddCommGroup (stage n)
  stageModule : ∀ n, Module R (stage n)
  emb : ∀ n, stage n →ₗ[R] stage (n + 1)
  J : ∀ n, stage n →ₗ[R] stage n
  J_involutive : ∀ n (x : stage n), J n (J n x) = x
  J_comm : ∀ n (x : stage n), J (n + 1) (emb n x) = emb n (J n x)

namespace KreinTower

variable {R : Type*} [Semiring R]
variable (T : KreinTower R)

instance (T : KreinTower R) (n : ℕ) : AddCommGroup (T.stage n) :=
  T.stageAdd n

instance (T : KreinTower R) (n : ℕ) : Module R (T.stage n) :=
  T.stageModule n

/-- Iterated successor embedding through a directed tower. -/
def embIter (T : KreinTower R) : ∀ (n : ℕ), (k : ℕ) → T.stage n →ₗ[R] T.stage (n + k)
  | _, 0 =>
      LinearMap.id
  | n, k + 1 =>
      (T.emb (n + k)).comp (KreinTower.embIter T n k)

@[simp]
theorem embIter_zero (_n : ℕ) :
    KreinTower.embIter T _n 0 = LinearMap.id := rfl

@[simp]
theorem embIter_succ (n k : ℕ) :
    KreinTower.embIter T n (k + 1) = (T.emb (n + k)).comp (KreinTower.embIter T n k) := rfl

/-- The reflection commutes with every iterated embedding. -/
theorem J_commutes_with_embIter :
    ∀ (n k : ℕ) (x : T.stage n),
      T.J (n + k) (KreinTower.embIter T n k x) = KreinTower.embIter T n k (T.J n x) := by
  intro n k
  induction k generalizing n with
  | zero =>
      intro x
      simp [KreinTower.embIter]
  | succ k ih =>
      intro x
      calc
        T.J (n + (k + 1)) (KreinTower.embIter T n (k + 1) x)
            = T.J (n + (k + 1)) (T.emb (n + k) (KreinTower.embIter T n k x)) := by
                rfl
        _ = T.emb (n + k) (T.J (n + k) (KreinTower.embIter T n k x)) := by
                simpa [Nat.add_assoc] using
                  (T.J_comm (n := n + k) (x := KreinTower.embIter T n k x))
        _ = T.emb (n + k) (KreinTower.embIter T n k (T.J n x)) := by
                exact congrArg (T.emb (n + k)) (ih (n := n) x)
        _ = KreinTower.embIter T n (k + 1) (T.J n x) := by
                rfl

/-- The reflection remains involutive after any finite number of embeddings. -/
theorem J_involutive_iterated (n k : ℕ) (x : T.stage n) :
    T.J (n + k) (T.J (n + k) (KreinTower.embIter T n k x)) =
      KreinTower.embIter T n k x := by
  have h1 := J_commutes_with_embIter (T := T) n k x
  have h2 := J_commutes_with_embIter (T := T) n k (T.J n x)
  calc
    T.J (n + k) (T.J (n + k) (KreinTower.embIter T n k x))
        = T.J (n + k) (KreinTower.embIter T n k (T.J n x)) := by
            rw [h1]
    _ = KreinTower.embIter T n k (T.J n (T.J n x)) := by
            rw [h2]
    _ = KreinTower.embIter T n k x := by
            simpa using congrArg (KreinTower.embIter T n k) (T.J_involutive n x)

end KreinTower

variable {R : Type*} [Semiring R]

/-- A very small concrete model: constant stage and identity reflection.

This is not the modular/Krein geometry itself.  It is the minimal witness that
the abstract tower interface is constructible by an actual Lean object.
-/
def trivialKreinTower : KreinTower (R := R) where
  stage := fun _ => PUnit
  stageAdd := by intro n; infer_instance
  stageModule := by intro n; infer_instance
  emb := fun _ => LinearMap.id
  J := fun _ => LinearMap.id
  J_involutive := by
    intro n x
    rfl
  J_comm := by
    intro n x
    rfl

/-- The trivial tower satisfies the iterated-compatibility theorem. -/
theorem trivial_J_commutes_with_embIter (n k : ℕ) (x : PUnit) :
    trivialKreinTower (R := R).J (n + k)
      (KreinTower.embIter (T := trivialKreinTower (R := R)) n k x) =
      KreinTower.embIter (T := trivialKreinTower (R := R)) n k
        (trivialKreinTower (R := R).J n x) := by
  simpa [KreinTower.embIter] using
    (KreinTower.J_commutes_with_embIter
      (T := trivialKreinTower (R := R)) n k x)

end ModularKreinReflectionColimit
