import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Stage sequences

The old quotient-based sequential-colimit file contains a useful elementary
calculus independent of the quotient construction.  This owner exposes that
calculus natively: finite composites of stage maps and their naturality.
-/

namespace InfoGeometry.Spectral.Colimit.Sequence

universe u

structure Diagram where
  carrier : ℕ → Type u
  step : ∀ n, carrier n → carrier (n + 1)

def iterate (D : Diagram) (n : ℕ) : (k : ℕ) → D.carrier n → D.carrier (n + k)
  | 0, x => x
  | k + 1, x =>
      cast (by simp [Nat.add_assoc]) (D.step (n + k) (iterate D n k x))

@[simp] theorem iterate_zero (D : Diagram) (n : ℕ) (x : D.carrier n) :
    iterate D n 0 x = x :=
  rfl

@[simp] theorem iterate_succ (D : Diagram) (n k : ℕ) (x : D.carrier n) :
    iterate D n (k + 1) x = D.step (n + k) (iterate D n k x) :=
  by simp [iterate]

structure Map (D E : Diagram) where
  toFun : ∀ n, D.carrier n → E.carrier n
  comm : ∀ n x, toFun (n + 1) (D.step n x) = E.step n (toFun n x)

instance {D E : Diagram} : CoeFun (Map D E)
    (fun _ => ∀ n, D.carrier n → E.carrier n) where
  coe f := f.toFun

@[simp] theorem Map.comm_apply {D E : Diagram} (f : Map D E) (n : ℕ)
    (x : D.carrier n) :
    f (n + 1) (D.step n x) = E.step n (f n x) :=
  f.comm n x

theorem Map.iterate_naturality {D E : Diagram} (f : Map D E)
    (n k : ℕ) (x : D.carrier n) :
    f (n + k) (iterate D n k x) = iterate E n k (f n x) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
      simpa only [Nat.add_succ, iterate] using
        (f.comm (n + k) (iterate D n k x)).trans
          (congrArg (E.step (n + k)) ih)

def Map.id (D : Diagram) : Map D D where
  toFun := fun _ x => x
  comm := by intro n x; rfl

def Map.comp {D E F : Diagram} (g : Map E F) (f : Map D E) : Map D F where
  toFun := fun n x => g n (f n x)
  comm := by
    intro n x
    rw [f.comm, g.comm]

@[simp] theorem Map.id_apply (D : Diagram) (n : ℕ) (x : D.carrier n) :
    Map.id D n x = x :=
  rfl

@[simp] theorem Map.comp_apply {D E F : Diagram} (g : Map E F) (f : Map D E)
    (n : ℕ) (x : D.carrier n) :
    Map.comp g f n x = g n (f n x) :=
  rfl

@[simp] theorem Map.comp_id {D E : Diagram} (f : Map D E) :
    Map.comp f (Map.id D) = f := by
  cases f
  rfl

@[simp] theorem Map.id_comp {D E : Diagram} (f : Map D E) :
    Map.comp (Map.id E) f = f := by
  cases f
  rfl

theorem Map.comp_assoc {D E F G : Diagram}
    (h : Map F G) (g : Map E F) (f : Map D E) :
    Map.comp h (Map.comp g f) = Map.comp (Map.comp h g) f := by
  cases f
  cases g
  cases h
  rfl

end InfoGeometry.Spectral.Colimit.Sequence
