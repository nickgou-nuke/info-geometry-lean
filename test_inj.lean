import Mathlib.Algebra.Module.Basic

structure Foo (A B : Type) [AddCommGroup A] [AddCommGroup B] where
  fst : A
  snd : B

def toProd {A B} [AddCommGroup A] [AddCommGroup B] (x : Foo A B) : A × B := (x.fst, x.snd)

lemma toProd_injective {A B} [AddCommGroup A] [AddCommGroup B] : Function.Injective (@toProd A B _ _) := by
  intro x y h
  cases x; cases y; injection h with h1 h2
  subst h1 h2
  rfl

instance {A B} [AddCommGroup A] [AddCommGroup B] : AddCommGroup (Foo A B) :=
  Function.Injective.addCommGroup toProd toProd_injective (by rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

