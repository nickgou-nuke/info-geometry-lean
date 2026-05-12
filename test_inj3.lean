import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Group.InjSurj

structure Foo (A B : Type) [AddCommGroup A] [AddCommGroup B] where
  fst : A
  snd : B

instance {A B} [AddCommGroup A] [AddCommGroup B] : Add (Foo A B) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance {A B} [AddCommGroup A] [AddCommGroup B] : Zero (Foo A B) := ⟨⟨0, 0⟩⟩
instance {A B} [AddCommGroup A] [AddCommGroup B] : Neg (Foo A B) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
instance {A B} [AddCommGroup A] [AddCommGroup B] : Sub (Foo A B) := ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
instance {A B} [AddCommGroup A] [AddCommGroup B] : SMul ℕ (Foo A B) := ⟨fun n x => ⟨n • x.fst, n • x.snd⟩⟩
instance {A B} [AddCommGroup A] [AddCommGroup B] : SMul ℤ (Foo A B) := ⟨fun n x => ⟨n • x.fst, n • x.snd⟩⟩

def toProd {A B} [AddCommGroup A] [AddCommGroup B] (x : Foo A B) : A × B := (x.fst, x.snd)

lemma toProd_injective {A B} [AddCommGroup A] [AddCommGroup B] : Function.Injective (@toProd A B _ _) := by
  intro x y h
  cases x; cases y; injection h with h1 h2
  subst h1 h2
  rfl

instance {A B} [AddCommGroup A] [AddCommGroup B] : AddCommGroup (Foo A B) :=
  Function.Injective.addCommGroup toProd toProd_injective rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

