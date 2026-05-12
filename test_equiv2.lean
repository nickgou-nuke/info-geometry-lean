import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Group.Equiv.Basic

structure Foo (A B : Type) [AddCommGroup A] [AddCommGroup B] where
  fst : A
  snd : B

def toProd {A B} [AddCommGroup A] [AddCommGroup B] : Foo A B ≃ A × B where
  toFun x := (x.fst, x.snd)
  invFun x := ⟨x.1, x.2⟩
  left_inv x := rfl
  right_inv x := rfl

instance {A B} [AddCommGroup A] [AddCommGroup B] : AddCommGroup (Foo A B) :=
  Equiv.addCommGroup toProd

