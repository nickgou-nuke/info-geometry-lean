import Mathlib.Algebra.Module.Basic
structure Foo (A B : Type) [AddCommGroup A] [AddCommGroup B] where
  fst : A
  snd : B
  deriving AddCommGroup
