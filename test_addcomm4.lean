import Mathlib.Algebra.Module.Basic

structure Foo (A B : Type) [AddCommGroup A] [AddCommGroup B] where
  fst : A
  snd : B

instance {A B} [AddCommGroup A] [AddCommGroup B] : Add (Foo A B) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance {A B} [AddCommGroup A] [AddCommGroup B] : Neg (Foo A B) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
instance {A B} [AddCommGroup A] [AddCommGroup B] : Zero (Foo A B) := ⟨⟨0, 0⟩⟩

@[ext] lemma ext_foo {A B} [AddCommGroup A] [AddCommGroup B] {x y : Foo A B} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := by
  cases x; cases y; congr

instance {A B} [AddCommGroup A] [AddCommGroup B] : AddCommGroup (Foo A B) where
  add_assoc x y z := by ext <;> simp [add_assoc]
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  neg_add_cancel x := by ext <;> simp
  add_comm x y := by ext <;> simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

