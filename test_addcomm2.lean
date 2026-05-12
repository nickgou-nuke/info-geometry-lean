import Mathlib.Algebra.Module.Basic

structure Foo (A B : Type) [AddCommGroup A] [AddCommGroup B] where
  fst : A
  snd : B

@[ext] lemma ext_foo {A B} [AddCommGroup A] [AddCommGroup B] {x y : Foo A B} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := by
  cases x; cases y; congr

instance {A B} [AddCommGroup A] [AddCommGroup B] : AddCommGroup (Foo A B) where
  add x y := ⟨x.fst + y.fst, x.snd + y.snd⟩
  add_assoc x y z := by ext <;> simp [add_assoc]
  zero := ⟨0, 0⟩
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  neg x := ⟨-x.fst, -x.snd⟩
  neg_add_cancel x := by ext <;> simp
  add_comm x y := by ext <;> simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

