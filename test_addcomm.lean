import Mathlib.Algebra.Module.Basic

structure Foo (A B : Type) [AddCommGroup A] [AddCommGroup B] where
  fst : A
  snd : B

instance {A B} [AddCommGroup A] [AddCommGroup B] : Add (Foo A B) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance {A B} [AddCommGroup A] [AddCommGroup B] : Neg (Foo A B) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
instance {A B} [AddCommGroup A] [AddCommGroup B] : Zero (Foo A B) := ⟨⟨0, 0⟩⟩
instance {A B} [AddCommGroup A] [AddCommGroup B] : Sub (Foo A B) := ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
instance {A B} [AddCommGroup A] [AddCommGroup B] : SMul ℕ (Foo A B) := ⟨fun n x => ⟨n • x.fst, n • x.snd⟩⟩
instance {A B} [AddCommGroup A] [AddCommGroup B] : SMul ℤ (Foo A B) := ⟨fun n x => ⟨n • x.fst, n • x.snd⟩⟩

@[ext] lemma ext_foo {A B} [AddCommGroup A] [AddCommGroup B] {x y : Foo A B} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := by
  cases x; cases y; congr

instance {A B} [AddCommGroup A] [AddCommGroup B] : AddCommGroup (Foo A B) where
  add_assoc x y z := by ext <;> simp [add_assoc]
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  add_left_neg x := by ext <;> simp
  add_comm x y := by ext <;> simp [add_comm]
  sub_eq_add_neg x y := by ext <;> simp [sub_eq_add_neg]
  nsmul_zero x := by ext <;> simp [zero_smul]
  nsmul_succ n x := by ext <;> simp [succ_nsmul]
  zsmul_zero' x := by ext <;> simp [zero_smul]
  zsmul_succ' n x := by ext <;> simp [succ_nsmul]
  zsmul_neg' n x := by ext <;> simp [neg_smul, succ_nsmul]

