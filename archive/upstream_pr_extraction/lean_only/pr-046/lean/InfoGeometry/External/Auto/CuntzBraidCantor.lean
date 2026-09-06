import Mathlib.Data.List.Basic

namespace CuntzBraidCantor

abbrev BitWord := List Bool

def complementWord : BitWord → BitWord :=
  List.map Bool.not

def prefixMap (u : BitWord) : BitWord → BitWord :=
  fun v => u ++ v

@[simp]
theorem complementWord_nil : complementWord [] = [] := by
  simp [complementWord]

@[simp]
theorem complementWord_cons (b : Bool) (w : BitWord) :
    complementWord (b :: w) = Bool.not b :: complementWord w := by
  simp [complementWord]

@[simp]
theorem complementWord_append (u v : BitWord) :
    complementWord (u ++ v) = complementWord u ++ complementWord v := by
  simp [complementWord]

@[simp]
theorem complementWord_involutive (w : BitWord) :
    complementWord (complementWord w) = w := by
  induction w with
  | nil => simp
  | cons b w ih =>
      cases b <;> simp [ih]

@[simp]
theorem prefixMap_nil (w : BitWord) :
    prefixMap [] w = w := by
  simp [prefixMap]

@[simp]
theorem prefixMap_append (u v w : BitWord) :
    prefixMap (u ++ v) w = prefixMap u (prefixMap v w) := by
  simp [prefixMap, List.append_assoc]

inductive SignedGen (n : Nat) where
  | pos : Fin n → SignedGen n
  | neg : Fin n → SignedGen n
deriving DecidableEq, Repr

abbrev BraidWord (n : Nat) := List (SignedGen n)

def invertGen {n : Nat} : SignedGen n → SignedGen n
  | SignedGen.pos i => SignedGen.neg i
  | SignedGen.neg i => SignedGen.pos i

def reverseInverse {n : Nat} (w : BraidWord n) : BraidWord n :=
  w.reverse.map invertGen

def braidLength {n : Nat} (w : BraidWord n) : Nat :=
  w.length

@[simp]
theorem invertGen_involutive {n : Nat} (g : SignedGen n) :
    invertGen (invertGen g) = g := by
  cases g <;> simp [invertGen]

@[simp]
theorem reverseInverse_nil {n : Nat} :
    reverseInverse ([] : BraidWord n) = [] := by
  simp [reverseInverse]

@[simp]
theorem reverseInverse_append {n : Nat} (u v : BraidWord n) :
    reverseInverse (u ++ v) = reverseInverse v ++ reverseInverse u := by
  simp [reverseInverse]

@[simp]
theorem braidLength_reverseInverse {n : Nat} (w : BraidWord n) :
    braidLength (reverseInverse w) = braidLength w := by
  simp [braidLength, reverseInverse]

@[simp]
theorem reverseInverse_involutive {n : Nat} (w : BraidWord n) :
    reverseInverse (reverseInverse w) = w := by
  induction w with
  | nil => simp
  | cons g w ih =>
      simp [reverseInverse, Function.comp_def]

end CuntzBraidCantor
