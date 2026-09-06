inductive Three
  | one
  | two
  | three

open Three

def s1 : Three → Three
  | one => two
  | two => one
  | three => three

def s2 : Three → Three
  | one => one
  | two => three
  | three => two

inductive B3Gen
  | sigma1
  | sigma2

structure BraidRep (A : Type) where
  rep : B3Gen → A
  comp : A → A → A
  artin : comp (comp (rep .sigma1) (rep .sigma2)) (rep .sigma1) = 
          comp (comp (rep .sigma2) (rep .sigma1)) (rep .sigma2)

def permRep : BraidRep (Three → Three) where
  rep
    | B3Gen.sigma1 => s1
    | B3Gen.sigma2 => s2
  comp f g := f ∘ g
  artin := by
    funext x
    cases x <;> rfl
