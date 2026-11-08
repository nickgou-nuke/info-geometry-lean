/-!
# Finite predicate-state copy

The former owner called two copies of the same predicate a spinor/vector
duality without providing a manifold, a representation, or an action that
could justify that interpretation.  This file keeps the genuine finite
content: a Klein-four multiplication law and an explicit equivalence between
two copies of one admissibility predicate.  A geometric spinor/vector bridge
requires a separate representation owner.
-/

inductive V4
| e : V4
| a : V4
| b : V4
| c : V4

namespace V4

def mul : V4 → V4 → V4
| e, x => x
| x, e => x
| a, a => e
| b, b => e
| c, c => e
| a, b => c
| b, a => c
| a, c => b
| c, a => b
| b, c => a
| c, b => a

theorem mul_assoc (x y z : V4) : mul x (mul y z) = mul (mul x y) z := by
  cases x <;> cases y <;> cases z <;> rfl

end V4

class KleinAction (M : Type) where
  act : V4 → M → M
  act_e : ∀ x, act V4.e x = x
  act_mul : ∀ g h x, act (V4.mul g h) x = act g (act h x)

abbrev AdmissiblePredicate (M : Type) := M → Prop

structure PredicateState (M : Type) (P : AdmissiblePredicate M) where
  val : M
  admissible : P val

structure PredicateStateCopy (M : Type) (P : AdmissiblePredicate M) where
  val : M
  admissible : P val

structure StateCopyEquivalence (A B : Type) where
  toFun : A → B
  invFun : B → A
  inverseOnLeft : ∀ a, invFun (toFun a) = a
  inverseOnRight : ∀ b, toFun (invFun b) = b

def predicateStateCopyEquiv (M : Type) (P : AdmissiblePredicate M) :
    StateCopyEquivalence (PredicateState M P) (PredicateStateCopy M P) where
  toFun s := ⟨s.val, s.admissible⟩
  invFun v := ⟨v.val, v.admissible⟩
  inverseOnLeft s := by cases s; rfl
  inverseOnRight v := by cases v; rfl
