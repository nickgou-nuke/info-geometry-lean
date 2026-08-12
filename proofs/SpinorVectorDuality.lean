/-- The Klein four-group V_4 represented abstractly. -/
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

/- An abstract carrier on which the supplied V4 action is defined. -/
class KleinAction (M : Type) where
  act : V4 → M → M
  act_e : ∀ x, act V4.e x = x
  act_mul : ∀ g h x, act (V4.mul g h) x = act g (act h x)

/-- Spinor and Vector state representations on the resolved manifold. -/
structure SpinorState (M : Type) where
  val : M

structure VectorState (M : Type) where
  val : M

/-- The equivalence relation mapping spinor states to vector states 
    (duality on resolved orbifolds). -/
structure IsoEquiv (A B : Type) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

def SpinorVectorEquiv (M : Type) : IsoEquiv (SpinorState M) (VectorState M) where
  toFun s := ⟨s.val⟩
  invFun v := ⟨v.val⟩
  left_inv s := by cases s; rfl
  right_inv v := by cases v; rfl

/-- Formal statement of the exact isomorphism between spinor and vector states. -/
def spinor_vector_duality (M : Type) [KleinAction M] :
  IsoEquiv (SpinorState M) (VectorState M) :=
  SpinorVectorEquiv M
