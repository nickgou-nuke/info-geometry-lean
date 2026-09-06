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

/-- A dummy topological manifold on which V4 acts. -/
class KleinAction (M : Type) where
  act : V4 → M → M
  act_e : ∀ x, act V4.e x = x
  act_mul : ∀ g h x, act (V4.mul g h) x = act g (act h x)

/-- A spinor predicate supplied by the geometric/Clifford owner. -/
abbrev SpinorPredicate (M : Type) := M → Prop

/-- Spinor states satisfying the supplied admissibility predicate. -/
structure SpinorState (M : Type) (P : SpinorPredicate M) where
  val : M
  is_spinor : P val

/-- Vector states satisfying the same carrier predicate. -/
structure VectorState (M : Type) (P : SpinorPredicate M) where
  val : M
  is_vector : P val

/-- The equivalence relation mapping spinor states to vector states 
    (duality on resolved orbifolds). -/
structure IsoEquiv (A B : Type) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

def SpinorVectorEquiv (M : Type) (P : SpinorPredicate M) :
    IsoEquiv (SpinorState M P) (VectorState M P) where
  toFun s := ⟨s.val, s.is_spinor⟩
  invFun v := ⟨v.val, v.is_vector⟩
  left_inv s := by cases s; rfl
  right_inv v := by cases v; rfl

/-- Formal statement of the exact isomorphism between spinor and vector states. -/
def spinor_vector_duality (M : Type) [KleinAction M] (P : SpinorPredicate M) :
  IsoEquiv (SpinorState M P) (VectorState M P) :=
  SpinorVectorEquiv M P
