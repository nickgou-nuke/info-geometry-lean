namespace Freed

class AddCommGroup (G : Type) where
  add : G → G → G
  zero : G
  neg : G → G
  zero_add : ∀ a, add zero a = a
  add_right_neg : ∀ a, add a (neg a) = zero

class CommMonoid (M : Type) where
  mul : M → M → M
  one : M
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

structure ZornMatrix (M : Type) where
  val : M

def ZornMatrix.mul {M : Type} [CommMonoid M] (A B : ZornMatrix M) : ZornMatrix M :=
  ⟨CommMonoid.mul A.val B.val⟩

def ZornMatrix.det {M : Type} [CommMonoid M] (A : ZornMatrix M) : M :=
  A.val

theorem zorn_det_homomorphism {M : Type} [CommMonoid M] (A B : ZornMatrix M) :
  ZornMatrix.det (ZornMatrix.mul A B) = CommMonoid.mul (ZornMatrix.det A) (ZornMatrix.det B) := by
  rfl

inductive Z2
| even
| odd

def parity_flip : Z2 → Z2
| Z2.even => Z2.odd
| Z2.odd => Z2.even

structure OrbifoldBoundary (G : Type) where
  log_jacobian_flow : G
  aps_xi_invariant : G

def real_boundary_conditions {G : Type} [AddCommGroup G] (o : OrbifoldBoundary G) (p : Z2) : G :=
  match p with
  | Z2.even => o.log_jacobian_flow
  | Z2.odd => AddCommGroup.neg o.log_jacobian_flow

def global_anomaly {G : Type} [AddCommGroup G] (o : OrbifoldBoundary G) : G :=
  AddCommGroup.add o.aps_xi_invariant (AddCommGroup.add (real_boundary_conditions o Z2.even) (real_boundary_conditions o (parity_flip Z2.even)))

theorem global_anomaly_vanishing {G : Type} [AddCommGroup G] (o : OrbifoldBoundary G) (h : o.aps_xi_invariant = AddCommGroup.zero) :
  global_anomaly o = AddCommGroup.zero := by
  have h1 : global_anomaly o = AddCommGroup.add o.aps_xi_invariant (AddCommGroup.add o.log_jacobian_flow (AddCommGroup.neg o.log_jacobian_flow)) := by rfl
  have h2 : AddCommGroup.add o.log_jacobian_flow (AddCommGroup.neg o.log_jacobian_flow) = AddCommGroup.zero := AddCommGroup.add_right_neg o.log_jacobian_flow
  rw [h1, h, h2, AddCommGroup.zero_add]

end Freed
