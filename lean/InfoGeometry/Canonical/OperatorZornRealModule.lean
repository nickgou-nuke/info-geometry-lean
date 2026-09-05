import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator

/-!
# The additive real module of the existing operator-Zorn carrier

Only additive and scalar structure is installed. The existing `mul` is
unchanged. In particular no associative, alternative, or Lie structure on
the Zorn product is inferred from its coefficient ring.
-/

noncomputable section
namespace InfoGeometry.Canonical.OperatorZornRealModule

open InfoGeometry.Physics.NCG

variable {A : Type*} [Ring A]

def coordinatesEquiv : OperatorZornMatrix A ≃ A × A × (Fin 3 → A) × (Fin 3 → A) where
  toFun X := (X.n_plus, X.n_minus, X.sigma_plus, X.sigma_minus)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv X := by cases X; rfl
  right_inv x := by rcases x with ⟨a,b,u,v⟩; rfl

theorem zornAdd_assoc (X Y Z : OperatorZornMatrix A) : (X+Y)+Z = X+(Y+Z) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i) | skip
  all_goals change (_ + _) + _ = _ + (_ + _)
  all_goals exact add_assoc _ _ _

theorem zornZero_add (X : OperatorZornMatrix A) : 0+X = X := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i) | skip
  all_goals change 0 + _ = _
  all_goals exact zero_add _

theorem zornNeg_add (X : OperatorZornMatrix A) : -X+X = 0 := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i) | skip
  all_goals change -_ + _ = 0
  all_goals exact neg_add_cancel _

instance instZornAddGroup : AddGroup (OperatorZornMatrix A) :=
  AddGroup.ofLeftAxioms zornAdd_assoc zornZero_add zornNeg_add

instance instZornAddCommGroup : AddCommGroup (OperatorZornMatrix A) :=
  AddCommGroup.mk (by
    intro X Y
    apply operatorZornMatrix_ext
    all_goals first | (funext i) | skip
    all_goals change _ + _ = _ + _
    all_goals exact add_comm _ _)

variable [Algebra ℝ A]

instance instZornSMul : SMul ℝ (OperatorZornMatrix A) :=
  ⟨fun c X => ⟨c • X.n_plus, c • X.n_minus,
    fun i => c • X.sigma_plus i, fun i => c • X.sigma_minus i⟩⟩

instance instZornModule : Module ℝ (OperatorZornMatrix A) where
  one_smul X := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i) | skip
    all_goals change (1 : ℝ) • _ = _
    all_goals exact one_smul ℝ _
  mul_smul c d X := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i) | skip
    all_goals change (c*d) • _ = c • (d • _)
    all_goals exact mul_smul c d _
  smul_zero c := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i) | skip
    all_goals change c • (0 : A) = 0
    all_goals exact smul_zero c
  smul_add c X Y := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i) | skip
    all_goals change c • (_ + _) = c • _ + c • _
    all_goals exact smul_add c _ _
  add_smul c d X := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i) | skip
    all_goals change (c+d) • _ = c • _ + d • _
    all_goals exact add_smul c d _
  zero_smul X := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i) | skip
    all_goals change (0 : ℝ) • _ = 0
    all_goals exact zero_smul ℝ _

def coordinatesLinearEquiv :
    OperatorZornMatrix A ≃ₗ[ℝ] A × A × (Fin 3 → A) × (Fin 3 → A) where
  toEquiv := coordinatesEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem smul_n_plus (c : ℝ) (X : OperatorZornMatrix A) :
    (c • X).n_plus = c • X.n_plus := rfl

@[simp] theorem smul_n_minus (c : ℝ) (X : OperatorZornMatrix A) :
    (c • X).n_minus = c • X.n_minus := rfl

@[simp] theorem smul_sigma_plus (c : ℝ) (X : OperatorZornMatrix A) (i : Fin 3) :
    (c • X).sigma_plus i = c • X.sigma_plus i := rfl

@[simp] theorem smul_sigma_minus (c : ℝ) (X : OperatorZornMatrix A) (i : Fin 3) :
    (c • X).sigma_minus i = c • X.sigma_minus i := rfl

/-- Scalar movement uses central real coefficients, not Zorn associativity. -/
theorem zorn_smul_mul (c : ℝ) (X Y : OperatorZornMatrix A) :
    (c • X) * Y = c • (X * Y) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals simp only [smul_mul_assoc, smul_add, smul_sub]

theorem zorn_mul_smul (c : ℝ) (X Y : OperatorZornMatrix A) :
    X * (c • Y) = c • (X * Y) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals simp only [mul_smul_comm, smul_add, smul_sub]

end InfoGeometry.Canonical.OperatorZornRealModule
