import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

private theorem zornDot_smul_left (c : ℝ) (u v : Fin 3 → A) :
    NCZornElement.zornDot (c • u) v = c • NCZornElement.zornDot u v := by
  simp only [NCZornElement.zornDot, Pi.smul_apply, Algebra.smul_def]
  noncomm_ring

private theorem zornDot_smul_right (c : ℝ) (u v : Fin 3 → A) :
    NCZornElement.zornDot u (c • v) = c • NCZornElement.zornDot u v := by
  have hc : ∀ a : A, (algebraMap ℝ A) c * a = a * (algebraMap ℝ A) c :=
    fun a => Algebra.commutes c a
  simp only [NCZornElement.zornDot, Pi.smul_apply, Algebra.smul_def]
  simp only [hc]
  noncomm_ring

private theorem zornCross_smul_left (c : ℝ) (u v : Fin 3 → A) :
    NCZornElement.zornCross (c • u) v = c • NCZornElement.zornCross u v := by
  funext i
  fin_cases i <;>
    simp only [NCZornElement.zornCross, Pi.smul_apply, Algebra.smul_def]
  all_goals try simp only [smul_eq_mul]
  all_goals noncomm_ring

private theorem zornCross_smul_right (c : ℝ) (u v : Fin 3 → A) :
    NCZornElement.zornCross u (c • v) = c • NCZornElement.zornCross u v := by
  have hc : ∀ a : A, (algebraMap ℝ A) c * a = a * (algebraMap ℝ A) c :=
    fun a => Algebra.commutes c a
  funext i
  fin_cases i <;>
    simp only [NCZornElement.zornCross, Pi.smul_apply, Algebra.smul_def]
  all_goals try simp only [smul_eq_mul]
  all_goals simp only [hc]
  all_goals noncomm_ring

@[simp] theorem mul_n_plus (X Y : OperatorZornMatrix A) :
    (X * Y).n_plus = X.n_plus * Y.n_plus +
      NCZornElement.zornDot X.sigma_plus Y.sigma_minus := rfl

@[simp] theorem mul_n_minus (X Y : OperatorZornMatrix A) :
    (X * Y).n_minus = X.n_minus * Y.n_minus +
      NCZornElement.zornDot X.sigma_minus Y.sigma_plus := rfl

@[simp] theorem mul_sigma_plus (X Y : OperatorZornMatrix A) (i : Fin 3) :
    (X * Y).sigma_plus i = X.n_plus * Y.sigma_plus i +
      X.sigma_plus i * Y.n_minus -
      NCZornElement.zornCross X.sigma_minus Y.sigma_minus i := rfl

@[simp] theorem mul_sigma_minus (X Y : OperatorZornMatrix A) (i : Fin 3) :
    (X * Y).sigma_minus i = X.n_minus * Y.sigma_minus i +
      X.sigma_minus i * Y.n_plus +
      NCZornElement.zornCross X.sigma_plus Y.sigma_plus i := rfl

theorem zorn_smul_mul (c : ℝ) (X Y : OperatorZornMatrix A) :
    (c • X) * Y = c • (X * Y) := by
  have hplus : (c • X).sigma_plus = c • X.sigma_plus := rfl
  have hminus : (c • X).sigma_minus = c • X.sigma_minus := rfl
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals simp only [mul_n_plus, mul_n_minus, mul_sigma_plus,
    mul_sigma_minus, hplus, hminus, smul_n_plus, smul_n_minus, smul_sigma_plus,
    smul_sigma_minus, zornDot_smul_left, zornCross_smul_left,
    smul_mul_assoc, smul_add, smul_sub]
  all_goals abel

theorem zorn_mul_smul (c : ℝ) (X Y : OperatorZornMatrix A) :
    X * (c • Y) = c • (X * Y) := by
  have hplus : (c • Y).sigma_plus = c • Y.sigma_plus := rfl
  have hminus : (c • Y).sigma_minus = c • Y.sigma_minus := rfl
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals simp only [mul_n_plus, mul_n_minus, mul_sigma_plus,
    mul_sigma_minus, hplus, hminus, smul_n_plus, smul_n_minus, smul_sigma_plus,
    smul_sigma_minus, zornDot_smul_right, zornCross_smul_right,
    mul_smul_comm, smul_add, smul_sub]
  all_goals abel

end InfoGeometry.Canonical.OperatorZornRealModule
