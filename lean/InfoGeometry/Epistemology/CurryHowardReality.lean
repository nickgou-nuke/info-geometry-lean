import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace InfoGeometry.Epistemology.CurryHowardReality

noncomputable section

structure Environment where
  coupling : ℝ
  coupling_pos : 0 < coupling

def response (environment : Environment) (efficiency : ℝ) : ℝ :=
  efficiency * (1 - environment.coupling * efficiency)

def balance (environment : Environment) : ℝ :=
  1 / (2 * environment.coupling)

def IsMaximizer (environment : Environment) (efficiency : ℝ) : Prop :=
  ∀ candidate, response environment candidate ≤ response environment efficiency

theorem response_completed_square (environment : Environment) (efficiency : ℝ) :
    response environment efficiency = 1 / (4 * environment.coupling) -
      environment.coupling * (efficiency - balance environment) ^ 2 := by
  have coupling_ne := ne_of_gt environment.coupling_pos
  unfold response balance
  field_simp
  ring

theorem response_at_balance (environment : Environment) :
    response environment (balance environment) = 1 / (4 * environment.coupling) := by
  rw [response_completed_square]
  simp

theorem response_le_capacity (environment : Environment) (efficiency : ℝ) :
    response environment efficiency ≤ 1 / (4 * environment.coupling) := by
  rw [response_completed_square]
  exact sub_le_self _ (mul_nonneg environment.coupling_pos.le (sq_nonneg _))

theorem capacity_isGreatest (environment : Environment) :
    IsGreatest (Set.range (response environment)) (1 / (4 * environment.coupling)) := by
  refine ⟨⟨balance environment, response_at_balance environment⟩, ?_⟩
  rintro value ⟨efficiency, rfl⟩
  exact response_le_capacity environment efficiency

theorem response_eq_capacity_iff (environment : Environment) (efficiency : ℝ) :
    response environment efficiency = 1 / (4 * environment.coupling) ↔
      efficiency = balance environment := by
  rw [response_completed_square]
  constructor
  · intro equality
    have product_zero : environment.coupling * (efficiency - balance environment) ^ 2 = 0 := by
      linarith
    have square_zero := (mul_eq_zero.mp product_zero).resolve_left
      (ne_of_gt environment.coupling_pos)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp square_zero)
  · intro equality
    simp [equality]

theorem balance_isMaximizer (environment : Environment) :
    IsMaximizer environment (balance environment) := by
  intro candidate
  rw [response_at_balance]
  exact response_le_capacity environment candidate

theorem isMaximizer_iff (environment : Environment) (efficiency : ℝ) :
    IsMaximizer environment efficiency ↔ efficiency = balance environment := by
  constructor
  · intro maximal
    apply (response_eq_capacity_iff environment efficiency).mp
    apply le_antisymm (response_le_capacity environment efficiency)
    simpa only [response_at_balance] using maximal (balance environment)
  · rintro rfl
    exact balance_isMaximizer environment

def CertifiedOptimum (environment : Environment) :=
  {efficiency : ℝ // IsMaximizer environment efficiency}

def certifiedOptimum (environment : Environment) : CertifiedOptimum environment :=
  ⟨balance environment, balance_isMaximizer environment⟩

instance (environment : Environment) : Subsingleton (CertifiedOptimum environment) where
  allEq first second := by
    apply Subtype.ext
    exact ((isMaximizer_iff environment first.val).mp first.property).trans
      ((isMaximizer_iff environment second.val).mp second.property).symm

def normalization (environment : Environment) (_initial : ℝ) : ℝ :=
  (certifiedOptimum environment).val

theorem normalization_idempotent (environment : Environment) (initial : ℝ) :
    normalization environment (normalization environment initial) =
      normalization environment initial := rfl

theorem normalization_fixed_iff (environment : Environment) (initial : ℝ) :
    normalization environment initial = initial ↔ initial = balance environment := by
  change balance environment = initial ↔ initial = balance environment
  exact eq_comm

theorem normalization_outputs_equal (environment : Environment) (first second : ℝ) :
    normalization environment first = normalization environment second := rfl

theorem equal_outputs_do_not_identify_inputs (environment : Environment) :
    ∃ first second : ℝ, first ≠ second ∧
      normalization environment first = normalization environment second :=
  ⟨0, 1, zero_ne_one, rfl⟩

def relaxation (environment : Environment) (fraction initial : ℝ) : ℝ :=
  balance environment + (1 - fraction) * (initial - balance environment)

theorem relaxation_error (environment : Environment) (fraction initial : ℝ) :
    relaxation environment fraction initial - balance environment =
      (1 - fraction) * (initial - balance environment) := by
  unfold relaxation
  ring

theorem relaxation_gap (environment : Environment) (fraction initial : ℝ) :
    response environment (balance environment) -
        response environment (relaxation environment fraction initial) =
      (1 - fraction) ^ 2 *
        (response environment (balance environment) - response environment initial) := by
  simp only [response_at_balance]
  rw [response_completed_square environment (relaxation _ _ _),
    response_completed_square environment initial, relaxation_error]
  ring

theorem relaxation_improves_response (environment : Environment) (fraction initial : ℝ)
    (fraction_nonneg : 0 ≤ fraction) (fraction_le_two : fraction ≤ 2) :
    response environment initial ≤ response environment (relaxation environment fraction initial) := by
  have contraction : (1 - fraction) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg fraction_nonneg (sub_nonneg.mpr fraction_le_two)]
  have gap_nonneg : 0 ≤ response environment (balance environment) - response environment initial := by
    rw [response_at_balance]
    exact sub_nonneg.mpr (response_le_capacity environment initial)
  have bound := mul_le_mul_of_nonneg_right contraction gap_nonneg
  rw [← relaxation_gap] at bound
  linarith

theorem relaxation_one_eq_normalization (environment : Environment) (initial : ℝ) :
    relaxation environment 1 initial = normalization environment initial := by
  simp [relaxation, normalization, certifiedOptimum]

end

end InfoGeometry.Epistemology.CurryHowardReality
