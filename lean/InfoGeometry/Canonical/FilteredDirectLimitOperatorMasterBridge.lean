import InfoGeometry.Canonical.FilteredDirectLimitOperator
import InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

noncomputable section

namespace InfoGeometry.Canonical.FilteredDirectLimitOperatorMasterBridge

open _root_.InfoGeometry.Canonical.FilteredDirectLimitOperator
open _root_.InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

universe u

/-- Compatibility transports a stage operator to the algebraic direct limit. -/
theorem colimit_intertwiner_diff_zero_law
    (Stage : ℕ → Type u) [∀ n, AddCommGroup (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)
    (F : CompatibleOperatorFamily Stage)
    (hcommutes :
      ∀ (m n : ℕ) (h : m ≤ n) (x : Stage m),
        F.op n (f m n h x) = f m n h (F.op m x))
    (m n : ℕ) (h : m ≤ n) (x : Stage m) :
    F.operatedOf Stage f n (f m n h x) = F.operatedOf Stage f m x := by
  exact CompatibleOperatorFamily.operatedOf_compatible
    Stage f F hcommutes m n h x

/-- A supplied anticommutation relation gives the vanishing anticommutator. -/
theorem hestenes_krein_anticommutator_law
    {Op : Type*} [Ring Op] (a b : Op)
    (h_anticomm : a * b = - (b * a)) :
    a * b + b * a = 0 := by
  rw [h_anticomm]
  exact neg_add_cancel (b * a)

/-- The antiunitary fixed locus is the critical line. -/
theorem antiunitary_fixed_locus_sum_law (s : ℂ)
    (h_anti : s = 1 - star s) : s.re = 1 / 2 := by
  exact (critical_line_fixed_locus_iff s).1 h_anti

end InfoGeometry.Canonical.FilteredDirectLimitOperatorMasterBridge
