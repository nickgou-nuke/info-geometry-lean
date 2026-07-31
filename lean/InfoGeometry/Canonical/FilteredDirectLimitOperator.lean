import Mathlib.Algebra.Colimit.Module

noncomputable section

namespace InfoGeometry.Canonical.FilteredDirectLimitOperator

universe u

variable
    (Stage : ℕ → Type u)
    [∀ n, AddCommGroup (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)

/-- A family of additive stage operators.  Compatibility with transitions is
supplied explicitly to the colimit constructions below. -/
structure CompatibleOperatorFamily where
  op : ∀ n, Stage n →+ Stage n

namespace CompatibleOperatorFamily

variable (F : CompatibleOperatorFamily Stage)

/-- Canonical map from one stage into the algebraic direct limit, after
applying the stage operator. -/
def operatedOf (n : ℕ) :
    Stage n →+ AddCommGroup.DirectLimit Stage f :=
  (AddCommGroup.DirectLimit.of Stage f n).comp (F.op n)

/-- The operated canonical maps form a cocone when the supplied stage family
commutes with every transition. -/
theorem operatedOf_compatible
    (hcommutes :
      ∀ (m n : ℕ) (h : m ≤ n) (x : Stage m),
        F.op n (f m n h x) = f m n h (F.op m x))
    (m n : ℕ) (h : m ≤ n) (x : Stage m) :
    operatedOf Stage f F n (f m n h x) =
      operatedOf Stage f F m x := by
  change
    AddCommGroup.DirectLimit.of Stage f n
        (F.op n (f m n h x)) =
      AddCommGroup.DirectLimit.of Stage f m (F.op m x)
  rw [hcommutes m n h x]
  exact AddCommGroup.DirectLimit.of_f
    (f := f) (i := m) (j := n) (hij := h) (x := F.op m x)

/-- The genuine additive operator induced on the algebraic filtered direct
limit by the compatible finite-stage family. -/
def directLimitOperator
    (hcommutes :
      ∀ (m n : ℕ) (h : m ≤ n) (x : Stage m),
        F.op n (f m n h x) = f m n h (F.op m x)) :
    AddCommGroup.DirectLimit Stage f →+
      AddCommGroup.DirectLimit Stage f :=
  AddCommGroup.DirectLimit.lift
    Stage f
    (AddCommGroup.DirectLimit Stage f)
    (operatedOf Stage f F)
    (operatedOf_compatible Stage f F hcommutes)

/-- The induced direct-limit operator agrees with every finite-stage operator
on canonical representatives. -/
@[simp] theorem directLimitOperator_of
    (hcommutes :
      ∀ (m n : ℕ) (h : m ≤ n) (x : Stage m),
        F.op n (f m n h x) = f m n h (F.op m x))
    (n : ℕ) (x : Stage n) :
    directLimitOperator Stage f F hcommutes
        (AddCommGroup.DirectLimit.of Stage f n x) =
      AddCommGroup.DirectLimit.of Stage f n (F.op n x) := by
  exact AddCommGroup.DirectLimit.lift_of
    (G := Stage)
    (f := f)
    (P := AddCommGroup.DirectLimit Stage f)
    (g := operatedOf Stage f F)
    (Hg := operatedOf_compatible Stage f F hcommutes)
    n x

theorem directLimitOperator_zero_of_stage_zero
    (hcommutes :
      ∀ (m n : ℕ) (h : m ≤ n) (x : Stage m),
        F.op n (f m n h x) = f m n h (F.op m x))
    {n : ℕ} {x : Stage n}
    (hx : F.op n x = 0) :
    directLimitOperator Stage f F hcommutes
        (AddCommGroup.DirectLimit.of Stage f n x) = 0 := by
  rw [directLimitOperator_of Stage f F hcommutes n x, hx]
  exact map_zero (AddCommGroup.DirectLimit.of Stage f n)

theorem directLimitKernel_of_stageKernel
    (hcommutes :
      ∀ m n (h : m ≤ n) x,
        F.op n (f m n h x) = f m n h (F.op m x))
    {n : ℕ} {x : Stage n}
    (hclass : AddCommGroup.DirectLimit.of Stage f n x ≠ 0)
    (hx : F.op n x = 0) :
    AddCommGroup.DirectLimit.of Stage f n x ≠ 0 ∧
      directLimitOperator Stage f F hcommutes
        (AddCommGroup.DirectLimit.of Stage f n x) = 0 :=
  ⟨hclass, directLimitOperator_zero_of_stage_zero Stage f F hcommutes hx⟩

end CompatibleOperatorFamily

end InfoGeometry.Canonical.FilteredDirectLimitOperator
