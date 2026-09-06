import InfoGeometry.Canonical.FilteredDirectLimitOperator

noncomputable section

namespace InfoGeometry.Canonical.FilteredDirectLimitOperator

universe u

variable
    (Stage : ℕ → Type u)
    [∀ n, AddCommGroup (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)

namespace CompatibleOperatorFamily

variable (F : CompatibleOperatorFamily Stage)

/-- The Mathlib direct-limit lift is the unique additive endomorphism agreeing
with the finite-stage operator family on canonical classes. -/
theorem directLimitOperator_unique
    (hcommutes :
      ∀ (m n : ℕ) (h : m ≤ n) (x : Stage m),
        F n (f m n h x) = f m n h (F m x))
    (T :
      AddCommGroup.DirectLimit Stage f →+
        AddCommGroup.DirectLimit Stage f)
    (hT :
      ∀ n x,
        T (AddCommGroup.DirectLimit.of Stage f n x) =
          AddCommGroup.DirectLimit.of Stage f n (F n x)) :
    T = directLimitOperator Stage f F hcommutes := by
  apply AddMonoidHom.ext
  intro z
  refine AddCommGroup.DirectLimit.induction_on z ?_
  intro n x
  rw [hT n x]
  symm
  exact directLimitOperator_of Stage f F hcommutes n x

/-- Two additive endomorphisms of the direct limit are equal whenever they
agree with the same finite-stage operator family. -/
theorem directLimitDescent_ext
    (hcommutes :
      ∀ (m n : ℕ) (h : m ≤ n) (x : Stage m),
        F n (f m n h x) = f m n h (F m x))
    (T U :
      AddCommGroup.DirectLimit Stage f →+
        AddCommGroup.DirectLimit Stage f)
    (hT :
      ∀ n x,
        T (AddCommGroup.DirectLimit.of Stage f n x) =
          AddCommGroup.DirectLimit.of Stage f n (F n x))
    (hU :
      ∀ n x,
        U (AddCommGroup.DirectLimit.of Stage f n x) =
          AddCommGroup.DirectLimit.of Stage f n (F n x)) :
    T = U := by
  rw [F.directLimitOperator_unique Stage f hcommutes T hT]
  symm
  exact F.directLimitOperator_unique Stage f hcommutes U hU

/-- The induced operator is characterized by existence and uniqueness together
with its finite-stage evaluation law. -/
theorem existsUnique_directLimitOperator :
    (hcommutes :
      ∀ (m n : ℕ) (h : m ≤ n) (x : Stage m),
        F n (f m n h x) = f m n h (F m x)) →
    ∃! T :
      AddCommGroup.DirectLimit Stage f →+
        AddCommGroup.DirectLimit Stage f,
      ∀ n x,
        T (AddCommGroup.DirectLimit.of Stage f n x) =
          AddCommGroup.DirectLimit.of Stage f n (F n x) := by
  intro hcommutes
  refine ⟨directLimitOperator Stage f F hcommutes, ?_, ?_⟩
  · intro n x
    exact directLimitOperator_of Stage f F hcommutes n x
  · intro T hT
    exact F.directLimitOperator_unique Stage f hcommutes T hT

end CompatibleOperatorFamily

end InfoGeometry.Canonical.FilteredDirectLimitOperator
