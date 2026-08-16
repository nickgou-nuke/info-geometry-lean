import InfoGeometry.KK.RealSplitKreinKasparovCycle

namespace InfoGeometry.KK

/-!
# Real Split Krein Resolvent

Primitive resolvent-control interface for the real split-Krein unbounded layer.

This file isolates the first genuinely bounded analytic datum attached to an
unbounded split-Krein Dirac-type operator: a concrete resolvent representative
for a real shift `λ`, together with the left resolvent identity
`(D - λ) ∘ R = 1` and compactness of `R`.
-/

/--
Concrete left-resolvent control for a domain-valued unbounded operator.

This is intentionally smaller than a full unbounded KK regularity package. It
stores only the bounded resolvent representative, its real shift, the domain
preservation needed to evaluate `D` on `R x`, the left resolvent identity, and
compactness of the resolvent.
-/
structure RealSplitKreinResolventData
    (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (domain : Set H)
    (D : {x // x ∈ domain} → H) where
  shift : ℝ
  resolvent : EndH H
  resolvent_preserves_domain : ∀ x : H, resolvent x ∈ domain
  left_resolvent :
    ∀ x : H,
      D ⟨resolvent x, resolvent_preserves_domain x⟩ - shift • resolvent x = x
  compact : IsCompactEnd H resolvent

namespace RealSplitKreinResolventData

variable {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable {domain : Set H}
variable {D : {x // x ∈ domain} → H}

/-- The shifted operator `(D - λ)` evaluated on the domain. -/
def shiftedApply
    (R : RealSplitKreinResolventData H domain D)
    (x : {x // x ∈ domain}) : H :=
  D x - R.shift • x.1

@[simp] lemma resolvent_mem_domain
    (R : RealSplitKreinResolventData H domain D) (x : H) :
    R.resolvent x ∈ domain :=
  R.resolvent_preserves_domain x

@[simp] lemma shiftedApply_resolvent
    (R : RealSplitKreinResolventData H domain D) (x : H) :
    R.shiftedApply ⟨R.resolvent x, R.resolvent_mem_domain x⟩ = x :=
  R.left_resolvent x

/-- The stored left-resolvent identity makes the shifted operator surjective.

This is the exact algebraic consequence available from the packet; no right
resolvent identity is inferred. -/
lemma shiftedApply_surjective
    (R : RealSplitKreinResolventData H domain D) :
    Function.Surjective R.shiftedApply := by
  intro x
  exact ⟨⟨R.resolvent x, R.resolvent_mem_domain x⟩,
    R.shiftedApply_resolvent x⟩

/-- A left inverse forces the bounded resolvent representative to be injective. -/
lemma resolvent_injective
    (R : RealSplitKreinResolventData H domain D) :
    Function.Injective R.resolvent := by
  intro x y hxy
  calc
    x = R.shiftedApply ⟨R.resolvent x, R.resolvent_mem_domain x⟩ :=
      (R.shiftedApply_resolvent x).symm
    _ = R.shiftedApply ⟨R.resolvent y, R.resolvent_mem_domain y⟩ := by
      apply congrArg R.shiftedApply
      apply Subtype.ext
      exact hxy
    _ = y := R.shiftedApply_resolvent y

/-- If the shifted operator is also injective, the stored left inverse is a
right inverse on the operator domain. -/
lemma resolvent_shiftedApply
    (R : RealSplitKreinResolventData H domain D)
    (hinj : Function.Injective R.shiftedApply)
    (x : {x // x ∈ domain}) :
    R.resolvent (R.shiftedApply x) = x.1 := by
  have hsub :
      (⟨R.resolvent (R.shiftedApply x),
          R.resolvent_mem_domain (R.shiftedApply x)⟩ : {x // x ∈ domain}) = x := by
    apply hinj
    simp only [R.shiftedApply_resolvent]
  exact congrArg Subtype.val hsub

/-- The concrete resolvent representative is compact as a bounded operator. -/
lemma isCompactOperator
    (R : RealSplitKreinResolventData H domain D) :
    IsCompactOperator ((R.resolvent : EndH H) : H → H) := by
  simpa [IsCompactEnd] using R.compact

/-- Postcomposing the resolvent by any bounded endomorphism stays compact. -/
lemma comp_left_isCompactEnd
    (R : RealSplitKreinResolventData H domain D) (T : EndH H) :
    IsCompactEnd H (T.comp R.resolvent) := by
  simpa [IsCompactEnd] using
    IsCompactOperator.clm_comp (hf := R.isCompactOperator) (g := T)

/-- Precomposing the resolvent by any bounded endomorphism stays compact. -/
lemma comp_right_isCompactEnd
    (R : RealSplitKreinResolventData H domain D) (T : EndH H) :
    IsCompactEnd H (R.resolvent.comp T) := by
  simpa [IsCompactEnd] using
    IsCompactOperator.comp_clm (hf := R.isCompactOperator) (g := T)

end RealSplitKreinResolventData

end InfoGeometry.KK
