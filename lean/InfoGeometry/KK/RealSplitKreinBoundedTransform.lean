import InfoGeometry.KK.RealSplitKreinUnboundedCycle
import InfoGeometry.KK.CompactOperatorBridge
import InfoGeometry.KK.KasparovCycle

open scoped InnerProductSpace

namespace InfoGeometry.KK

open InfoGeometry.Krein

/-!
# Real Split Krein Bounded Transform

First bounded-transform bridge from the primitive unbounded split-Krein cycle.

The current repository does not yet formalize the full unbounded functional
calculus needed for the canonical phase `D (1 + D²)^(-1/2)`. The genuinely
available bounded analytic datum is instead the compact resolvent
representative already packaged in `RealSplitKreinResolventData`.

This file uses that resolvent as the canonical bounded phase and makes the
remaining bounded-cycle hypotheses explicit exactly where the present
infrastructure still needs them: oddness, bounded-phase Krein skew-adjointness,
and compactness of `F² - 1`.
-/

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
/-- Compact endomorphisms are closed under negation. -/
lemma isCompactEnd_neg {T : EndH H}
    (hT : IsCompactEnd H T) :
    IsCompactEnd H (-T) := by
  simpa [IsCompactEnd] using (IsCompactOperator.neg hT)

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
/-- Compact endomorphisms are closed under subtraction. -/
lemma isCompactEnd_sub {S T : EndH H}
    (hS : IsCompactEnd H S) (hT : IsCompactEnd H T) :
    IsCompactEnd H (S - T) := by
  simpa [IsCompactEnd] using (IsCompactOperator.sub hS hT)

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
/-- Postcomposition of a compact endomorphism by a bounded endomorphism stays compact. -/
lemma isCompactEnd_comp_right {S T : EndH H}
    (hS : IsCompactEnd H S) :
    IsCompactEnd H (S.comp T) := by
  simpa [IsCompactEnd] using
    IsCompactOperator.comp_clm (hf := hS) (g := T)

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
/-- Precomposition of a compact endomorphism by a bounded endomorphism stays compact. -/
lemma isCompactEnd_comp_left {S T : EndH H}
    (hT : IsCompactEnd H T) :
    IsCompactEnd H (S.comp T) := by
  simpa [IsCompactEnd] using
    IsCompactOperator.clm_comp (hf := hT) (g := S)

/-- Grading conjugation preserves compactness of bounded endomorphisms. -/
lemma gradeConj_compact {T : EndH H}
    (hT : IsCompactEnd H T) :
    IsCompactEnd H (KreinGradedModule.gradeConj (H := H) T) := by
  unfold KreinGradedModule.gradeConj
  exact isCompactEnd_comp_left
    (S := KreinGradedModule.gradeCLM (H := H))
    (isCompactEnd_comp_right
      (T := KreinGradedModule.gradeCLM (H := H))
      hT)

/-- The grading-even part of a compact endomorphism is compact. -/
lemma evenPart_compact {T : EndH H}
    (hT : IsCompactEnd H T) :
    IsCompactEnd H (KreinGradedModule.evenPart (H := H) T) := by
  unfold KreinGradedModule.evenPart
  exact isCompactEnd_smul (2 : ℝ)⁻¹
    (isCompactEnd_add hT (gradeConj_compact hT))

/-- The grading-odd part of a compact endomorphism is compact. -/
lemma oddPart_compact {T : EndH H}
    (hT : IsCompactEnd H T) :
    IsCompactEnd H (KreinGradedModule.oddPart (H := H) T) := by
  unfold KreinGradedModule.oddPart
  exact isCompactEnd_smul (2 : ℝ)⁻¹
    (isCompactEnd_sub hT (gradeConj_compact hT))

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
/-- If the left factor is compact, the ordinary commutator is compact. -/
lemma comm_isCompactEnd_of_left_compact {S T : EndH H}
    (hS : IsCompactEnd H S) :
    IsCompactEnd H (KreinGradedModule.comm (H := H) S T) := by
  unfold KreinGradedModule.comm
  exact isCompactEnd_sub
    (isCompactEnd_comp_right (T := T) hS)
    (isCompactEnd_comp_left (S := T) hS)

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
/-- If the left factor is compact, the ordinary anticommutator is compact. -/
lemma anticomm_isCompactEnd_of_left_compact {S T : EndH H}
    (hS : IsCompactEnd H S) :
    IsCompactEnd H (KreinGradedModule.anticomm (H := H) S T) := by
  unfold KreinGradedModule.anticomm
  exact isCompactEnd_add
    (isCompactEnd_comp_right (T := T) hS)
    (isCompactEnd_comp_left (S := T) hS)

/-- If the left factor is compact, the graded commutator is compact. -/
lemma superComm_isCompactEnd_of_left_compact {S T : EndH H}
    (hS : IsCompactEnd H S) :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) S T) := by
  unfold KreinGradedModule.superComm
  have hEven : IsCompactEnd H (KreinGradedModule.evenPart (H := H) S) :=
    evenPart_compact hS
  have hOdd : IsCompactEnd H (KreinGradedModule.oddPart (H := H) S) :=
    oddPart_compact hS
  exact isCompactEnd_add
    (isCompactEnd_add
      (isCompactEnd_add
        (comm_isCompactEnd_of_left_compact (T := KreinGradedModule.evenPart (H := H) T) hEven)
        (comm_isCompactEnd_of_left_compact (T := KreinGradedModule.oddPart (H := H) T) hEven))
      (comm_isCompactEnd_of_left_compact (T := KreinGradedModule.evenPart (H := H) T) hOdd))
    (anticomm_isCompactEnd_of_left_compact (T := KreinGradedModule.oddPart (H := H) T) hOdd)

/--
Primitive bounded-transform bridge data over the unbounded split-Krein cycle.

The bounded phase is canonically chosen to be the concrete resolvent carried by
the unbounded cycle. The bridge records exactly the remaining phase properties
that are not yet derivable from the present resolvent packet alone.
-/
structure RealSplitKreinBoundedTransform
    (X : RealSplitKreinUnboundedCycle A B H) where
  phase_odd :
    KreinGradedModule.IsOdd (H := H) X.resolvent
  phase_krein_skewAdj :
    KreinSpace.IsKreinSkewAdjoint (H := H) X.resolvent
  phase_sq_one_compact :
    IsCompactEnd H (X.resolvent * X.resolvent - (1 : EndH H))

namespace RealSplitKreinBoundedTransform

variable {X : RealSplitKreinUnboundedCycle A B H}
variable (T : RealSplitKreinBoundedTransform X)

/-- The canonical bounded phase associated to the unbounded cycle. -/
abbrev phase (_T : RealSplitKreinBoundedTransform X) : EndH H :=
  X.resolvent

@[simp] theorem phase_eq_resolvent :
    phase T = X.resolvent := rfl

/-- The canonical bounded phase is compact because it is the chosen resolvent. -/
theorem phase_compact :
    IsCompactEnd H (phase T) :=
  RealSplitKreinUnboundedCycle.resolvent_compact X

/-- The canonical bounded phase is odd. -/
theorem phase_isOdd :
    KreinGradedModule.IsOdd (H := H) (phase T) :=
  RealSplitKreinBoundedTransform.phase_odd T

/-- The canonical bounded phase is Krein-skew-adjoint. -/
theorem phase_isKreinSkewAdjoint :
    KreinSpace.IsKreinSkewAdjoint (H := H) (phase T) :=
  RealSplitKreinBoundedTransform.phase_krein_skewAdj T

/-- The canonical bounded phase satisfies the primitive `F² - 1` compactness law. -/
theorem phase_sq_one_isCompact :
    IsCompactEnd H (phase T * phase T - (1 : EndH H)) :=
  RealSplitKreinBoundedTransform.phase_sq_one_compact T

/-- The bounded-phase commutator with the `A`-action is compact. -/
theorem phase_commutator_compact (a : A) :
    IsCompactEnd H (phase T * (X.π a) - (X.π a) * phase T) := by
  exact isCompactEnd_sub
    (isCompactEnd_comp_right (T := X.π a) (phase_compact T))
    (isCompactEnd_comp_left (S := X.π a) (phase_compact T))

/-- The bounded-phase graded commutator with `ε` is compact. -/
theorem phase_superComm_eps_compact :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) (phase T) X.cl11.eps) :=
  superComm_isCompactEnd_of_left_compact (phase_compact T)

/-- The bounded-phase graded commutator with `J` is compact. -/
theorem phase_superComm_J_compact :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) (phase T) X.cl11.J) :=
  superComm_isCompactEnd_of_left_compact (phase_compact T)

/--
Package the unbounded primitive cycle and its bounded-transform bridge as a
primitive bounded real split-Krein Kasparov cycle.
-/
noncomputable def toRealSplitKreinKasparovCycle :
    RealSplitKreinKasparovCycle A B H where
  cl11 := X.cl11
  π := X.π
  ρ := X.ρ
  π_even := X.π_even
  ρ_even := X.ρ_even
  F := phase T
  F_odd := phase_isOdd T
  F_skewAdj := phase_isKreinSkewAdjoint T
  F_sq_one_compact := phase_sq_one_isCompact T
  comm_compact := phase_commutator_compact T
  superComm_eps_compact := phase_superComm_eps_compact T
  superComm_J_compact := phase_superComm_J_compact T

/-- Forget the split-`Cl(1,1)` data and keep the bounded KK compatibility surface. -/
noncomputable def toKasparovCycle :
    KasparovCycle A B H :=
  RealSplitKreinKasparovCycle.toKasparovCycle
    (toRealSplitKreinKasparovCycle T)

@[simp] theorem toRealSplitKreinKasparovCycle_F :
    (toRealSplitKreinKasparovCycle T).F = X.resolvent := rfl

@[simp] theorem toKasparovCycle_F :
    (toKasparovCycle T).F = X.resolvent := rfl

end RealSplitKreinBoundedTransform

end InfoGeometry.KK
