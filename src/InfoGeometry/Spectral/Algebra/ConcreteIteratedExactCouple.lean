import InfoGeometry.Spectral.Algebra.IteratedDerivedCouple
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Iterated pages of the concrete bidegree exact couple

This file embeds the repository's original `Z2` exact couple into the generic
Mathlib-module stage tower.  It identifies the zeroth page and differential
with the existing concrete definitions and exposes every successor as native
homology of the preceding page.
-/

namespace InfoGeometry.Spectral.Algebra

universe u

namespace ExactCouple

variable {R : Type u} [Ring R]
variable {D E : Z2 → Type u}
variable [∀ p, AddCommGroup (D p)] [∀ p, AddCommGroup (E p)]
variable [∀ p, Module R (D p)] [∀ p, Module R (E p)]

/-- The concrete bidegree exact couple as an iterable Mathlib-module stage. -/
def initialStage (C : ExactCouple R D E) :
    GradedExactCouple.Stage R Z2 :=
  C.toGradedExactCouple.toStage

/-- The `n`th derived stage of a concrete bidegree exact couple. -/
noncomputable def iteratedGradedStage
    (C : ExactCouple R D E) (n : ℕ) :
    GradedExactCouple.Stage R Z2 :=
  GradedExactCouple.iteratedStage C.initialStage n

/-- The `E` module in bidegree `p` on the `n`th concrete page. -/
noncomputable abbrev IteratedPage
    (C : ExactCouple R D E) (n : ℕ) (p : Z2) :=
  GradedExactCouple.page C.initialStage n p

/-- The degree equivalence of the differential on the `n`th concrete page. -/
noncomputable abbrev iteratedDifferentialDegree
    (C : ExactCouple R D E) (n : ℕ) : Z2 ≃ Z2 :=
  GradedExactCouple.pageDifferentialDegree C.initialStage n

/-- The differential on the `n`th concrete page. -/
noncomputable def iteratedDifferential
    (C : ExactCouple R D E) (n : ℕ) (p : Z2) :
    (C.IteratedPage n p : Type u) →ₗ[R]
      (C.IteratedPage n (C.iteratedDifferentialDegree n p) : Type u) :=
  GradedExactCouple.pageDifferential C.initialStage n p

@[simp]
theorem iteratedGradedStage_zero
    (C : ExactCouple R D E) :
    C.iteratedGradedStage 0 = C.initialStage :=
  rfl

@[simp]
theorem iteratedGradedStage_succ
    (C : ExactCouple R D E) (n : ℕ) :
    C.iteratedGradedStage (n + 1) =
      GradedExactCouple.deriveStage (C.iteratedGradedStage n) :=
  GradedExactCouple.iteratedStage_succ C.initialStage n

@[simp]
theorem IteratedPage_zero
    (C : ExactCouple R D E) (p : Z2) :
    C.IteratedPage 0 p = ModuleCat.of R (E p) :=
  rfl

@[simp]
theorem iteratedDifferentialDegree_zero_apply
    (C : ExactCouple R D E) (p : Z2) :
    C.iteratedDifferentialDegree 0 p = shiftK p :=
  rfl

@[simp]
theorem iteratedDifferential_zero
    (C : ExactCouple R D E) (p : Z2) :
    C.iteratedDifferential 0 p = C.differential p :=
  rfl

/-- Every differential on every concrete derived page squares to zero. -/
theorem iteratedDifferential_comp_iteratedDifferential
    (C : ExactCouple R D E) (n : ℕ) (p : Z2) :
    (C.iteratedDifferential n
        (C.iteratedDifferentialDegree n p)).comp
      (C.iteratedDifferential n p) = 0 :=
  GradedExactCouple.pageDifferential_comp_pageDifferential
    C.initialStage n p

/-- The next concrete page is the native homology family of the current stage. -/
theorem IteratedPage_succ
    (C : ExactCouple R D E) (n : ℕ) (p : Z2) :
    (C.iteratedGradedStage (n + 1)).E p =
      ModuleCat.of R
        ((C.iteratedGradedStage n).couple.DirectDerivedE p) :=
  GradedExactCouple.iteratedStage_succ_E C.initialStage n p

end ExactCouple

end InfoGeometry.Spectral.Algebra
