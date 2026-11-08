import InfoGeometry.Spectral.Algebra.GenericDerivedCouple
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Iteration of derived graded exact couples

Derivation changes both graded module families and the degree maps.  To iterate
it without custom evidence records, a stage is represented by a dependent
sigma of Mathlib `ModuleCat` families, degree equivalences, and the exact
couple they support.  The proved generic derivation is then an endomorphism of
this sigma, so ordinary function iteration constructs every derived page.
-/

namespace InfoGeometry.Spectral.Algebra

open CategoryTheory

universe u v

namespace GradedExactCouple

/-- A dependently bundled graded exact-couple stage using Mathlib modules. -/
abbrev Stage (R : Type u) [Ring R] (I : Type v) :=
  Σ D : I → ModuleCat.{u} R,
  Σ E : I → ModuleCat.{u} R,
  Σ iDeg : I ≃ I,
  Σ jDeg : I ≃ I,
  Σ kDeg : I ≃ I,
    GradedExactCouple R I
      (fun p => (D p : Type u))
      (fun p => (E p : Type u))
      iDeg jDeg kDeg

/-- Bundle an existing graded exact couple as a Mathlib-module stage. -/
def toStage
    {R : Type u} [Ring R] {I : Type v}
    {D E : I → Type u}
    [∀ p, AddCommGroup (D p)] [∀ p, AddCommGroup (E p)]
    [∀ p, Module R (D p)] [∀ p, Module R (E p)]
    {iDeg jDeg kDeg : I ≃ I}
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) :
    Stage R I :=
  ⟨fun p => ModuleCat.of R (D p),
    fun p => ModuleCat.of R (E p),
    iDeg, jDeg, kDeg, C⟩

/-- Apply the proved generic derived-couple construction to one stage. -/
noncomputable def deriveStage
    {R : Type u} [Ring R] {I : Type v} :
    Stage R I → Stage R I
  | ⟨_, _, iDeg, jDeg, kDeg, C⟩ =>
      ⟨fun p => ModuleCat.of R (C.DirectDerivedD p),
        fun p => ModuleCat.of R (C.DirectDerivedE p),
        derivedIDegree iDeg,
        derivedJDegree iDeg jDeg,
        derivedKDegree kDeg,
        C.derived⟩

/-- The `n`-fold derived exact-couple stage. -/
noncomputable def iteratedStage
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) (n : ℕ) : Stage R I :=
  (deriveStage (R := R) (I := I))^[n] S

@[simp]
theorem iteratedStage_zero
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) :
    iteratedStage S 0 = S :=
  rfl

@[simp]
theorem iteratedStage_succ
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) (n : ℕ) :
    iteratedStage S (n + 1) =
      deriveStage (iteratedStage S n) := by
  simp [iteratedStage, Function.iterate_succ_apply']

/-- Iteration is additive in the number of derived-page steps. -/
theorem iteratedStage_add
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) (m n : ℕ) :
    iteratedStage S (m + n) =
      iteratedStage (iteratedStage S n) m := by
  simp [iteratedStage, Function.iterate_add_apply]

/-- The `D` family of a bundled exact-couple stage. -/
abbrev Stage.D
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) : I → ModuleCat.{u} R :=
  S.1

/-- The `E` family of a bundled exact-couple stage. -/
abbrev Stage.E
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) : I → ModuleCat.{u} R :=
  S.2.1

/-- The first degree equivalence of a stage. -/
abbrev Stage.iDeg
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) : I ≃ I :=
  S.2.2.1

/-- The second degree equivalence of a stage. -/
abbrev Stage.jDeg
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) : I ≃ I :=
  S.2.2.2.1

/-- The third degree equivalence of a stage. -/
abbrev Stage.kDeg
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) : I ≃ I :=
  S.2.2.2.2.1

/-- The proved exact couple carried by a stage. -/
abbrev Stage.couple
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) :
    GradedExactCouple R I
      (fun p => (S.D p : Type u))
      (fun p => (S.E p : Type u))
      S.iDeg S.jDeg S.kDeg :=
  S.2.2.2.2.2

/-- The `E` module on the `n`th derived page. -/
noncomputable abbrev page
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) (n : ℕ) (p : I) : ModuleCat.{u} R :=
  (iteratedStage S n).E p

/-- The degree of the differential on the `n`th page. -/
noncomputable abbrev pageDifferentialDegree
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) (n : ℕ) : I ≃ I :=
  (iteratedStage S n).couple.differentialDegree

/-- The differential on the `n`th iterated page. -/
noncomputable def pageDifferential
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) (n : ℕ) (p : I) :
    (page S n p : Type u) →ₗ[R]
      (page S n (pageDifferentialDegree S n p) : Type u) :=
  (iteratedStage S n).couple.differential p

/-- Every iterated page differential squares to zero. -/
theorem pageDifferential_comp_pageDifferential
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) (n : ℕ) (p : I) :
    (pageDifferential S n (pageDifferentialDegree S n p)).comp
        (pageDifferential S n p) = 0 :=
  (iteratedStage S n).couple.differential_comp_differential p

/--
The next `E` page is the native homology family of the current differential.
-/
theorem iteratedStage_succ_E
    {R : Type u} [Ring R] {I : Type v}
    (S : Stage R I) (n : ℕ) (p : I) :
    (iteratedStage S (n + 1)).E p =
      ModuleCat.of R
        ((iteratedStage S n).couple.DirectDerivedE p) := by
  rw [iteratedStage_succ]
  rcases iteratedStage S n with
    ⟨D, E, iDeg, jDeg, kDeg, C⟩
  rfl

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
