import InfoGeometry.Canonical.SplitSpinorCARAlgebraBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exterior-spinor chirality bridge

The exterior-algebra spinor carrier has an intrinsic parity involution: every
degree-one generator changes sign.  This is the algebraic chirality operator.
It is kept separate from the recursive `Cl(5,5)` matrix chirality carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExteriorSpinorChiralityBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.SplitSpinorCARAlgebraBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Grade involution on the exterior-spinor carrier. -/
def gradeInvolution : ExteriorAlgebra R V →ₐ[R] ExteriorAlgebra R V :=
  ExteriorAlgebra.lift R
    ⟨-(ExteriorAlgebra.ι R : V →ₗ[R] ExteriorAlgebra R V), by
      intro v
      simp⟩

@[simp] theorem gradeInvolution_ι (v : V) :
    gradeInvolution (ExteriorAlgebra.ι R v) = -ExteriorAlgebra.ι R v := by
  exact ExteriorAlgebra.lift_ι_apply R _ _ v

theorem gradeInvolution_comp_self :
    gradeInvolution.comp gradeInvolution = AlgHom.id R (ExteriorAlgebra R V) := by
  apply ExteriorAlgebra.hom_ext
  ext v
  simp [gradeInvolution]

theorem gradeInvolution_involutive (ψ : ExteriorAlgebra R V) :
    gradeInvolution (gradeInvolution ψ) = ψ := by
  have h := congrArg (fun f : ExteriorAlgebra R V →ₐ[R] ExteriorAlgebra R V => f ψ)
    (gradeInvolution_comp_self (R := R) (V := V))
  simpa using h

theorem gradeInvolution_sq (ψ : ExteriorAlgebra R V) :
    gradeInvolution (gradeInvolution ψ) = ψ :=
  gradeInvolution_involutive ψ

abbrev Spinor (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  SplitSpinorCARAlgebraBridge.Spinor R V

/-- The parity involution on the literal exterior-spinor carrier. -/
def spinorGradeInvolution : Spinor R V →ₐ[R] Spinor R V :=
  gradeInvolution (R := R) (V := Module.Dual R V)

@[simp] theorem spinorGradeInvolution_ι (alpha : Module.Dual R V) :
    spinorGradeInvolution (ExteriorAlgebra.ι R alpha) =
      -ExteriorAlgebra.ι R alpha := by
  exact gradeInvolution_ι alpha

/-- Creation operators reverse parity under the exterior-spinor involution. -/
theorem gradeInvolution_creation (alpha : Module.Dual R V) (ψ : Spinor R V) :
    spinorGradeInvolution (creation alpha ψ) =
      -(creation alpha (spinorGradeInvolution ψ)) := by
  change spinorGradeInvolution (ExteriorAlgebra.ι R alpha * ψ) =
    -(ExteriorAlgebra.ι R alpha * spinorGradeInvolution ψ)
  rw [map_mul, spinorGradeInvolution_ι]
  simp

end InfoGeometry.Canonical.ExteriorSpinorChiralityBridge
