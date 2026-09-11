import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CliffordEquiv

open InfoGeometry.Canonical.CliffordEquiv
open CliffordAlgebra

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (C : AbstractComplexStructure V)

-- Define AlgEquiv
def complexLiftAlgEquiv {A : Type*} [Ring A] [Algebra ℝ A] [Nontrivial A]
    (S : A) (hS : S * S = -1) : ℂ ≃ₐ[ℝ] complexSubalgebra S hS :=
  AlgEquiv.ofBijective ((complexLift S hS).rangeRestrict) ⟨by
    intro x y h
    have h_lin : (complexLiftEquiv S hS) x = (complexLiftEquiv S hS) y := by
      ext
      have h_eq : ((complexLift S hS).rangeRestrict x : A) = ((complexLift S hS).rangeRestrict y : A) := by
        exact congrArg Subtype.val h
      exact h_eq
    exact (complexLiftEquiv S hS).injective h_lin,
    by
    intro ⟨x, hx⟩
    rcases hx with ⟨z, rfl⟩
    use z
    ext
    rfl⟩

-- Now define the module over the clifford bivector algebra
abbrev CliffordBivectorSubalgebra := complexSubalgebra cliffordBivector cliffordBivector_sq

-- Let V be a complex module via C
noncomputable def hestenesKreinCliffordModule : Module CliffordBivectorSubalgebra V :=
  letI : Module ℂ V := inducedComplexModule C
  Module.compHom V (complexLiftAlgEquiv cliffordBivector cliffordBivector_sq).symm.toAlgHom.toRingHom

