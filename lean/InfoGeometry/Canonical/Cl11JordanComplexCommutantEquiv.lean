import InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Subalgebra.Basic

namespace InfoGeometry.Canonical.Cl11JordanComplexCommutantEquiv

open InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge

abbrev Commutant := {T : Mat4R // T ∈ complexStructureCommutant}

noncomputable def commutantSubalgebra : Subalgebra ℝ Mat4R :=
  Subalgebra.centralizer ℝ ({complexStructure} : Set Mat4R)

noncomputable def realifyCommutantHom : Mat2C →ₐ[ℝ] commutantSubalgebra := by
  let f := (realifyRingHom : Mat2C →+* Mat4R)
  exact
    { toFun := fun A => ⟨f A, by
        intro m hm
        have hm' : m = complexStructure := by simpa using hm
        subst m
        exact (realify_commutes_complexStructure A).symm⟩
      map_one' := by
        apply Subtype.ext
        exact realifyRingHom.map_one
      map_mul' := by
        intro A B
        apply Subtype.ext
        exact realifyRingHom.map_mul _ _
      map_zero' := by
        apply Subtype.ext
        exact realifyRingHom.map_zero
      map_add' := by
        intro A B
        apply Subtype.ext
        exact realifyRingHom.map_add _ _
      commutes' := by
        intro r
        apply Subtype.ext
        change f (algebraMap ℝ Mat2C r) = algebraMap ℝ Mat4R r
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        simpa [f, realifyRingHom_apply, realify_one] using realify_real_smul r 1 }

theorem realifyCommutantHom_injective :
    Function.Injective realifyCommutantHom := by
  intro A B h
  apply realify_injective
  exact congrArg Subtype.val h

theorem realifyCommutantHom_surjective :
    Function.Surjective realifyCommutantHom := by
  intro T
  have hT : (T : Mat4R) ∈ complexStructureCommutant := by
    change (T : Mat4R) * complexStructure = complexStructure * (T : Mat4R)
    exact (T.property complexStructure (by simp)).symm
  rw [complexStructureCommutant_eq_range_realify] at hT
  rcases hT with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  apply Subtype.ext
  exact hA

noncomputable def realifyCommutantAlgEquiv :
    Mat2C ≃ₐ[ℝ] commutantSubalgebra :=
  AlgEquiv.ofBijective realifyCommutantHom
    ⟨realifyCommutantHom_injective, realifyCommutantHom_surjective⟩

theorem realifyCommutantAlgEquiv_apply (A : Mat2C) :
    (realifyCommutantAlgEquiv A : Mat4R) = realify A := by
  rfl

theorem realifyCommutantAlgEquiv_symm_apply (T : commutantSubalgebra) :
    realify (realifyCommutantAlgEquiv.symm T) = (T : Mat4R) := by
  exact congrArg Subtype.val (realifyCommutantAlgEquiv.apply_symm_apply T)

end InfoGeometry.Canonical.Cl11JordanComplexCommutantEquiv
