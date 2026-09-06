import proofs.RealPin55KernelReduction

/-! # All anisotropic O(5,5) reflections lie in the Pin image -/

noncomputable section
namespace RealPin55ReflectionGenerators

open Clifford55
open SplitOctonionTKK55
open RealPin55Core
open RealPin55TwistedAction
open RealPin55OrthogonalAction
open RealPin55MatrixRepresentation
open RealOrthogonalGroup55
open V55Fin10Coordinates

def anisotropicPinLift (a : V55) (ha : Q55 a ≠ 0) : FullPin55 :=
  Classical.choose (anisotropicReflection_has_fullPin_lift a ha)

theorem anisotropicPinLift_action (a : V55) (ha : Q55 a ≠ 0) (v : V55) :
    twistedVector (anisotropicPinLift a ha) v = anisotropicReflection a v :=
  Classical.choose_spec (anisotropicReflection_has_fullPin_lift a ha) v

def orthogonalReflection55 (a : V55) (ha : Q55 a ≠ 0) : O55 :=
  fullPinToO55 (anisotropicPinLift a ha)

theorem orthogonalReflection55_mulVec (a : V55) (ha : Q55 a ≠ 0)
    (v : V55) :
    (orthogonalReflection55 a ha).1.1.mulVec
        (v55Fin10Equiv v) =
      v55Fin10Equiv (anisotropicReflection a v) := by
  change ((fullPinMatrixRepresentation (anisotropicPinLift a ha) : M10ˣ) : M10).mulVec
      (v55Fin10Equiv v) = _
  rw [fullPinMatrix_mulVec, anisotropicPinLift_action]

theorem orthogonalReflection55_mem_range (a : V55) (ha : Q55 a ≠ 0) :
    orthogonalReflection55 a ha ∈ MonoidHom.range fullPinToO55 := by
  exact ⟨anisotropicPinLift a ha, rfl⟩

def reflectionGeneratedO55 : Subgroup O55 :=
  Subgroup.closure {r | ∃ (a : V55) (ha : Q55 a ≠ 0),
    r = orthogonalReflection55 a ha}

theorem reflectionGeneratedO55_le_pinRange :
    reflectionGeneratedO55 ≤ MonoidHom.range fullPinToO55 := by
  rw [reflectionGeneratedO55, Subgroup.closure_le]
  intro r hr
  rcases hr with ⟨a, ha, rfl⟩
  exact orthogonalReflection55_mem_range a ha

/-- Once the specialized indefinite Cartan--Dieudonné generation theorem is
proved, surjectivity of the concrete Pin representation is immediate.  This
lemma isolates that final group-theoretic obligation without assuming it. -/
theorem fullPinToO55_surjective_of_reflection_generation
    (hCD : reflectionGeneratedO55 = ⊤) :
    Function.Surjective fullPinToO55 := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← hCD]
  exact reflectionGeneratedO55_le_pinRange

end RealPin55ReflectionGenerators
end noncomputable section
