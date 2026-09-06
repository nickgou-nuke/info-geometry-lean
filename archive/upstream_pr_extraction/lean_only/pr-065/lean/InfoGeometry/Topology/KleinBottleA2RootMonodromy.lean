import Mathlib

namespace InfoGeometry.Topology

/-!
# Klein Bottle A₂ Root Monodromy Data

This module formalizes the algebraic signature for the monodromy representation of the fundamental group of the Klein bottle into the Weyl group W(A₂) ≅ S₃.

The Klein bottle fundamental group π₁(K) has presentation ⟨g, t | g t g⁻¹ = t⁻¹⟩.
When we impose a cubic quotient on the translation t³ = 1, we obtain the Weyl group W(A₂) ≅ S₃ ≅ ℤ₃ ⋊ ℤ₂.

This is the algebraic realization of an A₂ root local system over a Klein bottle
with glide-twisted cyclotomic monodromy.
-/

namespace InfoGeometry.Topology.KleinBottleA2RootMonodromy

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/--
The Klein bottle monodromy data with cubic translation and glide reflection.

The translation t represents the cyclotomic rotation (order 3), corresponding to the Coxeter element of the A₂ root system.
The glide g represents the orientation-reversing reflection (order 2).
The conjugation relation g t g⁻¹ = t⁻¹ encodes the dihedral symmetry of the A₂ root system.
-/
structure KleinBottleA2RootMonodromyData
    (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  /-- Translation generator t (cubic rotation / Coxeter element of A₂) -/
  translation : V ≃ₗ[K] V

  /-- Glide reflection generator g (orientation-reversing) -/
  glide : V ≃ₗ[K] V

  /-- Cubic relation: t³ = 1 (Coxeter rotation of order 3) -/
  translation_cube : translation ^ 3 = 1

  /-- Quadratic relation: g² = 1 (reflection of order 2) -/
  glide_square : glide ^ 2 = 1

  /--
  The Klein bottle conjugation law: g t g⁻¹ = t⁻¹

  This is the Weyl group relation: the reflection conjugates the Coxeter rotation to its inverse.
  -/
  glide_conj_translation : glide * translation * glide.symm = translation.symm

/--
The fundamental group π₁(K) maps to S₃ ≅ W(A₂).
The translation maps to the Coxeter rotation (order 3), the glide maps to a reflection (order 2).
The conjugation law is exactly the dihedral presentation of S₃.
-/
theorem kleinBottleA2RootMonodromy_factors_through_S3
    (data : KleinBottleA2RootMonodromyData K V) :
    data.translation ^ 3 = 1 ∧
      data.glide ^ 2 = 1 ∧
      data.glide * data.translation * data.glide.symm =
        data.translation.symm := by
  exact ⟨data.translation_cube, data.glide_square,
    data.glide_conj_translation⟩

end InfoGeometry.Topology.KleinBottleA2RootMonodromy
