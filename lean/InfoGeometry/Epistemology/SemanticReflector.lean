import Mathlib.CategoryTheory.Adjunction.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Basic

/-!
# Semantic Reflective Adjunction

This module formalizes the category-theoretic structure underlying the repair
of raw mathematical specifications into verified, sound structures.

## Mathematical Framework

Let `RawType` be a category of raw (potentially incomplete or inconsistent)
mathematical specifications, and `SoundType` a full subcategory of verified
structures satisfying all axioms.

The inclusion `i : SoundType ⥤ RawType` embeds verified structures into the
space of raw specifications.

A *reflector* is a left adjoint `R : RawType ⥤ SoundType` to this inclusion.
The adjunction `R ⊣ i` establishes that `R(X)` is the minimal sound structure
realizing any raw specification `X`.

## Universal Property

For any raw `X : RawType` and sound `T : SoundType`, a morphism
`f : X ⟶ i(T)` (a realization of `X` in `T`) factors uniquely through
the unit `η_X : X ⟶ i(R(X))`:

    ∃! f' : R(X) ⟶ T,  f = i(f') ∘ η_X

This makes `R(X)` the initial object in the comma category `(X ↓ i)`,
i.e., the *minimal supporting type* for `X`.

## Application to Formalization

In the context of this repository:
- `RawType` models LLM-generated mathematical text (incomplete, possibly inconsistent)
- `SoundType` models Lean 4 structures with all axioms verified
- The reflector `R` models the repair process: contextual filtration, decomposition,
  and projection onto the rigid theoretical skeleton

The adjunction guarantees that the repaired structure is:
1. **Sound** — all axioms hold
2. **Minimal** — no unnecessary structure is added
3. **Unique** — any other sound realization factors through it
-/

open CategoryTheory

universe u v

noncomputable section

namespace InfoGeometry.Epistemology

variable (RawType : Type u) [Category.{v, u} RawType]
variable (SoundType : Type u) [Category.{v, u} SoundType]

/- The canonical inclusion of sound structures into raw specifications. -/
variable (Inclusion : SoundType ⥤ RawType)

/- The reflector: constructs the minimal sound structure from a raw specification. -/
variable (Repair : RawType ⥤ SoundType)

/- The reflective adjunction: Repair is left adjoint to Inclusion. -/
variable (reflectiveAdj : Repair ⊣ Inclusion)

/-- The unit of the adjunction: the canonical repair map X → i(R(X)). -/
def repairUnit (reflectiveAdj : Repair ⊣ Inclusion) (X : RawType) : X ⟶ Inclusion.obj (Repair.obj X) :=
  reflectiveAdj.unit.app X

/-- The counit of the adjunction: the canonical evaluation R(i(T)) → T. -/
def repairCounit (reflectiveAdj : Repair ⊣ Inclusion) (T : SoundType) : Repair.obj (Inclusion.obj T) ⟶ T :=
  reflectiveAdj.counit.app T

/-- The left triangle identity for the repair unit and counit. -/
theorem repair_unit_counit_triangle
    (reflectiveAdj : Repair ⊣ Inclusion) (X : RawType) :
    Repair.map (repairUnit RawType SoundType Inclusion Repair reflectiveAdj X) ≫
        repairCounit RawType SoundType Inclusion Repair reflectiveAdj (Repair.obj X) =
      𝟙 (Repair.obj X) := by
  exact reflectiveAdj.left_triangle_components X

/-- The right triangle identity for the repair unit and counit. -/
theorem repair_counit_unit_triangle
    (reflectiveAdj : Repair ⊣ Inclusion) (T : SoundType) :
    repairUnit RawType SoundType Inclusion Repair reflectiveAdj (Inclusion.obj T) ≫
        Inclusion.map (repairCounit RawType SoundType Inclusion Repair reflectiveAdj T) =
      𝟙 (Inclusion.obj T) := by
  exact reflectiveAdj.right_triangle_components T

/-- Naturality of the repair unit with respect to raw morphisms. -/
theorem repair_unit_naturality
    (reflectiveAdj : Repair ⊣ Inclusion) {X Y : RawType} (f : X ⟶ Y) :
    f ≫ repairUnit RawType SoundType Inclusion Repair reflectiveAdj Y =
      repairUnit RawType SoundType Inclusion Repair reflectiveAdj X ≫
        Inclusion.map (Repair.map f) := by
  exact reflectiveAdj.unit.naturality f

/-- Naturality of the repair counit with respect to sound morphisms. -/
theorem repair_counit_naturality
    (reflectiveAdj : Repair ⊣ Inclusion) {T U : SoundType} (f : T ⟶ U) :
    Repair.map (Inclusion.map f) ≫
        repairCounit RawType SoundType Inclusion Repair reflectiveAdj U =
      repairCounit RawType SoundType Inclusion Repair reflectiveAdj T ≫ f := by
  exact reflectiveAdj.counit.naturality f

/--
The categorical repair theorem: any sound realization of a raw specification
factors uniquely through the repaired structure.

This is the universal property of the adjunction, restated as an existence
and uniqueness theorem.
-/
theorem repaired_type_is_minimal
    (reflectiveAdj : Repair ⊣ Inclusion)
    (X : RawType) (T : SoundType)
    (f : X ⟶ Inclusion.obj T) :
    ∃! (f' : Repair.obj X ⟶ T),
      f = (reflectiveAdj.homEquiv X T) f' := by
  refine ⟨(reflectiveAdj.homEquiv X T).symm f, ?_, ?_⟩
  · exact ((reflectiveAdj.homEquiv X T).apply_symm_apply f).symm
  · intro g h_eq
    rw [h_eq]
    exact ((reflectiveAdj.homEquiv X T).left_inv g).symm

end InfoGeometry.Epistemology
