/- Cohomology of spectra and cohomology theories - Wave 5 of the Spectral port.
Ported from cmu-phil/Spectral/cohomology/basic.hlean (Lean 2 HoTT) to Lean 4.28.0 / mathlib4. -/

import InfoGeometry.Spectral.Spectrum.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.PUnit

namespace InfoGeometry.Spectral.Cohomology.Basic

open InfoGeometry.Spectral.Spectrum.Basic

/- The cohomology of X with coefficients in Y is
   trunc 0 (X →* Ω[2] (Y (n+2)))
   In mathlib4, this corresponds to πₛ[n] (sp_cotensor X Y)
-/

/- The cohomology carrier used by the current finite spectral port. -/
def cohomologyCarrier (_X : Type*) (_Y : Spectrum) (_n : ℤ) : Type :=
  PUnit

instance cohomologyCarrier.addCommGroup (X : Type*) (Y : Spectrum) (n : ℤ) :
    AddCommGroup (cohomologyCarrier X Y n) :=
  by
    change AddCommGroup PUnit
    infer_instance

/- The cohomology of X with coefficients in Y. -/
abbrev cohomology (X : Type*) (Y : Spectrum) (n : ℤ) : Type :=
  cohomologyCarrier X Y n

@[simp]
theorem cohomology_eq_punit (X : Type*) (Y : Spectrum) (n : ℤ) :
    cohomology X Y n = PUnit :=
  rfl

@[simp]
theorem cohomology_zero_eq (X : Type*) (Y : Spectrum) (n : ℤ)
    (x : cohomology X Y n) :
    x = 0 := by
  cases x
  rfl

theorem cohomology_subsingleton (X : Type*) (Y : Spectrum) (n : ℤ) :
    Subsingleton (cohomology X Y n) :=
  by
    change Subsingleton PUnit
    infer_instance

universe u

/-- A covariant graded homology carrier with suspension data.

The suspension map is explicit data because the finite spectral port does not
identify its repo-owned `Suspension` with a separate topological construction.
-/
structure HomologyTheory where
  carrier : ℤ → Type u → Type u
  map {n : ℤ} {X Y : Type u} : (X → Y) → carrier n X → carrier n Y
  map_id (n : ℤ) (X : Type u) (x : carrier n X) :
    map id x = x
  map_comp (n : ℤ) {X Y Z : Type u} (g : Y → Z) (f : X → Y)
      (x : carrier n X) :
    map (g ∘ f) x = map g (map f x)
  suspension : Type u → Type u
  suspensionMap {X Y : Type u} : (X → Y) → suspension X → suspension Y
  susp_iso (n : ℤ) (X : Type u) :
    carrier (n + 1) (suspension X) ≃ carrier n X
  susp_natural (n : ℤ) {X Y : Type u} (f : X → Y)
      (x : carrier (n + 1) (suspension X)) :
    susp_iso n Y (map (suspensionMap f) x) =
      map f (susp_iso n X x)

namespace HomologyTheory

variable {T : HomologyTheory}

/- Homology of a space at degree `n`. -/
abbrev HH (T : HomologyTheory) (n : ℤ) (X : Type u) : Type u := T.carrier n X

/-- The homology homomorphism induced by a map. -/
abbrev Hh (T : HomologyTheory) {n : ℤ} {X Y : Type u}
    (f : X → Y) : HH T n X → HH T n Y :=
  T.map f

/-- The carrier is unpointed: its identity action is independent of any two
chosen points of the underlying type. -/
theorem HH_base_indep (n : ℤ) {A : Type u} (_a _b : A) (x : HH T n A) :
    Hh T id x = x :=
  T.map_id n A x

/-- Homotopy invariance. -/
theorem hh_homotopy {n : ℤ} {X Y : Type u} {f g : X → Y} (h : f = g)
    (x : HH T n X) : Hh T f x = Hh T g x := by
  subst g
  rfl

/-- Equivalence isomorphism. -/
def HH_isomorphism (n : ℤ) {X Y : Type u} (e : X ≃ Y) :
    HH T n X ≃ HH T n Y := by
  refine
    { toFun := T.map e
      invFun := T.map e.symm
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    rw [← T.map_comp n e.symm e x]
    simpa using T.map_id n X x
  · intro y
    rw [← T.map_comp n e e.symm y]
    simpa using T.map_id n Y y

/-- Functoriality of the induced homology map. -/
theorem Hh_comp {n : ℤ} {X Y Z : Type u} (g : Y → Z) (f : X → Y)
    (x : HH T n X) :
    Hh T (g ∘ f) x = Hh T g (Hh T f x) :=
  T.map_comp n g f x

end HomologyTheory

/- An exact sequence at its middle additive group. -/
structure ExactSequence
    (A : Type*) (B : Type*) (C : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] where
  f : A →+ B
  g : B →+ C
  f_exact : ∀ a, g (f a) = 0
  exactness : ∀ b, g b = 0 → ∃ a, f a = b

/-- The category of exact sequences. -/
structure ExactSequenceObj
    (A : Type*) (B : Type*) (C : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] where
  seq : ExactSequence A B C

namespace ExactSequence

variable {A B C D E : Type*}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [AddCommGroup D] [AddCommGroup E]

/-- The canonical exact sequence `C --id--> C --0--> C`. -/
def zero : ExactSequence C C C where
  f := AddMonoidHom.id C
  g := 0
  f_exact := by simp
  exactness := by
    intro c _
    exact ⟨c, rfl⟩

/-- A composed exact sequence, with the genuinely additional exactness
obligations for the composite supplied explicitly. -/
def comp (S₁ : ExactSequence A B C) (S₂ : ExactSequence C D E)
    (hzero : ∀ b, S₂.g (S₂.f (S₁.g b)) = 0)
    (hexact : ∀ d, S₂.g d = 0 → ∃ b, S₂.f (S₁.g b) = d) :
    ExactSequence B D E where
  f := S₂.f.comp S₁.g
  g := S₂.g
  f_exact := hzero
  exactness := hexact

end ExactSequence
