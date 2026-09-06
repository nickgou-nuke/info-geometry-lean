import Mathlib

/-!
# Chirality-induced grading on endomorphisms

An involution on a module defines even (commuting) and odd (anticommuting)
endomorphisms.  The statements are purely algebraic: no identification with
an ambient Clifford grading is assumed.
-/

namespace InfoGeometry.Canonical.ChiralEndomorphismSupergrading

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

abbrev End (R E : Type*) [CommRing R] [AddCommGroup E] [Module R E] :=
  Module.End R E

def IsInvolution (K : End R E) : Prop := K.comp K = LinearMap.id

def IsEven (K A : End R E) : Prop := A.comp K = K.comp A

def IsOdd (K A : End R E) : Prop := A.comp K = -(K.comp A)

theorem even_zero (K : End R E) : IsEven K 0 := by
  simp [IsEven]

theorem odd_zero (K : End R E) : IsOdd K 0 := by
  simp [IsOdd]

theorem even_add (K A B : End R E) (hA : IsEven K A) (hB : IsEven K B) :
    IsEven K (A + B) := by
  simp only [IsEven, LinearMap.add_comp, LinearMap.comp_add]
  rw [hA, hB]

theorem odd_add (K A B : End R E) (hA : IsOdd K A) (hB : IsOdd K B) :
    IsOdd K (A + B) := by
  simp only [IsOdd, LinearMap.add_comp, LinearMap.comp_add]
  rw [hA, hB]
  simp [add_comm]

theorem even_comp_odd (K A B : End R E)
    (hA : IsEven K A) (hB : IsOdd K B) :
    IsOdd K (A.comp B) := by
  apply LinearMap.ext
  intro x
  change A (B (K x)) = -K (A (B x))
  rw [show B (K x) = -K (B x) from
    congrArg (fun T : End R E => T x) hB]
  simp only [map_neg]
  rw [show A (K (B x)) = K (A (B x)) from
    congrArg (fun T : End R E => T (B x)) hA]

theorem odd_comp_even (K A B : End R E)
    (hA : IsOdd K A) (hB : IsEven K B) :
    IsOdd K (A.comp B) := by
  apply LinearMap.ext
  intro x
  change A (B (K x)) = -K (A (B x))
  rw [show B (K x) = K (B x) from
    congrArg (fun T : End R E => T x) hB]
  rw [show A (K (B x)) = -K (A (B x)) from
    congrArg (fun T : End R E => T (B x)) hA]

theorem odd_comp_odd (K A B : End R E)
    (hA : IsOdd K A) (hB : IsOdd K B) :
    IsEven K (A.comp B) := by
  apply LinearMap.ext
  intro x
  change A (B (K x)) = K (A (B x))
  rw [show B (K x) = -K (B x) from
    congrArg (fun T : End R E => T x) hB]
  simp only [map_neg]
  rw [show A (K (B x)) = -K (A (B x)) from
    congrArg (fun T : End R E => T (B x)) hA]
  simp

theorem odd_square_even (K A : End R E)
    (hA : IsOdd K A) : IsEven K (A.comp A) := by
  exact odd_comp_odd K A A hA hA

end InfoGeometry.Canonical.ChiralEndomorphismSupergrading
