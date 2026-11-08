import InfoGeometry.Spectral.Colimit.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Sequential colimits of modules

This is the Lean 4 categorical replacement for the old quotient-based
`seq_colim` construction.  The carrier and its universal property are
Mathlib's colimit in `ModuleCat`; no second quotient implementation is
introduced.
-/

noncomputable section

namespace InfoGeometry.Spectral.Colimit.SequentialModule

open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [Ring R]

abbrev Diagram (R : Type u) [Ring R] := ℕ ⥤ ModuleCat R

abbrev Cocone (R : Type u) [Ring R] (F : Diagram R) :=
  CategoryTheory.Limits.Cocone F

abbrev Carrier (F : Diagram R) : ModuleCat R := colimit F

abbrev inclusion {F : Diagram R} (n : ℕ) : F.obj n ⟶ Carrier R F :=
  colimit.ι F n

@[simp]
theorem inclusion_naturality {F : Diagram R} {m n : ℕ} (h : m ≤ n) :
    F.map (homOfLE h) ≫ inclusion R n = inclusion R m := by
  simp [inclusion]

def descend {F : Diagram R} (t : Cocone R F) :
    Carrier R F ⟶ t.pt :=
  colimit.desc F t

@[simp]
theorem descend_fac {F : Diagram R} (t : Cocone R F) (n : ℕ) :
    inclusion R n ≫ descend R t = t.ι.app n := by
  exact colimit.ι_desc t n

theorem descend_unique {F : Diagram R}
    (t : Cocone R F) (f : Carrier R F ⟶ t.pt)
    (h : ∀ n, inclusion R n ≫ f = t.ι.app n) :
    f = descend R t := by
  apply colimit.hom_ext
  intro n
  exact (h n).trans (descend_fac R t n).symm

end InfoGeometry.Spectral.Colimit.SequentialModule
