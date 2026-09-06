import InfoGeometry.Categorical.FibonacciHomSpace

/-!
# Simple-object Hom-space consequences

These lemmas expose the elementary Schur-type zero Hom-spaces already encoded
by the concrete block-matrix `FibHom` carrier.  They do not assert the global
nontrivial Fibonacci pentagon or hexagon coherence.
-/

namespace InfoGeometry.Categorical.FibonacciSimpleHomLemmas

noncomputable section

open InfoGeometry.Categorical.FibonacciHomSpace
open InfoGeometry.Categorical.FibonacciFusionCategoryData

abbrev simpleUnit : FibCat := Finsupp.single FibSimple.unit 1
abbrev simpleTau : FibCat := Finsupp.single FibSimple.tau 1

theorem simpleUnit_count_unit :
    simpleUnit FibSimple.unit = 1 := by
  simp [simpleUnit]

theorem simpleUnit_count_tau :
    simpleUnit FibSimple.tau = 0 := by
  simp [simpleUnit]

theorem simpleTau_count_unit :
    simpleTau FibSimple.unit = 0 := by
  simp [simpleTau]

theorem simpleTau_count_tau :
    simpleTau FibSimple.tau = 1 := by
  simp [simpleTau]

theorem hom_simpleUnit_simpleTau_subsingleton :
    Subsingleton (FibHom simpleUnit simpleTau) := by
  constructor
  intro f g
  apply FibHom.ext
  · have hf : f.unit_comp = 0 := by
      ext i j
      exact Fin.elim0 (by simpa [simpleTau] using j)
    have hg : g.unit_comp = 0 := by
      ext i j
      exact Fin.elim0 (by simpa [simpleTau] using j)
    rw [hf, hg]
  · have hf : f.tau_comp = 0 := by
      ext i j
      exact Fin.elim0 (by simpa [simpleUnit] using i)
    have hg : g.tau_comp = 0 := by
      ext i j
      exact Fin.elim0 (by simpa [simpleUnit] using i)
    rw [hf, hg]

theorem hom_simpleTau_simpleUnit_subsingleton :
    Subsingleton (FibHom simpleTau simpleUnit) := by
  constructor
  intro f g
  apply FibHom.ext
  · have hf : f.unit_comp = 0 := by
      ext i j
      exact Fin.elim0 (by simpa [simpleTau] using i)
    have hg : g.unit_comp = 0 := by
      ext i j
      exact Fin.elim0 (by simpa [simpleTau] using i)
    rw [hf, hg]
  · have hf : f.tau_comp = 0 := by
      ext i j
      exact Fin.elim0 (by simpa [simpleUnit] using j)
    have hg : g.tau_comp = 0 := by
      ext i j
      exact Fin.elim0 (by simpa [simpleUnit] using j)
    rw [hf, hg]

end

open InfoGeometry.Categorical.FibonacciHomSpace
open InfoGeometry.Categorical.FibonacciFusionCategoryData

/-! ## Component readout for composition

These lemmas expose the two existing block components of `FibHom.comp`.
They are deliberately small: later finite coherence calculations can use
them without unfolding the category instance or rebuilding the Hom carrier.
-/

theorem fibHom_unit_comp_comp {X Y Z : FibCat}
    (f : FibHom X Y) (g : FibHom Y Z) :
    (FibHom.comp f g).unit_comp = f.unit_comp * g.unit_comp := rfl

theorem fibHom_tau_comp_comp {X Y Z : FibCat}
    (f : FibHom X Y) (g : FibHom Y Z) :
    (FibHom.comp f g).tau_comp = f.tau_comp * g.tau_comp := rfl

theorem fibHom_id_unit_comp (X : FibCat) :
    (FibHom.id X).unit_comp =
      (1 : Matrix (Fin (X FibSimple.unit)) (Fin (X FibSimple.unit)) ℂ) := rfl

theorem fibHom_id_tau_comp (X : FibCat) :
    (FibHom.id X).tau_comp =
      (1 : Matrix (Fin (X FibSimple.tau)) (Fin (X FibSimple.tau)) ℂ) := rfl

theorem fibHom_comp_unit_comp_id {X Y : FibCat} (f : FibHom X Y) :
    (FibHom.comp f (FibHom.id Y)).unit_comp = f.unit_comp := by
  rw [fibHom_unit_comp_comp, fibHom_id_unit_comp, Matrix.mul_one]

theorem fibHom_comp_tau_comp_id {X Y : FibCat} (f : FibHom X Y) :
    (FibHom.comp f (FibHom.id Y)).tau_comp = f.tau_comp := by
  rw [fibHom_tau_comp_comp, fibHom_id_tau_comp, Matrix.mul_one]

theorem fibHom_id_comp_unit_comp {X Y : FibCat} (f : FibHom X Y) :
    (FibHom.comp (FibHom.id X) f).unit_comp = f.unit_comp := by
  rw [fibHom_unit_comp_comp, fibHom_id_unit_comp, Matrix.one_mul]

theorem fibHom_id_comp_tau_comp {X Y : FibCat} (f : FibHom X Y) :
    (FibHom.comp (FibHom.id X) f).tau_comp = f.tau_comp := by
  rw [fibHom_tau_comp_comp, fibHom_id_tau_comp, Matrix.one_mul]

end InfoGeometry.Categorical.FibonacciSimpleHomLemmas
