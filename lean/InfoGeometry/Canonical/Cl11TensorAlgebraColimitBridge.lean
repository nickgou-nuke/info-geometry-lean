import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Tensor-algebra presentation of the `Cl(1,1)` tower colimit

The tensor algebra on `Vec11` is the free algebra of words in the local
Cl(1,1) generators.  The matrix tower has a different carrier: its colimit is
`Cl11TensorTowerLimit.Limit`.  This file records the canonical map between the
two using the existing Pauli generator and the stage-one colimit inclusion.

No generation, quotient, or isomorphism claim is made here.  Those require a
separate proof that the chosen atom images generate the entire tower colimit
and that their kernel is exactly the Clifford relation ideal.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11TensorAlgebraColimitBridge

open InfoGeometry.Algebra.TensorAlgebraCanonical
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.TowerMatrix

abbrev Atom : Type := SymmetryAtom
abbrev WordAlgebra : Type := SymmetryWord
abbrev TowerColimit : Type := Limit

/-! The local Pauli generator is placed at the first matrix stage and then in
the native filtered colimit. -/

noncomputable def atomToTowerColimit : Atom →ₗ[ℝ] TowerColimit where
  toFun x := ofStage 1 ((matEquivFinPowTwo 1).symm (gen x))
  map_add' x y := by
    simp [map_add]
  map_smul' r x := by
    change ofStage 1
        ((matEquivFinPowTwo 1).symm (gen (r • x))) =
      (algebraMap ℝ TowerColimit r) *
        ofStage 1 ((matEquivFinPowTwo 1).symm (gen x))
    rw [gen.map_smul, map_smul, Algebra.smul_def, map_mul]
    rw [← realAlgebraMap_stage 1 r]
    change realAlgebraMap r *
        ofStage 1 ((matEquivFinPowTwo 1).symm (gen x)) =
      realAlgebraMap r *
        ofStage 1 ((matEquivFinPowTwo 1).symm (gen x))
    rfl

noncomputable def tensorToTowerColimit :
    WordAlgebra →ₐ[ℝ] TowerColimit :=
  liftLinear atomToTowerColimit

/-! ## Foundation: the map is canonical by the tensor-algebra universal property

`WordAlgebra` is the free associative algebra on the local `Cl(1,1)` atoms.
The theorem below is the reusable foundation statement: any algebra morphism
from the word algebra into the tower colimit which agrees on the atoms is the
map constructed above.  Thus later Cuntz, BitWord, or readout morphisms only
need to specify their atom map; they do not introduce a second word algebra.
-/

theorem tensorToTowerColimit_unique
    (g : WordAlgebra →ₐ[ℝ] TowerColimit)
    (hg : g.toLinearMap.comp includeLinear = atomToTowerColimit) :
    g = tensorToTowerColimit := by
  exact (liftLinear_unique atomToTowerColimit g).mp hg

theorem tensorToTowerColimit_eq_lift
    (f : Atom →ₗ[ℝ] TowerColimit) :
    liftLinear f = tensorToTowerColimit ↔ f = atomToTowerColimit := by
  constructor
  · intro h
    have hcomp := congrArg
      (fun k : WordAlgebra →ₐ[ℝ] TowerColimit =>
        k.toLinearMap.comp includeLinear) h
    simpa [tensorToTowerColimit, liftLinear_comp_includeLinear] using hcomp
  · intro h
    rw [h]
    rfl

@[simp] theorem tensorToTowerColimit_atom (x : Atom) :
    tensorToTowerColimit (TensorAlgebra.ι ℝ x) =
      ofStage 1 ((matEquivFinPowTwo 1).symm (gen x)) := by
  exact liftLinear_includeLinear atomToTowerColimit x

theorem tensorToTowerColimit_atom_quadratic (x : Atom) :
    tensorToTowerColimit (TensorAlgebra.ι ℝ x) *
          tensorToTowerColimit (TensorAlgebra.ι ℝ x) =
      ofStage 1 ((matEquivFinPowTwo 1).symm
        ((q11 x) • (1 : Mat2))) := by
  have hmap :
      (matEquivFinPowTwo 1).symm (gen x * gen x) =
        (matEquivFinPowTwo 1).symm (gen x) *
          (matEquivFinPowTwo 1).symm (gen x) := by
    exact (matEquivFinPowTwo 1).symm.map_mul (gen x) (gen x)
  rw [tensorToTowerColimit_atom, ← map_mul]
  rw [← hmap, gen_sq]

end InfoGeometry.Canonical.Cl11TensorAlgebraColimitBridge
