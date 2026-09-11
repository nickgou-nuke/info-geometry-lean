import InfoGeometry.Topology.BrillouinKleinBottleManifold
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.V4D4WeylEmbedding

/-!
# Genuine finite `D₈` group behind the Brillouin wallpaper matrices

The existing `d4_comp` table and its matrix homomorphism theorem are the
authoritative finite data.  This owner packages that table as a genuine group
and exposes the matrix representation.  The projective central-sign quotient
is deliberately left to a separate owner.
-/


namespace InfoGeometry.Canonical.BrillouinWallpaperD8GroupBridge

open InfoGeometry.Canonical.V4D4WeylEmbedding
open InfoGeometry.Canonical.WallpaperKleinBottleCartan
open InfoGeometry.Topology.BrillouinKleinBottleManifold

structure D8PointGroup where
  index : Fin 8
  deriving DecidableEq, Repr

def d8Mul (a b : D8PointGroup) : D8PointGroup :=
  ⟨d4_comp a.index b.index⟩

def d8One : D8PointGroup := ⟨0⟩

def d8InvIndex : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 3
  | 2 => 2
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7

def d8Inv (a : D8PointGroup) : D8PointGroup :=
  ⟨d8InvIndex a.index⟩

instance : Mul D8PointGroup where
  mul := d8Mul

instance : One D8PointGroup where
  one := d8One

instance : Inv D8PointGroup where
  inv := d8Inv

instance : Group D8PointGroup where
  one := d8One
  mul := d8Mul
  inv := d8Inv
  mul_assoc := by
    intro a b c
    cases a with
    | mk a =>
      cases b with
      | mk b =>
        cases c with
        | mk c =>
          fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
  one_mul := by
    intro a
    cases a with
    | mk a => fin_cases a <;> rfl
  mul_one := by
    intro a
    cases a with
    | mk a => fin_cases a <;> rfl
  inv_mul_cancel := by
    intro a
    cases a with
    | mk a => fin_cases a <;> rfl

@[simp] theorem d8PointGroup_index_one :
    (1 : D8PointGroup).index = 0 := rfl

@[simp] theorem d8PointGroup_index_mul (a b : D8PointGroup) :
    (a * b).index = d4_comp a.index b.index := rfl

@[simp] theorem d8PointGroup_index_inv (a : D8PointGroup) :
    a⁻¹.index = d8InvIndex a.index := rfl

abbrev M2Q := InfoGeometry.Algebra.FiniteSpin.Mat2Q

noncomputable def wallpaperD4Representation : D8PointGroup →* M2Q where
  toFun a := wallpaperD4 a.index
  map_one' := by
    rfl
  map_mul' a b := by
    rw [d8PointGroup_index_mul]
    exact (wallpaperD4_is_homomorphism a.index b.index).symm

@[simp] theorem wallpaperD4Representation_apply (a : D8PointGroup) :
    wallpaperD4Representation a = wallpaperD4 a.index := rfl

theorem wallpaperD4Representation_Tx :
    wallpaperD4Representation ⟨5⟩ = Tx := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wallpaperD4Representation, wallpaperD4, Tx,
      InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinTwist2,
      InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinGlide2]

theorem wallpaperD4Representation_Ty :
    wallpaperD4Representation ⟨4⟩ = Ty := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wallpaperD4Representation, wallpaperD4, Ty,
      InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinGlide2]

theorem wallpaperD4Representation_Txy :
    wallpaperD4Representation ⟨1⟩ = Txy := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wallpaperD4Representation, wallpaperD4, Txy, Tx, Ty,
      InfoGeometry.Canonical.HolographicSouriauReconstruction.brillouinTwist2,
      Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.BrillouinWallpaperD8GroupBridge
