import Mathlib.Tactic

open Matrix
open scoped Matrix

namespace InfoGeometry.Topology

abbrev Affine3 := Matrix (Fin 3) (Fin 3) ℚ

def I3 : Affine3 := 1

def Tx : Affine3 := !![1, 0, 1; 0, 1, 0; 0, 0, 1]
def Ty : Affine3 := !![1, 0, 0; 0, 1, 1; 0, 0, 1]
def TxInv : Affine3 := !![1, 0, -1; 0, 1, 0; 0, 0, 1]
def TyInv : Affine3 := !![1, 0, 0; 0, 1, -1; 0, 0, 1]
def R2 : Affine3 := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]
def Mx : Affine3 := !![1, 0, 0; 0, -1, 0; 0, 0, 1]
def Gx : Affine3 := !![1, 0, (1 / 2 : ℚ); 0, -1, 0; 0, 0, 1]
def GxInv : Affine3 := !![1, 0, (-1 / 2 : ℚ); 0, -1, 0; 0, 0, 1]

theorem p2_square : R2 * R2 = I3 := by
  native_decide

theorem p2_conjugation : R2 * Tx * R2 = TxInv := by
  native_decide

theorem pm_square : Mx * Mx = I3 := by
  native_decide

theorem pm_conjugation : Mx * Ty * Mx = TyInv := by
  native_decide

theorem pg_square : Gx * Gx = Tx := by
  native_decide

theorem pg_inverse : Gx * GxInv = I3 := by
  native_decide

theorem pg_conjugation : Gx * Ty * GxInv = TyInv := by
  native_decide

end InfoGeometry.Topology
