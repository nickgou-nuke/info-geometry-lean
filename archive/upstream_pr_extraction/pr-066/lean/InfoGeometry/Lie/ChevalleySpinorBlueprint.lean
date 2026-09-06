import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.QuadraticForm.Basic

namespace InfoGeometry.Lie.ChevalleySpinor

open LinearMap
open ExteriorAlgebra

variable {R : Type*} [CommRing R]
variable {W : Type*} [AddCommGroup W] [Module R W]

abbrev DualSpace (R W : Type*) [CommRing R] [AddCommGroup W] [Module R W] :=
  W →ₗ[R] R

abbrev SplitV (R W : Type*) [CommRing R] [AddCommGroup W] [Module R W] :=
  W × DualSpace R W

def splitBilin : LinearMap.BilinForm R (SplitV R W) :=
  LinearMap.mk₂ R (fun v1 v2 => v2.2 v1.1)
    (fun x y z => by dsimp; simp [LinearMap.map_add])
    (fun c x y => by dsimp; simp)
    (fun x y z => by dsimp)
    (fun c x y => by dsimp)

def splitQ : QuadraticForm R (SplitV R W) :=
  splitBilin.toQuadraticMap

abbrev SpinorSpace (R W : Type*) [CommRing R] [AddCommGroup W] [Module R W] :=
  ExteriorAlgebra R W

def actionWedge : W →ₗ[R] Module.End R (SpinorSpace R W) where
  toFun w := LinearMap.mulLeft R (ι R w)
  map_add' x y := by
    ext z
    dsimp
    rw [map_add, add_mul]
  map_smul' c x := by
    ext z
    dsimp
    rw [map_smul, smul_mul_assoc]

def actionContraction : DualSpace R W →ₗ[R] Module.End R (SpinorSpace R W) :=
  CliffordAlgebra.contractLeft

def spinorAction : SplitV R W →ₗ[R] Module.End R (SpinorSpace R W) :=
  (actionWedge (R := R) (W := W)).comp (LinearMap.fst R W (DualSpace R W)) +
  (actionContraction (R := R) (W := W)).comp (LinearMap.snd R W (DualSpace R W))

theorem spinorAction_sq (v : SplitV R W) : 
    spinorAction (R := R) (W := W) v * spinorAction (R := R) (W := W) v = (splitQ v) • (1 : Module.End R (SpinorSpace R W)) := by
  dsimp [spinorAction]
  rw [add_mul, mul_add, mul_add]
  have h_wedge_sq : actionWedge (R := R) (W := W) v.1 * actionWedge (R := R) (W := W) v.1 = 0 := by
    ext x
    dsimp [actionWedge]
    rw [← mul_assoc, ι_sq_zero, zero_mul]
  have h_contract_sq : actionContraction (R := R) (W := W) v.2 * actionContraction (R := R) (W := W) v.2 = 0 := by
    ext x
    exact CliffordAlgebra.contractLeft_contractLeft v.2 x
  have h_anticomm : actionWedge (R := R) (W := W) v.1 * actionContraction (R := R) (W := W) v.2 + actionContraction (R := R) (W := W) v.2 * actionWedge (R := R) (W := W) v.1 = (v.2 v.1) • 1 := by
    ext x
    dsimp [actionWedge, actionContraction]
    rw [CliffordAlgebra.contractLeft_ι_mul v.2 v.1 x]
    abel
  rw [h_wedge_sq, h_contract_sq, zero_add, add_zero]
  exact h_anticomm

def abstractSpinorRep : CliffordAlgebra (splitQ (R := R) (W := W)) →ₐ[R] Module.End R (SpinorSpace R W) :=
  CliffordAlgebra.lift (splitQ (R := R) (W := W)) ⟨spinorAction, spinorAction_sq⟩

end InfoGeometry.Lie.ChevalleySpinor
