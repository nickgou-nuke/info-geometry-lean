import Mathlib.Tactic
import InfoGeometry.Categorical.ZornBraidColimit

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Categorical.ZornBraidColimit

universe u

variable (R : Type u) [CommRing R]
variable {J : Type u} [Category.{u} J] [IsFiltered J]

variable (ZornSequence : J ⥤ ModuleCat.{u} R)
variable [HasColimit ZornSequence]
variable (M : CompatibleBilinearMultiplication R ZornSequence)

/-- 
The finite BCFW property: at each stage `j`, the three elements satisfy the Arnold-Cohen
mixed relation under the stage multiplication.
-/
def SatisfiesFiniteArnoldCohen (j : J) (w12 w23 w31 : ZornSequence.obj j) : Prop :=
  M.stageMul j (M.stageMul j w12 w23) w31 + 
  M.stageMul j (M.stageMul j w23 w31) w12 + 
  M.stageMul j (M.stageMul j w31 w12) w23 = 0

/-- 
The macroscopic continuous BCFW property: the elements in the colimit satisfy 
the Arnold-Cohen mixed relation under the descended continuum multiplication.
-/
def SatisfiesContinuumArnoldCohen (W12 W23 W31 : ↑(zornContinuumModule R ZornSequence)) : Prop :=
  M.colimitMul (M.colimitMul W12 W23) W31 + 
  M.colimitMul (M.colimitMul W23 W31) W12 + 
  M.colimitMul (M.colimitMul W31 W12) W23 = 0

/--
Native colimit form of the mixed Arnold--Cohen relation.  The theorem type
contains the actual descended multiplication and injections; the named
predicate definitions above remain only as compatibility exports.
-/
theorem continuum_bcfw_arnold_cohen_native
    (j : J) (w12 w23 w31 : ZornSequence.obj j)
    (h_arnold :
      M.stageMul j (M.stageMul j w12 w23) w31 +
        M.stageMul j (M.stageMul j w23 w31) w12 +
        M.stageMul j (M.stageMul j w31 w12) w23 = 0) :
    M.colimitMul (M.colimitMul ((colimit.ι ZornSequence j) w12)
        ((colimit.ι ZornSequence j) w23)) ((colimit.ι ZornSequence j) w31) +
      M.colimitMul (M.colimitMul ((colimit.ι ZornSequence j) w23)
        ((colimit.ι ZornSequence j) w31)) ((colimit.ι ZornSequence j) w12) +
      M.colimitMul (M.colimitMul ((colimit.ι ZornSequence j) w31)
        ((colimit.ι ZornSequence j) w12)) ((colimit.ι ZornSequence j) w23) = 0 := by
  repeat rw [CompatibleBilinearMultiplication.mul_colimit_ι_ι]
  rw [← map_add, ← map_add, h_arnold, map_zero]

/--
The structural proof of Continuum BCFW:
If the Arnold-Cohen mixed relation holds for finite edges at some stage `j`,
it strictly maps to the continuous boundary.
-/
theorem continuum_bcfw_arnold_cohen (j : J) (w12 w23 w31 : ZornSequence.obj j)
    (h_arnold : SatisfiesFiniteArnoldCohen R ZornSequence M j w12 w23 w31) :
    SatisfiesContinuumArnoldCohen R ZornSequence M 
      ((colimit.ι ZornSequence j) w12) 
      ((colimit.ι ZornSequence j) w23) 
      ((colimit.ι ZornSequence j) w31) := by
  exact continuum_bcfw_arnold_cohen_native R ZornSequence M j w12 w23 w31 h_arnold
