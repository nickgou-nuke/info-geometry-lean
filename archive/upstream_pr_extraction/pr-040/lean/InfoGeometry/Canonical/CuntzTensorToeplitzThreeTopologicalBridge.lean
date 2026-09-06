import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.NativeToeplitzCuntzThreeArtinBraid

/-!
# Topological wire for the native three-generator Toeplitz carrier

The tensor/RingQuot carrier is given the discrete topology.  This is an
explicit finite-stage/topological interface: it does not assert a C*-norm or
completion.  Continuity of translations is then supplied by mathlib's native
discrete-topology instance, while the Artin equations come from the existing
Toeplitz algebraic owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzTensorToeplitzThreeTopologicalBridge

open CategoryTheory
open InfoGeometry.Canonical.NativeToeplitzCuntzThreeArtinBraid

abbrev NativeToeplitzThree := Carrier

local instance nativeDiscreteTopology : TopologicalSpace NativeToeplitzThree := ⊥
local instance nativeDiscrete : DiscreteTopology NativeToeplitzThree :=
  discreteTopology_bot NativeToeplitzThree
local instance nativeContinuousMul : ContinuousMul NativeToeplitzThree := by infer_instance

noncomputable def nativeBraidGenerator1 :
    TopCat.of NativeToeplitzThree ⟶ TopCat.of NativeToeplitzThree :=
  TopCat.ofHom
    { toFun := fun x => braidGenerator1 * x
      continuous_toFun := continuous_const.mul continuous_id }

noncomputable def nativeBraidGenerator2 :
    TopCat.of NativeToeplitzThree ⟶ TopCat.of NativeToeplitzThree :=
  TopCat.ofHom
    { toFun := fun x => braidGenerator2 * x
      continuous_toFun := continuous_const.mul continuous_id }

theorem native_braid_artin_relation :
    nativeBraidGenerator1 ≫ nativeBraidGenerator2 ≫ nativeBraidGenerator1 =
      nativeBraidGenerator2 ≫ nativeBraidGenerator1 ≫ nativeBraidGenerator2 := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change braidGenerator1 * (braidGenerator2 * (braidGenerator1 * x)) =
    braidGenerator2 * (braidGenerator1 * (braidGenerator2 * x))
  simpa only [mul_assoc] using congrArg (fun z : NativeToeplitzThree => z * x)
    artin_braid_relation

theorem native_braid_generator1_involutive :
    nativeBraidGenerator1 ≫ nativeBraidGenerator1 =
      𝟙 (TopCat.of NativeToeplitzThree) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change braidGenerator1 * (braidGenerator1 * x) = x
  rw [← mul_assoc, braidGenerator1_sq, one_mul]

theorem native_braid_generator2_involutive :
    nativeBraidGenerator2 ≫ nativeBraidGenerator2 =
      𝟙 (TopCat.of NativeToeplitzThree) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change braidGenerator2 * (braidGenerator2 * x) = x
  rw [← mul_assoc, braidGenerator2_sq, one_mul]

end InfoGeometry.Canonical.CuntzTensorToeplitzThreeTopologicalBridge
