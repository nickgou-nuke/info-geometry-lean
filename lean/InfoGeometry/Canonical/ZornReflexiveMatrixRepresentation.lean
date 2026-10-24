/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveMatrixCorner
import InfoGeometry.Algebra.ZornSignedCAR

/-! The negative signed CAR pair `(L_U, L_negV)` is normalized to
`(L_U, -L_negV)`. This yields a native matrix algebra representation on the
full Zorn module, using associative endomorphism composition throughout. -/
namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows
open InfoGeometry.Algebra InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

noncomputable def zornColorMatrixHom (i : Fin 3) :
    Matrix (Fin 2) (Fin 2) R →ₐ[R] Module.End R (ZornVectorMatrix R) := by
  let q := L_map (R := R) (U i : ZornVectorMatrix R)
  let c := L_map (R := R) (-(V i : ZornVectorMatrix R))
  have hq : q * q = 0 := L_U_square_zero i
  have hc : c * c = 0 := L_negV_square_zero i
  have hcar : q * c + c * q = -1 := by
    simpa only [ite_true, neg_one_smul] using L_U_negV_anticommutator (R := R) i i
  have hpair := negative_car_reflexive hq hc hcar
  apply pairMatrixAlgHom hq (show (-c) * (-c) = 0 by simpa using hc) hpair.1 hpair.2
  change q * (-c) + (-c) * q = 1
  rw [_root_.mul_neg, _root_.neg_mul, ← _root_.neg_add, hcar, _root_.neg_neg]

@[simp] theorem zornColorMatrixHom_apply (i : Fin 3) (M : Matrix (Fin 2) (Fin 2) R) :
    zornColorMatrixHom i M = pairMatrixLinear
      (L_map (R := R) (U i : ZornVectorMatrix R)) (-(L_map (R := R) (-V i))) M := rfl

end InfoGeometry.Canonical.ReflexiveNilpotentFlows
