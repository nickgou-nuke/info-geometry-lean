import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Rational topological readout for the native Zorn carrier

The algebraic owner already supplies `cartanCharge` on `ZornVectorMatrix ℚ`.
This file transports the product topology through its existing coordinate
equivalence and packages that same coordinate projection as a `TopCat` map.
No lattice, charge-spectrum, or maximal-order claim is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical

open CategoryTheory
open InfoGeometry.Algebra

instance zornVectorMatrixRationalTopologicalSpace :
    TopologicalSpace (ZornVectorMatrix ℚ) :=
  TopologicalSpace.induced ZornVectorMatrix.coordEquiv.toFun inferInstance

private theorem continuous_zornVectorMatrix_rational_coordEquiv :
    Continuous
      (ZornVectorMatrix.coordEquiv :
        ZornVectorMatrix ℚ ≃
          (ℚ × (Fin 3 → ℚ) × (Fin 3 → ℚ) × ℚ)) :=
  continuous_induced_dom

theorem continuous_zornVectorMatrix_rational_a :
    Continuous (fun X : ZornVectorMatrix ℚ => X.a) :=
  continuous_zornVectorMatrix_rational_coordEquiv.fst

theorem continuous_zornVectorMatrix_rational_b :
    Continuous (fun X : ZornVectorMatrix ℚ => X.b) :=
  continuous_zornVectorMatrix_rational_coordEquiv.snd.snd.snd

theorem continuous_zornVectorMatrix_rational_v (i : Fin 3) :
    Continuous (fun X : ZornVectorMatrix ℚ => X.v i) :=
  (continuous_apply i).comp
    continuous_zornVectorMatrix_rational_coordEquiv.snd.fst

theorem continuous_zornVectorMatrix_rational_w (i : Fin 3) :
    Continuous (fun X : ZornVectorMatrix ℚ => X.w i) :=
  (continuous_apply i).comp
    continuous_zornVectorMatrix_rational_coordEquiv.snd.snd.fst

theorem continuous_zornVectorMatrix_rational_trace :
    Continuous (fun X : ZornVectorMatrix ℚ => ZornVectorMatrix.trace X) := by
  simpa [ZornVectorMatrix.trace] using
    continuous_zornVectorMatrix_rational_a.add
      continuous_zornVectorMatrix_rational_b

theorem continuous_zornVectorMatrix_rational_norm :
    Continuous (fun X : ZornVectorMatrix ℚ => ZornVectorMatrix.norm X) := by
  have hv₀ := continuous_zornVectorMatrix_rational_v (0 : Fin 3)
  have hv₁ := continuous_zornVectorMatrix_rational_v (1 : Fin 3)
  have hv₂ := continuous_zornVectorMatrix_rational_v (2 : Fin 3)
  have hw₀ := continuous_zornVectorMatrix_rational_w (0 : Fin 3)
  have hw₁ := continuous_zornVectorMatrix_rational_w (1 : Fin 3)
  have hw₂ := continuous_zornVectorMatrix_rational_w (2 : Fin 3)
  have hdot : Continuous (fun X : ZornVectorMatrix ℚ =>
      X.v 0 * X.w 0 + X.v 1 * X.w 1 + X.v 2 * X.w 2) := by
    exact ((hv₀.mul hw₀).add (hv₁.mul hw₁)).add (hv₂.mul hw₂)
  simpa [ZornVectorMatrix.norm, ZornVec3.dot_eq_sum_coords] using
    (continuous_zornVectorMatrix_rational_a.mul
      continuous_zornVectorMatrix_rational_b).sub hdot

def zornVectorMatrixRationalTraceTopCat :
    TopCat.of (ZornVectorMatrix ℚ) ⟶ TopCat.of ℚ :=
  TopCat.ofHom
    { toFun := ZornVectorMatrix.trace
      continuous_toFun := continuous_zornVectorMatrix_rational_trace }

def zornVectorMatrixRationalNormTopCat :
    TopCat.of (ZornVectorMatrix ℚ) ⟶ TopCat.of ℚ :=
  TopCat.ofHom
    { toFun := ZornVectorMatrix.norm
      continuous_toFun := continuous_zornVectorMatrix_rational_norm }

def zornVectorMatrixRationalCartanChargeTopCat :
    TopCat.of (ZornVectorMatrix ℚ) ⟶ TopCat.of ℚ :=
  TopCat.ofHom
    { toFun := ZornVectorMatrix.cartanChargeFn
      continuous_toFun := by
        simpa [ZornVectorMatrix.cartanChargeFn] using
          continuous_zornVectorMatrix_rational_a }

@[simp] theorem zornVectorMatrixRationalCartanChargeTopCat_apply
    (X : ZornVectorMatrix ℚ) :
    zornVectorMatrixRationalCartanChargeTopCat X =
      ZornVectorMatrix.cartanCharge X := rfl

theorem zornVectorMatrixRationalCartanChargeTopCat_eq_projection :
    zornVectorMatrixRationalCartanChargeTopCat =
      TopCat.ofHom
        { toFun := fun X : ZornVectorMatrix ℚ => X.a
          continuous_toFun := continuous_zornVectorMatrix_rational_a } := by
  rfl

end InfoGeometry.Canonical
