import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.H3ZornTopologicalReadout
import InfoGeometry.Algebra.H3ZornJordanIdentity

noncomputable section

namespace InfoGeometry.Canonical

open CategoryTheory
open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn

def h3zornNormCubicContinuousMap : ContinuousMap (H3Zorn ℝ) ℝ :=
  ContinuousMap.mk normCubic continuous_h3Zorn_normCubic

@[simp] theorem h3zornNormCubicContinuousMap_apply (X : H3Zorn ℝ) :
    h3zornNormCubicContinuousMap X = normCubic X :=
  rfl

def h3zornNormCubicTopCat :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := normCubic
      continuous_toFun := continuous_h3Zorn_normCubic }

@[simp] theorem h3zornNormCubicTopCat_apply (X : H3Zorn ℝ) :
    h3zornNormCubicTopCat X = normCubic X :=
  rfl

def h3zornAdjointQuadContinuousMap :
    ContinuousMap (H3Zorn ℝ) (H3Zorn ℝ) :=
  ContinuousMap.mk adjointQuad continuous_h3Zorn_adjointQuad

@[simp] theorem h3zornAdjointQuadContinuousMap_apply (X : H3Zorn ℝ) :
    h3zornAdjointQuadContinuousMap X = adjointQuad X :=
  rfl

def h3zornAdjointQuadTopCat :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := adjointQuad
      continuous_toFun := continuous_h3Zorn_adjointQuad }

@[simp] theorem h3zornAdjointQuadTopCat_apply (X : H3Zorn ℝ) :
    h3zornAdjointQuadTopCat X = adjointQuad X :=
  rfl

end InfoGeometry.Canonical
