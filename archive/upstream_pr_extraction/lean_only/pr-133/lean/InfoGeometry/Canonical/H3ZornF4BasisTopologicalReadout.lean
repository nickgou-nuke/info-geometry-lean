import InfoGeometry.Algebra.H3ZornF4Basis
import InfoGeometry.Canonical.H3ZornTopCatReadout
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topology of the trace-zero H₃(Zorn) carrier

The algebraic owner defines `traceZero` as a `Submodule`.  Its topology here
is the inherited subtype topology.  This file packages the subtype inclusion
and the restricted coordinate readouts as genuine `TopCat` morphisms.
-/

noncomputable section

namespace InfoGeometry.Algebra.H3Zorn

def traceZeroInclusionTopCat :
    TopCat.of (traceZero (R := ℝ)) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := fun X : traceZero (R := ℝ) => (X : H3Zorn ℝ)
      continuous_toFun := continuous_subtype_val }

@[simp] theorem traceZeroInclusionTopCat_apply (X : traceZero (R := ℝ)) :
    traceZeroInclusionTopCat X = (X : H3Zorn ℝ) :=
  rfl

def traceZeroAlpha1ContinuousMap : ContinuousMap (traceZero (R := ℝ)) ℝ :=
  ContinuousMap.mk
    (fun X : traceZero (R := ℝ) => (X : H3Zorn ℝ).α₁)
    (continuous_h3Zorn_α₁.comp continuous_subtype_val)

def traceZeroAlpha2ContinuousMap : ContinuousMap (traceZero (R := ℝ)) ℝ :=
  ContinuousMap.mk
    (fun X : traceZero (R := ℝ) => (X : H3Zorn ℝ).α₂)
    (continuous_h3Zorn_α₂.comp continuous_subtype_val)

def traceZeroAlpha3ContinuousMap : ContinuousMap (traceZero (R := ℝ)) ℝ :=
  ContinuousMap.mk
    (fun X : traceZero (R := ℝ) => (X : H3Zorn ℝ).α₃)
    (continuous_h3Zorn_α₃.comp continuous_subtype_val)

def traceZeroAContinuousMap :
    ContinuousMap (traceZero (R := ℝ)) (ZornVectorMatrix ℝ) :=
  ContinuousMap.mk
    (fun X : traceZero (R := ℝ) => (X : H3Zorn ℝ).a)
    (continuous_h3Zorn_a.comp continuous_subtype_val)

def traceZeroBContinuousMap :
    ContinuousMap (traceZero (R := ℝ)) (ZornVectorMatrix ℝ) :=
  ContinuousMap.mk
    (fun X : traceZero (R := ℝ) => (X : H3Zorn ℝ).b)
    (continuous_h3Zorn_b.comp continuous_subtype_val)

def traceZeroCContinuousMap :
    ContinuousMap (traceZero (R := ℝ)) (ZornVectorMatrix ℝ) :=
  ContinuousMap.mk
    (fun X : traceZero (R := ℝ) => (X : H3Zorn ℝ).c)
    (continuous_h3Zorn_c.comp continuous_subtype_val)

def traceZeroAlpha1TopCat :
    TopCat.of (traceZero (R := ℝ)) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun X : traceZero (R := ℝ) => (X : H3Zorn ℝ).α₁
      continuous_toFun := continuous_h3Zorn_α₁.comp continuous_subtype_val }

def traceZeroAlpha2TopCat :
    TopCat.of (traceZero (R := ℝ)) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun X : traceZero (R := ℝ) => (X : H3Zorn ℝ).α₂
      continuous_toFun := continuous_h3Zorn_α₂.comp continuous_subtype_val }

def traceZeroAlpha3TopCat :
    TopCat.of (traceZero (R := ℝ)) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun X : traceZero (R := ℝ) => (X : H3Zorn ℝ).α₃
      continuous_toFun := continuous_h3Zorn_α₃.comp continuous_subtype_val }

def traceZeroATopCat :
    TopCat.of (traceZero (R := ℝ)) ⟶ TopCat.of (ZornVectorMatrix ℝ) :=
  TopCat.ofHom
    { toFun := fun X : traceZero (R := ℝ) => (X : H3Zorn ℝ).a
      continuous_toFun := continuous_h3Zorn_a.comp continuous_subtype_val }

def traceZeroBTopCat :
    TopCat.of (traceZero (R := ℝ)) ⟶ TopCat.of (ZornVectorMatrix ℝ) :=
  TopCat.ofHom
    { toFun := fun X : traceZero (R := ℝ) => (X : H3Zorn ℝ).b
      continuous_toFun := continuous_h3Zorn_b.comp continuous_subtype_val }

def traceZeroCTopCat :
    TopCat.of (traceZero (R := ℝ)) ⟶ TopCat.of (ZornVectorMatrix ℝ) :=
  TopCat.ofHom
    { toFun := fun X : traceZero (R := ℝ) => (X : H3Zorn ℝ).c
      continuous_toFun := continuous_h3Zorn_c.comp continuous_subtype_val }

@[simp] theorem traceZeroAlpha1TopCat_apply (X : traceZero (R := ℝ)) :
    traceZeroAlpha1TopCat X = (X : H3Zorn ℝ).α₁ := rfl

@[simp] theorem traceZeroAlpha2TopCat_apply (X : traceZero (R := ℝ)) :
    traceZeroAlpha2TopCat X = (X : H3Zorn ℝ).α₂ := rfl

@[simp] theorem traceZeroAlpha3TopCat_apply (X : traceZero (R := ℝ)) :
    traceZeroAlpha3TopCat X = (X : H3Zorn ℝ).α₃ := rfl

@[simp] theorem traceZeroATopCat_apply (X : traceZero (R := ℝ)) :
    traceZeroATopCat X = (X : H3Zorn ℝ).a := rfl

@[simp] theorem traceZeroBTopCat_apply (X : traceZero (R := ℝ)) :
    traceZeroBTopCat X = (X : H3Zorn ℝ).b := rfl

@[simp] theorem traceZeroCTopCat_apply (X : traceZero (R := ℝ)) :
    traceZeroCTopCat X = (X : H3Zorn ℝ).c := rfl

theorem traceZero_traceTopCat (X : traceZero (R := ℝ)) :
    (X : H3Zorn ℝ).α₁ + (X : H3Zorn ℝ).α₂ + (X : H3Zorn ℝ).α₃ = 0 :=
  X.property

end InfoGeometry.Algebra.H3Zorn
