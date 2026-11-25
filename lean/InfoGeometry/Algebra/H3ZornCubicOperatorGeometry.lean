/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornAutomorphismConjugation
import InfoGeometry.Algebra.H3ZornInfinitesimalReconstruction
import InfoGeometry.Algebra.H3ZornOperatorNoncommutativity
import InfoGeometry.Algebra.H3ZornCarrierBasis
import InfoGeometry.Algebra.H3ZornF4Basis
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Cubic geometry acting on full Albert operator Lie algebras

This module connects the polynomial geometry to the native noncommutative
operator constructions. A cubic-norm similitude conjugates the infinitesimal
cubic stabilizer. A cubic-norm isometry fixing the distinguished identity
reconstructs a Jordan automorphism and hence conjugates every derivation.

The actual inclusion order is Mathlib's `LieSubalgebra` partial order. The
proved infinitesimal reconstruction inclusion is one direction only; no
exceptional dimension, simplicity, or automorphism-classification conclusion
is asserted.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn TrilinearStabilizer

attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable instance : FiniteDimensional ℝ (H3Zorn ℝ) :=
  h3ZornBasis.finiteDimensional_of_finite

/-- The infinitesimal stabilizer of the full Albert cubic norm in the native
endomorphism Lie algebra. -/
def h3zornCubicStabilizer : LieSubalgebra ℝ (Module.End ℝ (H3Zorn ℝ)) :=
  trilinearStabilizer h3zornNormTrilin

/-- Evaluation at the Jordan unit of an infinitesimal cubic symmetry has
trace zero, by applying the stabilizer equation to the triple `(1,1,1)`. -/
theorem h3zorn_cubicStabilizer_evalOne_trace_zero
    (D : h3zornCubicStabilizer) : linearTrace (D.1 1) = 0 := by
  have hC := D.2 1 1 1
  change h3zornNormTrilin (D.1 1) 1 1 +
    h3zornNormTrilin 1 (D.1 1) 1 + h3zornNormTrilin 1 1 (D.1 1) = 0 at hC
  have h12 := h3zornCubicJordanDatum.normTrilin_swap₁₂ (D.1 1) 1 1
  have h23 := h3zornCubicJordanDatum.normTrilin_swap₂₃ 1 (D.1 1) 1
  change h3zornNormTrilin (D.1 1) 1 1 =
    h3zornNormTrilin 1 (D.1 1) 1 at h12
  change h3zornNormTrilin 1 (D.1 1) 1 =
    h3zornNormTrilin 1 1 (D.1 1) at h23
  rw [h12, h23] at hC
  rw [← h3zornNormTrilin_one_one (D.1 1)]
  linarith

/-- Unit evaluation is a linear map from the infinitesimal cubic stabilizer to
the full Albert carrier. -/
def h3zornCubicStabilizerEvalOne :
    h3zornCubicStabilizer →ₗ[ℝ] H3Zorn ℝ where
  toFun D := D.1 1
  map_add' D E := by
    change (D.1 + E.1) 1 = D.1 1 + E.1 1
    simp
  map_smul' r D := by
    change (r • D.1) 1 = r • D.1 1
    simp

/-- The unit-evaluation map factors through the native 26-dimensional
trace-zero subspace of the Albert carrier. -/
def h3zornCubicStabilizerUnitTraceReadout :
    h3zornCubicStabilizer →ₗ[ℝ] H3Zorn.traceZero (R := ℝ) where
  toFun D := ⟨h3zornCubicStabilizerEvalOne D,
    h3zorn_cubicStabilizer_evalOne_trace_zero D⟩
  map_add' D E := by
    apply Subtype.ext
    simp [h3zornCubicStabilizerEvalOne]
  map_smul' r D := by
    apply Subtype.ext
    simp [h3zornCubicStabilizerEvalOne]

/-- The reduced structure subgroup of the full split Albert carrier, defined
as the linear equivalences preserving its actual cubic norm. This is the
norm-isometry group; cubic-norm similitudes with a nontrivial multiplier are
not included in this subgroup. -/
def h3zornReducedStructureGroup : Subgroup (H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) where
  carrier := {e | ∀ x, normCubic (e x) = normCubic x}
  one_mem' := by
    intro x
    rfl
  mul_mem' := by
    intro e f he hf x
    rw [LinearEquiv.mul_apply, he, hf]
  inv_mem' := by
    intro e he x
    have hx := he (e.symm x)
    simpa using hx.symm

/-- The full split Albert structure group: a linear equivalence together with
its unit-valued cubic-norm multiplier. The carrier equation is
`N(e x) = μ N(x)` for every Albert element `x`. -/
def h3zornStructureGroup :
    Subgroup ((H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) × ℝˣ) where
  carrier := {g | ∀ x, normCubic (g.1 x) = (g.2 : ℝ) * normCubic x}
  one_mem' := by
    intro x
    simp
  mul_mem' := by
    intro g h hg hh x
    change normCubic ((g.1 * h.1) x) =
      ((g.2 * h.2 : ℝˣ) : ℝ) * normCubic x
    rw [LinearEquiv.mul_apply]
    calc
      normCubic (g.1 (h.1 x)) = (g.2 : ℝ) * normCubic (h.1 x) := hg _
      _ = (g.2 : ℝ) * ((h.2 : ℝ) * normCubic x) := by rw [hh]
      _ = ((g.2 * h.2 : ℝˣ) : ℝ) * normCubic x := by
        rw [Units.val_mul]
        ring
  inv_mem' := by
    intro g hg x
    change normCubic (g.1.symm x) =
      ((g.2⁻¹ : ℝˣ) : ℝ) * normCubic x
    have hx := hg (g.1.symm x)
    simp only [LinearEquiv.apply_symm_apply] at hx
    have hval : (g.2 : ℝ) ≠ 0 := Units.ne_zero _
    calc
      normCubic (g.1.symm x) = (g.2 : ℝ)⁻¹ *
          ((g.2 : ℝ) * normCubic (g.1.symm x)) := by field_simp [hval]
      _ = (g.2 : ℝ)⁻¹ * normCubic x := by rw [← hx]
      _ = ((g.2⁻¹ : ℝˣ) : ℝ) * normCubic x := by simp

/-- The multiplier homomorphism from the full structure group to `ℝˣ`. -/
def h3zornStructureMultiplier : h3zornStructureGroup →* ℝˣ where
  toFun g := g.1.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The cubic multiplier is read off from the image of the distinguished
Jordan unit; consequently it is determined by the underlying linear map. -/
@[simp] theorem h3zornStructureMultiplier_val_eq_normCubic_one
    (g : h3zornStructureGroup) :
    (h3zornStructureMultiplier g : ℝ) = normCubic (g.1.1 1) := by
  have h := g.2 (1 : H3Zorn ℝ)
  simpa [h3zornStructureMultiplier, normCubic_one] using h.symm

/-- The faithful action of the full cubic-similitude group on the Albert
carrier, forgetting the multiplier stored with each linear equivalence. -/
def h3zornStructureGroup_toLinearEquiv :
    h3zornStructureGroup →* (H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) where
  toFun g := g.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The unit value of the cubic norm recovers the multiplier, so the full
structure-group action on the Albert carrier is faithful. -/
theorem h3zornStructureGroup_toLinearEquiv_injective :
    Function.Injective h3zornStructureGroup_toLinearEquiv := by
  intro g h gh
  apply Subtype.ext
  apply Prod.ext
  · exact gh
  · apply Units.ext
    have hg : (g.1.2 : ℝ) = normCubic (g.1.1 1) := by
      simpa [h3zornStructureMultiplier] using
        h3zornStructureMultiplier_val_eq_normCubic_one g
    have hh : (h.1.2 : ℝ) = normCubic (h.1.1 1) := by
      simpa [h3zornStructureMultiplier] using
        h3zornStructureMultiplier_val_eq_normCubic_one h
    rw [hg, hh]
    exact congrArg normCubic (congrArg (fun e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ => e 1) gh)

/-- The multiplier-one subgroup is the norm-preserving reduced structure group. -/
theorem h3zornStructureMultiplier_ker_carrier (g : h3zornStructureGroup) :
    g ∈ h3zornStructureMultiplier.ker ↔
      (∀ x, normCubic (g.1.1 x) = normCubic x) := by
  change g.1.2 = 1 ↔ _
  constructor
  · intro h x
    rw [g.2 x, h]
    simp
  · intro h
    have h1 := h (1 : H3Zorn ℝ)
    have hmul := g.2 (1 : H3Zorn ℝ)
    simp only [normCubic_one, mul_one] at hmul
    rw [normCubic_one] at h1
    exact Units.ext (hmul.symm.trans h1)

/-- The reduced norm-preserver group is canonically the kernel of the full
structure-group multiplier. -/
def h3zornReducedStructureGroupMulEquivMultiplierKer :
    h3zornReducedStructureGroup ≃* h3zornStructureMultiplier.ker where
  toFun e := by
    refine ⟨⟨(e.1, 1), ?_⟩, ?_⟩
    · intro x
      simpa using e.2 x
    · rfl
  invFun g :=
    ⟨g.1.1.1, (h3zornStructureMultiplier_ker_carrier g.1).1 g.2⟩
  left_inv := by
    intro e
    apply Subtype.ext
    rfl
  right_inv := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact g.2.symm
  map_mul' := by
    intro e f
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp

/-- A reduced-structure element fixing the distinguished Jordan unit is an
actual member of the existing Albert Jordan automorphism group. -/
def h3zornJordanAutOfReducedStructure
    (e : h3zornReducedStructureGroup) (h1 : e.1 1 = 1) : H3ZornJordanAut :=
  h3zornJordanAutOfNorm e.1 e.2 h1

@[simp] theorem h3zornJordanAutOfReducedStructure_toLinearEquiv
    (e : h3zornReducedStructureGroup) (h1 : e.1 1 = 1) :
    (h3zornJordanAutOfReducedStructure e h1).toLinearEquiv = e.1 := rfl

/-- A similitude of the actual cubic polynomial transports its infinitesimal
stabilizer, with no fixed-unit hypothesis. -/
theorem h3zornCubicStabilizer_map_of_normSimilitude
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x) :
    h3zornCubicStabilizer.map e.lieConj.toLieHom = h3zornCubicStabilizer :=
  map_trilinearStabilizer_lieConj h3zornNormTrilin h3zornNormTrilin e u
    (h3zornNormTrilin_similitude_of_normCubic_similitude e.toLinearMap u hN)

/-- Structure-group elements act on the infinitesimal cubic stabilizer by
operator conjugation, using their stored multiplier equation. -/
theorem h3zornCubicStabilizer_map_of_structureGroup
    (g : h3zornStructureGroup) :
    h3zornCubicStabilizer.map g.1.1.lieConj.toLieHom = h3zornCubicStabilizer := by
  exact h3zornCubicStabilizer_map_of_normSimilitude g.1.1 g.1.2 g.2

/-- The adjoint for the nondegenerate split-Albert trace pairing. Its
convention is `T(f† x, y) = T(x, f y)`. -/
noncomputable def h3zornTraceAdjoint (f : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ) :
    H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ :=
  LinearMap.BilinForm.leftAdjointOfNondegenerate
    h3zornTraceBilin h3zornTraceBilin_nondegenerate f

/-- Evaluation law for the trace adjoint, with the pairing's actual slot order. -/
theorem h3zornTraceAdjoint_pair
    (f : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ) (x y : H3Zorn ℝ) :
    traceBilin (h3zornTraceAdjoint f x) y = traceBilin x (f y) := by
  exact LinearMap.BilinForm.isAdjointPairLeftAdjointOfNondegenerate
    h3zornTraceBilin h3zornTraceBilin_nondegenerate f x y

/-- The inverse adjoint `(e⁻¹)†` used by the Albert cross-product covariance law. -/
noncomputable def h3zornTraceInverseAdjoint
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ :=
  h3zornTraceAdjoint e.symm.toLinearMap

/-- The polarized cubic and cross product have the same sixfold trace normalization. -/
theorem h3zornNormTrilin_eq_trace_crossProduct (x y z : H3Zorn ℝ) :
    6 * h3zornNormTrilin x y z = traceBilin (crossProduct x y) z := by
  rw [h3zornNormTrilin_apply, traceBilin_crossProduct_assoc]
  ring

/-- A cubic-norm similitude intertwines the actual Albert cross product with
the inverse trace adjoint, carrying exactly its cubic multiplier. -/
theorem h3zorn_crossProduct_similitude_intertwines
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x)
    (x y : H3Zorn ℝ) :
    crossProduct (e x) (e y) =
      (u : ℝ) • h3zornTraceInverseAdjoint e (crossProduct x y) := by
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro z
  let w := e.symm z
  have hw : e w = z := by simp [w]
  rw [← hw]
  have hC := h3zornNormTrilin_similitude_of_normCubic_similitude
    e.toLinearMap (u : ℝ) hN x y w
  calc
    traceBilin (crossProduct (e x) (e y)) (e w) =
        6 * h3zornNormTrilin (e x) (e y) (e w) :=
      (h3zornNormTrilin_eq_trace_crossProduct (e x) (e y) (e w)).symm
    _ = (u : ℝ) * (6 * h3zornNormTrilin x y w) := by
      calc
        6 * h3zornNormTrilin (e x) (e y) (e w) =
            6 * ((u : ℝ) * h3zornNormTrilin x y w) := congrArg (6 * ·) hC
        _ = (u : ℝ) * (6 * h3zornNormTrilin x y w) := by ring
    _ = traceBilin ((u : ℝ) •
        h3zornTraceInverseAdjoint e (crossProduct x y)) (e w) := by
      rw [h3zornNormTrilin_eq_trace_crossProduct, traceBilin_smul_left]
      change (u : ℝ) * traceBilin (crossProduct x y) w =
        (u : ℝ) * traceBilin
          (h3zornTraceAdjoint e.symm.toLinearMap (crossProduct x y)) (e w)
      rw [h3zornTraceAdjoint_pair]
      simp

/-- The cross-product intertwining law specialized to the full split Albert
structure group, with the multiplier read from its stored structure-group
element. -/
theorem h3zornStructureGroup_crossProduct_intertwines
    (g : h3zornStructureGroup) (x y : H3Zorn ℝ) :
    crossProduct (g.1.1 x) (g.1.1 y) =
      (g.1.2 : ℝ) • h3zornTraceInverseAdjoint g.1.1 (crossProduct x y) := by
  exact h3zorn_crossProduct_similitude_intertwines
    g.1.1 g.1.2 g.2 x y

/-- The linear trace readout on the full split-Albert carrier. -/
private def h3zornLinearTraceMap : H3Zorn ℝ →ₗ[ℝ] ℝ where
  toFun := linearTrace
  map_add' := linearTrace_add
  map_smul' r x := by
    change linearTrace (r • x) = r • linearTrace x
    rw [linearTrace_smul]
    simp [smul_eq_mul]

/-- The carrier's trace-zero subspace has dimension 26, as the kernel of the
surjective scalar trace on the 27-dimensional Albert carrier. -/
theorem h3zorn_traceZero_finrank :
    Module.finrank ℝ (H3Zorn.traceZero (R := ℝ)) = 26 := by
  have hone : linearTrace (1 : H3Zorn ℝ) = 3 := by
    change (1 : ℝ) + 1 + 1 = 3
    norm_num
  have hker : h3zornLinearTraceMap.ker = H3Zorn.traceZero (R := ℝ) := by
    ext x
    change linearTrace x = 0 ↔ H3Zorn.trace x = 0
    rfl
  have hsurj : Function.Surjective h3zornLinearTraceMap := by
    intro r
    refine ⟨(r / 3) • (1 : H3Zorn ℝ), ?_⟩
    change linearTrace ((r / 3) • (1 : H3Zorn ℝ)) = r
    rw [linearTrace_smul, hone]
    field_simp
  have hrange : LinearMap.range h3zornLinearTraceMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rw [← hker]
  have hdim :
      Module.finrank ℝ (LinearMap.range h3zornLinearTraceMap) +
        Module.finrank ℝ (LinearMap.ker h3zornLinearTraceMap) =
          Module.finrank ℝ (H3Zorn ℝ) :=
    LinearMap.finrank_range_add_finrank_ker h3zornLinearTraceMap
  rw [hrange, finrank_top, Module.finrank_self, finrank_h3zorn] at hdim
  omega

/-- The resulting equivalence is a native Lie equivalence, with bracket
preservation inherited from genuine noncommutative operator conjugation. -/
def h3zornCubicStabilizerLieEquivOfNormSimilitude
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x) :
    h3zornCubicStabilizer ≃ₗ⁅ℝ⁆ h3zornCubicStabilizer :=
  e.lieConj.ofSubalgebras _ _ (h3zornCubicStabilizer_map_of_normSimilitude e u hN)

@[simp] theorem h3zornCubicStabilizerLieEquivOfNormSimilitude_apply
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x)
    (D : h3zornCubicStabilizer) :
    (h3zornCubicStabilizerLieEquivOfNormSimilitude e u hN D :
      Module.End ℝ (H3Zorn ℝ)) = e.lieConj (D : Module.End ℝ (H3Zorn ℝ)) := rfl

/-- A cubic-norm isometry fixing the unit transports every multiplication
operator of the actual Albert product. -/
theorem h3zorn_lieConj_jordanLmul_of_norm_and_unit
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (hN : ∀ x, normCubic (e x) = normCubic x) (h1 : e 1 = 1) (x : H3Zorn ℝ) :
    e.lieConj (jordanLmul (R := ℝ) x) = jordanLmul (R := ℝ) (e x) :=
  (h3zornJordanAutOfNorm e hN h1).lieConj_jordanLmul x

/-- The polynomial/basepoint assumptions alone produce a native equivalence
of the full derivation Lie algebra. -/
def h3zornDerivationLieEquivOfNorm
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (hN : ∀ x, normCubic (e x) = normCubic x) (h1 : e 1 = 1) :
    H3ZornF4Derivations ≃ₗ⁅ℝ⁆ H3ZornF4Derivations :=
  (h3zornJordanAutOfNorm e hN h1).derivationLieEquiv

@[simp] theorem h3zornDerivationLieEquivOfNorm_apply
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (hN : ∀ x, normCubic (e x) = normCubic x) (h1 : e 1 = 1)
    (D : H3ZornF4Derivations) :
    (h3zornDerivationLieEquivOfNorm e hN h1 D : Module.End ℝ (H3Zorn ℝ)) =
      e.lieConj (D : Module.End ℝ (H3Zorn ℝ)) := rfl

end InfoGeometry.Algebra
