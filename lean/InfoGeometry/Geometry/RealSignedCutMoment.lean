/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Geometry.RealHamiltonianMoment
import InfoGeometry.Geometry.ParaHessianMixedPotential
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Real auxiliary rotations and the signed cut moments

On the existing doubled real carrier `E × E`, the operator
`exchange ∘ grading` is literally `J(x,y) = (-y,x)`.  This file constructs
its continuous symplectic form, the derivative of the coordinate energy
`‖x‖² + ‖y‖²`, and its actual real rotation flow.  The coordinate sum is
deliberate: the norm of Mathlib's plain product is the maximum norm.

For a base Hamiltonian identity supplied as a genuine `HasFDerivAt`, the
direct-sum form then has moment `μ + q * energy` and auxiliary generator
`q • J`.  The paper's positive cut is `q = -1`; the negative cut is `q = 1`.
The construction works on arbitrary real normed base spaces and arbitrary
real Hilbert auxiliary factors.  Taking `E = ℝ` gives the usual real
two-dimensional auxiliary plane.  No quotient manifold, reduction theorem,
or Gromov--Witten statement is asserted here.
-/

noncomputable section

namespace InfoGeometry.Geometry.RealSignedCutMoment

open InfoGeometry.Canonical
open RealHamiltonianMoment

variable {E : Type*} [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev Plane (E : Type*) := ParaHessianMixedPotential.Doubled E

/-- The real imaginary operator is constructed from existing full operators. -/
def planeJ : Plane E →L[ℝ] Plane E :=
  (ParaHessianMixedPotential.exchange (E := E)).comp (ParaHessianMixedPotential.grading (E := E))

@[simp] theorem planeJ_apply (X : Plane E) :
    planeJ X = (-X.2, X.1) :=
  rfl

theorem planeJ_complexStructure :
    IsRealComplexStructure (planeJ (E := E)).toLinearMap := by
  unfold IsRealComplexStructure
  ext X <;> simp

/-- The normalized continuous form, retaining both real coordinates. -/
def planeOmega : Plane E →L[ℝ] Plane E →L[ℝ] ℝ :=
  (-2 : ℝ) •
    ((innerSL ℝ).bilinearComp (ContinuousLinearMap.fst ℝ E E)
        (ContinuousLinearMap.snd ℝ E E) -
      (innerSL ℝ).bilinearComp (ContinuousLinearMap.snd ℝ E E)
        (ContinuousLinearMap.fst ℝ E E))

@[simp] theorem planeOmega_apply (U V : Plane E) :
    planeOmega U V = -2 * (inner ℝ U.1 V.2 - inner ℝ U.2 V.1) :=
  rfl

/-- Exact normalization bridge to the existing coordinate symplectic owner. -/
theorem planeOmega_eq_existing (U V : Plane E) :
    planeOmega U V = -2 * ParaHessianMixedPotential.symplectic U V := by
  rw [planeOmega_apply, ParaHessianMixedPotential.symplectic_apply]

theorem planeOmega_skew (U V : Plane E) :
    planeOmega U V = -planeOmega V U := by
  rw [planeOmega_eq_existing, planeOmega_eq_existing, ParaHessianMixedPotential.symplectic_skew]
  ring

theorem planeOmega_nondegenerate (U : Plane E)
    (hU : ∀ V, planeOmega U V = 0) : U = 0 := by
  apply ParaHessianMixedPotential.symplectic_nondegenerate
  intro V
  have h := hU V
  rw [planeOmega_eq_existing] at h
  linarith

def planeEnergy (X : Plane E) : ℝ := ‖X.1‖ ^ 2 + ‖X.2‖ ^ 2

def planeEnergyDerivative (X : Plane E) : Plane E →L[ℝ] ℝ :=
  2 • (innerSL ℝ X.1).comp (ContinuousLinearMap.fst ℝ E E) +
    2 • (innerSL ℝ X.2).comp (ContinuousLinearMap.snd ℝ E E)

theorem hasFDerivAt_planeEnergy (X : Plane E) :
    HasFDerivAt planeEnergy (planeEnergyDerivative X) X := by
  exact ((ContinuousLinearMap.fst ℝ E E).hasFDerivAt.norm_sq).add
    ((ContinuousLinearMap.snd ℝ E E).hasFDerivAt.norm_sq)

theorem planeOmega_generator (X : Plane E) :
    planeOmega (planeJ X) = planeEnergyDerivative X := by
  apply ContinuousLinearMap.ext
  intro V
  simp [planeEnergyDerivative] <;> ring

/-- The actual derivative identity on the entirely real auxiliary carrier. -/
theorem hasFDerivAt_planeEnergy_moment (X : Plane E) :
    HasFDerivAt planeEnergy (planeOmega (planeJ X)) X := by
  rw [planeOmega_generator]
  exact hasFDerivAt_planeEnergy X

theorem fderiv_planeEnergy (X V : Plane E) :
    fderiv ℝ planeEnergy X V = planeOmega (planeJ X) V := by
  rw [(hasFDerivAt_planeEnergy_moment X).fderiv]

def planeRotation (t : ℝ) : Plane E →L[ℝ] Plane E :=
  rotation planeJ t

@[simp] theorem planeRotation_apply (t : ℝ) (X : Plane E) :
    planeRotation t X =
      (Real.cos t • X.1 - Real.sin t • X.2,
        Real.sin t • X.1 + Real.cos t • X.2) := by
  ext <;> simp [planeRotation, sub_eq_add_neg, add_comm]

theorem planeRotation_add (s t : ℝ) :
    planeRotation (E := E) (s + t) =
      (planeRotation s).comp (planeRotation t) := by
  change rotation (V := Plane E) (planeJ (E := E)) (s + t) =
    (rotation (V := Plane E) (planeJ (E := E)) s).comp
      (rotation (V := Plane E) (planeJ (E := E)) t)
  exact rotation_add (V := Plane E) (planeJ (E := E))
    (planeJ_complexStructure (E := E)) s t

theorem planeRotation_periodic :
    Function.Periodic (planeRotation (E := E)) (2 * Real.pi) := by
  change Function.Periodic (rotation (V := Plane E) (planeJ (E := E)))
    (2 * Real.pi)
  exact rotation_periodic (V := Plane E) (planeJ (E := E))

theorem hasDerivAt_planeRotation (t : ℝ) (X : Plane E) :
    HasDerivAt (fun s => planeRotation s X) (planeJ (planeRotation t X)) t := by
  change HasDerivAt
    (fun s => rotation (V := Plane E) (planeJ (E := E)) s X)
    (planeJ (E := E) (rotation (V := Plane E) (planeJ (E := E)) t X)) t
  exact hasDerivAt_rotation (V := Plane E) (planeJ (E := E))
    (planeJ_complexStructure (E := E)) t X

theorem productPairing_planeRotation (t : ℝ) (U V : Plane E) :
    ParaHessianMixedPotential.productPairing (planeRotation t U) (planeRotation t V) =
      ParaHessianMixedPotential.productPairing U V := by
  simp only [ParaHessianMixedPotential.productPairing, planeRotation_apply,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  calc
    _ = (Real.sin t ^ 2 + Real.cos t ^ 2) *
        (inner ℝ U.1 V.1 + inner ℝ U.2 V.2) := by ring
    _ = inner ℝ U.1 V.1 + inner ℝ U.2 V.2 := by
      rw [Real.sin_sq_add_cos_sq]
      ring

theorem planeEnergy_eq_pairing (X : Plane E) :
    planeEnergy X = ParaHessianMixedPotential.productPairing X X := by
  simp [planeEnergy, ParaHessianMixedPotential.productPairing, real_inner_self_eq_norm_sq]

theorem planeEnergy_rotation (t : ℝ) (X : Plane E) :
    planeEnergy (planeRotation t X) = planeEnergy X := by
  rw [planeEnergy_eq_pairing, productPairing_planeRotation, planeEnergy_eq_pairing]

theorem planeOmega_eq_pairing (U V : Plane E) :
    planeOmega U V = -2 * ParaHessianMixedPotential.productPairing (planeJ U) V := by
  simp [ParaHessianMixedPotential.productPairing] <;> ring

theorem planeOmega_rotation (t : ℝ) (U V : Plane E) :
    planeOmega (planeRotation t U) (planeRotation t V) = planeOmega U V := by
  rw [planeOmega_eq_pairing, planeOmega_eq_pairing]
  change -2 * ParaHessianMixedPotential.productPairing (planeJ (rotation planeJ t U))
      (rotation planeJ t V) = _
  rw [map_rotation]
  change -2 * ParaHessianMixedPotential.productPairing (planeRotation t (planeJ U))
      (planeRotation t V) = _
  rw [productPairing_planeRotation]

section Product

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

/-- Direct sum of the base continuous form and the constructed auxiliary form. -/
def productOmega (ωM : M →L[ℝ] M →L[ℝ] ℝ) :
    (M × Plane E) →L[ℝ] (M × Plane E) →L[ℝ] ℝ :=
  ωM.bilinearComp (ContinuousLinearMap.fst ℝ M (Plane E))
      (ContinuousLinearMap.fst ℝ M (Plane E)) +
    planeOmega.bilinearComp (ContinuousLinearMap.snd ℝ M (Plane E))
      (ContinuousLinearMap.snd ℝ M (Plane E))

@[simp] theorem productOmega_apply (ωM : M →L[ℝ] M →L[ℝ] ℝ)
    (U V : M × Plane E) :
    productOmega ωM U V = ωM U.1 V.1 + planeOmega U.2 V.2 :=
  rfl

theorem productOmega_skew (ωM : M →L[ℝ] M →L[ℝ] ℝ)
    (hM : ∀ u v, ωM u v = -ωM v u) (U V : M × Plane E) :
    productOmega ωM U V = -productOmega ωM V U := by
  rw [productOmega_apply, productOmega_apply, hM U.1 V.1,
    planeOmega_skew U.2 V.2]
  ring

theorem productOmega_nondegenerate (ωM : M →L[ℝ] M →L[ℝ] ℝ)
    (hM : ∀ u, (∀ v, ωM u v = 0) → u = 0) (U : M × Plane E)
    (hU : ∀ V, productOmega ωM U V = 0) : U = 0 := by
  apply Prod.ext
  · apply hM U.1
    intro v
    simpa using hU (v, 0)
  · apply planeOmega_nondegenerate U.2
    intro v
    simpa using hU (0, v)

/-- `q = -1` is the positive cut; `q = 1` is the negative cut. -/
def cutMoment (μ : M → ℝ) (q : ℝ) (X : M × Plane E) : ℝ :=
  μ X.1 + q * planeEnergy X.2

def cutGenerator (v : M → M) (q : ℝ) (X : M × Plane E) : M × Plane E :=
  (v X.1, q • planeJ X.2)

/-- A genuine base Hamiltonian derivative extends to the signed product moment. -/
theorem hasFDerivAt_cutMoment (ωM : M →L[ℝ] M →L[ℝ] ℝ)
    (μ : M → ℝ) (v : M → M) (q : ℝ) (X : M × Plane E)
    (hμ : HasFDerivAt μ (ωM (v X.1)) X.1) :
    HasFDerivAt (cutMoment μ q) (productOmega ωM (cutGenerator v q X)) X := by
  have hbase := hμ.comp X
    (ContinuousLinearMap.fst ℝ M (Plane E)).hasFDerivAt
  have haux := (hasFDerivAt_planeEnergy_moment X.2).comp X
    (ContinuousLinearMap.snd ℝ M (Plane E)).hasFDerivAt
  have hderivative :
      (ωM (v X.1)).comp (ContinuousLinearMap.fst ℝ M (Plane E)) +
        q • (planeOmega (planeJ X.2)).comp
          (ContinuousLinearMap.snd ℝ M (Plane E)) =
      productOmega ωM (cutGenerator v q X) := by
    apply ContinuousLinearMap.ext
    intro V
    change ωM (v X.1) V.1 + q * planeOmega (planeJ X.2) V.2 =
      ωM (v X.1) V.1 + planeOmega (q • planeJ X.2) V.2
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  change HasFDerivAt (fun Y => μ Y.1 + q * planeEnergy Y.2) _ X
  rw [← hderivative]
  exact hbase.add (haux.const_mul q)

/-- Inverse auxiliary rotation gives `μ - energy`. -/
theorem hasFDerivAt_positiveCutMoment (ωM : M →L[ℝ] M →L[ℝ] ℝ)
    (μ : M → ℝ) (v : M → M) (X : M × Plane E)
    (hμ : HasFDerivAt μ (ωM (v X.1)) X.1) :
    HasFDerivAt (fun Y : M × Plane E => μ Y.1 - planeEnergy Y.2)
      (productOmega ωM (v X.1, -planeJ X.2)) X := by
  have h := hasFDerivAt_cutMoment (E := E) ωM μ v (-1) X hμ
  have hfunction : cutMoment (E := E) μ (-1) =
      (fun Y : M × Plane E => μ Y.1 - planeEnergy Y.2) := by
    funext Y
    change μ Y.1 + (-1 : ℝ) * planeEnergy Y.2 = μ Y.1 - planeEnergy Y.2
    ring
  rw [hfunction] at h
  simpa only [cutGenerator, neg_one_smul] using h

/-- Direct auxiliary rotation gives `μ + energy`. -/
theorem hasFDerivAt_negativeCutMoment (ωM : M →L[ℝ] M →L[ℝ] ℝ)
    (μ : M → ℝ) (v : M → M) (X : M × Plane E)
    (hμ : HasFDerivAt μ (ωM (v X.1)) X.1) :
    HasFDerivAt (fun Y : M × Plane E => μ Y.1 + planeEnergy Y.2)
      (productOmega ωM (v X.1, planeJ X.2)) X := by
  have h := hasFDerivAt_cutMoment (E := E) ωM μ v 1 X hμ
  have hfunction : cutMoment (E := E) μ 1 =
      (fun Y : M × Plane E => μ Y.1 + planeEnergy Y.2) := by
    funext Y
    change μ Y.1 + (1 : ℝ) * planeEnergy Y.2 = μ Y.1 + planeEnergy Y.2
    rw [one_mul]
  rw [hfunction] at h
  simpa only [cutGenerator, one_smul] using h

def signedProductFlow (ρ : ℝ → M → M) (q t : ℝ) (X : M × Plane E) :
    M × Plane E :=
  (ρ t X.1, planeRotation (q * t) X.2)

theorem hasDerivAt_signedProductFlow (ρ : ℝ → M → M) (v : M → M)
    (q t : ℝ) (X : M × Plane E)
    (hρ : HasDerivAt (fun s => ρ s X.1) (v (ρ t X.1)) t) :
    HasDerivAt (fun s => signedProductFlow ρ q s X)
      (cutGenerator v q (signedProductFlow ρ q t X)) t := by
  have haux : HasDerivAt
      (fun s => planeRotation (E := E) (q * s) X.2)
      (q • planeJ (E := E) (planeRotation (E := E) (q * t) X.2)) t := by
    exact hasDerivAt_weightedRotation (V := Plane E) (planeJ (E := E))
      (planeJ_complexStructure (E := E)) q t X.2
  change HasDerivAt
    (fun s => (ρ s X.1, planeRotation (E := E) (q * s) X.2))
    (v (ρ t X.1), q • planeJ (E := E) (planeRotation (E := E) (q * t) X.2)) t
  exact hρ.prodMk haux

theorem cutMoment_signedProductFlow (ρ : ℝ → M → M) (μ : M → ℝ)
    (q t : ℝ) (X : M × Plane E) (hμ : μ (ρ t X.1) = μ X.1) :
    cutMoment μ q (signedProductFlow ρ q t X) = cutMoment μ q X := by
  simp only [cutMoment, signedProductFlow, planeEnergy_rotation, hμ]

theorem signedProductFlow_add (ρ : ℝ → M → M) (q s t : ℝ)
    (hρ : ∀ x, ρ (s + t) x = ρ s (ρ t x)) (X : M × Plane E) :
    signedProductFlow ρ q (s + t) X =
      signedProductFlow ρ q s (signedProductFlow ρ q t X) := by
  apply Prod.ext
  · exact hρ X.1
  · change planeRotation (q * (s + t)) X.2 =
      planeRotation (q * s) (planeRotation (q * t) X.2)
    rw [mul_add, planeRotation_add, ContinuousLinearMap.comp_apply]

end Product

end InfoGeometry.Geometry.RealSignedCutMoment
