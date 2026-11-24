/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
import InfoGeometry.Clifford.Cl44BornReciprocity
import InfoGeometry.Clifford.Cl44VolumeElement
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Native real `Cl(4,4)` operators on the doubled Zorn carrier

An explicit quadratic isometry joins the existing diagonal `splitQ44` owner
to the existing Zorn norm and universal Dirac representation. Normalized Witt
CAR, the negative-generator involution, and the ordered volume are transported
through that algebra homomorphism.

The coordinate map is a quadratic isometry. No multiplicativity theorem for
an additional octonion table is assumed, and no equivalence between the full
Clifford algebra and the endomorphism algebra is asserted here.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.ZornCl44DiracTransport

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Clifford.Cl44BornReciprocity
open InfoGeometry.Clifford.Cl44VolumeElement
open InfoGeometry.Clifford.KoszulFoundation
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

/-- Group the diagonal eight coordinates into two scalar/vector quadruples. -/
def splitCartesianEquiv : (Fin 8 → ℝ) ≃ₗ[ℝ] CartesianCoordinates where
  toFun v := ((v 0, ![v 1, v 2, v 3]), (v 4, ![v 5, v 6, v 7]))
  invFun qr := ![qr.1.1, qr.1.2 0, qr.1.2 1, qr.1.2 2,
    qr.2.1, qr.2.2 0, qr.2.2 1, qr.2.2 2]
  left_inv v := by
    funext i
    fin_cases i <;> rfl
  right_inv qr := by
    apply Prod.ext <;> apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  map_add' v w := by
    apply Prod.ext <;> apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  map_smul' r v := by
    apply Prod.ext <;> apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
    · funext i; fin_cases i <;> rfl

/-- Reuse the established circular Zorn coordinate equivalence. -/
def splitZornEquiv : (Fin 8 → ℝ) ≃ₗ[ℝ] ZornMatrix ℝ :=
  splitCartesianEquiv.trans cartesianZornLinearEquiv

theorem splitZornEquiv_norm (v : Fin 8 → ℝ) :
    zornNorm (splitZornEquiv v) = splitQ44 v := by
  rw [zornNorm_apply]
  change InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
      (cartesianZornLinearEquiv (splitCartesianEquiv v)) = splitQ44 v
  rw [detZ_cartesianZornLinearEquiv]
  simp [quaternionNorm, splitCartesianEquiv, splitQ44_apply, dot]
  ring

/-- A native quadratic-form isometry, with the inverse supplied by the owner maps. -/
def splitZornIsometry : splitQ44.IsometryEquiv (zornNorm (R := ℝ)) :=
  { splitZornEquiv with map_app' := splitZornEquiv_norm }

/-- The actual Clifford equivalence induced by the quadratic isometry. -/
def splitZornCliffordEquiv :
    Cl44 ≃ₐ[ℝ] CliffordAlgebra (zornNorm (R := ℝ)) :=
  CliffordAlgebra.equivOfIsometry splitZornIsometry

/-- The existing real doubled Zorn carrier. -/
abbrev DiracCarrier := DiracSpinor16 (R := ℝ)

/-- Its dimension is computed through the same coordinate equivalence. -/
theorem diracCarrier_finrank : Module.finrank ℝ DiracCarrier = 16 := by
  change Module.finrank ℝ (ZornMatrix ℝ × ZornMatrix ℝ) = 16
  rw [← (splitZornEquiv.prodCongr splitZornEquiv).finrank_eq]
  simp

/-- Compose the native Clifford transport with the established Zorn representation. -/
def diracRepresentation : Cl44 →ₐ[ℝ] Module.End ℝ DiracCarrier :=
  (zornCliffordRepresentation (R := ℝ)).comp splitZornCliffordEquiv.toAlgHom

@[simp] theorem diracRepresentation_ι (v : Fin 8 → ℝ) :
    diracRepresentation (CliffordAlgebra.ι splitQ44 v) =
      diracGammaLinear (splitZornEquiv v) := by
  change zornCliffordRepresentation
      (CliffordAlgebra.map splitZornIsometry.toIsometry
        (CliffordAlgebra.ι splitQ44 v)) = _
  simp only [CliffordAlgebra.map_apply_ι, zornCliffordRepresentation_ι]

/-- Readback on the two genuine eight-dimensional Zorn sheets. -/
theorem diracRepresentation_generator_apply (v : Fin 8 → ℝ) (S C : ZornMatrix ℝ) :
    diracRepresentation (CliffordAlgebra.ι splitQ44 v) (S, C) =
      (splitZornEquiv v * C, zornConj (splitZornEquiv v) * S) := by
  rw [diracRepresentation_ι]
  rfl

/-- The polarized Clifford identity on the actual real operator carrier. -/
theorem diracGamma_polar (v w : Fin 8 → ℝ) :
    diracGammaLinear (splitZornEquiv v) * diracGammaLinear (splitZornEquiv w) +
      diracGammaLinear (splitZornEquiv w) * diracGammaLinear (splitZornEquiv v) =
      algebraMap ℝ (Module.End ℝ DiracCarrier) (QuadraticMap.polar splitQ44 v w) := by
  have h := congrArg diracRepresentation
    (CliffordAlgebra.ι_mul_ι_add_swap (Q := splitQ44) v w)
  simpa only [map_add, map_mul, AlgHom.commutes, diracRepresentation_ι] using h

def positiveGamma (i : Fin 4) : Module.End ℝ DiracCarrier := diracRepresentation (e i)
def negativeGamma (i : Fin 4) : Module.End ℝ DiracCarrier := diracRepresentation (f i)
def primalWitt (i : Fin 4) : Module.End ℝ DiracCarrier := diracRepresentation (a i)
def dualWitt (i : Fin 4) : Module.End ℝ DiracCarrier := diracRepresentation (adag i)

theorem primalWitt_eq_half_sum (i : Fin 4) :
    primalWitt i = (1 / 2 : ℝ) • (positiveGamma i + negativeGamma i) := by
  simp only [primalWitt, a_eq_half_sum, map_smul, map_add, positiveGamma, negativeGamma]

theorem dualWitt_eq_half_sub (i : Fin 4) :
    dualWitt i = (1 / 2 : ℝ) • (positiveGamma i - negativeGamma i) := by
  simp only [dualWitt, adag_eq_half_sub, map_smul, map_sub, positiveGamma, negativeGamma]

/-- The primal CAR are transported from their existing owner. -/
theorem primalWitt_anticomm (i j : Fin 4) :
    primalWitt i * primalWitt j + primalWitt j * primalWitt i = 0 := by
  simpa only [map_add, map_mul, map_zero, primalWitt] using
    congrArg diracRepresentation (witt_annihilation_anticomm i j)

/-- The dual CAR are transported from their existing owner. -/
theorem dualWitt_anticomm (i j : Fin 4) :
    dualWitt i * dualWitt j + dualWitt j * dualWitt i = 0 := by
  simpa only [map_add, map_mul, map_zero, dualWitt] using
    congrArg diracRepresentation (witt_creation_anticomm i j)

/-- Both one-half normalizations give the unit mixed CAR. -/
theorem witt_mixed_CAR (i j : Fin 4) :
    primalWitt i * dualWitt j + dualWitt j * primalWitt i =
      if i = j then 1 else 0 := by
  by_cases hij : i = j <;>
    simpa [hij, primalWitt, dualWitt] using
      congrArg diracRepresentation (witt_CAR i j)

theorem primalWitt_sq (i : Fin 4) : primalWitt i * primalWitt i = 0 := by
  simpa only [map_mul, map_zero, primalWitt] using
    congrArg diracRepresentation (a_sq_zero i)

theorem dualWitt_sq (i : Fin 4) : dualWitt i * dualWitt i = 0 := by
  simpa only [map_mul, map_zero, dualWitt] using
    congrArg diracRepresentation (adag_sq_zero i)

/-- The actual negative-generator word acting on the doubled Zorn carrier. -/
def diracBorn : Module.End ℝ DiracCarrier := diracRepresentation bornWord

theorem diracBorn_eq_product :
    diracBorn = negativeGamma 0 * negativeGamma 1 * negativeGamma 2 * negativeGamma 3 := by
  simp only [diracBorn, bornWord_eq_product, map_mul, negativeGamma]

theorem diracBorn_sq : diracBorn * diracBorn = 1 := by
  simpa only [diracBorn, map_mul, map_one] using
    congrArg diracRepresentation bornWord_sq

theorem diracBorn_swaps_primal (i : Fin 4) :
    diracBorn * primalWitt i * diracBorn = dualWitt i := by
  simpa only [diracBorn, primalWitt, dualWitt, map_mul] using
    congrArg diracRepresentation (bornWord_conj_a i)

theorem diracBorn_swaps_dual (i : Fin 4) :
    diracBorn * dualWitt i * diracBorn = primalWitt i := by
  simpa only [diracBorn, primalWitt, dualWitt, map_mul] using
    congrArg diracRepresentation (bornWord_conj_adag i)

/-- The signed sheetwise coordinate reflection produced by the four-generator word. -/
def bornReflection : ZornMatrix ℝ ≃ₗ[ℝ] ZornMatrix ℝ where
  toFun Z := { a := Z.b, b := Z.a, x := -Z.y, y := -Z.x }
  invFun Z := { a := Z.b, b := Z.a, x := -Z.y, y := -Z.x }
  left_inv Z := by ext <;> simp
  right_inv Z := by ext <;> simp
  map_add' Z W := by ext <;> simp
  map_smul' r Z := by ext <;> simp

@[simp] theorem bornReflection_twice (Z : ZornMatrix ℝ) :
    bornReflection (bornReflection Z) = Z := by
  ext <;> simp [bornReflection]

/-- Four sparse generator actions identify the represented Born word exactly. -/
theorem diracBorn_apply (Ψ : DiracCarrier) :
    diracBorn Ψ = (bornReflection Ψ.1, bornReflection Ψ.2) := by
  rw [diracBorn_eq_product]
  simp only [negativeGamma, f, diracRepresentation_ι, Module.End.mul_apply]
  apply Prod.ext <;> ext i <;> (try fin_cases i) <;>
    simp [diracGammaLinear, diracGamma, cliffordMinus, cliffordPlus,
      splitZornEquiv, splitCartesianEquiv, cartesianZornLinearEquiv,
      fVec, zornConj, mul, dot, cross, bornReflection]

private theorem positiveWord_apply (Ψ : DiracCarrier) :
    (positiveGamma 0 * positiveGamma 1 * positiveGamma 2 * positiveGamma 3) Ψ =
      (bornReflection Ψ.1, -bornReflection Ψ.2) := by
  simp only [positiveGamma, e, diracRepresentation_ι, Module.End.mul_apply]
  apply Prod.ext <;> ext i <;> (try fin_cases i) <;>
    simp [diracGammaLinear, diracGamma, cliffordMinus, cliffordPlus,
      splitZornEquiv, splitCartesianEquiv, cartesianZornLinearEquiv,
      eVec, zornConj, mul, dot, cross, bornReflection]

/-- The represented ordered pseudoscalar uses the native volume owner. -/
def diracVolume : Module.End ℝ DiracCarrier := diracRepresentation volumeElement

private theorem volumeElement_eq_positive_born :
    volumeElement = e 0 * e 1 * e 2 * e 3 * bornWord := by
  simp [volumeElement, volumeVectorList, volumeVector, cliffordVolumeElement,
    List.ofFn_succ, bornWord_eq_product, e, f, mul_assoc]

/-- The source convention fixes the orientation: the volume is `+I` on the
first Zorn sheet and `-I` on the second. -/
theorem diracVolume_apply (Ψ : DiracCarrier) : diracVolume Ψ = (Ψ.1, -Ψ.2) := by
  have hword : diracVolume =
      (positiveGamma 0 * positiveGamma 1 * positiveGamma 2 * positiveGamma 3) *
        diracBorn := by
    simp only [diracVolume, volumeElement_eq_positive_born, map_mul,
      positiveGamma, diracBorn]
  rw [hword, Module.End.mul_apply, diracBorn_apply, positiveWord_apply]
  simp only [bornReflection_twice]

/-- Native endomorphism equality identifying the ordered volume with sheet grading. -/
theorem diracVolume_eq_grading :
    diracVolume = LinearMap.prodMap (LinearMap.id : Module.End ℝ (ZornMatrix ℝ))
      (-LinearMap.id : Module.End ℝ (ZornMatrix ℝ)) := by
  apply LinearMap.ext
  intro Ψ
  rw [diracVolume_apply]
  rfl

theorem diracVolume_sq : diracVolume * diracVolume = 1 := by
  simpa only [diracVolume, map_mul, map_one] using
    congrArg diracRepresentation volumeElement_sq

theorem diracVolume_anticommutes_positive (i : Fin 4) :
    diracVolume * positiveGamma i = -(positiveGamma i * diracVolume) := by
  simpa only [diracVolume, positiveGamma, map_mul, map_neg] using
    congrArg diracRepresentation (volumeElement_anticommutes_e i)

theorem diracVolume_anticommutes_negative (i : Fin 4) :
    diracVolume * negativeGamma i = -(negativeGamma i * diracVolume) := by
  simpa only [diracVolume, negativeGamma, map_mul, map_neg] using
    congrArg diracRepresentation (volumeElement_anticommutes_f i)

end InfoGeometry.Canonical.ZornCl44DiracTransport
