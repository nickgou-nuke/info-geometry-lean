/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NormalizedVectorPin
import InfoGeometry.Geometry.KleinPinDirac

/-!
# Freed's ordered suspension on the actual Klein spinor carrier

Let `γ` be the existing positive two-dimensional Clifford representation and
let `K = γ(e₁)γ(e₂)`. The already proved identities `K² = -1` and
`Kγ(v) = -γ(v)K` give the suspended vector action

`(v,t) ↦ -γ(v)K + tK`.

Its square is the real quadratic form `Q(v) - t²`, so the native Clifford
universal property gives a representation of Freed's actual target algebra.
The ordered product `ι(v,0) * ι(0,1)` then acts as exactly `γ(v)`.
This identifies the pulled-back representation, every represented normalized
Pin element, the actual Klein glide lift, and the coefficients of the
differential Dirac operator on the same spinor carrier.

The real volume matrix supplies the extra negative generator; no additional
scalar square root is introduced. These are representation-level statements.
No grading of the irreducible spinor fibre is inferred from the fact that
Freed's image lies in the ambient even Clifford algebra.
-/

noncomputable section

namespace InfoGeometry.Clifford.FreedKleinRepresentation

open InfoGeometry.Topology.KleinCliffordPinLift
open InfoGeometry.Geometry.KleinPinDirac
open InfoGeometry.Topology.KleinQuotientDeckInvariants
open InfoGeometry.Topology.KleinDeckRepresentation
open InfoGeometry.Topology.KleinAssociatedSpinors
open scoped Matrix ContDiff

local notation "Q₂" => InfoGeometry.Topology.KleinCliffordPinLift.positiveForm

/-- Freed's positive suspension of the existing real two-dimensional form. -/
abbrev targetForm := FreedCliffordSuspension.positiveForm Q₂

/-- The suspended Clifford vector action on the existing spinor matrices. -/
def targetVector : (Tangent × ℝ) →ₗ[ℝ] Mat where
  toFun x := -(vectorPlus x.1 * cliffordVolume) + x.2 • cliffordVolume
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_mul, neg_add, add_smul]
    abel
  map_smul' r x := by
    simp [smul_add, smul_neg, smul_smul, smul_eq_mul]

/-- The square law has the exact signature and scalar convention of the
native suspended quadratic form. -/
theorem targetVector_sq (x : Tangent × ℝ) :
    targetVector x * targetVector x = algebraMap ℝ Mat (targetForm x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [targetVector, cliffordVolume, vectorPlus, Matrix.mul_apply,
      Fin.sum_univ_two, targetForm,
      positiveForm_apply, Matrix.algebraMap_matrix_apply, smul_eq_mul] <;>
    ring

/-- An actual algebra homomorphism on Freed's full suspended Clifford algebra. -/
def representation : CliffordAlgebra targetForm →ₐ[ℝ] Mat :=
  CliffordAlgebra.lift targetForm ⟨targetVector, targetVector_sq⟩

@[simp] theorem representation_ι (x : Tangent × ℝ) :
    representation (CliffordAlgebra.ι targetForm x) = targetVector x :=
  CliffordAlgebra.lift_ι_apply _ _ _

theorem representation_extra :
    representation (CliffordAlgebra.ι targetForm (0, 1)) = cliffordVolume := by
  simp [targetVector]

theorem representation_vector (v : Tangent) :
    representation (CliffordAlgebra.ι targetForm (v, 0)) =
      -(vectorPlus v * cliffordVolume) := by
  simp [targetVector]

/-- The order `v * e` is essential: it recovers the original Clifford action. -/
theorem representation_ordered_pair (v : Tangent) :
    representation
      (CliffordAlgebra.ι targetForm (v, 0) *
        CliffordAlgebra.ι targetForm (0, 1)) = vectorPlus v := by
  rw [map_mul, representation_vector, representation_extra]
  simp [mul_assoc, cliffordVolume_sq]

/-- Equality on native Clifford generators determines the entire pulled-back
algebra representation, not only a numerical coefficient readout. -/
theorem pullback_eq_positiveRepresentation :
    representation.comp (FreedCliffordSuspension.positiveMap Q₂) =
      InfoGeometry.Topology.KleinCliffordPinLift.positiveRepresentation := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  change representation (FreedCliffordSuspension.positiveMap Q₂
    (CliffordAlgebra.ι Q₂ v)) =
      InfoGeometry.Topology.KleinCliffordPinLift.positiveRepresentation
        (CliffordAlgebra.ι Q₂ v)
  rw [FreedCliffordSuspension.positiveMap_ι, representation_ordered_pair,
    positiveRepresentation_vector]

/-- The actual restricted Pin homomorphism from PR338 has the same action
as the source Pin element, for every element of the generated subgroup. -/
theorem positivePinHom_representation (g : NormalizedVectorPin.pin Q₂) :
    Units.map representation.toMonoidHom
        (NormalizedVectorPin.evenPinToUnits targetForm
          (NormalizedVectorPin.positivePinHom Q₂ g)) =
      Units.map
        InfoGeometry.Topology.KleinCliffordPinLift.positiveRepresentation.toMonoidHom
        (g : (CliffordAlgebra Q₂)ˣ) := by
  apply Units.ext
  change representation (FreedCliffordSuspension.positiveMap Q₂
      ((g : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂)) = _
  exact congrArg
    (fun f : CliffordAlgebra Q₂ →ₐ[ℝ] Mat =>
      f ((g : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂))
    pullback_eq_positiveRepresentation

/-- The existing Klein glide reflection is represented by an actual element
of PR338's normalized-vector Pin subgroup. -/
def glidePin : NormalizedVectorPin.pin Q₂ :=
  NormalizedVectorPin.pinVector Q₂ ![1, 0]
    (Or.inl (by simp [positiveForm_apply]))

theorem suspended_glide_action (s : Spinor) :
    (Units.map representation.toMonoidHom
      (NormalizedVectorPin.evenPinToUnits targetForm
        (NormalizedVectorPin.positivePinHom Q₂ glidePin))).val.mulVec s =
      InfoGeometry.Geometry.KleinPinDirac.reflection false s := by
  rw [positivePinHom_representation]
  change
    (InfoGeometry.Topology.KleinCliffordPinLift.positiveRepresentation
      (((glidePin : NormalizedVectorPin.pin Q₂) :
        (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂)).mulVec s = _
  simp only [glidePin, NormalizedVectorPin.pinVector_coe,
    positiveRepresentation_vector]
  rw [reflection_false_native]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vectorPlus, plusUnit, reflectionPlus]

/-- The differential operator's coefficients are exactly the represented
ordered suspension products. Its Fréchet derivatives and spinor carrier are
unchanged by the proved representation identification. -/
theorem dirac_eq_ordered_suspension (ψ : PlanePoint → Spinor) (p : PlanePoint) :
    dirac ψ p =
      (representation
        (CliffordAlgebra.ι targetForm (![1, 0], 0) *
          CliffordAlgebra.ι targetForm (0, 1))).mulVec
        (fderiv ℝ ψ p (1, 0)) +
      (representation
        (CliffordAlgebra.ι targetForm (![0, 1], 0) *
          CliffordAlgebra.ι targetForm (0, 1))).mulVec
        (fderiv ℝ ψ p (0, 1)) := by
  rw [representation_ordered_pair, representation_ordered_pair]
  rfl

/-! ## The same-sector operator from the suspended vector coefficients

The source operator `dirac` interchanges the two orientation sectors. The
real volume action interchanges them once more. Consequently the operator
whose coefficients are the suspended vectors `targetVector (v,0)` preserves
each smooth sector. It equals `K ∘ dirac`; it is a distinct differential
operator from the source `dirac`.
-/

/-- The actual real continuous volume action on the existing spinor fibre. -/
def volumeAction : Spinor →L[ℝ] Spinor :=
  (cliffordVolume.mulVecLin.restrictScalars ℝ).toContinuousLinearMap

@[simp] theorem volumeAction_apply (s : Spinor) :
    volumeAction s = ![-s 1, s 0] := by
  ext i
  fin_cases i <;>
    simp [volumeAction, cliffordVolume, vectorPlus,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem volumeAction_sq (s : Spinor) : volumeAction (volumeAction s) = -s := by
  ext i
  fin_cases i <;> simp [volumeAction_apply]

theorem volumeAction_injective : Function.Injective volumeAction := by
  intro s t h
  have h' := congrArg volumeAction h
  simpa only [volumeAction_sq, neg_inj] using h'

/-- Volume multiplication itself changes the actual glide-sign sector. -/
theorem volumeAction_monodromy (sector : Bool) (g : KleinDeckGroup) (s : Spinor) :
    volumeAction (monodromy sector g s) =
      monodromy (!sector) g (volumeAction s) := by
  rw [monodromy_apply, monodromy_apply]
  by_cases hn : g.n % 2 = 0
  · simp [hn]
  · cases sector <;> ext i <;> fin_cases i <;>
      simp [hn, reflection, volumeAction_apply]

/-- A suspended tangent vector acts as the volume action after the source
Clifford action. This is the exact order forced by anticommutation. -/
theorem targetVector_mulVec_eq_volume_clifford (v : Tangent) (s : Spinor) :
    (targetVector (v, 0)).mulVec s = volumeAction (clifford v s) := by
  change (targetVector (v, 0)).mulVec s =
    cliffordVolume.mulVec ((vectorPlus v).mulVec s)
  rw [Matrix.mulVec_mulVec, cliffordVolume_anticommute]
  simp [targetVector]

/-- The cover-level operator formed from the actual suspended vector
coefficients, with real Fréchet differentiation on the same cover. -/
def suspendedDirac (ψ : PlanePoint → Spinor) (p : PlanePoint) : Spinor :=
  (targetVector (![1, 0], 0)).mulVec (fderiv ℝ ψ p (1, 0)) +
    (targetVector (![0, 1], 0)).mulVec (fderiv ℝ ψ p (0, 1))

/-- The source and suspended differential operators are related by the
actual volume action, rather than identified as the same operator. -/
theorem suspendedDirac_eq_volume_dirac (ψ : PlanePoint → Spinor) (p : PlanePoint) :
    suspendedDirac ψ p = volumeAction (dirac ψ p) := by
  simp only [suspendedDirac, targetVector_mulVec_eq_volume_clifford,
    dirac, map_add, gammaX, gammaY]

/-- The two proved sector changes compose to same-sector covariance. -/
theorem suspendedDirac_equivariant (sector : Bool)
    (ψ : equivariantSections (monodromy sector))
    (hψ : Differentiable ℝ (ψ : PlanePoint → Spinor))
    (g : KleinDeckGroup) (p : PlanePoint) :
    suspendedDirac (ψ : PlanePoint → Spinor) (deckAction g p) =
      monodromy sector g (suspendedDirac (ψ : PlanePoint → Spinor) p) := by
  rw [suspendedDirac_eq_volume_dirac, suspendedDirac_eq_volume_dirac,
    dirac_equivariant sector ψ hψ, volumeAction_monodromy]
  simp

/-- The suspended operator takes differentiable equivariant sections to
sections of the same associated representation. -/
def suspendedDiracSection (sector : Bool)
    (ψ : equivariantSections (monodromy sector))
    (hψ : Differentiable ℝ (ψ : PlanePoint → Spinor)) :
    equivariantSections (monodromy sector) :=
  ⟨suspendedDirac (ψ : PlanePoint → Spinor),
    suspendedDirac_equivariant sector ψ hψ⟩

/-- Its same-sector associated-quotient descent uses the existing quotient
construction and the differential covariance proved above. -/
def descendedSuspendedDiracSection (sector : Bool)
    (ψ : equivariantSections (monodromy sector))
    (hψ : Differentiable ℝ (ψ : PlanePoint → Spinor)) :
    DeckOrbitBase → AssociatedSpace (monodromy sector) :=
  descendedSection (monodromy sector) (suspendedDiracSection sector ψ hψ)

theorem descendedSuspendedDiracSection_projects (sector : Bool)
    (ψ : equivariantSections (monodromy sector))
    (hψ : Differentiable ℝ (ψ : PlanePoint → Spinor)) (q : DeckOrbitBase) :
    bundleProjection (monodromy sector)
      (descendedSuspendedDiracSection sector ψ hψ q) = q :=
  descendedSection_projects _ _ q

theorem suspendedDirac_smooth (ψ : PlanePoint → Spinor)
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (suspendedDirac ψ) := by
  have heq : suspendedDirac ψ = volumeAction ∘ dirac ψ :=
    funext (suspendedDirac_eq_volume_dirac ψ)
  rw [heq]
  exact volumeAction.contDiff.comp (dirac_smooth ψ hψ)

/-- A native real linear endomorphism of the actual smooth equivariant
domain, whose differential coefficients are the suspended representation. -/
def suspendedDiracSmoothLinear (sector : Bool) :
    smoothSections sector →ₗ[ℝ] smoothSections sector where
  toFun ψ :=
    ⟨suspendedDiracSection sector ψ.val (smoothSection_differentiable sector ψ),
      suspendedDirac_smooth _ (smoothSection_contDiff sector ψ)⟩
  map_add' ψ χ := by
    apply Subtype.ext
    apply Subtype.ext
    change suspendedDirac
        ((ψ.val : PlanePoint → Spinor) + (χ.val : PlanePoint → Spinor)) =
      suspendedDirac (ψ.val : PlanePoint → Spinor) +
        suspendedDirac (χ.val : PlanePoint → Spinor)
    funext p
    simp only [suspendedDirac_eq_volume_dirac,
      dirac_add _ _ (smoothSection_differentiable sector ψ)
        (smoothSection_differentiable sector χ), Pi.add_apply, map_add]
  map_smul' r ψ := by
    apply Subtype.ext
    apply Subtype.ext
    change suspendedDirac (r • (ψ.val : PlanePoint → Spinor)) =
      r • suspendedDirac (ψ.val : PlanePoint → Spinor)
    funext p
    simp only [suspendedDirac_eq_volume_dirac,
      dirac_smul r _ (smoothSection_differentiable sector ψ),
      Pi.smul_apply, map_smul]

/-- The same-sector operator has a concrete nonzero differential image. -/
theorem suspendedDirac_cosineField_nonzero :
    suspendedDirac cosineField (1 / 4, 0) ≠ 0 := by
  intro h
  apply dirac_cosineField_nonzero
  have h' := congrArg volumeAction h
  simpa only [suspendedDirac_eq_volume_dirac, volumeAction_sq,
    map_zero, neg_eq_zero] using h'

end InfoGeometry.Clifford.FreedKleinRepresentation

end
