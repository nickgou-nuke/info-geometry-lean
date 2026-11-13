/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.KleinAssociatedSpinors
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The differential Dirac operator on the Klein cover

The base, affine deck action, positive quadratic form, and Clifford matrices
are the existing Klein owners. The operator differentiates actual fields
`(ℝ × ℝ) → (Fin 2 → ℂ)` using Mathlib's real Fréchet derivative.

The odd Pin lift acts by the existing matrix `reflectionPlus`. Its twisted
adjoint reflects the horizontal tangent coordinate. Consequently the Dirac
operator interchanges two glide-sign sectors: it does not preserve a single
sector. The proof below derives this sign from the chain rule and the actual
Clifford matrices. Equivariant differentiated fields descend through the
existing associated-quotient construction.

The two sectors both use the positive Clifford form and lifts of square one.
They differ by the central sign of the glide lift; they are not the two
different Clifford-sign conventions. No curved connection, smooth quotient
manifold structure, Hilbert completion, or Fredholm assertion is made here.
-/

noncomputable section

namespace InfoGeometry.Geometry.KleinPinDirac

open InfoGeometry.Topology.KleinQuotientDeckInvariants
open InfoGeometry.Topology.KleinDeckRepresentation
open InfoGeometry.Topology.KleinCliffordPinLift
open InfoGeometry.Topology.KleinAssociatedSpinors
open scoped KleinDeckRepresentation Matrix ContDiff

/-- The existing positive Clifford action, now as real continuous operators
on its existing complex spinor fibre. -/
def clifford (v : Tangent) : Spinor →L[ℝ] Spinor :=
  ((vectorPlus v).mulVecLin.restrictScalars ℝ).toContinuousLinearMap

@[simp] theorem clifford_apply (v : Tangent) (s : Spinor) :
    clifford v s = (vectorPlus v).mulVec s := rfl

/-- The differential coefficients are images of native Clifford generators. -/
theorem clifford_native (v : Tangent) (s : Spinor) :
    clifford v s =
      (positiveRepresentation (CliffordAlgebra.ι positiveForm v)).mulVec s := by
  rw [positiveRepresentation_vector]
  rfl

/-- The real Clifford volume matrix on this two-dimensional spinor model.
It is built from the existing generators, without a new scalar square root. -/
def cliffordVolume : Mat := vectorPlus ![1, 0] * vectorPlus ![0, 1]

theorem cliffordVolume_sq : cliffordVolume * cliffordVolume = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cliffordVolume, vectorPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem cliffordVolume_anticommute (v : Tangent) :
    cliffordVolume * vectorPlus v = -(vectorPlus v * cliffordVolume) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cliffordVolume, vectorPlus, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def gammaX : Spinor →L[ℝ] Spinor := clifford ![1, 0]
def gammaY : Spinor →L[ℝ] Spinor := clifford ![0, 1]

@[simp] theorem gammaX_apply (s : Spinor) : gammaX s = ![s 1, s 0] := by
  ext i
  fin_cases i <;>
    simp [gammaX, clifford, vectorPlus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

@[simp] theorem gammaY_apply (s : Spinor) : gammaY s = ![s 0, -s 1] := by
  ext i
  fin_cases i <;>
    simp [gammaY, clifford, vectorPlus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

/-- The two central choices of the positive Clifford reflection lift. -/
def reflection (sector : Bool) : Spinor ≃ₗ[ℂ] Spinor where
  toFun s := if sector then -![s 1, s 0] else ![s 1, s 0]
  invFun s := if sector then -![s 1, s 0] else ![s 1, s 0]
  left_inv s := by cases sector <;> ext i <;> fin_cases i <;> simp
  right_inv s := by cases sector <;> ext i <;> fin_cases i <;> simp
  map_add' s t := by cases sector <;> ext i <;> fin_cases i <;> simp
  map_smul' z s := by cases sector <;> ext i <;> fin_cases i <;> simp

theorem reflection_false_native (s : Spinor) :
    reflection false s = plusUnit.val.mulVec s := by
  ext i
  fin_cases i <;>
    simp [reflection, plusUnit, reflectionPlus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

theorem reflection_sq (sector : Bool) : reflection sector * reflection sector = 1 := by
  ext s i
  cases sector <;> fin_cases i <;> simp [reflection]

@[simp] theorem reflection_inv (sector : Bool) :
    (reflection sector)⁻¹ = reflection sector := by
  cases sector <;> rfl

theorem reflection_zpow (sector : Bool) (n : ℤ) :
    reflection sector ^ n = if n % 2 = 0 then 1 else reflection sector := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [zpow_add_one, ih]
      have hn : (n : ℤ) % 2 = 0 ∨ (n : ℤ) % 2 = 1 := by omega
      rcases hn with hn | hn <;>
        simp [Int.add_emod, hn, reflection_sq]
  | pred n ih =>
      rw [zpow_sub_one, ih, reflection_inv]
      have hn : (-(n : ℤ)) % 2 = 0 ∨ (-(n : ℤ)) % 2 = 1 := by omega
      rcases hn with hn | hn <;>
        simp [Int.sub_emod, hn, reflection_sq]

/-- An actual representation of the full affine deck group, obtained from
the existing flat-representation constructor and the chosen Clifford lift.
The horizontal cycle acts trivially. -/
def monodromy (sector : Bool) : KleinDeckGroup →* (Spinor ≃ₗ[ℂ] Spinor) :=
  flatRepresentation 1 (reflection sector) (by simp) (Commute.one_left _)

theorem monodromy_apply (sector : Bool) (g : KleinDeckGroup) (s : Spinor) :
    monodromy sector g s = if g.n % 2 = 0 then s else reflection sector s := by
  change ((1 : Spinor ≃ₗ[ℂ] Spinor) ^ g.m * reflection sector ^ g.n) s = _
  rw [one_zpow, one_mul, reflection_zpow]
  split_ifs <;> rfl

/-- The representation used in the differential theorem has exactly the
existing positive Pin matrix as its glide generator. -/
theorem monodromy_glide_native (s : Spinor) :
    monodromy false KleinDeckGroup.b s =
      (plusMonodromy false false KleinDeckGroup.b).val.mulVec s := by
  rw [show monodromy false KleinDeckGroup.b = reflection false by
    exact flatRepresentation_b _ _ _ _]
  rw [reflection_false_native]
  congr 1
  simp [plusMonodromy, flatRepresentation_b, signUnit]

def monodromyCLM (sector : Bool) (g : KleinDeckGroup) : Spinor →L[ℝ] Spinor :=
  ((monodromy sector g).toLinearMap.restrictScalars ℝ).toContinuousLinearMap

@[simp] theorem monodromyCLM_apply (sector : Bool) (g : KleinDeckGroup) (s : Spinor) :
    monodromyCLM sector g s = monodromy sector g s := rfl

theorem signR_sq (n : ℤ) : signR n * signR n = 1 := by
  unfold signR signZ
  split_ifs <;> norm_num

/-- Changing the glide-sign sector is precisely tensoring its action with
the orientation character of the actual affine deck transformation. -/
theorem monodromy_twist (sector : Bool) (g : KleinDeckGroup) (s : Spinor) :
    monodromy (!sector) g s = signR g.n • monodromy sector g s := by
  rw [monodromy_apply, monodromy_apply]
  by_cases hn : g.n % 2 = 0
  · simp [hn, signR, signZ]
  · cases sector <;> simp [hn, signR, signZ, reflection]

theorem gammaX_monodromy (sector : Bool) (g : KleinDeckGroup) (s : Spinor) :
    gammaX (monodromy sector g s) = monodromy sector g (gammaX s) := by
  rw [monodromy_apply, monodromy_apply]
  by_cases hn : g.n % 2 = 0
  · simp [hn]
  · cases sector <;> ext i <;> fin_cases i <;>
      simp [hn, reflection, gammaX_apply]

theorem gammaY_monodromy (sector : Bool) (g : KleinDeckGroup) (s : Spinor) :
    gammaY (monodromy sector g s) =
      signR g.n • monodromy sector g (gammaY s) := by
  rw [monodromy_apply, monodromy_apply]
  by_cases hn : g.n % 2 = 0
  · simp [hn, signR, signZ]
  · cases sector <;> ext i <;> fin_cases i <;>
      simp [hn, reflection, gammaY_apply, signR, signZ]

/-- The real derivative of the existing full affine deck action. -/
def deckDerivative (g : KleinDeckGroup) : PlanePoint →L[ℝ] PlanePoint :=
  ((signR g.n) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem hasFDerivAt_deckAction (g : KleinDeckGroup) (p : PlanePoint) :
    HasFDerivAt (deckAction g) (deckDerivative g) p := by
  unfold deckAction deckDerivative
  fun_prop

@[simp] theorem deckDerivative_horizontal (g : KleinDeckGroup) :
    deckDerivative g (signR g.n • ((1, 0) : PlanePoint)) = (1, 0) := by
  ext <;> simp [deckDerivative, signR_sq]

@[simp] theorem deckDerivative_vertical (g : KleinDeckGroup) :
    deckDerivative g ((0, 1) : PlanePoint) = (0, 1) := by
  ext <;> simp [deckDerivative]

/-- The cover-level Dirac operator has genuine first derivatives as its
coefficients; its scalar differentiation field is real. -/
def dirac (ψ : PlanePoint → Spinor) (p : PlanePoint) : Spinor :=
  gammaX (fderiv ℝ ψ p (1, 0)) + gammaY (fderiv ℝ ψ p (0, 1))

/-- Derivative covariance is obtained from the chain rule, not supplied as
a field of the equivariant-section datum. -/
theorem fderiv_equivariant_comp (sector : Bool)
    (ψ : equivariantSections (monodromy sector))
    (hψ : Differentiable ℝ (ψ : PlanePoint → Spinor))
    (g : KleinDeckGroup) (p : PlanePoint) :
    (fderiv ℝ (ψ : PlanePoint → Spinor) (deckAction g p)).comp (deckDerivative g) =
      (monodromyCLM sector g).comp (fderiv ℝ (ψ : PlanePoint → Spinor) p) := by
  have hleft := (hψ (deckAction g p)).hasFDerivAt.comp p (hasFDerivAt_deckAction g p)
  have hright := (monodromyCLM sector g).hasFDerivAt.comp p (hψ p).hasFDerivAt
  have heq : ((ψ : PlanePoint → Spinor) ∘ deckAction g) =
      (monodromyCLM sector g) ∘ (ψ : PlanePoint → Spinor) := by
    funext x
    exact ψ.property g x
  rw [heq] at hleft
  exact hleft.unique hright

/-- The actual differential operator interchanges orientation-twisted
sectors of the full deck group. -/
theorem dirac_equivariant (sector : Bool)
    (ψ : equivariantSections (monodromy sector))
    (hψ : Differentiable ℝ (ψ : PlanePoint → Spinor))
    (g : KleinDeckGroup) (p : PlanePoint) :
    dirac (ψ : PlanePoint → Spinor) (deckAction g p) =
      monodromy (!sector) g (dirac (ψ : PlanePoint → Spinor) p) := by
  have hc := fderiv_equivariant_comp sector ψ hψ g p
  have hx := congrArg (fun L : PlanePoint →L[ℝ] Spinor =>
    L (signR g.n • ((1, 0) : PlanePoint))) hc
  have hy := congrArg (fun L : PlanePoint →L[ℝ] Spinor => L (0, 1)) hc
  simp only [ContinuousLinearMap.comp_apply, deckDerivative_horizontal, map_smul,
    monodromyCLM_apply] at hx
  simp only [ContinuousLinearMap.comp_apply, deckDerivative_vertical,
    monodromyCLM_apply] at hy
  rw [dirac, hx, hy, map_smul, gammaX_monodromy, gammaY_monodromy,
    ← smul_add, ← map_add, ← monodromy_twist]
  rfl

/-- Differentiating a differentiable equivariant spinor produces an actual
element of the other sector's equivariant-section submodule. -/
def diracSection (sector : Bool)
    (ψ : equivariantSections (monodromy sector))
    (hψ : Differentiable ℝ (ψ : PlanePoint → Spinor)) :
    equivariantSections (monodromy (!sector)) :=
  ⟨dirac (ψ : PlanePoint → Spinor), dirac_equivariant sector ψ hψ⟩

/-- The differentiated field descends through the existing associated
quotient, with its target representation fixed by the proved twist law. -/
def descendedDiracSection (sector : Bool)
    (ψ : equivariantSections (monodromy sector))
    (hψ : Differentiable ℝ (ψ : PlanePoint → Spinor)) :
    DeckOrbitBase → AssociatedSpace (monodromy (!sector)) :=
  descendedSection (monodromy (!sector)) (diracSection sector ψ hψ)

theorem descendedDiracSection_projects (sector : Bool)
    (ψ : equivariantSections (monodromy sector))
    (hψ : Differentiable ℝ (ψ : PlanePoint → Spinor)) (q : DeckOrbitBase) :
    bundleProjection (monodromy (!sector)) (descendedDiracSection sector ψ hψ q) = q :=
  descendedSection_projects _ _ q

theorem dirac_add (ψ χ : PlanePoint → Spinor)
    (hψ : Differentiable ℝ ψ) (hχ : Differentiable ℝ χ) :
    dirac (ψ + χ) = dirac ψ + dirac χ := by
  funext p
  simp only [dirac, fderiv_add (hψ p) (hχ p), ContinuousLinearMap.add_apply,
    map_add, Pi.add_apply]
  abel

theorem dirac_smul (r : ℝ) (ψ : PlanePoint → Spinor)
    (hψ : Differentiable ℝ ψ) : dirac (r • ψ) = r • dirac ψ := by
  funext p
  simp [dirac, fderiv_const_smul (hψ p), smul_add]

/-- The operator domain retains both actual deck equivariance and real
differentiability. No differentiability law is assumed for arbitrary fields. -/
def differentiableSections (sector : Bool) :
    Submodule ℝ (equivariantSections (monodromy sector)) where
  carrier := {ψ | Differentiable ℝ (ψ : PlanePoint → Spinor)}
  zero_mem' := differentiable_const _
  add_mem' hψ hχ := hψ.add hχ
  smul_mem' r ψ hψ := hψ.const_smul r

/-- The constructed differential operator as a real linear map with an
explicit domain and the correctly twisted equivariant target. -/
def diracLinear (sector : Bool) :
    differentiableSections sector →ₗ[ℝ] equivariantSections (monodromy (!sector)) where
  toFun ψ := diracSection sector ψ.val ψ.property
  map_add' ψ χ := by
    apply Subtype.ext
    exact dirac_add _ _ ψ.property χ.property
  map_smul' r ψ := by
    apply Subtype.ext
    exact dirac_smul r _ ψ.property

theorem dirac_smooth (ψ : PlanePoint → Spinor)
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (dirac ψ) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
  exact (gammaX.contDiff.comp (hd.clm_apply contDiff_const)).add
    (gammaY.contDiff.comp (hd.clm_apply contDiff_const))

/-- Smooth equivariant fields on the actual cover; smoothness is a proved
property of the underlying function, independent of the quotient carrier. -/
def smoothSections (sector : Bool) :
    Submodule ℝ (equivariantSections (monodromy sector)) where
  carrier := {ψ | ContDiff ℝ ∞ (ψ : PlanePoint → Spinor)}
  zero_mem' := contDiff_const
  add_mem' hψ hχ := hψ.add hχ
  smul_mem' r ψ hψ := hψ.const_smul r

/-- The actual differential operator between the two smooth equivariance
sectors, with smoothness of its output proved from Fréchet calculus. -/
def diracSmoothLinear (sector : Bool) :
    smoothSections sector →ₗ[ℝ] smoothSections (!sector) where
  toFun ψ :=
    ⟨diracSection sector ψ.val (ψ.property.differentiable (by simp)),
      dirac_smooth _ ψ.property⟩
  map_add' ψ χ := by
    apply Subtype.ext
    apply Subtype.ext
    exact dirac_add _ _ (ψ.property.differentiable (by simp))
      (χ.property.differentiable (by simp))
  map_smul' r ψ := by
    apply Subtype.ext
    apply Subtype.ext
    exact dirac_smul r _ (ψ.property.differentiable (by simp))

/-! ## A nonzero field with a nonzero Dirac image -/

/-- A smooth periodic field in the positive glide-sign sector. Its two
components coincide, so the actual reflection lift fixes each fibre value. -/
def cosineField (p : PlanePoint) : Spinor :=
  fun _ => (Real.cos (2 * Real.pi * p.1) : ℂ)

theorem cosineField_equivariant :
    cosineField ∈ equivariantSections (monodromy false) := by
  intro g p
  have hcos :
      Real.cos (2 * Real.pi * (signR g.n * p.1 + (g.m : ℝ))) =
        Real.cos (2 * Real.pi * p.1) := by
    calc
      Real.cos (2 * Real.pi * (signR g.n * p.1 + (g.m : ℝ))) =
          Real.cos (signR g.n * (2 * Real.pi * p.1) + (g.m : ℝ) * (2 * Real.pi)) := by
            congr 1
            ring
      _ = Real.cos (signR g.n * (2 * Real.pi * p.1)) :=
        Real.cos_add_int_mul_two_pi _ _
      _ = Real.cos (2 * Real.pi * p.1) := by
        unfold signR signZ
        split_ifs <;> simp
  have hfield : cosineField (deckAction g p) = cosineField p := by
    ext i
    exact congrArg Complex.ofReal hcos
  rw [hfield, monodromy_apply]
  split_ifs
  · rfl
  · ext i
    fin_cases i <;> simp [reflection, cosineField]

def cosineFieldDerivative (p : PlanePoint) : PlanePoint →L[ℝ] Spinor :=
  ContinuousLinearMap.pi (fun _ : Fin 2 =>
    Complex.ofRealCLM.comp
      ((-Real.sin (2 * Real.pi * p.1)) •
        ((2 * Real.pi) • ContinuousLinearMap.fst ℝ ℝ ℝ)))

theorem cosineField_hasFDerivAt (p : PlanePoint) :
    HasFDerivAt cosineField (cosineFieldDerivative p) p := by
  unfold cosineField cosineFieldDerivative
  apply hasFDerivAt_pi.mpr
  intro i
  have harg : HasFDerivAt (fun x : PlanePoint => 2 * Real.pi * x.1)
      ((2 * Real.pi) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    fun_prop
  exact Complex.ofRealCLM.hasFDerivAt.comp p
    ((Real.hasDerivAt_cos _).comp_hasFDerivAt p harg)

theorem cosineField_differentiable : Differentiable ℝ cosineField :=
  fun p => (cosineField_hasFDerivAt p).differentiableAt

theorem cosineField_smooth : ContDiff ℝ ∞ cosineField := by
  unfold cosineField
  fun_prop

theorem dirac_cosineField (p : PlanePoint) :
    dirac cosineField p =
      fun _ => ((-(2 * Real.pi) * Real.sin (2 * Real.pi * p.1) : ℝ) : ℂ) := by
  rw [dirac, (cosineField_hasFDerivAt p).fderiv]
  ext i
  fin_cases i <;>
    simp [cosineFieldDerivative, gammaX_apply, gammaY_apply,
      ContinuousLinearMap.pi_apply, Complex.ofRealCLM_apply] <;> ring

theorem cosineField_nonzero : cosineField (0, 0) ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  norm_num [cosineField] at h0

theorem dirac_cosineField_nonzero : dirac cosineField (1 / 4, 0) ≠ 0 := by
  intro h
  rw [dirac_cosineField] at h
  have h0 := congrFun h (0 : Fin 2)
  have hangle : (2 * Real.pi * (1 / 4 : ℝ)) = Real.pi / 2 := by ring
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  norm_num [hangle, hp] at h0

/-- A concrete inhabitant of the differentiable source sector. -/
def cosineSection : equivariantSections (monodromy false) :=
  ⟨cosineField, cosineField_equivariant⟩

def cosineDifferentiableSection : differentiableSections false :=
  ⟨cosineSection, cosineField_differentiable⟩

def cosineSmoothSection : smoothSections false :=
  ⟨cosineSection, cosineField_smooth⟩

/-- The nonzero image lies in the opposite sector by the proved chain-rule
theorem, so its associated-quotient descent is available without extra data. -/
theorem cosineSection_dirac_nonzero :
    (diracSection false cosineSection cosineField_differentiable).val (1 / 4, 0) ≠ 0 :=
  dirac_cosineField_nonzero

end InfoGeometry.Geometry.KleinPinDirac

end
