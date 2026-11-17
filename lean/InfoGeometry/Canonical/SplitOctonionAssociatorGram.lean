/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionBogoliubovCarrierBridge
import InfoGeometry.Canonical.SplitOctonionAlternativeLaws
import InfoGeometry.Thermo.AssociatorGramDissipation
import InfoGeometry.Thermo.ConstrainedBilinearProjection

/-!
# Positive associator dissipation on the full real split-octonion carrier

The existing `SplitOctonion` multiplication remains nonassociative. Its right
regular maps give the first-slot associator operator
`R(a,b) v = (v * a) * b - v * (a * b)`.

The observer form is the pullback of the existing positive doubled Hilbert
pairing through `splitOctonionQuaternionicCarrierEquiv`. It is distinct from
the split quadratic form. Squaring the actual associator operators in this
form gives a positive semidefinite response with an exact common-kernel
description.

For the energy direction `H = 1`, the normalized observer projection removes
exactly `span {1}`. The concrete example satisfies `[ell, iEll, j] = -2k`
and has production `4` at `ell`, while preserving the nonzero energy
direction. The same nonzero operator has zero production at `iEll`, whose
projection is nonzero. Thus zero production cannot generally be replaced by
zero projected force.

The associative-limit theorem explicitly places all three associator inputs
in one associative set. It makes no claim that one or two such inputs suffice.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionAssociatorGram

open InfoGeometry.Krein
open InfoGeometry.Thermo.AssociatorGramDissipation
open InfoGeometry.Thermo.ConstrainedBilinearProjection
open scoped BigOperators Quaternion

/-- Pull back the existing positive observer pairing to the full eight-dimensional carrier. -/
def observerForm : LinearMap.BilinForm ℝ SplitOctonion :=
  (doubledHilbertBilin (E := Quaternion ℝ)).compl₁₂
    splitOctonionQuaternionicCarrierEquiv.toLinearMap
    splitOctonionQuaternionicCarrierEquiv.toLinearMap

theorem observerForm_apply (x y : SplitOctonion) :
    observerForm x y =
      inner ℝ (splitOctonionQuaternionicCarrierEquiv x)
        (splitOctonionQuaternionicCarrierEquiv y) := rfl

theorem observerForm_coordinates (x y : SplitOctonion) :
    observerForm x y = inner ℝ x.a y.a + inner ℝ x.b y.b := by
  change doubledHilbertBilin (to_doubled x.a x.b) (to_doubled y.a y.b) = _
  exact doubledHilbertBilin_to_doubled x.a x.b y.a y.b

theorem observerForm_isSymm : observerForm.IsSymm :=
  ⟨fun x y => real_inner_comm _ _⟩

theorem observerForm_nonneg (x : SplitOctonion) : 0 ≤ observerForm x x := by
  rw [observerForm_apply]
  exact real_inner_self_nonneg

theorem observerForm_strictPos (x : SplitOctonion) (hx : x ≠ 0) :
    0 < observerForm x x := by
  rw [observerForm_apply]
  apply real_inner_self_pos.mpr
  intro hz
  apply hx
  apply splitOctonionQuaternionicCarrierEquiv.injective
  simpa only [map_zero] using hz

theorem observerForm_isPosSemidef : observerForm.IsPosSemidef where
  isSymm := observerForm_isSymm
  isNonneg := ⟨observerForm_nonneg⟩

/-- The associator is linear in the force slot, using the native right regular maps. -/
def leakageOperator (a b : SplitOctonion) : Module.End ℝ SplitOctonion :=
  (SplitOctonion.rightRegular b).comp (SplitOctonion.rightRegular a) -
    SplitOctonion.rightRegular (a * b)

@[simp] theorem leakageOperator_apply (a b v : SplitOctonion) :
    leakageOperator a b v = SplitOctonion.associator v a b := rfl

theorem leakageOperator_self_left (a b : SplitOctonion) :
    leakageOperator a b a = 0 := by
  rw [leakageOperator_apply, SplitOctonion.associator,
    SplitOctonion.left_alternative, sub_self]

/-- A finite family of actual associators produces a native real bilinear form. -/
def dissipation {ι : Type*} [Fintype ι] (a b : ι → SplitOctonion)
    (P : Module.End ℝ SplitOctonion) (γ : ℝ) :
    LinearMap.BilinForm ℝ SplitOctonion :=
  gramForm observerForm (fun i => leakageOperator (a i) (b i)) P γ

theorem dissipation_apply {ι : Type*} [Fintype ι] (a b : ι → SplitOctonion)
    (P : Module.End ℝ SplitOctonion) (γ : ℝ) (x y : SplitOctonion) :
    dissipation a b P γ x y = γ * ∑ i,
      observerForm (SplitOctonion.associator (P x) (a i) (b i))
        (SplitOctonion.associator (P y) (a i) (b i)) := by
  simp only [dissipation, gramForm_apply, leakageOperator_apply]

/-- These squares use the positive observer norm, not the indefinite split norm. -/
theorem dissipation_self_eq_sum_norm_sq {ι : Type*} [Fintype ι]
    (a b : ι → SplitOctonion) (P : Module.End ℝ SplitOctonion)
    (γ : ℝ) (x : SplitOctonion) :
    dissipation a b P γ x x = γ * ∑ i,
      ‖splitOctonionQuaternionicCarrierEquiv
        (SplitOctonion.associator (P x) (a i) (b i))‖ ^ 2 := by
  simp only [dissipation_apply, observerForm_apply, real_inner_self_eq_norm_sq]

theorem dissipation_isSymm {ι : Type*} [Fintype ι] (a b : ι → SplitOctonion)
    (P : Module.End ℝ SplitOctonion) (γ : ℝ) : (dissipation a b P γ).IsSymm :=
  gramForm_isSymm observerForm _ P γ observerForm_isSymm

theorem dissipation_isPosSemidef {ι : Type*} [Fintype ι]
    (a b : ι → SplitOctonion) (P : Module.End ℝ SplitOctonion)
    (γ : ℝ) (hγ : 0 ≤ γ) : (dissipation a b P γ).IsPosSemidef :=
  gramForm_isPosSemidef observerForm _ P γ observerForm_isPosSemidef hγ

theorem dissipation_self_eq_zero_iff {ι : Type*} [Fintype ι]
    (a b : ι → SplitOctonion) (P : Module.End ℝ SplitOctonion)
    (γ : ℝ) (hγ : 0 < γ) (x : SplitOctonion) :
    dissipation a b P γ x x = 0 ↔
      ∀ i, SplitOctonion.associator (P x) (a i) (b i) = 0 := by
  simpa only [dissipation, leakageOperator_apply] using
    gramForm_self_eq_zero_iff observerForm
      (fun i => leakageOperator (a i) (b i)) P γ observerForm_strictPos hγ x

theorem dissipation_self_pos_iff {ι : Type*} [Fintype ι]
    (a b : ι → SplitOctonion) (P : Module.End ℝ SplitOctonion)
    (γ : ℝ) (hγ : 0 < γ) (x : SplitOctonion) :
    0 < dissipation a b P γ x x ↔
      ∃ i, SplitOctonion.associator (P x) (a i) (b i) ≠ 0 := by
  simpa only [dissipation, leakageOperator_apply] using
    gramForm_self_pos_iff observerForm
      (fun i => leakageOperator (a i) (b i)) P γ observerForm_strictPos hγ x

/-- The full radical remains an intersection of native operator kernels. -/
theorem ker_dissipation {ι : Type*} [Fintype ι]
    (a b : ι → SplitOctonion) (P : Module.End ℝ SplitOctonion)
    (γ : ℝ) (hγ : 0 < γ) :
    LinearMap.ker (dissipation a b P γ) =
      ⨅ i, LinearMap.ker ((leakageOperator (a i) (b i)).comp P) :=
  ker_gramForm observerForm _ P γ observerForm_strictPos hγ

/-- Every argument belongs to the same associative set in this limit theorem. -/
theorem dissipation_eq_zero_on_associative_set {ι : Type*} [Fintype ι]
    (a b : ι → SplitOctonion) (P : Module.End ℝ SplitOctonion)
    (γ : ℝ) (x y : SplitOctonion) (S : Set SplitOctonion)
    (hassoc : ∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, (u * v) * w = u * (v * w))
    (hx : P x ∈ S) (ha : ∀ i, a i ∈ S) (hb : ∀ i, b i ∈ S) :
    dissipation a b P γ x y = 0 := by
  apply gramForm_eq_zero_of_commonKernel observerForm _ P γ x y
  intro i
  rw [leakageOperator_apply, SplitOctonion.associator,
    hassoc (P x) hx (a i) (ha i) (b i) (hb i), sub_self]

/-- The embedded quaternion copy gives an actual associative triple. -/
theorem associator_quaternion_copy (u v w : Quaternion ℝ) :
    SplitOctonion.associator ⟨u, 0⟩ ⟨v, 0⟩ ⟨w, 0⟩ = 0 := by
  apply SplitOctonion.ext <;> simp [SplitOctonion.associator, mul_assoc]

theorem observerForm_one_one : observerForm (1 : SplitOctonion) 1 = 1 := by
  simp [observerForm_coordinates, Quaternion.inner_def]

/-- The exact observer-orthogonal projection away from the energy direction `1`. -/
def energyProjection : Module.End ℝ SplitOctonion :=
  center observerForm (1 : SplitOctonion)

theorem energyProjection_apply (x : SplitOctonion) :
    energyProjection x = x - observerForm 1 x • (1 : SplitOctonion) := rfl

@[simp] theorem energyProjection_one : energyProjection (1 : SplitOctonion) = 0 :=
  center_unit observerForm 1 observerForm_one_one

theorem energyProjection_pairing (x : SplitOctonion) :
    observerForm 1 (energyProjection x) = 0 :=
  center_pairing_left observerForm 1 observerForm_one_one x

theorem energyProjection_idempotent : IsIdempotentElem energyProjection := by
  change energyProjection.comp energyProjection = energyProjection
  apply LinearMap.ext
  intro x
  change center observerForm 1 (center observerForm 1 x) = center observerForm 1 x
  rw [center_apply, center_pairing_left observerForm 1 observerForm_one_one,
    zero_smul, sub_zero]

/-- No extra quaternionic constraint is silently included in the projection. -/
theorem ker_energyProjection :
    LinearMap.ker energyProjection =
      Submodule.span ℝ ({(1 : SplitOctonion)} : Set SplitOctonion) := by
  ext x
  exact center_eq_zero_iff observerForm 1 x observerForm_one_one

@[simp] theorem energyProjection_pureSecond (q : Quaternion ℝ) :
    energyProjection (⟨0, q⟩ : SplitOctonion) = ⟨0, q⟩ := by
  simp [energyProjection_apply, observerForm_coordinates]

/-- Every finite associator family is energy-degenerate under this projection. -/
theorem dissipation_energy {ι : Type*} [Fintype ι] (a b : ι → SplitOctonion)
    (γ : ℝ) (x : SplitOctonion) :
    dissipation a b energyProjection γ x 1 = 0 :=
  gramForm_eq_zero_of_projection_right observerForm _ energyProjection γ x 1
    energyProjection_one

theorem energy_direction_ne_zero : (1 : SplitOctonion) ≠ 0 := by
  intro h
  have hre := congrArg (fun z : SplitOctonion => z.a.re) h
  change (1 : ℝ) = 0 at hre
  exact one_ne_zero hre

/-! ## A nonzero associative defect with positive production -/

def ell : SplitOctonion := ⟨0, 1⟩

def iEll : SplitOctonion := ⟨0, ⟨0, 1, 0, 0⟩⟩

def quaternionJ : SplitOctonion := ⟨⟨0, 0, 1, 0⟩, 0⟩

theorem associator_ell_iEll_j :
    SplitOctonion.associator ell iEll quaternionJ =
      (⟨⟨0, 0, 0, -2⟩, 0⟩ : SplitOctonion) := by
  apply SplitOctonion.ext <;> apply Quaternion.ext <;>
    norm_num [SplitOctonion.associator, ell, iEll, quaternionJ]

theorem leakage_witness_ne_zero : leakageOperator iEll quaternionJ ell ≠ 0 := by
  rw [leakageOperator_apply, associator_ell_iEll_j]
  intro h
  have hk := congrArg (fun z : SplitOctonion => z.a.imK) h
  change (-2 : ℝ) = 0 at hk
  norm_num at hk

theorem multiplication_not_associative_at_witness :
    (ell * iEll) * quaternionJ ≠ ell * (iEll * quaternionJ) := by
  intro h
  apply leakage_witness_ne_zero
  rw [leakageOperator_apply, SplitOctonion.associator, h, sub_self]

@[simp] theorem energyProjection_ell : energyProjection ell = ell :=
  energyProjection_pureSecond 1

@[simp] theorem energyProjection_iEll : energyProjection iEll = iEll :=
  energyProjection_pureSecond ⟨0, 1, 0, 0⟩

/-- One genuine associator mode, with the nonzero energy direction removed. -/
def exampleDissipation : LinearMap.BilinForm ℝ SplitOctonion :=
  dissipation (fun _ : Unit => iEll) (fun _ : Unit => quaternionJ) energyProjection 1

theorem exampleDissipation_energy (x : SplitOctonion) :
    exampleDissipation x 1 = 0 :=
  dissipation_energy (fun _ : Unit => iEll) (fun _ : Unit => quaternionJ) 1 x

theorem exampleDissipation_ell_eq_four : exampleDissipation ell ell = 4 := by
  norm_num [exampleDissipation, dissipation_apply, energyProjection_ell,
    associator_ell_iEll_j, observerForm_coordinates,
    Quaternion.inner_self, Quaternion.normSq_def']

theorem exampleDissipation_ell_pos : 0 < exampleDissipation ell ell := by
  rw [exampleDissipation_ell_eq_four]
  norm_num

/-- The same nonzero operator has a stationary vector with nonzero projected force. -/
theorem exampleDissipation_iEll_eq_zero : exampleDissipation iEll iEll = 0 := by
  change dissipation (fun _ : Unit => iEll) (fun _ : Unit => quaternionJ)
    energyProjection 1 iEll iEll = 0
  apply (dissipation_self_eq_zero_iff _ _ _ 1 (by norm_num) iEll).mpr
  intro _
  rw [energyProjection_iEll]
  exact leakageOperator_self_left iEll quaternionJ

theorem energyProjection_iEll_ne_zero : energyProjection iEll ≠ 0 := by
  rw [energyProjection_iEll]
  intro h
  have hi := congrArg (fun z : SplitOctonion => z.b.imI) h
  change (1 : ℝ) = 0 at hi
  exact one_ne_zero hi

end InfoGeometry.Canonical.SplitOctonionAssociatorGram
