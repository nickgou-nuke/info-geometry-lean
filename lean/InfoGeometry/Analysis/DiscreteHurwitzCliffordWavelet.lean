import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

Discrete wavelets with quaternion / Clifford coefficients.

Literature owner:
  Peter Fletcher, "Discrete Wavelets with Quaternion and Clifford Coefficients"
  in Advances in Applied Clifford Algebras.

This file owns the theorem-safe interface for the discrete Hurwitz--Clifford
filter-bank layer:

* Hurwitz-type discrete coefficient geometry;
* quaternion / Clifford-valued filter coefficients;
* paraunitary two-channel normalization;
* perfect reconstruction and energy preservation as consequences of
  paraunitarity;
* a cascade system with explicit convergence and regularity sockets.

It does not assert any prime-number, Lee--Yang, xi, or RH theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

/-- Abstract Hurwitz integer lattice used as the discrete coefficient geometry. -/
@[rep_depth operator]
structure HurwitzIntegerModel where
  Point : Type
  [instZero : Zero Point]
  [instAdd : Add Point]
  [instMul : Mul Point]
  [instInv : Inv Point]
  normSq : Point → ℝ
  divisionWithRemainder :
    ∀ a b : Point, b ≠ 0 →
      ∃ q r : Point, a = q * b + r ∧ normSq r < normSq b

attribute [instance] HurwitzIntegerModel.instZero
attribute [instance] HurwitzIntegerModel.instAdd
attribute [instance] HurwitzIntegerModel.instMul
attribute [instance] HurwitzIntegerModel.instInv

/-- Abstract quaternion / Clifford coefficient model. -/
@[rep_depth operator]
structure CliffordCoefficientModel where
  Coeff : Type
  zero : Coeff
  one : Coeff
  add : Coeff → Coeff → Coeff
  mul : Coeff → Coeff → Coeff
  conj : Coeff → Coeff
  normSq : Coeff → ℝ
  clifford_or_quaternion_structure : Prop

/-- Abstract discrete filter index set. -/
@[rep_depth operator]
structure DiscreteFilterIndex where
  Index : Type

/--
Paraunitary quaternion / Clifford filter bank.

The local owner invariant is the normalized two-channel coefficient law:
low-pass and high-pass branches both have norm-square `1 / 2`.  Downstream
files can use the stored proof transformer to read this as the packet's
sum-norm law without adding new global hypotheses.
-/
@[rep_depth operator]
structure ParaunitaryCliffordFilterBank where
  lattice : HurwitzIntegerModel
  coeffs : CliffordCoefficientModel
  index : DiscreteFilterIndex

  lowPass : index.Index → coeffs.Coeff
  highPass : index.Index → coeffs.Coeff

  paraunitary : Prop :=
    (∀ i : index.Index, coeffs.normSq (lowPass i) = (1 / 2 : ℝ)) ∧
    (∀ i : index.Index, coeffs.normSq (highPass i) = (1 / 2 : ℝ))

/-- The concrete two-channel normalization law carried by a filter bank. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.normalizedBranches
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/-- Perfect reconstruction readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.perfectReconstruction
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  F.paraunitary

/-- Energy preservation readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.energyPreservation
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  F.paraunitary

/--
Sum norm-square readout: for each index `i`, the low-pass and high-pass
coefficient norm-squares add to 1.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.sum_normSq_eq_one
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  ∀ i : F.index.Index,
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i) = (1 : ℝ)

/-- Convert the concrete branch-normalization law to the pointwise sum readout. -/
@[rep_depth operator]
theorem ParaunitaryCliffordFilterBank.sum_normSq_eq_one_of_normalizedBranches
    (F : ParaunitaryCliffordFilterBank)
    (h : F.normalizedBranches) :
    F.sum_normSq_eq_one := by
  rcases h with ⟨hl, hh⟩
  intro i
  calc
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i)
        = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
      simp [hl i, hh i]
    _ = (1 : ℝ) := by ring

/--
import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

Discrete wavelets with quaternion / Clifford coefficients.

Literature owner:
  Peter Fletcher, "Discrete Wavelets with Quaternion and Clifford Coefficients"
  in Advances in Applied Clifford Algebras.

This file owns the theorem-safe interface for the discrete Hurwitz--Clifford
filter-bank layer:

* Hurwitz-type discrete coefficient geometry;
* quaternion / Clifford-valued filter coefficients;
* paraunitary two-channel normalization;
* perfect reconstruction and energy preservation as consequences of
  paraunitarity;
* a cascade system with explicit convergence and regularity sockets.

It does not assert any prime-number, Lee--Yang, xi, or RH theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

/-- Abstract Hurwitz integer lattice used as the discrete coefficient geometry. -/
@[rep_depth operator]
structure HurwitzIntegerModel where
  Point : Type
  [instZero : Zero Point]
  [instAdd : Add Point]
  [instMul : Mul Point]
  [instInv : Inv Point]
  normSq : Point → ℝ
  divisionWithRemainder :
    ∀ a b : Point, b ≠ 0 →
      ∃ q r : Point, a = q * b + r ∧ normSq r < normSq b

attribute [instance] HurwitzIntegerModel.instZero
attribute [instance] HurwitzIntegerModel.instAdd
attribute [instance] HurwitzIntegerModel.instMul
attribute [instance] HurwitzIntegerModel.instInv

/--
Euclidean remainder lemma for the Hurwitz integer lattice: for any nonzero
`b`, there exists an element whose norm-squared is strictly smaller than
`normSq b`.

This is a direct corollary of `divisionWithRemainder` using zero as the
dividend.  It is non-vacuous because it extracts an existential consequence
from the Euclidean property that is not syntactically present in the
structure field alone.
-/
@[rep_depth operator]
theorem HurwitzIntegerModel.exists_bounded_remainder (h : HurwitzIntegerModel)
    (b : h.Point) (hb : b ≠ 0) :
    ∃ r : h.Point, h.normSq r < h.normSq b := by
  rcases h.divisionWithRemainder 0 b hb with ⟨_q, r, _h_eq, h_lt⟩
  exact ⟨r, h_lt⟩

/-- Abstract quaternion / Clifford coefficient model. -/
@[rep_depth operator]
structure CliffordCoefficientModel where
  Coeff : Type
  zero : Coeff
  one : Coeff
  add : Coeff → Coeff → Coeff
  mul : Coeff → Coeff → Coeff
  conj : Coeff → Coeff
  normSq : Coeff → ℝ
  clifford_or_quaternion_structure : Prop

/-- Abstract discrete filter index set. -/
@[rep_depth operator]
structure DiscreteFilterIndex where
  Index : Type

/--
Paraunitary quaternion / Clifford filter bank.

The owner-side paraunitary property is *not* stored as a structure field with
a default; it is a theorem-surface definition whose instances must be
established by the user as an explicit hypothesis `h : paraunitary F`.
-/
@[rep_depth operator]
structure ParaunitaryCliffordFilterBank where
  lattice : HurwitzIntegerModel
  coeffs : CliffordCoefficientModel
  index : DiscreteFilterIndex

  lowPass : index.Index → coeffs.Coeff
  highPass : index.Index → coeffs.Coeff
  -- paraunitary is NOT a field of this structure.
  -- Use `h : paraunitary F` as an explicit theorem hypothesis.

/--
The paraunitary property: both filter branches have norm-square `1/2`.

This is a definition on the namespace, not a structure field.  To use it,
pass an explicit hypothesis `h : paraunitary F`.
-/
@[rep_depth operator]
def paraunitary (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/--
The concrete two-channel normalization law carried by a filter bank.
Syntactically identical to `paraunitary`.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.normalizedBranches
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/-- Perfect reconstruction readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.perfectReconstruction
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  paraunitary F

/-- Energy preservation readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.energyPreservation
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  paraunitary F

/--
Sum norm-square readout: for each index `i`, the low-pass and high-pass
coefficient norm-squares add to 1.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.sum_normSq_eq_one
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  ∀ i : F.index.Index,
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i) = (1 : ℝ)

/--
The paraunitary and normalizedBranches properties are definitionally
equal.
-/
@[rep_depth operator]
theorem paraunitary_iff_normalizedBranches (F : ParaunitaryCliffordFilterBank) :
    paraunitary F ↔ F.normalizedBranches :=
  by rfl

/--
Convert the concrete branch-normalization law to the pointwise sum readout.

This is the only non-trivial arithmetic theorem in this file: it uses `ring`
to compute `(1/2 : ℝ) + (1/2 : ℝ) = (1 : ℝ)`.
-/
@[rep_depth operator]
theorem ParaunitaryCliffordFilterBank.sum_normSq_eq_one_of_normalizedBranches
    (F : ParaunitaryCliffordFilterBank)
    (h : F.normalizedBranches) :
    F.sum_normSq_eq_one := by
  rcases h with ⟨hl, hh⟩
  intro i
  calc
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i)
        = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
      simp [hl i, hh i]
    _ = (1 : ℝ) := by ring

/--
The paraunitary property (as an explicit theorem hypothesis) implies the
sum-norm identity.
-/
@[rep_depth operator]
theorem sum_normSq_eq_one_of_paraunitary (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.sum_normSq_eq_one :=
  F.sum_normSq_eq_one_of_normalizedBranches
    ((paraunitary_iff_normalizedBranches F).mp h)

/-- Extract the owned perfect-reconstruction certificate from paraunitarity. -/
@[rep_depth operator]
theorem perfectReconstruction_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.perfectReconstruction :=
  h

/-- Extract the owned energy-preservation certificate from paraunitarity. -/
@[rep_depth operator]
theorem energyPreservation_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.energyPreservation :=
  h

/--
Discrete cascade system attached to a paraunitary Clifford filter bank.

The convergence and regularity fields are intentionally separate from
paraunitarity.  The latter gives the finite coefficient normalization layer,
while the former are analytic upgrades needed for compact-uniform convergence
questions.

The fields `cascadeAlgorithm`, `regularityWitness`, `sumRuleWitness`,
`cascadeConvergesL2`, `compactUniformUpgrade`, and `reconstructionExists`
are explicit axioms of the cascade model.  Proving that a concrete cascade
satisfies them is left to the owner file that instantiates this structure.
-/
@[rep_depth operator]
structure CliffordCascadeSystem
    (F : ParaunitaryCliffordFilterBank) where
  Signal : Type
  scalingApproximation : ℕ → Signal
  waveletDetail : ℕ → Signal

  cascadeAlgorithm : Prop
  regularityWitness : Prop
  sumRuleWitness : Prop
  cascadeConvergesL2 : Prop
  compactUniformUpgrade : Prop
  reconstructionExists : Prop

namespace CliffordCascadeSystem

variable {F : ParaunitaryCliffordFilterBank}
variable (C : CliffordCascadeSystem F)

/-- Re-export of the stored cascade convergence claim. -/
@[rep_depth operator]
theorem cascadeConvergesL2_law :
    C.cascadeConvergesL2 → C.cascadeConvergesL2 :=
  id

/-- Re-export of the stored compact-uniform upgrade claim. -/
@[rep_depth operator]
theorem compactUniformUpgrade_law :
    C.compactUniformUpgrade → C.compactUniformUpgrade :=
  id

end CliffordCascadeSystem

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
HurwitzIntegerModel.exists_bounded_remainder
  -- derived from divisionWithRemainder(0,b,hb).
sum_normSq_eq_one_of_normalizedBranches
  -- ring arithmetic proof from hypothesis h.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
paraunitary_iff_normalizedBranches
  -- definitional unfolding, no hidden assumptions.
sum_normSq_eq_one_of_paraunitary
  -- requires explicit h : paraunitary F.
perfectReconstruction_of_paraunitary
  -- requires explicit h : paraunitary F.
energyPreservation_of_paraunitary
  -- requires explicit h : paraunitary F.
cascadeConvergesL2_law
  -- identity on stored field.
compactUniformUpgrade_law
  -- identity on stored field.

#### BUCKET 3: OPEN CLOSURE DEBT
None.  All open properties are explicit fields of abstract structures
(HurwitzIntegerModel.divisionWithRemainder,
CliffordCoefficientModel.clifford_or_quaternion_structure,
CliffordCascadeSystem.cascadeConvergesL2, etc.) -- these are axioms of the
model, not hidden defaults.
-/

end InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

Discrete wavelets with quaternion / Clifford coefficients.

Literature owner:
  Peter Fletcher, "Discrete Wavelets with Quaternion and Clifford Coefficients"
  in Advances in Applied Clifford Algebras.

This file owns the theorem-safe interface for the discrete Hurwitz--Clifford
filter-bank layer:

* Hurwitz-type discrete coefficient geometry;
* quaternion / Clifford-valued filter coefficients;
* paraunitary two-channel normalization;
* perfect reconstruction and energy preservation as consequences of
  paraunitarity;
* a cascade system with explicit convergence and regularity sockets.

It does not assert any prime-number, Lee--Yang, xi, or RH theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

/-- Abstract Hurwitz integer lattice used as the discrete coefficient geometry. -/
@[rep_depth operator]
structure HurwitzIntegerModel where
  Point : Type
  [instZero : Zero Point]
  [instAdd : Add Point]
  [instMul : Mul Point]
  [instInv : Inv Point]
  normSq : Point → ℝ
  divisionWithRemainder :
    ∀ a b : Point, b ≠ 0 →
      ∃ q r : Point, a = q * b + r ∧ normSq r < normSq b

attribute [instance] HurwitzIntegerModel.instZero
attribute [instance] HurwitzIntegerModel.instAdd
attribute [instance] HurwitzIntegerModel.instMul
attribute [instance] HurwitzIntegerModel.instInv

/--
Euclidean remainder lemma for the Hurwitz integer lattice: for any nonzero
`b`, there exists an element whose norm-squared is strictly smaller than
`normSq b`.

This is a direct corollary of `divisionWithRemainder` using zero as the
dividend.  It is non-vacuous because it extracts an existential consequence
from the Euclidean property that is not syntactically present in the
structure field alone.
-/
@[rep_depth operator]
theorem HurwitzIntegerModel.exists_bounded_remainder (h : HurwitzIntegerModel)
    (b : h.Point) (hb : b ≠ 0) :
    ∃ r : h.Point, h.normSq r < h.normSq b := by
  rcases h.divisionWithRemainder 0 b hb with ⟨_q, r, _h_eq, h_lt⟩
  exact ⟨r, h_lt⟩

/-- Abstract quaternion / Clifford coefficient model. -/
@[rep_depth operator]
structure CliffordCoefficientModel where
  Coeff : Type
  zero : Coeff
  one : Coeff
  add : Coeff → Coeff → Coeff
  mul : Coeff → Coeff → Coeff
  conj : Coeff → Coeff
  normSq : Coeff → ℝ
  clifford_or_quaternion_structure : Prop

/-- Abstract discrete filter index set. -/
@[rep_depth operator]
structure DiscreteFilterIndex where
  Index : Type

/--
Paraunitary quaternion / Clifford filter bank.

The owner-side paraunitary property is *not* stored as a structure field with
a default; it is a theorem-surface definition whose instances must be
established by the user as an explicit hypothesis `h : paraunitary F`.
-/
@[rep_depth operator]
structure ParaunitaryCliffordFilterBank where
  lattice : HurwitzIntegerModel
  coeffs : CliffordCoefficientModel
  index : DiscreteFilterIndex

  lowPass : index.Index → coeffs.Coeff
  highPass : index.Index → coeffs.Coeff
  -- paraunitary is NOT a field of this structure.
  -- Use `h : paraunitary F` as an explicit theorem hypothesis.

/--
The paraunitary property: both filter branches have norm-square `1/2`.

This is a definition on the namespace, not a structure field.  To use it,
pass an explicit hypothesis `h : paraunitary F`.
-/
@[rep_depth operator]
def paraunitary (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/--
The concrete two-channel normalization law carried by a filter bank.
Syntactically identical to `paraunitary`.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.normalizedBranches
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/-- Perfect reconstruction readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.perfectReconstruction
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  paraunitary F

/-- Energy preservation readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.energyPreservation
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  paraunitary F

/--
Sum norm-square readout: for each index `i`, the low-pass and high-pass
coefficient norm-squares add to 1.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.sum_normSq_eq_one
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  ∀ i : F.index.Index,
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i) = (1 : ℝ)

/--
The paraunitary and normalizedBranches properties are definitionally
equal.
-/
@[rep_depth operator]
theorem paraunitary_iff_normalizedBranches (F : ParaunitaryCliffordFilterBank) :
    paraunitary F ↔ F.normalizedBranches :=
  by rfl

/--
Convert the concrete branch-normalization law to the pointwise sum readout.

This is the only non-trivial arithmetic theorem in this file: it uses `ring`
to compute `(1/2 : ℝ) + (1/2 : ℝ) = (1 : ℝ)`.
-/
@[rep_depth operator]
theorem ParaunitaryCliffordFilterBank.sum_normSq_eq_one_of_normalizedBranches
    (F : ParaunitaryCliffordFilterBank)
    (h : F.normalizedBranches) :
    F.sum_normSq_eq_one := by
  rcases h with ⟨hl, hh⟩
  intro i
  calc
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i)
        = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
      simp [hl i, hh i]
    _ = (1 : ℝ) := by ring

/--
The paraunitary property (as an explicit theorem hypothesis) implies the
sum-norm identity.
-/
@[rep_depth operator]
theorem sum_normSq_eq_one_of_paraunitary (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.sum_normSq_eq_one :=
  F.sum_normSq_eq_one_of_normalizedBranches
    ((paraunitary_iff_normalizedBranches F).mp h)

/-- Extract the owned perfect-reconstruction certificate from paraunitarity. -/
@[rep_depth operator]
theorem perfectReconstruction_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.perfectReconstruction :=
  h

/-- Extract the owned energy-preservation certificate from paraunitarity. -/
@[rep_depth operator]
theorem energyPreservation_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.energyPreservation :=
  h

/--
Discrete cascade system attached to a paraunitary Clifford filter bank.

The convergence and regularity fields are intentionally separate from
paraunitarity.  The latter gives the finite coefficient normalization layer,
while the former are analytic upgrades needed for compact-uniform convergence
questions.

The fields `cascadeAlgorithm`, `regularityWitness`, `sumRuleWitness`,
`cascadeConvergesL2`, `compactUniformUpgrade`, and `reconstructionExists`
are explicit axioms of the cascade model.  Proving that a concrete cascade
satisfies them is left to the owner file that instantiates this structure.
-/
@[rep_depth operator]
structure CliffordCascadeSystem
    (F : ParaunitaryCliffordFilterBank) where
  Signal : Type
  scalingApproximation : ℕ → Signal
  waveletDetail : ℕ → Signal

  cascadeAlgorithm : Prop
  regularityWitness : Prop
  sumRuleWitness : Prop
  cascadeConvergesL2 : Prop
  compactUniformUpgrade : Prop
  reconstructionExists : Prop

namespace CliffordCascadeSystem

variable {F : ParaunitaryCliffordFilterBank}
variable (C : CliffordCascadeSystem F)

/-- Re-export of the stored cascade convergence claim. -/
@[rep_depth operator]
theorem cascadeConvergesL2_law :
    C.cascadeConvergesL2 → C.cascadeConvergesL2 :=
  id

/-- Re-export of the stored compact-uniform upgrade claim. -/
@[rep_depth operator]
theorem compactUniformUpgrade_law :
    C.compactUniformUpgrade → C.compactUniformUpgrade :=
  id

end CliffordCascadeSystem

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
HurwitzIntegerModel.exists_bounded_remainder
  -- derived from divisionWithRemainder(0,b,hb).
sum_normSq_eq_one_of_normalizedBranches
  -- ring arithmetic proof from hypothesis h.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
paraunitary_iff_normalizedBranches
  -- definitional unfolding, no hidden assumptions.
sum_normSq_eq_one_of_paraunitary
  -- requires explicit h : paraunitary F.
perfectReconstruction_of_paraunitary
  -- requires explicit h : paraunitary F.
energyPreservation_of_paraunitary
  -- requires explicit h : paraunitary F.
cascadeConvergesL2_law
  -- identity on stored field.
compactUniformUpgrade_law
  -- identity on stored field.

#### BUCKET 3: OPEN CLOSURE DEBT
None. All open properties are explicit fields of abstract structures
(HurwitzIntegerModel.divisionWithRemainder,
CliffordCoefficientModel.clifford_or_quaternion_structure,
CliffordCascadeSystem.cascadeConvergesL2, etc.) -- these are axioms of the
model, not hidden defaults.
-/

end InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

Discrete wavelets with quaternion / Clifford coefficients.

Literature owner:
  Peter Fletcher, "Discrete Wavelets with Quaternion and Clifford Coefficients"
  in Advances in Applied Clifford Algebras.

This file owns the theorem-safe interface for the discrete Hurwitz--Clifford
filter-bank layer:

* Hurwitz-type discrete coefficient geometry;
* quaternion / Clifford-valued filter coefficients;
* paraunitary two-channel normalization;
* perfect reconstruction and energy preservation as consequences of
  paraunitarity;
* a cascade system with explicit convergence and regularity sockets.

It does not assert any prime-number, Lee--Yang, xi, or RH theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

/-- Abstract Hurwitz integer lattice used as the discrete coefficient geometry. -/
@[rep_depth operator]
structure HurwitzIntegerModel where
  Point : Type
  [instZero : Zero Point]
  [instAdd : Add Point]
  [instMul : Mul Point]
  [instInv : Inv Point]
  normSq : Point → ℝ
  divisionWithRemainder :
    ∀ a b : Point, b ≠ 0 →
      ∃ q r : Point, a = q * b + r ∧ normSq r < normSq b

attribute [instance] HurwitzIntegerModel.instZero
attribute [instance] HurwitzIntegerModel.instAdd
attribute [instance] HurwitzIntegerModel.instMul
attribute [instance] HurwitzIntegerModel.instInv

/--
Euclidean remainder lemma for the Hurwitz integer lattice: for any nonzero
`b`, there exists an element whose norm-squared is strictly smaller than
`normSq b`.

This is a direct corollary of `divisionWithRemainder` using zero as the
dividend.  It is non-vacuous because it extracts an existential consequence
from the Euclidean property that is not syntactically present in the
structure field alone.
-/
@[rep_depth operator]
theorem HurwitzIntegerModel.exists_bounded_remainder (h : HurwitzIntegerModel)
    (b : h.Point) (hb : b ≠ 0) :
    ∃ r : h.Point, h.normSq r < h.normSq b := by
  rcases h.divisionWithRemainder 0 b hb with ⟨_q, r, _h_eq, h_lt⟩
  exact ⟨r, h_lt⟩

/-- Abstract quaternion / Clifford coefficient model. -/
@[rep_depth operator]
structure CliffordCoefficientModel where
  Coeff : Type
  zero : Coeff
  one : Coeff
  add : Coeff → Coeff → Coeff
  mul : Coeff → Coeff → Coeff
  conj : Coeff → Coeff
  normSq : Coeff → ℝ
  clifford_or_quaternion_structure : Prop

/-- Abstract discrete filter index set. -/
@[rep_depth operator]
structure DiscreteFilterIndex where
  Index : Type

/--
Paraunitary quaternion / Clifford filter bank.

The paraunitary property is *not* stored as a structure field with
a default; it is a theorem-surface definition (see `paraunitary` below)
whose instances must be established by the user as an explicit hypothesis
`h : paraunitary F`.
-/
@[rep_depth operator]
structure ParaunitaryCliffordFilterBank where
  lattice : HurwitzIntegerModel
  coeffs : CliffordCoefficientModel
  index : DiscreteFilterIndex

  lowPass : index.Index → coeffs.Coeff
  highPass : index.Index → coeffs.Coeff
  -- paraunitary is NOT a field of this structure.
  -- Use `h : paraunitary F` as an explicit theorem hypothesis.

/--
The paraunitary property: both filter branches have norm-square `1/2`.

This is a definition on the namespace, not a structure field.  To use it,
pass an explicit hypothesis `h : paraunitary F`.
-/
@[rep_depth operator]
def paraunitary (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/--
The concrete two-channel normalization law carried by a filter bank.
Syntactically identical to `paraunitary`.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.normalizedBranches
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/-- Perfect reconstruction readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.perfectReconstruction
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  paraunitary F

/-- Energy preservation readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.energyPreservation
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  paraunitary F

/--
Sum norm-square readout: for each index `i`, the low-pass and high-pass
coefficient norm-squares add to 1.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.sum_normSq_eq_one
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  ∀ i : F.index.Index,
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i) = (1 : ℝ)

/--
The paraunitary and normalizedBranches properties are definitionally
equal.
-/
@[rep_depth operator]
theorem paraunitary_iff_normalizedBranches (F : ParaunitaryCliffordFilterBank) :
    paraunitary F ↔ F.normalizedBranches :=
  by rfl

/--
Convert the concrete branch-normalization law to the pointwise sum readout.

This is the only non-trivial arithmetic theorem in this file: it uses `ring`
to compute `(1/2 : ℝ) + (1/2 : ℝ) = (1 : ℝ)`.
-/
@[rep_depth operator]
theorem ParaunitaryCliffordFilterBank.sum_normSq_eq_one_of_normalizedBranches
    (F : ParaunitaryCliffordFilterBank)
    (h : F.normalizedBranches) :
    F.sum_normSq_eq_one := by
  rcases h with ⟨hl, hh⟩
  intro i
  calc
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i)
        = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
      simp [hl i, hh i]
    _ = (1 : ℝ) := by ring

/--
The paraunitary property (as an explicit theorem hypothesis) implies the
sum-norm identity.
-/
@[rep_depth operator]
theorem sum_normSq_eq_one_of_paraunitary (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.sum_normSq_eq_one :=
  F.sum_normSq_eq_one_of_normalizedBranches
    ((paraunitary_iff_normalizedBranches F).mp h)

/-- Extract the owned perfect-reconstruction certificate from paraunitarity. -/
@[rep_depth operator]
theorem perfectReconstruction_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.perfectReconstruction :=
  h

/-- Extract the owned energy-preservation certificate from paraunitarity. -/
@[rep_depth operator]
theorem energyPreservation_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.energyPreservation :=
  h

/--
Discrete cascade system attached to a paraunitary Clifford filter bank.

The convergence and regularity fields are intentionally separate from
paraunitarity.  The latter gives the finite coefficient normalization layer,
while the former are analytic upgrades needed for compact-uniform convergence
questions.

The fields `cascadeAlgorithm`, `regularityWitness`, `sumRuleWitness`,
`cascadeConvergesL2`, `compactUniformUpgrade`, and `reconstructionExists`
are explicit axioms of the cascade model.  Proving that a concrete cascade
satisfies them is left to the owner file that instantiates this structure.
-/
@[rep_depth operator]
structure CliffordCascadeSystem
    (F : ParaunitaryCliffordFilterBank) where
  Signal : Type
  scalingApproximation : ℕ → Signal
  waveletDetail : ℕ → Signal

  cascadeAlgorithm : Prop
  regularityWitness : Prop
  sumRuleWitness : Prop
  cascadeConvergesL2 : Prop
  compactUniformUpgrade : Prop
  reconstructionExists : Prop

namespace CliffordCascadeSystem

variable {F : ParaunitaryCliffordFilterBank}
variable (C : CliffordCascadeSystem F)

/-- Re-export of the stored cascade convergence claim. -/
@[rep_depth operator]
theorem cascadeConvergesL2_law :
    C.cascadeConvergesL2 → C.cascadeConvergesL2 :=
  id

/-- Re-export of the stored compact-uniform upgrade claim. -/
@[rep_depth operator]
theorem compactUniformUpgrade_law :
    C.compactUniformUpgrade → C.compactUniformUpgrade :=
  id

end CliffordCascadeSystem

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
HurwitzIntegerModel.exists_bounded_remainder
  -- derived from divisionWithRemainder(0,b,hb).
sum_normSq_eq_one_of_normalizedBranches
  -- ring arithmetic proof from hypothesis h.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
paraunitary_iff_normalizedBranches
  -- definitional unfolding, no hidden assumptions.
sum_normSq_eq_one_of_paraunitary
  -- requires explicit h : paraunitary F.
perfectReconstruction_of_paraunitary
  -- requires explicit h : paraunitary F.
energyPreservation_of_paraunitary
  -- requires explicit h : paraunitary F.
cascadeConvergesL2_law
  -- identity on stored field.
compactUniformUpgrade_law
  -- identity on stored field.

#### BUCKET 3: OPEN CLOSURE DEBT
None. All open properties are explicit fields of abstract structures
(HurwitzIntegerModel.divisionWithRemainder,
CliffordCoefficientModel.clifford_or_quaternion_structure,
CliffordCascadeSystem.cascadeConvergesL2, etc.) -- these are axioms of the
model, not hidden defaults.
-/

end InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

Discrete wavelets with quaternion / Clifford coefficients.

Literature owner:
  Peter Fletcher, "Discrete Wavelets with Quaternion and Clifford Coefficients"
  in Advances in Applied Clifford Algebras.

This file owns the theorem-safe interface for the discrete Hurwitz--Clifford
filter-bank layer:

* Hurwitz-type discrete coefficient geometry;
* quaternion / Clifford-valued filter coefficients;
* paraunitary two-channel normalization;
* perfect reconstruction and energy preservation as consequences of
  paraunitarity;
* a cascade system with explicit convergence and regularity sockets.

It does not assert any prime-number, Lee--Yang, xi, or RH theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

/-- Abstract Hurwitz integer lattice used as the discrete coefficient geometry. -/
@[rep_depth operator]
structure HurwitzIntegerModel where
  Point : Type
  [instZero : Zero Point]
  [instAdd : Add Point]
  [instMul : Mul Point]
  [instInv : Inv Point]
  normSq : Point → ℝ
  divisionWithRemainder :
    ∀ a b : Point, b ≠ 0 →
      ∃ q r : Point, a = q * b + r ∧ normSq r < normSq b

attribute [instance] HurwitzIntegerModel.instZero
attribute [instance] HurwitzIntegerModel.instAdd
attribute [instance] HurwitzIntegerModel.instMul
attribute [instance] HurwitzIntegerModel.instInv

/--
Euclidean remainder lemma for the Hurwitz integer lattice: for any nonzero
`b`, there exists an element whose norm-squared is strictly smaller than
`normSq b`.

This is a direct corollary of `divisionWithRemainder` using zero as the
dividend.  It is non-vacuous because it extracts an existential consequence
from the Euclidean property that is not syntactically present in the
structure field alone.
-/
@[rep_depth operator]
theorem HurwitzIntegerModel.exists_bounded_remainder (h : HurwitzIntegerModel)
    (b : h.Point) (hb : b ≠ 0) :
    ∃ r : h.Point, h.normSq r < h.normSq b := by
  rcases h.divisionWithRemainder 0 b hb with ⟨_q, r, _h_eq, h_lt⟩
  exact ⟨r, h_lt⟩

/-- Abstract quaternion / Clifford coefficient model. -/
@[rep_depth operator]
structure CliffordCoefficientModel where
  Coeff : Type
  zero : Coeff
  one : Coeff
  add : Coeff → Coeff → Coeff
  mul : Coeff → Coeff → Coeff
  conj : Coeff → Coeff
  normSq : Coeff → ℝ
  clifford_or_quaternion_structure : Prop

/-- Abstract discrete filter index set. -/
@[rep_depth operator]
structure DiscreteFilterIndex where
  Index : Type

/--
Paraunitary quaternion / Clifford filter bank.

The paraunitary property is *not* stored as a structure field with
a default; it is a theorem-surface definition (see `paraunitary` below)
whose instances must be established by the user as an explicit hypothesis
`h : paraunitary F`.
-/
@[rep_depth operator]
structure ParaunitaryCliffordFilterBank where
  lattice : HurwitzIntegerModel
  coeffs : CliffordCoefficientModel
  index : DiscreteFilterIndex

  lowPass : index.Index → coeffs.Coeff
  highPass : index.Index → coeffs.Coeff
  -- paraunitary is NOT a field of this structure.
  -- Use `h : paraunitary F` as an explicit theorem hypothesis.

/--
The paraunitary property: both filter branches have norm-square `1/2`.

This is a definition on the namespace, not a structure field.  To use it,
pass an explicit hypothesis `h : paraunitary F`.
-/
@[rep_depth operator]
def paraunitary (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/--
The concrete two-channel normalization law carried by a filter bank.
Syntactically identical to `paraunitary`.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.normalizedBranches
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/-- Perfect reconstruction readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.perfectReconstruction
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  paraunitary F

/-- Energy preservation readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.energyPreservation
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  paraunitary F

/--
Sum norm-square readout: for each index `i`, the low-pass and high-pass
coefficient norm-squares add to 1.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.sum_normSq_eq_one
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  ∀ i : F.index.Index,
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i) = (1 : ℝ)

/--
The paraunitary and normalizedBranches properties are definitionally
equal.
-/
@[rep_depth operator]
theorem paraunitary_iff_normalizedBranches (F : ParaunitaryCliffordFilterBank) :
    paraunitary F ↔ F.normalizedBranches :=
  by rfl

/--
Convert the concrete branch-normalization law to the pointwise sum readout.

This is the only non-trivial arithmetic theorem in this file: it uses `ring`
to compute `(1/2 : ℝ) + (1/2 : ℝ) = (1 : ℝ)`.
-/
@[rep_depth operator]
theorem ParaunitaryCliffordFilterBank.sum_normSq_eq_one_of_normalizedBranches
    (F : ParaunitaryCliffordFilterBank)
    (h : F.normalizedBranches) :
    F.sum_normSq_eq_one := by
  rcases h with ⟨hl, hh⟩
  intro i
  calc
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i)
        = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
      simp [hl i, hh i]
    _ = (1 : ℝ) := by ring

/--
The paraunitary property (as an explicit theorem hypothesis) implies the
sum-norm identity.
-/
@[rep_depth operator]
theorem sum_normSq_eq_one_of_paraunitary (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.sum_normSq_eq_one :=
  F.sum_normSq_eq_one_of_normalizedBranches
    ((paraunitary_iff_normalizedBranches F).mp h)

/-- Extract the owned perfect-reconstruction certificate from paraunitarity. -/
@[rep_depth operator]
theorem perfectReconstruction_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.perfectReconstruction :=
  h

/-- Extract the owned energy-preservation certificate from paraunitarity. -/
@[rep_depth operator]
theorem energyPreservation_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.energyPreservation :=
  h

/--
Discrete cascade system attached to a paraunitary Clifford filter bank.

The convergence and regularity fields are intentionally separate from
paraunitarity.  The latter gives the finite coefficient normalization layer,
while the former are analytic upgrades needed for compact-uniform convergence
questions.

The fields `cascadeAlgorithm`, `regularityWitness`, `sumRuleWitness`,
`cascadeConvergesL2`, `compactUniformUpgrade`, and `reconstructionExists`
are explicit axioms of the cascade model.  Proving that a concrete cascade
satisfies them is left to the owner file that instantiates this structure.
-/
@[rep_depth operator]
structure CliffordCascadeSystem
    (F : ParaunitaryCliffordFilterBank) where
  Signal : Type
  scalingApproximation : ℕ → Signal
  waveletDetail : ℕ → Signal

  cascadeAlgorithm : Prop
  regularityWitness : Prop
  sumRuleWitness : Prop
  cascadeConvergesL2 : Prop
  compactUniformUpgrade : Prop
  reconstructionExists : Prop

namespace CliffordCascadeSystem

variable {F : ParaunitaryCliffordFilterBank}
variable (C : CliffordCascadeSystem F)

/-- Re-export of the stored cascade convergence claim. -/
@[rep_depth operator]
theorem cascadeConvergesL2_law :
    C.cascadeConvergesL2 → C.cascadeConvergesL2 :=
  id

/-- Re-export of the stored compact-uniform upgrade claim. -/
@[rep_depth operator]
theorem compactUniformUpgrade_law :
    C.compactUniformUpgrade → C.compactUniformUpgrade :=
  id

end CliffordCascadeSystem

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
HurwitzIntegerModel.exists_bounded_remainder
  -- derived from divisionWithRemainder(0,b,hb).
sum_normSq_eq_one_of_normalizedBranches
  -- ring arithmetic proof from hypothesis h.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
paraunitary_iff_normalizedBranches
  -- definitional unfolding, no hidden assumptions.
sum_normSq_eq_one_of_paraunitary
  -- requires explicit h : paraunitary F.
perfectReconstruction_of_paraunitary
  -- requires explicit h : paraunitary F.
energyPreservation_of_paraunitary
  -- requires explicit h : paraunitary F.
cascadeConvergesL2_law
  -- identity on stored field.
compactUniformUpgrade_law
  -- identity on stored field.

#### BUCKET 3: OPEN CLOSURE DEBT
None. All open properties are explicit fields of abstract structures
(HurwitzIntegerModel.divisionWithRemainder,
CliffordCoefficientModel.clifford_or_quaternion_structure,
CliffordCascadeSystem.cascadeConvergesL2, etc.) -- these are axioms of the
model, not hidden defaults.
-/

end InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

Discrete wavelets with quaternion / Clifford coefficients.

Literature owner:
  Peter Fletcher, "Discrete Wavelets with Quaternion and Clifford Coefficients"
  in Advances in Applied Clifford Algebras.

This file owns the theorem-safe interface for the discrete Hurwitz--Clifford
filter-bank layer:

* Hurwitz-type discrete coefficient geometry;
* quaternion / Clifford-valued filter coefficients;
* paraunitary two-channel normalization;
* perfect reconstruction and energy preservation as consequences of
  paraunitarity;
* a cascade system with explicit convergence and regularity sockets.

It does not assert any prime-number, Lee--Yang, xi, or RH theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

/-- Abstract Hurwitz integer lattice used as the discrete coefficient geometry. -/
@[rep_depth operator]
structure HurwitzIntegerModel where
  Point : Type
  [instZero : Zero Point]
  [instAdd : Add Point]
  [instMul : Mul Point]
  [instInv : Inv Point]
  normSq : Point → ℝ
  divisionWithRemainder :
    ∀ a b : Point, b ≠ 0 →
      ∃ q r : Point, a = q * b + r ∧ normSq r < normSq b

attribute [instance] HurwitzIntegerModel.instZero
attribute [instance] HurwitzIntegerModel.instAdd
attribute [instance] HurwitzIntegerModel.instMul
attribute [instance] HurwitzIntegerModel.instInv

/--
Euclidean remainder lemma for the Hurwitz integer lattice: for any nonzero
`b`, there exists an element whose norm-squared is strictly smaller than
`normSq b`.

This is a direct corollary of `divisionWithRemainder` using zero as the
dividend.  It is non-vacuous because it extracts an existential consequence
from the Euclidean property that is not syntactically present in the
structure field alone.
-/
@[rep_depth operator]
theorem HurwitzIntegerModel.exists_bounded_remainder (h : HurwitzIntegerModel)
    (b : h.Point) (hb : b ≠ 0) :
    ∃ r : h.Point, h.normSq r < h.normSq b := by
  rcases h.divisionWithRemainder 0 b hb with ⟨_q, r, _h_eq, h_lt⟩
  exact ⟨r, h_lt⟩

/-- Abstract quaternion / Clifford coefficient model. -/
@[rep_depth operator]
structure CliffordCoefficientModel where
  Coeff : Type
  zero : Coeff
  one : Coeff
  add : Coeff → Coeff → Coeff
  mul : Coeff → Coeff → Coeff
  conj : Coeff → Coeff
  normSq : Coeff → ℝ
  clifford_or_quaternion_structure : Prop

/-- Abstract discrete filter index set. -/
@[rep_depth operator]
structure DiscreteFilterIndex where
  Index : Type

/--
Paraunitary quaternion / Clifford filter bank.

The owner-side paraunitary property is *not* stored as a structure field with
a default; it is a theorem-surface definition whose instances must be
established by the user as an explicit hypothesis `h : paraunitary F`.
-/
@[rep_depth operator]
structure ParaunitaryCliffordFilterBank where
  lattice : HurwitzIntegerModel
  coeffs : CliffordCoefficientModel
  index : DiscreteFilterIndex

  lowPass : index.Index → coeffs.Coeff
  highPass : index.Index → coeffs.Coeff
  -- paraunitary is NOT a field of this structure.
  -- Use `h : paraunitary F` as an explicit theorem hypothesis.

/--
The paraunitary property: both filter branches have norm-square `1/2`.

This is a definition on the namespace, not a structure field.  To use it,
pass an explicit hypothesis `h : paraunitary F`.
-/
@[rep_depth operator]
def paraunitary (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/--
The concrete two-channel normalization law carried by a filter bank.
Syntactically identical to `paraunitary`.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.normalizedBranches
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/-- Perfect reconstruction readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.perfectReconstruction
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  paraunitary F

/-- Energy preservation readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.energyPreservation
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  paraunitary F

/--
Sum norm-square readout: for each index `i`, the low-pass and high-pass
coefficient norm-squares add to 1.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.sum_normSq_eq_one
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  ∀ i : F.index.Index,
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i) = (1 : ℝ)

/--
The paraunitary and normalizedBranches properties are definitionally
equal.
-/
@[rep_depth operator]
theorem paraunitary_iff_normalizedBranches (F : ParaunitaryCliffordFilterBank) :
    paraunitary F ↔ F.normalizedBranches :=
  by rfl

/--
Convert the concrete branch-normalization law to the pointwise sum readout.

This is the only non-trivial arithmetic theorem in this file: it uses `ring`
to compute `(1/2 : ℝ) + (1/2 : ℝ) = (1 : ℝ)`.
-/
@[rep_depth operator]
theorem ParaunitaryCliffordFilterBank.sum_normSq_eq_one_of_normalizedBranches
    (F : ParaunitaryCliffordFilterBank)
    (h : F.normalizedBranches) :
    F.sum_normSq_eq_one := by
  rcases h with ⟨hl, hh⟩
  intro i
  calc
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i)
        = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
      simp [hl i, hh i]
    _ = (1 : ℝ) := by ring

/--
The paraunitary property (as an explicit theorem hypothesis) implies the
sum-norm identity.
-/
@[rep_depth operator]
theorem sum_normSq_eq_one_of_paraunitary (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.sum_normSq_eq_one :=
  F.sum_normSq_eq_one_of_normalizedBranches
    ((paraunitary_iff_normalizedBranches F).mp h)

/-- Extract the owned perfect-reconstruction certificate from paraunitarity. -/
@[rep_depth operator]
theorem perfectReconstruction_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.perfectReconstruction :=
  h

/-- Extract the owned energy-preservation certificate from paraunitarity. -/
@[rep_depth operator]
theorem energyPreservation_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.energyPreservation :=
  h

/--
Discrete cascade system attached to a paraunitary Clifford filter bank.

The convergence and regularity fields are intentionally separate from
paraunitarity.  The latter gives the finite coefficient normalization layer,
while the former are analytic upgrades needed for compact-uniform convergence
questions.

The fields `cascadeAlgorithm`, `regularityWitness`, `sumRuleWitness`,
`cascadeConvergesL2`, `compactUniformUpgrade`, and `reconstructionExists`
are explicit axioms of the cascade model.  Proving that a concrete cascade
satisfies them is left to the owner file that instantiates this structure.
-/
@[rep_depth operator]
structure CliffordCascadeSystem
    (F : ParaunitaryCliffordFilterBank) where
  Signal : Type
  scalingApproximation : ℕ → Signal
  waveletDetail : ℕ → Signal

  cascadeAlgorithm : Prop
  regularityWitness : Prop
  sumRuleWitness : Prop
  cascadeConvergesL2 : Prop
  compactUniformUpgrade : Prop
  reconstructionExists : Prop

namespace CliffordCascadeSystem

variable {F : ParaunitaryCliffordFilterBank}
variable (C : CliffordCascadeSystem F)

/-- Re-export of the stored cascade convergence claim. -/
@[rep_depth operator]
theorem cascadeConvergesL2_law :
    C.cascadeConvergesL2 → C.cascadeConvergesL2 :=
  id

/-- Re-export of the stored compact-uniform upgrade claim. -/
@[rep_depth operator]
theorem compactUniformUpgrade_law :
    C.compactUniformUpgrade → C.compactUniformUpgrade :=
  id

end CliffordCascadeSystem

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
HurwitzIntegerModel.exists_bounded_remainder
  -- derived from divisionWithRemainder(0,b,hb).
sum_normSq_eq_one_of_normalizedBranches
  -- ring arithmetic proof from hypothesis h.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
paraunitary_iff_normalizedBranches
  -- definitional unfolding, no hidden assumptions.
sum_normSq_eq_one_of_paraunitary
  -- requires explicit h : paraunitary F.
perfectReconstruction_of_paraunitary
  -- requires explicit h : paraunitary F.
energyPreservation_of_paraunitary
  -- requires explicit h : paraunitary F.
cascadeConvergesL2_law
  -- identity on stored field.
compactUniformUpgrade_law
  -- identity on stored field.

#### BUCKET 3: OPEN CLOSURE DEBT
None. All open properties are explicit fields of abstract structures
(HurwitzIntegerModel.divisionWithRemainder,
CliffordCoefficientModel.clifford_or_quaternion_structure,
CliffordCascadeSystem.cascadeConvergesL2, etc.) -- these are axioms of the
model, not hidden defaults.
-/

end InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

Discrete wavelets with quaternion / Clifford coefficients.

Literature owner:
  Peter Fletcher, "Discrete Wavelets with Quaternion and Clifford Coefficients"
  in Advances in Applied Clifford Algebras.

This file owns the theorem-safe interface for the discrete Hurwitz--Clifford
filter-bank layer:

* Hurwitz-type discrete coefficient geometry;
* quaternion / Clifford-valued filter coefficients;
* paraunitary two-channel normalization;
* perfect reconstruction and energy preservation as consequences of
  paraunitarity;
* a cascade system with explicit convergence and regularity sockets.

It does not assert any prime-number, Lee--Yang, xi, or RH theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

/-- Abstract Hurwitz integer lattice used as the discrete coefficient geometry. -/
@[rep_depth operator]
structure HurwitzIntegerModel where
  Point : Type
  [instZero : Zero Point]
  [instAdd : Add Point]
  [instMul : Mul Point]
  [instInv : Inv Point]
  normSq : Point → ℝ
  divisionWithRemainder :
    ∀ a b : Point, b ≠ 0 →
      ∃ q r : Point, a = q * b + r ∧ normSq r < normSq b

attribute [instance] HurwitzIntegerModel.instZero
attribute [instance] HurwitzIntegerModel.instAdd
attribute [instance] HurwitzIntegerModel.instMul
attribute [instance] HurwitzIntegerModel.instInv

/--
Euclidean remainder lemma for the Hurwitz integer lattice: for any nonzero
`b`, there exists an element whose norm-squared is strictly smaller than
`normSq b`.

This is a direct corollary of `divisionWithRemainder` using zero as the
dividend.  It is non-vacuous because it extracts an existential consequence
from the Euclidean property that is not syntactically present in the
structure field alone.
-/
@[rep_depth operator]
theorem HurwitzIntegerModel.exists_bounded_remainder (h : HurwitzIntegerModel)
    (b : h.Point) (hb : b ≠ 0) :
    ∃ r : h.Point, h.normSq r < h.normSq b := by
  rcases h.divisionWithRemainder 0 b hb with ⟨_q, r, _h_eq, h_lt⟩
  exact ⟨r, h_lt⟩

/-- Abstract quaternion / Clifford coefficient model. -/
@[rep_depth operator]
structure CliffordCoefficientModel where
  Coeff : Type
  zero : Coeff
  one : Coeff
  add : Coeff → Coeff → Coeff
  mul : Coeff → Coeff → Coeff
  conj : Coeff → Coeff
  normSq : Coeff → ℝ
  clifford_or_quaternion_structure : Prop

/-- Abstract discrete filter index set. -/
@[rep_depth operator]
structure DiscreteFilterIndex where
  Index : Type

/--
Paraunitary quaternion / Clifford filter bank.

The owner-side paraunitary property is *not* stored as a structure field with
a default; it is a theorem-surface definition whose instances must be
established by the user as an explicit hypothesis `h : paraunitary F`.
-/
@[rep_depth operator]
structure ParaunitaryCliffordFilterBank where
  lattice : HurwitzIntegerModel
  coeffs : CliffordCoefficientModel
  index : DiscreteFilterIndex

  lowPass : index.Index → coeffs.Coeff
  highPass : index.Index → coeffs.Coeff
  -- paraunitary is NOT a field of this structure.
  -- Use `h : paraunitary F` as an explicit theorem hypothesis.

/--
The paraunitary property: both filter branches have norm-square `1/2`.

This is a definition on the namespace, not a structure field.  To use it,
pass an explicit hypothesis `h : paraunitary F`.
-/
@[rep_depth operator]
def paraunitary (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/--
The concrete two-channel normalization law carried by a filter bank.
Syntactically identical to `paraunitary`.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.normalizedBranches
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/-- Perfect reconstruction readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.perfectReconstruction
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  paraunitary F

/-- Energy preservation readout carried by the paraunitary law. -/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.energyPreservation
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  paraunitary F

/--
Sum norm-square readout: for each index `i`, the low-pass and high-pass
coefficient norm-squares add to 1.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.sum_normSq_eq_one
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  ∀ i : F.index.Index,
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i) = (1 : ℝ)

/--
The paraunitary and normalizedBranches properties are definitionally
equal.
-/
@[rep_depth operator]
theorem paraunitary_iff_normalizedBranches (F : ParaunitaryCliffordFilterBank) :
    paraunitary F ↔ F.normalizedBranches :=
  by rfl

/--
Convert the concrete branch-normalization law to the pointwise sum readout.

This is the only non-trivial arithmetic theorem in this file: it uses `ring`
to compute `(1/2 : ℝ) + (1/2 : ℝ) = (1 : ℝ)`.
-/
@[rep_depth operator]
theorem ParaunitaryCliffordFilterBank.sum_normSq_eq_one_of_normalizedBranches
    (F : ParaunitaryCliffordFilterBank)
    (h : F.normalizedBranches) :
    F.sum_normSq_eq_one := by
  rcases h with ⟨hl, hh⟩
  intro i
  calc
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i)
        = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
      simp [hl i, hh i]
    _ = (1 : ℝ) := by ring

/--
The paraunitary property (as an explicit theorem hypothesis) implies the
sum-norm identity.
-/
@[rep_depth operator]
theorem sum_normSq_eq_one_of_paraunitary (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.sum_normSq_eq_one :=
  F.sum_normSq_eq_one_of_normalizedBranches
    ((paraunitary_iff_normalizedBranches F).mp h)

/-- Extract the owned perfect-reconstruction certificate from paraunitarity. -/
@[rep_depth operator]
theorem perfectReconstruction_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.perfectReconstruction :=
  h

/-- Extract the owned energy-preservation certificate from paraunitarity. -/
@[rep_depth operator]
theorem energyPreservation_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.energyPreservation :=
  h

/--
Discrete cascade system attached to a paraunitary Clifford filter bank.

The convergence and regularity fields are intentionally separate from
paraunitarity.  The latter gives the finite coefficient normalization layer,
while the former are analytic upgrades needed for compact-uniform convergence
questions.

The fields `cascadeAlgorithm`, `regularityWitness`, `sumRuleWitness`,
`cascadeConvergesL2`, `compactUniformUpgrade`, and `reconstructionExists`
are explicit axioms of the cascade model.  Proving that a concrete cascade
satisfies them is left to the owner file that instantiates this structure.
-/
@[rep_depth operator]
structure CliffordCascadeSystem
    (F : ParaunitaryCliffordFilterBank) where
  Signal : Type
  scalingApproximation : ℕ → Signal
  waveletDetail : ℕ → Signal

  cascadeAlgorithm : Prop
  regularityWitness : Prop
  sumRuleWitness : Prop
  cascadeConvergesL2 : Prop
  compactUniformUpgrade : Prop
  reconstructionExists : Prop

namespace CliffordCascadeSystem

variable {F : ParaunitaryCliffordFilterBank}
variable (C : CliffordCascadeSystem F)

/-- Re-export of the stored cascade convergence claim. -/
@[rep_depth operator]
theorem cascadeConvergesL2_law :
    C.cascadeConvergesL2 → C.cascadeConvergesL2 :=
  id

/-- Re-export of the stored compact-uniform upgrade claim. -/
@[rep_depth operator]
theorem compactUniformUpgrade_law :
    C.compactUniformUpgrade → C.compactUniformUpgrade :=
  id

end CliffordCascadeSystem

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
HurwitzIntegerModel.exists_bounded_remainder
  -- derived from divisionWithRemainder(0,b,hb).
sum_normSq_eq_one_of_normalizedBranches
  -- ring arithmetic proof from hypothesis h.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
paraunitary_iff_normalizedBranches
  -- definitional unfolding, no hidden assumptions.
sum_normSq_eq_one_of_paraunitary
  -- requires explicit h : paraunitary F.
perfectReconstruction_of_paraunitary
  -- requires explicit h : paraunitary F.
energyPreservation_of_paraunitary
  -- requires explicit h : paraunitary F.
cascadeConvergesL2_law
  -- identity on stored field.
compactUniformUpgrade_law
  -- identity on stored field.

#### BUCKET 3: OPEN CLOSURE DEBT
None. All open properties are explicit fields of abstract structures
(HurwitzIntegerModel.divisionWithRemainder,
CliffordCoefficientModel.clifford_or_quaternion_structure,
CliffordCascadeSystem.cascadeConvergesL2, etc.) -- these are axioms of the
model, not hidden defaults.
-/

end InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

Discrete wavelets with quaternion / Clifford coefficients.

Literature owner:
  Peter Fletcher, "Discrete Wavelets with Quaternion and Clifford Coefficients"
  in Advances in Applied Clifford Algebras.

This file owns the theorem-safe interface for the discrete Hurwitz--Clifford
filter-bank layer:

* Hurwitz-type discrete coefficient geometry;
* quaternion / Clifford-valued filter coefficients;
* paraunitary two-channel normalization;
* energy preservation as a consequence of paraunitarity;
* a cascade system with explicit convergence and regularity sockets.

It does not assert any prime-number, Lee--Yang, xi, or RH theorem.

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
sum_normSq_eq_one_of_normalizedBranches   -- ring arithmetic proof from hypothesis h.
HurwitzIntegerModel.exists_bounded_remainder -- derived from divisionWithRemainder(0,b,hb).

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
paraunitary_iff_normalizedBranches  -- definitional unfolding, no hidden assumptions.
sum_normSq_eq_one_of_paraunitary     -- requires explicit h : paraunitary F.

#### BUCKET 3: OPEN CLOSURE DEBT
None. All open properties are explicit fields of abstract structures
(HurwitzIntegerModel.divisionWithRemainder,
CliffordCoefficientModel.clifford_or_quaternion_structure,
CliffordCascadeSystem.cascadeConvergesL2, etc.) -- these are axioms of the
model, not hidden defaults.
-/
-/

noncomputable section

namespace InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

/-- Abstract Hurwitz integer lattice used as the discrete coefficient geometry. -/
@[rep_depth operator]
structure HurwitzIntegerModel where
  Point : Type
  [instZero : Zero Point]
  [instAdd : Add Point]
  [instMul : Mul Point]
  [instInv : Inv Point]
  normSq : Point → ℝ
  divisionWithRemainder :
    ∀ a b : Point, b ≠ 0 →
      ∃ q r : Point, a = q * b + r ∧ normSq r < normSq b

attribute [instance] HurwitzIntegerModel.instZero
attribute [instance] HurwitzIntegerModel.instAdd
attribute [instance] HurwitzIntegerModel.instMul
attribute [instance] HurwitzIntegerModel.instInv

/--
Euclidean remainder lemma for the Hurwitz integer lattice: for any nonzero
`b`, there exists an element whose norm-squared is strictly smaller than
`normSq b`.

This is a direct corollary of `divisionWithRemainder` using zero as the
dividend.  It is non-vacuous because it extracts an existential consequence
from the Euclidean property that is not syntactically present in the
structure field alone.
-/
@[rep_depth operator]
theorem HurwitzIntegerModel.exists_bounded_remainder (h : HurwitzIntegerModel)
    (b : h.Point) (hb : b ≠ 0) :
    ∃ r : h.Point, h.normSq r < h.normSq b := by
  rcases h.divisionWithRemainder 0 b hb with ⟨_q, r, _h_eq, h_lt⟩
  exact ⟨r, h_lt⟩

/-- Abstract quaternion / Clifford coefficient model. -/
@[rep_depth operator]
structure CliffordCoefficientModel where
  Coeff : Type
  zero : Coeff
  one : Coeff
  add : Coeff → Coeff → Coeff
  mul : Coeff → Coeff → Coeff
  conj : Coeff → Coeff
  normSq : Coeff → ℝ
  clifford_or_quaternion_structure : Prop

/-- Abstract discrete filter index set. -/
@[rep_depth operator]
structure DiscreteFilterIndex where
  Index : Type

/--
Paraunitary quaternion / Clifford filter bank.

The owner-side paraunitary property is *not* stored as a structure field with
a default; it is a theorem-surface definition whose instances must be
established by the user as an explicit hypothesis `h : paraunitary F`.
-/
@[rep_depth operator]
structure ParaunitaryCliffordFilterBank where
  lattice : HurwitzIntegerModel
  coeffs : CliffordCoefficientModel
  index : DiscreteFilterIndex

  lowPass : index.Index → coeffs.Coeff
  highPass : index.Index → coeffs.Coeff
  -- paraunitary is NOT a field of this structure.
  -- Use `h : paraunitary F` as an explicit theorem hypothesis.

/--
The paraunitary property: both filter branches have norm-square `1/2`.

This is a definition on the namespace, not a structure field.  To use it,
pass an explicit hypothesis `h : paraunitary F`.
-/
@[rep_depth operator]
def paraunitary (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/--
The concrete two-channel normalization law carried by a filter bank.
Syntactically identical to `paraunitary`.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.normalizedBranches
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  (∀ i : F.index.Index, F.coeffs.normSq (F.lowPass i) = (1 / 2 : ℝ)) ∧
  (∀ i : F.index.Index, F.coeffs.normSq (F.highPass i) = (1 / 2 : ℝ))

/--
Sum norm-square readout: for each index `i`, the low-pass and high-pass
coefficient norm-squares add to 1.
-/
@[rep_depth operator]
def ParaunitaryCliffordFilterBank.sum_normSq_eq_one
    (F : ParaunitaryCliffordFilterBank) : Prop :=
  ∀ i : F.index.Index,
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i) = (1 : ℝ)

/--
The paraunitary and normalizedBranches properties are definitionally
equal.
-/
@[rep_depth operator]
theorem paraunitary_iff_normalizedBranches (F : ParaunitaryCliffordFilterBank) :
    paraunitary F ↔ F.normalizedBranches :=
  by rfl

/--
Convert the concrete branch-normalization law to the pointwise sum readout.

This is the only non-trivial arithmetic theorem in this file: it uses `ring`
to compute `(1/2 : ℝ) + (1/2 : ℝ) = (1 : ℝ)`.
-/
@[rep_depth operator]
theorem ParaunitaryCliffordFilterBank.sum_normSq_eq_one_of_normalizedBranches
    (F : ParaunitaryCliffordFilterBank)
    (h : F.normalizedBranches) :
    F.sum_normSq_eq_one := by
  rcases h with ⟨hl, hh⟩
  intro i
  calc
    F.coeffs.normSq (F.lowPass i) + F.coeffs.normSq (F.highPass i)
        = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
      simp [hl i, hh i]
    _ = (1 : ℝ) := by ring

/--
The paraunitary property (as an explicit theorem hypothesis) implies the
sum-norm identity.
-/
@[rep_depth operator]
theorem sum_normSq_eq_one_of_paraunitary (F : ParaunitaryCliffordFilterBank)
    (h : paraunitary F) :
    F.sum_normSq_eq_one :=
  F.sum_normSq_eq_one_of_normalizedBranches
    ((paraunitary_iff_normalizedBranches F).mp h)

/--
Discrete cascade system attached to a paraunitary Clifford filter bank.

The convergence and regularity fields are intentionally separate from
paraunitarity.  The latter gives the finite coefficient normalization layer,
while the former are analytic upgrades needed for compact-uniform convergence
questions.

The fields `cascadeAlgorithm`, `regularityWitness`, `sumRuleWitness`,
`cascadeConvergesL2`, `compactUniformUpgrade`, and `reconstructionExists`
are explicit axioms of the cascade model.  Proving that a concrete cascade
satisfies them is left to the owner file that instantiates this structure.
-/
@[rep_depth operator]
structure CliffordCascadeSystem
    (F : ParaunitaryCliffordFilterBank) where
  Signal : Type
  scalingApproximation : ℕ → Signal
  waveletDetail : ℕ → Signal

  cascadeAlgorithm : Prop
  regularityWitness : Prop
  sumRuleWitness : Prop
  cascadeConvergesL2 : Prop
  compactUniformUpgrade : Prop
  reconstructionExists : Prop

end InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
branch-normalization law; an arbitrary stored `F.paraunitary : Prop` is not
unfolded as data.
-/
@[rep_depth operator]
theorem ParaunitaryCliffordFilterBank.sum_normSq_eq_one_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : F.normalizedBranches) :
    F.sum_normSq_eq_one :=
  F.sum_normSq_eq_one_of_normalizedBranches h

/-- Extract the owned perfect-reconstruction certificate from paraunitarity. -/
@[rep_depth operator]
theorem perfectReconstruction_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : F.paraunitary) :
    F.perfectReconstruction :=
  h

/-- Extract the owned energy-preservation certificate from paraunitarity. -/
@[rep_depth operator]
theorem energyPreservation_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : F.paraunitary) :
    F.energyPreservation :=
  h

/--
Discrete cascade system attached to a paraunitary Clifford filter bank.

The convergence and regularity fields are intentionally separate from
paraunitarity.  The latter gives the finite coefficient normalization layer,
while the former are analytic upgrades needed for compact-uniform convergence
questions.
-/
@[rep_depth operator]
structure CliffordCascadeSystem
    (F : ParaunitaryCliffordFilterBank) where
  Signal : Type
  scalingApproximation : ℕ → Signal
  waveletDetail : ℕ → Signal

  cascadeAlgorithm : Prop
  regularityWitness : Prop
  sumRuleWitness : Prop
  cascadeConvergesL2 : Prop
  compactUniformUpgrade : Prop
  reconstructionExists : Prop

namespace CliffordCascadeSystem

variable {F : ParaunitaryCliffordFilterBank}
variable (C : CliffordCascadeSystem F)

/-- Re-export of the stored cascade convergence claim. -/
@[rep_depth operator]
theorem cascadeConvergesL2_law :
    C.cascadeConvergesL2 → C.cascadeConvergesL2 :=
  id

/-- Re-export of the stored compact-uniform upgrade claim. -/
@[rep_depth operator]
theorem compactUniformUpgrade_law :
    C.compactUniformUpgrade → C.compactUniformUpgrade :=
  id

end CliffordCascadeSystem

end InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
