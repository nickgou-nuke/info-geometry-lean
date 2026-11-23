/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionEllCircularKreinOperatorBridge
import InfoGeometry.Canonical.RealDoubledChiralKreinFrame
import InfoGeometry.Geometry.AssociativeBianchi
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Gram compatibility of the Ell circular Krein basis and the doubled frame

## i. Overview

The Ell circular coordinate owner constructs an eight-vector basis and its
signed Krein Gram matrix.  This file compares that matrix with the actual
`4 + 4` doubled carrier frame, defines operator Hilbert-Schmidt inner products
on both carriers, and establishes Krein-skew Lie bracket closure alongside
compatibility with `AssociativeGaugeConnection.cyclicBianchi`.  The comparison
is bilinear/Krein and operator-algebraic data only: it does not identify
split-octonion multiplication with an associative product on the doubled
carrier.

## ii. Key results

- `ellCircularToDoubledFrame_isometry` and
  `ellCircularToDoubledFrame_hilbert_isometry`: unit-scale isometry between
  `(Coordinate, ellKreinPair, ellHilbertPair)` and
  `(KreinFrame4, splitKreinForm, chiralHilbertForm)`.
- `ellOperatorHilbertInner`, `doubledOperatorHilbertInner`, and
  `ellEndToDoubledEnd_hilbertInner`: positive-definite operator Hilbert-Schmidt
  pairings transported at unit scale by `ellEndToDoubledEnd`.
- `isEllKreinSkew_commutator`, `isDoubledKreinSkew_commutator`,
  `doubledKrein_cyclicBianchi_and_all_curvature_skew`, and
  `doubledKrein_cyclicBianchi_and_curvature_skew`: commutator closure of
  Krein-skew endomorphisms and cyclic second Bianchi compatibility with
  Krein-skewness of all three cyclic curvatures under explicit skew-preservation
  hypotheses on the commuting Leibniz derivations.

## iii. Table of contents

1. Doubled frame basis, split bilinear form, and coordinate transport
2. Krein and Hilbert-form Gram compatibility and operator intertwining
3. Operator Hilbert-Schmidt inner products and positivity transport
4. Krein-skew endomorphism Lie closure and cyclic Bianchi compatibility

## iv. References

- `InfoGeometry.Lie.SplitOctonionEllCircularKreinOperatorBridge`
- `InfoGeometry.Canonical.RealDoubledChiralKreinFrame`
- `InfoGeometry.Geometry.AssociativeBianchi`
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllDoubledKreinFrameBridge

open InfoGeometry.Lie.SplitOctonionEllCircularKreinOperatorBridge
open InfoGeometry.Canonical.RealDoubledChiralKreinFrame
open InfoGeometry.Canonical.ZornPolarizationMetricBridge
open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

/-- The ordered `4 + 4` frame on the actual doubled carrier.  Each individual
sheet is null for the off-block chiral form; for the diagonal split form the
ordered vectors have positive then negative signature. -/
def doubledKreinFrameBasis (i : Fin 4 ⊕ Fin 4) : KreinFrame4 :=
  match i with
  | Sum.inl j => plusFrame j
  | Sum.inr j => minusFrame j

/-- The actual doubled carrier basis, transported from the product of the two
Euclidean coordinate bases. -/
noncomputable def doubledKreinBasis : Module.Basis (Fin 4 ⊕ Fin 4) ℝ KreinFrame4 :=
  (((EuclideanSpace.basisFun (Fin 4) ℝ).toBasis).prod
    ((EuclideanSpace.basisFun (Fin 4) ℝ).toBasis)).map
      (WithLp.linearEquiv (2 : ENNReal) ℝ (FourSpace × FourSpace)).symm

/-- The product coordinates of the actual `WithLp` doubled carrier. -/
noncomputable def doubledProductEquiv : KreinFrame4 ≃ₗ[ℝ] FourSpace × FourSpace :=
  WithLp.linearEquiv (2 : ENNReal) ℝ (FourSpace × FourSpace)

/-- The split Krein pairing, represented as a genuine Mathlib bilinear form
on the doubled carrier. -/
noncomputable def doubledSplitBilin : LinearMap.BilinForm ℝ KreinFrame4 :=
  LinearMap.BilinForm.comp (innerₗ FourSpace)
      ((LinearMap.fst ℝ FourSpace FourSpace).comp doubledProductEquiv.toLinearMap)
      ((LinearMap.fst ℝ FourSpace FourSpace).comp doubledProductEquiv.toLinearMap) -
    LinearMap.BilinForm.comp (innerₗ FourSpace)
      ((LinearMap.snd ℝ FourSpace FourSpace).comp doubledProductEquiv.toLinearMap)
      ((LinearMap.snd ℝ FourSpace FourSpace).comp doubledProductEquiv.toLinearMap)

/-- Applying `doubledSplitBilin` recovers `splitKreinForm`. -/
@[simp] lemma doubledSplitBilin_apply (x y : KreinFrame4) :
    doubledSplitBilin x y = splitKreinForm (E := FourSpace) x y := by
  rfl

/-- Evaluating `doubledKreinBasis` gives `doubledKreinFrameBasis`. -/
@[simp] lemma doubledKreinBasis_apply (i : Fin 4 ⊕ Fin 4) :
    doubledKreinBasis i = doubledKreinFrameBasis i := by
  cases i with
  | inl i =>
      simp [doubledKreinBasis, doubledKreinFrameBasis, plusFrame, frameBasis]
  | inr i =>
      simp [doubledKreinBasis, doubledKreinFrameBasis, minusFrame, frameBasis]

/-- The basis correspondence induces a genuine linear equivalence from Ell
circular coordinates to the doubled chiral carrier. -/
noncomputable def ellCircularToDoubledFrame :
    Coordinate ≃ₗ[ℝ] KreinFrame4 :=
  ellKreinEigenbasis.equiv doubledKreinBasis (Equiv.refl (Fin 4 ⊕ Fin 4))

/-- The Ell raw Krein form as a Mathlib bilinear form, pulled back from the
native Zorn polar form through the owner's coordinate equivalence. -/
noncomputable def ellCircularKreinBilin : LinearMap.BilinForm ℝ Coordinate :=
  LinearMap.BilinForm.comp polarForm ellToKrein.toLinearMap ellToKrein.toLinearMap

/-- `ellCircularToDoubledFrame` sends `ellKreinEigenbasis` to `doubledKreinFrameBasis`. -/
@[simp] lemma ellCircularToDoubledFrame_basis (i : Fin 4 ⊕ Fin 4) :
    ellCircularToDoubledFrame (ellKreinEigenbasis i) =
      doubledKreinFrameBasis i := by
  simp [ellCircularToDoubledFrame]

/-- `ellCircularToDoubledFrame` sends positive Ell eigenvectors to `plusFrame`. -/
@[simp] lemma ellCircularToDoubledFrame_positiveVector (i : Fin 4) :
    ellCircularToDoubledFrame (ellKreinPositiveVector i) = plusFrame i := by
  rw [← ellKreinEigenbasis_positive_apply, ellCircularToDoubledFrame_basis]
  rfl

/-- `ellCircularToDoubledFrame` sends negative Ell eigenvectors to `minusFrame`. -/
@[simp] lemma ellCircularToDoubledFrame_negativeVector (i : Fin 4) :
    ellCircularToDoubledFrame (ellKreinNegativeVector i) = minusFrame i := by
  rw [← ellKreinEigenbasis_negative_apply, ellCircularToDoubledFrame_basis]
  rfl

/-- The original positive-half Ell coordinate vector lands on the half-sum
of its positive and negative doubled-frame vectors. -/
lemma ellCircularToDoubledFrame_pair_coordinate (i : Fin 4) :
    ellCircularToDoubledFrame (Pi.single (ellKreinPairIndex i) (1 : ℝ)) =
      (1 / 2 : ℝ) • (plusFrame i + minusFrame i) := by
  have hcoord : Pi.single (ellKreinPairIndex i) (1 : ℝ) =
      (1 / 2 : ℝ) • (ellKreinPositiveVector i + ellKreinNegativeVector i) := by
    ext k
    fin_cases i <;> fin_cases k <;>
      simp [ellKreinPairIndex, ellKreinOppositeIndex, ellKreinPairSign,
        ellKreinPositiveVector, ellKreinNegativeVector] <;> ring
  rw [hcoord]
  simp only [map_smul, map_add, ellCircularToDoubledFrame_positiveVector,
    ellCircularToDoubledFrame_negativeVector]

/-- The original negative-half Ell coordinate vector lands on the signed
half-difference.  The sign is inherited from the actual Ell root convention:
it is positive for the pole pair and negative on the three circular root
pairs. -/
lemma ellCircularToDoubledFrame_opposite_coordinate (i : Fin 4) :
    ellCircularToDoubledFrame (Pi.single (ellKreinOppositeIndex i) (1 : ℝ)) =
      (ellKreinPairSign i / 2) • (plusFrame i - minusFrame i) := by
  have hcoord : Pi.single (ellKreinOppositeIndex i) (1 : ℝ) =
      ellKreinPairSign i •
        ((1 / 2 : ℝ) • (ellKreinPositiveVector i - ellKreinNegativeVector i)) := by
    ext k
    fin_cases i <;> fin_cases k <;>
      simp [ellKreinPairIndex, ellKreinOppositeIndex, ellKreinPairSign,
        ellKreinPositiveVector, ellKreinNegativeVector] <;> ring
  rw [hcoord]
  simp only [map_smul, map_sub, ellCircularToDoubledFrame_positiveVector,
    ellCircularToDoubledFrame_negativeVector, smul_smul]
  ring_nf

/-- The Ell fundamental symmetry is carried to the doubled chiral grading.
This states the operator compatibility on the entire carrier, not only on
the displayed basis vectors. -/
lemma ellCircularToDoubledFrame_fundamental_intertwining :
    ellCircularToDoubledFrame.toLinearMap.comp ellFundamental =
      gamma5.toLinearMap.comp ellCircularToDoubledFrame.toLinearMap := by
  apply ellKreinEigenbasis.ext
  intro i
  cases i with
  | inl i =>
      simp only [LinearMap.comp_apply, ellKreinEigenbasis_positive_apply]
      change ellCircularToDoubledFrame
          (ellFundamental (ellKreinPositiveVector i)) =
        gamma5 (ellCircularToDoubledFrame (ellKreinPositiveVector i))
      rw [ellFundamental_positive_eigenvector,
        ellCircularToDoubledFrame_positiveVector, gamma5_plusFrame]
  | inr i =>
      simp only [LinearMap.comp_apply, ellKreinEigenbasis_negative_apply]
      change ellCircularToDoubledFrame
          (ellFundamental (ellKreinNegativeVector i)) =
        gamma5 (ellCircularToDoubledFrame (ellKreinNegativeVector i))
      rw [ellFundamental_negative_eigenvector]
      simp only [map_neg, ellCircularToDoubledFrame_negativeVector,
        gamma5_minusFrame]

/-- The actual Ell regular `J` operator is carried to the doubled sheet flip.
The result preserves the regular-operator action on the full carrier. -/
lemma ellCircularToDoubledFrame_regularJ_intertwining :
    ellCircularToDoubledFrame.toLinearMap.comp ellRegularJ =
      sheetFlip.toLinearMap.comp ellCircularToDoubledFrame.toLinearMap := by
  apply ellKreinEigenbasis.ext
  intro i
  cases i with
  | inl i =>
      simp only [LinearMap.comp_apply, ellKreinEigenbasis_positive_apply]
      change ellCircularToDoubledFrame
          (ellRegularJ (ellKreinPositiveVector i)) =
        sheetFlip (ellCircularToDoubledFrame (ellKreinPositiveVector i))
      rw [ellRegularJ_positiveVector,
        ellCircularToDoubledFrame_negativeVector,
        ellCircularToDoubledFrame_positiveVector, sheetFlip_plusFrame]
  | inr i =>
      simp only [LinearMap.comp_apply, ellKreinEigenbasis_negative_apply]
      change ellCircularToDoubledFrame
          (ellRegularJ (ellKreinNegativeVector i)) =
        sheetFlip (ellCircularToDoubledFrame (ellKreinNegativeVector i))
      rw [ellRegularJ_negativeVector,
        ellCircularToDoubledFrame_positiveVector,
        ellCircularToDoubledFrame_negativeVector, sheetFlip_minusFrame]

/-- The doubled frame has the standard signature `(+, +, +, +, -, -, -, -)`
for the diagonal split Krein form. -/
lemma doubledKreinFrameBasis_gram (i j : Fin 4 ⊕ Fin 4) :
    splitKreinForm (E := FourSpace) (doubledKreinFrameBasis i)
      (doubledKreinFrameBasis j) =
        if i = j then (match j with
          | Sum.inl _ => (1 : ℝ)
          | Sum.inr _ => -1) else 0 := by
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp [doubledKreinFrameBasis, splitKreinForm_to_doubled,
            plusFrame, frameBasis_inner]
      | inr j =>
          simp [doubledKreinFrameBasis, splitKreinForm_to_doubled,
            plusFrame, minusFrame]
  | inr i =>
      cases j with
      | inl j =>
          simp [doubledKreinFrameBasis, splitKreinForm_to_doubled,
            plusFrame, minusFrame]
      | inr j =>
          simp [doubledKreinFrameBasis, splitKreinForm_to_doubled,
            minusFrame, frameBasis_inner]
          by_cases hij : i = j <;> simp [hij]

/-- Exact basis-level soldering: the circular split-octonion Krein basis and
the doubled chiral frame have identical Gram matrices.  This is the precise
bilinear compatibility needed to define an isometry by sending corresponding
basis vectors to one another. -/
lemma ellKreinEigenbasis_matches_doubledFrame_gram
    (i j : Fin 4 ⊕ Fin 4) :
    ellKreinPair (ellKreinEigenbasis i) (ellKreinEigenbasis j) =
      splitKreinForm (E := FourSpace) (doubledKreinFrameBasis i)
        (doubledKreinFrameBasis j) := by
  rw [ellKreinPair_eigenbasis_gram, doubledKreinFrameBasis_gram]
  cases j <;> simp [ellFundamentalEigenvalue]

/-- The basis-level Gram calculation extends to the whole carrier: the
linear equivalence is an isometry for the actual raw Krein bilinear forms.
In particular, this is unit-scale and uses the repository's signed Ell
eigenbasis without inserting an additional polarization transform. -/
lemma ellCircularToDoubledFrame_isometry :
    ∀ x y : Coordinate,
      splitKreinForm (E := FourSpace)
          (ellCircularToDoubledFrame x) (ellCircularToDoubledFrame y) =
        ellKreinPair x y := by
  have hForms :
      LinearMap.BilinForm.comp doubledSplitBilin
          ellCircularToDoubledFrame.toLinearMap
          ellCircularToDoubledFrame.toLinearMap =
        LinearMap.BilinForm.comp polarForm
          ellToKrein.toLinearMap ellToKrein.toLinearMap := by
    apply LinearMap.BilinForm.ext_basis
    intro i j
    change splitKreinForm (ellCircularToDoubledFrame (ellKreinEigenbasis i))
        (ellCircularToDoubledFrame (ellKreinEigenbasis j)) =
      ellKreinPair (ellKreinEigenbasis i) (ellKreinEigenbasis j)
    rw [ellCircularToDoubledFrame_basis, ellCircularToDoubledFrame_basis,
      ← ellKreinEigenbasis_matches_doubledFrame_gram]
  intro x y
  have h := congrArg (fun B : LinearMap.BilinForm ℝ Coordinate => B x y) hForms
  simpa [doubledSplitBilin_apply, ellKreinPair] using h

/-- The carrier map packaged as a genuine bilinear isometry equivalence.
This is the reusable bridge object for transporting constructions that depend
on the signed Krein pairing. -/
noncomputable def ellCircularToDoubledKreinIsometry :
    ellCircularKreinBilin.IsometryEquiv doubledSplitBilin :=
  { ellCircularToDoubledFrame with
    map_app' := by
      intro x y
      change splitKreinForm (E := FourSpace)
          (ellCircularToDoubledFrame x) (ellCircularToDoubledFrame y) =
        ellKreinPair x y
      exact ellCircularToDoubledFrame_isometry x y }

/-- On the doubled frame, inserting the chiral grading into the split form
gives the positive Hilbert form. -/
lemma splitKreinForm_gamma5_eq_chiralHilbertForm (x y : KreinFrame4) :
    splitKreinForm (E := FourSpace) x (gamma5 y) =
      chiralHilbertForm (E := FourSpace) x y := by
  rw [chiralHilbertForm_eq_inner]
  simp [splitKreinForm, gamma5, spectral_epsilon,
    WithLp.prod_inner_apply]

/-- The basis-to-frame map also preserves the positive Hilbert pairing at
unit scale.  This follows from the already-proved full Krein isometry and
the operator intertwining, rather than a second coordinate normalization. -/
lemma ellCircularToDoubledFrame_hilbert_isometry (x y : Coordinate) :
    chiralHilbertForm (E := FourSpace)
        (ellCircularToDoubledFrame x) (ellCircularToDoubledFrame y) =
      ellHilbertPair x y := by
  have hIntertwine :
      ellCircularToDoubledFrame (ellFundamental y) =
        gamma5 (ellCircularToDoubledFrame y) := by
    have h := congrArg
      (fun f : Coordinate →ₗ[ℝ] KreinFrame4 => f y)
      ellCircularToDoubledFrame_fundamental_intertwining
    simpa [LinearMap.comp_apply] using h
  calc
    chiralHilbertForm (E := FourSpace)
        (ellCircularToDoubledFrame x) (ellCircularToDoubledFrame y)
      = splitKreinForm (E := FourSpace) (ellCircularToDoubledFrame x)
          (gamma5 (ellCircularToDoubledFrame y)) :=
            (splitKreinForm_gamma5_eq_chiralHilbertForm _ _).symm
    _ = ellKreinPair x (ellFundamental y) := by
          rw [← hIntertwine]
          exact ellCircularToDoubledFrame_isometry x (ellFundamental y)
    _ = ellHilbertPair x y := rfl

/-! ## Transport of the actual Krein-skew operator algebras -/

/-- Conjugation by the already-proved carrier equivalence transports all linear
endomorphisms of Ell coordinates to endomorphisms of the doubled frame. -/
noncomputable def ellEndToDoubledEnd :
    Module.End ℝ Coordinate ≃ₐ[ℝ] Module.End ℝ KreinFrame4 :=
  ellCircularToDoubledFrame.conjAlgEquiv ℝ

/-- Conjugated endomorphisms act via `ellCircularToDoubledFrame`. -/
@[simp] lemma ellEndToDoubledEnd_apply
    (T : Module.End ℝ Coordinate) (x : Coordinate) :
    ellEndToDoubledEnd T (ellCircularToDoubledFrame x) =
      ellCircularToDoubledFrame (T x) := by
  rw [ellEndToDoubledEnd, LinearEquiv.conjAlgEquiv_apply]
  simp [LinearMap.comp_apply]

/-- Krein-skew-adjointness on the Ell carrier, stated using its actual
owner-defined bilinear form. -/
def IsEllKreinSkew (T : Module.End ℝ Coordinate) : Prop :=
  ∀ x y, ellKreinPair (T x) y + ellKreinPair x (T y) = 0

/-- Krein-skew-adjointness on the doubled carrier, stated using the actual
split form of `RealDoubledChiralKreinFrame`. -/
def IsDoubledKreinSkew (S : Module.End ℝ KreinFrame4) : Prop :=
  ∀ x y, splitKreinForm (E := FourSpace) (S x) y +
    splitKreinForm (E := FourSpace) x (S y) = 0

/-- The basis isometry transports the Krein-skew endomorphism condition in
both directions.  Together with `ellEndToDoubledEnd` being an algebra
equivalence, this gives the operator-level carrier bridge: it
transports the genuine bilinear skew condition, rather than merely matching
matrix dimensions or basis labels. -/
lemma ellEndToDoubledEnd_kreinSkew_iff (T : Module.End ℝ Coordinate) :
    IsDoubledKreinSkew (ellEndToDoubledEnd T) ↔ IsEllKreinSkew T := by
  constructor
  · intro h x y
    have hxy := h (ellCircularToDoubledFrame x) (ellCircularToDoubledFrame y)
    simpa only [ellEndToDoubledEnd_apply, ellCircularToDoubledFrame_isometry] using hxy
  · intro h u v
    let x := ellCircularToDoubledFrame.symm u
    let y := ellCircularToDoubledFrame.symm v
    have hxy := h x y
    have hu : ellCircularToDoubledFrame x = u := by
      dsimp [x]
      exact ellCircularToDoubledFrame.apply_symm_apply u
    have hv : ellCircularToDoubledFrame y = v := by
      dsimp [y]
      exact ellCircularToDoubledFrame.apply_symm_apply v
    calc
      splitKreinForm (E := FourSpace) (ellEndToDoubledEnd T u) v +
          splitKreinForm (E := FourSpace) u (ellEndToDoubledEnd T v) =
        splitKreinForm (E := FourSpace)
            (ellCircularToDoubledFrame (T x)) (ellCircularToDoubledFrame y) +
          splitKreinForm (E := FourSpace)
            (ellCircularToDoubledFrame x) (ellCircularToDoubledFrame (T y)) := by
              rw [← hu, ← hv]
              simp only [ellEndToDoubledEnd_apply]
      _ = ellKreinPair (T x) y + ellKreinPair x (T y) := by
            rw [ellCircularToDoubledFrame_isometry, ellCircularToDoubledFrame_isometry]
      _ = 0 := hxy

/-! ## Operator Hilbert-Schmidt pairings and positivity transport -/

/-- Operator Hilbert-Schmidt inner product on `Module.End ℝ Coordinate`,
computed in the orthonormal signed Krein eigenbasis `ellKreinEigenbasis`. -/
noncomputable def ellOperatorHilbertInner (S T : Module.End ℝ Coordinate) : ℝ :=
  ∑ i : Fin 4 ⊕ Fin 4,
    ellHilbertPair (S (ellKreinEigenbasis i)) (T (ellKreinEigenbasis i))

/-- Operator Hilbert-Schmidt inner product on `Module.End ℝ KreinFrame4`,
computed in the orthonormal doubled frame `doubledKreinBasis`. -/
noncomputable def doubledOperatorHilbertInner (A B : Module.End ℝ KreinFrame4) : ℝ :=
  ∑ i : Fin 4 ⊕ Fin 4,
    chiralHilbertForm (E := FourSpace) (A (doubledKreinBasis i)) (B (doubledKreinBasis i))

/-- Nonnegativity of the Ell operator Hilbert-Schmidt quadratic form. -/
lemma ellOperatorHilbertInner_self_nonneg (T : Module.End ℝ Coordinate) :
    0 ≤ ellOperatorHilbertInner T T :=
  Finset.sum_nonneg fun i _ => ellHilbertPair_nonneg (T (ellKreinEigenbasis i))

/-- Positive definiteness of the Ell operator Hilbert-Schmidt inner product. -/
lemma ellOperatorHilbertInner_self_eq_zero_iff (T : Module.End ℝ Coordinate) :
    ellOperatorHilbertInner T T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hnonneg :
        ∀ i ∈ (Finset.univ : Finset (Fin 4 ⊕ Fin 4)),
          0 ≤ ellHilbertPair (T (ellKreinEigenbasis i)) (T (ellKreinEigenbasis i)) :=
      fun i _ => ellHilbertPair_nonneg _
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h
    apply ellKreinEigenbasis.ext
    intro i
    exact (ellHilbertPair_zero_iff _).mp (hall i (Finset.mem_univ i))
  · intro hT
    subst T
    simp [ellOperatorHilbertInner, (ellHilbertPair_zero_iff 0).mpr rfl]

/-- `ellEndToDoubledEnd` is a unit-scale isometry for the operator Hilbert-Schmidt pairings. -/
lemma ellEndToDoubledEnd_hilbertInner (S T : Module.End ℝ Coordinate) :
    doubledOperatorHilbertInner (ellEndToDoubledEnd S) (ellEndToDoubledEnd T) =
      ellOperatorHilbertInner S T := by
  unfold doubledOperatorHilbertInner ellOperatorHilbertInner
  refine Finset.sum_congr rfl fun i _ => ?_
  have hbasis : doubledKreinBasis i = ellCircularToDoubledFrame (ellKreinEigenbasis i) := by
    rw [doubledKreinBasis_apply, ellCircularToDoubledFrame_basis]
  rw [hbasis, ellEndToDoubledEnd_apply, ellEndToDoubledEnd_apply]
  exact ellCircularToDoubledFrame_hilbert_isometry _ _

/-! ## Krein-skew Lie closure and associative cyclic Bianchi compatibility -/

/-- Krein-skew endomorphisms of `Coordinate` are closed under the associative commutator. -/
lemma isEllKreinSkew_commutator {S T : Module.End ℝ Coordinate}
    (hS : IsEllKreinSkew S) (hT : IsEllKreinSkew T) :
    IsEllKreinSkew (S * T - T * S) := by
  intro x y
  have hS' : ∀ u v, ellKreinPair (S u) v = -ellKreinPair u (S v) :=
    fun u v => eq_neg_of_add_eq_zero_left (hS u v)
  have hT' : ∀ u v, ellKreinPair (T u) v = -ellKreinPair u (T v) :=
    fun u v => eq_neg_of_add_eq_zero_left (hT u v)
  change ellCircularKreinBilin (S (T x) - T (S x)) y +
      ellCircularKreinBilin x (S (T y) - T (S y)) = 0
  rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right]
  change (ellKreinPair (S (T x)) y - ellKreinPair (T (S x)) y) +
      (ellKreinPair x (S (T y)) - ellKreinPair x (T (S y))) = 0
  rw [hS', hT', hT', hS']
  simp only [neg_neg]
  abel

/-- Krein-skew endomorphisms of `KreinFrame4` are closed under addition. -/
lemma isDoubledKreinSkew_add {A B : Module.End ℝ KreinFrame4}
    (hA : IsDoubledKreinSkew A) (hB : IsDoubledKreinSkew B) :
    IsDoubledKreinSkew (A + B) := by
  intro x y
  change doubledSplitBilin (A x + B x) y + doubledSplitBilin x (A y + B y) = 0
  rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right]
  have hAx : doubledSplitBilin (A x) y + doubledSplitBilin x (A y) = 0 := hA x y
  have hBx : doubledSplitBilin (B x) y + doubledSplitBilin x (B y) = 0 := hB x y
  rw [add_add_add_comm, hAx, hBx, add_zero]

/-- Krein-skew endomorphisms of `KreinFrame4` are closed under subtraction. -/
lemma isDoubledKreinSkew_sub {A B : Module.End ℝ KreinFrame4}
    (hA : IsDoubledKreinSkew A) (hB : IsDoubledKreinSkew B) :
    IsDoubledKreinSkew (A - B) := by
  intro x y
  change doubledSplitBilin (A x - B x) y + doubledSplitBilin x (A y - B y) = 0
  rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right]
  have hAx : doubledSplitBilin (A x) y + doubledSplitBilin x (A y) = 0 := hA x y
  have hBx : doubledSplitBilin (B x) y + doubledSplitBilin x (B y) = 0 := hB x y
  rw [sub_add_sub_comm, hAx, hBx, sub_zero]

/-- Krein-skew endomorphisms of `KreinFrame4` are closed under the associative commutator. -/
lemma isDoubledKreinSkew_commutator {A B : Module.End ℝ KreinFrame4}
    (hA : IsDoubledKreinSkew A) (hB : IsDoubledKreinSkew B) :
    IsDoubledKreinSkew (A * B - B * A) := by
  intro x y
  have hA' : ∀ u v, doubledSplitBilin (A u) v = -doubledSplitBilin u (A v) :=
    fun u v => eq_neg_of_add_eq_zero_left (hA u v)
  have hB' : ∀ u v, doubledSplitBilin (B u) v = -doubledSplitBilin u (B v) :=
    fun u v => eq_neg_of_add_eq_zero_left (hB u v)
  change doubledSplitBilin (A (B x) - B (A x)) y +
      doubledSplitBilin x (A (B y) - B (A y)) = 0
  rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hA', hB', hB', hA']
  simp only [neg_neg]
  abel

/-- Curvature of Krein-skew potentials under skew-preserving derivations is Krein-skew. -/
lemma isDoubledKreinSkew_curvature
    (D E : Module.End ℝ (Module.End ℝ KreinFrame4))
    (hD_skew : ∀ X, IsDoubledKreinSkew X → IsDoubledKreinSkew (D X))
    (hE_skew : ∀ X, IsDoubledKreinSkew X → IsDoubledKreinSkew (E X))
    {A B : Module.End ℝ KreinFrame4}
    (hA : IsDoubledKreinSkew A) (hB : IsDoubledKreinSkew B) :
    IsDoubledKreinSkew
      (InfoGeometry.Geometry.AssociativeGaugeConnection.curvature D E A B) := by
  have hDeriv : IsDoubledKreinSkew (D B - E A) :=
    isDoubledKreinSkew_sub (hD_skew B hB) (hE_skew A hA)
  have hComm : IsDoubledKreinSkew (A * B - B * A) :=
    isDoubledKreinSkew_commutator hA hB
  have hEq :
      InfoGeometry.Geometry.AssociativeGaugeConnection.curvature D E A B =
        (D B - E A) + (A * B - B * A) := by
    unfold InfoGeometry.Geometry.AssociativeGaugeConnection.curvature
    abel
  rw [hEq]
  exact isDoubledKreinSkew_add hDeriv hComm

/-- Associative gauge connections on `Module.End ℝ KreinFrame4` satisfy the cyclic
second Bianchi identity, and when the commuting Leibniz derivatives preserve
`IsDoubledKreinSkew`, all three cyclic curvatures of Krein-skew potentials
remain Krein-skew. -/
lemma doubledKrein_cyclicBianchi_and_all_curvature_skew
    (D E G : Module.End ℝ (Module.End ℝ KreinFrame4))
    (hD : InfoGeometry.Geometry.AssociativeGaugeConnection.IsLeibniz D)
    (hE : InfoGeometry.Geometry.AssociativeGaugeConnection.IsLeibniz E)
    (hG : InfoGeometry.Geometry.AssociativeGaugeConnection.IsLeibniz G)
    (hD_skew : ∀ X, IsDoubledKreinSkew X → IsDoubledKreinSkew (D X))
    (hE_skew : ∀ X, IsDoubledKreinSkew X → IsDoubledKreinSkew (E X))
    (hG_skew : ∀ X, IsDoubledKreinSkew X → IsDoubledKreinSkew (G X))
    (hDE : ∀ x, D (E x) = E (D x))
    (hEG : ∀ x, E (G x) = G (E x))
    (hGD : ∀ x, G (D x) = D (G x))
    (A B C : Module.End ℝ KreinFrame4)
    (hA : IsDoubledKreinSkew A) (hB : IsDoubledKreinSkew B)
    (hC : IsDoubledKreinSkew C) :
    InfoGeometry.Geometry.AssociativeGaugeConnection.adjointCovariantDerivative D A
        (InfoGeometry.Geometry.AssociativeGaugeConnection.curvature E G B C) +
      InfoGeometry.Geometry.AssociativeGaugeConnection.adjointCovariantDerivative E B
        (InfoGeometry.Geometry.AssociativeGaugeConnection.curvature G D C A) +
      InfoGeometry.Geometry.AssociativeGaugeConnection.adjointCovariantDerivative G C
        (InfoGeometry.Geometry.AssociativeGaugeConnection.curvature D E A B) = 0 ∧
    IsDoubledKreinSkew
      (InfoGeometry.Geometry.AssociativeGaugeConnection.curvature D E A B) ∧
    IsDoubledKreinSkew
      (InfoGeometry.Geometry.AssociativeGaugeConnection.curvature E G B C) ∧
    IsDoubledKreinSkew
      (InfoGeometry.Geometry.AssociativeGaugeConnection.curvature G D C A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact InfoGeometry.Geometry.AssociativeGaugeConnection.cyclicBianchi
      D E G hD hE hG hDE hEG hGD A B C
  · exact isDoubledKreinSkew_curvature D E hD_skew hE_skew hA hB
  · exact isDoubledKreinSkew_curvature E G hE_skew hG_skew hB hC
  · exact isDoubledKreinSkew_curvature G D hG_skew hD_skew hC hA

/-- Associative gauge connections on `Module.End ℝ KreinFrame4` satisfy the cyclic
second Bianchi identity, and when the commuting Leibniz derivatives preserve
`IsDoubledKreinSkew`, the curvature of Krein-skew potentials remains Krein-skew. -/
lemma doubledKrein_cyclicBianchi_and_curvature_skew
    (D E G : Module.End ℝ (Module.End ℝ KreinFrame4))
    (hD : InfoGeometry.Geometry.AssociativeGaugeConnection.IsLeibniz D)
    (hE : InfoGeometry.Geometry.AssociativeGaugeConnection.IsLeibniz E)
    (hG : InfoGeometry.Geometry.AssociativeGaugeConnection.IsLeibniz G)
    (hD_skew : ∀ X, IsDoubledKreinSkew X → IsDoubledKreinSkew (D X))
    (hE_skew : ∀ X, IsDoubledKreinSkew X → IsDoubledKreinSkew (E X))
    (hG_skew : ∀ X, IsDoubledKreinSkew X → IsDoubledKreinSkew (G X))
    (hDE : ∀ x, D (E x) = E (D x))
    (hEG : ∀ x, E (G x) = G (E x))
    (hGD : ∀ x, G (D x) = D (G x))
    (A B C : Module.End ℝ KreinFrame4)
    (hA : IsDoubledKreinSkew A) (hB : IsDoubledKreinSkew B)
    (hC : IsDoubledKreinSkew C) :
    InfoGeometry.Geometry.AssociativeGaugeConnection.adjointCovariantDerivative D A
        (InfoGeometry.Geometry.AssociativeGaugeConnection.curvature E G B C) +
      InfoGeometry.Geometry.AssociativeGaugeConnection.adjointCovariantDerivative E B
        (InfoGeometry.Geometry.AssociativeGaugeConnection.curvature G D C A) +
      InfoGeometry.Geometry.AssociativeGaugeConnection.adjointCovariantDerivative G C
        (InfoGeometry.Geometry.AssociativeGaugeConnection.curvature D E A B) = 0 ∧
    IsDoubledKreinSkew
      (InfoGeometry.Geometry.AssociativeGaugeConnection.curvature D E A B) := by
  have hAll := doubledKrein_cyclicBianchi_and_all_curvature_skew
    D E G hD hE hG hD_skew hE_skew hG_skew hDE hEG hGD A B C hA hB hC
  exact ⟨hAll.1, hAll.2.1⟩

end InfoGeometry.Lie.SplitOctonionEllDoubledKreinFrameBridge
