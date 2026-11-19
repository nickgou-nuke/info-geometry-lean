/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionEllCircularKreinOperatorBridge
import InfoGeometry.Canonical.RealDoubledChiralKreinFrame
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Gram compatibility of the Ell circular Krein basis and the doubled frame

The Ell circular coordinate owner constructs an eight-vector basis and its
signed Krein Gram matrix.  This file compares that matrix with the actual
`4 + 4` doubled carrier frame.  The comparison is bilinear/Krein data only:
it does not identify split-octonion multiplication with an associative
product on the doubled carrier.
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

@[simp] theorem doubledSplitBilin_apply (x y : KreinFrame4) :
    doubledSplitBilin x y = splitKreinForm (E := FourSpace) x y := by
  rfl

@[simp] theorem doubledKreinBasis_apply (i : Fin 4 ⊕ Fin 4) :
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

@[simp] theorem ellCircularToDoubledFrame_basis (i : Fin 4 ⊕ Fin 4) :
    ellCircularToDoubledFrame (ellKreinEigenbasis i) =
      doubledKreinFrameBasis i := by
  simp [ellCircularToDoubledFrame]

@[simp] theorem ellCircularToDoubledFrame_positiveVector (i : Fin 4) :
    ellCircularToDoubledFrame (ellKreinPositiveVector i) = plusFrame i := by
  rw [← ellKreinEigenbasis_positive_apply, ellCircularToDoubledFrame_basis]
  rfl

@[simp] theorem ellCircularToDoubledFrame_negativeVector (i : Fin 4) :
    ellCircularToDoubledFrame (ellKreinNegativeVector i) = minusFrame i := by
  rw [← ellKreinEigenbasis_negative_apply, ellCircularToDoubledFrame_basis]
  rfl

/-- The original positive-half Ell coordinate vector lands on the half-sum
of its positive and negative doubled-frame vectors. -/
theorem ellCircularToDoubledFrame_pair_coordinate (i : Fin 4) :
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
theorem ellCircularToDoubledFrame_opposite_coordinate (i : Fin 4) :
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
theorem ellCircularToDoubledFrame_fundamental_intertwining :
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
theorem ellCircularToDoubledFrame_regularJ_intertwining :
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
theorem doubledKreinFrameBasis_gram (i j : Fin 4 ⊕ Fin 4) :
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
theorem ellKreinEigenbasis_matches_doubledFrame_gram
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
theorem ellCircularToDoubledFrame_isometry :
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
theorem splitKreinForm_gamma5_eq_chiralHilbertForm (x y : KreinFrame4) :
    splitKreinForm (E := FourSpace) x (gamma5 y) =
      chiralHilbertForm (E := FourSpace) x y := by
  rw [chiralHilbertForm_eq_inner]
  simp [splitKreinForm, gamma5, spectral_epsilon,
    WithLp.prod_inner_apply]

/-- The basis-to-frame map also preserves the positive Hilbert pairing at
unit scale.  This follows from the already-proved full Krein isometry and
the operator intertwining, rather than a second coordinate normalization. -/
theorem ellCircularToDoubledFrame_hilbert_isometry (x y : Coordinate) :
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

@[simp] theorem ellEndToDoubledEnd_apply
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
theorem ellEndToDoubledEnd_kreinSkew_iff (T : Module.End ℝ Coordinate) :
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

end InfoGeometry.Lie.SplitOctonionEllDoubledKreinFrameBridge
