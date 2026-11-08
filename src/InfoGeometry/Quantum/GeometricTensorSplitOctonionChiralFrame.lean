import InfoGeometry.Quantum.GeometricTensorFrameTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
import InfoGeometry.Algebra.Zorn.SplitCayleyStabilizer
import InfoGeometry.Canonical.SplitOctonionGogberashviliCarrierBridge
import InfoGeometry.Lie.SplitOctonionAxialCartanFlow

/-!
# QGT readout for split-octonion chiral coordinates

The split-octonion carrier and its Cartan automorphism flow are owned by the
Lie/Zorn modules.  This file only transports their eight-coordinate readout
to the existing Bogoliubov/QGT metric API.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Quantum.GeometricQuantumTensor

open InfoGeometry.Algebra.Zorn.SplitCayleyStabilizer
open Algebra.Zorn.ConcreteComposition
open InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Lie.SplitOctonionAxialCartanFlow
open InfoGeometry.Canonical.SplitOctonionGogberashviliCarrierBridge

abbrev SplitOctonionCarrier := Algebra.Zorn.ConcreteComposition.ZornCell ℝ
abbrev ChiralCoordinates := EuclideanSpace ℝ (Fin 8)
abbrev ChiralDoubled := DoubledSpace ChiralCoordinates

def chiralBasis : Fin 8 → SplitOctonionCarrier :=
  ![oneZ, J 0, J 1, J 2, j 0, j 1, j 2, I]

noncomputable def chiralCoordinates (x : SplitOctonionCarrier) : ChiralCoordinates :=
  (EuclideanSpace.equiv (Fin 8) ℝ).symm (ZornCell.coordEquiv x)

noncomputable def chiralBasisCoordinates : Fin 8 → ChiralCoordinates :=
  fun i => chiralCoordinates (chiralBasis i)

noncomputable def cellAxialCartanFlow
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    SplitOctonionCarrier ≃ₗ[ℝ] SplitOctonionCarrier :=
  cellToCanonical.trans ((axialCartanFlow k t).trans cellToCanonical.symm)

theorem cellAxialCartanFlow_map_mul
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (X Y : SplitOctonionCarrier) :
    cellAxialCartanFlow k hk t (X * Y) =
      cellAxialCartanFlow k hk t X * cellAxialCartanFlow k hk t Y := by
  apply cellToCanonical.injective
  simpa [cellAxialCartanFlow, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, cellToCanonical_mul] using
    axialCartanFlow_map_mul k hk t
      (cellToCanonical X) (cellToCanonical Y)

@[simp] theorem cellAxialCartanFlow_zero
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) :
    cellAxialCartanFlow k hk 0 = LinearEquiv.refl ℝ SplitOctonionCarrier := by
  apply LinearEquiv.ext
  intro X
  apply cellToCanonical.injective
  simp [cellAxialCartanFlow, axialCartanFlow_zero]

theorem cellAxialCartanFlow_add
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (s t : ℝ) :
    cellAxialCartanFlow k hk (s + t) =
      (cellAxialCartanFlow k hk t).trans (cellAxialCartanFlow k hk s) := by
  apply LinearEquiv.ext
  intro X
  apply cellToCanonical.injective
  simpa [cellAxialCartanFlow, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply] using
    axialCartanFlow_add k s t (cellToCanonical X)

def chiralDoubled (x : ChiralCoordinates) : ChiralDoubled :=
  to_doubled x 0

noncomputable def chiralCarrierDoubled (x : SplitOctonionCarrier) : ChiralDoubled :=
  chiralDoubled (chiralCoordinates x)

theorem chiralDoubled_apply
    (V : BogoliubovVielbeinBundle (E := ChiralCoordinates))
    (G₀ : ChiralDoubled →L[ℝ] ChiralDoubled) (t : ℝ)
    (x y : ChiralCoordinates) :
    metricOfOperator (E := ChiralCoordinates)
        (transportedKreinMetric V G₀ t)
        (chiralDoubled x) (chiralDoubled y) =
      ⟪G₀ (V.localFrame t (chiralDoubled x)),
        V.localFrame t (chiralDoubled y)⟫_ℝ := by
  exact metricOfOperator_transportedKreinMetric_apply V G₀ t
    (chiralDoubled x) (chiralDoubled y)

theorem chiralDoubled_swap
    (V : BogoliubovVielbeinBundle (E := ChiralCoordinates))
    (G₀ : ChiralDoubled →L[ℝ] ChiralDoubled) (t : ℝ)
    (hG : ContinuousLinearMap.adjoint G₀ = G₀)
    (x y : ChiralCoordinates) :
    metricOfOperator (E := ChiralCoordinates)
        (transportedKreinMetric V G₀ t)
        (chiralDoubled x) (chiralDoubled y) =
      metricOfOperator (E := ChiralCoordinates)
        (transportedKreinMetric V G₀ t)
        (chiralDoubled y) (chiralDoubled x) := by
  exact metricOfOperator_transportedKreinMetric_swap V G₀ t hG
    (chiralDoubled x) (chiralDoubled y)

end InfoGeometry.Quantum.GeometricQuantumTensor
