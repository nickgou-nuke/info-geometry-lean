import Mathlib.Tactic
import InfoGeometry.Arithmetic.IdeleClassZetaSymmetry
import InfoGeometry.Arithmetic.ZetaSouriauSymmetryThermodynamics

/-!
# InfoGeometry.Arithmetic.IdeleSouriauZetaThermodynamics

Theorem-safe bridge from the existing three-layer idele-class symmetry shadow

to the existing zeta Souriau thermodynamics on centered coordinates.

This file does NOT construct the full idele class group of `ℚ`, prove the
Bost--Connes KMS classification, or prove RH. It only packages the algebra that
is already present in the codebase:

* `ThreeLayerIdeleSymmetry G` from `IdeleClassZetaSymmetry.lean`;
* `ZetaSouriauLieSymmetry` and its displacement thermodynamics from
  `ZetaSouriauSymmetryThermodynamics.lean`.

The resulting chart action keeps exactly the theorem-safe content:

* the `ℝ^*_+` layer contributes the real chart-height/log-temperature shift;
* the Fourier `ℤ₂` layer contributes the critical mirror;
* the arithmetic/Galois layer acts on the cyclotomic/Bost--Connes lane, but not
  directly on the centered chart coordinates;
* the displacement Souriau partition and Massieu potential are invariant under
  the induced chart action.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.IdeleSouriauZetaThermodynamics

open InfoGeometry.Arithmetic.IdeleClassZetaSymmetry
open InfoGeometry.Arithmetic.IdeleClassZetaSymmetry.IdeleClassLayer
open InfoGeometry.Arithmetic.IdeleClassZetaSymmetry.FourierParity
open InfoGeometry.Arithmetic.IdeleClassZetaSymmetry.ThreeLayerIdeleSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart
open InfoGeometry.Arithmetic.ZetaSouriauSymmetryThermodynamics
open InfoGeometry.Arithmetic.ZetaSouriauSymmetryThermodynamics.ZetaSouriauLieSymmetry

/-- The Fourier parity layer seen as the exact finite zeta chart frame. -/
def parityToChartSymmetry : FourierParity → ChartSymmetry
  | FourierParity.identity => ChartSymmetry.identity
  | FourierParity.dual => ChartSymmetry.criticalMirror

@[simp] theorem parityToChartSymmetry_identity :
    parityToChartSymmetry FourierParity.identity = ChartSymmetry.identity := rfl

@[simp] theorem parityToChartSymmetry_dual :
    parityToChartSymmetry FourierParity.dual = ChartSymmetry.criticalMirror := rfl

/-- The parity-to-frame map respects the `ℤ₂`/Klein composition law on this lane. -/
theorem parityToChartSymmetry_compose (p q : FourierParity) :
    parityToChartSymmetry (FourierParity.compose p q) =
      chartSymmetryCompose (parityToChartSymmetry p) (parityToChartSymmetry q) := by
  cases p <;> cases q <;> rfl

section CommGroup

variable {G : Type*} [CommGroup G]

/--
Induced Souriau chart symmetry from a three-layer idele symmetry shadow.

Only the continuous log-scale and the Fourier parity contribute to the centered
chart action; the arithmetic layer remains available separately on the
cyclotomic/Bost--Connes side.
-/
def toZetaSouriauLieSymmetry (A : ThreeLayerIdeleSymmetry G) : ZetaSouriauLieSymmetry :=
  ⟨parityToChartSymmetry A.parity, A.layer.logScale⟩

@[simp] theorem toZetaSouriauLieSymmetry_frame (A : ThreeLayerIdeleSymmetry G) :
    (toZetaSouriauLieSymmetry A).frame = parityToChartSymmetry A.parity := rfl

@[simp] theorem toZetaSouriauLieSymmetry_height (A : ThreeLayerIdeleSymmetry G) :
    (toZetaSouriauLieSymmetry A).height = A.layer.logScale := rfl

/--
The induced centered-chart action is exactly height translation composed with
Fourier critical reflection when the parity is nontrivial.
-/
theorem act_eq_heightTranslation_after_parity
    (A : ThreeLayerIdeleSymmetry G) (x : ZetaCenteredChart) :
    (toZetaSouriauLieSymmetry A).act x =
      heightTranslation A.layer.logScale (FourierParity.actOnCentered A.parity x) := by
  cases A with
  | mk layer parity =>
    cases layer with
    | mk logScale arithmetic =>
      cases parity <;>
        cases x <;>
        rfl

/-- The arithmetic layer does not affect the induced centered-chart action. -/
theorem act_eq_of_same_logScale_and_parity
    {A B : ThreeLayerIdeleSymmetry G}
    (hlog : A.layer.logScale = B.layer.logScale)
    (hpar : A.parity = B.parity)
    (x : ZetaCenteredChart) :
    (toZetaSouriauLieSymmetry A).act x =
      (toZetaSouriauLieSymmetry B).act x := by
  cases A
  cases B
  simp_all [toZetaSouriauLieSymmetry]

/-- The dual parity layer acts on centered coordinates by the critical mirror. -/
theorem dual_act_eq_heightTranslation_criticalMirror
    (A : ThreeLayerIdeleSymmetry G) (h : A.parity = FourierParity.dual)
    (x : ZetaCenteredChart) :
    (toZetaSouriauLieSymmetry A).act x =
      heightTranslation A.layer.logScale (criticalMirror x) := by
  rw [act_eq_heightTranslation_after_parity]
  simp [h, FourierParity.actOnCentered]

/-- For dual parity, fixed points modulo the height readout lie on the critical line `u = 0`. -/
theorem dual_fixed_iff_centeredCriticalLine
    (A : ThreeLayerIdeleSymmetry G) (h : A.parity = FourierParity.dual)
    (x : ZetaCenteredChart) :
    FourierParity.actOnCentered A.parity x = x ↔ x.u = 0 := by
  simpa [h] using FourierParity.dual_fixed_iff_centeredCriticalLine x

/--
The induced Souriau displacement energy is invariant under the three-layer chart
shadow.
-/
theorem zetaSouriauDisplacementEnergy_invariant
    (A : ThreeLayerIdeleSymmetry G) (beta moment : ZetaCenteredChart) :
    zetaSouriauDisplacementEnergy
        ((toZetaSouriauLieSymmetry A).act beta)
        ((toZetaSouriauLieSymmetry A).act moment) =
      zetaSouriauDisplacementEnergy beta moment := by
  exact ZetaSouriauSymmetryThermodynamics.zetaSouriauDisplacementEnergy_invariant
    (toZetaSouriauLieSymmetry A) beta moment

/--
The finite displacement Souriau partition is invariant under the induced
three-layer chart action.
-/
theorem zetaSouriauDisplacementPartition_invariant
    {State : Type*} [Fintype State]
    (A : ThreeLayerIdeleSymmetry G)
    (moment : State → ZetaCenteredChart)
    (beta : ZetaCenteredChart) :
    zetaSouriauDisplacementPartition
        (fun x => (toZetaSouriauLieSymmetry A).act (moment x))
        ((toZetaSouriauLieSymmetry A).act beta) =
      zetaSouriauDisplacementPartition moment beta := by
  exact ZetaSouriauSymmetryThermodynamics.zetaSouriauDisplacementPartition_invariant
    (toZetaSouriauLieSymmetry A) moment beta

/--
The finite displacement Massieu potential is invariant under the induced
three-layer chart action.
-/
theorem zetaSouriauDisplacementMassieu_invariant
    {State : Type*} [Fintype State]
    (A : ThreeLayerIdeleSymmetry G)
    (moment : State → ZetaCenteredChart)
    (beta : ZetaCenteredChart) :
    zetaSouriauDisplacementMassieu
        (fun x => (toZetaSouriauLieSymmetry A).act (moment x))
        ((toZetaSouriauLieSymmetry A).act beta) =
      zetaSouriauDisplacementMassieu moment beta := by
  exact ZetaSouriauSymmetryThermodynamics.zetaSouriauDisplacementMassieu_invariant
    (toZetaSouriauLieSymmetry A) moment beta

/--
The displacement-Massieu cocycle vanishes for the induced three-layer chart
shadow.
-/
theorem zetaSouriauDisplacementMassieuCocycle_eq_zero
    {State : Type*} [Fintype State]
    (A : ThreeLayerIdeleSymmetry G)
    (moment : State → ZetaCenteredChart)
    (beta : ZetaCenteredChart) :
    zetaSouriauDisplacementMassieuCocycle
        (toZetaSouriauLieSymmetry A) moment beta = 0 := by
  exact ZetaSouriauSymmetryThermodynamics.zetaSouriauDisplacementMassieuCocycle_eq_zero
    (toZetaSouriauLieSymmetry A) moment beta

/--
Conservative synthesis packet for a Bost--Connes/Souriau zeta symmetry model.

This records exactly the theorem-safe ingredients already present in the repo:
* three-layer idele symmetry shadow;
* cyclotomic arithmetic action;
* induced chart/Killing Souriau symmetry;
* optional trace realization predicate supplied externally.
-/
structure IdeleSouriauZetaModel
    (C_comm : Type*) [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    (G : Type*) [CommGroup G] [InfoGeometry.Canonical.BostConnesGalois.GaloisActionData G] where
  eRep : InfoGeometry.Canonical.BostConnesGalois.GroupElementRepresentation C_comm
  symmetry : ThreeLayerIdeleSymmetry G
  temperature : ℂ
  zetaReadout : ℂ → ℂ
  tracePartition : ℂ
  traceRealizes :
    ThreeLayerIdeleSymmetry.BostConnesTraceRealizesZeta
      (State := Unit)
      (fun _ => tracePartition)
      zetaReadout
      (fun _ => temperature)

/-- The model trace equals the zeta readout at the supplied temperature. -/
theorem model_tracePartition_eq_zetaReadout
    {C_comm : Type*} [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    {G : Type*} [CommGroup G] [InfoGeometry.Canonical.BostConnesGalois.GaloisActionData G]
    (M : IdeleSouriauZetaModel C_comm G) :
    M.tracePartition = M.zetaReadout M.temperature := by
  simpa using ThreeLayerIdeleSymmetry.tracePartition_eq_zetaReadout
    (State := Unit)
    (tracePartition := fun _ => M.tracePartition)
    (zetaReadout := M.zetaReadout)
    (temperature := fun _ => M.temperature)
    M.traceRealizes ()

end CommGroup

end InfoGeometry.Arithmetic.IdeleSouriauZetaThermodynamics
