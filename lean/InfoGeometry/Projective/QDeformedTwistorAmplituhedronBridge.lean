import InfoGeometry.Projective.KuzminCuntzPath
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.TwistorAmplituhedronConfigurationBridge

/-!
# q-Deformed Twistor / Amplituhedron Bridge

This file attaches the repo's finite Kuzmin q-CCR surface to the conservative
twistor/amplituhedron configuration bridge.

Closed here:

* the open Kuzmin window is the explicit inequality `|q| < 1`;
* `q = 0` lies in that window, while the CAR/CCR endpoints `q = -1` and
  `q = 1` do not;
* the existing finite q-Gram positivity and endpoint q-CCR readbacks are
  re-exported at the projective bridge layer;
* a q-deformed amplituhedron/topological-stability statement is only a supplied
  comparison interface.

Not closed here:

* no C*-classification theorem is proved;
* no theorem identifies q-CCR stability with amplituhedron invariance;
* no theorem proves q-deformed BCFW recursion, q-deformed plabic moves, or
  physical scattering-amplitude stability.
-/

namespace InfoGeometry.Projective.QDeformedTwistorAmplituhedronBridge

open InfoGeometry.Algebra.QCCR.Kuzmin
open InfoGeometry.Algebra.QCCR.Proved
open InfoGeometry.Projective.KuzminCuntzPath
open InfoGeometry.Projective.TwistorAmplituhedronConfigurationBridge
open InfoGeometry.Projective.PenroseSpinTiling
open InfoGeometry.Topology.Delaunay
open InfoGeometry.Topology.PureBraid
open InfoGeometry.Topology.RohozhkinBoundary

/-- The open real q-window used by Kuzmin's Fock-image Cuntz-Toeplitz theorem. -/
abbrev InKuzminOpenWindow (q : ℝ) : Prop :=
  |q| < 1

/-- The Cuntz-Toeplitz midpoint `q = 0` is inside the open Kuzmin window. -/
theorem zero_mem_kuzmin_open_window :
    InKuzminOpenWindow (0 : ℝ) := by
  norm_num [InKuzminOpenWindow]

/-- The CAR endpoint `q = -1` is a boundary readout, not an interior Kuzmin-window point. -/
theorem minus_one_not_mem_kuzmin_open_window :
    ¬ InKuzminOpenWindow (-1 : ℝ) := by
  norm_num [InKuzminOpenWindow]

/-- The CCR endpoint `q = 1` is a boundary readout, not an interior Kuzmin-window point. -/
theorem one_not_mem_kuzmin_open_window :
    ¬ InKuzminOpenWindow (1 : ℝ) := by
  norm_num [InKuzminOpenWindow]

/-! ## Finite q-CCR readbacks -/

/-- Finite q-Gram positivity readback for the `k=2,n=2` owner theorem. -/
theorem q_window_finite_gram_positive
    (q : ℝ) (hq : InKuzminOpenWindow q) (x : Fin 4 → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ ((gram_matrix_k2_n2 q).mulVec x) :=
  finite_q_gram_positive q hq x hx

/-- At `q = 0`, the algebraic q-CCR seed has Cuntz-Toeplitz orthogonality. -/
theorem q_seed_toeplitz_endpoint_readback
    {R : Type*} [CommRing R] [StarRing R]
    (H : QCCRSeed R)
    (hq : H.q = (0 : R))
    (i j : Fin 2) :
    H.creation i * H.annihilation j =
      (if i = j then 1 else 0) :=
  seed_toeplitz_limit (H := H) hq i j

/-- At `q = -1`, the algebraic q-CCR seed has the CAR anticommutation readout. -/
theorem q_seed_car_endpoint_readback
    {R : Type*} [CommRing R] [StarRing R]
    (H : QCCRSeed R)
    (hq : H.q = (-1 : R))
    (i j : Fin 2) :
    H.creation i * H.annihilation j + H.annihilation j * H.creation i =
      (if i = j then 1 else 0) :=
  seed_car_from_minus_one (H := H) hq i j

/-- At `q = 1`, the algebraic q-CCR seed has the CCR commutator readout. -/
theorem q_seed_ccr_endpoint_readback
    {R : Type*} [CommRing R] [StarRing R]
    (H : QCCRSeed R)
    (hq : H.q = (1 : R))
    (i j : Fin 2) :
    H.creation i * H.annihilation j - H.annihilation j * H.creation i =
      (if i = j then 1 else 0) :=
  seed_ccr_from_plus_one (H := H) hq i j

/-! ## q-deformed carrier interface -/

universe u

/--
An explicit q-stable carrier equivalence.

This is deliberately weaker than Kuzmin's C*-algebra theorem: it records the
specific carrier equivalence supplied to a downstream bridge.
-/
structure KuzminQStableCarrier where
  q : ℝ
  inWindow : InKuzminOpenWindow q
  qCarrier : Type u
  toeplitzCarrier : Type u
  stableEquiv : qCarrier ≃ toeplitzCarrier

/-- A q-stable carrier always has the open-window proof used by the finite q-Gram owner. -/
theorem qStableCarrier_in_window (K : KuzminQStableCarrier.{u}) :
    InKuzminOpenWindow K.q :=
  K.inWindow

/-- The supplied q-stability equivalence is explicit data. -/
def qStableCarrier_equiv (K : KuzminQStableCarrier.{u}) :
    K.qCarrier ≃ K.toeplitzCarrier :=
  K.stableEquiv

/--
Interface asserting that the q-stable carrier preserves the chosen
twistor/amplituhedron comparison layer.

The preservation claims are fields.  This file only wires them to the already
checked Klein/rank/Rohozhkin packets.
-/
structure QDeformedTwistorAmplituhedronDatum (moving : ℕ) where
  base : TwistorAmplituhedronBridgeDatum moving
  qStable : KuzminQStableCarrier

namespace QDeformedTwistorAmplituhedronDatum

/--
Boundary preservation is the already-installed Klein-incidence to
amplituhedron-boundary map of the undeformed owner.
-/
theorem boundaryPreserved {moving : ℕ}
    (D : QDeformedTwistorAmplituhedronDatum moving)
    {i j : Fin 3} (hij : i ≠ j)
    (hinc : D.base.lines.OnIncidenceBoundary i j) :
    D.base.boundary.boundary i j :=
  D.base.boundary.incidence_to_boundary hij hinc

/-- The configured spin-tiled rank equals the selected scattering-state budget. -/
theorem rankBudgetPreserved {moving : ℕ}
    (D : QDeformedTwistorAmplituhedronDatum moving) :
    D.base.rank.data.totalRank * spinTilingMultiplicity =
      D.base.rank.stateBudget :=
  spin_tiled_rank_matches_stateBudget D.base.rank

/-- The native Arnold/cooperad and BCFW operators agree in the base packet. -/
theorem bcfwComparisonPreserved {moving : ℕ}
    (D : QDeformedTwistorAmplituhedronDatum moving)
    (hComparison : D.base.arnoldBCFW.cooperadReadout =
      D.base.arnoldBCFW.bcfwReadout) :
    D.base.arnoldBCFW.cooperadReadout =
      D.base.arnoldBCFW.bcfwReadout :=
  hComparison

end QDeformedTwistorAmplituhedronDatum

/--
Combined readback: the supplied q-carrier is in the Kuzmin open window, the
carrier equivalence is explicit, the selected stability comparisons hold, and
the undeformed twistor/amplituhedron packet remains available.
-/
theorem q_deformed_twistor_amplituhedron_packet {moving : ℕ}
    (D : QDeformedTwistorAmplituhedronDatum moving)
    (hComparison : D.base.arnoldBCFW.cooperadReadout =
      D.base.arnoldBCFW.bcfwReadout)
    (i : Fin 3) :
    InKuzminOpenWindow D.qStable.q ∧
      Nonempty (D.qStable.qCarrier ≃ D.qStable.toeplitzCarrier) ∧
      D.base.arnoldBCFW.cooperadReadout =
        D.base.arnoldBCFW.bcfwReadout ∧
      InfoGeometry.Projective.KleinQuadric.Plucker6.IsKlein (D.base.lines.line i) ∧
      D.base.rank.data.totalRank * spinTilingMultiplicity = D.base.rank.stateBudget ∧
      ∃ ρ : RohozhkinPureBraidGroup moving →* RohozhkinMatrixUnits moving,
        ∀ g : PureBraidGenerator (rohozhkinTotalPoints moving),
          ρ (of g) = InfoGeometry.Projective.RohozhkinDelaunayScramblingBridge.rohozhkinProjectiveBraidPacketGen D.base.rohozhkin.packet g := by
  have hbase := twistor_amplituhedron_bridge_packet D.base i
  exact ⟨D.qStable.inWindow,
    ⟨D.qStable.stableEquiv⟩,
    D.bcfwComparisonPreserved hComparison,
    hbase.1,
    hbase.2.1,
    hbase.2.2⟩

end InfoGeometry.Projective.QDeformedTwistorAmplituhedronBridge
