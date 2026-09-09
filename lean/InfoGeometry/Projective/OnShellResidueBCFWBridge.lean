import InfoGeometry.Projective.KleinQuadricGrothendieckDeRham
import InfoGeometry.Projective.QDeformedTwistorAmplituhedronBridge
import InfoGeometry.Projective.TwistorAmplituhedronBridge
import InfoGeometry.Topology.GrandUnificationLinker
import InfoGeometry.Topology.ThermodynamicGauge

/-!
# On-Shell Residue / BCFW Interface

This module records the theorem-safe computational shift from diagram
bookkeeping to residue/on-shell boundary readouts.

Closed here:

* the local `dlog` residue around one Klein factor is the existing `2πi`
  circle-integral theorem;
* an Arnold mixed relation evaluates to zero in any target whose kernel
  contains that relation;
* a three-boundary residue balance gives a BCFW-style readout only through an
  explicit supplied implication;
* the illustrative `220` diagram count versus `1` carrier count is finite
  arithmetic only.

Not closed here:

* no Feynman-diagram theorem is proved;
* no scattering amplitude is computed;
* no residue theorem on a compactified configuration space is proved;
* no BCFW recursion theorem is derived from differential forms;
* no amplituhedron volume or positive-geometry statement is proved.
-/

namespace InfoGeometry.Projective.OnShellResidueBCFWBridge

open scoped BigOperators

open InfoGeometry.Projective.ArnoldRelations
open InfoGeometry.Projective.KleinQuadric.DeRhamMotive
open InfoGeometry.Projective.QDeformedTwistorAmplituhedronBridge
open InfoGeometry.Projective.TwistorAmplituhedronConfigurationBridge

/-! ## Local dlog residue boundary -/

/-- The local `dlog` pole model around one Klein factor gives `2πi`. -/
theorem local_dlog_residue (R : ℝ) (hR : 0 < R) :
    (∮ z in C((0 : ℂ), R), grothendieck_dlog z) =
      (2 * Real.pi * Complex.I : ℂ) :=
  circleIntegral_grothendieck_dlog R hR

/-! ## Finite Arnold-to-residue interface -/

/--
A concrete realization of the three-edge Arnold mixed relation in a target
semiring.

The field `hKernel` is the mathematical obligation: it says the selected target
model kills the Arnold relation.  This structure does not construct the
concrete `d log Q` differential forms.
-/
structure ArnoldResidueRealization
    (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    (A : Type*) [Semiring A] where
  w12 : ArnoldExterior R M
  w23 : ArnoldExterior R M
  w31 : ArnoldExterior R M
  φ : ArnoldExterior R M →+* A
  hKernel : arnoldMixedRelation R M w12 w23 w31 ∈ RingHom.ker φ

namespace ArnoldResidueRealization

/-- The target realization evaluates the Arnold mixed relation to zero. -/
theorem arnold_relation_zero
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {A : Type*} [Semiring A]
    (D : ArnoldResidueRealization R M A) :
    D.φ (arnoldMixedRelation R M D.w12 D.w23 D.w31) = 0 :=
  arnold_mixed_relation_vanishes_under_kernel_membership
    R M D.w12 D.w23 D.w31 D.φ D.hKernel

end ArnoldResidueRealization

/-! ## Native Thermodynamic BCFW boundary -/

open InfoGeometry.Topology.GrandUnificationLinker
open InfoGeometry.Topology.ThermodynamicGauge
/--
Native finite BCFW-style readout from the closed DAG-flow theorem.

This is exactly the theorem proved in `GrandUnificationLinker`, restated at the
residue interface boundary. It does not compute a physical scattering amplitude.
-/
theorem residue_bcfw
    {Op : Type*} [Ring Op] [Star Op]
    (jewel : QuantumJewel Op) :
    jewel.dag_edge * amplituhedron_volume_element jewel =
      amplituhedron_volume_element jewel * jewel.dag_edge :=
  global_isometry_preservation jewel

/-! ## Diagram-bookkeeping compression surface -/

/--
Finite bookkeeping surface for the common six-gluon tree-level comparison.

The values are explicit arithmetic data.  They are not a theorem about
Feynman diagrams or Parke-Taylor amplitudes.
-/
structure DiagramCompressionDatum where
  diagramCount : ℕ
  carrierCount : ℕ
  diagramCount_eq : diagramCount = 220
  carrierCount_eq : carrierCount = 1

/-- The bookkeeping carrier count is strictly smaller than the diagram count. -/
theorem diagram_compression_count
    (D : DiagramCompressionDatum) :
    D.carrierCount < D.diagramCount := by
  rw [D.carrierCount_eq, D.diagramCount_eq]
  norm_num

/-- The illustrative bookkeeping difference is `219`. -/
theorem diagram_compression_difference
    (D : DiagramCompressionDatum) :
    D.diagramCount - D.carrierCount = 219 := by
  simp [D.diagramCount_eq, D.carrierCount_eq]

/-! ## Combined q-stable on-shell packet -/

/--
Combined finite packet for the q-stable twistor/residue lane.
The BCFW readout is now native.
-/
structure OnShellQResidueComputationDatum {Op : Type*} [Ring Op] [Star Op] [Algebra ℝ Op]
    (moving : ℕ) (jewel : QuantumJewel Op)
    (trace : Op →ₗ[ℝ] ℝ) extends
    QDeformedTwistorAmplituhedronDatum moving where
  compression : DiagramCompressionDatum

/-- Combined readback for the finite q-stable on-shell/residue interface. -/
theorem on_shell_q_residue_packet {Op : Type*} [Ring Op] [Star Op] [Algebra ℝ Op]
    {moving : ℕ} {jewel : QuantumJewel Op}
    {trace : Op →ₗ[ℝ] ℝ}
    (D : OnShellQResidueComputationDatum moving jewel trace)
    (i : Fin 3) :
    InKuzminOpenWindow D.qStable.q ∧
      Nonempty (D.qStable.qCarrier ≃ D.qStable.toeplitzCarrier) ∧
      D.compression.carrierCount < D.compression.diagramCount ∧
      (jewel.dag_edge * amplituhedron_volume_element jewel =
        amplituhedron_volume_element jewel * jewel.dag_edge) ∧
      InfoGeometry.Projective.KleinQuadric.Plucker6.IsKlein (D.base.lines.line i) := by
  exact ⟨D.qStable.inWindow,
    ⟨D.qStable.stableEquiv⟩,
    diagram_compression_count D.compression,
    residue_bcfw jewel,
    D.base.lines.line_isKlein i⟩

/--
Package an on-shell residue packet into BCFW + curvature readouts.
This helper keeps the Option-B interface explicit.
-/
def on_shell_q_residue_to_bost_connes_certificate
    {Op : Type*} [Ring Op] [Star Op] [Algebra ℝ Op]
    {moving : ℕ} {jewel : QuantumJewel Op}
    {trace : Op →ₗ[ℝ] ℝ}
    (_D : OnShellQResidueComputationDatum moving jewel trace)
    (path : List Op)
    (zetaValue : ℝ)
    (h_holonomy : trace (finite_wilson_loop path) = zetaValue)
    (h_curvature :
      trace (thermodynamic_curvature jewel.thermodynamic_flow) = zetaValue) :
    trace (finite_wilson_loop path) = zetaValue ∧
    trace (thermodynamic_curvature jewel.thermodynamic_flow) = zetaValue :=
  ⟨h_holonomy, h_curvature⟩

end InfoGeometry.Projective.OnShellResidueBCFWBridge
