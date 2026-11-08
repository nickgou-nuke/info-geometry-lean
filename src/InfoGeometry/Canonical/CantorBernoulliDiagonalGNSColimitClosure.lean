/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalGNSBridge

/-!
# Stage coherence of the Cantor-Bernoulli diagonal GNS sector

The finite diagonal GNS vectors must be compared after the actual UHF matrix
transition, not merely by their readouts in boundary `L²`. This file proves
successor and arbitrary-stage compatibility, then the mixed-stage
inner-product identity by transport to a common prefix level. It does not
identify the full noncommutative GNS colimit with the boundary Hilbert space.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace NNReal

open MeasureTheory

namespace InfoGeometry.Canonical.CantorBernoulliDiagonalGNSColimitClosure

open InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalGNSBridge
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagL2Embedding
open InfoGeometry.Canonical.CantorBernoulliCylinderColimitL2
open InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
open CStarStateColimit.Native.FilteredGNS

/-- The finite diagonal GNS vector is carried by the native successor map to
the GNS vector of the refined diagonal observable. -/
theorem gaugeDiagonalGNSStageDiagonalVector_transition_succ
    (n : ℕ) (f : DiagAlg n) :
    filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily
        (Nat.le.step (le_refl n))
        (gaugeDiagonalGNSStageDiagonalVector n f) =
      gaugeDiagonalGNSStageDiagonalVector (n + 1)
        (diagEmbedSucc n f) := by
  change filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily
      (Nat.le.step (le_refl n))
      ((gaugeStateFamily.state n).functional.toPreGNS
        ((cstarStageToBitWordStage n).symm (Matrix.diagonal f)) :
        gaugeGNSStage n) =
    ((gaugeStateFamily.state (n + 1)).functional.toPreGNS
      ((cstarStageToBitWordStage (n + 1)).symm
        (Matrix.diagonal (diagEmbedSucc n f))) :
      gaugeGNSStage (n + 1))
  rw [filteredGNSMap_toPreGNS]
  apply congrArg
    (fun A : CStarMatrixStage (n + 1) =>
      ((gaugeStateFamily.state (n + 1)).functional.toPreGNS A :
        gaugeGNSStage (n + 1)))
  apply (cstarStageToBitWordStage (n + 1)).injective
  calc
    cstarStageToBitWordStage (n + 1)
        (gaugeSystem.map (Nat.le.step (le_refl n))
          ((cstarStageToBitWordStage n).symm (Matrix.diagonal f))) =
      ComplexMatrixStage.bondFun n (Matrix.diagonal f) := by
        rw [cstarStageToBitWordStage_succ]
        simp
    _ = Matrix.diagonal (diagEmbedSucc n f) :=
      ComplexMatrixStage.bond_diagonal n f
    _ = cstarStageToBitWordStage (n + 1)
        ((cstarStageToBitWordStage (n + 1)).symm
          (Matrix.diagonal (diagEmbedSucc n f))) := by
        exact ((cstarStageToBitWordStage (n + 1)).apply_symm_apply _).symm

/-- The diagonal GNS readout preserves inner products between adjacent
prefix stages. The lower-stage vector is first transported to the common
successor stage, where the finite-stage inner-product theorem applies. -/
theorem gaugeDiagonalGNSHilbertColimitMap_inner_diagonal_succ
    (n : ℕ) (f : DiagAlg n) (g : DiagAlg (n + 1)) :
    inner ℂ
        (gaugeGNSStageToColimit n
          (gaugeDiagonalGNSStageDiagonalVector n f))
        (gaugeGNSStageToColimit (n + 1)
          (gaugeDiagonalGNSStageDiagonalVector (n + 1) g)) =
      inner ℂ (diagonalCylinderL2 n f)
        (diagonalCylinderL2 (n + 1) g) := by
  calc
    inner ℂ
        (gaugeGNSStageToColimit n
          (gaugeDiagonalGNSStageDiagonalVector n f))
        (gaugeGNSStageToColimit (n + 1)
          (gaugeDiagonalGNSStageDiagonalVector (n + 1) g)) =
      inner ℂ
        (gaugeGNSStageToColimit (n + 1)
          (filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily
            (Nat.le.step (le_refl n))
            (gaugeDiagonalGNSStageDiagonalVector n f)))
        (gaugeGNSStageToColimit (n + 1)
          (gaugeDiagonalGNSStageDiagonalVector (n + 1) g)) := by
            rw [← gaugeGNSStageToColimit_transition
              (Nat.le.step (le_refl n))
              (gaugeDiagonalGNSStageDiagonalVector n f)]
    _ = inner ℂ
        (filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily
          (Nat.le.step (le_refl n))
          (gaugeDiagonalGNSStageDiagonalVector n f))
        (gaugeDiagonalGNSStageDiagonalVector (n + 1) g) :=
          (gaugeGNSStageToColimit (n + 1)).inner_map_map _ _
    _ = inner ℂ
        (gaugeDiagonalGNSStageDiagonalVector (n + 1)
          (diagEmbedSucc n f))
        (gaugeDiagonalGNSStageDiagonalVector (n + 1) g) := by
          rw [gaugeDiagonalGNSStageDiagonalVector_transition_succ]
    _ = inner ℂ
        (diagonalCylinderL2 (n + 1) (diagEmbedSucc n f))
        (diagonalCylinderL2 (n + 1) g) :=
          gaugeDiagonalGNSStageDiagonalVector_inner (n + 1)
            (diagEmbedSucc n f) g
    _ = inner ℂ (diagonalCylinderL2 n f)
        (diagonalCylinderL2 (n + 1) g) := by
          rw [diagonalCylinderL2_compatible_succ]

/-- The canonical finite diagonal embedding from any prefix level to a later
level commutes with one further successor. -/
theorem diagEmbedTo_succ
    (n m : ℕ) (h : n ≤ m) (f : DiagAlg n) :
    diagEmbedTo n (m + 1) (h.trans (Nat.le_succ m)) f =
      diagEmbedSucc m (diagEmbedTo n m h f) := by
  ext w
  rfl

/-- Actual native GNS transitions carry every finite diagonal vector to its
canonical refinement at any later prefix level. -/
theorem gaugeDiagonalGNSStageDiagonalVector_transition
    {n m : ℕ} (hnm : n ≤ m) (f : DiagAlg n) :
    filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily hnm
        (gaugeDiagonalGNSStageDiagonalVector n f) =
      gaugeDiagonalGNSStageDiagonalVector m (diagEmbedTo n m hnm f) := by
  induction m, hnm using Nat.le_induction with
  | base =>
      rw [filteredGNSMap_id]
      have hdiag : diagEmbedTo n n (le_refl n) f = f := by
        ext w
        rfl
      rw [hdiag]
      rfl
  | succ m hnm ih =>
      calc
        filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily
            (Nat.le.step hnm) (gaugeDiagonalGNSStageDiagonalVector n f) =
          filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily
            (Nat.le.step (le_refl m))
            (filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily hnm
              (gaugeDiagonalGNSStageDiagonalVector n f)) := by
                have hcomp := congrFun
                  (filteredGNSMap_comp gaugeStage gaugeSystem gaugeStateFamily
                    hnm (Nat.le.step (le_refl m)))
                  (gaugeDiagonalGNSStageDiagonalVector n f)
                have hproof :
                    le_trans hnm (Nat.le.step (le_refl m)) =
                      Nat.le.step hnm := Subsingleton.elim _ _
                simpa [hproof] using hcomp.symm
        _ = gaugeDiagonalGNSStageDiagonalVector (m + 1)
              (diagEmbedSucc m (diagEmbedTo n m hnm f)) := by
                rw [ih]
                exact gaugeDiagonalGNSStageDiagonalVector_transition_succ m
                  (diagEmbedTo n m hnm f)
        _ = gaugeDiagonalGNSStageDiagonalVector (m + 1)
              (diagEmbedTo n (m + 1) (Nat.le.step hnm) f) := by
                rw [diagEmbedTo_succ n m hnm f]

/-- The boundary `L²` cylinder map is compatible with the existing general
finite-prefix diagonal embedding. -/
theorem diagonalCylinderL2_compatible_of_le
    (n m : ℕ) (h : n ≤ m) (f : DiagAlg n) :
    diagonalCylinderL2 m (diagEmbedTo n m h f) = diagonalCylinderL2 n f := by
  change (cylinder_memLp m (diagEmbedTo n m h f)).toLp
      (cylinder m (diagEmbedTo n m h f)) =
    (cylinder_memLp n f).toLp (cylinder n f)
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun x =>
    congrFun (cylinder_diagEmbedTo n m h f) x

/-- Inner products of canonical diagonal GNS vectors are independent of their
chosen finite prefix levels. Both representatives are transported to their
common maximum stage before the finite-stage trace/integral identity is used. -/
theorem gaugeDiagonalGNSHilbertColimitMap_inner_diagonal_stages
    (n m : ℕ) (f : DiagAlg n) (g : DiagAlg m) :
    inner ℂ
        (gaugeGNSStageToColimit n
          (gaugeDiagonalGNSStageDiagonalVector n f))
        (gaugeGNSStageToColimit m
          (gaugeDiagonalGNSStageDiagonalVector m g)) =
      inner ℂ (diagonalCylinderL2 n f) (diagonalCylinderL2 m g) := by
  let k := max n m
  let f' := diagEmbedTo n k (Nat.le_max_left n m) f
  let g' := diagEmbedTo m k (Nat.le_max_right n m) g
  calc
    inner ℂ
        (gaugeGNSStageToColimit n
          (gaugeDiagonalGNSStageDiagonalVector n f))
        (gaugeGNSStageToColimit m
          (gaugeDiagonalGNSStageDiagonalVector m g)) =
      inner ℂ
        (gaugeGNSStageToColimit k
          (filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily
            (Nat.le_max_left n m)
            (gaugeDiagonalGNSStageDiagonalVector n f)))
        (gaugeGNSStageToColimit k
          (filteredGNSMap gaugeStage gaugeSystem gaugeStateFamily
            (Nat.le_max_right n m)
            (gaugeDiagonalGNSStageDiagonalVector m g))) := by
              rw [← gaugeGNSStageToColimit_transition
                (Nat.le_max_left n m)
                (gaugeDiagonalGNSStageDiagonalVector n f),
                ← gaugeGNSStageToColimit_transition
                (Nat.le_max_right n m)
                (gaugeDiagonalGNSStageDiagonalVector m g)]
    _ = inner ℂ
        (gaugeGNSStageToColimit k
          (gaugeDiagonalGNSStageDiagonalVector k f'))
        (gaugeGNSStageToColimit k
          (gaugeDiagonalGNSStageDiagonalVector k g')) := by
            rw [gaugeDiagonalGNSStageDiagonalVector_transition,
              gaugeDiagonalGNSStageDiagonalVector_transition]
    _ = inner ℂ (diagonalCylinderL2 k f') (diagonalCylinderL2 k g') := by
          rw [← gaugeDiagonalGNSStageDiagonalVector_inner]
          exact (gaugeGNSStageToColimit k).inner_map_map _ _
    _ = inner ℂ (diagonalCylinderL2 n f) (diagonalCylinderL2 m g) := by
          rw [diagonalCylinderL2_compatible_of_le n k
                (Nat.le_max_left n m) f,
              diagonalCylinderL2_compatible_of_le m k
                (Nat.le_max_right n m) g]

/-- The set of all canonical finite-stage diagonal vectors inside the
completed native GNS colimit. -/
def gaugeDiagonalGNSStageVectorSet : Set gaugeGNSHilbertColimit :=
  Set.range fun p : Σ n, DiagAlg n =>
    gaugeGNSStageToColimit p.1
      (gaugeDiagonalGNSStageDiagonalVector p.1 p.2)

/-- The algebraic diagonal sector is the complex linear span of the actual
finite-stage diagonal GNS vectors in the full colimit. -/
def gaugeDiagonalGNSAlgebraicDiagonalSubmodule :
    Submodule ℂ gaugeGNSHilbertColimit :=
  Submodule.span ℂ gaugeDiagonalGNSStageVectorSet

/-- The closed diagonal GNS sector, defined as the topological closure of the
algebraic span of the finite-stage diagonal GNS vectors. -/
def gaugeDiagonalGNSClosedDiagonalSector :
    ClosedSubmodule ℂ gaugeGNSHilbertColimit :=
  ⟨gaugeDiagonalGNSAlgebraicDiagonalSubmodule.topologicalClosure,
    Submodule.isClosed_topologicalClosure _⟩

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
/-- The GNS-to-boundary readout preserves inner products on the algebraic
span generated by all finite diagonal-stage vectors. -/
theorem gaugeDiagonalGNSHilbertColimitMap_inner_algebraic_diagonal
    {x y : gaugeGNSHilbertColimit}
    (hx : x ∈ gaugeDiagonalGNSAlgebraicDiagonalSubmodule)
    (hy : y ∈ gaugeDiagonalGNSAlgebraicDiagonalSubmodule) :
    inner ℂ x y =
      inner ℂ (gaugeDiagonalGNSHilbertColimitMap x)
        (gaugeDiagonalGNSHilbertColimitMap y) := by
  change x ∈ Submodule.span ℂ gaugeDiagonalGNSStageVectorSet at hx
  change y ∈ Submodule.span ℂ gaugeDiagonalGNSStageVectorSet at hy
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
      rcases hx with ⟨⟨n, f⟩, rfl⟩
      rcases hy with ⟨⟨m, g⟩, rfl⟩
      calc
        inner ℂ
            (gaugeGNSStageToColimit n
              (gaugeDiagonalGNSStageDiagonalVector n f))
            (gaugeGNSStageToColimit m
              (gaugeDiagonalGNSStageDiagonalVector m g)) =
          inner ℂ (diagonalCylinderL2 n f) (diagonalCylinderL2 m g) :=
            gaugeDiagonalGNSHilbertColimitMap_inner_diagonal_stages n m f g
        _ = inner ℂ
            (gaugeDiagonalGNSHilbertColimitMap
              (gaugeGNSStageToColimit n
                (gaugeDiagonalGNSStageDiagonalVector n f)))
            (gaugeDiagonalGNSHilbertColimitMap
              (gaugeGNSStageToColimit m
                (gaugeDiagonalGNSStageDiagonalVector m g)) ) := by
              rw [gaugeDiagonalGNSHilbertColimitMap_stage,
                gaugeDiagonalGNSMap_diagonal_stage,
                gaugeDiagonalGNSHilbertColimitMap_stage,
                gaugeDiagonalGNSMap_diagonal_stage]
  | zero_left y hy => simp
  | zero_right x hx => simp
  | add_left x₁ x₂ y hx₁ hx₂ hy h₁ h₂ =>
      calc
        inner ℂ (x₁ + x₂) y =
          inner ℂ x₁ y + inner ℂ x₂ y := inner_add_left _ _ _
        _ = inner ℂ
              (gaugeDiagonalGNSHilbertColimitMap x₁)
              (gaugeDiagonalGNSHilbertColimitMap y) +
            inner ℂ
              (gaugeDiagonalGNSHilbertColimitMap x₂)
              (gaugeDiagonalGNSHilbertColimitMap y) := by rw [h₁, h₂]
        _ = inner ℂ
              (gaugeDiagonalGNSHilbertColimitMap (x₁ + x₂))
              (gaugeDiagonalGNSHilbertColimitMap y) := by
                rw [ContinuousLinearMap.map_add, inner_add_left]
  | add_right x y₁ y₂ hx hy₁ hy₂ h₁ h₂ =>
      calc
        inner ℂ x (y₁ + y₂) =
          inner ℂ x y₁ + inner ℂ x y₂ := inner_add_right _ _ _
        _ = inner ℂ
              (gaugeDiagonalGNSHilbertColimitMap x)
              (gaugeDiagonalGNSHilbertColimitMap y₁) +
            inner ℂ
              (gaugeDiagonalGNSHilbertColimitMap x)
              (gaugeDiagonalGNSHilbertColimitMap y₂) := by rw [h₁, h₂]
        _ = inner ℂ
              (gaugeDiagonalGNSHilbertColimitMap x)
              (gaugeDiagonalGNSHilbertColimitMap (y₁ + y₂)) := by
                rw [ContinuousLinearMap.map_add, inner_add_right]
  | smul_left c x y hx hy h =>
      calc
        inner ℂ (c • x) y = star c * inner ℂ x y := inner_smul_left _ _ _
        _ = star c * inner ℂ
              (gaugeDiagonalGNSHilbertColimitMap x)
              (gaugeDiagonalGNSHilbertColimitMap y) := by rw [h]
        _ = inner ℂ (c • gaugeDiagonalGNSHilbertColimitMap x)
              (gaugeDiagonalGNSHilbertColimitMap y) := by
                exact (inner_smul_left _ _ _).symm
        _ = inner ℂ
              (gaugeDiagonalGNSHilbertColimitMap (c • x))
              (gaugeDiagonalGNSHilbertColimitMap y) := by
                rw [ContinuousLinearMap.map_smul]
  | smul_right c x y hx hy h =>
      calc
        inner ℂ x (c • y) = c * inner ℂ x y := inner_smul_right _ _ _
        _ = c * inner ℂ
              (gaugeDiagonalGNSHilbertColimitMap x)
              (gaugeDiagonalGNSHilbertColimitMap y) := by rw [h]
        _ = inner ℂ (gaugeDiagonalGNSHilbertColimitMap x)
              (c • gaugeDiagonalGNSHilbertColimitMap y) := by
                exact (inner_smul_right _ _ _).symm
        _ = inner ℂ
              (gaugeDiagonalGNSHilbertColimitMap x)
              (gaugeDiagonalGNSHilbertColimitMap (c • y)) := by
                rw [ContinuousLinearMap.map_smul]

/-- Restriction of the continuous diagonal readout to the closed diagonal
GNS sector. -/
def gaugeDiagonalGNSClosedSectorReadout :
    gaugeDiagonalGNSClosedDiagonalSector.toSubmodule →L[ℂ] L2Boundary :=
  gaugeDiagonalGNSHilbertColimitMap.comp
    gaugeDiagonalGNSClosedDiagonalSector.toSubmodule.subtypeL

/-- The finite-stage diagonal span is dense in its closed-sector subtype.
This is the canonical inclusion into the closure, not an extra density
hypothesis. -/
theorem gaugeDiagonalGNSAlgebraicToClosedSector_denseRange :
    DenseRange (fun x : gaugeDiagonalGNSAlgebraicDiagonalSubmodule =>
      (⟨(x : gaugeGNSHilbertColimit),
        Submodule.le_topologicalClosure
          gaugeDiagonalGNSAlgebraicDiagonalSubmodule x.property⟩ :
        gaugeDiagonalGNSClosedDiagonalSector.toSubmodule)) := by
  rw [denseRange_iff_closure_range]
  have himage :
      (Subtype.val : gaugeDiagonalGNSClosedDiagonalSector.toSubmodule →
        gaugeGNSHilbertColimit) ''
          Set.range (fun x : gaugeDiagonalGNSAlgebraicDiagonalSubmodule =>
            (⟨(x : gaugeGNSHilbertColimit),
              Submodule.le_topologicalClosure
                gaugeDiagonalGNSAlgebraicDiagonalSubmodule x.property⟩ :
              gaugeDiagonalGNSClosedDiagonalSector.toSubmodule)) =
        (gaugeDiagonalGNSAlgebraicDiagonalSubmodule :
          Set gaugeGNSHilbertColimit) := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact x.property
    · intro hz
      refine ⟨⟨z, Submodule.le_topologicalClosure
        gaugeDiagonalGNSAlgebraicDiagonalSubmodule hz⟩, ?_, rfl⟩
      refine ⟨⟨z, hz⟩, ?_⟩
      apply Subtype.ext
      rfl
  ext z
  rw [closure_subtype, himage]
  have hz := z.property
  change (z : gaugeGNSHilbertColimit) ∈
    gaugeDiagonalGNSAlgebraicDiagonalSubmodule.topologicalClosure at hz
  simp only [Set.mem_univ, iff_true]
  change (z : gaugeGNSHilbertColimit) ∈
    closure (gaugeDiagonalGNSAlgebraicDiagonalSubmodule :
      Set gaugeGNSHilbertColimit)
  rw [← Submodule.topologicalClosure_coe]
  exact hz

/-- The continuous diagonal readout preserves inner products on the entire
closed diagonal GNS sector. The result follows by continuity from the
algebraic-span theorem and density of that span in its closure. -/
theorem gaugeDiagonalGNSClosedSectorReadout_inner
    (x y : gaugeDiagonalGNSClosedDiagonalSector.toSubmodule) :
    inner ℂ x y =
      inner ℂ (gaugeDiagonalGNSClosedSectorReadout x)
        (gaugeDiagonalGNSClosedSectorReadout y) := by
  let f := gaugeDiagonalGNSClosedSectorReadout
  have hleft : Continuous (fun p :
      gaugeDiagonalGNSClosedDiagonalSector.toSubmodule ×
        gaugeDiagonalGNSClosedDiagonalSector.toSubmodule =>
      inner ℂ p.1 p.2) :=
    continuous_inner (𝕜 := ℂ)
      (E := gaugeDiagonalGNSClosedDiagonalSector.toSubmodule)
  have hright : Continuous (fun p :
      gaugeDiagonalGNSClosedDiagonalSector.toSubmodule ×
        gaugeDiagonalGNSClosedDiagonalSector.toSubmodule =>
      inner ℂ (f p.1) (f p.2)) :=
    (continuous_inner (𝕜 := ℂ) (E := L2Boundary)).comp
      (f.continuous.prodMap f.continuous)
  have hclosed : IsClosed {p :
      gaugeDiagonalGNSClosedDiagonalSector.toSubmodule ×
        gaugeDiagonalGNSClosedDiagonalSector.toSubmodule |
      inner ℂ p.1 p.2 = inner ℂ (f p.1) (f p.2)} :=
    isClosed_eq hleft hright
  refine
    (gaugeDiagonalGNSAlgebraicToClosedSector_denseRange).induction_on₂
      hclosed ?_ x y
  intro a b
  change inner ℂ (a : gaugeGNSHilbertColimit)
      (b : gaugeGNSHilbertColimit) =
    inner ℂ (gaugeDiagonalGNSHilbertColimitMap a)
      (gaugeDiagonalGNSHilbertColimitMap b)
  exact gaugeDiagonalGNSHilbertColimitMap_inner_algebraic_diagonal
    a.property b.property

/-- The closed-sector readout, now proved to be a complex linear isometry by
its preservation of the full inner product. -/
def gaugeDiagonalGNSClosedSectorReadoutLinearIsometry :
    gaugeDiagonalGNSClosedDiagonalSector.toSubmodule →ₗᵢ[ℂ] L2Boundary :=
  LinearMap.isometryOfInner
    gaugeDiagonalGNSClosedSectorReadout.toLinearMap
    (fun x y =>
      (gaugeDiagonalGNSClosedSectorReadout_inner x y).symm)

/-- The closed diagonal sector readout has dense range because it contains
every finite Bernoulli cylinder function and those cylinder functions are
dense in `L2Boundary`. -/
theorem gaugeDiagonalGNSClosedSectorReadoutLinearIsometry_denseRange :
    DenseRange gaugeDiagonalGNSClosedSectorReadoutLinearIsometry := by
  apply cylinderColimitToL2_denseRange.mono
  rintro y ⟨g, rfl⟩
  obtain ⟨⟨n, f⟩, hg⟩ := g.property
  have hstage :
      g = ⟨cylinder n f, cylinder_mem_colimit n f⟩ := by
    apply Subtype.ext
    exact hg.symm
  have hmem : gaugeGNSStageToColimit n
      (gaugeDiagonalGNSStageDiagonalVector n f) ∈
        gaugeDiagonalGNSAlgebraicDiagonalSubmodule := by
    change gaugeGNSStageToColimit n
        (gaugeDiagonalGNSStageDiagonalVector n f) ∈
      Submodule.span ℂ gaugeDiagonalGNSStageVectorSet
    exact Submodule.subset_span ⟨⟨n, f⟩, rfl⟩
  let x : gaugeDiagonalGNSClosedDiagonalSector.toSubmodule :=
    ⟨gaugeGNSStageToColimit n
      (gaugeDiagonalGNSStageDiagonalVector n f),
      Submodule.le_topologicalClosure
        gaugeDiagonalGNSAlgebraicDiagonalSubmodule hmem⟩
  refine ⟨x, ?_⟩
  change gaugeDiagonalGNSHilbertColimitMap
      (gaugeGNSStageToColimit n
        (gaugeDiagonalGNSStageDiagonalVector n f)) = _
  rw [gaugeDiagonalGNSHilbertColimitMap_stage,
    gaugeDiagonalGNSMap_diagonal_stage, hstage,
    cylinderColimitToL2_stage]

/-- A dense-range linear isometry from the complete closed diagonal sector
is surjective. -/
theorem gaugeDiagonalGNSClosedSectorReadoutLinearIsometry_surjective :
    Function.Surjective gaugeDiagonalGNSClosedSectorReadoutLinearIsometry := by
  let : CompleteSpace gaugeDiagonalGNSClosedDiagonalSector.toSubmodule :=
    Submodule.topologicalClosure.completeSpace
      gaugeDiagonalGNSAlgebraicDiagonalSubmodule
  let e := gaugeDiagonalGNSClosedSectorReadoutLinearIsometry
  have hclosed : IsClosed (Set.range e) :=
    e.isometry.antilipschitzWith.isClosed_range
      e.isometry.lipschitzWith.uniformContinuous
  have hdense : Dense (Set.range e) :=
    gaugeDiagonalGNSClosedSectorReadoutLinearIsometry_denseRange
  intro y
  exact hdense.induction (fun _ hy => hy) hclosed y

/-- The canonical Bernoulli boundary `L²` space is linearly isometric to
the closed span of finite diagonal vectors inside the native filtered matrix
GNS Hilbert colimit. This is a diagonal-sector identification, not an
identification of the full noncommutative GNS colimit. -/
def gaugeDiagonalGNSClosedSectorReadoutEquiv :
    gaugeDiagonalGNSClosedDiagonalSector.toSubmodule ≃ₗᵢ[ℂ] L2Boundary :=
  LinearIsometryEquiv.ofSurjective
    gaugeDiagonalGNSClosedSectorReadoutLinearIsometry
    gaugeDiagonalGNSClosedSectorReadoutLinearIsometry_surjective

end InfoGeometry.Canonical.CantorBernoulliDiagonalGNSColimitClosure

end
