import InfoGeometry.Topology.PositiveGrassmannianAmplituhedronTopological
import InfoGeometry.Topology.SymbolicLatentCore

/-!
# Symbolic latent readout of bounded amplituhedron stages

The carrier is the subtype of one finite bounded amplituhedron image.  Its
coordinate observables form a finite symbolic latent system.  This is a
topological readout only: it does not identify the latent image with a
Grassmannian quotient or with scattering data.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

variable {k n m : ℕ}

abbrev BoundedAmplituhedronCarrier
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :=
  {Y : Matrix (Fin k) (Fin m) ℝ //
    Y ∈ boundedAmplituhedronImage (k := k) (n := n) (m := m) Z B}

abbrev BoundedAmplituhedronCoordinateObservable
    (k n m : ℕ) (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :=
  ContinuousObservable (BoundedAmplituhedronCarrier (k := k) Z B)

def boundedAmplituhedronCoordinateObservable
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ)
    (i : Fin k) (j : Fin m) :
    BoundedAmplituhedronCoordinateObservable k n m Z B :=
  { toFun := fun Y => Y.1 i j
    continuous_toFun := (continuous_apply j).comp
      ((continuous_apply i).comp continuous_subtype_val) }

abbrev BoundedAmplituhedronLatentSystem
    (k n m : ℕ) (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :=
  FiniteContinuousObservableSystem
    (BoundedAmplituhedronCarrier (k := k) Z B) (Fin k × Fin m)

def boundedAmplituhedronLatentSystem
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    BoundedAmplituhedronLatentSystem k n m Z B :=
  fun ij => boundedAmplituhedronCoordinateObservable Z B ij.1 ij.2

def boundedAmplituhedronObservationMap
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    BoundedAmplituhedronCarrier (k := k) Z B → (Fin k × Fin m → ℝ) :=
  (boundedAmplituhedronLatentSystem (k := k) Z B).observationMap

/-- The bounded amplituhedron carrier is compact as a subtype of a compact
finite image. -/
noncomputable instance boundedAmplituhedronCarrier_compactSpace
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    CompactSpace (BoundedAmplituhedronCarrier (k := k) Z B) :=
  isCompact_iff_compactSpace.mp
    (isCompact_boundedAmplituhedronImage (k := k) (n := n) (m := m) Z B)

/-- Compactness yields local compactness for the bounded amplituhedron carrier. -/
instance boundedAmplituhedronCarrier_locallyCompactSpace
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    LocallyCompactSpace (BoundedAmplituhedronCarrier (k := k) Z B) := by
  infer_instance

theorem continuous_boundedAmplituhedronObservationMap
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    Continuous (boundedAmplituhedronObservationMap (k := k) Z B) := by
  unfold boundedAmplituhedronObservationMap
  exact continuous_observationMap _

theorem isCompact_boundedAmplituhedronObservationImage
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    IsCompact (boundedAmplituhedronObservationMap (k := k) Z B ''
      (Set.univ : Set (BoundedAmplituhedronCarrier (k := k) Z B))) := by
  exact isCompact_univ.image
    (continuous_boundedAmplituhedronObservationMap Z B)

theorem isClosed_boundedAmplituhedronObservationImage
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    IsClosed (boundedAmplituhedronObservationMap (k := k) Z B ''
      (Set.univ : Set (BoundedAmplituhedronCarrier (k := k) Z B))) := by
  exact (isCompact_boundedAmplituhedronObservationImage (k := k) Z B).isClosed

theorem boundedAmplituhedronLatentSystem_feasibleSet_isClosed
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ)
    (targets : Fin k × Fin m → Set ℝ)
    (hclosed : ∀ ij, IsClosed (targets ij)) :
    IsClosed ((boundedAmplituhedronLatentSystem (k := k) Z B).feasibleSet targets) := by
  exact isClosed_feasibleSet
    (boundedAmplituhedronLatentSystem (k := k) Z B) targets hclosed

theorem boundedAmplituhedronLatentSystem_feasibleSet_isCompact
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ)
    (targets : Fin k × Fin m → Set ℝ)
    (hclosed : ∀ ij, IsClosed (targets ij)) :
    IsCompact ((boundedAmplituhedronLatentSystem (k := k) Z B).feasibleSet targets) := by
  exact isCompact_feasibleSet
    (boundedAmplituhedronLatentSystem (k := k) Z B) targets hclosed

end InfoGeometry.Topology
