import Mathlib.Tactic
import InfoGeometry.Topology.CuntzCantorSpectralTriple

/-!
# Holographic Cuntz Shard

Finite theorem-owner for the optical hologram intuition: an isometric shard can
carry a recoverable copy of its source sector, while its range projection records
the restricted aperture.

The abstract theorems use only the named `CuntzO2Carrier` hypotheses already
imported.  The finite shard model is an exact rational matrix model over `ℚ`.
Analytic Fourier holography, Reeh-Schlieder density, Tomita-Takesaki modular
flow, and infinite `C*` representation theorems are separate topics and are not
asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.HolographicCuntzShard

open InfoGeometry.Topology

universe u

variable {Op : Type u} [Ring Op] [StarRing Op]

/-- Left shard reconstruction in an abstract Cuntz `O₂` carrier. -/
theorem left_cuntz_shard_reconstructs
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (x : Op) :
    star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_left C * x) = x := by
  calc
    star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_left C * x) =
      (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
        InfoGeometry.Topology.CuntzO2Carrier.S_left C) * x := by
      rw [mul_assoc]
    _ = 1 * x := by
      rw [InfoGeometry.Topology.CuntzO2Carrier.left_isometry]
    _ = x := by simp

/-- Right shard reconstruction in an abstract Cuntz `O₂` carrier. -/
theorem right_cuntz_shard_reconstructs
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (x : Op) :
    star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_right C * x) = x := by
  calc
    star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_right C * x) =
      (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
        InfoGeometry.Topology.CuntzO2Carrier.S_right C) * x := by
      rw [mul_assoc]
    _ = 1 * x := by
      rw [InfoGeometry.Topology.CuntzO2Carrier.right_isometry]
    _ = x := by simp

/-- The left aperture/range projection of a Cuntz shard. -/
def leftAperture (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) : Op :=
  InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C

/-- The right aperture/range projection of a Cuntz shard. -/
def rightAperture (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) : Op :=
  InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C

/-- The left aperture is idempotent: the algebraic shadow of restricted viewing angle. -/
theorem left_aperture_idempotent (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    leftAperture C * leftAperture C = leftAperture C := by
  exact InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection_idempotent C

/-- The right aperture is idempotent. -/
theorem right_aperture_idempotent (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    rightAperture C * rightAperture C = rightAperture C := by
  exact InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection_idempotent C

/-- Two-shard aperture partition readout from the Cuntz relation. -/
theorem aperture_partition (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    leftAperture C + rightAperture C = 1 :=
  InfoGeometry.Topology.CuntzO2Carrier.range_sum C

/-! ## Finite exact-rational shard algebra -/

abbrev Mat2Q := Matrix (Fin 2) (Fin 2) ℚ

/-- A finite rational shard embedding the second coordinate into the first aperture. -/
def finiteShard : Mat2Q :=
  !![0, 1;
     0, 0]

/-- The complementary finite shard embedding the first coordinate into the second aperture. -/
def finiteComplementShard : Mat2Q :=
  !![0, 0;
     1, 0]

/-- The source sector selected by `finiteShard`. -/
def finiteSourceProjection : Mat2Q :=
  !![0, 0;
     0, 1]

/-- The observed aperture/range sector of `finiteShard`. -/
def finiteApertureProjection : Mat2Q :=
  !![1, 0;
     0, 0]

/-- The complementary source sector. -/
def finiteComplementSourceProjection : Mat2Q :=
  !![1, 0;
     0, 0]

/-- Finite shard source identity: `S* S` is the selected source projection. -/
theorem finiteShard_source :
    star finiteShard * finiteShard = finiteSourceProjection := by
  native_decide

/-- Finite shard aperture identity: `S S*` is the observed aperture projection. -/
theorem finiteShard_aperture :
    finiteShard * star finiteShard = finiteApertureProjection := by
  native_decide

/-- Complementary shard source identity. -/
theorem finiteComplementShard_source :
    star finiteComplementShard * finiteComplementShard = finiteComplementSourceProjection := by
  native_decide

/-- The two finite source sectors partition the signal plane. -/
theorem finite_source_partition :
    finiteSourceProjection + finiteComplementSourceProjection = 1 := by
  native_decide

/-- Finite source-sector reconstruction: the shard recovers exactly the selected component. -/
theorem finiteShard_reconstructs_source (x : Fin 2 → ℚ) :
    (star finiteShard).mulVec (finiteShard.mulVec x) = finiteSourceProjection.mulVec x := by
  ext i
  fin_cases i <;> simp [finiteShard, finiteSourceProjection, Matrix.mulVec]

/-- Finite aperture projection is idempotent. -/
theorem finiteAperture_idempotent :
    finiteApertureProjection * finiteApertureProjection = finiteApertureProjection := by
  native_decide

/-- Finite source projection is idempotent. -/
theorem finiteSource_idempotent :
    finiteSourceProjection * finiteSourceProjection = finiteSourceProjection := by
  native_decide

/-- The aperture is genuinely smaller than the full plane. -/
theorem finiteAperture_not_identity :
    finiteApertureProjection ≠ 1 := by
  intro h
  have h11 : finiteApertureProjection 1 1 = (1 : Mat2Q) 1 1 := by
    rw [h]
  norm_num [finiteApertureProjection] at h11

/-- Finite shard partial-isometry identity. -/
theorem finiteShard_partial_isometry :
    finiteShard * star finiteShard * finiteShard = finiteShard := by
  native_decide

/-- Compact packet joining the finite shard algebraic identities. -/
theorem finite_holographic_shard_packet (x : Fin 2 → ℚ) :
    (star finiteShard * finiteShard = finiteSourceProjection) ∧
      (finiteShard * star finiteShard = finiteApertureProjection) ∧
      ((star finiteShard).mulVec (finiteShard.mulVec x) = finiteSourceProjection.mulVec x) ∧
      (finiteApertureProjection * finiteApertureProjection = finiteApertureProjection) ∧
      (finiteSourceProjection + finiteComplementSourceProjection = 1) := by
  exact ⟨finiteShard_source, finiteShard_aperture,
    finiteShard_reconstructs_source x, finiteAperture_idempotent, finite_source_partition⟩

end InfoGeometry.Canonical.HolographicCuntzShard

end noncomputable section
