import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
    (C : CuntzO2Carrier Op) (x : Op) :
    star C.S_left * (C.S_left * x) = x := by
  calc
    star C.S_left * (C.S_left * x) = (star C.S_left * C.S_left) * x := by
      rw [mul_assoc]
    _ = 1 * x := by rw [C.left_isometry]
    _ = x := by simp

/-- Right shard reconstruction in an abstract Cuntz `O₂` carrier. -/
theorem right_cuntz_shard_reconstructs
    (C : CuntzO2Carrier Op) (x : Op) :
    star C.S_right * (C.S_right * x) = x := by
  calc
    star C.S_right * (C.S_right * x) = (star C.S_right * C.S_right) * x := by
      rw [mul_assoc]
    _ = 1 * x := by rw [C.right_isometry]
    _ = x := by simp

/-- The left aperture/range projection of a Cuntz shard. -/
def leftAperture (C : CuntzO2Carrier Op) : Op :=
  C.S_left * star C.S_left

/-- The right aperture/range projection of a Cuntz shard. -/
def rightAperture (C : CuntzO2Carrier Op) : Op :=
  C.S_right * star C.S_right

/-- The left aperture is idempotent: the algebraic shadow of restricted viewing angle. -/
theorem left_aperture_idempotent (C : CuntzO2Carrier Op) :
    leftAperture C * leftAperture C = leftAperture C := by
  calc
    (C.S_left * star C.S_left) * (C.S_left * star C.S_left)
        = C.S_left * (star C.S_left * C.S_left) * star C.S_left := by
          noncomm_ring
    _ = C.S_left * 1 * star C.S_left := by rw [C.left_isometry]
    _ = C.S_left * star C.S_left := by simp

/-- The right aperture is idempotent. -/
theorem right_aperture_idempotent (C : CuntzO2Carrier Op) :
    rightAperture C * rightAperture C = rightAperture C := by
  calc
    (C.S_right * star C.S_right) * (C.S_right * star C.S_right)
        = C.S_right * (star C.S_right * C.S_right) * star C.S_right := by
          noncomm_ring
    _ = C.S_right * 1 * star C.S_right := by rw [C.right_isometry]
    _ = C.S_right * star C.S_right := by simp

/-- Two-shard aperture partition readout from the Cuntz relation. -/
theorem aperture_partition (C : CuntzO2Carrier Op) :
    leftAperture C + rightAperture C = 1 :=
  C.range_sum

/-! ## Finite exact-rational shard algebra -/

abbrev Mat2Q := InfoGeometry.Algebra.FiniteSpin.Mat2Q

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
