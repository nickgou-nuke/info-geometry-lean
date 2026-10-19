/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinBottleCanonicalCarrier
import InfoGeometry.Topology.KleinBottleOrbitQuotient
import InfoGeometry.Topology.KleinBrillouinBase
import InfoGeometry.Topology.KleinBottleCellularEuler
import InfoGeometry.Topology.KleinBottleExteriorOrientationBridge
import InfoGeometry.Superalgebra.SplitOctonionTwistedParityElement

/-!
# Kernel-checked Klein/glide/parity interfaces

This file records individual compatibility theorems only.  The compact mapping
-torus carrier, the torus orbit quotient, the cellular rank model, the deck
orientation character, and the split-octonion parity path remain distinct
carriers; each bridge below states its exact compatibility.
-/

noncomputable section
namespace InfoGeometry.Topology.KleinBottleCanonicalBridge

open KleinBrillouinBase
open KleinBottleOrbitQuotient
open InfoGeometry.Topology.KleinBottleCanonicalCarrier
open InfoGeometry.Topology.KleinBottleCellularEuler
open InfoGeometry.Topology.KleinBottleExteriorOrientationBridge
open InfoGeometry.Topology.KleinQuotientDeckInvariants
open InfoGeometry.Superalgebra.MadelungNonassociativeVortex
open InfoGeometry.Superalgebra.WittenMoebiusParity

/-- The lifted glide has the defining Klein relation with transverse translation. -/
theorem glide_conjugates_transverse_translation (k : Cover) :
    glide (ty (glideInv k)) = tyInv k :=
  glide_conj_ty k

/-- The lifted glide squares to the longitudinal period. -/
theorem glide_square_is_longitudinal_period (k : Cover) :
    glide (glide k) = tx k :=
  glide_sq k

/-- The affine glide descends to the torus glide. -/
theorem cover_to_torus_glide_equivariant (k : Cover) :
    coverToTorus (glide k) = torusGlide (coverToTorus k) :=
  coverToTorus_glide k

/-- The orbit quotient projection is invariant under the torus glide. -/
theorem orbit_projection_glide_invariant (k : BrillouinTorus) :
    quotientMap (torusGlide k) = quotientMap k :=
  quotientMap_glide k

/-- The compact mapping-torus endpoint gluing for fibre negation. -/
theorem compact_klein_endpoint (x : MomentumCircle) :
    canonicalMk (⟨0, by constructor <;> norm_num⟩, x) =
      canonicalMk (⟨1, by constructor <;> norm_num⟩, fibreNeg x) :=
  canonical_endpoint x

/-- The compact carrier's fibre flip is an involutive equivalence. -/
theorem compact_klein_fibre_flip_involutive (q : CanonicalKleinBottle) :
    canonicalFibreFlip (canonicalFibreFlip q) = q :=
  canonicalFibreFlip_involutive q

/-- The cellular rank model has Euler characteristic zero. -/
theorem klein_cellular_euler_zero :
    (Module.finrank ℝ EvenCells : ℤ) - Module.finrank ℝ OddCells = 0 :=
  cellularEulerCharacteristic_zero

/-- The deck generator reverses the orientation character. -/
theorem klein_deck_orientation_reverses :
    Matrix.det deckB_diff = (-1 : ℝ) :=
  deckB_det_neg

/-- The induced top exterior form changes sign under the deck glide. -/
theorem klein_deck_top_form_sign_change :
    glideExterior (ExteriorAlgebra.ι ℝ firstAxis *
      ExteriorAlgebra.ι ℝ secondAxis) =
        -(ExteriorAlgebra.ι ℝ firstAxis * ExteriorAlgebra.ι ℝ secondAxis) :=
  glideExterior_topForm

/-- The parity path attached to the chiral split-octonion carrier. -/
def parityPath (u v : ColorVec3 ℝ) (θ : ℝ) : SplitOctonion ℝ :=
  parityElement (Real.cos θ) (Real.sin θ) u v

/-- The glide half-period acts on the parity path by the central sign. -/
theorem parityPath_glide_equivariant (u v : ColorVec3 ℝ) (θ : ℝ) :
    parityPath u v (θ + Real.pi) =
      SplitOctonion.scale (-1) (parityPath u v θ) := by
  exact parityElement_antiperiodic θ u v

/-- The full period acts trivially on the parity path. -/
theorem parityPath_periodic (u v : ColorVec3 ℝ) (θ : ℝ) :
    parityPath u v (θ + 2 * Real.pi) = parityPath u v θ := by
  exact parityElement_period_two_pi θ u v

/-- On the unit circle, the pairing `u · v = -1` makes parity involutive. -/
theorem parityPath_involutive_of_pairing (u v : ColorVec3 ℝ)
    {c s : ℝ} (hcircle : c ^ 2 + s ^ 2 = 1)
    (hpairing : ColorVec3.dot u v = -1) :
    SplitOctonion.mul (parityElement c s u v) (parityElement c s u v) =
      SplitOctonion.one :=
  parityElement_involutive_of_unitCircle_pairing c s u v hcircle hpairing

/-- The deck presentation contains the Klein relation `bab⁻¹a = 1`. -/
theorem klein_deck_presentation_relation :
    KleinDeckGroup.mul KleinDeckGroup.b
      (KleinDeckGroup.mul KleinDeckGroup.a
        (KleinDeckGroup.mul (KleinDeckGroup.inv KleinDeckGroup.b)
          KleinDeckGroup.a)) = KleinDeckGroup.one :=
  KleinDeckGroup.relation_bab_a

end InfoGeometry.Topology.KleinBottleCanonicalBridge
end noncomputable section
