import InfoGeometry.Clifford.SplitQ11PhaseFlip
import InfoGeometry.Canonical.TopologicalResidue
import InfoGeometry.Quantum.SuperchargeMultiplet
import InfoGeometry.KK.QuasilatticeIndexInvariance
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.TopologicalInvariantInvariance

Canonical invariance/coherence surface for currently-owned topological quantities.

This file is intentionally a transport layer:
- it does not create new index owners;
- it records the split `Cl(1,1)` phase-flip invariants already proved at the
  Clifford owner level;
- it re-exports the operatorial KK analytical-index invariance already proved
  for quasilattice transport.
-/

namespace InfoGeometry.Canonical.TopologicalInvariantInvariance

section SplitQ11

open InfoGeometry.Clifford.SplitQ11PhaseFlip

/-- The split-null CAR relation is invariant under the canonical phase flip. -/
@[rep_depth transport]
theorem nullCAR_phaseFlip_invariant :
    (phaseFlipAlg nullMinus) * (phaseFlipAlg nullPlus)
      + (phaseFlipAlg nullPlus) * (phaseFlipAlg nullMinus) = 1 := by
  calc
    (phaseFlipAlg nullMinus) * (phaseFlipAlg nullPlus)
        + (phaseFlipAlg nullPlus) * (phaseFlipAlg nullMinus)
      = nullPlus * nullMinus + nullMinus * nullPlus := by
          rw [phaseFlip_apply_nullMinus, phaseFlip_apply_nullPlus]
    _ = 1 := by
          simpa [add_comm] using nullMinus_mul_nullPlus_add_swap

/-- Null nilpotency is preserved by the canonical phase flip. -/
@[rep_depth transport]
theorem nullMinus_sq_phaseFlip_invariant :
    (phaseFlipAlg nullMinus) * (phaseFlipAlg nullMinus) = 0 := by
  calc
    (phaseFlipAlg nullMinus) * (phaseFlipAlg nullMinus)
      = nullPlus * nullPlus := by rw [phaseFlip_apply_nullMinus]
    _ = 0 := by simpa using nullPlus_sq

/-- Null nilpotency is preserved by the canonical phase flip. -/
@[rep_depth transport]
theorem nullPlus_sq_phaseFlip_invariant :
    (phaseFlipAlg nullPlus) * (phaseFlipAlg nullPlus) = 0 := by
  calc
    (phaseFlipAlg nullPlus) * (phaseFlipAlg nullPlus)
      = nullMinus * nullMinus := by rw [phaseFlip_apply_nullPlus]
    _ = 0 := by simpa using nullMinus_sq

end SplitQ11

section DoubledCarrier

open InfoGeometry.Canonical.TopologicalResidue
open InfoGeometry.Quantum

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/--
On the canonical doubled carrier, the modular residue vanishes for the
canonical supercharge multiplet.
-/
@[rep_depth transport]
theorem canonical_wittenIndexResidue_eq_zero :
    wittenIndexResidue (E := E)
      (Quantum.canonicalSuperchargeMultiplet.inst (E := E)) = 0 := by
  simpa using
    (wittenIndexResidue_eq_zero (E := E)
      (Quantum.canonicalSuperchargeMultiplet.inst (E := E)))

end DoubledCarrier

section KK

open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Krein

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/--
Operatorial quasilattice transport preserves the Fredholm/chiral analytical
index between any two time slices.
-/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_transport_invariant
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (s t : ℝ) :
    quasilatticeAnalyticalIndex V X s
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven s)
      =
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) := by
  simpa using quasilatticeAnalyticalIndex_eq (E := E) V X hX hEven s t

end KK

end InfoGeometry.Canonical.TopologicalInvariantInvariance
