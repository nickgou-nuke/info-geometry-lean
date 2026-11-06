/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CyclicIntertwiner
import InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum

/-!
# Uniqueness of bounded intertwiners from the completed GNS representation

The native Mathlib GNS Hilbert completion supplies the source carrier. Its
vacuum orbit is already proved dense by `PositiveLinearMapGNSVacuum`; hence
cyclicity is discharged here, rather than assumed for this specialization.
The positive functional need not be faithful or normalized.

This is an operator uniqueness theorem, not an existence theorem for a
bounded intertwiner or an identification of GNS with a conformal-net vacuum.
-/

namespace InfoGeometry.OperatorAlgebra.GNSCyclicIntertwiner

open PositiveLinearMapGNSVacuum
open scoped ComplexOrder

variable {A F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A bounded intertwiner out of a completed GNS representation is
determined by its value on the actual GNS vacuum `Λ(1)`. -/
theorem eq_of_eval_vacuum_eq (φ : A →ₚ[ℂ] ℂ)
    {B : A → F →L[ℂ] F} {T S : φ.GNS →L[ℂ] F}
    (hT : ∀ a, T.comp (φ.gnsStarAlgHom a) = (B a).comp T)
    (hS : ∀ a, S.comp (φ.gnsStarAlgHom a) = (B a).comp S)
    (hEval : T (gnsVacuum φ) = S (gnsVacuum φ)) : T = S := by
  have hOrbit : DenseRange (fun a : A => φ.gnsStarAlgHom a (gnsVacuum φ)) := by
    simpa only [← gnsOrbitMap_eq_gnsRepresentation] using gnsOrbitMap_denseRange φ
  exact CyclicIntertwiner.eq_of_eval_eq
    (Dense.mono Submodule.subset_span hOrbit) hT hS hEval

end InfoGeometry.OperatorAlgebra.GNSCyclicIntertwiner
