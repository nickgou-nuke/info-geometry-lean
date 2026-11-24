/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import InfoGeometry.Canonical.CStarAlgebraStateColimit
import InfoGeometry.Canonical.BostConnesKMS

/-!
# Bost--Connes generators in the native GNS representation

The Bost--Connes partition series and its zeta identification are owned by
`InfoGeometry.Arithmetic.BostConnesNativeZetaPartition`; the projection
readout and its explicit KMS closure boundary are owned by
`InfoGeometry.Canonical.BostConnesKMS`. Neither a scalar-valued function
definition nor an arbitrary cyclic module is a C*-algebraic KMS state or a
GNS construction. This file records the concrete transport that is justified:
an isometric indexed generator remains an isometry in Mathlib's GNS
representation of any supplied normalized positive state.
-/

noncomputable section

namespace InfoGeometry.Physics.BostConnesGNS

open InfoGeometry.Canonical.BostConnesKMS
open CStarStateColimit.Native

variable {Op : Type*}
variable [CStarAlgebra Op] [PartialOrder Op] [StarOrderedRing Op]

/-- The native GNS representation sends each Cuntz-indexed Bost--Connes
generator to an isometry. This uses the actual Mathlib GNS star-algebra
homomorphism, not an abstract cyclicity field. -/
theorem gns_generator_isometry
    (C : BostConnesCuntzSystem Op)
    (ω : State Op) (n : ℕ+) :
    star (ω.functional.gnsStarAlgHom (S C n)) *
        ω.functional.gnsStarAlgHom (S C n) = 1 := by
  have hgen : star (S C n) * S C n = 1 := by
    change star (C.generator n) * C.generator n = 1
    exact C.generator_isometry n
  simpa only [map_mul, map_star, map_one] using
    congrArg ω.functional.gnsStarAlgHom hgen

abbrev BostConnesAlgebra (A : Type*) [Ring A] [Algebra ℂ A] := Algebra ℂ A

/-- An algebra representation with a chosen cyclic vector. -/
structure GNSRepresentation (A H : Type*) [Ring A] [Algebra ℂ A] [AddCommGroup H] [Module ℂ H] where
  pi : A →ₐ[ℂ] (H →ₗ[ℂ] H)
  vacuum : H
  cyclic : ∀ h : H, ∃ a : A, pi a vacuum = h

/-- The declared scalar partition readout. -/
noncomputable def partitionFunction (β : ℂ) : ℂ :=
  riemannZeta β

/-- A scalar readout named by the temperature parameter. -/
noncomputable def kmsState (β : ℂ) : ℂ :=
  partitionFunction β

/-- Reference parameter used by the readout. -/
def criticalBeta : ℂ := 1

theorem cyclic_vacuum_representation_exists
    (A H : Type*) [Ring A] [Algebra ℂ A] [AddCommGroup H] [Module ℂ H]
    (rep : GNSRepresentation A H) (state_vector : H) :
    ∃ (observable : A), rep.pi observable rep.vacuum = state_vector := by
  exact rep.cyclic state_vector

/-- Evaluate an observable on the cyclic vacuum vector. -/
noncomputable def evaluateObservableVacuum
    (A H : Type*) [Ring A] [Algebra ℂ A] [AddCommGroup H] [Module ℂ H]
    (rep : GNSRepresentation A H) (obs : A) : H :=
  rep.pi obs rep.vacuum

end InfoGeometry.Physics.BostConnesGNS
