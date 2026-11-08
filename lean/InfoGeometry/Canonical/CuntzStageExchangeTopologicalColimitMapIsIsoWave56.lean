/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CuntzStageExchangeTopologicalColimit

noncomputable section

namespace InfoGeometry.Canonical.CuntzStageExchangeTopologicalColimit

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzStageModularFlowTopologicalColimit
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
open FilteredColimit.Native.Topological

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

theorem exchangeTopologicalColimitMap_isIso
    (Θ : ∀ n, ContinuousMap (Stage n) (Stage n))
    (hcompat :
      ∀ {m n : ℕ} (hmn : m ≤ n) (a : Stage m),
        T.map hmn (Θ m a) = Θ n (T.map hmn a))
    (hsq : ∀ n (a : Stage n), Θ n (Θ n a) = a) :
    IsIso (exchangeTopologicalColimitMap Stage T Θ hcompat) := by
  exact (exchangeTopologicalColimitIso Stage T Θ hcompat hsq).isIso_hom

end InfoGeometry.Canonical.CuntzStageExchangeTopologicalColimit
