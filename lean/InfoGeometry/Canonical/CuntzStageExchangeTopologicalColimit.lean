/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CuntzStageModularFlowTopologicalColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Stagewise exchange on the native Cuntz topological colimit

The exchange maps are supplied as continuous stage maps.  The only extra
data is their compatibility with the existing Cuntz tower.  The colimit map
and its involution are then obtained from Mathlib's `TopCat` colimit API.
-/

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

abbrev system : ContinuousStarInductiveSystem Stage :=
  T.toContinuousStarInductiveSystem

def exchangeTopCatNatTrans
    (Θ : ∀ n, ContinuousMap (Stage n) (Stage n))
    (hcompat :
      ∀ {m n : ℕ} (hmn : m ≤ n) (a : Stage m),
        T.map hmn (Θ m a) = Θ n (T.map hmn a)) :
    topologicalDiagram Stage (system Stage T) ⟶
      topologicalDiagram Stage (system Stage T) where
  app n := TopCat.ofHom (Θ n)
  naturality := by
    intro m n f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    change Θ n (T.map (leOfHom f) a) = T.map (leOfHom f) (Θ m a)
    exact (hcompat (leOfHom f) a).symm

noncomputable def exchangeTopologicalColimitMap
    (Θ : ∀ n, ContinuousMap (Stage n) (Stage n))
    (hcompat :
      ∀ {m n : ℕ} (hmn : m ≤ n) (a : Stage m),
        T.map hmn (Θ m a) = Θ n (T.map hmn a)) :
    topologicalColimit Stage (system Stage T) ⟶
      topologicalColimit Stage (system Stage T) :=
  colim.map (exchangeTopCatNatTrans Stage T Θ hcompat)

@[simp] theorem exchangeTopologicalColimitMap_inclusion
    (Θ : ∀ n, ContinuousMap (Stage n) (Stage n))
    (hcompat :
      ∀ {m n : ℕ} (hmn : m ≤ n) (a : Stage m),
        T.map hmn (Θ m a) = Θ n (T.map hmn a))
    (n : ℕ) (a : Stage n) :
    exchangeTopologicalColimitMap Stage T Θ hcompat
        (topologicalInjection Stage (system Stage T) n a) =
      topologicalInjection Stage (system Stage T) n (Θ n a) := by
  have hι := colimit.ι_map (exchangeTopCatNatTrans Stage T Θ hcompat) n
  exact congrArg (fun f => f a) hι

theorem exchangeTopologicalColimitMap_involution
    (Θ : ∀ n, ContinuousMap (Stage n) (Stage n))
    (hcompat :
      ∀ {m n : ℕ} (hmn : m ≤ n) (a : Stage m),
        T.map hmn (Θ m a) = Θ n (T.map hmn a))
    (hsq : ∀ n (a : Stage n), Θ n (Θ n a) = a) :
    exchangeTopologicalColimitMap Stage T Θ hcompat ≫
        exchangeTopologicalColimitMap Stage T Θ hcompat =
      𝟙 (topologicalColimit Stage (system Stage T)) := by
  apply colimit.hom_ext
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  dsimp [topologicalDiagram] at a
  change exchangeTopologicalColimitMap Stage T Θ hcompat
      (exchangeTopologicalColimitMap Stage T Θ hcompat
        (topologicalInjection Stage (system Stage T) n a)) =
    topologicalInjection Stage (system Stage T) n a
  rw [exchangeTopologicalColimitMap_inclusion,
    exchangeTopologicalColimitMap_inclusion, hsq]

/-- Stagewise commuting continuous endomorphisms remain commuting after
descent to the native topological colimit carrier. -/
theorem exchangeTopologicalColimitMap_commutes
    (Θ Ψ : ∀ n, ContinuousMap (Stage n) (Stage n))
    (hΘ :
      ∀ {m n : ℕ} (hmn : m ≤ n) (a : Stage m),
        T.map hmn (Θ m a) = Θ n (T.map hmn a))
    (hΨ :
      ∀ {m n : ℕ} (hmn : m ≤ n) (a : Stage m),
        T.map hmn (Ψ m a) = Ψ n (T.map hmn a))
    (hcomm : ∀ (n : ℕ) (a : Stage n),
      Θ n (Ψ n a) = Ψ n (Θ n a)) :
    exchangeTopologicalColimitMap Stage T Θ hΘ ≫
        exchangeTopologicalColimitMap Stage T Ψ hΨ =
      exchangeTopologicalColimitMap Stage T Ψ hΨ ≫
        exchangeTopologicalColimitMap Stage T Θ hΘ := by
  change colim.map (exchangeTopCatNatTrans Stage T Θ hΘ) ≫
      colim.map (exchangeTopCatNatTrans Stage T Ψ hΨ) =
    colim.map (exchangeTopCatNatTrans Stage T Ψ hΨ) ≫
      colim.map (exchangeTopCatNatTrans Stage T Θ hΘ)
  rw [← colim.map_comp, ← colim.map_comp]
  congr 1
  apply NatTrans.ext
  funext n
  rw [CategoryTheory.NatTrans.comp_app, CategoryTheory.NatTrans.comp_app]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app, TopCat.comp_app]
  change Ψ n (Θ n a) = Θ n (Ψ n a)
  exact (hcomm n a).symm

def exchangeTopologicalColimitIso
    (Θ : ∀ n, ContinuousMap (Stage n) (Stage n))
    (hcompat :
      ∀ {m n : ℕ} (hmn : m ≤ n) (a : Stage m),
        T.map hmn (Θ m a) = Θ n (T.map hmn a))
    (hsq : ∀ n (a : Stage n), Θ n (Θ n a) = a) :
    topologicalColimit Stage (system Stage T) ≅
      topologicalColimit Stage (system Stage T) where
  hom := exchangeTopologicalColimitMap Stage T Θ hcompat
  inv := exchangeTopologicalColimitMap Stage T Θ hcompat
  hom_inv_id := exchangeTopologicalColimitMap_involution Stage T Θ hcompat hsq
  inv_hom_id := exchangeTopologicalColimitMap_involution Stage T Θ hcompat hsq

end InfoGeometry.Canonical.CuntzStageExchangeTopologicalColimit
