/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.KitaevChainMajoranaZeroModes
import InfoGeometry.Canonical.CARMajoranaFiniteBridge

/-! Coordinate adapters to the doubled-real CAR owner and finite-chain endpoints. -/
namespace InfoGeometry.Canonical.CARMajoranaOwnerAdapters

open scoped BigOperators
open InfoGeometry.MajoranaPfaffianNaturalClosure
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Krein
open CARMajoranaFiniteBridge KitaevChainMajoranaZeroModes

noncomputable section

/-- Coordinate map on the actual doubled-real carrier. -/
def doubledCoordinates (v : DoubledSpace ℝ) : Fin 2 → ℝ :=
  ![WithLp.fst v, WithLp.snd v]

theorem creation_coordinates (x y : ℝ) :
    doubledCoordinates (concreteCARCreation (E := ℝ) (to_doubled x y)) =
      annihilationR.mulVec ![x, y] := by
  funext i
  fin_cases i <;>
    simp [doubledCoordinates, concreteCARCreation,
      cliffordConcreteCreation_apply_to_doubled, to_doubled,
      annihilationR, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem annihilation_coordinates (x y : ℝ) :
    doubledCoordinates (concreteCARAnnihilation (E := ℝ) (to_doubled x y)) =
      creationR.mulVec ![x, y] := by
  funext i
  fin_cases i <;>
    simp [doubledCoordinates, concreteCARAnnihilation,
      cliffordConcreteAnnihilation_apply_to_doubled, to_doubled,
      creationR, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Definitional adapter to the existing normalized CAR predicate. -/
theorem twoSiteMajorana_isMajoranaBasis : IsMajoranaBasis 2 twoSiteMajorana :=
  twoSiteMajorana_car

/-- Both endpoints commute with the complete native finite-chain sum. -/
theorem sweetSpot_boundary_commutes {A : Type*} [Ring A]
    {N : ℕ} {g : Fin (2 * N) → A}
    (hg : IsMajoranaBasis N g) (t : A) (q : Fin (2 * N))
    (hq : q.val = 0 ∨ q.val + 1 = 2 * N) (ht : Commute (g q) t) :
    g q * kitaevSweetSpotHamiltonian N t g -
      kitaevSweetSpotHamiltonian N t g * g q = 0 := by
  apply sub_eq_zero.mpr
  change Commute (g q) (kitaevSweetSpotHamiltonian N t g)
  unfold kitaevSweetSpotHamiltonian
  apply Commute.sum_right
  intro j _
  apply ht.mul_right
  apply sub_eq_zero.mp
  apply left_boundary_majorana_zero_mode
  · have hne : q ≠ (⟨2 * j.val + 1, by omega⟩ : Fin (2 * N)) := by
      intro he
      have hv := congrArg Fin.val he
      rcases hq with hq | hq <;> omega
    simpa [hne] using hg q ⟨2 * j.val + 1, by omega⟩
  · have hne : q ≠ (⟨2 * j.val + 2, by omega⟩ : Fin (2 * N)) := by
      intro he
      have hv := congrArg Fin.val he
      rcases hq with hq | hq <;> omega
    simpa [hne] using hg q ⟨2 * j.val + 2, by omega⟩

end
end InfoGeometry.Canonical.CARMajoranaOwnerAdapters
