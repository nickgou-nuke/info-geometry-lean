/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.KitaevChainMajoranaZeroModes
import InfoGeometry.Canonical.CARMajoranaFiniteBridge

/-! Integration candidates importing the complete existing owners. Their
pinned Architect dependency must compile before this module can be checked. -/
namespace InfoGeometry.Canonical.CARMajoranaOwnerAdapters

open scoped BigOperators
open InfoGeometry.MajoranaPfaffianNaturalClosure
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Krein
open CARMajoranaFiniteBridge MajoranaLinearKernel KitaevChainMajoranaZeroModes

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

/-- The concrete generator is the existing finite-chain operator at two sites. -/
theorem twoSiteGenerator_eq_chain (t : ℝ) :
    twoSiteGenerator t =
      kitaevSweetSpotHamiltonian 2 (t • (1 : ChainOp)) twoSiteMajorana := by
  simp [twoSiteGenerator, kitaevSweetSpotHamiltonian, Fin.sum_univ_succ,
    Algebra.smul_mul_assoc]

/-- Both endpoints commute with the complete native finite-chain sum. -/
theorem sweetSpot_boundary_commutes {A : Type*} [Ring A] [Algebra ℝ A]
    {N : ℕ} {g : Fin (2 * N) → A}
    (hg : IsMajoranaBasis N g) (t : A) (q : Fin (2 * N))
    (hq : q.val = 0 ∨ q.val + 1 = 2 * N) (ht : Commute (g q) t) :
    g q * kitaevSweetSpotHamiltonian N t g -
      kitaevSweetSpotHamiltonian N t g * g q = 0 := by
  apply finite_bilinear_boundary_commutes hg
    (fun j : Fin (N - 1) => ⟨2 * j.val + 1, by omega⟩)
    (fun j : Fin (N - 1) => ⟨2 * j.val + 2, by omega⟩) q ?_ ?_ t ht
  all_goals
    intro j he
    have he' := congrArg Fin.val he
    rcases hq with hq | hq <;> simp only [Fin.val_mk] at he' <;> omega

end
end InfoGeometry.Canonical.CARMajoranaOwnerAdapters
