/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.BosonParityString
import InfoGeometry.Algebra.PeirceDeWittChiralSplit
import InfoGeometry.Algebra.OperatorCyclotomicParafermions
import InfoGeometry.Algebra.OperatorCyclotomicCoxeterBridge

/-! # A finite-site Jordan--Wigner to operator-cyclotomic bridge

The source carrier is the arbitrary associative ring of
`IsCommutingBosonSystem`. Its dressed annihilation and creation modes are
square-zero and have on-site anticommutator `1`. The generic Bruhat theorem
then gives a sixth-cyclotomic root. This is a conditional algebraic bridge;
it asserts no classification of parafermion or Coxeter groups.
-/

namespace InfoGeometry.Algebra.JordanWignerCyclotomicBridge

open InfoGeometry.Algebra.OperatorCyclotomicParafermions
open InfoGeometry.Algebra.IsotropicCyclotomicGalois
open InfoGeometry.Core.BosonParityString

variable {A : Type*} [Ring A] {N : ℕ}
variable {d b : Fin N → A}

/-- Total mode obtained by summing the Jordan--Wigner dressed modes over all
sites of a finite commuting hard-core system. -/
def dressedTotal (h : IsCommutingBosonSystem d b) (c : Bool) : A :=
  ∑ j : Fin N, h.dressed c j

/-- The total creation and annihilation modes of a finite Jordan--Wigner
system are square-zero. This follows from the sitewise square-zero laws and
the cross-site CAR, via the generic finite-family closure theorem. -/
theorem dressed_total_modes_square_zero
    (h : IsCommutingBosonSystem d b) :
    dressedTotal h false * dressedTotal h false = 0 ∧
    dressedTotal h true * dressedTotal h true = 0 := by
  constructor
  · unfold dressedTotal
    apply InfoGeometry.Algebra.PeirceDeWittChiralSplit.jw_finite_sum_square_zero
    · intro j hj
      exact h.dressed_sq false j
    · intro j hj k hk hne
      exact h.dressed_self_car false j k
  · unfold dressedTotal
    apply InfoGeometry.Algebra.PeirceDeWittChiralSplit.jw_finite_sum_square_zero
    · intro j hj
      exact h.dressed_sq true j
    · intro j hj k hk hne
      exact h.dressed_self_car true j k

/-- The anticommutator of the total creation and annihilation modes is the
finite sum of the on-site units. Off-site terms cancel by the Jordan--Wigner
string sign; no scalar normalization or matrix realization is imposed. -/
theorem dressed_total_mixed_anticommutator
    (h : IsCommutingBosonSystem d b) :
    dressedTotal h false * dressedTotal h true +
      dressedTotal h true * dressedTotal h false =
        ∑ j : Fin N, (1 : A) := by
  unfold dressedTotal
  rw [InfoGeometry.Algebra.PeirceDeWittChiralSplit.jw_finite_sum_metric_additive
    Finset.univ (fun j : Fin N => h.dressed false j)
    (fun j : Fin N => h.dressed true j) (by
      intro i hi j hj hne
      rw [h.dressed_mixed_car]
      simp [hne])]
  apply Finset.sum_congr rfl
  intro j hj
  simpa using h.dressed_mixed_car j j

/-- The total Jordan--Wigner pair inherits the generic off-shell Bruhat
cyclotomic identity. Its metric is the sum of the site units, so a sixth
root conclusion is stated only under the explicit unit-metric condition. -/
theorem dressed_total_bruhat_metric_law
    (h : IsCommutingBosonSystem d b) :
    cyclo6 (bruhat (dressedTotal h false) (dressedTotal h true)) =
      (1 - (dressedTotal h false * dressedTotal h true +
        dressedTotal h true * dressedTotal h false)) *
        bruhat (dressedTotal h false) (dressedTotal h true) ∧
    dressedTotal h false * dressedTotal h true +
      dressedTotal h true * dressedTotal h false =
        ∑ j : Fin N, (1 : A) ∧
    (dressedTotal h false * dressedTotal h true +
      dressedTotal h true * dressedTotal h false = 1 →
      cyclo6 (bruhat (dressedTotal h false) (dressedTotal h true)) = 0 ∧
      bruhat (dressedTotal h false) (dressedTotal h true) ^ 6 = 1) := by
  let u := dressedTotal h false
  let v := dressedTotal h true
  have hu : u * u = 0 := (dressed_total_modes_square_zero h).1
  have hv : v * v = 0 := (dressed_total_modes_square_zero h).2
  have hmetric : u * v + v * u = ∑ j : Fin N, (1 : A) := by
    simpa [u, v] using dressed_total_mixed_anticommutator h
  have hcyclo := (bruhat_cyclotomic_characteristic u v hu hv).2.2.2.2.2.1
  refine ⟨?_, hmetric, ?_⟩
  · simpa [u, v, anticommutator] using hcyclo
  · intro hunit
    have hunit' : anticommutator u v = 1 := by
      simpa [u, v, anticommutator] using hunit
    have hroot : cyclo6 (bruhat u v) = 0 := by
      have hspec := (bruhat_metric_cyclotomic_specializations u v hu hv).1
      exact (hspec hunit').1
    constructor
    · simpa [u, v] using hroot
    · obtain ⟨_, _, hpow⟩ :=
        (bruhat_metric_cyclotomic_specializations u v hu hv).1 hunit'
      have hsix : (bruhat u v) ^ 6 = 1 := by
        calc
          (bruhat u v) ^ 6 =
              bruhat u v * bruhat u v * bruhat u v * bruhat u v *
                bruhat u v * bruhat u v := by noncomm_ring
          _ = 1 := hpow
      simpa [u, v] using hsix

/-- Under the explicit unit-metric condition, the total Jordan--Wigner
creation/annihilation pair induces the checked `G₂ = I₂(6)` representation.
The condition is retained because the total metric is generally the sum of
all site units, not automatically a single unit. -/
noncomputable def dressedTotalG2Rep
    (h : IsCommutingBosonSystem d b)
    (hmetric : dressedTotal h false * dressedTotal h true +
      dressedTotal h true * dressedTotal h false = 1) :
    (CoxeterMatrix.G₂).Group →* Equiv.Perm (A × A) := by
  let u := dressedTotal h false
  let v := dressedTotal h true
  have hu : u * u = 0 := (dressed_total_modes_square_zero h).1
  have hv : v * v = 0 := (dressed_total_modes_square_zero h).2
  have huv : anticommutator u v = 1 := by
    simpa [u, v, anticommutator] using hmetric
  have hsix := bruhatUnit_sixth_power_on_shell u v hu hv huv |>.1
  exact OperatorCyclotomicCoxeterBridge.g2BlockOperatorRep
    (bruhatUnit u v hu hv) hsix

/-- At each site of a commuting hard-core system, the ordered product of the
Jordan--Wigner dressed annihilation and creation modes is an exact
sixth-cyclotomic root. The inverse is the reversed Bruhat product, and the
cube of the root is `-1`. -/
theorem dressed_site_bruhat_sixth_root
    (h : IsCommutingBosonSystem d b) (j : Fin N) :
    bruhat (h.dressed false j) (h.dressed true j) *
        bruhatInv (h.dressed false j) (h.dressed true j) = 1 ∧
    cyclo6 (bruhat (h.dressed false j) (h.dressed true j)) = 0 ∧
    bruhat (h.dressed false j) (h.dressed true j) *
      bruhat (h.dressed false j) (h.dressed true j) *
      bruhat (h.dressed false j) (h.dressed true j) = -1 := by
  let u := h.dressed false j
  let v := h.dressed true j
  have hu : u * u = 0 := by exact h.dressed_sq false j
  have hv : v * v = 0 := by exact h.dressed_sq true j
  have huv : anticommutator u v = 1 := by
    simpa [u, v, anticommutator] using h.dressed_mixed_car j j
  obtain ⟨hinv, _, _, _, _, hcyclo6, _, _⟩ :=
    bruhat_cyclotomic_characteristic u v hu hv
  have hroot : cyclo6 (bruhat u v) = 0 := by
    rw [hcyclo6, huv]
    noncomm_ring
  refine ⟨hinv, hroot, ?_⟩
  exact cyclo6_root_cube_eq_neg_one (bruhat u v) hroot

/-- The same on-site Jordan--Wigner CAR pair gives the existing genuine
`G₂ = I₂(6)` Coxeter representation on the doubled operator carrier. The
representation is obtained through the checked Coxeter lift, not inferred
from a sixth-root equation alone. -/
noncomputable def dressedSiteG2Rep
    (h : IsCommutingBosonSystem d b) (j : Fin N) :
    (CoxeterMatrix.G₂).Group →* Equiv.Perm (A × A) := by
  let u := h.dressed false j
  let v := h.dressed true j
  have hu : u * u = 0 := by exact h.dressed_sq false j
  have hv : v * v = 0 := by exact h.dressed_sq true j
  have huv : anticommutator u v = 1 := by
    simpa [u, v, anticommutator] using h.dressed_mixed_car j j
  have hsix := bruhatUnit_sixth_power_on_shell u v hu hv huv |>.1
  exact OperatorCyclotomicCoxeterBridge.g2BlockOperatorRep
    (bruhatUnit u v hu hv) hsix

@[simp] theorem dressedSiteG2Rep_apply_simple_zero
    (h : IsCommutingBosonSystem d b) (j : Fin N) :
    dressedSiteG2Rep h j ((CoxeterMatrix.G₂).simple 0) =
      OperatorCyclotomicCoxeterBridge.blockSwap := by
  unfold dressedSiteG2Rep
  simp

@[simp] theorem dressedSiteG2Rep_apply_simple_one
    (h : IsCommutingBosonSystem d b) (j : Fin N) :
    dressedSiteG2Rep h j ((CoxeterMatrix.G₂).simple 1) =
      OperatorCyclotomicCoxeterBridge.blockTwistedReflection
        (bruhatUnit (h.dressed false j) (h.dressed true j)
          (h.dressed_sq false j) (h.dressed_sq true j)) := by
  unfold dressedSiteG2Rep
  simp

/-- The product of the two represented Coxeter generators is the concrete
block rotation associated to the reversed Bruhat unit. -/
theorem dressedSiteG2Rep_simple_product
    (h : IsCommutingBosonSystem d b) (j : Fin N) :
    dressedSiteG2Rep h j
        ((CoxeterMatrix.G₂).simple 0 * (CoxeterMatrix.G₂).simple 1) =
      OperatorCyclotomicCoxeterBridge.blockRotation
        (bruhatUnit (h.dressed false j) (h.dressed true j)
          (h.dressed_sq false j) (h.dressed_sq true j))⁻¹ := by
  let u := h.dressed false j
  let v := h.dressed true j
  have hu : u * u = 0 := by exact h.dressed_sq false j
  have hv : v * v = 0 := by exact h.dressed_sq true j
  have huv : anticommutator u v = 1 := by
    simpa [u, v, anticommutator] using h.dressed_mixed_car j j
  have hsix := bruhatUnit_sixth_power_on_shell u v hu hv huv |>.1
  simpa [dressedSiteG2Rep, u, v] using
    (OperatorCyclotomicCoxeterBridge.g2BlockOperatorRep_simple_product
      (bruhatUnit u v hu hv) hsix)

theorem dressed_site_g2_coxeter_representation
    (h : IsCommutingBosonSystem d b) (j : Fin N) :
    Nonempty ((CoxeterMatrix.G₂).Group →* Equiv.Perm (A × A)) := by
  exact ⟨dressedSiteG2Rep h j⟩

end InfoGeometry.Algebra.JordanWignerCyclotomicBridge
