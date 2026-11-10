/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.InfiniteCARColimit
import InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import InfoGeometry.Clifford.Cl11ColimitDimension

set_option autoImplicit false

/-!
# Countably many CAR generators in the algebraic Clifford tensor colimit

The finite head is only the stage needed to represent a chosen finite set of
modes. The coefficient carrier is the actual algebraic direct limit of the
full matrix stages; it is not assigned a fixed matrix dimension. This module
constructs the repository's abstract countable CAR interface from the
Jordan--Wigner operators and records that the carrier is infinite-dimensional.
No C*-completion or analytic Fock representation is asserted.

## BUCKET 1: Proved
The algebraic direct-limit CAR relations, mode separation, and linear
independence statements are proved from the finite-head Jordan--Wigner laws.

## BUCKET 2: Conditional
No conditional results are introduced in this module.

## BUCKET 3: Open boundary
No C*-completion, analytic Fock representation, or infinite CAR series is
constructed here.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11TensorTowerInfiniteCAR

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11JordanWignerCARBridge
open InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit
open InfoGeometry.Canonical.InfiniteCARColimit

abbrev OperatorColimit : Type :=
  InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

/-- The countable creation mode `i` represented at the head ending in site `i`.
The mode is an element of the infinite algebraic colimit, not of a fixed head. -/
def creationMode (i : ℕ) : OperatorColimit := uImage (Fin.last i)

/-- The countable annihilation mode `i` represented at the head ending in site
`i`. The mode is an element of the infinite algebraic colimit. -/
def annihilationMode (i : ℕ) : OperatorColimit := vImage (Fin.last i)

/-- Read a finite-site mode at every later head by casting its site index. -/
theorem uImage_castLE {n m : ℕ} (h : n ≤ m) (k : Fin n) :
    ofStage m (u m (Fin.castLE h k)) = uImage k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => rfl
  | succ d ih =>
      calc
        ofStage (n + Nat.succ d)
            (u (n + Nat.succ d) (Fin.castLE (Nat.le_add_right n (Nat.succ d)) k)) =
            ofStage ((n + d) + 1)
              (matStageEmbed (n + d)
                (u (n + d) (Fin.castLE (Nat.le_add_right n d) k))) := by
                  simp only [matStageEmbed_u]
                  congr 2
        _ = ofStage (n + d) (u (n + d) (Fin.castLE (Nat.le_add_right n d) k)) :=
          ofStage_apply_bond (n + d)
            (u (n + d) (Fin.castLE (Nat.le_add_right n d) k))
        _ = uImage k := ih (Nat.le_add_right n d)

/-- The analogous later-head readout for annihilation modes. -/
theorem vImage_castLE {n m : ℕ} (h : n ≤ m) (k : Fin n) :
    ofStage m (v m (Fin.castLE h k)) = vImage k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => rfl
  | succ d ih =>
      calc
        ofStage (n + Nat.succ d)
            (v (n + Nat.succ d) (Fin.castLE (Nat.le_add_right n (Nat.succ d)) k)) =
            ofStage ((n + d) + 1)
              (matStageEmbed (n + d)
                (v (n + d) (Fin.castLE (Nat.le_add_right n d) k))) := by
                  simp only [matStageEmbed_v]
                  congr 2
        _ = ofStage (n + d) (v (n + d) (Fin.castLE (Nat.le_add_right n d) k)) :=
          ofStage_apply_bond (n + d)
            (v (n + d) (Fin.castLE (Nat.le_add_right n d) k))
        _ = vImage k := ih (Nat.le_add_right n d)

/-- Pair two modes at the common head `max i j + 1`, transporting both through
the actual direct-limit bonding maps. -/
private theorem siteAtCommonHead (i j : ℕ) :
    ∃ N : ℕ, ∃ hi : i < N, ∃ hj : j < N,
      ofStage N (u N ⟨i, hi⟩) = creationMode i ∧
      ofStage N (v N ⟨i, hi⟩) = annihilationMode i ∧
      ofStage N (u N ⟨j, hj⟩) = creationMode j ∧
      ofStage N (v N ⟨j, hj⟩) = annihilationMode j := by
  let N := max i j + 1
  have hi : i < N := Nat.lt_succ_of_le (Nat.le_max_left i j)
  have hj : j < N := Nat.lt_succ_of_le (Nat.le_max_right i j)
  have hiLE : i + 1 ≤ N := Nat.succ_le_succ (Nat.le_max_left i j)
  have hjLE : j + 1 ≤ N := Nat.succ_le_succ (Nat.le_max_right i j)
  have hUi := uImage_castLE hiLE (Fin.last i)
  have hVi := vImage_castLE hiLE (Fin.last i)
  have hUj := uImage_castLE hjLE (Fin.last j)
  have hVj := vImage_castLE hjLE (Fin.last j)
  have hiIndex : Fin.castLE hiLE (Fin.last i) = ⟨i, hi⟩ := by
    apply Fin.ext
    rfl
  have hjIndex : Fin.castLE hjLE (Fin.last j) = ⟨j, hj⟩ := by
    apply Fin.ext
    rfl
  refine ⟨N, hi, hj, ?_, ?_, ?_, ?_⟩
  · simpa [creationMode, u, hiIndex] using hUi
  · simpa [annihilationMode, v, hiIndex] using hVi
  · simpa [creationMode, u, hjIndex] using hUj
  · simpa [annihilationMode, v, hjIndex] using hVj

/-- Countable creation modes anticommute in the operator colimit. -/
theorem creationMode_anticomm (i j : ℕ) :
    creationMode i * creationMode j + creationMode j * creationMode i = 0 := by
  obtain ⟨N, hi, hj, hUi, _, hUj, _⟩ := siteAtCommonHead i j
  rw [← hUi, ← hUj]
  rw [← (ofStage N).map_mul, ← (ofStage N).map_mul, ← (ofStage N).map_add]
  by_cases hij : i = j
  · subst j
    have hsq := jwCreation_sq N ⟨i, hi⟩
    rw [hsq]
    simp
  · have hne : (⟨i, hi⟩ : Fin N) ≠ ⟨j, hj⟩ := by
      intro h
      apply hij
      exact congrArg Fin.val h
    simpa [u, v] using congrArg (ofStage N)
      (InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.creation_cross_site_anticommute
        N ⟨i, hi⟩ ⟨j, hj⟩ hne)

/-- Countable annihilation modes anticommute in the operator colimit. -/
theorem annihilationMode_anticomm (i j : ℕ) :
    annihilationMode i * annihilationMode j +
      annihilationMode j * annihilationMode i = 0 := by
  obtain ⟨N, hi, hj, _, hVi, _, hVj⟩ := siteAtCommonHead i j
  rw [← hVi, ← hVj]
  rw [← (ofStage N).map_mul, ← (ofStage N).map_mul, ← (ofStage N).map_add]
  by_cases hij : i = j
  · subst j
    have hsq := jwAnnihilation_sq N ⟨i, hi⟩
    rw [hsq]
    simp
  · have hne : (⟨i, hi⟩ : Fin N) ≠ ⟨j, hj⟩ := by
      intro h
      apply hij
      exact congrArg Fin.val h
    simpa [u, v] using congrArg (ofStage N)
      (InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.annihilation_cross_site_anticommute
        N ⟨i, hi⟩ ⟨j, hj⟩ hne)

/-- Creation and annihilation modes satisfy the full Kronecker-delta CAR law
in the algebraic operator colimit. -/
theorem creationMode_annihilationMode_CAR (i j : ℕ) :
    creationMode i * annihilationMode j +
      annihilationMode j * creationMode i = if i = j then 1 else 0 := by
  obtain ⟨N, hi, hj, hUi, _, _, hVj⟩ := siteAtCommonHead i j
  rw [← hUi, ← hVj]
  rw [← (ofStage N).map_mul, ← (ofStage N).map_mul, ← (ofStage N).map_add]
  have hfinite :
      jwCreation N ⟨i, hi⟩ * jwAnnihilation N ⟨j, hj⟩ +
        jwAnnihilation N ⟨j, hj⟩ * jwCreation N ⟨i, hi⟩ =
          if i = j then 1 else 0 := by
    by_cases hij : (⟨i, hi⟩ : Fin N) = ⟨j, hj⟩
    · have hval : i = j := congrArg Fin.val hij
      subst j
      simpa [add_comm] using jwAnnihilation_creation_anticommutator N
        ⟨i, hi⟩ ⟨i, hj⟩
    · have hval : i ≠ j := by
        intro heq
        apply hij
        exact Fin.ext heq
      have hne : (⟨i, hi⟩ : Fin N) ≠ ⟨j, hj⟩ := by
        intro h
        apply hval
        exact congrArg Fin.val h
      simpa [hval] using
        (InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.creation_annihilation_cross_site_anticommute
          N ⟨i, hi⟩ ⟨j, hj⟩ hne)
  rw [hfinite]
  by_cases hij : i = j <;> simp [hij]

/-- The algebraic `Cl(1,1)` tensor colimit carries a concrete countable CAR
family. -/
def countableCAR : CARAlgebra OperatorColimit where
  u := creationMode
  v := annihilationMode
  anticomm_uv := creationMode_annihilationMode_CAR
  anticomm_uu := creationMode_anticomm
  anticomm_vv := annihilationMode_anticomm

/-- Distinct natural-number modes remain distinct elements of the operator
colimit. The proof extracts the diagonal CAR relation and contradicts the
off-diagonal one, so it records information beyond the defining CAR fields. -/
theorem countableCAR_modes_separate_indices :
    Function.Injective creationMode ∧ Function.Injective annihilationMode := by
  constructor
  · intro i j hij
    by_contra hne
    have hdiag := creationMode_annihilationMode_CAR i i
    have hoff := creationMode_annihilationMode_CAR j i
    have hzero : (1 : OperatorColimit) = 0 := by
      calc
        1 = creationMode i * annihilationMode i +
            annihilationMode i * creationMode i := by simpa using hdiag.symm
        _ = creationMode j * annihilationMode i +
            annihilationMode i * creationMode j := by rw [hij]
        _ = 0 := by simpa [Ne.symm hne] using hoff
    exact one_ne_zero hzero
  · intro i j hij
    by_contra hne
    have hdiag := creationMode_annihilationMode_CAR i i
    have hoff := creationMode_annihilationMode_CAR i j
    have hzero : (1 : OperatorColimit) = 0 := by
      calc
        1 = creationMode i * annihilationMode i +
            annihilationMode i * creationMode i := by simpa using hdiag.symm
        _ = creationMode i * annihilationMode j +
            annihilationMode j * creationMode i := by rw [hij]
        _ = 0 := by simpa [hne] using hoff
    exact one_ne_zero hzero

/-- The countable creation operators are linearly independent over `ℝ` in
the actual algebraic operator colimit.  For a finite linear relation, taking
the anticommutator with the matching annihilation mode extracts its coefficient
times the unit; the Kronecker-delta CAR law makes all other terms vanish. -/
theorem creationMode_linearIndependent :
    LinearIndependent ℝ creationMode := by
  rw [linearIndependent_iff']
  intro s g hsum i his
  have hpairing :
      (∑ j ∈ s, g j •
        (creationMode j * annihilationMode i + annihilationMode i * creationMode j)) = 0 := by
    calc
      _ = (∑ j ∈ s, g j • creationMode j) * annihilationMode i +
          annihilationMode i * (∑ j ∈ s, g j • creationMode j) := by
            simp only [Finset.sum_add_distrib, smul_add]
            rw [Finset.sum_mul, Finset.mul_sum]
            simp only [smul_mul_assoc, mul_smul_comm]
      _ = 0 := by rw [hsum]; simp
  have hcoeff : (∑ j ∈ s, g j •
      (if j = i then (1 : OperatorColimit) else 0)) = 0 := by
    simpa only [creationMode_annihilationMode_CAR] using hpairing
  have hcollapse :
      (∑ j ∈ s, g j • (if j = i then (1 : OperatorColimit) else 0)) =
        g i • (1 : OperatorColimit) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [hji]
    · intro hi
      exact (hi his).elim
  rw [hcollapse] at hcoeff
  exact (smul_eq_zero.mp hcoeff).resolve_right one_ne_zero

end InfoGeometry.Clifford.Cl11TensorTowerInfiniteCAR

end
