/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import InfoGeometry.OperatorAlgebra.PeirceDissipatorTrinity

/-!
# Lie--Jordan and Peirce transport into the native full-matrix inductive limit

The carrier and bonding maps are owned by `Cl11TensorTowerLimit`. These laws
commute with those actual ring homomorphisms. No topological completion,
state-dependent metric, or analytic continuation is asserted here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.LieJordanPeirceColimit

open LieJordanDuality PeirceLieJordanResolution
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

open InfoGeometry.OperatorAlgebra.PeirceDissipatorTrinity
open InfoGeometry.Clifford.Cl11JordanWignerCARBridge

/-- The stage-one Cl(1,1) creation operator, a concrete matrix operator. -/
def wittCreation : Stage 1 := jwCreation 1 0

/-- The stage-one Cl(1,1) annihilation operator, a concrete matrix operator. -/
def wittAnnihilation : Stage 1 := jwAnnihilation 1 0

/-- The native creation and annihilation operators form a reflexive
square-zero pair and do not commute. This rules out a scalar or diagonal
surrogate for the concrete witness. -/
theorem witt_pair_noncommutative_reflexive :
    wittCreation * wittCreation = 0 ∧
    wittAnnihilation * wittAnnihilation = 0 ∧
    wittCreation * wittAnnihilation * wittCreation = wittCreation ∧
    wittAnnihilation * wittCreation * wittAnnihilation = wittAnnihilation ∧
    wittCreation * wittAnnihilation ≠ wittAnnihilation * wittCreation := by
  have hu : wittCreation * wittCreation = 0 := by
    simpa [wittCreation] using jwCreation_last_sq 0
  have hv : wittAnnihilation * wittAnnihilation = 0 := by
    simpa [wittAnnihilation] using jwAnnihilation_last_sq 0
  have hcar : wittAnnihilation * wittCreation +
      wittCreation * wittAnnihilation = 1 := by
    simpa [wittAnnihilation, wittCreation] using
      jwAnnihilation_creation_anticommutator 1 0 0
  have huv : wittCreation * wittAnnihilation * wittCreation = wittCreation := by
    calc
      wittCreation * wittAnnihilation * wittCreation =
          wittCreation * (wittAnnihilation * wittCreation +
            wittCreation * wittAnnihilation) := by
              have hzero : wittCreation * (wittCreation * wittAnnihilation) = 0 := by
                rw [← mul_assoc, hu, zero_mul]
              calc
                _ = wittCreation * (wittAnnihilation * wittCreation) := by
                  simp [mul_assoc]
                _ = wittCreation * (wittAnnihilation * wittCreation) +
                    wittCreation * (wittCreation * wittAnnihilation) := by
                  rw [hzero]
                  simp
                _ = _ := by rw [mul_add]
      _ = wittCreation * 1 := by rw [hcar]
      _ = wittCreation := by simp
  have hvu : wittAnnihilation * wittCreation * wittAnnihilation =
      wittAnnihilation := by
    calc
      wittAnnihilation * wittCreation * wittAnnihilation =
          (wittAnnihilation * wittCreation +
            wittCreation * wittAnnihilation) * wittAnnihilation := by
              have hzero : (wittCreation * wittAnnihilation) * wittAnnihilation = 0 := by
                rw [mul_assoc, hv, mul_zero]
              calc
                _ = (wittAnnihilation * wittCreation) * wittAnnihilation := by
                  simp [mul_assoc]
                _ = (wittAnnihilation * wittCreation) * wittAnnihilation +
                    (wittCreation * wittAnnihilation) * wittAnnihilation := by
                  rw [hzero]
                  simp
                _ = _ := by rw [add_mul]
      _ = 1 * wittAnnihilation := by rw [hcar]
      _ = wittAnnihilation := by simp
  have hne : wittCreation * wittAnnihilation ≠
      wittAnnihilation * wittCreation := by
    intro hcomm
    have hu0 : wittCreation = 0 := by
      calc
        wittCreation = wittCreation * wittAnnihilation * wittCreation := huv.symm
        _ = wittCreation * (wittAnnihilation * wittCreation) := by rw [mul_assoc]
        _ = wittCreation * (wittCreation * wittAnnihilation) := by rw [hcomm.symm]
        _ = (wittCreation * wittCreation) * wittAnnihilation := by rw [← mul_assoc]
        _ = 0 := by rw [hu, zero_mul]
    rw [hu0] at hcar
    simp at hcar
  exact ⟨hu, hv, huv, hvu, hne⟩

/-- A reflexive square-zero pair at any native full-matrix stage retains its
Dirac support and involution identities in the actual Cl(1,1) tensor-tower
direct limit. -/
theorem stage_reflexive_dirac_support_in_limit (n : ℕ) (u v : Stage n)
    (hu : u * u = 0) (hv : v * v = 0)
    (huv : u * v * u = u) (hvu : v * u * v = v) :
    (ofStage n u + ofStage n v) * (ofStage n u + ofStage n v) =
      ofStage n u * ofStage n v + ofStage n v * ofStage n u ∧
    (ofStage n u + ofStage n v) *
        (ofStage n u * ofStage n v + ofStage n v * ofStage n u) =
      ofStage n u + ofStage n v ∧
    (ofStage n u * ofStage n v + ofStage n v * ofStage n u) *
        (ofStage n u + ofStage n v) = ofStage n u + ofStage n v ∧
    ((1 - (ofStage n u * ofStage n v + ofStage n v * ofStage n u)) +
      (ofStage n u + ofStage n v)) *
      ((1 - (ofStage n u * ofStage n v + ofStage n v * ofStage n u)) +
        (ofStage n u + ofStage n v)) = 1 := by
  exact ringHom_preserves_reflexive_pair_dirac_support
    (ofStage n) u v hu hv huv hvu

/-- The concrete Cl(1,1) Witt creation and annihilation operators satisfy the
Dirac support and global involution identities in the native tensor-tower
direct limit. -/
theorem native_witt_dirac_support_in_limit :
    (ofStage 1 wittCreation + ofStage 1 wittAnnihilation) *
        (ofStage 1 wittCreation + ofStage 1 wittAnnihilation) =
      ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation ∧
    (ofStage 1 wittCreation + ofStage 1 wittAnnihilation) *
        (ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
          ofStage 1 wittAnnihilation * ofStage 1 wittCreation) =
      ofStage 1 wittCreation + ofStage 1 wittAnnihilation ∧
    ((1 - (ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation)) +
      (ofStage 1 wittCreation + ofStage 1 wittAnnihilation)) *
      ((1 - (ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation)) +
        (ofStage 1 wittCreation + ofStage 1 wittAnnihilation)) = 1 := by
  rcases witt_pair_noncommutative_reflexive with ⟨hu, hv, huv, hvu, _⟩
  rcases stage_reflexive_dirac_support_in_limit 1 wittCreation wittAnnihilation
      hu hv huv hvu with ⟨hDiracSq, hLeft, _hRight, hInvolution⟩
  exact ⟨hDiracSq, hLeft, hInvolution⟩

/-- The concrete noncommuting Witt operators carry the reflexive-pair
`sl₂` Casimir identity in the native Cl(1,1) direct limit. -/
theorem native_witt_sl2_casimir_in_limit :
    ((ofStage 1 wittCreation * ofStage 1 wittAnnihilation -
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation) *
      (ofStage 1 wittCreation * ofStage 1 wittAnnihilation -
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation)) +
      (2 : ℕ) • (ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation) =
      (3 : ℕ) • (ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation) := by
  rcases witt_pair_noncommutative_reflexive with ⟨hu₀, hv₀, huv₀, hvu₀, _⟩
  have hu : ofStage 1 wittCreation * ofStage 1 wittCreation = 0 := by
    rw [← map_mul, hu₀, map_zero]
  have hv : ofStage 1 wittAnnihilation * ofStage 1 wittAnnihilation = 0 := by
    rw [← map_mul, hv₀, map_zero]
  have huv : ofStage 1 wittCreation * ofStage 1 wittAnnihilation *
      ofStage 1 wittCreation = ofStage 1 wittCreation := by
    rw [← map_mul, ← map_mul, huv₀]
  have hvu : ofStage 1 wittAnnihilation * ofStage 1 wittCreation *
      ofStage 1 wittAnnihilation = ofStage 1 wittAnnihilation := by
    rw [← map_mul, ← map_mul, hvu₀]
  exact reflexive_pair_casimir hu hv huv hvu

/-- The shifted Dirac product factors through the native Witt mass support in
the Cl(1,1) direct limit for every spectral operator commuting with the Dirac
and mass operators. -/
theorem native_witt_shifted_dirac_factorization_in_limit (c : Limit)
    (hCE : Commute c
      (ofStage 1 wittCreation + ofStage 1 wittAnnihilation))
    (hCM : Commute c
      (ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation)) :
    (c - (ofStage 1 wittCreation + ofStage 1 wittAnnihilation)) *
        (c + (ofStage 1 wittCreation + ofStage 1 wittAnnihilation)) =
      c * c * (1 - (ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation)) +
        (c * c - 1) * (ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
          ofStage 1 wittAnnihilation * ofStage 1 wittCreation) := by
  rcases witt_pair_noncommutative_reflexive with ⟨hu₀, hv₀, huv₀, hvu₀, _⟩
  have hu : ofStage 1 wittCreation * ofStage 1 wittCreation = 0 := by
    rw [← map_mul, hu₀, map_zero]
  have hv : ofStage 1 wittAnnihilation * ofStage 1 wittAnnihilation = 0 := by
    rw [← map_mul, hv₀, map_zero]
  have huv : ofStage 1 wittCreation * ofStage 1 wittAnnihilation *
      ofStage 1 wittCreation = ofStage 1 wittCreation := by
    rw [← map_mul, ← map_mul, huv₀]
  have hvu : ofStage 1 wittAnnihilation * ofStage 1 wittCreation *
      ofStage 1 wittAnnihilation = ofStage 1 wittAnnihilation := by
    rw [← map_mul, ← map_mul, hvu₀]
  have hE2 : (ofStage 1 wittCreation + ofStage 1 wittAnnihilation) *
      (ofStage 1 wittCreation + ofStage 1 wittAnnihilation) =
        ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
          ofStage 1 wittAnnihilation * ofStage 1 wittCreation :=
    (reflexive_pair_dirac_support_and_involution hu hv huv hvu).1
  exact shifted_dirac_product_factorization hE2 hCE hCM

/-- The signed axial dissipator's exact five-element action also holds for the
images of the concrete Witt pair in the native direct limit. -/
theorem native_witt_axial_actions_in_limit :
    differenceDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation) 1 = 0 ∧
    differenceDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
          ofStage 1 wittAnnihilation * ofStage 1 wittCreation) = 0 ∧
    differenceDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation - ofStage 1 wittAnnihilation) = 0 ∧
    differenceDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation + ofStage 1 wittAnnihilation) =
      -((4 : ℕ) • ((ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation) *
          (ofStage 1 wittCreation + ofStage 1 wittAnnihilation))) ∧
    differenceDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation * ofStage 1 wittAnnihilation -
          ofStage 1 wittAnnihilation * ofStage 1 wittCreation) =
      -((4 : ℕ) • ((ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation) *
          (ofStage 1 wittCreation * ofStage 1 wittAnnihilation -
            ofStage 1 wittAnnihilation * ofStage 1 wittCreation))) := by
  rcases witt_pair_noncommutative_reflexive with ⟨hu₀, hv₀, huv₀, hvu₀, _⟩
  have hu : ofStage 1 wittCreation * ofStage 1 wittCreation = 0 := by
    rw [← map_mul, hu₀, map_zero]
  have hv : ofStage 1 wittAnnihilation * ofStage 1 wittAnnihilation = 0 := by
    rw [← map_mul, hv₀, map_zero]
  have huv : ofStage 1 wittCreation * ofStage 1 wittAnnihilation *
      ofStage 1 wittCreation = ofStage 1 wittCreation := by
    rw [← map_mul, ← map_mul, huv₀]
  have hvu : ofStage 1 wittAnnihilation * ofStage 1 wittCreation *
      ofStage 1 wittAnnihilation = ofStage 1 wittAnnihilation := by
    rw [← map_mul, ← map_mul, hvu₀]
  exact differenceDissipator_reflexive_pair_actions hu hv huv hvu

/-- The symmetric cross-branch dissipator has its exact five-element action
on the concrete Witt pair in the native direct limit. -/
theorem native_witt_symmetric_actions_in_limit :
    crossDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation) 1 = 0 ∧
    crossDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
          ofStage 1 wittAnnihilation * ofStage 1 wittCreation) = 0 ∧
    crossDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation) (ofStage 1 wittCreation +
          ofStage 1 wittAnnihilation) =
      -((2 : ℕ) • ((ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation) *
          (ofStage 1 wittCreation + ofStage 1 wittAnnihilation))) ∧
    crossDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation) (ofStage 1 wittCreation -
          ofStage 1 wittAnnihilation) =
      -((2 : ℕ) • ((ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation) *
          (ofStage 1 wittCreation - ofStage 1 wittAnnihilation))) ∧
    crossDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation * ofStage 1 wittAnnihilation -
          ofStage 1 wittAnnihilation * ofStage 1 wittCreation) =
      -((4 : ℕ) • ((ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation) *
          (ofStage 1 wittCreation * ofStage 1 wittAnnihilation -
            ofStage 1 wittAnnihilation * ofStage 1 wittCreation))) := by
  rcases witt_pair_noncommutative_reflexive with ⟨hu₀, hv₀, huv₀, hvu₀, _⟩
  have hu : ofStage 1 wittCreation * ofStage 1 wittCreation = 0 := by
    rw [← map_mul, hu₀, map_zero]
  have hv : ofStage 1 wittAnnihilation * ofStage 1 wittAnnihilation = 0 := by
    rw [← map_mul, hv₀, map_zero]
  have huv : ofStage 1 wittCreation * ofStage 1 wittAnnihilation *
      ofStage 1 wittCreation = ofStage 1 wittCreation := by
    rw [← map_mul, ← map_mul, huv₀]
  have hvu : ofStage 1 wittAnnihilation * ofStage 1 wittCreation *
      ofStage 1 wittAnnihilation = ofStage 1 wittAnnihilation := by
    rw [← map_mul, ← map_mul, hvu₀]
  exact crossDissipator_reflexive_pair_actions hu hv huv hvu

/-- The full Dirac double-commutator channel has its exact five-element action
on the concrete noncommuting Witt operators in the native limit. -/
theorem native_witt_dirac_dissipator_actions_in_limit :
    sumDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation) 1 = 0 ∧
    sumDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
          ofStage 1 wittAnnihilation * ofStage 1 wittCreation) = 0 ∧
    sumDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation + ofStage 1 wittAnnihilation) = 0 ∧
    sumDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation - ofStage 1 wittAnnihilation) =
      -((4 : ℕ) • ((ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation) *
          (ofStage 1 wittCreation - ofStage 1 wittAnnihilation))) ∧
    sumDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation * ofStage 1 wittAnnihilation -
          ofStage 1 wittAnnihilation * ofStage 1 wittCreation) =
      -((4 : ℕ) • ((ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation) *
          (ofStage 1 wittCreation * ofStage 1 wittAnnihilation -
            ofStage 1 wittAnnihilation * ofStage 1 wittCreation))) := by
  rcases witt_pair_noncommutative_reflexive with ⟨hu₀, hv₀, huv₀, hvu₀, _⟩
  have hu : ofStage 1 wittCreation * ofStage 1 wittCreation = 0 := by
    rw [← map_mul, hu₀, map_zero]
  have hv : ofStage 1 wittAnnihilation * ofStage 1 wittAnnihilation = 0 := by
    rw [← map_mul, hv₀, map_zero]
  have huv : ofStage 1 wittCreation * ofStage 1 wittAnnihilation *
      ofStage 1 wittCreation = ofStage 1 wittCreation := by
    rw [← map_mul, ← map_mul, huv₀]
  have hvu : ofStage 1 wittAnnihilation * ofStage 1 wittCreation *
      ofStage 1 wittAnnihilation = ofStage 1 wittAnnihilation := by
    rw [← map_mul, ← map_mul, hvu₀]
  exact sumDissipator_reflexive_pair_actions hu hv huv hvu

/-- The three dissipator channels obey the midpoint and phase-conjugate
difference laws on the actual noncommuting Witt pair in the direct limit. -/
theorem native_witt_dissipator_trinity_in_limit :
    (2 : ℕ) • crossDissipator (R := ℝ)
        (ofStage 1 wittCreation) (ofStage 1 wittAnnihilation) =
      sumDissipator (R := ℝ) (ofStage 1 wittCreation)
          (ofStage 1 wittAnnihilation) +
        differenceDissipator (R := ℝ) (ofStage 1 wittCreation)
          (ofStage 1 wittAnnihilation) ∧
    sumDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation) -
      differenceDissipator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation) =
      (4 : ℕ) • sameCornerChannel (R := ℝ)
        (ofStage 1 wittCreation) (ofStage 1 wittAnnihilation) := by
  exact ⟨twice_crossDissipator_eq_sum_add_difference (R := ℝ) _ _,
    sum_sub_difference_eq_four_sameCorner (R := ℝ) _ _⟩

/-- The full mass-commutator GKSL generator's exact five-element action holds
on the concrete noncommuting Witt operators in the native direct limit. -/
theorem native_witt_mass_gksl_actions_in_limit :
    massGkslGenerator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation) 1 = 0 ∧
    massGkslGenerator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
          ofStage 1 wittAnnihilation * ofStage 1 wittCreation) = 0 ∧
    massGkslGenerator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation + ofStage 1 wittAnnihilation) =
      -((2 : ℕ) • ((ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation) *
          (ofStage 1 wittCreation + ofStage 1 wittAnnihilation))) ∧
    massGkslGenerator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation - ofStage 1 wittAnnihilation) =
      -((2 : ℕ) • ((ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation) *
          (ofStage 1 wittCreation - ofStage 1 wittAnnihilation))) ∧
    massGkslGenerator (R := ℝ) (ofStage 1 wittCreation)
        (ofStage 1 wittAnnihilation)
        (ofStage 1 wittCreation * ofStage 1 wittAnnihilation -
          ofStage 1 wittAnnihilation * ofStage 1 wittCreation) =
      -((4 : ℕ) • ((ofStage 1 wittCreation * ofStage 1 wittAnnihilation +
        ofStage 1 wittAnnihilation * ofStage 1 wittCreation) *
          (ofStage 1 wittCreation * ofStage 1 wittAnnihilation -
            ofStage 1 wittAnnihilation * ofStage 1 wittCreation))) := by
  rcases witt_pair_noncommutative_reflexive with ⟨hu₀, hv₀, huv₀, hvu₀, _⟩
  have hu : ofStage 1 wittCreation * ofStage 1 wittCreation = 0 := by
    rw [← map_mul, hu₀, map_zero]
  have hv : ofStage 1 wittAnnihilation * ofStage 1 wittAnnihilation = 0 := by
    rw [← map_mul, hv₀, map_zero]
  have huv : ofStage 1 wittCreation * ofStage 1 wittAnnihilation *
      ofStage 1 wittCreation = ofStage 1 wittCreation := by
    rw [← map_mul, ← map_mul, huv₀]
  have hvu : ofStage 1 wittAnnihilation * ofStage 1 wittCreation *
      ofStage 1 wittAnnihilation = ofStage 1 wittAnnihilation := by
    rw [← map_mul, ← map_mul, hvu₀]
  exact mass_gksl_reflexive_pair_actions hu hv huv hvu

/-- The native creation and annihilation operators remain noncommuting in the
direct limit because the Cl(1,1) tensor-tower bonding maps are injective. -/
theorem native_witt_pair_noncommute_in_limit :
    ofStage 1 wittCreation * ofStage 1 wittAnnihilation ≠
      ofStage 1 wittAnnihilation * ofStage 1 wittCreation := by
  have hStageNe := witt_pair_noncommutative_reflexive.2.2.2.2
  have hBond : ∀ n, Function.Injective (stageBond n) := by
    intro n x y hxy
    exact matStageEmbed_injective n (by simpa [stageBond] using hxy)
  have hOf : Function.Injective (ofStage 1) := by
    exact directLimitOf_injective stageBond hBond 1
  intro hcomm
  apply hStageNe
  apply hOf
  simpa only [map_mul] using hcomm

/-- The native stage inclusion intertwines the positive regular-module action. -/
theorem stage_dualPlus (n : ℕ) (H S X : Stage n) :
    ofStage n (dualPlus ℝ H S X) =
      dualPlus ℝ (ofStage n H) (ofStage n S) (ofStage n X) := by
  simp only [dualPlus_apply, map_add, map_sub, map_mul]

theorem stage_dualMinus (n : ℕ) (H S X : Stage n) :
    ofStage n (dualMinus ℝ H S X) =
      dualMinus ℝ (ofStage n H) (ofStage n S) (ofStage n X) := by
  simp only [dualMinus_apply, map_add, map_sub, map_mul]

/-- All four native Peirce corners commute with the same stage inclusion. -/
theorem stage_corner (n : ℕ) (p X : Stage n) (i j : Bool) :
    ofStage n (corner ℝ p i j X) =
      corner ℝ (ofStage n p) i j (ofStage n X) := by
  cases i <;> cases j <;>
    simp only [corner_apply, Bool.false_eq_true, ite_false, ite_true,
      compIdempotent, map_mul, map_sub, map_one]

/-- The full mixed defect is preserved, not discarded at infinity. -/
theorem stage_mixed_defect (n : ℕ) (H S X : Stage n) :
    ofStage n (jordan ℝ (H * S - S * H) X) =
      jordan ℝ (ofStage n H * ofStage n S - ofStage n S * ofStage n H)
        (ofStage n X) := by
  simp only [jordan_apply, map_add, map_sub, map_mul]

/-- Passing through one more matrix stage gives the identical colimit action. -/
theorem stage_dualPlus_bond (n : ℕ) (H S X : Stage n) :
    ofStage (n + 1)
      (dualPlus ℝ (stageEmbed n H) (stageEmbed n S) (stageEmbed n X)) =
      ofStage n (dualPlus ℝ H S X) := by
  rw [← map_dualPlus ℝ (stageEmbed n), ofStage_apply_bond]

theorem stage_dualMinus_bond (n : ℕ) (H S X : Stage n) :
    ofStage (n + 1)
      (dualMinus ℝ (stageEmbed n H) (stageEmbed n S) (stageEmbed n X)) =
      ofStage n (dualMinus ℝ H S X) := by
  rw [← map_dualMinus ℝ (stageEmbed n), ofStage_apply_bond]

/-- The complementary corner identity holds on the actual limit. -/
theorem limit_complementary_corner (n : ℕ) (p : Stage n) (hp : p * p = p)
    (X : Limit) :
    2 • peirce00 (ofStage n p) X =
      2 • X - jordan ℝ (ofStage n p) X -
        ad ℝ (ofStage n p) (ad ℝ (ofStage n p) X) := by
  exact twice_peirce00 ℝ (limit_idempotent hp) X

/-- The four projector compositions hold for arbitrary inputs of the limit,
not only for matrices at the original stage. -/
theorem limit_corner_comp (n : ℕ) (p : Stage n) (hp : p * p = p)
    (i j k l : Bool) :
    corner ℝ (ofStage n p) i j * corner ℝ (ofStage n p) k l =
      if i = k ∧ j = l then corner ℝ (ofStage n p) i j else 0 := by
  exact corner_comp ℝ (limit_idempotent hp) i j k l

end InfoGeometry.OperatorAlgebra.LieJordanPeirceColimit
