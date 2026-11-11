/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11ChiralityTransport
import InfoGeometry.Clifford.Cl11StarAlgebraColimit
import InfoGeometry.Canonical.Cl11TensorTowerInfiniteCAR
import InfoGeometry.OperatorAlgebra.GradedAdjointHomotopy

/-!
# Graded CAR endomorphisms on the infinite Clifford algebraic colimit

The carrier is the existing `Cl11TensorTowerLimit.Limit`, whose infinite
dimension is proved in `Cl11ColimitDimension`. The descended global chirality
is upgraded by proving scalar preservation, then used in actual real-linear
endomorphisms of that carrier. Countable creation charges and ordinary left
annihilation actions form a new CAR family of endomorphisms.

Each mode gives a full algebraic contraction, so the unit is exact. This same
fact obstructs descent of the differential to the existing annihilation-vacuum
GNS quotient. No bounded Hilbert realization or physical mass gap is claimed.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11ChiralityGradedCAR

open Cl11TensorTowerLimit Cl11TensorTowerInfiniteCAR
open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint
open InfoGeometry.Canonical.InfiniteCARColimit
open InfoGeometry.Prequantum.GNSBridge

/-- Scalar preservation is proved on an actual stage representative. -/
theorem limitChiralityConj_algebraMap (r : ℝ) :
    limitChiralityConj (algebraMap ℝ Limit r) = algebraMap ℝ Limit r := by
  change limitChiralityConj (realAlgebraMap r) = realAlgebraMap r
  rw [realAlgebraMap_stage 0 r, limitChiralityConj_ofStage]
  congr 1
  rw [← Algebra.commutes r (Cl11TensorTower.globalChirality 0), mul_assoc,
    JordanWignerCAR.globalChirality_sq, mul_one]

/-- The existing descended chirality, with its self-inverse and scalar laws. -/
def chirality : Limit ≃ₐ[ℝ] Limit where
  toFun := limitChiralityConj
  invFun := limitChiralityConj
  left_inv := limitChiralityConj_involutive
  right_inv := limitChiralityConj_involutive
  map_mul' := limitChiralityConj.map_mul
  map_add' := limitChiralityConj.map_add
  commutes' := limitChiralityConj_algebraMap

@[simp] theorem chirality_apply (x : Limit) :
    chirality x = limitChiralityConj x := rfl

theorem chirality_involutive : Function.Involutive chirality :=
  limitChiralityConj_involutive

/-- Every countable creation mode is odd for the actual global grading. -/
theorem chirality_creationMode (i : ℕ) :
    chirality (creationMode i) = -creationMode i := by
  simpa only [chirality_apply, creationMode,
    InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit.uImage,
    Cl11TensorTower.u] using limitChiralityConj_jwCreation (i + 1) (Fin.last i)

/-- Every countable annihilation mode is odd for the same global grading. -/
theorem chirality_annihilationMode (i : ℕ) :
    chirality (annihilationMode i) = -annihilationMode i := by
  simpa only [chirality_apply, annihilationMode,
    InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit.vImage,
    Cl11TensorTower.v] using limitChiralityConj_jwAnnihilation (i + 1) (Fin.last i)

/-- Nilpotence is transported from the concrete Jordan–Wigner matrix law. -/
theorem creationMode_sq_zero (i : ℕ) : creationMode i * creationMode i = 0 := by
  simpa only [creationMode,
    InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit.uImage,
    Cl11TensorTower.u] using
    (limit_square_zero (Cl11JordanWignerCARBridge.jwCreation_sq (i + 1) (Fin.last i)))

theorem annihilationMode_sq_zero (i : ℕ) :
    annihilationMode i * annihilationMode i = 0 := by
  simpa only [annihilationMode,
    InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit.vImage,
    Cl11TensorTower.v] using
    (limit_square_zero
      (Cl11JordanWignerCARBridge.jwAnnihilation_sq (i + 1) (Fin.last i)))

/-- A graded differential on the entire infinite algebraic carrier. -/
def differential (i : ℕ) : Module.End ℝ Limit :=
  gradedAdjoint chirality (creationMode i)

/-- Its homotopy is left annihilation, retaining the operator coefficient. -/
def homotopy (i : ℕ) : Module.End ℝ Limit :=
  LinearMap.mulLeft ℝ (annihilationMode i)

@[simp] theorem differential_apply (i : ℕ) (x : Limit) :
    differential i x = creationMode i * x - chirality x * creationMode i := rfl

@[simp] theorem homotopy_apply (i : ℕ) (x : Limit) :
    homotopy i x = annihilationMode i * x := rfl

/-- Square-zero holds in the genuine endomorphism algebra. -/
theorem differential_sq_zero (i : ℕ) : differential i * differential i = 0 := by
  apply LinearMap.ext
  intro x
  change gradedAdjoint chirality (creationMode i)
    (gradedAdjoint chirality (creationMode i) x) = 0
  rw [gradedAdjoint_square_apply chirality chirality_involutive _
    (chirality_creationMode i), creationMode_sq_zero, zero_mul, mul_zero, sub_self]

theorem homotopy_sq_zero (i : ℕ) : homotopy i * homotopy i = 0 := by
  apply LinearMap.ext
  intro x
  change annihilationMode i * (annihilationMode i * x) = 0
  rw [← mul_assoc, annihilationMode_sq_zero, zero_mul]

/-- The graded differentials anticommute at all countable modes. -/
theorem differential_anticomm (i j : ℕ) :
    differential i * differential j + differential j * differential i = 0 := by
  unfold differential
  rw [gradedAdjoint_mixed chirality chirality_involutive _ _
    (chirality_creationMode i) (chirality_creationMode j), creationMode_anticomm]
  apply LinearMap.ext
  intro x
  change (0 : Limit) * x - x * 0 = 0
  simp

theorem homotopy_anticomm (i j : ℕ) :
    homotopy i * homotopy j + homotopy j * homotopy i = 0 := by
  apply LinearMap.ext
  intro x
  change annihilationMode i * (annihilationMode j * x) +
    annihilationMode j * (annihilationMode i * x) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul, annihilationMode_anticomm, zero_mul]

/-- Mixed CAR, now as an equality of operators on the whole infinite algebra. -/
theorem differential_homotopy_CAR (i j : ℕ) :
    differential i * homotopy j + homotopy j * differential i =
      if i = j then 1 else 0 := by
  unfold differential homotopy
  rw [gradedAdjoint_mulLeft_anticommutator chirality _ _
    (chirality_annihilationMode j), creationMode_annihilationMode_CAR]
  by_cases hij : i = j
  · simp only [if_pos hij]
    apply LinearMap.ext
    intro x
    change (1 : Limit) * x = x
    exact one_mul x
  · simp only [if_neg hij]
    apply LinearMap.ext
    intro x
    change (0 : Limit) * x = 0
    exact zero_mul x

/-- The derived countable CAR family acts on the existing infinite algebra;
its relations are proved above rather than supplied as model assumptions. -/
def endomorphismCAR : CARAlgebra (Module.End ℝ Limit) where
  u := differential
  v := homotopy
  anticomm_uv := differential_homotopy_CAR
  anticomm_uu := differential_anticomm
  anticomm_vv := homotopy_anticomm

theorem differential_homotopy_contracts (i : ℕ) :
    differential i * homotopy i + homotopy i * differential i = 1 := by
  simpa using differential_homotopy_CAR i i

/-- The primitive is explicit and remains in the actual algebraic colimit. -/
theorem differential_cycle_primitive (i : ℕ) (x : Limit)
    (hx : differential i x = 0) : differential i (annihilationMode i * x) = x := by
  apply gradedAdjoint_cycle_primitive chirality (creationMode i) (annihilationMode i)
    (chirality_annihilationMode i)
  · simpa using creationMode_annihilationMode_CAR i i
  · exact hx

theorem differential_ker_eq_range (i : ℕ) :
    LinearMap.ker (differential i) = LinearMap.range (differential i) := by
  apply gradedAdjoint_ker_eq_range chirality chirality_involutive
    (creationMode i) (annihilationMode i) (chirality_creationMode i)
    (chirality_annihilationMode i) (creationMode_sq_zero i)
  simpa using creationMode_annihilationMode_CAR i i

/-- The unit is exact, so this full contraction retains no unit cohomology class. -/
theorem differential_annihilationMode (i : ℕ) :
    differential i (annihilationMode i) = 1 := by
  change gradedAdjoint chirality (creationMode i) (annihilationMode i) = 1
  rw [gradedAdjoint_of_odd chirality _ _ (chirality_annihilationMode i)]
  simpa using creationMode_annihilationMode_CAR i i

/-- The algebraic differential is not representative-independent on the
annihilation-vacuum GNS quotient: it sends a null generator to the nonzero unit.
This rules out even an arbitrary function on that quotient, not just bounded
or linear candidates. It is not an inconsistency of the state or quotient. -/
theorem differential_not_descend_souriau (s : SouriauState countableCAR) (i : ℕ) :
    ¬ ∃ D : s.functional.gnsQuotient → s.functional.gnsQuotient,
      ∀ x : Limit,
        D (Quotient.mk (AbstractGNSState.gnsSetoid s.functional) x) =
          Quotient.mk (AbstractGNSState.gnsSetoid s.functional) (differential i x) := by
  rintro ⟨D, hD⟩
  have hnull :
      (Quotient.mk (AbstractGNSState.gnsSetoid s.functional) (annihilationMode i) :
        s.functional.gnsQuotient) =
      Quotient.mk (AbstractGNSState.gnsSetoid s.functional) 0 := by
    simpa only [mul_one] using souriau_vacuum_annihilated s i
  have hunit :
      (Quotient.mk (AbstractGNSState.gnsSetoid s.functional) (1 : Limit) :
        s.functional.gnsQuotient) =
      Quotient.mk (AbstractGNSState.gnsSetoid s.functional) 0 := by
    calc
      _ = D (Quotient.mk (AbstractGNSState.gnsSetoid s.functional)
          (annihilationMode i)) := by
        rw [hD (annihilationMode i), differential_annihilationMode]
      _ = D (Quotient.mk (AbstractGNSState.gnsSetoid s.functional) 0) :=
        congrArg D hnull
      _ = Quotient.mk (AbstractGNSState.gnsSetoid s.functional) 0 := by
        rw [hD 0, map_zero]
  have hequiv := Quotient.exact hunit
  change s.functional.state.eval (star ((1 : Limit) - 0) * ((1 : Limit) - 0)) = 0
    at hequiv
  have hfalse : (1 : ℝ) = 0 := by
    simpa only [sub_zero, star_one, mul_one,
      InfoGeometry.Prequantum.AlgebraicGNSState.RealAlgebraicState.eval_one] using hequiv
  exact one_ne_zero hfalse

end InfoGeometry.Clifford.Cl11ChiralityGradedCAR
