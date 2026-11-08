/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SteinbergBraidDefectSpine

/-!
# Peirce realization of the Omega quadratic seed

For an idempotent `P` and its two off-diagonal Peirce corners, the element
`T = P + Φ` satisfies `T² - T = V`. This is an operator-valued quadratic
relation in an arbitrary associative ring. It specializes to `T² = T + 1`
only under the additional mass equation `V = 1`; no combinatorial shift,
Fibonacci tower, or entropy statement follows from this algebraic identity
alone.
-/

namespace PureNonCommutativeOperatorSpine

variable {B : Type*} [Ring B]

/-- Peirce transfer element `P + Φ`, with the lower-right Peirce block zero. -/
def goldenTransfer (P A C : B) : B := P + genPhi P A C

/-- Complementary element `1 - T` for the Peirce transfer element. -/
def goldenTransferConj (P A C : B) : B := (1 - P) - genPhi P A C

/-- The parallel difference-channel element `P + J`. -/
def goldenTransferJ (P A C : B) : B := P + genJ P A C

/-- The Peirce blocks of the transfer element: its `P`-diagonal corner is `P`,
the off-diagonal corners are the two switches, and its `(1-P)`-diagonal
corner vanishes. -/
theorem goldenTransfer_peirce_blocks {P : B} (hP : P * P = P)
    (A C : B) :
    P * goldenTransfer P A C * P = P ∧
    P * goldenTransfer P A C * (1 - P) = conePlus P A ∧
    (1 - P) * goldenTransfer P A C * P = coneMinus P C ∧
    (1 - P) * goldenTransfer P A C * (1 - P) = 0 := by
  unfold goldenTransfer genPhi conePlus coneMinus
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring [hP, P_assoc hP]

/-- The idempotent acts on the odd Peirce element with anticommutator `Φ`. -/
theorem peirce_idempotent_genPhi_anticomm {P : B} (hP : P * P = P)
    (A C : B) :
    P * genPhi P A C + genPhi P A C * P = genPhi P A C := by
  simp only [genPhi, conePlus, coneMinus, anticomm]
  noncomm_ring [hP, P_assoc hP]

/-- The golden transfer element has operator-valued defect `V`:
`(P + Φ)² - (P + Φ) = V`. -/
theorem goldenTransfer_idempotencyDefect {P : B} (hP : P * P = P)
    (A C : B) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (goldenTransfer P A C) = genV P A C := by
  unfold InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
    goldenTransfer
  have hPF := peirce_idempotent_genPhi_anticomm hP A C
  have hPhiSq := genPhi_sq hP A C
  calc
    (P + genPhi P A C) * (P + genPhi P A C) -
        (P + genPhi P A C) =
        P * P + (P * genPhi P A C + genPhi P A C * P) +
          genPhi P A C * genPhi P A C - (P + genPhi P A C) := by
            noncomm_ring
    _ = genV P A C := by rw [hP, hPF, hPhiSq]; abel

/-- Applying the defect polynomial to the odd Peirce generator gives its
quadratic relation with the linear term retained. -/
theorem genPhi_idempotencyDefect {P : B} (hP : P * P = P)
    (A C : B) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (genPhi P A C) = genV P A C - genPhi P A C := by
  unfold InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
  have hPhiSq := genPhi_sq hP A C
  rw [hPhiSq]

/-- The negative odd generator gives the complementary defect value. -/
theorem genPhi_neg_idempotencyDefect {P : B} (hP : P * P = P)
    (A C : B) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (-(genPhi P A C)) = genV P A C + genPhi P A C := by
  unfold InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
  have hPhiSq := genPhi_sq hP A C
  rw [neg_mul_neg, hPhiSq]
  abel

/-- The defect values at `-Φ` and `Φ` multiply to the defect at the mass
operator `V`, an instance of the universal defect-tower identity. -/
theorem genPhi_defect_tower {P : B} (hP : P * P = P)
    (A C : B) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (-(genPhi P A C)) *
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (genPhi P A C) =
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (genV P A C) := by
  rw [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect_neg_mul,
    genPhi_sq hP A C]

/-- The transfer element is genuinely noncommutative with the sheet idempotent
whenever the block-swapping operator `J` is nonzero: `[P,T]=J`. -/
theorem idempotent_comm_goldenTransfer {P : B} (hP : P * P = P)
    (A C : B) : comm P (goldenTransfer P A C) = genJ P A C := by
  unfold comm goldenTransfer genPhi genJ conePlus coneMinus
  noncomm_ring [hP, P_assoc hP]

/-- The difference-channel element has the opposite mass defect. -/
theorem goldenTransferJ_idempotencyDefect {P : B} (hP : P * P = P)
    (A C : B) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (goldenTransferJ P A C) = -(genV P A C) := by
  unfold InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
    goldenTransferJ
  have hPJ : P * genJ P A C + genJ P A C * P = genJ P A C := by
    simp only [genJ, conePlus, coneMinus]
    noncomm_ring [hP, P_assoc hP]
  have hJSq := genJ_sq hP A C
  calc
    (P + genJ P A C) * (P + genJ P A C) - (P + genJ P A C) =
        P * P + (P * genJ P A C + genJ P A C * P) +
          genJ P A C * genJ P A C - (P + genJ P A C) := by
            noncomm_ring
    _ = -genV P A C := by rw [hP, hPJ, hJSq]; abel

/-- `goldenTransferConj` is exactly `1 - goldenTransfer`; hence it has the
same idempotency defect by complementary symmetry. -/
theorem goldenTransferConj_eq_one_sub {P : B} (A C : B) :
    goldenTransferConj P A C = 1 - goldenTransfer P A C := by
  unfold goldenTransferConj goldenTransfer genPhi
  noncomm_ring

theorem goldenTransferConj_idempotencyDefect {P : B} (hP : P * P = P)
    (A C : B) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (goldenTransferConj P A C) = genV P A C := by
  rw [goldenTransferConj_eq_one_sub]
  rw [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect_one_sub,
    goldenTransfer_idempotencyDefect hP]

/-- The Peirce mass commutes with the base idempotent. -/
theorem genV_commute_idempotent {P : B} (hP : P * P = P) (A C : B) :
    comm (genV P A C) P = 0 := by
  simp only [comm, genV, anticomm, conePlus, coneMinus]
  noncomm_ring [hP, P_assoc hP]

/-- Consequently the operator-valued recurrence coefficient `V` commutes
with the transfer element `T=P+Φ`. -/
theorem genV_commute_goldenTransfer {P : B} (hP : P * P = P)
    (A C : B) : comm (genV P A C) (goldenTransfer P A C) = 0 := by
  have hVP : genV P A C * P = P * genV P A C :=
    sub_eq_zero.mp (genV_commute_idempotent hP A C)
  have hPlus : genV P A C * conePlus P A =
      conePlus P A * genV P A C :=
    (sub_eq_zero.mp (genV_commute_conePlus hP A C)).symm
  have hMinus : genV P A C * coneMinus P C =
      coneMinus P C * genV P A C :=
    (sub_eq_zero.mp (genV_commute_coneMinus hP A C)).symm
  unfold comm goldenTransfer genPhi
  noncomm_ring [hVP, hPlus, hMinus]

/-- The transfer and its complement sum to one and their ordered products
both equal `-V`. These are quadratic-algebra relations, not scalar norms. -/
theorem goldenTransfer_vieta_relations {P : B} (hP : P * P = P)
    (A C : B) :
    goldenTransfer P A C + goldenTransferConj P A C = 1 ∧
    goldenTransfer P A C * goldenTransferConj P A C = -genV P A C ∧
    goldenTransferConj P A C * goldenTransfer P A C = -genV P A C := by
  have hcomp := goldenTransferConj_eq_one_sub (P := P) A C
  have hdef := goldenTransfer_idempotencyDefect hP A C
  have hsq : goldenTransfer P A C * goldenTransfer P A C =
      goldenTransfer P A C + genV P A C := by
    unfold InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect at hdef
    exact sub_eq_iff_eq_add'.mp hdef
  refine ⟨?_, ?_, ?_⟩
  · rw [hcomp]
    noncomm_ring
  · rw [hcomp, mul_sub, mul_one, hsq]
    abel
  · rw [hcomp, sub_mul, one_mul, hsq]
    abel

/-- The operator transfer element satisfies the exact `V`-weighted Fibonacci
power recurrence. The coefficient remains an operator in the ambient ring. -/
theorem goldenTransfer_pow_recurrence {P : B} (hP : P * P = P)
    (A C : B) (n : ℕ) :
    goldenTransfer P A C ^ (n + 2) =
      goldenTransfer P A C ^ (n + 1) +
        genV P A C * goldenTransfer P A C ^ n := by
  have hdef := goldenTransfer_idempotencyDefect hP A C
  change goldenTransfer P A C * goldenTransfer P A C - goldenTransfer P A C =
    genV P A C at hdef
  have hsq : goldenTransfer P A C * goldenTransfer P A C =
      goldenTransfer P A C + genV P A C := sub_eq_iff_eq_add'.mp hdef
  calc
    goldenTransfer P A C ^ (n + 2) = goldenTransfer P A C ^ (2 + n) := by
      rw [Nat.add_comm]
    _ = (goldenTransfer P A C ^ 2) * goldenTransfer P A C ^ n := by
      rw [pow_add]
    _ = (goldenTransfer P A C + genV P A C) *
        goldenTransfer P A C ^ n := by rw [pow_two, hsq]
    _ = goldenTransfer P A C ^ (n + 1) +
        genV P A C * goldenTransfer P A C ^ n := by
      rw [add_mul, ← pow_succ']

/-- Cubic transfer identity `T³ = (1+V)T+V`. -/
theorem goldenTransfer_cube {P : B} (hP : P * P = P) (A C : B) :
    goldenTransfer P A C ^ 3 =
      (1 + genV P A C) * goldenTransfer P A C + genV P A C := by
  have hsq : goldenTransfer P A C * goldenTransfer P A C =
      goldenTransfer P A C + genV P A C := by
    have hdef := goldenTransfer_idempotencyDefect hP A C
    change goldenTransfer P A C * goldenTransfer P A C - goldenTransfer P A C =
      genV P A C at hdef
    exact sub_eq_iff_eq_add'.mp hdef
  have hrec := goldenTransfer_pow_recurrence hP A C 1
  have hrec' : goldenTransfer P A C ^ 3 =
      goldenTransfer P A C ^ 2 + genV P A C * goldenTransfer P A C := by
    simpa using hrec
  calc
    goldenTransfer P A C ^ 3 =
        goldenTransfer P A C ^ 2 + genV P A C * goldenTransfer P A C := hrec'
    _ = (goldenTransfer P A C + genV P A C) +
        genV P A C * goldenTransfer P A C := by rw [pow_two, hsq]
    _ = (1 + genV P A C) * goldenTransfer P A C + genV P A C := by
      noncomm_ring

/-- Fourth transfer power in terms of the central mass polynomial. -/
theorem goldenTransfer_fourth {P : B} (hP : P * P = P) (A C : B) :
    goldenTransfer P A C ^ 4 =
      (1 + (2 : ℤ) • genV P A C) * goldenTransfer P A C +
        genV P A C + genV P A C * genV P A C := by
  have hsq : goldenTransfer P A C * goldenTransfer P A C =
      goldenTransfer P A C + genV P A C := by
    have hdef := goldenTransfer_idempotencyDefect hP A C
    change goldenTransfer P A C * goldenTransfer P A C - goldenTransfer P A C =
      genV P A C at hdef
    exact sub_eq_iff_eq_add'.mp hdef
  have hrec := goldenTransfer_pow_recurrence hP A C 2
  have hrec' : goldenTransfer P A C ^ 4 =
      goldenTransfer P A C ^ 3 + genV P A C * goldenTransfer P A C ^ 2 := by
    simpa using hrec
  calc
    goldenTransfer P A C ^ 4 =
        goldenTransfer P A C ^ 3 + genV P A C * goldenTransfer P A C ^ 2 := hrec'
    _ = ((1 + genV P A C) * goldenTransfer P A C + genV P A C) +
        genV P A C * (goldenTransfer P A C + genV P A C) := by
      rw [goldenTransfer_cube hP, pow_two, hsq]
    _ = (1 + (2 : ℤ) • genV P A C) * goldenTransfer P A C +
        genV P A C + genV P A C * genV P A C := by
      noncomm_ring

/-- The first two Binet--Lucas power sums of `T` and `1-T` are operator-valued
polynomials in the Peirce mass. -/
theorem goldenTransfer_lucas_moments {P : B} (hP : P * P = P)
    (A C : B) :
    goldenTransfer P A C ^ 2 + goldenTransferConj P A C ^ 2 =
      1 + (2 : ℤ) • genV P A C ∧
    goldenTransfer P A C ^ 3 + goldenTransferConj P A C ^ 3 =
      1 + (3 : ℤ) • genV P A C := by
  let T := goldenTransfer P A C
  let Tb := goldenTransferConj P A C
  have hT2 : T * T = T + genV P A C := by
    have hdef := goldenTransfer_idempotencyDefect hP A C
    change T * T - T = genV P A C at hdef
    exact sub_eq_iff_eq_add'.mp hdef
  have hTb2 : Tb * Tb = Tb + genV P A C := by
    have hdef := goldenTransferConj_idempotencyDefect hP A C
    change Tb * Tb - Tb = genV P A C at hdef
    exact sub_eq_iff_eq_add'.mp hdef
  have hsum : T + Tb = 1 := by
    dsimp [T, Tb]
    rw [goldenTransferConj_eq_one_sub]
    noncomm_ring
  have hT3 : T ^ 3 = T ^ 2 + genV P A C * T := by
    simpa [T] using goldenTransfer_pow_recurrence hP A C 1
  have hTb3 : Tb ^ 3 = Tb ^ 2 + genV P A C * Tb := by
    calc
      Tb ^ 3 = (Tb * Tb) * Tb := by simp [pow_succ, pow_two]
      _ = (Tb + genV P A C) * Tb := by rw [hTb2]
      _ = Tb ^ 2 + genV P A C * Tb := by rw [add_mul, pow_two]
  have hL2 : T ^ 2 + Tb ^ 2 = 1 + (2 : ℤ) • genV P A C := by
    calc
      T ^ 2 + Tb ^ 2 = (T + genV P A C) + (Tb + genV P A C) := by
        simp only [pow_two, hT2, hTb2]
      _ = (T + Tb) + (genV P A C + genV P A C) := by abel
      _ = 1 + (2 : ℤ) • genV P A C := by rw [hsum, two_zsmul]
  refine ⟨hL2, ?_⟩
  · calc
      T ^ 3 + Tb ^ 3 =
          (T ^ 2 + genV P A C * T) + (Tb ^ 2 + genV P A C * Tb) := by
        rw [hT3, hTb3]
      _ = (T ^ 2 + Tb ^ 2) + genV P A C * (T + Tb) := by noncomm_ring
      _ = (1 + (2 : ℤ) • genV P A C) + genV P A C := by
        rw [hL2, hsum]
        simp
      _ = 1 + (3 : ℤ) • genV P A C := by
        rw [two_zsmul]
        abel

/-- On the unit-mass shell `V=1`, the Peirce transfer element satisfies
Omega's quadratic seed equation `T²=T+1`. -/
theorem goldenTransfer_seed_of_mass_eq_one {P : B} (hP : P * P = P)
    (A C : B) (hV : genV P A C = 1) :
    goldenTransfer P A C * goldenTransfer P A C =
      goldenTransfer P A C + 1 := by
  have hdef := goldenTransfer_idempotencyDefect hP A C
  change goldenTransfer P A C * goldenTransfer P A C - goldenTransfer P A C =
    genV P A C at hdef
  have hsq : goldenTransfer P A C * goldenTransfer P A C =
      goldenTransfer P A C + genV P A C := sub_eq_iff_eq_add'.mp hdef
  rw [hV] at hsq
  exact hsq

end PureNonCommutativeOperatorSpine
