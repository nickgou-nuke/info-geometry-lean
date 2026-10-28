/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.ZornCommutator
import InfoGeometry.NCG.PeirceGradingOperator
import InfoGeometry.NCG.TrialitySingletLieDerivation
import InfoGeometry.NCG.CausalPoset
import Mathlib.Tactic

/-!
# Peirce Components of Associator and Jacobiator Defects

This file records exact Peirce-component readouts for the repository's native
nonassociative `OpZornMatrix A` carrier. Every element, including an
associator or Jacobiator, decomposes into two diagonal corners and two
off-diagonal corners. This decomposition alone does **not** imply that a
nonzero defect has a nonzero off-diagonal component.

The file proves the native ordered `skewCross` product and associator formulas
for specified homogeneous inputs, the universal four-component decomposition,
and the criterion that a Jacobiator is diagonal exactly when both of its
off-diagonal components vanish. The Jacobiator–associator identity and the
sector-specific Jacobi/associativity results are owned by the imported modules.

All results use the actual `OpZornMatrix A` multiplication over `[Ring A]`;
this carrier is nonassociative in general. No alternate Zorn multiplication or
commutative/scalar surrogate is introduced. A nonzero defect is not asserted
to generate a particular grade without a theorem identifying its component
and proving that component nonzero. -/

namespace InfoGeometry.NCG.AnomalyGradeGeneration

variable {A : Type*} [Ring A]

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix
open InfoGeometry.NCG.ZornCommutator
open InfoGeometry.NCG.PeirceGradingOperator
open InfoGeometry.NCG.TrialitySingletLieDerivation
open InfoGeometry.NCG.CausalPoset

/-- Peirce corner block extraction of any operator X:
  P₊·X·P₊ (P₊-corner), P₋·X·P₋ (P₋-corner),
  P₊·X·P₋ (off-diagonal +), P₋·X·P₊ (off-diagonal -). -/
def peirce_pp (X : OpZornMatrix A) : OpZornMatrix A := P_plus * X * P_plus
def peirce_mm (X : OpZornMatrix A) : OpZornMatrix A := P_minus * X * P_minus
def peirce_pm (X : OpZornMatrix A) : OpZornMatrix A := P_plus * X * P_minus
def peirce_mp (X : OpZornMatrix A) : OpZornMatrix A := P_minus * X * P_plus

/-- The two off-diagonal Peirce grades, using the repository's actual Zorn
carrier and ordered coefficient operations. -/
def fockRaise (u : OpVec3 A) : OpZornMatrix A := ⟨0, u, 0, 0⟩
def fockLower (w : OpVec3 A) : OpZornMatrix A := ⟨0, 0, w, 0⟩

/-- P₊·X·P₊ = ⟨X.a, 0, 0, 0⟩: only the P₊-scalar survives. -/
@[simp] theorem peirce_pp_eq (X : OpZornMatrix A) :
    peirce_pp X = ⟨X.a, 0, 0, 0⟩ := by
  ext <;>
  simp [peirce_pp, P_plus, mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- P₋·X·P₋ = ⟨0, 0, 0, X.b⟩: only the P₋-scalar survives. -/
@[simp] theorem peirce_mm_eq (X : OpZornMatrix A) :
    peirce_mm X = ⟨0, 0, 0, X.b⟩ := by
  ext <;>
  simp [peirce_mm, P_minus, mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- P₊·X·P₋ = ⟨0, X.v, 0, 0⟩: the upper off-diagonal block. -/
@[simp] theorem peirce_pm_eq (X : OpZornMatrix A) :
    peirce_pm X = ⟨0, X.v, 0, 0⟩ := by
  ext <;>
  simp [peirce_pm, P_plus, P_minus, mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- P₋·X·P₊ = ⟨0, 0, X.w, 0⟩: the lower off-diagonal block. -/
@[simp] theorem peirce_mp_eq (X : OpZornMatrix A) :
    peirce_mp X = ⟨0, 0, X.w, 0⟩ := by
  ext <;>
  simp [peirce_mp, P_plus, P_minus, mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- Peirce decomposition of any operator into four component readouts:
  `X = P₊·X·P₊ + P₋·X·P₋ + P₊·X·P₋ + P₋·X·P₊`.
This is a coordinate decomposition; it makes no nonvanishing claim about any
component of a particular defect. -/
theorem peirce_decomposition (X : OpZornMatrix A) :
    X = peirce_pp X + peirce_mm X + peirce_pm X + peirce_mp X := by
  rw [peirce_pp_eq, peirce_mm_eq, peirce_pm_eq, peirce_mp_eq]
  ext <;>
  simp [P_plus, P_minus, mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale,
    OpZornMatrix.add_a, OpZornMatrix.add_b, OpZornMatrix.add_v, OpZornMatrix.add_w] <;>
  (try noncomm_ring) <;>
  (try abel)

/-!
## Product and associator anomalies

The coefficient-valued cross operation in this owner is `skewCross`, not the
naive coordinate cross product. The identities below therefore record the
actual image of each anomaly in the opposite Peirce grade, without assuming
commutativity of `A`.
-/

/-- Same-grade products need not vanish: their exact defect is the
`skewCross` element in the opposite odd Peirce grade. -/
theorem odd_product_anomaly_generates_opposite_grade
    (u₁ u₂ w₁ w₂ : OpVec3 A) :
    fockRaise u₁ * fockRaise u₂ = fockLower (OpVec3.skewCross u₁ u₂) ∧
    fockLower w₁ * fockLower w₂ = -fockRaise (OpVec3.skewCross w₁ w₂) := by
  constructor <;>
    ext <;>
    simp [fockRaise, fockLower, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- The upper odd-grade embedding is injective, so its image is zero exactly
when its vector coordinate is zero. -/
theorem fockRaise_eq_zero_iff (u : OpVec3 A) : fockRaise u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hv := congrArg (fun X : OpZornMatrix A => X.v) h
    simpa [fockRaise] using hv
  · rintro rfl
    rfl

/-- The lower odd-grade embedding has the corresponding exact support
criterion. -/
theorem fockLower_eq_zero_iff (w : OpVec3 A) : fockLower w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have hw := congrArg (fun X : OpZornMatrix A => X.w) h
    simpa [fockLower] using hw
  · rintro rfl
    rfl

/-- A same-grade product anomaly is nonzero exactly when its opposite-grade
`skewCross` component is nonzero. No nonvanishing claim is made for arbitrary
inputs or coefficient rings. -/
theorem odd_product_anomaly_nonzero_iff
    (u₁ u₂ w₁ w₂ : OpVec3 A) :
    (fockRaise u₁ * fockRaise u₂ ≠ 0 ↔
      OpVec3.skewCross u₁ u₂ ≠ 0) ∧
    (fockLower w₁ * fockLower w₂ ≠ 0 ↔
      OpVec3.skewCross w₁ w₂ ≠ 0) := by
  rcases odd_product_anomaly_generates_opposite_grade u₁ u₂ w₁ w₂ with
    ⟨hUpper, hLower⟩
  constructor
  · rw [hUpper]
    exact (fockLower_eq_zero_iff (OpVec3.skewCross u₁ u₂)).not
  · rw [hLower]
    simpa using (fockRaise_eq_zero_iff (OpVec3.skewCross w₁ w₂)).not

/-- Three upper odd-grade elements have an associator entirely in the two
diagonal Peirce corners. Signs reflect the owner multiplication
`a = a₁a₂ - dot(v₁,w₂)`, `b = -dot(w₁,v₂) + b₁b₂`. -/
theorem triple_raise_associator_corner_anomaly (u₁ u₂ u₃ : OpVec3 A) :
    opAssociator (fockRaise u₁) (fockRaise u₂) (fockRaise u₃) =
      peirce_pp ⟨OpVec3.dot u₁ (OpVec3.skewCross u₂ u₃), 0, 0, 0⟩ +
      peirce_mm ⟨0, 0, 0, -OpVec3.dot (OpVec3.skewCross u₁ u₂) u₃⟩ := by
  ext <;>
    simp [opAssociator, peirce_pp_eq, peirce_mm_eq,
      fockRaise, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- A mixed associator of two upper odd-grade elements and one lower one lands
in the upper odd grade. This is the ordered double-`skewCross` anomaly. -/
theorem mixed_raise_associator_grade_anomaly (u₁ u₂ w : OpVec3 A) :
    opAssociator (fockRaise u₁) (fockRaise u₂) (fockLower w) =
      fockRaise (-(OpVec3.skewCross (OpVec3.skewCross u₁ u₂) w)) := by
  ext <;>
    simp [opAssociator, fockRaise, fockLower, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- The Jacobiator's Peirce corner blocks are even-grade components. -/
theorem jacobiator_peirce_corners_even
    (X Y Z : OpZornMatrix A) :
    peirce_pp (zornJacobiator X Y Z) = P_plus * zornJacobiator X Y Z * P_plus ∧
    peirce_mm (zornJacobiator X Y Z) = P_minus * zornJacobiator X Y Z * P_minus := by
  refine ⟨rfl, rfl⟩

/-- The Jacobiator's off-diagonal Peirce components are η-odd:
  `η·J₊₋·η = -J₊₋` and `η·J₋₊·η = -J₋₊`.
This identifies their parity, not their nonvanishing. -/
theorem jacobiator_peirce_offdiag_odd
    (X Y Z : OpZornMatrix A) :
    peirce_pm (zornJacobiator X Y Z) = P_plus * zornJacobiator X Y Z * P_minus ∧
    peirce_mp (zornJacobiator X Y Z) = P_minus * zornJacobiator X Y Z * P_plus ∧
    eta_grading * peirce_pm (zornJacobiator X Y Z) * eta_grading =
      -peirce_pm (zornJacobiator X Y Z) ∧
    eta_grading * peirce_mp (zornJacobiator X Y Z) * eta_grading =
      -peirce_mp (zornJacobiator X Y Z) := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;>
  simp [peirce_pm_eq, peirce_mp_eq] <;>
  ext <;>
  simp [peirce_pp_eq, peirce_mm_eq, peirce_pm_eq, peirce_mp_eq,
    eta_grading, instMulOpZornMatrix, instNegOpZornMatrix,
    mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- On the x-axis sector, the owner-proved Jacobi identity implies that all
four Peirce components vanish. This theorem supplies the sector inputs itself;
it does not assume the Jacobiator is zero. -/
theorem jacobiator_vanishes_on_xaxis_all_peirce_blocks
    (a₁ v₁ w₁ b₁ a₂ v₂ w₂ b₂ a₃ v₃ w₃ b₃ : A) :
    peirce_pp (zornJacobiator (quatSubalgX a₁ v₁ w₁ b₁)
      (quatSubalgX a₂ v₂ w₂ b₂)
      (quatSubalgX a₃ v₃ w₃ b₃)) = 0 ∧
    peirce_mm (zornJacobiator (quatSubalgX a₁ v₁ w₁ b₁)
      (quatSubalgX a₂ v₂ w₂ b₂)
      (quatSubalgX a₃ v₃ w₃ b₃)) = 0 ∧
    peirce_pm (zornJacobiator (quatSubalgX a₁ v₁ w₁ b₁)
      (quatSubalgX a₂ v₂ w₂ b₂)
      (quatSubalgX a₃ v₃ w₃ b₃)) = 0 ∧
    peirce_mp (zornJacobiator (quatSubalgX a₁ v₁ w₁ b₁)
      (quatSubalgX a₂ v₂ w₂ b₂)
      (quatSubalgX a₃ v₃ w₃ b₃)) = 0 := by
  rw [zornJacobiator_vanishes_on_quatSubalgX]
  simp [peirce_pp, peirce_mm, peirce_pm, peirce_mp]

/-- The associator's Peirce corner blocks are even-grade components. -/
theorem associator_peirce_corners_even
    (X Y Z : OpZornMatrix A) :
    peirce_pp (opAssociator X Y Z) = P_plus * opAssociator X Y Z * P_plus ∧
    peirce_mm (opAssociator X Y Z) = P_minus * opAssociator X Y Z * P_minus := by
  refine ⟨rfl, rfl⟩

/-- The associator's off-diagonal Peirce components are η-odd:
  `η·Ass₊₋·η = -Ass₊₋` and `η·Ass₋₊·η = -Ass₋₊`.
This identifies their parity, not their nonvanishing. -/
theorem associator_peirce_offdiag_odd
    (X Y Z : OpZornMatrix A) :
    peirce_pm (opAssociator X Y Z) = P_plus * opAssociator X Y Z * P_minus ∧
    peirce_mp (opAssociator X Y Z) = P_minus * opAssociator X Y Z * P_plus ∧
    eta_grading * peirce_pm (opAssociator X Y Z) * eta_grading =
      -peirce_pm (opAssociator X Y Z) ∧
    eta_grading * peirce_mp (opAssociator X Y Z) * eta_grading =
      -peirce_mp (opAssociator X Y Z) := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;>
  simp [peirce_pm_eq, peirce_mp_eq] <;>
  ext <;>
  simp [peirce_pp_eq, peirce_mm_eq, peirce_pm_eq, peirce_mp_eq,
    eta_grading, instMulOpZornMatrix, instNegOpZornMatrix,
    mul_a, mul_b, mul_v, mul_w,
    OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] <;>
  (try noncomm_ring) <;>
  (try abel)

/-- On the triality-singlet sector, the owner-proved associativity theorem
implies that all four Peirce components vanish. The inputs are quantified
explicitly; associator-vanishing is not assumed as a premise. -/
theorem associator_vanishes_on_singlet_all_peirce_blocks
    (a₁ c₁ d₁ b₁ a₂ c₂ d₂ b₂ a₃ c₃ d₃ b₃ : A) :
    peirce_pp (opAssociator (zornSinglet a₁ c₁ d₁ b₁)
      (zornSinglet a₂ c₂ d₂ b₂) (zornSinglet a₃ c₃ d₃ b₃)) = 0 ∧
    peirce_mm (opAssociator (zornSinglet a₁ c₁ d₁ b₁)
      (zornSinglet a₂ c₂ d₂ b₂) (zornSinglet a₃ c₃ d₃ b₃)) = 0 ∧
    peirce_pm (opAssociator (zornSinglet a₁ c₁ d₁ b₁)
      (zornSinglet a₂ c₂ d₂ b₂) (zornSinglet a₃ c₃ d₃ b₃)) = 0 ∧
    peirce_mp (opAssociator (zornSinglet a₁ c₁ d₁ b₁)
      (zornSinglet a₂ c₂ d₂ b₂) (zornSinglet a₃ c₃ d₃ b₃)) = 0 := by
  rw [opAssociator_zornSinglet_eq_zero]
  simp [peirce_pp, peirce_mm, peirce_pm, peirce_mp]

/-- The universal Jacobiator component formula: the Jacobiator decomposes into
  Peirce grade blocks:
    J(X,Y,Z) = J₊₊ + J₋₋ + J₊₋ + J₋₊
  where J₊₊ = P₊·J·P₊ and J₋₋ = P₋·J·P₋ are diagonal corner readouts,
  and J₊₋ = P₊·J·P₋ and J₋₊ = P₋·J·P₊ are off-diagonal readouts.
  On the x-axis sector, all four blocks vanish (Jacobi holds there). For a
  general triple this decomposition alone says nothing about which blocks are
  nonzero, and does not assert that a block generates a grade. -/
theorem jacobiator_peirce_grade_decomposition
    (X Y Z : OpZornMatrix A) :
    zornJacobiator X Y Z =
      peirce_pp (zornJacobiator X Y Z) +
      peirce_mm (zornJacobiator X Y Z) +
      peirce_pm (zornJacobiator X Y Z) +
      peirce_mp (zornJacobiator X Y Z) := by
  have h₁ := peirce_decomposition (zornJacobiator X Y Z)
  simpa [peirce_pp, peirce_mm, peirce_pm, peirce_mp] using h₁
  <;> abel

/-- The universal associator component formula: the associator decomposes into
  Peirce grade blocks:
    Ass(X,Y,Z) = Ass₊₊ + Ass₋₋ + Ass₊₋ + Ass₋₊
  where Ass₊₊ = P₊·Ass·P₊ and Ass₋₋ = P₋·Ass·P₋ are diagonal corner readouts,
  and Ass₊₋ = P₊·Ass·P₋ and Ass₋₊ = P₋·Ass·P₊ are off-diagonal readouts.
  On the zornSinglet sector, all four blocks vanish (associativity holds there).
  For a general triple this decomposition alone says nothing about which blocks
  are nonzero, and does not assert that a block generates a grade. -/
theorem associator_peirce_grade_decomposition
    (X Y Z : OpZornMatrix A) :
    opAssociator X Y Z =
      peirce_pp (opAssociator X Y Z) +
      peirce_mm (opAssociator X Y Z) +
      peirce_pm (opAssociator X Y Z) +
      peirce_mp (opAssociator X Y Z) := by
  have h₁ := peirce_decomposition (opAssociator X Y Z)
  simpa [peirce_pp, peirce_mm, peirce_pm, peirce_mp] using h₁
  <;> abel

/-- An element is supported in the diagonal Peirce corners exactly when
both off-diagonal components vanish. The converse uses their disjoint
coordinate support. This is a component criterion, not a claim that every
nonzero element or defect has a nonzero off-diagonal component. -/
theorem peirce_diagonal_iff_offdiag_vanish (T : OpZornMatrix A) :
    T = peirce_pp T + peirce_mm T ↔ peirce_pm T = 0 ∧ peirce_mp T = 0 := by
  constructor
  · intro hdiag
    have hv := congrArg (fun S : OpZornMatrix A => S.v) hdiag
    have hw := congrArg (fun S : OpZornMatrix A => S.w) hdiag
    simp only [peirce_pp_eq, peirce_mm_eq, add_v, add_w] at hv hw
    have hv0 : T.v = 0 := by
      ext
      · simpa using congrArg OpVec3.x hv
      · simpa using congrArg OpVec3.y hv
      · simpa using congrArg OpVec3.z hv
    have hw0 : T.w = 0 := by
      ext
      · simpa using congrArg OpVec3.x hw
      · simpa using congrArg OpVec3.y hw
      · simpa using congrArg OpVec3.z hw
    constructor
    · rw [peirce_pm_eq, hv0]
      rfl
    · rw [peirce_mp_eq, hw0]
      rfl
  · rintro ⟨hpm, hmp⟩
    calc
      T = peirce_pp T + peirce_mm T + peirce_pm T + peirce_mp T :=
        peirce_decomposition T
      _ = peirce_pp T + peirce_mm T := by rw [hpm, hmp]; simp

/-- A Jacobiator is diagonal exactly when its two off-diagonal Peirce
components vanish. This makes no claim that every nonzero Jacobiator has an
off-diagonal component. -/
theorem jacobiator_diagonal_iff_offdiag_vanish (X Y Z : OpZornMatrix A) :
    zornJacobiator X Y Z =
        peirce_pp (zornJacobiator X Y Z) + peirce_mm (zornJacobiator X Y Z) ↔
      peirce_pm (zornJacobiator X Y Z) = 0 ∧
        peirce_mp (zornJacobiator X Y Z) = 0 :=
  peirce_diagonal_iff_offdiag_vanish (zornJacobiator X Y Z)

/-- The same diagonal-support criterion applies to the associator defect. -/
theorem associator_diagonal_iff_offdiag_vanish (X Y Z : OpZornMatrix A) :
    opAssociator X Y Z =
        peirce_pp (opAssociator X Y Z) + peirce_mm (opAssociator X Y Z) ↔
      peirce_pm (opAssociator X Y Z) = 0 ∧
        peirce_mp (opAssociator X Y Z) = 0 :=
  peirce_diagonal_iff_offdiag_vanish (opAssociator X Y Z)

end InfoGeometry.NCG.AnomalyGradeGeneration
