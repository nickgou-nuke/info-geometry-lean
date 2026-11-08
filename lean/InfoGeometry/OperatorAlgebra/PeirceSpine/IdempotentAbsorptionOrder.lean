/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlockTriangularIntervention

/-!
# Two-sided absorption order and one-sided affine-chart relations

This module supplies the order interface for the existing partial-flag and
three-layer Peirce results. It distinguishes two-sided idempotent containment
from the one-sided absorption relations of affine charts over any associative ring.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Two-sided absorption, the natural containment relation on idempotents. -/
def idempotentAbsorbed (P Q : B) : Prop := P * Q = P ∧ Q * P = P

/-- Left-chart absorption pair: `P Q = Q` and `Q P = P`. -/
def leftChartAbsorption (P Q : B) : Prop := P * Q = Q ∧ Q * P = P

/-- Right-chart absorption pair: `Q P = Q` and `P Q = P`. -/
def rightChartAbsorption (P Q : B) : Prop := Q * P = Q ∧ P * Q = P

/-- The left-chart relation is reflexive on idempotents. -/
theorem leftChartAbsorption_refl {P : B} (hP : P * P = P) :
    leftChartAbsorption P P := ⟨hP, hP⟩

/-- The left-chart relation is transitive, with its displayed absorption orientation. -/
theorem leftChartAbsorption_trans {P Q R : B} :
    leftChartAbsorption P Q → leftChartAbsorption Q R → leftChartAbsorption P R := by
  rintro ⟨hPQ, hQP⟩ ⟨hQR, hRQ⟩
  constructor
  · calc
      P * R = P * (Q * R) := by rw [hQR]
      _ = (P * Q) * R := by rw [mul_assoc]
      _ = Q * R := by rw [hPQ]
      _ = R := hQR
  · calc
      R * P = R * (Q * P) := by rw [hQP]
      _ = (R * Q) * P := by rw [← mul_assoc]
      _ = Q * P := by rw [hRQ]
      _ = P := hQP

/-- The right-chart relation is reflexive on idempotents. -/
theorem rightChartAbsorption_refl {P : B} (hP : P * P = P) :
    rightChartAbsorption P P := ⟨hP, hP⟩

/-- The right-chart relation is transitive, with its displayed absorption orientation. -/
theorem rightChartAbsorption_trans {P Q R : B} :
    rightChartAbsorption P Q → rightChartAbsorption Q R → rightChartAbsorption P R := by
  rintro ⟨hQP, hPQ⟩ ⟨hRQ, hQR⟩
  constructor
  · calc
      R * P = (R * Q) * P := by rw [hRQ]
      _ = R * (Q * P) := by rw [mul_assoc]
      _ = R * Q := by rw [hQP]
      _ = R := hRQ
  · calc
      P * R = (P * Q) * R := by rw [hPQ]
      _ = P * (Q * R) := by rw [mul_assoc]
      _ = P * Q := by rw [hQR]
      _ = P := hPQ

/-- Forward and backward affine idempotent charts from Peirce cones. -/
def affineChartPlus (P A : B) : B :=
  (1 + conePlus P A) * P * (1 - conePlus P A)

def affineChartMinus (P C : B) : B :=
  (1 + coneMinus P C) * P * (1 - coneMinus P C)

/-- The nine operator corners associated with three strata. -/
def threeStratumCorners (E F G X : B) : B :=
  E * X * E + E * X * F + E * X * G +
  F * X * E + F * X * F + F * X * G +
  G * X * E + G * X * F + G * X * G

/-- The opposite-sign finite resolvent polynomial for a cubic-nilpotent step. -/
def cubicPlusResolvent (W : B) : B := 1 - W + W * W

/-- Two-sided absorption is reflexive on idempotents. -/
theorem idempotentAbsorbed_refl {P : B} (hP : P * P = P) :
    idempotentAbsorbed P P := ⟨hP, hP⟩

/-- Two-sided absorption is antisymmetric. -/
theorem idempotentAbsorbed_antisymm {P Q : B} :
    idempotentAbsorbed P Q → idempotentAbsorbed Q P → P = Q := by
  rintro ⟨hPQ, _⟩ ⟨_, hQP⟩
  calc
    P = P * Q := hPQ.symm
    _ = Q := hQP

/-- Two-sided absorption is transitive. -/
theorem idempotentAbsorbed_trans {P Q R : B} :
    idempotentAbsorbed P Q → idempotentAbsorbed Q R → idempotentAbsorbed P R := by
  rintro ⟨hPQ, hQP⟩ ⟨hQR, hRQ⟩
  constructor
  · calc
      P * R = (P * Q) * R := by rw [hPQ]
      _ = P * (Q * R) := by rw [mul_assoc]
      _ = P * Q := by rw [hQR]
      _ = P := hPQ
  · calc
      R * P = R * (Q * P) := by rw [hQP]
      _ = (R * Q) * P := by rw [← mul_assoc]
      _ = Q * P := by rw [hRQ]
      _ = P := hQP

/-- The carrier of idempotents in `B`, ordered by two-sided absorption below. -/
abbrev IdempotentCarrier (B : Type*) [Ring B] := {P : B // P * P = P}

instance : PartialOrder (IdempotentCarrier B) where
  le P Q := idempotentAbsorbed P.1 Q.1
  le_refl P := idempotentAbsorbed_refl P.2
  le_trans P Q R hPQ hQR := idempotentAbsorbed_trans hPQ hQR
  le_antisymm P Q hPQ hQP := Subtype.ext (idempotentAbsorbed_antisymm hPQ hQP)

/-- For idempotents, two-sided absorption is equivalent to commutation and
the one equation `P Q = P`. -/
theorem idempotentAbsorbed_iff_commute_and_mul
    {P Q : B} :
    idempotentAbsorbed P Q ↔ P * Q = Q * P ∧ P * Q = P := by
  constructor
  · rintro ⟨hPQ, hQP⟩
    exact ⟨hPQ.trans hQP.symm, hPQ⟩
  · rintro ⟨hComm, hPQ⟩
    exact ⟨hPQ, hComm.symm.trans hPQ⟩

/-- The relative difference of nested idempotents is idempotent and orthogonal to the smaller one. -/
theorem relative_idempotent_complement
    {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : idempotentAbsorbed P Q) :
    (Q - P) * (Q - P) = Q - P ∧
    P * (Q - P) = 0 ∧ (Q - P) * P = 0 ∧ P + (Q - P) = Q := by
  rcases hPQ with ⟨hPQ, hQP⟩
  have hSq : (Q - P) * (Q - P) = Q - P := by
    noncomm_ring [hP, hQ, hPQ, hQP]
  have hLeft : P * (Q - P) = 0 := by
    rw [mul_sub, hPQ, hP, sub_self]
  have hRight : (Q - P) * P = 0 := by
    rw [sub_mul, hQP, hP, sub_self]
  exact ⟨hSq, hLeft, hRight, by abel⟩

/-- The forward affine chart has left-chart absorption; its displacement is the square-zero upper cone. -/
theorem affineChartPlus_absorption
    {P : B} (hP : P * P = P) (A : B) :
    leftChartAbsorption P (affineChartPlus P A) ∧
    P - affineChartPlus P A = conePlus P A ∧
    conePlus P A * conePlus P A = 0 := by
  have hChart : affineChartPlus P A = P - conePlus P A := by
    unfold affineChartPlus
    peirce_nf hP
  have hN2 : conePlus P A * conePlus P A = 0 := by peirce_nf hP
  refine ⟨?_, ?_, hN2⟩
  · unfold leftChartAbsorption
    rw [hChart]
    constructor <;> peirce_nf hP
  · rw [hChart]
    abel

/-- The backward affine chart has right-chart absorption; its displacement is the square-zero lower cone. -/
theorem affineChartMinus_absorption
    {P : B} (hP : P * P = P) (C : B) :
    rightChartAbsorption P (affineChartMinus P C) ∧
    affineChartMinus P C - P = coneMinus P C ∧
    coneMinus P C * coneMinus P C = 0 := by
  have hChart : affineChartMinus P C = P + coneMinus P C := by
    unfold affineChartMinus
    peirce_nf hP
  have hN2 : coneMinus P C * coneMinus P C = 0 := by peirce_nf hP
  refine ⟨?_, ?_, hN2⟩
  · unfold rightChartAbsorption
    rw [hChart]
    constructor <;> peirce_nf hP
  · rw [hChart]
    abel

/-- A nested pair yields the orthogonal middle stratum used by the existing three-layer flag and root-space theorems. -/
theorem nested_idempotents_middle_stratum
    {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : idempotentAbsorbed P Q) :
    (Q - P) * (Q - P) = Q - P ∧
    P * (Q - P) = 0 ∧ (Q - P) * P = 0 ∧
    P + (Q - P) + (1 - Q) = 1 := by
  rcases relative_idempotent_complement hP hQ hPQ with
    ⟨hE, hPE, hEP, hSum⟩
  refine ⟨hE, hPE, hEP, ?_⟩
  rw [hSum]
  abel

/-- Expanding `1 = E + F + G` on both sides decomposes every operator into
its nine noncommutative source/target corners. No commutativity is assumed. -/
theorem threeStratumCorners_eq_of_partition (E F G X : B)
    (hPart : E + F + G = 1) :
    threeStratumCorners E F G X = X := by
  unfold threeStratumCorners
  calc
    E * X * E + E * X * F + E * X * G +
        F * X * E + F * X * F + F * X * G +
        G * X * E + G * X * F + G * X * G =
      (E + F + G) * X * (E + F + G) := by noncomm_ring
    _ = X := by rw [hPart]; simp

/-- The nested idempotent pair gives a complete three-stratum corner
decomposition with `E = P`, `F = Q - P`, and `G = 1 - Q`. -/
theorem nested_idempotents_threeStratumCorners
    {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : idempotentAbsorbed P Q) (X : B) :
    threeStratumCorners P (Q - P) (1 - Q) X = X := by
  have hPartition : P + (Q - P) + (1 - Q) = 1 := by
    rcases relative_idempotent_complement hP hQ hPQ with ⟨_, _, _, hSum⟩
    rw [hSum]
    abel
  exact threeStratumCorners_eq_of_partition P (Q - P) (1 - Q) X hPartition

/-- For the existing three-layer transition `W = dagEdge2`, cubic
nilpotency also gives the two-sided polynomial inverse of `1 + W`. -/
theorem ranked_dag_three_layer_plus_resolvent
    {P₁ P₂ : B} (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) (A C : B) :
    (1 + dagEdge2 P₁ P₂ A C) * cubicPlusResolvent (dagEdge2 P₁ P₂ A C) = 1 ∧
    cubicPlusResolvent (dagEdge2 P₁ P₂ A C) * (1 + dagEdge2 P₁ P₂ A C) = 1 := by
  rcases ranked_dag_three_layer_resolvent h1 h2 h12 h21 A C with ⟨_, hCube, _, _⟩
  constructor
  · unfold cubicPlusResolvent
    calc
      (1 + dagEdge2 P₁ P₂ A C) *
          (1 - dagEdge2 P₁ P₂ A C + dagEdge2 P₁ P₂ A C * dagEdge2 P₁ P₂ A C) =
        1 + dagEdge2 P₁ P₂ A C * dagEdge2 P₁ P₂ A C * dagEdge2 P₁ P₂ A C := by
          noncomm_ring
      _ = 1 := by rw [hCube]; simp
  · unfold cubicPlusResolvent
    calc
      (1 - dagEdge2 P₁ P₂ A C + dagEdge2 P₁ P₂ A C * dagEdge2 P₁ P₂ A C) *
          (1 + dagEdge2 P₁ P₂ A C) =
        1 + dagEdge2 P₁ P₂ A C * dagEdge2 P₁ P₂ A C * dagEdge2 P₁ P₂ A C := by
          noncomm_ring
      _ = 1 := by rw [hCube]; simp

end InfoGeometry.OperatorAlgebra.PeirceSpine
