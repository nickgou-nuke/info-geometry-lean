/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import InfoGeometry.Canonical.SouriauKaluzaJanusBimetricPoset

/-!
# Archetypes $\mathcal{J}_0$–$\mathcal{J}_3$: Non-Commutative Souriau Moment Maps, Kaluza–Janus Extensions & Bimetric Operator Systems

Pure non-commutative matrix/operator algebra over an arbitrary associative ring `[Ring B]`
(with `[StarRing B]` for the Hermitian Souriau moment torsor congruence in $\mathcal{J}_0$).
Zero axioms, zero `sorry`, and zero commutative or scalar-toy reductions.

Causal poset: $\mathcal{J}_0 \prec \mathcal{J}_1 \prec \mathcal{J}_2 \prec \mathcal{J}_3$,
connected directly to [`InfoGeometry.Canonical.SouriauKaluzaJanusBimetricPoset`](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauKaluzaJanusBimetricPoset.lean).
-/

namespace InfoGeometry.Archetypes.SouriauKaluzaJanusBimetric

open InfoGeometry.Canonical.SouriauKaluzaJanusBimetricPoset

/-! -----------------------------------------------------------------------
    1. 2×2 NON-COMMUTATIVE MATRIX RING (ARCHETYPES J₀ AND J₃)
    ----------------------------------------------------------------------- -/

/-- Explicit $2 \times 2$ matrix carrier over a non-commutative ring `B`. -/
@[ext]
structure SKJBMat2 (B : Type*) where
  a11 : B
  a12 : B
  a21 : B
  a22 : B
  deriving DecidableEq, Repr, Inhabited

section Mat2Operations

variable {B : Type*} [Ring B]

@[simp] def SKJBZero2 : SKJBMat2 B := ⟨0, 0, 0, 0⟩
instance instZeroSKJBMat2 : Zero (SKJBMat2 B) := ⟨SKJBZero2⟩

@[simp] lemma zero2_a11 : (0 : SKJBMat2 B).a11 = 0 := rfl
@[simp] lemma zero2_a12 : (0 : SKJBMat2 B).a12 = 0 := rfl
@[simp] lemma zero2_a21 : (0 : SKJBMat2 B).a21 = 0 := rfl
@[simp] lemma zero2_a22 : (0 : SKJBMat2 B).a22 = 0 := rfl

@[simp] def SKJBOne2 : SKJBMat2 B := ⟨1, 0, 0, 1⟩
instance instOneSKJBMat2 : One (SKJBMat2 B) := ⟨SKJBOne2⟩

@[simp] lemma one2_a11 : (1 : SKJBMat2 B).a11 = 1 := rfl
@[simp] lemma one2_a12 : (1 : SKJBMat2 B).a12 = 0 := rfl
@[simp] lemma one2_a21 : (1 : SKJBMat2 B).a21 = 0 := rfl
@[simp] lemma one2_a22 : (1 : SKJBMat2 B).a22 = 1 := rfl

@[simp] def SKJBAdd2 (X Y : SKJBMat2 B) : SKJBMat2 B :=
  ⟨X.a11 + Y.a11, X.a12 + Y.a12, X.a21 + Y.a21, X.a22 + Y.a22⟩
instance instAddSKJBMat2 : Add (SKJBMat2 B) := ⟨SKJBAdd2⟩

@[simp] lemma add2_a11 (X Y : SKJBMat2 B) : (X + Y).a11 = X.a11 + Y.a11 := rfl
@[simp] lemma add2_a12 (X Y : SKJBMat2 B) : (X + Y).a12 = X.a12 + Y.a12 := rfl
@[simp] lemma add2_a21 (X Y : SKJBMat2 B) : (X + Y).a21 = X.a21 + Y.a21 := rfl
@[simp] lemma add2_a22 (X Y : SKJBMat2 B) : (X + Y).a22 = X.a22 + Y.a22 := rfl

@[simp] def SKJBSub2 (X Y : SKJBMat2 B) : SKJBMat2 B :=
  ⟨X.a11 - Y.a11, X.a12 - Y.a12, X.a21 - Y.a21, X.a22 - Y.a22⟩
instance instSubSKJBMat2 : Sub (SKJBMat2 B) := ⟨SKJBSub2⟩

@[simp] lemma sub2_a11 (X Y : SKJBMat2 B) : (X - Y).a11 = X.a11 - Y.a11 := rfl
@[simp] lemma sub2_a12 (X Y : SKJBMat2 B) : (X - Y).a12 = X.a12 - Y.a12 := rfl
@[simp] lemma sub2_a21 (X Y : SKJBMat2 B) : (X - Y).a21 = X.a21 - Y.a21 := rfl
@[simp] lemma sub2_a22 (X Y : SKJBMat2 B) : (X - Y).a22 = X.a22 - Y.a22 := rfl

@[simp] def SKJBNeg2 (X : SKJBMat2 B) : SKJBMat2 B :=
  ⟨-X.a11, -X.a12, -X.a21, -X.a22⟩
instance instNegSKJBMat2 : Neg (SKJBMat2 B) := ⟨SKJBNeg2⟩

@[simp] def SKJBMul2 (X Y : SKJBMat2 B) : SKJBMat2 B :=
  ⟨X.a11 * Y.a11 + X.a12 * Y.a21,
   X.a11 * Y.a12 + X.a12 * Y.a22,
   X.a21 * Y.a11 + X.a22 * Y.a21,
   X.a21 * Y.a12 + X.a22 * Y.a22⟩
instance instMulSKJBMat2 : Mul (SKJBMat2 B) := ⟨SKJBMul2⟩

@[simp] lemma mul2_a11 (X Y : SKJBMat2 B) : (X * Y).a11 = X.a11 * Y.a11 + X.a12 * Y.a21 := rfl
@[simp] lemma mul2_a12 (X Y : SKJBMat2 B) : (X * Y).a12 = X.a11 * Y.a12 + X.a12 * Y.a22 := rfl
@[simp] lemma mul2_a21 (X Y : SKJBMat2 B) : (X * Y).a21 = X.a21 * Y.a11 + X.a22 * Y.a21 := rfl
@[simp] lemma mul2_a22 (X Y : SKJBMat2 B) : (X * Y).a22 = X.a21 * Y.a12 + X.a22 * Y.a22 := rfl

@[simp] def SKJBTr2 (X : SKJBMat2 B) : B := X.a11 + X.a22

/-- Hermitian conjugate transpose on `SKJBMat2 B`. -/
@[simp] def SKJBConjTranspose2 [StarRing B] (X : SKJBMat2 B) : SKJBMat2 B :=
  ⟨star X.a11, star X.a21, star X.a12, star X.a22⟩

instance instStarSKJBMat2 [StarRing B] : Star (SKJBMat2 B) := ⟨SKJBConjTranspose2⟩

@[simp] lemma star2_a11 [StarRing B] (X : SKJBMat2 B) : (star X).a11 = star X.a11 := rfl
@[simp] lemma star2_a12 [StarRing B] (X : SKJBMat2 B) : (star X).a12 = star X.a21 := rfl
@[simp] lemma star2_a21 [StarRing B] (X : SKJBMat2 B) : (star X).a21 = star X.a12 := rfl
@[simp] lemma star2_a22 [StarRing B] (X : SKJBMat2 B) : (star X).a22 = star X.a22 := rfl

/-- Canonical embedding of `SKJBMat2 B` into `Matrix (Fin 2) (Fin 2) B`. -/
def toMatrix2 (X : SKJBMat2 B) : Matrix (Fin 2) (Fin 2) B :=
  !![X.a11, X.a12; X.a21, X.a22]

@[simp] def SKJBAffGroup (L C : B) : SKJBMat2 B := ⟨L, C, 0, 1⟩

@[simp] def SKJBAffInv (L_inv C : B) : SKJBMat2 B := ⟨L_inv, -(L_inv * C), 0, 1⟩

@[simp] def SKJBMomentTorsor [StarRing B] (M P : B) : SKJBMat2 B := ⟨M, -P, star P, 0⟩

@[simp] def SKJBKJanus2 (b1 b2 : B) : SKJBMat2 B := ⟨1, b1, -b2, -1⟩

@[simp] def SKJBAnnihilator2 (b2 : B) : SKJBMat2 B := ⟨b2, 1, 0, 0⟩

@[simp] def SKJBEz2 : SKJBMat2 B := ⟨1, 0, 0, -1⟩

@[simp] def SKJBStressSelf2 (ρ p : B) : SKJBMat2 B := ⟨ρ, 0, 0, -p⟩

@[simp] def SKJBStressInduced2 (ρ p : B) : SKJBMat2 B := ⟨ρ, 0, 0, p⟩

/-- Bridge connecting `SKJBAffGroup`, `SKJBKJanus2`, and `SKJBEz2` to the canonical
`Matrix (Fin 2) (Fin 2) B` operators in `SouriauKaluzaJanusBimetricPoset`. -/
theorem toMatrix2_bridges (L C b1 b2 : B) :
    toMatrix2 (SKJBAffGroup L C) = affGroup2 L C ∧
    toMatrix2 (SKJBKJanus2 b1 b2) = janusCoupling2 b1 b2 ∧
    toMatrix2 (SKJBEz2 (B := B)) = cartanEz2 :=
  ⟨rfl, rfl, rfl⟩

/-- **Archetype $\mathcal{J}_0$ (`SKJBSouriauPoincareMomentTorsorCongruence`)**:
Over any non-commutative `*`-ring `[Ring B] [StarRing B]`:
1. `SKJBAffGroup` satisfies the semidirect product law `(L₁, C₁) · (L₂, C₂) = (L₁ L₂, L₁ C₂ + C₁)`
   and two-sided inverse laws with `SKJBAffInv L_inv C` whenever `L_inv * L = 1` and `L * L_inv = 1`.
2. Hermitian congruence `G * Y * star G` of `SKJBMomentTorsor M P` by `G = SKJBAffGroup L C`
   transforms the angular moment `M` and momentum `P` by the exact non-commutative Souriau
   coadjoint action `M' = L * M * star L - L * P * star C + C * star (L * P)` and `P' = L * P`.
3. Pure translation (`L = 1`) shifts `M` by `-P * star C + C * star P`, while discrete inversion
   (`L = -1, C = 0`) reverses `P ↦ -P`. -/
theorem SKJBSouriauPoincareMomentTorsorCongruence
    {B : Type*} [Ring B] [StarRing B] (L1 C1 L2 C2 L L_inv C M P : B) :
    SKJBAffGroup L1 C1 * SKJBAffGroup L2 C2 = SKJBAffGroup (L1 * L2) (L1 * C2 + C1) ∧
    (L_inv * L = 1 → SKJBAffInv L_inv C * SKJBAffGroup L C = 1) ∧
    (L * L_inv = 1 → SKJBAffGroup L C * SKJBAffInv L_inv C = 1) ∧
    SKJBAffGroup L C * SKJBMomentTorsor M P * star (SKJBAffGroup L C) =
      SKJBMomentTorsor (L * M * star L - L * P * star C + C * star (L * P)) (L * P) ∧
    SKJBAffGroup 1 C * SKJBMomentTorsor M P * star (SKJBAffGroup 1 C) =
      SKJBMomentTorsor (M - P * star C + C * star P) P ∧
    SKJBAffGroup (-1 : B) 0 * SKJBMomentTorsor M P * star (SKJBAffGroup (-1 : B) 0) =
      SKJBMomentTorsor M (-P) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> (simp; try noncomm_ring)
  · intro hL
    ext <;> simp [hL]
  · intro hL
    ext
    · simpa using hL
    · simp
      calc
        -(L * (L_inv * C)) + C = -((L * L_inv) * C) + C := by noncomm_ring
        _ = -(1 * C) + C := by rw [hL]
        _ = 0 := by noncomm_ring
    · simp
    · simp
  · ext <;> (simp [star_mul]; try noncomm_ring)
  · ext <;> (simp; try noncomm_ring)
  · ext <;> simp

/-- **Archetype $\mathcal{J}_3$ (`SKJBBimetricCouplingNilpotencyConservationPressureFlip`)**:
Over any non-commutative ring `[Ring B]`:
1. The square of `SKJBKJanus2 b1 b2` is the diagonal Socratic aporia matrix
   `⟨1 - b1 * b2, 0, 0, 1 - b2 * b1⟩`, which vanishes identically when `b1 * b2 = 1` and `b2 * b1 = 1`.
2. The trace `SKJBTr2 (SKJBKJanus2 b1 b2)` vanishes identically.
3. The coupled Bianchi identity defect is `(b2 * b1 - 1) * T_minus`, which vanishes when `b2 * b1 = 1`.
4. Left multiplication by the Cartan grading involution `SKJBEz2` flips the pressure sign between
   `SKJBStressSelf2 ρ p` and `SKJBStressInduced2 ρ p`. -/
theorem SKJBBimetricCouplingNilpotencyConservationPressureFlip
    {B : Type*} [Ring B] (b1 b2 T_plus T_minus ρ p : B) :
    SKJBKJanus2 b1 b2 * SKJBKJanus2 b1 b2 = ⟨1 - b1 * b2, 0, 0, 1 - b2 * b1⟩ ∧
    (b1 * b2 = 1 → b2 * b1 = 1 → SKJBKJanus2 b1 b2 * SKJBKJanus2 b1 b2 = 0) ∧
    SKJBTr2 (SKJBKJanus2 b1 b2) = 0 ∧
    b2 * (T_plus + b1 * T_minus) + (-(b2 * T_plus) - T_minus) = (b2 * b1 - 1) * T_minus ∧
    (b2 * b1 = 1 → b2 * (T_plus + b1 * T_minus) + (-(b2 * T_plus) - T_minus) = 0) ∧
    SKJBEz2 * SKJBStressSelf2 ρ p = SKJBStressInduced2 ρ p ∧
    SKJBStressSelf2 ρ p + SKJBStressInduced2 ρ p = ⟨ρ + ρ, 0, 0, 0⟩ ∧
    SKJBStressSelf2 ρ p - SKJBStressInduced2 ρ p = ⟨0, 0, 0, -(p + p)⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext <;> (simp; try noncomm_ring)
  · intro h12 h21
    ext <;> simp [h12, h21]
  · simp
  · noncomm_ring
  · intro h21
    calc
      b2 * (T_plus + b1 * T_minus) + (-(b2 * T_plus) - T_minus) =
        (b2 * b1 - 1) * T_minus := by noncomm_ring
      _ = (1 - 1) * T_minus := by rw [h21]
      _ = 0 := by noncomm_ring
  · ext <;> simp
  · ext <;> simp
  · ext <;> (simp; try noncomm_ring)

end Mat2Operations

/-! -----------------------------------------------------------------------
    2. 3×3 NON-COMMUTATIVE MATRIX RING (ARCHETYPES J₁ AND J₂)
    ----------------------------------------------------------------------- -/

/-- Explicit $3 \times 3$ matrix carrier over a non-commutative ring `B`. -/
@[ext]
structure SKJBMat3 (B : Type*) where
  a11 : B
  a12 : B
  a13 : B
  a21 : B
  a22 : B
  a23 : B
  a31 : B
  a32 : B
  a33 : B
  deriving DecidableEq, Repr, Inhabited

section Mat3Operations

variable {B : Type*} [Ring B]

@[simp] def SKJBZero3 : SKJBMat3 B := ⟨0,0,0, 0,0,0, 0,0,0⟩
instance instZeroSKJBMat3 : Zero (SKJBMat3 B) := ⟨SKJBZero3⟩

@[simp] lemma zero3_a11 : (0 : SKJBMat3 B).a11 = 0 := rfl
@[simp] lemma zero3_a12 : (0 : SKJBMat3 B).a12 = 0 := rfl
@[simp] lemma zero3_a13 : (0 : SKJBMat3 B).a13 = 0 := rfl
@[simp] lemma zero3_a21 : (0 : SKJBMat3 B).a21 = 0 := rfl
@[simp] lemma zero3_a22 : (0 : SKJBMat3 B).a22 = 0 := rfl
@[simp] lemma zero3_a23 : (0 : SKJBMat3 B).a23 = 0 := rfl
@[simp] lemma zero3_a31 : (0 : SKJBMat3 B).a31 = 0 := rfl
@[simp] lemma zero3_a32 : (0 : SKJBMat3 B).a32 = 0 := rfl
@[simp] lemma zero3_a33 : (0 : SKJBMat3 B).a33 = 0 := rfl

@[simp] def SKJBOne3 : SKJBMat3 B := ⟨1,0,0, 0,1,0, 0,0,1⟩
instance instOneSKJBMat3 : One (SKJBMat3 B) := ⟨SKJBOne3⟩

@[simp] lemma one3_a11 : (1 : SKJBMat3 B).a11 = 1 := rfl
@[simp] lemma one3_a12 : (1 : SKJBMat3 B).a12 = 0 := rfl
@[simp] lemma one3_a13 : (1 : SKJBMat3 B).a13 = 0 := rfl
@[simp] lemma one3_a21 : (1 : SKJBMat3 B).a21 = 0 := rfl
@[simp] lemma one3_a22 : (1 : SKJBMat3 B).a22 = 1 := rfl
@[simp] lemma one3_a23 : (1 : SKJBMat3 B).a23 = 0 := rfl
@[simp] lemma one3_a31 : (1 : SKJBMat3 B).a31 = 0 := rfl
@[simp] lemma one3_a32 : (1 : SKJBMat3 B).a32 = 0 := rfl
@[simp] lemma one3_a33 : (1 : SKJBMat3 B).a33 = 1 := rfl

@[simp] def SKJBMul3 (X Y : SKJBMat3 B) : SKJBMat3 B :=
  ⟨X.a11 * Y.a11 + X.a12 * Y.a21 + X.a13 * Y.a31,
   X.a11 * Y.a12 + X.a12 * Y.a22 + X.a13 * Y.a32,
   X.a11 * Y.a13 + X.a12 * Y.a23 + X.a13 * Y.a33,
   X.a21 * Y.a11 + X.a22 * Y.a21 + X.a23 * Y.a31,
   X.a21 * Y.a12 + X.a22 * Y.a22 + X.a23 * Y.a32,
   X.a21 * Y.a13 + X.a22 * Y.a23 + X.a23 * Y.a33,
   X.a31 * Y.a11 + X.a32 * Y.a21 + X.a33 * Y.a31,
   X.a31 * Y.a12 + X.a32 * Y.a22 + X.a33 * Y.a32,
   X.a31 * Y.a13 + X.a32 * Y.a23 + X.a33 * Y.a33⟩
instance instMulSKJBMat3 : Mul (SKJBMat3 B) := ⟨SKJBMul3⟩

@[simp] lemma mul3_a11 (X Y : SKJBMat3 B) :
    (X * Y).a11 = X.a11 * Y.a11 + X.a12 * Y.a21 + X.a13 * Y.a31 := rfl
@[simp] lemma mul3_a12 (X Y : SKJBMat3 B) :
    (X * Y).a12 = X.a11 * Y.a12 + X.a12 * Y.a22 + X.a13 * Y.a32 := rfl
@[simp] lemma mul3_a13 (X Y : SKJBMat3 B) :
    (X * Y).a13 = X.a11 * Y.a13 + X.a12 * Y.a23 + X.a13 * Y.a33 := rfl
@[simp] lemma mul3_a21 (X Y : SKJBMat3 B) :
    (X * Y).a21 = X.a21 * Y.a11 + X.a22 * Y.a21 + X.a23 * Y.a31 := rfl
@[simp] lemma mul3_a22 (X Y : SKJBMat3 B) :
    (X * Y).a22 = X.a21 * Y.a12 + X.a22 * Y.a22 + X.a23 * Y.a32 := rfl
@[simp] lemma mul3_a23 (X Y : SKJBMat3 B) :
    (X * Y).a23 = X.a21 * Y.a13 + X.a22 * Y.a23 + X.a23 * Y.a33 := rfl
@[simp] lemma mul3_a31 (X Y : SKJBMat3 B) :
    (X * Y).a31 = X.a31 * Y.a11 + X.a32 * Y.a21 + X.a33 * Y.a31 := rfl
@[simp] lemma mul3_a32 (X Y : SKJBMat3 B) :
    (X * Y).a32 = X.a31 * Y.a12 + X.a32 * Y.a22 + X.a33 * Y.a32 := rfl
@[simp] lemma mul3_a33 (X Y : SKJBMat3 B) :
    (X * Y).a33 = X.a31 * Y.a13 + X.a32 * Y.a23 + X.a33 * Y.a33 := rfl

@[simp] def SKJBTr3 (X : SKJBMat3 B) : B := X.a11 + X.a22 + X.a33

/-- Canonical embedding of `SKJBMat3 B` into `Matrix (Fin 3) (Fin 3) B`. -/
def toMatrix3 (X : SKJBMat3 B) : Matrix (Fin 3) (Fin 3) B :=
  !![X.a11, X.a12, X.a13; X.a21, X.a22, X.a23; X.a31, X.a32, X.a33]

@[simp] def SKJBJanusGroup (χ φ L C : B) : SKJBMat3 B :=
  ⟨χ, 0, φ,
   0, L, C,
   0, 0, 1⟩

@[simp] def SKJBJanusInv (χ_inv φ L_inv C : B) : SKJBMat3 B :=
  ⟨χ_inv, 0, -(χ_inv * φ),
   0, L_inv, -(L_inv * C),
   0, 0, 1⟩

@[simp] def SKJBJanusLie (Ω γ δφ : B) : SKJBMat3 B :=
  ⟨0, 0, δφ,
   0, Ω, γ,
   0, 0, 0⟩

@[simp] def SKJBJanusDualMoment (M P q : B) : SKJBMat3 B :=
  ⟨0, 0, 0,
   0, M, 0,
   q, P, 0⟩

/-- Bridge connecting `SKJBJanusGroup`, `SKJBJanusInv`, `SKJBJanusLie`, and `SKJBJanusDualMoment`
to the canonical `Matrix (Fin 3) (Fin 3) B` operators in `SouriauKaluzaJanusBimetricPoset`. -/
theorem toMatrix3_bridges (χ χ_inv φ L L_inv C Ω γ δφ M P q : B) :
    toMatrix3 (SKJBJanusGroup χ φ L C) = janusGroup3 χ φ L C ∧
    toMatrix3 (SKJBJanusInv χ_inv φ L_inv C) = janusInv3 χ_inv φ L_inv C ∧
    toMatrix3 (SKJBJanusLie Ω γ δφ) = janusLie3 Ω γ δφ ∧
    toMatrix3 (SKJBJanusDualMoment M P q) = janusDualMoment3 M P q :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Archetype $\mathcal{J}_1$ (`SKJBKaluzaJanusGroupAndLieAdjointAction`)**:
Over any non-commutative ring `[Ring B]`:
1. `SKJBJanusGroup` satisfies the double semidirect product law
   `(χ₁, φ₁, L₁, C₁) · (χ₂, φ₂, L₂, C₂) = (χ₁ χ₂, χ₁ φ₂ + φ₁, L₁ L₂, L₁ C₂ + C₁)`
   and two-sided inverse laws with `SKJBJanusInv χ_inv φ L_inv C`.
2. Adjoint conjugation `G⁻¹ * Z * G` of `SKJBJanusLie Ω γ δφ` transforms the Lie algebra
   generators by `Ω ↦ L_inv * Ω * L`, `γ ↦ L_inv * Ω * C + L_inv * γ`, and `δφ ↦ χ_inv * δφ`,
   completely independent of the fifth-coordinate gauge translation `φ`.
3. The translation/gauge radical `SKJBJanusLie 0 γ δφ` is 2-step nilpotent (`Z² = 0`). -/
theorem SKJBKaluzaJanusGroupAndLieAdjointAction
    {B : Type*} [Ring B] (χ1 φ1 L1 C1 χ2 φ2 L2 C2 χ χ_inv φ L L_inv C Ω γ δφ : B) :
    SKJBJanusGroup χ1 φ1 L1 C1 * SKJBJanusGroup χ2 φ2 L2 C2 =
      SKJBJanusGroup (χ1 * χ2) (χ1 * φ2 + φ1) (L1 * L2) (L1 * C2 + C1) ∧
    (χ_inv * χ = 1 → L_inv * L = 1 →
      SKJBJanusInv χ_inv φ L_inv C * SKJBJanusGroup χ φ L C = 1) ∧
    (χ * χ_inv = 1 → L * L_inv = 1 →
      SKJBJanusGroup χ φ L C * SKJBJanusInv χ_inv φ L_inv C = 1) ∧
    SKJBJanusInv χ_inv φ L_inv C * SKJBJanusLie Ω γ δφ * SKJBJanusGroup χ φ L C =
      SKJBJanusLie (L_inv * Ω * L) (L_inv * Ω * C + L_inv * γ) (χ_inv * δφ) ∧
    SKJBJanusLie 0 γ δφ * SKJBJanusLie 0 γ δφ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext <;> simp
  · intro hχ hL
    ext <;> simp [hχ, hL]
  · intro hχ hL
    ext
    · simpa using hχ
    · simp
    · simp
      calc
        -(χ * (χ_inv * φ)) + φ = -((χ * χ_inv) * φ) + φ := by noncomm_ring
        _ = -(1 * φ) + φ := by rw [hχ]
        _ = 0 := by noncomm_ring
    · simp
    · simpa using hL
    · simp
      calc
        -(L * (L_inv * C)) + C = -((L * L_inv) * C) + C := by noncomm_ring
        _ = -(1 * C) + C := by rw [hL]
        _ = 0 := by noncomm_ring
    · simp
    · simp
    · simp
  · ext <;> simp
  · ext <;> simp

/-- **Archetype $\mathcal{J}_2$ (`SKJBSouriauNoetherPairingInvariance`)**:
Over any non-commutative ring `[Ring B]`:
1. The matrix trace `SKJBTr3 (SKJBJanusDualMoment M P q * SKJBJanusLie Ω γ δφ)` equals the
   non-commutative Souriau–Noether bilinear pairing `M * Ω + P * γ + q * δφ`.
2. Coadjoint conjugation `SKJBJanusInv χ_inv φ L_inv C * SKJBJanusDualMoment M P q * SKJBJanusGroup χ φ L C`
   transforms the charge sector `(3,1)` as `q * χ`, momentum sector `(3,2)` as `P * L`, and
   Lorentz moment sector `(2,2)` as `L_inv * M * L - L_inv * C * P * L`.
3. Under pure translation `C` and charge reflection `χ * χ_inv = 1` (`L = L_inv = 1`), the
   contragredient Souriau–Noether pairing equals `(M * Ω + P * γ + q * δφ) + P * (Ω * C - C * Ω)`. -/
theorem SKJBSouriauNoetherPairingInvariance
    {B : Type*} [Ring B] (M P q Ω γ δφ χ χ_inv φ L L_inv C : B) :
    SKJBTr3 (SKJBJanusDualMoment M P q * SKJBJanusLie Ω γ δφ) =
      M * Ω + P * γ + q * δφ ∧
    (SKJBJanusInv χ_inv φ L_inv C * SKJBJanusDualMoment M P q * SKJBJanusGroup χ φ L C).a31 =
      q * χ ∧
    (SKJBJanusInv χ_inv φ L_inv C * SKJBJanusDualMoment M P q * SKJBJanusGroup χ φ L C).a32 =
      P * L ∧
    (SKJBJanusInv χ_inv φ L_inv C * SKJBJanusDualMoment M P q * SKJBJanusGroup χ φ L C).a22 =
      L_inv * M * L - L_inv * C * P * L ∧
    (χ * χ_inv = 1 →
      SKJBTr3
        (SKJBJanusDualMoment (M - P * C) P (q * χ) *
          (SKJBJanusInv χ_inv φ 1 C * SKJBJanusLie Ω γ δφ * SKJBJanusGroup χ φ 1 C)) =
        (M * Ω + P * γ + q * δφ) + P * (Ω * C - C * Ω)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp
    abel
  · simp
  · simp
  · simp
    noncomm_ring
  · intro hχ
    simp
    calc
      (M - P * C) * Ω + (q * χ * (χ_inv * δφ) + P * (Ω * C + γ)) =
        (M - P * C) * Ω + P * (Ω * C + γ) + q * (χ * χ_inv) * δφ := by noncomm_ring
      _ = (M - P * C) * Ω + P * (Ω * C + γ) + q * 1 * δφ := by rw [hχ]
      _ = M * Ω + P * γ + q * δφ + P * (Ω * C - C * Ω) := by noncomm_ring

/-- **Trap T16 Witness (`SKJBMat2_noncommutative`)**:
Over any nontrivial ring `[Ring B] [Nontrivial B]`, `SKJBMat2 B` is strictly non-commutative. -/
theorem SKJBMat2_noncommutative [Nontrivial B] :
    (⟨0, 1, 0, 0⟩ : SKJBMat2 B) * ⟨0, 0, 1, 0⟩ ≠
      (⟨0, 0, 1, 0⟩ : SKJBMat2 B) * ⟨0, 1, 0, 0⟩ := by
  intro h
  have h11 : ((⟨0, 1, 0, 0⟩ : SKJBMat2 B) * ⟨0, 0, 1, 0⟩).a11 =
      ((⟨0, 0, 1, 0⟩ : SKJBMat2 B) * ⟨0, 1, 0, 0⟩).a11 := by
    rw [h]
  simp at h11

end Mat3Operations

end InfoGeometry.Archetypes.SouriauKaluzaJanusBimetric
