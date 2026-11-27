/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import InfoGeometry.Physics.NoncommutativeZornBdGDerivations
import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge

/-!
# Noncommutative Zorn Peirce Idempotents and Color/Grading Carrier Subspaces

This module formalizes the algebraic carrier structures associated with the
Standard Model color and hypercharge sectors within the Noncommutative
Split-Octonion Zorn Algebra $\operatorname{NCZorn}(A)$, bridging
`NoncommutativeZornBdGDerivations` to the Peirce-decomposed carrier subspaces:

1. **Vacuum Peirce Idempotent System**:
   - Canonical orthogonal vacuum projectors $P_1 = \operatorname{diag}(1, 0)$
     and $P_2 = \operatorname{diag}(0, 1)$ in $\operatorname{NCZorn}(A)$.
   - Idempotency: $P_1^2 = P_1, P_2^2 = P_2$.
   - Pairwise orthogonality: $P_1 P_2 = 0, P_2 P_1 = 0$.
   - Partition of unity: $P_1 + P_2 = \mathbb{1}_{\mathbb{O}_s}$.
   - Exact 4-term Peirce decomposition:
     $X = P_1 X P_1 + P_1 X P_2 + P_2 X P_1 + P_2 X P_2$.

2. **Derivation Stabilizer Equivalence & Peirce Block Invariance**:
   - A Zorn derivation $D \in \operatorname{Der}(\operatorname{NCZorn} A)$
     stabilizes the vacuum idempotent $P_1$ ($D(P_1) = 0$) if and only if
     it stabilizes $P_2$ ($D(P_2) = 0$), via $D(\mathbb{1}) = 0$.
   - Stabilizing derivations strictly preserve the four Peirce subspaces:
     - Color triplet subspace: $D(P_1 X P_2) = P_1 D(X) P_2$;
     - Color antitriplet subspace: $D(P_2 X P_1) = P_2 D(X) P_1$;
     - Vacuum scalar blocks: $D(P_1 X P_1) = P_1 D(X) P_1$ and
       $D(P_2 X P_2) = P_2 D(X) P_2$.

3. **Algebraic Invariants of the Triplet Sector**:
   - The product of two color triplets $(P_1 X P_2)(P_1 Y P_2)$ lands strictly
     in the antitriplet subspace $P_2 (\operatorname{NCZorn} A) P_1$ via the
     cross product $\mathbf{u} \times \mathbf{u}'$.
   - The pairing of a triplet and antitriplet $(P_1 X P_2)(P_2 Y P_1)$ lands
     strictly in the scalar block $P_1 (\operatorname{NCZorn} A) P_1$ via the
     dot product $\mathbf{u} \cdot \mathbf{v}$.
   - The algebraic invariance of the cross and dot products under vacuum-stabilizing
     derivations physically motivates their action as infinitesimal automorphisms
     of the color carrier $A^3$.

4. **Tripotent Grading Operator & Hypercharge $\mathfrak{u}(1)$ Sector**:
   - The canonical tripotent grading operator $\chi(X) = \langle 0, \mathbf{u}, -\mathbf{v}, 0 \rangle$.
   - Tripotent law: $\chi^3 = \chi$.
   - Eigenspace trisection into $+1$ (color $\mathbf{3}$), $-1$ (anticolor $\bar{\mathbf{3}}$),
     and $0$ (Cartan scalars).
   - Annihilation of the vacuum idempotents: $\chi(P_1) = 0$ and $\chi(P_2) = 0$.

5. **Master Synthesis Certificate**:
   - Data packet `ZornGaugeEmergenceCertificate` bundling all algebraic invariants.
-/

namespace InfoGeometry.Algebra.ZornGaugeEmergence

open InfoGeometry.Physics.NoncommutativeZornBdGDerivations

variable {A : Type*} [Ring A]

/-! ### 1. Vacuum Peirce Idempotent System -/

section VacuumIdempotents

/-- First vacuum Peirce projector $P_1 = \operatorname{diag}(1, 0) \in \operatorname{NCZorn}(A)$. -/
def vacuumP1 : NCZorn A where
  a := 1
  u := fun _ => 0
  v := fun _ => 0
  b := 0

/-- Second vacuum Peirce projector $P_2 = \operatorname{diag}(0, 1) \in \operatorname{NCZorn}(A)$. -/
def vacuumP2 : NCZorn A where
  a := 0
  u := fun _ => 0
  v := fun _ => 0
  b := 1

/-- $P_1^2 = P_1$. -/
@[simp]
theorem vacuumP1_sq : (vacuumP1 : NCZorn A) * vacuumP1 = vacuumP1 := by
  apply NCZorn.ext
  · change 1 * 1 + dotNC (fun _ => (0 : A)) (fun _ => 0) = 1
    simp [dotNC]
  · ext i
    change 1 * (0 : A) + (0 : A) * 0 - crossNC (fun _ => (0 : A)) (fun _ => 0) i = 0
    simp
  · ext i
    change (0 : A) * 1 + 0 * (0 : A) + crossNC (fun _ => (0 : A)) (fun _ => 0) i = 0
    simp
  · change 0 * 0 + dotNC (fun _ => (0 : A)) (fun _ => 0) = 0
    simp [dotNC]

/-- $P_2^2 = P_2$. -/
@[simp]
theorem vacuumP2_sq : (vacuumP2 : NCZorn A) * vacuumP2 = vacuumP2 := by
  apply NCZorn.ext
  · change 0 * 0 + dotNC (fun _ => (0 : A)) (fun _ => 0) = 0
    simp [dotNC]
  · ext i
    change 0 * (0 : A) + (0 : A) * 1 - crossNC (fun _ => (0 : A)) (fun _ => 0) i = 0
    simp
  · ext i
    change (0 : A) * 0 + 1 * (0 : A) + crossNC (fun _ => (0 : A)) (fun _ => 0) i = 0
    simp
  · change 1 * 1 + dotNC (fun _ => (0 : A)) (fun _ => 0) = 1
    simp [dotNC]

/-- $P_1 P_2 = 0$. -/
@[simp]
theorem vacuumP1_mul_vacuumP2 : (vacuumP1 : NCZorn A) * vacuumP2 = ncZornZero := by
  apply NCZorn.ext
  · change 1 * 0 + dotNC (fun _ => (0 : A)) (fun _ => 0) = 0
    simp [dotNC]
  · ext i
    change 1 * (0 : A) + (0 : A) * 1 - crossNC (fun _ => (0 : A)) (fun _ => 0) i = 0
    simp
  · ext i
    change (0 : A) * 0 + 0 * (0 : A) + crossNC (fun _ => (0 : A)) (fun _ => 0) i = 0
    simp
  · change 0 * 1 + dotNC (fun _ => (0 : A)) (fun _ => 0) = 0
    simp [dotNC]

/-- $P_2 P_1 = 0$. -/
@[simp]
theorem vacuumP2_mul_vacuumP1 : (vacuumP2 : NCZorn A) * vacuumP1 = ncZornZero := by
  apply NCZorn.ext
  · change 0 * 1 + dotNC (fun _ => (0 : A)) (fun _ => 0) = 0
    simp [dotNC]
  · ext i
    change 0 * (0 : A) + (0 : A) * 0 - crossNC (fun _ => (0 : A)) (fun _ => 0) i = 0
    simp
  · ext i
    change (0 : A) * 1 + 1 * (0 : A) + crossNC (fun _ => (0 : A)) (fun _ => 0) i = 0
    simp
  · change 1 * 0 + dotNC (fun _ => (0 : A)) (fun _ => 0) = 0
    simp [dotNC]

/-- Partition of unity: $P_1 + P_2 = \mathbb{1}$. -/
@[simp]
theorem vacuumP1_add_vacuumP2 :
    ncZornAdd (vacuumP1 : NCZorn A) vacuumP2 = (1 : NCZorn A) := by
  apply NCZorn.ext
  · change 1 + 0 = 1; simp
  · ext i; change (0 : A) + 0 = 0; simp
  · ext i; change (0 : A) + 0 = 0; simp
  · change 0 + 1 = 1; simp

/-- Left multiplication by $P_1$ projects onto the top rows: $\langle a, \mathbf{u}, 0, 0 \rangle$. -/
theorem vacuumP1_mul (X : NCZorn A) :
    vacuumP1 * X = ⟨X.a, X.u, fun _ => 0, 0⟩ := by
  apply NCZorn.ext
  · change 1 * X.a + dotNC (fun _ => 0) X.v = X.a
    simp [dotNC]
  · ext i
    show 1 * X.u i + (0 : A) * X.b - crossNC (fun _ => 0) X.v i = X.u i
    simp [crossNC_zero_left]
  · ext i
    show (0 : A) * X.a + (0 : A) * X.v i + crossNC (fun _ => 0) X.u i = 0
    simp [crossNC_zero_left]
  · change 0 * X.b + dotNC (fun _ => 0) X.u = 0
    simp [dotNC]

/-- Left multiplication by $P_2$ projects onto the bottom rows: $\langle 0, 0, \mathbf{v}, b \rangle$. -/
theorem vacuumP2_mul (X : NCZorn A) :
    vacuumP2 * X = ⟨0, fun _ => 0, X.v, X.b⟩ := by
  apply NCZorn.ext
  · change 0 * X.a + dotNC (fun _ => 0) X.v = 0
    simp [dotNC]
  · ext i
    show 0 * X.u i + (0 : A) * X.b - crossNC (fun _ => 0) X.v i = 0
    simp [crossNC_zero_left]
  · ext i
    show (0 : A) * X.a + 1 * X.v i + crossNC (fun _ => 0) X.u i = X.v i
    simp [crossNC_zero_left]
  · change 1 * X.b + dotNC (fun _ => 0) X.u = X.b
    simp [dotNC]

/-- Peirce (1,1) block: $P_1 X P_1 = \langle a, 0, 0, 0 \rangle$. -/
theorem peirce_11 (X : NCZorn A) :
    (vacuumP1 * X) * vacuumP1 = ⟨X.a, fun _ => 0, fun _ => 0, 0⟩ := by
  rw [vacuumP1_mul]
  apply NCZorn.ext
  · change X.a * 1 + dotNC X.u (fun _ => 0) = X.a
    simp [dotNC]
  · ext i
    show X.a * (0 : A) + X.u i * 0 - crossNC (fun _ => 0) (fun _ => 0) i = 0
    simp
  · ext i
    show (0 : A) * 1 + (0 : A) * (0 : A) + crossNC X.u (fun _ => 0) i = 0
    simp [crossNC_zero_right]
  · change (0 : A) * 0 + dotNC (fun _ => 0) (fun _ => 0) = 0
    simp [dotNC]

/-- Peirce (1,2) block (Color Triplet): $P_1 X P_2 = \langle 0, \mathbf{u}, 0, 0 \rangle$. -/
theorem peirce_12 (X : NCZorn A) :
    (vacuumP1 * X) * vacuumP2 = ⟨0, X.u, fun _ => 0, 0⟩ := by
  rw [vacuumP1_mul]
  apply NCZorn.ext
  · change X.a * 0 + dotNC X.u (fun _ => 0) = 0
    simp [dotNC]
  · ext i
    show X.a * (0 : A) + X.u i * 1 - crossNC (fun _ => 0) (fun _ => 0) i = X.u i
    simp
  · ext i
    show (0 : A) * 0 + (0 : A) * (0 : A) + crossNC X.u (fun _ => 0) i = 0
    simp [crossNC_zero_right]
  · change (0 : A) * 1 + dotNC (fun _ => 0) (fun _ => 0) = 0
    simp [dotNC]

/-- Peirce (2,1) block (Color Antitriplet): $P_2 X P_1 = \langle 0, 0, \mathbf{v}, 0 \rangle$. -/
theorem peirce_21 (X : NCZorn A) :
    (vacuumP2 * X) * vacuumP1 = ⟨0, fun _ => 0, X.v, 0⟩ := by
  rw [vacuumP2_mul]
  apply NCZorn.ext
  · change 0 * 1 + dotNC (fun _ => 0) (fun _ => 0) = 0
    simp [dotNC]
  · ext i
    show 0 * (0 : A) + (0 : A) * 0 - crossNC X.v (fun _ => 0) i = 0
    simp [crossNC_zero_right]
  · ext i
    show X.v i * 1 + X.b * (0 : A) + crossNC (fun _ => 0) (fun _ => 0) i = X.v i
    simp
  · change X.b * 0 + dotNC X.v (fun _ => 0) = 0
    simp [dotNC]

/-- Peirce (2,2) block: $P_2 X P_2 = \langle 0, 0, 0, b \rangle$. -/
theorem peirce_22 (X : NCZorn A) :
    (vacuumP2 * X) * vacuumP2 = ⟨0, fun _ => 0, fun _ => 0, X.b⟩ := by
  rw [vacuumP2_mul]
  apply NCZorn.ext
  · change 0 * 0 + dotNC (fun _ => 0) (fun _ => 0) = 0
    simp [dotNC]
  · ext i
    show 0 * (0 : A) + (0 : A) * 1 - crossNC X.v (fun _ => 0) i = 0
    simp [crossNC_zero_right]
  · ext i
    show X.v i * 0 + X.b * (0 : A) + crossNC (fun _ => 0) (fun _ => 0) i = 0
    simp
  · change X.b * 1 + dotNC X.v (fun _ => 0) = X.b
    simp [dotNC]

/-- THEOREM: Full 4-term Peirce decomposition of any Zorn matrix $X$:
$X = P_1 X P_1 + P_1 X P_2 + P_2 X P_1 + P_2 X P_2$. -/
theorem zorn_peirce_decomposition (X : NCZorn A) :
    X = ncZornAdd (ncZornAdd (vacuumP1 * X * vacuumP1) (vacuumP1 * X * vacuumP2))
                  (ncZornAdd (vacuumP2 * X * vacuumP1) (vacuumP2 * X * vacuumP2)) := by
  rw [peirce_11, peirce_12, peirce_21, peirce_22]
  apply NCZorn.ext
  · change X.a = (X.a + 0) + (0 + 0); simp
  · ext i; change X.u i = (0 + X.u i) + (0 + 0); simp
  · ext i; change X.v i = (0 + 0) + (X.v i + 0); simp
  · change X.b = (0 + 0) + (0 + X.b); simp

end VacuumIdempotents

/-! ### 2. Derivation Stabilizer of Vacuum Idempotents -/

section DerivationStabilizer

/-- Predicate: A derivation $D$ stabilizes the vacuum idempotent $P_1$. -/
def StabilizesVacuum (D : ZornDerivation A) : Prop :=
  D.toFun vacuumP1 = ncZornZero

/-- Helper: An element whose sum with zero is zero. -/
theorem ncZorn_add_zero_left {X : NCZorn A} :
    ncZornAdd ncZornZero X = X := by
  apply NCZorn.ext <;> simp [ncZornAdd, ncZornZero]

theorem ncZorn_add_zero_right {X : NCZorn A} :
    ncZornAdd X ncZornZero = X := by
  apply NCZorn.ext <;> simp [ncZornAdd, ncZornZero]

/-- THEOREM: $D(P_1) = 0 \iff D(P_2) = 0$.
A derivation stabilizes $P_1$ if and only if it stabilizes $P_2$. -/
theorem stabilizes_vacuum_iff_P2 (D : ZornDerivation A) :
    StabilizesVacuum D ↔ D.toFun vacuumP2 = ncZornZero := by
  constructor
  · intro h1
    have hsum : D.toFun (ncZornAdd vacuumP1 vacuumP2) = D.toFun 1 := by
      rw [vacuumP1_add_vacuumP2]
    rw [D.map_add, derivation_annihilates_one] at hsum
    unfold StabilizesVacuum at h1
    rw [h1, ncZorn_add_zero_left] at hsum
    exact hsum
  · intro h2
    unfold StabilizesVacuum
    have hsum : D.toFun (ncZornAdd vacuumP1 vacuumP2) = D.toFun 1 := by
      rw [vacuumP1_add_vacuumP2]
    rw [D.map_add, derivation_annihilates_one] at hsum
    rw [h2, ncZorn_add_zero_right] at hsum
    exact hsum

/-- THEOREM: Peirce Triplet Invariance under Stabilizing Derivations.
When $D$ stabilizes the vacuum, the color triplet subspace $P_1 (\operatorname{NCZorn} A) P_2$
is strictly invariant under $D$. -/
theorem derivation_preserves_color_triplet (D : ZornDerivation A)
    (hD : StabilizesVacuum D) (X : NCZorn A) :
    (D.toFun (vacuumP1 * X * vacuumP2)).a = 0 ∧
    (D.toFun (vacuumP1 * X * vacuumP2)).b = 0 ∧
    (D.toFun (vacuumP1 * X * vacuumP2)).v = (fun _ => 0) := by
  have hP2 : D.toFun vacuumP2 = ncZornZero := (stabilizes_vacuum_iff_P2 D).mp hD
  have hP1 : D.toFun vacuumP1 = ncZornZero := hD
  have h_leib1 : D.toFun ((vacuumP1 * X) * vacuumP2) =
      ncZornAdd (D.toFun (vacuumP1 * X) * vacuumP2) ((vacuumP1 * X) * D.toFun vacuumP2) :=
    D.leibniz (vacuumP1 * X) vacuumP2
  rw [hP2] at h_leib1
  have h_mul_zero : (vacuumP1 * X) * (ncZornZero : NCZorn A) = ncZornZero := by
    apply NCZorn.ext
    · change (vacuumP1 * X).a * 0 + dotNC (vacuumP1 * X).u (fun _ => 0) = 0; simp [dotNC]
    · ext i
      show (vacuumP1 * X).a * 0 + (vacuumP1 * X).u i * 0 - crossNC (vacuumP1 * X).v (fun _ => 0) i = 0
      simp [crossNC_zero_right]
    · ext i
      show (vacuumP1 * X).v i * 0 + (vacuumP1 * X).b * 0 + crossNC (vacuumP1 * X).u (fun _ => 0) i = 0
      simp [crossNC_zero_right]
    · change (vacuumP1 * X).b * 0 + dotNC (vacuumP1 * X).v (fun _ => 0) = 0; simp [dotNC]
  rw [h_mul_zero, ncZorn_add_zero_right] at h_leib1
  have h_leib2 : D.toFun (vacuumP1 * X) =
      ncZornAdd (D.toFun vacuumP1 * X) (vacuumP1 * D.toFun X) :=
    D.leibniz vacuumP1 X
  rw [hP1] at h_leib2
  have h_zero_mul : (ncZornZero : NCZorn A) * X = ncZornZero := by
    apply NCZorn.ext
    · change 0 * X.a + dotNC (fun _ => 0) X.v = 0; simp [dotNC]
    · ext i
      show 0 * X.u i + 0 * X.b - crossNC (fun _ => 0) X.v i = 0
      simp [crossNC_zero_left]
    · ext i
      show 0 * X.a + 0 * X.v i + crossNC (fun _ => 0) X.u i = 0
      simp [crossNC_zero_left]
    · change 0 * X.b + dotNC (fun _ => 0) X.u = 0; simp [dotNC]
  rw [h_zero_mul, ncZorn_add_zero_left] at h_leib2
  rw [h_leib2] at h_leib1
  have h_peirce := peirce_12 (D.toFun X)
  rw [h_leib1, h_peirce]
  refine ⟨rfl, rfl, rfl⟩

/-- THEOREM: Peirce Antitriplet Invariance under Stabilizing Derivations.
When $D$ stabilizes the vacuum, the color antitriplet subspace $P_2 (\operatorname{NCZorn} A) P_1$
is strictly invariant under $D$. -/
theorem derivation_preserves_color_antitriplet (D : ZornDerivation A)
    (hD : StabilizesVacuum D) (X : NCZorn A) :
    (D.toFun (vacuumP2 * X * vacuumP1)).a = 0 ∧
    (D.toFun (vacuumP2 * X * vacuumP1)).b = 0 ∧
    (D.toFun (vacuumP2 * X * vacuumP1)).u = (fun _ => 0) := by
  have hP2 : D.toFun vacuumP2 = ncZornZero := (stabilizes_vacuum_iff_P2 D).mp hD
  have hP1 : D.toFun vacuumP1 = ncZornZero := hD
  have h_leib1 : D.toFun ((vacuumP2 * X) * vacuumP1) =
      ncZornAdd (D.toFun (vacuumP2 * X) * vacuumP1) ((vacuumP2 * X) * D.toFun vacuumP1) :=
    D.leibniz (vacuumP2 * X) vacuumP1
  rw [hP1] at h_leib1
  have h_mul_zero : (vacuumP2 * X) * (ncZornZero : NCZorn A) = ncZornZero := by
    apply NCZorn.ext
    · change (vacuumP2 * X).a * 0 + dotNC (vacuumP2 * X).u (fun _ => 0) = 0; simp [dotNC]
    · ext i
      show (vacuumP2 * X).a * 0 + (vacuumP2 * X).u i * 0 - crossNC (vacuumP2 * X).v (fun _ => 0) i = 0
      simp [crossNC_zero_right]
    · ext i
      show (vacuumP2 * X).v i * 0 + (vacuumP2 * X).b * 0 + crossNC (vacuumP2 * X).u (fun _ => 0) i = 0
      simp [crossNC_zero_right]
    · change (vacuumP2 * X).b * 0 + dotNC (vacuumP2 * X).v (fun _ => 0) = 0; simp [dotNC]
  rw [h_mul_zero, ncZorn_add_zero_right] at h_leib1
  have h_leib2 : D.toFun (vacuumP2 * X) =
      ncZornAdd (D.toFun vacuumP2 * X) (vacuumP2 * D.toFun X) :=
    D.leibniz vacuumP2 X
  rw [hP2] at h_leib2
  have h_zero_mul : (ncZornZero : NCZorn A) * X = ncZornZero := by
    apply NCZorn.ext
    · change 0 * X.a + dotNC (fun _ => 0) X.v = 0; simp [dotNC]
    · ext i
      show 0 * X.u i + 0 * X.b - crossNC (fun _ => 0) X.v i = 0
      simp [crossNC_zero_left]
    · ext i
      show 0 * X.a + 0 * X.v i + crossNC (fun _ => 0) X.u i = 0
      simp [crossNC_zero_left]
    · change 0 * X.b + dotNC (fun _ => 0) X.u = 0; simp [dotNC]
  rw [h_zero_mul, ncZorn_add_zero_left] at h_leib2
  rw [h_leib2] at h_leib1
  have h_peirce := peirce_21 (D.toFun X)
  rw [h_leib1, h_peirce]
  refine ⟨rfl, rfl, rfl⟩

/-- THEOREM: Peirce (1,1) Scalar Block Invariance under Stabilizing Derivations. -/
theorem derivation_preserves_vacuum_p1_block (D : ZornDerivation A)
    (hD : StabilizesVacuum D) (X : NCZorn A) :
    (D.toFun (vacuumP1 * X * vacuumP1)).u = (fun _ => 0) ∧
    (D.toFun (vacuumP1 * X * vacuumP1)).v = (fun _ => 0) ∧
    (D.toFun (vacuumP1 * X * vacuumP1)).b = 0 := by
  have hP1 : D.toFun vacuumP1 = ncZornZero := hD
  have h_leib1 : D.toFun ((vacuumP1 * X) * vacuumP1) =
      ncZornAdd (D.toFun (vacuumP1 * X) * vacuumP1) ((vacuumP1 * X) * D.toFun vacuumP1) :=
    D.leibniz (vacuumP1 * X) vacuumP1
  rw [hP1] at h_leib1
  have h_mul_zero : (vacuumP1 * X) * (ncZornZero : NCZorn A) = ncZornZero := by
    apply NCZorn.ext
    · change (vacuumP1 * X).a * 0 + dotNC (vacuumP1 * X).u (fun _ => 0) = 0; simp [dotNC]
    · ext i; show (vacuumP1 * X).a * 0 + (vacuumP1 * X).u i * 0 - crossNC (vacuumP1 * X).v (fun _ => 0) i = 0; simp [crossNC_zero_right]
    · ext i; show (vacuumP1 * X).v i * 0 + (vacuumP1 * X).b * 0 + crossNC (vacuumP1 * X).u (fun _ => 0) i = 0; simp [crossNC_zero_right]
    · change (vacuumP1 * X).b * 0 + dotNC (vacuumP1 * X).v (fun _ => 0) = 0; simp [dotNC]
  rw [h_mul_zero, ncZorn_add_zero_right] at h_leib1
  have h_leib2 : D.toFun (vacuumP1 * X) =
      ncZornAdd (D.toFun vacuumP1 * X) (vacuumP1 * D.toFun X) :=
    D.leibniz vacuumP1 X
  rw [hP1] at h_leib2
  have h_zero_mul : (ncZornZero : NCZorn A) * X = ncZornZero := by
    apply NCZorn.ext
    · change 0 * X.a + dotNC (fun _ => 0) X.v = 0; simp [dotNC]
    · ext i; show 0 * X.u i + 0 * X.b - crossNC (fun _ => 0) X.v i = 0; simp [crossNC_zero_left]
    · ext i; show 0 * X.a + 0 * X.v i + crossNC (fun _ => 0) X.u i = 0; simp [crossNC_zero_left]
    · change 0 * X.b + dotNC (fun _ => 0) X.u = 0; simp [dotNC]
  rw [h_zero_mul, ncZorn_add_zero_left] at h_leib2
  rw [h_leib2] at h_leib1
  have h_peirce := peirce_11 (D.toFun X)
  rw [h_leib1, h_peirce]
  refine ⟨rfl, rfl, rfl⟩

/-- THEOREM: Peirce (2,2) Scalar Block Invariance under Stabilizing Derivations. -/
theorem derivation_preserves_vacuum_p2_block (D : ZornDerivation A)
    (hD : StabilizesVacuum D) (X : NCZorn A) :
    (D.toFun (vacuumP2 * X * vacuumP2)).a = 0 ∧
    (D.toFun (vacuumP2 * X * vacuumP2)).u = (fun _ => 0) ∧
    (D.toFun (vacuumP2 * X * vacuumP2)).v = (fun _ => 0) := by
  have hP2 : D.toFun vacuumP2 = ncZornZero := (stabilizes_vacuum_iff_P2 D).mp hD
  have h_leib1 : D.toFun ((vacuumP2 * X) * vacuumP2) =
      ncZornAdd (D.toFun (vacuumP2 * X) * vacuumP2) ((vacuumP2 * X) * D.toFun vacuumP2) :=
    D.leibniz (vacuumP2 * X) vacuumP2
  rw [hP2] at h_leib1
  have h_mul_zero : (vacuumP2 * X) * (ncZornZero : NCZorn A) = ncZornZero := by
    apply NCZorn.ext
    · change (vacuumP2 * X).a * 0 + dotNC (vacuumP2 * X).u (fun _ => 0) = 0; simp [dotNC]
    · ext i; show (vacuumP2 * X).a * 0 + (vacuumP2 * X).u i * 0 - crossNC (vacuumP2 * X).v (fun _ => 0) i = 0; simp [crossNC_zero_right]
    · ext i; show (vacuumP2 * X).v i * 0 + (vacuumP2 * X).b * 0 + crossNC (vacuumP2 * X).u (fun _ => 0) i = 0; simp [crossNC_zero_right]
    · change (vacuumP2 * X).b * 0 + dotNC (vacuumP2 * X).v (fun _ => 0) = 0; simp [dotNC]
  rw [h_mul_zero, ncZorn_add_zero_right] at h_leib1
  have h_leib2 : D.toFun (vacuumP2 * X) =
      ncZornAdd (D.toFun vacuumP2 * X) (vacuumP2 * D.toFun X) :=
    D.leibniz vacuumP2 X
  rw [hP2] at h_leib2
  have h_zero_mul : (ncZornZero : NCZorn A) * X = ncZornZero := by
    apply NCZorn.ext
    · change 0 * X.a + dotNC (fun _ => 0) X.v = 0; simp [dotNC]
    · ext i; show 0 * X.u i + 0 * X.b - crossNC (fun _ => 0) X.v i = 0; simp [crossNC_zero_left]
    · ext i; show 0 * X.a + 0 * X.v i + crossNC (fun _ => 0) X.u i = 0; simp [crossNC_zero_left]
    · change 0 * X.b + dotNC (fun _ => 0) X.u = 0; simp [dotNC]
  rw [h_zero_mul, ncZorn_add_zero_left] at h_leib2
  rw [h_leib2] at h_leib1
  have h_peirce := peirce_22 (D.toFun X)
  rw [h_leib1, h_peirce]
  refine ⟨rfl, rfl, rfl⟩

end DerivationStabilizer

/-! ### 3. Algebraic Invariants of the Triplet Sector -/

section TripletInvariants

/-- Extracting the color triplet from a Zorn matrix. -/
def extractTriplet (X : NCZorn A) : Fin 3 → A := X.u

/-- Extracting the color antitriplet from a Zorn matrix. -/
def extractAntitriplet (X : NCZorn A) : Fin 3 → A := X.v

/-- Embedding a color 3-vector into the Peirce (1,2) subspace: $\mathbf{u} \mapsto \begin{pmatrix} 0 & \mathbf{u} \\ 0 & 0 \end{pmatrix}$. -/
def embedTriplet (u : Fin 3 → A) : NCZorn A where
  a := 0
  u := u
  v := fun _ => 0
  b := 0

/-- Embedding an anticolor 3-vector into the Peirce (2,1) subspace: $\mathbf{v} \mapsto \begin{pmatrix} 0 & 0 \\ \mathbf{v} & 0 \end{pmatrix}$. -/
def embedAntitriplet (v : Fin 3 → A) : NCZorn A where
  a := 0
  u := fun _ => 0
  v := v
  b := 0

/-- THEOREM: The product of two color triplets lands strictly in the antitriplet subspace
via the non-commutative cross product:
$\mathbf{u}_1 \star \mathbf{u}_2 = \begin{pmatrix} 0 & 0 \\ \mathbf{u}_1 \times \mathbf{u}_2 & 0 \end{pmatrix}$. -/
theorem triplet_mul_triplet (u1 u2 : Fin 3 → A) :
    embedTriplet u1 * embedTriplet u2 = embedAntitriplet (crossNC u1 u2) := by
  apply NCZorn.ext
  · change 0 * 0 + dotNC u1 (fun _ => 0) = 0
    simp [dotNC]
  · ext i
    show 0 * u2 i + u1 i * 0 - crossNC (fun _ => 0) (fun _ => 0) i = 0
    simp
  · ext i
    show (0 : A) * 0 + 0 * (0 : A) + crossNC u1 u2 i = crossNC u1 u2 i
    simp
  · change 0 * 0 + dotNC (fun _ => 0) u2 = 0
    simp [dotNC]

/-- THEOREM: The pairing of a triplet and antitriplet lands strictly in the scalar diagonal
subspace via the non-commutative dot product:
$\mathbf{u} \star \mathbf{v} = \operatorname{diag}(\mathbf{u} \cdot \mathbf{v}, 0)$. -/
theorem triplet_mul_antitriplet (u v : Fin 3 → A) :
    embedTriplet u * embedAntitriplet v = ⟨dotNC u v, fun _ => 0, fun _ => 0, 0⟩ := by
  apply NCZorn.ext
  · change 0 * 0 + dotNC u v = dotNC u v; simp
  · ext i
    show 0 * (0 : A) + u i * 0 - crossNC (fun _ => 0) v i = 0
    simp [crossNC_zero_left]
  · ext i
    show (0 : A) * 0 + 0 * v i + crossNC u (fun _ => 0) i = 0
    simp [crossNC_zero_right]
  · change 0 * 0 + dotNC (fun _ => 0) (fun _ => 0) = 0
    simp [dotNC]

end TripletInvariants

/-! ### 4. Tripotent Grading Operator & Hypercharge $\mathfrak{u}(1)$ Sector -/

section TripotentGrading

/-- The tripotent grading operator $\chi : \operatorname{NCZorn}(A) \to \operatorname{NCZorn}(A)$
scaling the triplet $\mathbf{u}$ by $+1$, the antitriplet $\mathbf{v}$ by $-1$,
and annihilating the diagonal scalars. -/
def tripotentGrading (X : NCZorn A) : NCZorn A where
  a := 0
  u := X.u
  v := fun i => -X.v i
  b := 0

/-- Second power: $\chi^2(X) = \langle 0, \mathbf{u}, \mathbf{v}, 0 \rangle$. -/
theorem tripotentGrading_sq (X : NCZorn A) :
    tripotentGrading (tripotentGrading X) = ⟨0, X.u, X.v, 0⟩ := by
  apply NCZorn.ext
  · rfl
  · rfl
  · ext i; change -(-X.v i) = X.v i; simp
  · rfl

/-- THEOREM: Tripotency $\chi^3 = \chi$.
The grading operator satisfies $\chi(\chi(\chi(X))) = \chi(X)$ unconditionally. -/
theorem tripotentGrading_cube (X : NCZorn A) :
    tripotentGrading (tripotentGrading (tripotentGrading X)) = tripotentGrading X := by
  rw [tripotentGrading_sq]
  rfl

/-- $\chi$ annihilates the vacuum idempotent $P_1$: $\chi(P_1) = 0$. -/
@[simp]
theorem tripotentGrading_annihilates_P1 :
    tripotentGrading (vacuumP1 (A := A)) = ncZornZero := by
  apply NCZorn.ext <;> simp [tripotentGrading, vacuumP1, ncZornZero]

/-- $\chi$ annihilates the vacuum idempotent $P_2$: $\chi(P_2) = 0$. -/
@[simp]
theorem tripotentGrading_annihilates_P2 :
    tripotentGrading (vacuumP2 (A := A)) = ncZornZero := by
  apply NCZorn.ext <;> simp [tripotentGrading, vacuumP2, ncZornZero]

/-- $\chi$ acts as $+1$ on the color triplet subspace. -/
theorem tripotentGrading_on_triplet (u : Fin 3 → A) :
    tripotentGrading (embedTriplet u) = embedTriplet u := by
  apply NCZorn.ext
  · rfl
  · rfl
  · ext i; change -(0 : A) = 0; simp
  · rfl

/-- $\chi$ acts as $-1$ on the color antitriplet subspace. -/
theorem tripotentGrading_on_antitriplet (v : Fin 3 → A) :
    tripotentGrading (embedAntitriplet v) = ncZornNeg (embedAntitriplet v) := by
  apply NCZorn.ext
  · change (0 : A) = -0; simp
  · ext i; change (0 : A) = -0; simp
  · ext i; rfl
  · change (0 : A) = -0; simp

end TripotentGrading

/-! ### 5. Master Synthesis Certificate -/

section Synthesis

/-- Data certificate verifying the Noncommutative Zorn Peirce Idempotent
Stabilizer and Color/Grading Subspace Algebraic Invariants. -/
structure ZornGaugeEmergenceCertificate (A : Type*) [Ring A] where
  p1_idem : (vacuumP1 (A := A)) * vacuumP1 = vacuumP1
  p2_idem : (vacuumP2 (A := A)) * vacuumP2 = vacuumP2
  p1_p2_ortho : (vacuumP1 (A := A)) * vacuumP2 = ncZornZero
  p2_p1_ortho : (vacuumP2 (A := A)) * vacuumP1 = ncZornZero
  partition_unity : ncZornAdd (vacuumP1 (A := A)) vacuumP2 = 1
  peirce_decomp : ∀ X : NCZorn A,
    X = ncZornAdd (ncZornAdd (vacuumP1 * X * vacuumP1) (vacuumP1 * X * vacuumP2))
                  (ncZornAdd (vacuumP2 * X * vacuumP1) (vacuumP2 * X * vacuumP2))
  stabilizer_equiv : ∀ D : ZornDerivation A,
    StabilizesVacuum D ↔ D.toFun vacuumP2 = ncZornZero
  triplet_mul : ∀ u1 u2 : Fin 3 → A,
    embedTriplet u1 * embedTriplet u2 = embedAntitriplet (crossNC u1 u2)
  pairing_mul : ∀ (u v : Fin 3 → A),
    embedTriplet u * embedAntitriplet v = ⟨dotNC u v, fun _ => 0, fun _ => 0, 0⟩
  tripotent_cube : ∀ X : NCZorn A,
    tripotentGrading (tripotentGrading (tripotentGrading X)) = tripotentGrading X
  grading_p1_zero : tripotentGrading (vacuumP1 (A := A)) = ncZornZero
  grading_p2_zero : tripotentGrading (vacuumP2 (A := A)) = ncZornZero

/-- THEOREM: Master Synthesis of Zorn Peirce Gauge Emergence. -/
theorem zorn_gauge_emergence_synthesis : ZornGaugeEmergenceCertificate A where
  p1_idem := vacuumP1_sq
  p2_idem := vacuumP2_sq
  p1_p2_ortho := vacuumP1_mul_vacuumP2
  p2_p1_ortho := vacuumP2_mul_vacuumP1
  partition_unity := vacuumP1_add_vacuumP2
  peirce_decomp := zorn_peirce_decomposition
  stabilizer_equiv := stabilizes_vacuum_iff_P2
  triplet_mul := triplet_mul_triplet
  pairing_mul := triplet_mul_antitriplet
  tripotent_cube := tripotentGrading_cube
  grading_p1_zero := tripotentGrading_annihilates_P1
  grading_p2_zero := tripotentGrading_annihilates_P2

end Synthesis

/-! ### 6. Explicit $\mathfrak{sl}_3(R)$ Derivation Representation on `NCZorn R` -/

section SL3DerivationRepresentation

variable {R : Type*} [CommRing R]

/-- Underlying linear action of a `3 × 3` matrix `X` on `NCZorn R`:
    acts on the quark triplet `u` in the fundamental `3` (`X · u`) and on the
    antiquark antitriplet `v` in the dual `3̄` (`-Xᵀ · v`), while annihilating the
    diagonal Cartan/vacuum sector. -/
def sl3Action (X : Matrix (Fin 3) (Fin 3) R) (Z : NCZorn R) : NCZorn R where
  a := 0
  u := X.mulVec Z.u
  v := -(X.transpose.mulVec Z.v)
  b := 0

/-- Trace-zero identity for `X · (a × b) + (Xᵀ · a) × b + a × (Xᵀ · b) = 0`. -/
private theorem mulVec_crossNC_of_trace_zero (X : Matrix (Fin 3) (Fin 3) R)
    (hTr : Matrix.trace X = 0) (a b : Fin 3 → R) :
    -(X.mulVec (crossNC a b)) =
      crossNC (X.transpose.mulVec a) b + crossNC a (X.transpose.mulVec b) := by
  have htr : X 0 0 + X 1 1 + X 2 2 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_three] using hTr
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, crossNC, Fin.sum_univ_three]
    linear_combination -(a 1 * b 2 - a 2 * b 1) * htr
  · simp [Matrix.mulVec, dotProduct, crossNC, Fin.sum_univ_three]
    linear_combination -(a 2 * b 0 - a 0 * b 2) * htr
  · simp [Matrix.mulVec, dotProduct, crossNC, Fin.sum_univ_three]
    linear_combination -(a 0 * b 1 - a 1 * b 0) * htr

/-- Dual trace-zero identity for `-(Xᵀ · (a × b)) = (X · a) × b + a × (X · b)`. -/
private theorem transpose_mulVec_crossNC_of_trace_zero (X : Matrix (Fin 3) (Fin 3) R)
    (hTr : Matrix.trace X = 0) (a b : Fin 3 → R) :
    -(X.transpose.mulVec (crossNC a b)) =
      crossNC (X.mulVec a) b + crossNC a (X.mulVec b) := by
  have hTrT : Matrix.trace X.transpose = 0 := by simpa [Matrix.trace_transpose] using hTr
  simpa [Matrix.transpose_transpose] using mulVec_crossNC_of_trace_zero X.transpose hTrT a b

/-- Every traceless `3 × 3` matrix `X` (`Matrix.trace X = 0`) induces a genuine global
    `ZornDerivation R` on `NCZorn R`. -/
def sl3Derivation (X : Matrix (Fin 3) (Fin 3) R) (hTr : Matrix.trace X = 0) :
    ZornDerivation R where
  toFun := sl3Action X
  map_add := fun Y Z => by
    apply NCZorn.ext
    · simp [sl3Action, ncZornAdd]
    · ext i
      change (X.mulVec (Y.u + Z.u)) i = (X.mulVec Y.u) i + (X.mulVec Z.u) i
      rw [Matrix.mulVec_add]; rfl
    · ext i
      change (-(X.transpose.mulVec (Y.v + Z.v))) i =
        (-(X.transpose.mulVec Y.v)) i + (-(X.transpose.mulVec Z.v)) i
      rw [Matrix.mulVec_add, neg_add]; rfl
    · simp [sl3Action, ncZornAdd]
  leibniz := fun Y Z => by
    apply NCZorn.ext
    · simp only [sl3Action, ncZornAdd, ncZorn_mul_a, dotNC, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply, Pi.neg_apply, Fin.sum_univ_three]
      ring
    · have hcross := mulVec_crossNC_of_trace_zero X hTr Y.v Z.v
      have h0 := congrFun hcross 0
      have h1 := congrFun hcross 1
      have h2 := congrFun hcross 2
      ext i
      change (X.mulVec (ncZornMul Y Z).u) i =
        (ncZornMul (sl3Action X Y) Z).u i + (ncZornMul Y (sl3Action X Z)).u i
      fin_cases i <;>
      · simp [sl3Action, ncZornMul, Matrix.mulVec, dotProduct, crossNC,
          Fin.sum_univ_three] at h0 h1 h2 ⊢
        first | linear_combination h0 | linear_combination h1 | linear_combination h2
    · have hcross := transpose_mulVec_crossNC_of_trace_zero X hTr Y.u Z.u
      have h0 := congrFun hcross 0
      have h1 := congrFun hcross 1
      have h2 := congrFun hcross 2
      ext i
      change (-(X.transpose.mulVec (ncZornMul Y Z).v)) i =
        (ncZornMul (sl3Action X Y) Z).v i + (ncZornMul Y (sl3Action X Z)).v i
      fin_cases i <;>
      · simp [sl3Action, ncZornMul, Matrix.mulVec, dotProduct, crossNC,
          Fin.sum_univ_three] at h0 h1 h2 ⊢
        first | linear_combination h0 | linear_combination h1 | linear_combination h2
    · simp only [sl3Action, ncZornAdd, ncZorn_mul_b, dotNC, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply, Pi.neg_apply, Fin.sum_univ_three]
      ring

/-- **Master $\mathfrak{sl}_3(R) \to \mathrm{Der}_{\mathrm{vac}}(\mathrm{NCZorn}(R))$ Theorem**:
    For every traceless `3 × 3` matrices `X, Y` (`Matrix.trace X = 0`, `Matrix.trace Y = 0`),
    every `Z : NCZorn R`, and all color vectors `u, v : Fin 3 → R`:
    1. `sl3Derivation X hTr` stabilizes both Peirce vacuum projectors (`StabilizesVacuum`);
    2. It transforms the quark color triplet in the fundamental `3`:
       `sl3Derivation X hTr (embedTriplet u) = embedTriplet (X.mulVec u)`;
    3. It transforms the antiquark color antitriplet in the contragredient dual `3̄`:
       `sl3Derivation X hTr (embedAntitriplet v) = embedAntitriplet (-(X.transpose.mulVec v))`;
    4. Exact Lie algebra homomorphism preserving the commutator bracket:
       `D_X(D_Y(Z)) - D_Y(D_X(Z)) = D_{[X, Y]}(Z)` (with `Matrix.trace (X * Y - Y * X) = 0`)! -/
theorem sl3Derivation_representation
    (X Y : Matrix (Fin 3) (Fin 3) R) (hX : Matrix.trace X = 0) (hY : Matrix.trace Y = 0)
    (Z : NCZorn R) (u v : Fin 3 → R) :
    let DX := sl3Derivation X hX
    let DY := sl3Derivation Y hY
    let hXY : Matrix.trace (X * Y - Y * X) = 0 := by
      rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
    let DXY := sl3Derivation (X * Y - Y * X) hXY
    StabilizesVacuum DX ∧
    DX.toFun vacuumP2 = ncZornZero ∧
    DX.toFun (embedTriplet u) = embedTriplet (X.mulVec u) ∧
    DX.toFun (embedAntitriplet v) = embedAntitriplet (-(X.transpose.mulVec v)) ∧
    ncZornAdd (DX.toFun (DY.toFun Z)) (ncZornNeg (DY.toFun (DX.toFun Z))) = DXY.toFun Z := by
  intro DX DY hXY DXY
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply NCZorn.ext
    · rfl
    · ext i; change (X.mulVec 0) i = 0; simp
    · ext i; change (-(X.transpose.mulVec 0)) i = 0; simp
    · rfl
  · apply NCZorn.ext
    · rfl
    · ext i; change (X.mulVec 0) i = 0; simp
    · ext i; change (-(X.transpose.mulVec 0)) i = 0; simp
    · rfl
  · apply NCZorn.ext
    · rfl
    · rfl
    · change -(X.transpose.mulVec 0) = 0; simp
    · rfl
  · apply NCZorn.ext
    · rfl
    · change X.mulVec 0 = 0; simp
    · rfl
    · rfl
  · apply NCZorn.ext
    · simp [DX, DY, DXY, sl3Derivation, sl3Action, ncZornAdd, ncZornNeg]
    · ext i
      change (X.mulVec (Y.mulVec Z.u)) i + -((Y.mulVec (X.mulVec Z.u)) i) =
        ((X * Y - Y * X).mulVec Z.u) i
      rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      simp [sub_eq_add_neg]
    · ext i
      change (-(X.transpose.mulVec (-(Y.transpose.mulVec Z.v)))) i +
          -((-(Y.transpose.mulVec (-(X.transpose.mulVec Z.v)))) i) =
        (-((X * Y - Y * X).transpose.mulVec Z.v)) i
      rw [Matrix.mulVec_neg, neg_neg, Matrix.mulVec_neg, neg_neg,
        Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      simp [sub_eq_add_neg]
    · simp [DX, DY, DXY, sl3Derivation, sl3Action, ncZornAdd, ncZornNeg]

end SL3DerivationRepresentation

/-! ### 7. Generalized `[Ring A]` Baryon Triple-Product & Peirce Sector Closure -/

section GeneralizedBaryonAndPeirceClosure

variable {A : Type*} [Ring A]

/-- Product of two antiquark color antitriplets lands strictly in the quark color triplet
sector via the negative cross product:
`embedAntitriplet v₁ * embedAntitriplet v₂ = embedTriplet (-(v₁ × v₂))`. -/
theorem antitriplet_mul_antitriplet (v₁ v₂ : Fin 3 → A) :
    embedAntitriplet v₁ * embedAntitriplet v₂ = embedTriplet (fun i => -crossNC v₁ v₂ i) := by
  apply NCZorn.ext
  · change 0 * 0 + dotNC (fun _ => 0) v₂ = 0
    simp [dotNC]
  · ext i
    show (0 : A) * 0 + 0 * 0 - crossNC v₁ v₂ i = -crossNC v₁ v₂ i
    simp
  · ext i
    show v₁ i * 0 + (0 : A) * v₂ i + crossNC (fun _ => 0) (fun _ => 0) i = 0
    simp
  · change 0 * 0 + dotNC v₁ (fun _ => 0) = 0
    simp [dotNC]

/-- Pairing an antitriplet on the left with a triplet on the right lands strictly in the
second Peirce diagonal vacuum sector `P₂`:
`embedAntitriplet v * embedTriplet u = diag(0, v · u)`. -/
theorem antitriplet_mul_triplet (v u : Fin 3 → A) :
    embedAntitriplet v * embedTriplet u = ⟨0, fun _ => 0, fun _ => 0, dotNC v u⟩ := by
  apply NCZorn.ext
  · change 0 * 0 + dotNC (fun _ => 0) (fun _ => 0) = 0
    simp [dotNC]
  · ext i
    show (0 : A) * u i + 0 * 0 - crossNC v (fun _ => 0) i = 0
    simp [crossNC_zero_right]
  · ext i
    show v i * 0 + (0 : A) * 0 + crossNC (fun _ => 0) u i = 0
    simp [crossNC_zero_left]
  · change 0 * 0 + dotNC v u = dotNC v u
    simp

/-- **Noncommutative Color Baryon Triple Product (`[Ring A]`)**:
Combining three color triplets lands exclusively on the diagonal Peirce vacuum sectors `P₂` and `P₁`
via the noncommutative scalar triple product `(u₁ × u₂) · u₃` and `u₃ · (u₁ × u₂)`. -/
theorem baryon_triplet_triple_product (u₁ u₂ u₃ : Fin 3 → A) :
    ((embedTriplet u₁ * embedTriplet u₂) * embedTriplet u₃ =
      ⟨0, fun _ => 0, fun _ => 0, dotNC (crossNC u₁ u₂) u₃⟩) ∧
    (embedTriplet u₃ * (embedTriplet u₁ * embedTriplet u₂) =
      ⟨dotNC u₃ (crossNC u₁ u₂), fun _ => 0, fun _ => 0, 0⟩) := by
  rw [triplet_mul_triplet u₁ u₂]
  exact ⟨antitriplet_mul_triplet (crossNC u₁ u₂) u₃, triplet_mul_antitriplet u₃ (crossNC u₁ u₂)⟩

/-- **Noncommutative Antibaryon Triple Product (`[Ring A]`)**:
Combining three antiquark antitriplets lands in the first Peirce diagonal vacuum sector `P₁`. -/
theorem baryon_antitriplet_triple_product (v₁ v₂ v₃ : Fin 3 → A) :
    (embedAntitriplet v₁ * embedAntitriplet v₂) * embedAntitriplet v₃ =
      ⟨dotNC (fun i => -crossNC v₁ v₂ i) v₃, fun _ => 0, fun _ => 0, 0⟩ := by
  rw [antitriplet_mul_antitriplet v₁ v₂]
  exact triplet_mul_antitriplet (fun i => -crossNC v₁ v₂ i) v₃

/-- **Peirce Orthogonality & Bimodule Selection Rules over `[Ring A]`**:
`P₁` (`vacuumP1`) and `P₂` (`vacuumP2`) act as left/right Peirce unit idempotents for `3` (`embedTriplet`)
and `3̄` (`embedAntitriplet`). -/
theorem peirce_sector_orthogonal_closure (u v : Fin 3 → A) :
    (vacuumP1 * embedTriplet u = embedTriplet u) ∧
    (embedTriplet u * vacuumP2 = embedTriplet u) ∧
    (vacuumP2 * embedTriplet u = 0) ∧
    (embedTriplet u * vacuumP1 = 0) ∧
    (vacuumP2 * embedAntitriplet v = embedAntitriplet v) ∧
    (embedAntitriplet v * vacuumP1 = embedAntitriplet v) ∧
    (vacuumP1 * embedAntitriplet v = 0) ∧
    (embedAntitriplet v * vacuumP2 = 0) := by
  have hmul_nc : ∀ U V : NCZorn A, U * V = ncZornMul U V := fun _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [hmul_nc]
    apply NCZorn.ext
    · simp [ncZornMul, vacuumP1, vacuumP2, embedTriplet, embedAntitriplet, dotNC]
      try rfl
    · ext i
      fin_cases i <;>
        (simp [ncZornMul, vacuumP1, vacuumP2, embedTriplet, embedAntitriplet,
          crossNC_zero_left, crossNC_zero_right]; try rfl)
    · ext i
      fin_cases i <;>
        (simp [ncZornMul, vacuumP1, vacuumP2, embedTriplet, embedAntitriplet,
          crossNC_zero_left, crossNC_zero_right]; try rfl)
    · simp [ncZornMul, vacuumP1, vacuumP2, embedTriplet, embedAntitriplet, dotNC]
      try rfl

/-- Over any commutative ring `R`, the baryon triple product is cyclic and alternating. -/
theorem baryon_triple_product_alternating {R : Type*} [CommRing R] (u₁ u₂ u₃ : Fin 3 → R) :
    dotNC (crossNC u₁ u₂) u₃ = dotNC u₃ (crossNC u₁ u₂) ∧
    dotNC (crossNC u₁ u₂) u₃ = dotNC u₁ (crossNC u₂ u₃) ∧
    dotNC (crossNC u₁ u₂) u₁ = 0 ∧
    dotNC (crossNC u₁ u₂) u₂ = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [dotNC, crossNC]
    ring

end GeneralizedBaryonAndPeirceClosure

/-! ### 8. Generalized `[CommRing R]` Split-Octonion & Vector-Matrix Algebra Isomorphisms -/

section GeneralizedZornEquivalences

/-- Noncommutative split-signature Zorn norm `N(X) = a b - u · v` over any ring `A`. -/
def ncZornNorm {A : Type*} [Ring A] (X : NCZorn A) : A :=
  X.a * X.b - dotNC X.u X.v

/-- Canonical equivalence `NCZorn R ≃ ZornSplitOctonion R` over any commutative ring `R`. -/
def ncZornSplitOctonionEquivR (R : Type*) :
    NCZorn R ≃ InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.ZornSplitOctonion R where
  toFun X := ⟨X.a, X.u, X.v, X.b⟩
  invFun Z := ⟨Z.a, Z.u, Z.v, Z.b⟩
  left_inv X := by cases X; rfl
  right_inv Z := by cases Z; rfl

/-- Over any commutative ring `R`, `ncZornSplitOctonionEquivR R` preserves multiplication and the
multiplicative split-octonion norm `N(X * Y) = N(X) * N(Y)`. -/
theorem ncZornSplitOctonionEquivR_laws {R : Type*} [CommRing R] (X Y : NCZorn R) :
    (ncZornSplitOctonionEquivR R (X * Y) =
      InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul
        (ncZornSplitOctonionEquivR R X) (ncZornSplitOctonionEquivR R Y)) ∧
    (InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornNorm
        (ncZornSplitOctonionEquivR R X) = ncZornNorm X) ∧
    (ncZornNorm (X * Y) = ncZornNorm X * ncZornNorm Y) := by
  have hmul :
      ncZornSplitOctonionEquivR R (X * Y) =
        InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul
          (ncZornSplitOctonionEquivR R X) (ncZornSplitOctonionEquivR R Y) := by
    have hmul_nc : X * Y = ncZornMul X Y := rfl
    rw [hmul_nc]
    ext k
    · simp [ncZornSplitOctonionEquivR, ncZornMul, dotNC,
        InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul,
        InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Dot]
    · fin_cases k <;>
        (simp [ncZornSplitOctonionEquivR, ncZornMul, crossNC,
          InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul,
          InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Cross]; ring)
    · fin_cases k <;>
        (simp [ncZornSplitOctonionEquivR, ncZornMul, crossNC,
          InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul,
          InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Cross]; ring)
    · simp [ncZornSplitOctonionEquivR, ncZornMul, dotNC,
        InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornMul,
        InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Dot]
  have hnorm : InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornNorm
      (ncZornSplitOctonionEquivR R X) = ncZornNorm X := by
    simp [ncZornSplitOctonionEquivR, ncZornNorm, dotNC,
      InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornNorm,
      InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Dot]
  have hcomp : ncZornNorm (X * Y) = ncZornNorm X * ncZornNorm Y := by
    have hz := InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornNorm_mul
      (ncZornSplitOctonionEquivR R X) (ncZornSplitOctonionEquivR R Y)
    rw [← hmul] at hz
    simpa [hnorm, ncZornSplitOctonionEquivR, ncZornNorm, dotNC,
      InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.zornNorm,
      InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.vec3Dot] using hz
  exact ⟨hmul, hnorm, hcomp⟩

/-- Canonical equivalence `NCZorn R ≃ ZornVectorMatrix R`. -/
def ncZornVectorMatrixEquivR (R : Type*) :
    NCZorn R ≃ InfoGeometry.Algebra.ZornVectorMatrix R where
  toFun X := ⟨X.a, X.u, X.v, X.b⟩
  invFun Z := ⟨Z.a, Z.v, Z.w, Z.b⟩
  left_inv X := by cases X; rfl
  right_inv Z := by cases Z; rfl

/-- Over any commutative ring `R`, `ncZornVectorMatrixEquivR R` intertwines Zorn multiplication,
quadratic norm, and the four Peirce sectors `P₁, P₂, 3, 3̄`. -/
theorem ncZornVectorMatrixEquivR_laws {R : Type*} [CommRing R]
    (X Y : NCZorn R) (u v : Fin 3 → R) :
    (ncZornVectorMatrixEquivR R (X * Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.mul
        (ncZornVectorMatrixEquivR R X) (ncZornVectorMatrixEquivR R Y)) ∧
    (InfoGeometry.Algebra.ZornVectorMatrix.norm (ncZornVectorMatrixEquivR R X) = ncZornNorm X) ∧
    (ncZornVectorMatrixEquivR R vacuumP1 = InfoGeometry.Algebra.ZornVectorMatrix.E11) ∧
    (ncZornVectorMatrixEquivR R vacuumP2 = InfoGeometry.Algebra.ZornVectorMatrix.E22) ∧
    (ncZornVectorMatrixEquivR R (embedTriplet u) = ⟨0, u, fun _ => 0, 0⟩) ∧
    (ncZornVectorMatrixEquivR R (embedAntitriplet v) = ⟨0, fun _ => 0, v, 0⟩) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hmul_nc : X * Y = ncZornMul X Y := rfl
    rw [hmul_nc]
    ext k
    · simp [ncZornVectorMatrixEquivR, ncZornMul, dotNC,
        InfoGeometry.Algebra.ZornVectorMatrix.mul,
        InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three]
    · fin_cases k <;>
        (simp [ncZornVectorMatrixEquivR, ncZornMul, crossNC,
          InfoGeometry.Algebra.ZornVectorMatrix.mul,
          InfoGeometry.Algebra.ZornVec3.cross]; ring)
    · fin_cases k <;>
        (simp [ncZornVectorMatrixEquivR, ncZornMul, crossNC,
          InfoGeometry.Algebra.ZornVectorMatrix.mul,
          InfoGeometry.Algebra.ZornVec3.cross]; ring)
    · simp [ncZornVectorMatrixEquivR, ncZornMul, dotNC,
        InfoGeometry.Algebra.ZornVectorMatrix.mul,
        InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three]
      ring
  · simp [ncZornVectorMatrixEquivR, ncZornNorm, dotNC,
      InfoGeometry.Algebra.ZornVectorMatrix.norm,
      InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three]
  · rfl
  · rfl
  · rfl
  · rfl

end GeneralizedZornEquivalences

/-! ### 9. Generalized `[CommRing R]` Rank-1 Outer Product & `sl₃ ⊕ gl₁` Decomposition -/

section GeneralizedSL3GL1Decomposition

variable {R : Type*} [CommRing R]

/-- Rank-1 quark–antiquark outer product `(u ⊗ vᵀ)_{ij} = u_i v_j` over any commutative ring `R`. -/
def quarkAntiquarkOuterR (u v : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j => u i * v j

/-- Cleared-denominator trace-zero `sl₃(R)` part `3 (u ⊗ vᵀ) - (u · v) I₃` over any commutative ring `R`. -/
def quarkAntiquarkTraceless3R (u v : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  (3 : R) • quarkAntiquarkOuterR u v - dotNC u v • (1 : Matrix (Fin 3) (Fin 3) R)

/-- **Cleared-Denominator `sl₃(R) ⊕ gl₁(R)` Superbracket Decomposition Theorem**:
Over **any** commutative ring `R` (without requiring `3` invertible),
1. `tr(u ⊗ vᵀ) = u · v`,
2. `tr(quarkAntiquarkTraceless3R u v) = 0`,
3. `3 • (u ⊗ vᵀ) = quarkAntiquarkTraceless3R u v + (u · v) • I₃`,
4. `sl3Derivation (quarkAntiquarkTraceless3R u v)` acts on `3` (`embedTriplet w`) by
   `3 (v · w) u - (u · v) w` and on `3̄` (`embedAntitriplet w`) by
   `-(3 (u · w) v - (u · v) w)`. -/
theorem quarkAntiquark_sl3_gl1_split (u v w : Fin 3 → R) :
    (Matrix.trace (quarkAntiquarkOuterR u v) = dotNC u v) ∧
    (Matrix.trace (quarkAntiquarkTraceless3R u v) = 0) ∧
    ((3 : R) • quarkAntiquarkOuterR u v =
      quarkAntiquarkTraceless3R u v + dotNC u v • (1 : Matrix (Fin 3) (Fin 3) R)) ∧
    ((sl3Derivation (quarkAntiquarkTraceless3R u v) (by
        simp [quarkAntiquarkTraceless3R, quarkAntiquarkOuterR, dotNC,
          Matrix.trace, Matrix.diag, Fin.sum_univ_three])).toFun (embedTriplet w) =
      embedTriplet (fun i => (3 : R) * dotNC v w * u i - dotNC u v * w i)) ∧
    ((sl3Derivation (quarkAntiquarkTraceless3R u v) (by
        simp [quarkAntiquarkTraceless3R, quarkAntiquarkOuterR, dotNC,
          Matrix.trace, Matrix.diag, Fin.sum_univ_three])).toFun (embedAntitriplet w) =
      embedAntitriplet (fun i => -((3 : R) * dotNC u w * v i - dotNC u v * w i))) := by
  have htr_outer : Matrix.trace (quarkAntiquarkOuterR u v) = dotNC u v := by
    simp [quarkAntiquarkOuterR, dotNC, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  have htr_sl3 : Matrix.trace (quarkAntiquarkTraceless3R u v) = 0 := by
    simp [quarkAntiquarkTraceless3R, quarkAntiquarkOuterR, dotNC,
      Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  have hsplit : (3 : R) • quarkAntiquarkOuterR u v =
      quarkAntiquarkTraceless3R u v + dotNC u v • (1 : Matrix (Fin 3) (Fin 3) R) := by
    dsimp [quarkAntiquarkTraceless3R]
    abel
  refine ⟨htr_outer, htr_sl3, hsplit, ?_, ?_⟩
  · rw [(sl3Derivation_representation (quarkAntiquarkTraceless3R u v)
        (quarkAntiquarkTraceless3R u v) htr_sl3 htr_sl3 0 w 0).2.2.1]
    congr 1
    ext i
    fin_cases i <;>
      (simp [quarkAntiquarkTraceless3R, quarkAntiquarkOuterR, dotNC,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring)
  · rw [(sl3Derivation_representation (quarkAntiquarkTraceless3R u v)
        (quarkAntiquarkTraceless3R u v) htr_sl3 htr_sl3 0 0 w).2.2.2.1]
    congr 1
    ext i
    fin_cases i <;>
      (simp [quarkAntiquarkTraceless3R, quarkAntiquarkOuterR, dotNC,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring)

/-- Exact `sl₃ ⊕ gl₁` projection recovery whenever `3` is invertible in `R` (e.g. `R = ℝ` or `ℚ`):
`⅟3 • quarkAntiquarkTraceless3R u v + (⅟3 * dotNC u v) • I₃ = quarkAntiquarkOuterR u v`. -/
theorem quarkAntiquark_sl3_gl1_proj_invertible [Invertible (3 : R)] (u v : Fin 3 → R) :
    (⅟(3 : R)) • quarkAntiquarkTraceless3R u v +
        (⅟(3 : R) * dotNC u v) • (1 : Matrix (Fin 3) (Fin 3) R) =
      quarkAntiquarkOuterR u v := by
  have hsplit := (quarkAntiquark_sl3_gl1_split u v 0).2.2.1
  calc
    (⅟(3 : R)) • quarkAntiquarkTraceless3R u v +
        (⅟(3 : R) * dotNC u v) • (1 : Matrix (Fin 3) (Fin 3) R)
      = (⅟(3 : R)) • (quarkAntiquarkTraceless3R u v +
          dotNC u v • (1 : Matrix (Fin 3) (Fin 3) R)) := by
          rw [smul_add, smul_smul]
    _ = (⅟(3 : R)) • ((3 : R) • quarkAntiquarkOuterR u v) := by rw [← hsplit]
    _ = quarkAntiquarkOuterR u v := by
          rw [smul_smul, invOf_mul_self, one_smul]

end GeneralizedSL3GL1Decomposition

/-! ### 10. $\mathbb{Z}_2 \times \mathbb{Z}_2$ Bi-Grading, Günaydin–Gürsey Superbrackets & `Cl(5,5)` Unification -/

section Z2Z2PeirceColorUnification

/-- The four Peirce color/vacuum sectors of `NCZorn`. -/
inductive ZornPeirceSector
  | vacP1
  | vacP2
  | quark3
  | antiquark3Bar
  deriving DecidableEq, Repr

/-- Exact $\mathbb{Z}_2 \times \mathbb{Z}_2$ bi-degree $(\deg_e, \deg_c)$ of each Peirce sector:
- `vacP1, vacP2 ↦ (0, 0)` (even gauge/vacuum sector),
- `quark3, antiquark3Bar ↦ (1, 1)` (quark / antiquark color-triplet sector). -/
def zornSectorBiGrade : ZornPeirceSector → Fin 2 × Fin 2
  | .vacP1 => (0, 0)
  | .vacP2 => (0, 0)
  | .quark3 => (1, 1)
  | .antiquark3Bar => (1, 1)

/-- $\mathbb{Z}_2 \times \mathbb{Z}_2$ bi-degree of the leptonic color-singlet sector `(1, 0)`. -/
def zornLeptonBiGrade : Fin 2 × Fin 2 := (1, 0)

/-- $\mathbb{Z}_2 \times \mathbb{Z}_2$ bi-degree of the pure color-odd bosonic sector `(0, 1)`. -/
def zornColorBosonBiGrade : Fin 2 × Fin 2 := (0, 1)

/-- Integral $\mathbb{Z}_2 \times \mathbb{Z}_2$ color-supersymmetry Koszul sign
`(-1)^(g₁.1 * g₂.1 + g₁.2 * g₂.2)`. -/
def zornBiGradeKoszulSign (g₁ g₂ : Fin 2 × Fin 2) : ℤ :=
  (-1 : ℤ) ^ (g₁.1.val * g₂.1.val + g₁.2.val * g₂.2.val)

/-- **Fundamental $\mathbb{Z}_2 \times \mathbb{Z}_2$ Koszul Sign Theorem on Zorn Color Bi-Degrees**:
Symmetric, involutive (`sign^2 = 1`), gauge-boson transparent (`+1` on `(0,0)`),
lepton–quark anticommuting (`-1`), lepton–lepton fermionic (`-1`), and quark–quark bi-odd (`+1`). -/
theorem zornBiGrade_koszul_sign_laws (g₁ g₂ : Fin 2 × Fin 2) :
    (zornBiGradeKoszulSign g₁ g₂ = zornBiGradeKoszulSign g₂ g₁) ∧
    (zornBiGradeKoszulSign g₁ g₂ * zornBiGradeKoszulSign g₁ g₂ = 1) ∧
    (zornBiGradeKoszulSign (zornSectorBiGrade .vacP1) g₁ = 1) ∧
    (zornBiGradeKoszulSign (zornSectorBiGrade .quark3) zornLeptonBiGrade = -1) ∧
    (zornBiGradeKoszulSign zornLeptonBiGrade zornLeptonBiGrade = -1) ∧
    (zornBiGradeKoszulSign (zornSectorBiGrade .quark3) (zornSectorBiGrade .antiquark3Bar) = 1) := by
  have hsymm : g₁.1.val * g₂.1.val + g₁.2.val * g₂.2.val =
      g₂.1.val * g₁.1.val + g₂.2.val * g₁.2.val := by
    rw [mul_comm g₁.1.val g₂.1.val, mul_comm g₁.2.val g₂.2.val]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [zornBiGradeKoszulSign, hsymm]
  · simp only [zornBiGradeKoszulSign, ← pow_add, ← two_mul, pow_mul]
    norm_num
  · simp [zornBiGradeKoszulSign, zornSectorBiGrade]
  · decide
  · decide
  · decide

/-- **Cross-Lane Unification Theorem (`ZornGaugeEmergence` ↔ `ZornSplitOctonion` ↔ `Cl55SpinorCartanFock`)**:
Over any commutative ring `R`, simultaneously packages:
1. Vacuum-stabilizing `sl₃(R)` derivations acting as `3 ⊕ 3̄` on `NCZorn R`,
2. Cleared-denominator `sl₃ ⊕ gl₁` quark–antiquark outer-product closure,
3. Split-octonion norm composition `ncZornNorm (X * Y) = ncZornNorm X * ncZornNorm Y` via `ZornSplitOctonionFin8Bridge`,
4. Concrete `Cl(5,5)` 5-mode Fock realization (`MatStage 5`): Cartan gluon neutrality on white singlets,
   exact `32 = 4 + 12 + 12 + 4` color-sector traces, `16 = 2 + 6 + 2 + 6` chiral half-spinor traces,
   and Catto `1₀ ↔ 3 ↔ 3̄ ↔ 1₃` CAR transitions! -/
theorem zorn_cl55_color_weak_unification {R : Type*} [CommRing R]
    (X_sl3 : Matrix (Fin 3) (Fin 3) R) (hTr : Matrix.trace X_sl3 = 0)
    (X Y : NCZorn R) (u v w : Fin 3 → R) :
    StabilizesVacuum (sl3Derivation X_sl3 hTr) ∧
    ((sl3Derivation X_sl3 hTr).toFun (embedTriplet u) = embedTriplet (X_sl3.mulVec u)) ∧
    ((sl3Derivation X_sl3 hTr).toFun (embedAntitriplet v) =
      embedAntitriplet (-(X_sl3.transpose.mulVec v))) ∧
    (Matrix.trace (quarkAntiquarkTraceless3R u v) = 0 ∧
     (3 : R) • quarkAntiquarkOuterR u v =
       quarkAntiquarkTraceless3R u v + dotNC u v • (1 : Matrix (Fin 3) (Fin 3) R)) ∧
    (ncZornNorm (X * Y) = ncZornNorm X * ncZornNorm Y) ∧
    (InfoGeometry.Physics.Cl55SpinorCartanFock.colorGluonT3 *
        (InfoGeometry.Physics.Cl55SpinorCartanFock.colorBaryonSingletProj +
          InfoGeometry.Physics.Cl55SpinorCartanFock.colorVacuumSingletProj) = 0 ∧
     InfoGeometry.Physics.Cl55SpinorCartanFock.colorGluon3Y *
        (InfoGeometry.Physics.Cl55SpinorCartanFock.colorBaryonSingletProj +
          InfoGeometry.Physics.Cl55SpinorCartanFock.colorVacuumSingletProj) = 0) ∧
    (Matrix.trace InfoGeometry.Physics.Cl55SpinorCartanFock.colorVacuumSingletProj = 4 ∧
     Matrix.trace InfoGeometry.Physics.Cl55SpinorCartanFock.colorQuarkTripletProj = 12 ∧
     Matrix.trace InfoGeometry.Physics.Cl55SpinorCartanFock.colorDiquarkAntitripletProj = 12 ∧
     Matrix.trace InfoGeometry.Physics.Cl55SpinorCartanFock.colorBaryonSingletProj = 4) ∧
    (Matrix.trace (InfoGeometry.Physics.Cl55SpinorCartanFock.colorBaryonSingletProj *
        InfoGeometry.Physics.Cl55SpinorCartanFock.isospinCarrier 3 4) = 2 ∧
     Matrix.trace (InfoGeometry.Physics.Cl55SpinorCartanFock.colorQuarkTripletProj *
        InfoGeometry.Physics.Cl55SpinorCartanFock.isospinCarrier 3 4) = 6 ∧
     Matrix.trace (InfoGeometry.Physics.Cl55SpinorCartanFock.colorVacuumSingletProj *
        InfoGeometry.Physics.Cl55SpinorCartanFock.pairingCarrier 3 4) = 2 ∧
     Matrix.trace (InfoGeometry.Physics.Cl55SpinorCartanFock.colorDiquarkAntitripletProj *
        InfoGeometry.Physics.Cl55SpinorCartanFock.pairingCarrier 3 4) = 6) ∧
    (∀ c : Fin 3,
      InfoGeometry.Physics.Cl55SpinorCartanFock.colorQuarkTripletProj *
          (InfoGeometry.Physics.Cl55SpinorCartanFock.e (c.castLE (by omega)) *
            InfoGeometry.Physics.Cl55SpinorCartanFock.colorVacuumSingletProj) =
        InfoGeometry.Physics.Cl55SpinorCartanFock.e (c.castLE (by omega)) *
          InfoGeometry.Physics.Cl55SpinorCartanFock.colorVacuumSingletProj) := by
  have hrep := sl3Derivation_representation X_sl3 X_sl3 hTr hTr X u v
  have hsplit := quarkAntiquark_sl3_gl1_split u v w
  have hnorm := (ncZornSplitOctonionEquivR_laws X Y).2.2
  have htr4 := InfoGeometry.Physics.Cl55SpinorCartanFock.trace_colorFourSectors_cl55
  have htr16 := InfoGeometry.Physics.Cl55SpinorCartanFock.trace_chiralHalfSpinorMinus16_multiplets_cl55
  have hcatto := InfoGeometry.Physics.Cl55SpinorCartanFock.catto_car_color_transitions_cl55
  refine ⟨hrep.1, hrep.2.2.1, hrep.2.2.2.1, ⟨hsplit.2.1, hsplit.2.2.1⟩, hnorm,
    InfoGeometry.Physics.Cl55SpinorCartanFock.colorGluon_cartan_white_singlets_neutrality,
    htr4, ⟨htr16.1, htr16.2.1, htr16.2.2.1, htr16.2.2.2.1⟩, fun c => (hcatto.1 c).1⟩

/-- Noncommutativity witness for `3 × 3` color gauge matrices over any nontrivial ring `R`. -/
theorem sl3_matrix_noncomm_witness {R : Type*} [Ring R] [Nontrivial R] :
    (!![(0 : R), 1, 0; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) R) *
        !![0, 0, 0; 1, 0, 0; 0, 0, 0] ≠
      !![(0 : R), 0, 0; 1, 0, 0; 0, 0, 0] *
        !![0, 1, 0; 0, 0, 0; 0, 0, 0] := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h00

/-- Existential noncommutativity witness for `3 × 3` color gauge matrices over any nontrivial
ring `R`. -/
theorem sl3_matrix_exists_noncomm_witness {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 3) (Fin 3) R, A * B ≠ B * A := by
  refine ⟨!![0, 1, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 1, 0, 0; 0, 0, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h00

end Z2Z2PeirceColorUnification

end InfoGeometry.Algebra.ZornGaugeEmergence
