/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import InfoGeometry.Physics.NoncommutativeZornBdGDerivations

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

end InfoGeometry.Algebra.ZornGaugeEmergence
