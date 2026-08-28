/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import InfoGeometry.Algebra.ZornMatrix

/-!
# Split-Octonion Witt Planes and Nambu-Gorkov Quasiparticle Bridge

This module formalizes the canonical micro-generator of nuclear pairing
and chiral dynamics by decomposing the split-octonion algebra $\mathbb{O}_s \cong \mathcal{M}_2(\mathbb{R} \oplus \mathbb{R}^3)$
into its **4 mutually orthogonal Witt planes**:

1. **$\Pi_0$ (Scalar Plane)**:
   $$\Pi_0 = \operatorname{span}\{E_{11}, E_{22}\} = \operatorname{span}\{u_0^+, u_0^-\}$$
   carrying the Peirce idempotents $(u_0^\pm)^2 = u_0^\pm$, $u_0^+ u_0^- = 0$, $u_0^+ + u_0^- = I$.
   This represents the particle-hole vacuum projectors and the seniority/scale grading $\xi$.

2. **$\Pi_a$ ($a \in \{0, 1, 2\}$, Vector Planes)**:
   $$\Pi_a = \operatorname{span}\{U(a), V(a)\} = \operatorname{span}\{u_a^+, u_a^-\}$$
   carrying the nilpotent ladder operators $(u_a^\pm)^2 = 0$, representing Cooper pair creation ($u_a^+$)
   and annihilation ($u_a^-$) operators satisfying the canonical CAR relations:
   $$\{u_a^+, u_b^-\} = \delta_{ab} I, \quad \{u_a^+, u_b^+\} = 0, \quad \{u_a^-, u_b^-\} = 0$$

3. **Nambu-Gorkov Quasiparticle Matrix**:
   $$X_{\text{NG}}(\xi, \vec{\Delta}) = \begin{pmatrix} \xi & \vec{\Delta} \\ \vec{\Delta} & -\xi \end{pmatrix} = \xi u_0^+ - \xi u_0^- + \sum_{i=0}^2 \Delta_i (u_i^+ + u_i^-)$$

4. **Bogoliubov Dispersion Spectrum from the Zorn Reduced Norm**:
   $$\operatorname{zornNorm}(X_{\text{NG}}) = - (\xi^2 + \|\vec{\Delta}\|^2) = - E_{\text{quasiparticle}}^2$$

5. **Pauli / Quasispin Generator Algebra**:
   - $\tau_3 = u_0^+ - u_0^-$ with $\tau_3^2 = I$
   - $\tau_1(i) = u_i^+ + u_i^-$ with $\tau_1(i)^2 = I$
   - $\{\tau_3, \tau_1(i)\} = 0$

All proofs are complete in native Mathlib with 0 `sorry`s and 0 custom axioms.
-/

noncomputable section

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix

namespace InfoGeometry.Nuclear.NambuGorkov

variable {R : Type*} [CommRing R]

/-! ## 1. The 4 Witt Planes and Generators -/

/-- Positive Peirce idempotent $u_0^+ = E_{11}$ in scalar plane $\Pi_0$. -/
def u0_plus : ZornMatrix R := E11

/-- Negative Peirce idempotent $u_0^- = E_{22}$ in scalar plane $\Pi_0$. -/
def u0_minus : ZornMatrix R := E22

/-- Positive nilpotent ladder operator $u_a^+ = U(a)$ in vector plane $\Pi_a$. -/
def ua_plus (i : Fin 3) : ZornMatrix R := U i

/-- Negative nilpotent ladder operator $u_a^- = V(a)$ in vector plane $\Pi_a$. -/
def ua_minus (i : Fin 3) : ZornMatrix R := V i

/-! ## 2. Fundamental Algebraic Laws of the Witt Basis -/

/-- 🏆 THEOREM: Peirce idempotents sum to the identity in $\Pi_0$. -/
@[simp] theorem peirce_sum_id :
    (u0_plus (R := R)) + u0_minus = I :=
  E11_add_E22

/-- 🏆 THEOREM: Peirce idempotents are orthogonal: $u_0^+ u_0^- = 0$. -/
@[simp] theorem peirce_plus_mul_minus :
    (u0_plus (R := R)) * u0_minus = 0 :=
  E11_mul_E22

/-- 🏆 THEOREM: Peirce idempotents are orthogonal: $u_0^- u_0^+ = 0$. -/
@[simp] theorem peirce_minus_mul_plus :
    (u0_minus (R := R)) * u0_plus = 0 :=
  E22_mul_E11

/-- 🏆 THEOREM: Positive Peirce idempotent is a true projector: $(u_0^+)^2 = u_0^+$. -/
@[simp] theorem peirce_plus_sq :
    (u0_plus (R := R)) * u0_plus = u0_plus :=
  E11_mul_E11

/-- 🏆 THEOREM: Negative Peirce idempotent is a true projector: $(u_0^-)^2 = u_0^-$. -/
@[simp] theorem peirce_minus_sq :
    (u0_minus (R := R)) * u0_minus = u0_minus :=
  E22_mul_E22

/-- 🏆 THEOREM: Vector plane ladder operators are strictly nilpotent: $(u_a^+)^2 = 0$. -/
@[simp] theorem ladder_plus_sq (i : Fin 3) :
    (ua_plus (R := R) i) * ua_plus i = 0 :=
  U_mul_self_zero i

/-- 🏆 THEOREM: Vector plane ladder operators are strictly nilpotent: $(u_a^-)^2 = 0$. -/
@[simp] theorem ladder_minus_sq (i : Fin 3) :
    (ua_minus (R := R) i) * ua_minus i = 0 :=
  V_mul_self_zero i

/-- 🏆 THEOREM: Forward-backward pairing yields the upper Peirce idempotent: $u_a^+ u_a^- = u_0^+$. -/
@[simp] theorem ladder_plus_mul_minus_self (i : Fin 3) :
    (ua_plus (R := R) i) * ua_minus i = u0_plus :=
  U_mul_V_self i

/-- 🏆 THEOREM: Backward-forward pairing yields the lower Peirce idempotent: $u_a^- u_a^+ = u_0^-$. -/
@[simp] theorem ladder_minus_mul_plus_self (i : Fin 3) :
    (ua_minus (R := R) i) * ua_plus i = u0_minus :=
  V_mul_U_self i

/-- 🏆 THEOREM (CAR Anti-Commutation): $\{u_a^+, u_b^-\} = \delta_{ab} I$. -/
theorem ladder_car_anticommutator (i j : Fin 3) :
    (ua_plus (R := R) i) * ua_minus j + ua_minus j * ua_plus i =
      if i = j then I else 0 :=
  U_V_anticommutator i j

/-- 🏆 THEOREM: Ladder creation operators anti-commute: $\{u_a^+, u_b^+\} = 0$. -/
theorem ladder_plus_anticommute (i j : Fin 3) :
    (ua_plus (R := R) i) * ua_plus j + ua_plus j * ua_plus i = 0 :=
  U_anticommute i j

/-- 🏆 THEOREM: Ladder annihilation operators anti-commute: $\{u_a^-, u_b^-\} = 0$. -/
theorem ladder_minus_anticommute (i j : Fin 3) :
    (ua_minus (R := R) i) * ua_minus j + ua_minus j * ua_minus i = 0 :=
  V_anticommute i j

/-! ## 3. Pauli Quasispin Operators in the Witt Basis -/

/-- Pauli $\tau_3$ operator (seniority grading / particle-hole asymmetry): $\tau_3 = u_0^+ - u_0^-$. -/
def tau3 : ZornMatrix R := u0_plus - u0_minus

/-- Pauli $\tau_1(i)$ operator (Hermitian pairing mode): $\tau_1(i) = u_i^+ + u_i^-$. -/
def tau1 (i : Fin 3) : ZornMatrix R := ua_plus i + ua_minus i

/-- 🏆 THEOREM: $\tau_3^2 = I$. -/
@[simp] theorem tau3_sq :
    (tau3 (R := R)) * tau3 = I := by
  dsimp [tau3, u0_plus, u0_minus]
  ext j <;> simp [E11, E22, I, mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

/-- 🏆 THEOREM: $\tau_1(i)^2 = I$. -/
@[simp] theorem tau1_sq (i : Fin 3) :
    (tau1 (R := R) i) * tau1 i = I := by
  dsimp [tau1, ua_plus, ua_minus]
  fin_cases i <;>
    ext j <;>
      simp [U, V, I, Vec3.basis, mul, add, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

/-- 🏆 THEOREM: $\tau_3$ and $\tau_1(i)$ strictly anti-commute: $\{\tau_3, \tau_1(i)\} = 0$. -/
theorem tau3_tau1_anticommute (i : Fin 3) :
    (tau3 (R := R)) * tau1 i + tau1 i * tau3 = 0 := by
  dsimp [tau3, tau1, u0_plus, u0_minus, ua_plus, ua_minus]
  fin_cases i <;>
    ext j <;>
      simp [E11, E22, U, V, zero, Vec3.basis, mul, add,
        Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

/-! ## 4. Nambu-Gorkov Quasiparticle Carrier and Zorn Matrix Lift -/

/-- The Nambu-Gorkov nuclear pairing carrier: single-particle energy $\xi$ and pairing gap vector $\vec{\Delta}$. -/
structure NambuGorkovCarrier (R : Type*) [CommRing R] where
  xi : R
  delta : Vec3 R

/-- Canonical embedding of the Nambu-Gorkov state into the Zorn matrix algebra. -/
def toZorn (N : NambuGorkovCarrier R) : ZornMatrix R where
  a := N.xi
  v := N.delta
  w := N.delta
  b := - N.xi

/-- 🏆 THEOREM: The Nambu-Gorkov matrix is strictly traceless: $\operatorname{Tr}_Z(X_{\text{NG}}) = 0$. -/
@[simp] theorem nambu_gorkov_traceless (N : NambuGorkovCarrier R) :
    zornTrace (toZorn N) = 0 := by
  dsimp [zornTrace, toZorn]
  ring

/-- 🏆 THEOREM: Linear expansion of the Nambu-Gorkov state into the 4 Witt planes. -/
theorem toZorn_eq_witt_expansion (N : NambuGorkovCarrier R) :
    toZorn N = N.xi • tau3 +
      N.delta 0 • tau1 0 + N.delta 1 • tau1 1 + N.delta 2 • tau1 2 := by
  have hrw : N.xi • tau3 + N.delta 0 • tau1 0 + N.delta 1 • tau1 1 + N.delta 2 • tau1 2 =
    add (add (add (smul N.xi (sub E11 E22)) (smul (N.delta 0) (add (U 0) (V 0))))
             (smul (N.delta 1) (add (U 1) (V 1))))
        (smul (N.delta 2) (add (U 2) (V 2))) := rfl
  rw [hrw]
  ext j
  · dsimp [toZorn, add, sub, smul, E11, E22, U, V]
    ring
  · fin_cases j <;> {
      dsimp [toZorn, add, sub, smul, E11, E22, U, V, Vec3.add, Vec3.sub, Vec3.smul, Vec3.basis]
      ring
    }
  · fin_cases j <;> {
      dsimp [toZorn, add, sub, smul, E11, E22, U, V, Vec3.add, Vec3.sub, Vec3.smul, Vec3.basis]
      ring
    }
  · dsimp [toZorn, add, sub, smul, E11, E22, U, V]
    ring

/-- 🏆 THEOREM: The Zorn reduced norm of the Nambu-Gorkov state gives the negative squared dispersion. -/
theorem nambu_gorkov_zornNorm (N : NambuGorkovCarrier R) :
    zornNorm (toZorn N) = - (N.xi ^ 2 + Vec3.dot N.delta N.delta) := by
  dsimp [zornNorm, toZorn]
  ring

/-! ## 5. Real Bogoliubov Quasiparticle Spectrum -/

/-- The canonical Bogoliubov quasiparticle energy $E = \sqrt{\xi^2 + \|\vec{\Delta}\|^2}$. -/
def bogoliubovEnergy (N : NambuGorkovCarrier ℝ) : ℝ :=
  Real.sqrt (N.xi ^ 2 + Vec3.dot N.delta N.delta)

/-- 🏆 THEOREM: The squared Bogoliubov energy is the negative Zorn determinant / norm. -/
theorem bogoliubovEnergy_sq (N : NambuGorkovCarrier ℝ) :
    (bogoliubovEnergy N) ^ 2 = - zornNorm (toZorn N) := by
  dsimp [bogoliubovEnergy]
  have h_dot_nonneg : 0 ≤ Vec3.dot N.delta N.delta := by
    dsimp [Vec3.dot]
    have h0 : 0 ≤ N.delta 0 * N.delta 0 := by nlinarith
    have h1 : 0 ≤ N.delta 1 * N.delta 1 := by nlinarith
    have h2 : 0 ≤ N.delta 2 * N.delta 2 := by nlinarith
    linarith
  have h_nonneg : 0 ≤ N.xi ^ 2 + Vec3.dot N.delta N.delta := by
    have hxi : 0 ≤ N.xi ^ 2 := sq_nonneg N.xi
    linarith
  rw [Real.sq_sqrt h_nonneg]
  rw [nambu_gorkov_zornNorm]
  ring

/-- 🏆 THEOREM: The Bogoliubov quasiparticle energy is strictly positive for any nontrivial state. -/
theorem bogoliubovEnergy_pos (N : NambuGorkovCarrier ℝ)
    (h_nontriv : N.xi ≠ 0 ∨ N.delta 0 ≠ 0 ∨ N.delta 1 ≠ 0 ∨ N.delta 2 ≠ 0) :
    0 < bogoliubovEnergy N := by
  dsimp [bogoliubovEnergy]
  have h_dot_nonneg : 0 ≤ Vec3.dot N.delta N.delta := by
    dsimp [Vec3.dot]
    have h0 : 0 ≤ N.delta 0 * N.delta 0 := by nlinarith
    have h1 : 0 ≤ N.delta 1 * N.delta 1 := by nlinarith
    have h2 : 0 ≤ N.delta 2 * N.delta 2 := by nlinarith
    linarith
  have h_sum_pos : 0 < N.xi ^ 2 + Vec3.dot N.delta N.delta := by
    rcases h_nontriv with hxi | hd0 | hd1 | hd2
    · have hxi_pos : 0 < N.xi ^ 2 := sq_pos_of_ne_zero hxi
      linarith
    · dsimp [Vec3.dot]
      have hd0_pos : 0 < N.delta 0 * N.delta 0 := by
        have hsq : N.delta 0 * N.delta 0 = (N.delta 0) ^ 2 := by ring
        rw [hsq]; exact sq_pos_of_ne_zero hd0
      have hd1_nonneg : 0 ≤ N.delta 1 * N.delta 1 := by nlinarith
      have hd2_nonneg : 0 ≤ N.delta 2 * N.delta 2 := by nlinarith
      have hxi_nonneg : 0 ≤ N.xi ^ 2 := sq_nonneg N.xi
      linarith
    · dsimp [Vec3.dot]
      have hd1_pos : 0 < N.delta 1 * N.delta 1 := by
        have hsq : N.delta 1 * N.delta 1 = (N.delta 1) ^ 2 := by ring
        rw [hsq]; exact sq_pos_of_ne_zero hd1
      have hd0_nonneg : 0 ≤ N.delta 0 * N.delta 0 := by nlinarith
      have hd2_nonneg : 0 ≤ N.delta 2 * N.delta 2 := by nlinarith
      have hxi_nonneg : 0 ≤ N.xi ^ 2 := sq_nonneg N.xi
      linarith
    · dsimp [Vec3.dot]
      have hd2_pos : 0 < N.delta 2 * N.delta 2 := by
        have hsq : N.delta 2 * N.delta 2 = (N.delta 2) ^ 2 := by ring
        rw [hsq]; exact sq_pos_of_ne_zero hd2
      have hd0_nonneg : 0 ≤ N.delta 0 * N.delta 0 := by nlinarith
      have hd1_nonneg : 0 ≤ N.delta 1 * N.delta 1 := by nlinarith
      have hxi_nonneg : 0 ≤ N.xi ^ 2 := sq_nonneg N.xi
      linarith
  exact Real.sqrt_pos.mpr h_sum_pos

end InfoGeometry.Nuclear.NambuGorkov

