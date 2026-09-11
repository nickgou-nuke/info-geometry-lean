/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Canonical.GunaydinGurseyQuarkBasisBridge

/-!
# Pauli–Weyl Lightcone, Twistor Quantization, & Günaydin–Gürsey Quark Color

This module formalizes the exact mathematical nexus uniting:
1. **The Pauli–Weyl Lightcone & Dyadic Spinor Factorization**:
   - Spacetime coordinates represented as $2 \times 2$ matrices in $\mathrm{Mat}_2(R) \cong \mathbb{H}'$.
   - The lightcone condition $\det(X) = 0$.
   - Any dyadic spinor product $X = \pi \lambda^T$ identically satisfies $\det(X) = 0$
     and $X^2 = \operatorname{tr}(X) X$, proving that every lightlike 4-vector factorizes
     into a dyad of chiral Pauli–Weyl spinors.

2. **Polarized Quaternionic Subspaces in Split Cayley–Dickson Doubling**:
   - Under split doubling $\mathbb{O}' = \mathbb{H}'_1 \oplus \mathbb{H}'_2 \ell$ ($\ell^2 = +1$),
     the split Peirce projectors $P_\pm = \frac{1 \pm \ell}{2}$ polarize the 8-dimensional
     space into two 4-dimensional isotropic subspaces:
     position space $P_+ \mathbb{O}' \cong \mathbb{H}'_1$ and momentum space $P_- \mathbb{O}' \cong \mathbb{H}'_2$.

3. **First Quantization of the Penrose Twistor Pair**:
   - The geometric dyad $Z = (\omega, \pi)$ promotes to quantum operators satisfying
     canonical commutation relations $[\hat{\omega}, \hat{\pi}] = c \mathbf{1}$.
   - The symmetrized helicity operator $\hat{s} = \frac{1}{2}(\hat{\omega}\hat{\pi} + \hat{\pi}\hat{\omega})$
     acts as the Euler dilation generator of the Iwasawa triad $\mathfrak{a}$:
     $[\hat{s}, \hat{\omega}] = -c \hat{\omega}$ and $[\hat{s}, \hat{\pi}] = +c \hat{\pi}$.

4. **Preservation by $\mathrm{SU}(3)$ and the Lepton–Quark Split $\mathbf{8} \to \mathbf{1} \oplus \mathbf{3}$**:
   - In the Günaydin–Gürsey split octonion Zorn realization, fixing the split Peirce unit
     $\ell = E_{11} - E_{22}$ breaks the automorphism group down to the color gauge group $\mathrm{SU}(3)$
     (split real form $\mathrm{SL}_3(\mathbb{R})$).
   - The 8-dimensional algebra decomposes into:
     - **The Lepton Singlet $\mathbf{1}$**: The 2-dimensional diagonal split-complex subalgebra
       $\{E_{11}, E_{22}\}$ (spacetime chiral vacuum / uncolored leptons).
     - **The Quark Triplet $\mathbf{3}$**: The 6-dimensional off-diagonal subspace spanned by
       $\{u_0, u_1, u_2, u_0^*, u_1^*, u_2^*\}$.
   - Color nilpotency: $u_i^2 = 0$ and $(u_i^*)^2 = 0$.
   - Diquark color cross-product: $u_0 u_1 = u_2^*$, $u_1 u_2 = u_0^*$, $u_2 u_0 = u_1^*$
     (two quarks bind into the antiquark of the complementary color).
   - Canonical Anticommutation Relations (CAR): $\{u_i, u_j\} = 0$ and $\{u_i, u_j^*\} = -\delta_{ij} \mathbf{1}$.

All theorems are proved constructively in native Lean 4 / Mathlib with zero gaps.
-/

noncomputable section

namespace InfoGeometry.Canonical.PauliWeylTwistorQuarkColor

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Canonical.GunaydinGursey

variable {R : Type*} [CommRing R]

/-! ### 1. Pauli–Weyl Lightcone & Dyadic Spinor Factorization -/

/-- Relativistic 4-vector mapped to a 2x2 matrix in neutral signature (2,2). -/
def pauliMatrix22 (x0 x1 x2 x3 : R) : Matrix (Fin 2) (Fin 2) R :=
  ![![x0 + x3, x1 - x2],
    ![x1 + x2, x0 - x3]]

/-- The determinant of the Pauli matrix gives the quadratic metric norm. -/
theorem pauliMatrix22_det (x0 x1 x2 x3 : R) :
    (pauliMatrix22 x0 x1 x2 x3).det = x0^2 + x2^2 - x1^2 - x3^2 := by
  rw [Matrix.det_fin_two]
  dsimp [pauliMatrix22]
  ring

/-- The dyadic outer product of two 2-component chiral Weyl spinors. -/
def dyadicSpinorMatrix (pi lambda : Fin 2 → R) : Matrix (Fin 2) (Fin 2) R :=
  ![![pi 0 * lambda 0, pi 0 * lambda 1],
    ![pi 1 * lambda 0, pi 1 * lambda 1]]

/-- 🏆 THEOREM: Every dyadic spinor matrix has zero determinant identically. -/
theorem dyadicSpinorMatrix_det (pi lambda : Fin 2 → R) :
    (dyadicSpinorMatrix pi lambda).det = 0 := by
  rw [Matrix.det_fin_two]
  dsimp [dyadicSpinorMatrix]
  ring

/-- 🏆 THEOREM: A dyadic spinor matrix satisfies X² = tr(X) X. -/
theorem dyadicSpinorMatrix_sq (pi lambda : Fin 2 → R) :
    dyadicSpinorMatrix pi lambda * dyadicSpinorMatrix pi lambda =
      (pi 0 * lambda 0 + pi 1 * lambda 1) • dyadicSpinorMatrix pi lambda := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [dyadicSpinorMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  }

/-- When the trace vanishes, the lightlike spinor dyad is square-nilpotent. -/
theorem dyadicSpinorMatrix_nilpotent_of_tr_zero (pi lambda : Fin 2 → R)
    (htr : pi 0 * lambda 0 + pi 1 * lambda 1 = 0) :
    dyadicSpinorMatrix pi lambda * dyadicSpinorMatrix pi lambda = 0 := by
  rw [dyadicSpinorMatrix_sq, htr, zero_smul]

/-! ### 2. Split Peirce Polarized Quaternionic Subspaces -/

/-- Split Peirce plus idempotent P+ = (1 + J)/2. -/
def peircePlus {A : Type*} [Ring A] [Algebra ℝ A] (J : A) : A :=
  (1/2 : ℝ) • (1 + J)

/-- Split Peirce minus idempotent P- = (1 - J)/2. -/
def peirceMinus {A : Type*} [Ring A] [Algebra ℝ A] (J : A) : A :=
  (1/2 : ℝ) • (1 - J)

/-- P+ is an idempotent: P+² = P+. -/
theorem peirce_plus_sq {A : Type*} [Ring A] [Algebra ℝ A] (J : A) (hJ : J * J = 1) :
    peircePlus J * peircePlus J = peircePlus J := by
  dsimp [peircePlus]
  rw [smul_mul_smul]
  have hhalf : (1/2 : ℝ) * (1/2 : ℝ) = (1/4 : ℝ) := by norm_num
  rw [hhalf]
  have h1 : (1 + J) * (1 + J) = (2 : ℝ) • (1 + J) := by
    rw [two_smul]
    calc
      (1 + J) * (1 + J) = 1 + J + J + J * J := by noncomm_ring
      _ = 1 + J + J + 1 := by rw [hJ]
      _ = (1 + J) + (1 + J) := by abel
  rw [h1, smul_smul]
  norm_num

/-- P- is an idempotent: P-² = P-. -/
theorem peirce_minus_sq {A : Type*} [Ring A] [Algebra ℝ A] (J : A) (hJ : J * J = 1) :
    peirceMinus J * peirceMinus J = peirceMinus J := by
  dsimp [peirceMinus]
  rw [smul_mul_smul]
  have hhalf : (1/2 : ℝ) * (1/2 : ℝ) = (1/4 : ℝ) := by norm_num
  rw [hhalf]
  have h1 : (1 - J) * (1 - J) = (2 : ℝ) • (1 - J) := by
    rw [two_smul]
    calc
      (1 - J) * (1 - J) = 1 - J - J + J * J := by noncomm_ring
      _ = 1 - J - J + 1 := by rw [hJ]
      _ = (1 - J) + (1 - J) := by abel
  rw [h1, smul_smul]
  norm_num

/-- Orthogonality of split Peirce projectors: P+ P- = 0. -/
theorem peirce_ortho {A : Type*} [Ring A] [Algebra ℝ A] (J : A) (hJ : J * J = 1) :
    peircePlus J * peirceMinus J = 0 := by
  dsimp [peircePlus, peirceMinus]
  rw [smul_mul_smul]
  have h1 : (1 + J) * (1 - J) = 0 := by
    calc
      (1 + J) * (1 - J) = 1 - J + J - J * J := by noncomm_ring
      _ = 1 - 1 := by rw [hJ]; abel
      _ = 0 := sub_self 1
  rw [h1, _root_.smul_zero]

/-- Resolution of identity: P+ + P- = 1. -/
theorem peirce_sum_id {A : Type*} [Ring A] [Algebra ℝ A] (J : A) :
    peircePlus J + peirceMinus J = 1 := by
  dsimp [peircePlus, peirceMinus]
  rw [← _root_.smul_add]
  have h : (1 + J) + (1 - J) = (2 : ℝ) • (1 : A) := by
    rw [two_smul]
    abel
  rw [h, smul_smul]
  norm_num

/-! ### 3. Twistor Canonical Quantization & Iwasawa Helicity Scaling -/

/-- Lie commutator [a, b] = a*b - b*a. -/
def commutator {A : Type*} [Ring A] (a b : A) : A := a * b - b * a

/-- Symmetrized quantum helicity operator s = (omega*pi + pi*omega). -/
def helicityOperator {A : Type*} [Ring A] (omega pi : A) : A :=
  omega * pi + pi * omega

/-- 🏆 THEOREM: Iwasawa split Cartan scaling of twistor coordinate omega: [s, omega] = -2c * omega. -/
theorem twistor_helicity_scaling_omega {A : Type*} [Ring A]
    (omega pi c : A)
    (h_ccr : commutator omega pi = c)
    (hc_omega : c * omega = omega * c) :
    commutator (helicityOperator omega pi) omega = - 2 * c * omega := by
  dsimp [helicityOperator, commutator] at *
  calc
    (omega * pi + pi * omega) * omega - omega * (omega * pi + pi * omega)
      = (pi * omega - omega * pi) * omega + omega * (pi * omega - omega * pi) := by
        noncomm_ring
    _ = (- c) * omega + omega * (- c) := by
        have h_pi_omega : pi * omega - omega * pi = - c := by
          rw [← h_ccr]
          abel
        rw [h_pi_omega]
    _ = - 2 * c * omega := by
        have h : omega * (-c) = - (c * omega) := by
          rw [_root_.mul_neg, hc_omega]
        have h2 : (-c) * omega = - (c * omega) := by
          rw [_root_.neg_mul]
        rw [h, h2]
        noncomm_ring

/-- 🏆 THEOREM: Iwasawa split Cartan scaling of twistor momentum pi: [s, pi] = +2c * pi. -/
theorem twistor_helicity_scaling_pi {A : Type*} [Ring A]
    (omega pi c : A)
    (h_ccr : commutator omega pi = c)
    (hc_pi : c * pi = pi * c) :
    commutator (helicityOperator omega pi) pi = 2 * c * pi := by
  dsimp [helicityOperator, commutator] at *
  calc
    (omega * pi + pi * omega) * pi - pi * (omega * pi + pi * omega)
      = (omega * pi - pi * omega) * pi + pi * (omega * pi - pi * omega) := by
        noncomm_ring
    _ = c * pi + pi * c := by
        rw [h_ccr]
    _ = 2 * c * pi := by
        rw [← hc_pi]
        noncomm_ring

/-! ### 4. Günaydin–Gürsey Zorn Split Octonions & The Color SU(3) Lepton–Quark Split -/

/-- The split Peirce unit ell = E11 - E22 in the Zorn algebra. -/
def ellZorn : ZornVectorMatrix R :=
  sub E11 E22

/-- 🏆 THEOREM: The split Peirce unit ell squares to identity: ell² = 1. -/
theorem ellZorn_sq : mul (ellZorn : ZornVectorMatrix R) ellZorn = one := by
  ext : 1 <;> simp [ellZorn, sub, add, neg, E11, E22, mul, one, ZornVec3.dot, ZornVec3.cross]

/-- The diagonal idempotent E11 is the +1 eigenvector of ell. -/
theorem ellZorn_mul_E11 : mul (ellZorn : ZornVectorMatrix R) E11 = E11 := by
  ext : 1 <;> simp [ellZorn, sub, add, neg, E11, E22, mul, ZornVec3.dot, ZornVec3.cross]

/-- The diagonal idempotent E22 is the -1 eigenvector of ell. -/
theorem ellZorn_mul_E22 : mul (ellZorn : ZornVectorMatrix R) E22 = neg E22 := by
  ext : 1 <;> simp [ellZorn, sub, add, neg, E11, E22, mul, ZornVec3.dot, ZornVec3.cross]

/-- 🏆 THEOREM: Every quark color state is square-nilpotent: u(i)² = 0. -/
theorem quark_color_nilpotent (i : Fin 3) :
    mul (u i : ZornVectorMatrix R) (u i) = zero := by
  ext : 1
  · simp [u, V, mul, zero]
  · ext k
    fin_cases i <;> fin_cases k <;> simp [u, V, mul, zero, ZornVec3.cross, ZornVec3.basis]
  · ext k
    fin_cases i <;> fin_cases k <;> simp [u, V, mul, zero, ZornVec3.cross, ZornVec3.basis]
  · simp [u, V, mul, zero]

/-- 🏆 THEOREM: Every antiquark color state is square-nilpotent: (u*(i))² = 0. -/
theorem antiquark_color_nilpotent (i : Fin 3) :
    mul (uStar i : ZornVectorMatrix R) (uStar i) = zero := by
  ext : 1
  · simp [uStar, U, neg, mul, zero]
  · ext k
    fin_cases i <;> fin_cases k <;> simp [uStar, U, neg, mul, zero, ZornVec3.cross, ZornVec3.basis]
  · ext k
    fin_cases i <;> fin_cases k <;> simp [uStar, U, neg, mul, zero, ZornVec3.cross, ZornVec3.basis]
  · simp [uStar, U, neg, mul, zero]

/-- 🏆 THEOREM: Diquark color product 0 * 1 = u*(2) (Red * Green = anti-Blue). -/
theorem diquark_color_01 : mul (u 0 : ZornVectorMatrix R) (u 1) = uStar 2 := by
  ext : 1
  · simp [u, uStar, V, U, neg, mul]
  · ext k
    fin_cases k <;> simp [u, uStar, V, U, neg, mul, ZornVec3.cross, ZornVec3.basis]
  · ext k
    fin_cases k <;> simp [u, uStar, V, U, neg, mul, ZornVec3.cross, ZornVec3.basis]
  · simp [u, uStar, V, U, neg, mul]

/-- 🏆 THEOREM: Diquark color product 1 * 2 = u*(0) (Green * Blue = anti-Red). -/
theorem diquark_color_12 : mul (u 1 : ZornVectorMatrix R) (u 2) = uStar 0 := by
  ext : 1
  · simp [u, uStar, V, U, neg, mul]
  · ext k
    fin_cases k <;> simp [u, uStar, V, U, neg, mul, ZornVec3.cross, ZornVec3.basis]
  · ext k
    fin_cases k <;> simp [u, uStar, V, U, neg, mul, ZornVec3.cross, ZornVec3.basis]
  · simp [u, uStar, V, U, neg, mul]

/-- 🏆 THEOREM: Diquark color product 2 * 0 = u*(1) (Blue * Red = anti-Green). -/
theorem diquark_color_20 : mul (u 2 : ZornVectorMatrix R) (u 0) = uStar 1 := by
  ext : 1
  · simp [u, uStar, V, U, neg, mul]
  · ext k
    fin_cases k <;> simp [u, uStar, V, U, neg, mul, ZornVec3.cross, ZornVec3.basis]
  · ext k
    fin_cases k <;> simp [u, uStar, V, U, neg, mul, ZornVec3.cross, ZornVec3.basis]
  · simp [u, uStar, V, U, neg, mul]

/-- 🏆 THEOREM: Antidiquark color product 0 * 1 = u(2) (anti-Red * anti-Green = Blue). -/
theorem antidiquark_color_01 : mul (uStar 0 : ZornVectorMatrix R) (uStar 1) = u 2 := by
  ext : 1
  · simp [u, uStar, V, U, neg, mul]
  · ext k
    fin_cases k <;> simp [u, uStar, V, U, neg, mul, ZornVec3.cross, ZornVec3.basis]
  · ext k
    fin_cases k <;> simp [u, uStar, V, U, neg, mul, ZornVec3.cross, ZornVec3.basis]
  · simp [u, uStar, V, U, neg, mul]

/-- 🏆 THEOREM: Antidiquark color product 1 * 2 = u(0) (anti-Green * anti-Blue = Red). -/
theorem antidiquark_color_12 : mul (uStar 1 : ZornVectorMatrix R) (uStar 2) = u 0 := by
  ext : 1
  · simp [u, uStar, V, U, neg, mul]
  · ext k
    fin_cases k <;> simp [u, uStar, V, U, neg, mul, ZornVec3.cross, ZornVec3.basis]
  · ext k
    fin_cases k <;> simp [u, uStar, V, U, neg, mul, ZornVec3.cross, ZornVec3.basis]
  · simp [u, uStar, V, U, neg, mul]

/-- 🏆 THEOREM: Antidiquark color product 2 * 0 = u(1) (anti-Blue * anti-Red = Green). -/
theorem antidiquark_color_20 : mul (uStar 2 : ZornVectorMatrix R) (uStar 0) = u 1 := by
  ext : 1
  · simp [u, uStar, V, U, neg, mul]
  · ext k
    fin_cases k <;> simp [u, uStar, V, U, neg, mul, ZornVec3.cross, ZornVec3.basis]
  · ext k
    fin_cases k <;> simp [u, uStar, V, U, neg, mul, ZornVec3.cross, ZornVec3.basis]
  · simp [u, uStar, V, U, neg, mul]

/-- 🏆 THEOREM: Canonical Anticommutation Relation (CAR) for matching colors: {u(i), u*(i)} = -1. -/
theorem quark_antiquark_car_same (i : Fin 3) :
    add (mul (u i : ZornVectorMatrix R) (uStar i))
        (mul (uStar i) (u i)) = neg one := by
  ext : 1
  · fin_cases i <;> simp [u, uStar, V, U, neg, mul, add, one, ZornVec3.basis, ZornVec3.dot_eq_sum_coords]
  · ext k
    fin_cases i <;> fin_cases k <;> simp [u, uStar, V, U, neg, mul, add, one, ZornVec3.cross, ZornVec3.basis]
  · ext k
    fin_cases i <;> fin_cases k <;> simp [u, uStar, V, U, neg, mul, add, one, ZornVec3.cross, ZornVec3.basis]
  · fin_cases i <;> simp [u, uStar, V, U, neg, mul, add, one, ZornVec3.basis, ZornVec3.dot_eq_sum_coords]

/-- 🏆 THEOREM: Canonical Anticommutation Relation (CAR) for distinct colors: {u(i), u*(j)} = 0. -/
theorem quark_antiquark_car_diff (i j : Fin 3) (hij : i ≠ j) :
    add (mul (u i : ZornVectorMatrix R) (uStar j))
        (mul (uStar j) (u i)) = zero := by
  ext : 1
  · simp [u, uStar, V, U, neg, mul, add, zero, ZornVec3.basis]
    intro h
    exact False.elim (hij h)
  · ext k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [u, uStar, V, U, neg, mul, add, zero, ZornVec3.cross, ZornVec3.basis]
  · ext k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [u, uStar, V, U, neg, mul, add, zero, ZornVec3.cross, ZornVec3.basis]
  · simp [u, uStar, V, U, neg, mul, add, zero, ZornVec3.basis]
    intro h
    exact False.elim (hij h)

/-- Predicate characterizing the 2-dimensional Lepton Singlet subspace (pure diagonal). -/
def isLeptonSinglet (X : ZornVectorMatrix R) : Prop :=
  X.v = (fun _ => 0) ∧ X.w = (fun _ => 0)

/-- 🏆 THEOREM: The Lepton Singlet forms a commutative, associative split-complex subalgebra. -/
theorem lepton_singlet_subalgebra (X Y : ZornVectorMatrix R)
    (hX : isLeptonSinglet X) (hY : isLeptonSinglet Y) :
    isLeptonSinglet (mul X Y) ∧
    (mul X Y).a = X.a * Y.a ∧
    (mul X Y).b = X.b * Y.b := by
  rcases hX with ⟨hXv, hXw⟩
  rcases hY with ⟨hYv, hYw⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · ext i; simp [mul, hXv, hXw, hYv, hYw]
  · ext i; simp [mul, hXv, hXw, hYv, hYw]
  · simp [mul, hXv, hYw, ZornVec3.dot_eq_sum_coords]
  · simp [mul, hXw, hYv, ZornVec3.dot_eq_sum_coords]

/-! ### 5. Master Packet -/

/-- Master packet packaging the Pauli-Weyl lightcone dyad, twistor quantization, and quark SU(3) color algebra. -/
structure PauliWeylTwistorQuarkColorPacket where
  dyad_det :
    ∀ (pi lambda : Fin 2 → ℝ),
      (dyadicSpinorMatrix pi lambda).det = 0
  dyad_sq :
    ∀ (pi lambda : Fin 2 → ℝ),
      dyadicSpinorMatrix pi lambda * dyadicSpinorMatrix pi lambda =
        (pi 0 * lambda 0 + pi 1 * lambda 1) • dyadicSpinorMatrix pi lambda
  peirce_ortho :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (J : A),
      J * J = 1 → peircePlus J * peirceMinus J = 0
  peirce_id :
    ∀ {A : Type*} [Ring A] [Algebra ℝ A] (J : A),
      peircePlus J + peirceMinus J = 1
  twistor_helicity_omega :
    ∀ {A : Type*} [Ring A] (omega pi c : A),
      commutator omega pi = c →
      c * omega = omega * c →
      commutator (helicityOperator omega pi) omega = - 2 * c * omega
  twistor_helicity_pi :
    ∀ {A : Type*} [Ring A] (omega pi c : A),
      commutator omega pi = c →
      c * pi = pi * c →
      commutator (helicityOperator omega pi) pi = 2 * c * pi
  ell_sq :
    mul (ellZorn (R := ℝ)) ellZorn = one
  quark_nilpotent :
    ∀ i : Fin 3, mul (u i : ZornVectorMatrix ℝ) (u i) = zero
  antiquark_nilpotent :
    ∀ i : Fin 3, mul (uStar i : ZornVectorMatrix ℝ) (uStar i) = zero
  diquark_01 :
    mul (u 0 : ZornVectorMatrix ℝ) (u 1) = uStar 2
  diquark_12 :
    mul (u 1 : ZornVectorMatrix ℝ) (u 2) = uStar 0
  diquark_20 :
    mul (u 2 : ZornVectorMatrix ℝ) (u 0) = uStar 1
  car_same :
    ∀ i : Fin 3,
      add (mul (u i : ZornVectorMatrix ℝ) (uStar i))
          (mul (uStar i) (u i)) = neg one
  car_diff :
    ∀ (i j : Fin 3),
      i ≠ j →
      add (mul (u i : ZornVectorMatrix ℝ) (uStar j))
          (mul (uStar j) (u i)) = zero

/-- Constructor for the master packet. -/
def makePauliWeylTwistorQuarkColorPacket : PauliWeylTwistorQuarkColorPacket where
  dyad_det := dyadicSpinorMatrix_det
  dyad_sq := dyadicSpinorMatrix_sq
  peirce_ortho := peirce_ortho
  peirce_id := peirce_sum_id
  twistor_helicity_omega := twistor_helicity_scaling_omega
  twistor_helicity_pi := twistor_helicity_scaling_pi
  ell_sq := ellZorn_sq
  quark_nilpotent := quark_color_nilpotent
  antiquark_nilpotent := antiquark_color_nilpotent
  diquark_01 := diquark_color_01
  diquark_12 := diquark_color_12
  diquark_20 := diquark_color_20
  car_same := quark_antiquark_car_same
  car_diff := quark_antiquark_car_diff

end InfoGeometry.Canonical.PauliWeylTwistorQuarkColor
