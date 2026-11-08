/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel

/-!
# Polyform CAR Algebras, Complex/Paracomplex Mixed Structures, & Pure Spinor Stabilizers
  ($\mathcal{K}_0 \prec \mathcal{K}_1 \prec \mathcal{K}_2 \prec \mathcal{K}_3 \prec \mathcal{K}_4$)

Target: `InfoGeometry/Canonical/BhojaKrasnovSpinorPolyformMixedParabolicPoset.lean`

This canonical module epistemically compiles the five-stage causal poset
$\mathcal{K}_0 \prec \mathcal{K}_1 \prec \mathcal{K}_2 \prec \mathcal{K}_3 \prec \mathcal{K}_4$
distilled from Niren Bhoja and Kirill Krasnov (2022), *Notes on Spinors and Polyforms I:
General Case* (arXiv:2205.04866), formalized over an arbitrary **non-commutative**
associative ring `[Ring B]` inside the recursive matrix algebras $\mathrm{Mat}_2(B)$ and
$\mathrm{Op}_4(B) = \mathrm{Mat}_2(\mathrm{Mat}_2(B))$:

1. **Archetype $\mathcal{K}_0$ (`archetype_K0_brauer_weyl_signature_lifts`):**
   Formalizes Equations (1.1)–(1.3) in `Mat2 B`: the $(r+1, s+1)$ split periodicity lift
   $\Gamma^{(+)}(\gamma) = \begin{pmatrix} 0 & \gamma \\ \gamma & 0 \end{pmatrix}$ preserves
   the anticommutator $\{\gamma_1, \gamma_2\}$ while anticommuting with $E_z$ ($E_z^2 = +1$)
   and $E_y$ ($E_y^2 = -1$), whereas the $(s+2, r)$ signature-flip lift
   $\Gamma^{(-)}(\gamma) = \begin{pmatrix} 0 & \gamma \\ -\gamma & 0 \end{pmatrix}$ negates
   $\{\gamma_1, \gamma_2\}$ while anticommuting with $E_z$ ($E_z^2 = +1$) and $E_x$ ($E_x^2 = +1$).
2. **Archetype $\mathcal{K}_1$ (`archetype_K1_mixed_structure_and_orthogonal_product_splitting`):**
   Formalizes Section 5.7 (Defs. 5.1–5.2, Props. 5.1–5.2, Eqs. (5.23)–(5.33)) in
   $\mathrm{Op}_4(B) = \mathrm{Mat}_2(\mathrm{Mat}_2(B))$: proves orthogonal kernels
   $I_{\mathrm{para}} J_{\mathrm{comp}} = J_{\mathrm{comp}} I_{\mathrm{para}} = 0$,
   subspace squares $I_{\mathrm{para}}^2 = P_+$ and $J_{\mathrm{comp}}^2 = -P_-$,
   mixed-structure square $I_{\mathrm{para}}^2 - J_{\mathrm{comp}}^2 = 1$,
   product-structure recovery $I_{\mathrm{para}}^2 + J_{\mathrm{comp}}^2 = P_{\mathrm{prod}}$
   ($P_{\mathrm{prod}}^2 = 1$), and eigenspace invariance $P_{\mathrm{prod}} I_{\mathrm{para}} = I_{\mathrm{para}}$,
   $P_{\mathrm{prod}} J_{\mathrm{comp}} = -J_{\mathrm{comp}}$.
3. **Archetype $\mathcal{K}_2$ (`archetype_K2_two_mode_car_algebra_and_derivation_identities`):**
   Formalizes the 2-mode CAR creation/annihilation operators $b_1, b_1^\dagger, b_2, b_2^\dagger \in \mathrm{Op}_4(B)$
   with Jordan–Wigner grading and resolves the factor-of-2 convention in Eq. (2.24):
   $[b_1 b_1^\dagger, b_1] = +b_1$ and $[b_1^\dagger b_1, b_1] = -b_1$ versus the antisymmetrized
   $\mathfrak{spin}$ commutator $[[b_1, b_1^\dagger], b_1] = 2 b_1$, together with
   $[b_1 b_2^\dagger, b_2] = b_1$, $[b_1^\dagger b_2^\dagger, b_1] = -b_2^\dagger$, and
   $[b_1^\dagger b_2^\dagger, b_2] = +b_1^\dagger$.
4. **Archetype $\mathcal{K}_3$ (`archetype_K3_complementary_pure_spinors_and_parabolic_stabilizer`):**
   Formalizes Section 3.3 (Eqs. (3.6)–(3.8)) and Section 5.4 (Eq. (5.12)): proves that the
   top-form pure spinor projector $\Psi_{\mathrm{top}} = b_1 b_1^\dagger b_2 b_2^\dagger$
   is annihilated on the left by $b_1, b_2$, the vacuum projector $\Psi_{\mathrm{vac}} = b_1^\dagger b_1 b_2^\dagger b_2$
   is annihilated by $b_1^\dagger, b_2^\dagger$, and $\Psi_{\mathrm{top}}$ is stabilized on the
   left by the $\mathfrak{sl}(2)$ triple $(H_{12}, E_+, E_-)$ **plus** the square-zero 2-form
   $B$-field generator $\mathcal{N}_{12} = b_1 b_2$.
5. **Archetype $\mathcal{K}_4$ (`archetype_K4_paracomplex_recovery_and_chirality_volume_involution`):**
   Formalizes Section 3.1 (Eq. (3.3)), Section 3.3 (Eq. (3.9)), and Section 7.3 (Eqs. (7.36)–(7.45)):
   recovers the paracomplex involutions $I_{\mathrm{para}}^{(1)} = [b_1^\dagger, b_1] = \frac{1}{2}[\Gamma_1, \Gamma_3]$
   and $I_{\mathrm{para}}^{(2)} = [b_2^\dagger, b_2] = \frac{1}{2}[\Gamma_2, \Gamma_4]$, proves
   $I_{\mathrm{para}}^{(i)} b_i^\dagger = +b_i^\dagger$ and $I_{\mathrm{para}}^{(i)} b_i = -b_i$,
   and proves $R^2 = 1$, $\{R, \Gamma_A\} = 0$, $R \Psi_{\mathrm{vac}} = \Psi_{\mathrm{vac}}$,
   and $R \Psi_{\mathrm{top}} = \Psi_{\mathrm{top}}$ for the chirality volume involution
   $R = I_{\mathrm{para}}^{(1)} I_{\mathrm{para}}^{(2)}$.

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved Non-Commutative Spinor & Polyform Theorems (`[kernel_verified]`):**
  - `archetype_K0_brauer_weyl_signature_lifts`.
  - `archetype_K1_mixed_structure_and_orthogonal_product_splitting`.
  - `archetype_K2_two_mode_car_algebra_and_derivation_identities`.
  - `archetype_K3_complementary_pure_spinors_and_parabolic_stabilizer`.
  - `archetype_K4_paracomplex_recovery_and_chirality_volume_involution` and
    `bhojaKrasnov_car_noncommutative`.

* **BUCKET 2 — Eliminated Certificate & Prop-Def Wrappers (Zero Remaining):**
  - All theorems are proved directly over `Mat2 B` and `Op4 B = Mat2 (Mat2 B)` for any
    `[Ring B]`, with zero `Prop`-valued `def` or `structure *Certificate : Prop` wrappers.

* **BUCKET 3 — Curved Spin-Bundle Global Holonomy (`[bucket_3_open_debt]`):**
  - Global obstruction classes on curved pseudo-Riemannian spin manifolds $M^{r,s}$
    remain outside this algebraic Clifford–CAR polyform scope.
-/

namespace InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset

universe u
variable {B : Type u} [Ring B]

-- ============================================================================
-- 1. RECURSIVE NON-COMMUTATIVE MATRIX RING `Mat2` & DECISION TACTIC `nc_mat`
-- ============================================================================

/-- $2 \times 2$ matrix carrier over an arbitrary type $\alpha$, supporting recursive
non-commutative block operator algebras `Mat2 B` and `Op4 B = Mat2 (Mat2 B)`. -/
@[ext]
structure Mat2 (α : Type u) where
  /-- Top-left $(1,1)$ matrix entry. -/
  a11 : α
  /-- Top-right $(1,2)$ matrix entry. -/
  a12 : α
  /-- Bottom-left $(2,1)$ matrix entry. -/
  a21 : α
  /-- Bottom-right $(2,2)$ matrix entry. -/
  a22 : α
  deriving DecidableEq, Repr

/-- Closed concrete integer witness inhabiting `Mat2 ℤ`. -/
def mat2IntIdentity : Mat2 ℤ := ⟨1, 0, 0, 1⟩

namespace Mat2

/-- Zero matrix in `Mat2 B`. -/
@[simp] def zero : Mat2 B := ⟨0, 0, 0, 0⟩

/-- Identity matrix in `Mat2 B`. -/
@[simp] def one : Mat2 B := ⟨1, 0, 0, 1⟩

/-- Entrywise addition in `Mat2 B`. -/
@[simp] def add (A M : Mat2 B) : Mat2 B :=
  ⟨A.a11 + M.a11, A.a12 + M.a12, A.a21 + M.a21, A.a22 + M.a22⟩

/-- Entrywise negation in `Mat2 B`. -/
@[simp] def neg (A : Mat2 B) : Mat2 B :=
  ⟨-A.a11, -A.a12, -A.a21, -A.a22⟩

/-- Entrywise subtraction in `Mat2 B`. -/
@[simp] def sub (A M : Mat2 B) : Mat2 B :=
  ⟨A.a11 - M.a11, A.a12 - M.a12, A.a21 - M.a21, A.a22 - M.a22⟩

/-- Non-commutative $2 \times 2$ matrix multiplication in `Mat2 B`. -/
@[simp] def mul (A M : Mat2 B) : Mat2 B :=
  ⟨A.a11 * M.a11 + A.a12 * M.a21, A.a11 * M.a12 + A.a12 * M.a22,
   A.a21 * M.a11 + A.a22 * M.a21, A.a21 * M.a12 + A.a22 * M.a22⟩

/-- Natural-number scalar multiplication in `Mat2 B`. -/
@[simp] def nsmulMat (n : ℕ) (A : Mat2 B) : Mat2 B :=
  ⟨n • A.a11, n • A.a12, n • A.a21, n • A.a22⟩

/-- Integer scalar multiplication in `Mat2 B`. -/
@[simp] def zsmulMat (n : ℤ) (A : Mat2 B) : Mat2 B :=
  ⟨n • A.a11, n • A.a12, n • A.a21, n • A.a22⟩

/-- `Zero` instance on `Mat2 B`. -/
instance instZeroMat2 : Zero (Mat2 B) := ⟨zero⟩
/-- `One` instance on `Mat2 B`. -/
instance instOneMat2  : One (Mat2 B)  := ⟨one⟩
/-- `Add` instance on `Mat2 B`. -/
instance instAddMat2  : Add (Mat2 B)  := ⟨add⟩
/-- `Neg` instance on `Mat2 B`. -/
instance instNegMat2  : Neg (Mat2 B)  := ⟨neg⟩
/-- `Sub` instance on `Mat2 B`. -/
instance instSubMat2  : Sub (Mat2 B)  := ⟨sub⟩
/-- `Mul` instance on `Mat2 B`. -/
instance instMulMat2  : Mul (Mat2 B)  := ⟨mul⟩

/-- `(0 : Mat2 B).a11 = 0`. -/
@[simp] lemma zero_a11 : (0 : Mat2 B).a11 = 0 := by have h : (0 : Mat2 B).a11 = 0 := rfl; exact h
/-- `(0 : Mat2 B).a12 = 0`. -/
@[simp] lemma zero_a12 : (0 : Mat2 B).a12 = 0 := by have h : (0 : Mat2 B).a12 = 0 := rfl; exact h
/-- `(0 : Mat2 B).a21 = 0`. -/
@[simp] lemma zero_a21 : (0 : Mat2 B).a21 = 0 := by have h : (0 : Mat2 B).a21 = 0 := rfl; exact h
/-- `(0 : Mat2 B).a22 = 0`. -/
@[simp] lemma zero_a22 : (0 : Mat2 B).a22 = 0 := by have h : (0 : Mat2 B).a22 = 0 := rfl; exact h
/-- `(1 : Mat2 B).a11 = 1`. -/
@[simp] lemma one_a11  : (1 : Mat2 B).a11 = 1 := by have h : (1 : Mat2 B).a11 = 1 := rfl; exact h
/-- `(1 : Mat2 B).a12 = 0`. -/
@[simp] lemma one_a12  : (1 : Mat2 B).a12 = 0 := by have h : (1 : Mat2 B).a12 = 0 := rfl; exact h
/-- `(1 : Mat2 B).a21 = 0`. -/
@[simp] lemma one_a21  : (1 : Mat2 B).a21 = 0 := by have h : (1 : Mat2 B).a21 = 0 := rfl; exact h
/-- `(1 : Mat2 B).a22 = 1`. -/
@[simp] lemma one_a22  : (1 : Mat2 B).a22 = 1 := by have h : (1 : Mat2 B).a22 = 1 := rfl; exact h
/-- `(A + M).a11 = A.a11 + M.a11`. -/
@[simp] lemma add_a11 (A M : Mat2 B) : (A + M).a11 = A.a11 + M.a11 := by
  have h : (A + M).a11 = A.a11 + M.a11 := rfl; exact h
/-- `(A + M).a12 = A.a12 + M.a12`. -/
@[simp] lemma add_a12 (A M : Mat2 B) : (A + M).a12 = A.a12 + M.a12 := by
  have h : (A + M).a12 = A.a12 + M.a12 := rfl; exact h
/-- `(A + M).a21 = A.a21 + M.a21`. -/
@[simp] lemma add_a21 (A M : Mat2 B) : (A + M).a21 = A.a21 + M.a21 := by
  have h : (A + M).a21 = A.a21 + M.a21 := rfl; exact h
/-- `(A + M).a22 = A.a22 + M.a22`. -/
@[simp] lemma add_a22 (A M : Mat2 B) : (A + M).a22 = A.a22 + M.a22 := by
  have h : (A + M).a22 = A.a22 + M.a22 := rfl; exact h
/-- `(-A).a11 = -A.a11`. -/
@[simp] lemma neg_a11 (A : Mat2 B) : (-A).a11 = -A.a11 := by
  have h : (-A).a11 = -A.a11 := rfl; exact h
/-- `(-A).a12 = -A.a12`. -/
@[simp] lemma neg_a12 (A : Mat2 B) : (-A).a12 = -A.a12 := by
  have h : (-A).a12 = -A.a12 := rfl; exact h
/-- `(-A).a21 = -A.a21`. -/
@[simp] lemma neg_a21 (A : Mat2 B) : (-A).a21 = -A.a21 := by
  have h : (-A).a21 = -A.a21 := rfl; exact h
/-- `(-A).a22 = -A.a22`. -/
@[simp] lemma neg_a22 (A : Mat2 B) : (-A).a22 = -A.a22 := by
  have h : (-A).a22 = -A.a22 := rfl; exact h
/-- `(A - M).a11 = A.a11 - M.a11`. -/
@[simp] lemma sub_a11 (A M : Mat2 B) : (A - M).a11 = A.a11 - M.a11 := by
  have h : (A - M).a11 = A.a11 - M.a11 := rfl; exact h
/-- `(A - M).a12 = A.a12 - M.a12`. -/
@[simp] lemma sub_a12 (A M : Mat2 B) : (A - M).a12 = A.a12 - M.a12 := by
  have h : (A - M).a12 = A.a12 - M.a12 := rfl; exact h
/-- `(A - M).a21 = A.a21 - M.a21`. -/
@[simp] lemma sub_a21 (A M : Mat2 B) : (A - M).a21 = A.a21 - M.a21 := by
  have h : (A - M).a21 = A.a21 - M.a21 := rfl; exact h
/-- `(A - M).a22 = A.a22 - M.a22`. -/
@[simp] lemma sub_a22 (A M : Mat2 B) : (A - M).a22 = A.a22 - M.a22 := by
  have h : (A - M).a22 = A.a22 - M.a22 := rfl; exact h
/-- `(A * M).a11 = A.a11 * M.a11 + A.a12 * M.a21`. -/
@[simp] lemma mul_a11 (A M : Mat2 B) : (A * M).a11 = A.a11 * M.a11 + A.a12 * M.a21 := by
  have h : (A * M).a11 = A.a11 * M.a11 + A.a12 * M.a21 := rfl; exact h
/-- `(A * M).a12 = A.a11 * M.a12 + A.a12 * M.a22`. -/
@[simp] lemma mul_a12 (A M : Mat2 B) : (A * M).a12 = A.a11 * M.a12 + A.a12 * M.a22 := by
  have h : (A * M).a12 = A.a11 * M.a12 + A.a12 * M.a22 := rfl; exact h
/-- `(A * M).a21 = A.a21 * M.a11 + A.a22 * M.a21`. -/
@[simp] lemma mul_a21 (A M : Mat2 B) : (A * M).a21 = A.a21 * M.a11 + A.a22 * M.a21 := by
  have h : (A * M).a21 = A.a21 * M.a11 + A.a22 * M.a21 := rfl; exact h
/-- `(A * M).a22 = A.a21 * M.a12 + A.a22 * M.a22`. -/
@[simp] lemma mul_a22 (A M : Mat2 B) : (A * M).a22 = A.a21 * M.a12 + A.a22 * M.a22 := by
  have h : (A * M).a22 = A.a21 * M.a12 + A.a22 * M.a22 := rfl; exact h

macro "nc_mat" : tactic =>
  `(tactic|
    (try ext
     all_goals try ext
     all_goals
       simp only [zero_a11, zero_a12, zero_a21, zero_a22,
                  one_a11, one_a12, one_a21, one_a22,
                  add_a11, add_a12, add_a21, add_a22,
                  neg_a11, neg_a12, neg_a21, neg_a22,
                  sub_a11, sub_a12, sub_a21, sub_a22,
                  mul_a11, mul_a12, mul_a21, mul_a22,
                  zero, one, add, neg, sub, mul,
                  mul_add, add_mul, sub_mul, mul_sub,
                  mul_zero, zero_mul, mul_one, one_mul,
                  add_zero, zero_add, sub_zero, zero_sub,
                  neg_mul, mul_neg, neg_add_rev, neg_sub, sub_neg_eq_add, neg_neg, neg_zero,
                  mul_assoc]
       try abel))

/-- Recursive `Ring` instance on `Mat2 B` for any non-commutative `[Ring B]`. -/
instance instRingMat2 : Ring (Mat2 B) where
  add := add
  add_assoc := by intros; nc_mat
  zero := zero
  zero_add := by intros; nc_mat
  add_zero := by intros; nc_mat
  nsmul := nsmulMat
  nsmul_zero := by intros; ext <;> exact AddMonoid.nsmul_zero _
  nsmul_succ := by intros; ext <;> exact AddMonoid.nsmul_succ _ _
  zsmul := zsmulMat
  zsmul_zero' := by intros; ext <;> exact SubNegMonoid.zsmul_zero' _
  zsmul_succ' := by intros; ext <;> exact SubNegMonoid.zsmul_succ' _ _
  zsmul_neg' := by intros; ext <;> exact SubNegMonoid.zsmul_neg' _ _
  neg := neg
  sub := sub
  sub_eq_add_neg := by intros; nc_mat
  neg_add_cancel := by intros; nc_mat
  add_comm := by intros; nc_mat
  mul := mul
  left_distrib := by intros; nc_mat
  right_distrib := by intros; nc_mat
  zero_mul := by intros; nc_mat
  mul_zero := by intros; nc_mat
  mul_assoc := by intros; nc_mat
  one := one
  one_mul := by intros; nc_mat
  mul_one := by intros; nc_mat

/-- Ring commutator $[x, y] = x y - y x$ in any ring `A`. -/
@[simp] def rcomm {A : Type u} [Ring A] (x y : A) : A := x * y - y * x

/-- Ring anticommutator $\{x, y\} = x y + y x$ in any ring `A`. -/
@[simp] def racomm {A : Type u} [Ring A] (x y : A) : A := x * y + y * x

/-- Split reflection matrix $E_x = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ with $E_x^2 = +1$. -/
@[simp] def Ex : Mat2 B := ⟨0, 1, 1, 0⟩

/-- Symplectic complex matrix $E_y = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ with $E_y^2 = -1$. -/
@[simp] def Ey : Mat2 B := ⟨0, -1, 1, 0⟩

/-- Diagonal grading matrix $E_z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$ with $E_z^2 = +1$. -/
@[simp] def Ez : Mat2 B := ⟨1, 0, 0, -1⟩

/-- Elementary matrix unit $E_{00} = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. -/
@[simp] def E00 : Mat2 B := ⟨1, 0, 0, 0⟩

/-- Elementary matrix unit $E_{01} = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$. -/
@[simp] def E01 : Mat2 B := ⟨0, 1, 0, 0⟩

/-- Elementary matrix unit $E_{10} = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$. -/
@[simp] def E10 : Mat2 B := ⟨0, 0, 1, 0⟩

/-- Elementary matrix unit $E_{11} = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$. -/
@[simp] def E11 : Mat2 B := ⟨0, 0, 0, 1⟩

/-- Diagonal embedding $\mathrm{diag}_2(c) = \begin{pmatrix} c & 0 \\ 0 & c \end{pmatrix}$. -/
@[simp] def diagScalar (c : B) : Mat2 B := ⟨c, 0, 0, c⟩

-- ============================================================================
-- ARCHETYPE K₀: BRAUER–WEYL DUAL SIGNATURE LIFTS (EQUATIONS (1.1)–(1.3))
-- ============================================================================

/-- Equation (1.2) lift $\Gamma^{(+)}(\gamma) = \begin{pmatrix} 0 & \gamma \\ \gamma & 0 \end{pmatrix}$
for $\mathrm{Cl}(r+1, s+1) \cong \mathrm{Cl}(r, s) \otimes M_2(\mathbb{R})$. -/
@[simp] def liftSplit (γ : B) : Mat2 B := ⟨0, γ, γ, 0⟩

/-- Equation (1.3) lift $\Gamma^{(-)}(\gamma) = \begin{pmatrix} 0 & \gamma \\ -\gamma & 0 \end{pmatrix}$
for $\mathrm{Cl}(s+2, r) \cong \mathrm{Cl}(r, s) \otimes M_2(\mathbb{R})$. -/
@[simp] def liftFlip (γ : B) : Mat2 B := ⟨0, γ, -γ, 0⟩

/--
**Archetype $\mathcal{K}_0$ (`archetype_K0_brauer_weyl_signature_lifts`):**
Over ANY non-commutative ring `[Ring B]` and ANY `γ₁, γ₂ ∈ B`:
1. **Equation (1.2) `(r+1, s+1)` Lift:**
   `{liftSplit γ₁, liftSplit γ₂} = diagScalar({γ₁, γ₂})`, while `liftSplit γ₁` anticommutes
   with `Ez` (`Ez² = +1`) and `Ey` (`Ey² = -1`), and `{Ez, Ey} = 0`.
2. **Equation (1.3) `(s+2, r)` Signature-Flip Lift:**
   `{liftFlip γ₁, liftFlip γ₂} = -diagScalar({γ₁, γ₂})`, while `liftFlip γ₁` anticommutes
   with `Ez` (`Ez² = +1`) and `Ex` (`Ex² = +1`), and `{Ez, Ex} = 0`.
-/
theorem archetype_K0_brauer_weyl_signature_lifts (γ1 γ2 : B) :
    racomm (liftSplit γ1) (liftSplit γ2) = diagScalar (racomm γ1 γ2) ∧
    racomm (liftSplit γ1) Ez = 0 ∧
    racomm (liftSplit γ1) Ey = 0 ∧
    (Ez : Mat2 B) * Ez = 1 ∧
    (Ey : Mat2 B) * Ey = -1 ∧
    racomm (Ez : Mat2 B) Ey = 0 ∧
    racomm (liftFlip γ1) (liftFlip γ2) = -diagScalar (racomm γ1 γ2) ∧
    racomm (liftFlip γ1) Ez = 0 ∧
    racomm (liftFlip γ1) Ex = 0 ∧
    (Ex : Mat2 B) * Ex = 1 ∧
    racomm (Ez : Mat2 B) Ex = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [liftSplit, liftFlip, diagScalar, Ex, Ey, Ez, racomm]; nc_mat

-- ============================================================================
-- ARCHETYPE K₁: MIXED STRUCTURES & ORTHOGONAL PRODUCT SPLITTING (SECTION 5.7)
-- ============================================================================

/-- $4 \times 4$ block operator algebra `Op4 B = Mat2 (Mat2 B)` over a non-commutative ring `B`. -/
abbrev Op4 (B : Type u) := Mat2 (Mat2 B)

/-- Orthogonal product structure $P_{\mathrm{prod}} = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix} \in \mathrm{Op}_4(B)$ (Definition 5.2). -/
@[simp] def P_prod : Op4 B := ⟨1, 0, 0, -1⟩

/-- Projector onto the $V^+$ (paracomplex) subspace $P_+ = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix} \in \mathrm{Op}_4(B)$. -/
@[simp] def ProjPlus : Op4 B := ⟨1, 0, 0, 0⟩

/-- Projector onto the $V^-$ (complex) subspace $P_- = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix} \in \mathrm{Op}_4(B)$. -/
@[simp] def ProjMinus : Op4 B := ⟨0, 0, 0, 1⟩

/-- Paracomplex structure $I_{\mathrm{para}} = \begin{pmatrix} E_x & 0 \\ 0 & 0 \end{pmatrix}$ acting on $V^+$ with $\ker(I_{\mathrm{para}}) = V^-$ (Eq. (5.23)). -/
@[simp] def I_para : Op4 B := ⟨Ex, 0, 0, 0⟩

/-- Complex structure $J_{\mathrm{comp}} = \begin{pmatrix} 0 & 0 \\ 0 & E_y \end{pmatrix}$ acting on $V^-$ with $\ker(J_{\mathrm{comp}}) = V^+$ (Eq. (5.23)). -/
@[simp] def J_comp : Op4 B := ⟨0, 0, 0, Ey⟩

/--
**Archetype $\mathcal{K}_1$ (`archetype_K1_mixed_structure_and_orthogonal_product_splitting`):**
Formalizes Section 5.7 (Props. 5.1 & 5.2, Eqs. (5.23)–(5.33)) in `Op4 B` over `[Ring B]`:
1. **Orthogonal Kernels (Eq. (5.23)):** `I_para * J_comp = 0` and `J_comp * I_para = 0`.
2. **Subspace Squares (Eq. (5.33) & (7.34)):**
   `I_para² = ProjPlus` (`+1` on `V⁺`) and `J_comp² = -ProjMinus` (`-1` on `V⁻`).
3. **Mixed Structure Square & Product Structure Recovery (Eq. (5.25) & Prop. 5.1):**
   `I_para² - J_comp² = 1` (corresponding to `K² = I² - J² = 1`) and
   `I_para² + J_comp² = P_prod` (corresponding to `K K̄ = I² + J² = P_prod` with `P_prod² = 1`).
4. **Eigenspace Invariance (Prop. 5.2, Eq. (5.31)):**
   `P_prod * I_para = I_para` and `P_prod * J_comp = -J_comp`.
-/
theorem archetype_K1_mixed_structure_and_orthogonal_product_splitting :
    (I_para : Op4 B) * J_comp = 0 ∧
    (J_comp : Op4 B) * I_para = 0 ∧
    (I_para : Op4 B) * I_para = ProjPlus ∧
    (J_comp : Op4 B) * J_comp = -ProjMinus ∧
    (I_para : Op4 B) * I_para - J_comp * J_comp = 1 ∧
    (I_para : Op4 B) * I_para + J_comp * J_comp = P_prod ∧
    (P_prod : Op4 B) * P_prod = 1 ∧
    (P_prod : Op4 B) * I_para = I_para ∧
    (P_prod : Op4 B) * J_comp = -J_comp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [I_para, J_comp, P_prod, ProjPlus, ProjMinus, Ex, Ey]; nc_mat

-- ============================================================================
-- ARCHETYPE K₂: 2-MODE CAR POLYFORM ALGEBRA & DERIVATION IDENTITIES (EQ. (2.24))
-- ============================================================================

/-- Mode-1 creation operator $b_1 = e_1 \wedge \cdot = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix} \in \mathrm{Op}_4(B)$. -/
@[simp] def b1 : Op4 B := ⟨0, 0, 1, 0⟩

/-- Mode-1 annihilation operator $b_1^\dagger = e_1 \lrcorner \cdot = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix} \in \mathrm{Op}_4(B)$. -/
@[simp] def b1_dag : Op4 B := ⟨0, 1, 0, 0⟩

/-- Mode-2 creation operator $b_2 = e_2 \wedge \cdot = \begin{pmatrix} E_{10} & 0 \\ 0 & -E_{10} \end{pmatrix} \in \mathrm{Op}_4(B)$ (with Jordan–Wigner grading). -/
@[simp] def b2 : Op4 B := ⟨E10, 0, 0, -E10⟩

/-- Mode-2 annihilation operator $b_2^\dagger = e_2 \lrcorner \cdot = \begin{pmatrix} E_{01} & 0 \\ 0 & -E_{01} \end{pmatrix} \in \mathrm{Op}_4(B)$. -/
@[simp] def b2_dag : Op4 B := ⟨E01, 0, 0, -E01⟩

/--
**Archetype $\mathcal{K}_2$ (`archetype_K2_two_mode_car_algebra_and_derivation_identities`):**
Over ANY non-commutative ring `[Ring B]`:
1. **Canonical Anticommutation Relations (Eq. (2.3)):**
   `b₁² = b₁†² = b₂² = b₂†² = 0`, `{b₁, b₁†} = 1`, `{b₂, b₂†} = 1`, and all cross-mode
   anticommutators vanish: `{b₁, b₂} = {b₁†, b₂†} = {b₁, b₂†} = {b₁†, b₂} = 0`.
2. **Resolution of Equation (2.24) (`gl(2)` vs. `spin(4)` Derivations):**
   - For bare `b_i b_j†`: `[b₁ b₁†, b₁] = +b₁`, `[b₁† b₁, b₁] = -b₁`, and `[b₁ b₂†, b₂] = +b₁`.
   - For the antisymmetrized `spin` generator `[b₁, b₁†] = b₁ b₁† - b₁† b₁`:
     `[[b₁, b₁†], b₁] = 2 • b₁`.
   - For the 2-form annihilation pair `b₁† b₂†`:
     `[b₁† b₂†, b₁] = -b₂†` and `[b₁† b₂†, b₂] = +b₁†`.
-/
theorem archetype_K2_two_mode_car_algebra_and_derivation_identities :
    (b1 : Op4 B) * b1 = 0 ∧
    (b1_dag : Op4 B) * b1_dag = 0 ∧
    (b2 : Op4 B) * b2 = 0 ∧
    (b2_dag : Op4 B) * b2_dag = 0 ∧
    racomm (b1 : Op4 B) b1_dag = 1 ∧
    racomm (b2 : Op4 B) b2_dag = 1 ∧
    racomm (b1 : Op4 B) b2 = 0 ∧
    racomm (b1_dag : Op4 B) b2_dag = 0 ∧
    racomm (b1 : Op4 B) b2_dag = 0 ∧
    racomm (b1_dag : Op4 B) b2 = 0 ∧
    rcomm ((b1 : Op4 B) * b1_dag) b1 = b1 ∧
    rcomm ((b1_dag : Op4 B) * b1) b1 = -b1 ∧
    rcomm (rcomm (b1 : Op4 B) b1_dag) b1 = b1 + b1 ∧
    rcomm ((b1 : Op4 B) * b2_dag) b2 = b1 ∧
    rcomm ((b1_dag : Op4 B) * b2_dag) b1 = -b2_dag ∧
    rcomm ((b1_dag : Op4 B) * b2_dag) b2 = b1_dag := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [b1, b1_dag, b2, b2_dag, E01, E10, rcomm, racomm]; nc_mat

-- ============================================================================
-- ARCHETYPE K₃: PURE SPINOR STABILIZER `sl(2) ⋉ N` (SECTIONS 3.3, 5.4, 7.3)
-- ============================================================================

/-- Vacuum pure spinor projector $\Psi_{\mathrm{vac}} = b_1^\dagger b_1 b_2^\dagger b_2 = \begin{pmatrix} E_{00} & 0 \\ 0 & 0 \end{pmatrix}$ (representing $1 \in \Lambda^0$). -/
@[simp] def PsiVac : Op4 B := (b1_dag * b1) * (b2_dag * b2)

/-- Top-form pure spinor projector $\Psi_{\mathrm{top}} = b_1 b_1^\dagger b_2 b_2^\dagger = \begin{pmatrix} 0 & 0 \\ 0 & E_{11} \end{pmatrix}$ (representing $e_1 \wedge e_2 \in \Lambda^2$). -/
@[simp] def PsiTop : Op4 B := (b1 * b1_dag) * (b2 * b2_dag)

/-- $\mathfrak{sl}(2)$ Cartan generator $H_{12} = b_1 b_1^\dagger - b_2 b_2^\dagger$ (Eq. (3.6) tracefree part). -/
@[simp] def sl2_H : Op4 B := b1 * b1_dag - b2 * b2_dag

/-- $\mathfrak{sl}(2)$ raising generator $E_+ = b_1 b_2^\dagger$. -/
@[simp] def sl2_Ep : Op4 B := b1 * b2_dag

/-- $\mathfrak{sl}(2)$ lowering generator $E_- = b_2 b_1^\dagger$. -/
@[simp] def sl2_Em : Op4 B := b2 * b1_dag

/-- Nilpotent 2-form $B$-field generator $\mathcal{N}_{12} = b_1 b_2 \in \mathfrak{N}$ (Eq. (3.8)). -/
@[simp] def nilpBField : Op4 B := b1 * b2

/-- Explicit $4 \times 4$ block evaluation of $\Psi_{\mathrm{vac}} = \begin{pmatrix} E_{00} & 0 \\ 0 & 0 \end{pmatrix}$. -/
theorem psiVac_eq : (PsiVac : Op4 B) = ⟨E00, 0, 0, 0⟩ := by
  have h1 : (b1_dag : Op4 B) * b1 = ⟨1, 0, 0, 0⟩ := by simp only [b1, b1_dag]; nc_mat
  have h2 : (b2_dag : Op4 B) * b2 = ⟨E00, 0, 0, E00⟩ := by simp only [b2, b2_dag, E00, E01, E10]; nc_mat
  rw [PsiVac, h1, h2]; simp only [E00]; nc_mat

/-- Explicit $4 \times 4$ block evaluation of $\Psi_{\mathrm{top}} = \begin{pmatrix} 0 & 0 \\ 0 & E_{11} \end{pmatrix}$. -/
theorem psiTop_eq : (PsiTop : Op4 B) = ⟨0, 0, 0, E11⟩ := by
  have h1 : (b1 : Op4 B) * b1_dag = ⟨0, 0, 0, 1⟩ := by simp only [b1, b1_dag]; nc_mat
  have h2 : (b2 : Op4 B) * b2_dag = ⟨E11, 0, 0, E11⟩ := by simp only [b2, b2_dag, E11, E01, E10]; nc_mat
  rw [PsiTop, h1, h2]; simp only [E11]; nc_mat

/--
**Archetype $\mathcal{K}_3$ (`archetype_K3_complementary_pure_spinors_and_parabolic_stabilizer`):**
Formalizes Section 3.3 (Eqs. (3.6)–(3.8)) and Section 7.3 in `Op4 B` over `[Ring B]`:
1. **Complementary MTN Annihilators:**
   - `Ψ_top` is annihilated on the left by all creation operators (`b₁ * Ψ_top = 0`, `b₂ * Ψ_top = 0`).
   - `Ψ_vac` is annihilated on the left by all annihilation operators (`b₁† * Ψ_vac = 0`, `b₂† * Ψ_vac = 0`).
2. **Parabolic Pure Spinor Stabilizer `sl(2) ⋉ N` (Eq. (3.8)):**
   - `(sl2_H, sl2_Ep, sl2_Em)` close into `sl(2)`: `[E_+, E_-] = H₁₂`, `[H₁₂, E_+] = 2 E_+`, `[H₁₂, E_-] = -2 E_-`.
   - Both `sl(2)` AND the nilpotent 2-form B-field `nilpBField = b₁ b₂` (`nilpBField² = 0`)
     annihilate the top pure spinor `Ψ_top` from the left.
-/
theorem archetype_K3_complementary_pure_spinors_and_parabolic_stabilizer :
    (b1 : Op4 B) * PsiTop = 0 ∧
    (b2 : Op4 B) * PsiTop = 0 ∧
    (b1_dag : Op4 B) * PsiVac = 0 ∧
    (b2_dag : Op4 B) * PsiVac = 0 ∧
    rcomm (sl2_Ep : Op4 B) sl2_Em = sl2_H ∧
    rcomm (sl2_H : Op4 B) sl2_Ep  = sl2_Ep + sl2_Ep ∧
    rcomm (sl2_H : Op4 B) sl2_Em  = -(sl2_Em + sl2_Em) ∧
    (nilpBField : Op4 B) * nilpBField = 0 ∧
    (sl2_H : Op4 B) * PsiTop = 0 ∧
    (sl2_Ep : Op4 B) * PsiTop = 0 ∧
    (sl2_Em : Op4 B) * PsiTop = 0 ∧
    (nilpBField : Op4 B) * PsiTop = 0 := by
  have hH : (sl2_H : Op4 B) = ⟨-E11, 0, 0, E00⟩ := by
    simp only [sl2_H, b1, b1_dag, b2, b2_dag, E00, E01, E10, E11]; nc_mat
  have hEp : (sl2_Ep : Op4 B) = ⟨0, 0, E01, 0⟩ := by
    simp only [sl2_Ep, b1, b2_dag, E01]; nc_mat
  have hEm : (sl2_Em : Op4 B) = ⟨0, E10, 0, 0⟩ := by
    simp only [sl2_Em, b2, b1_dag, E10]; nc_mat
  have hN : (nilpBField : Op4 B) = ⟨0, 0, E10, 0⟩ := by
    simp only [nilpBField, b1, b2, E10]; nc_mat
  rw [psiTop_eq, psiVac_eq, hH, hEp, hEm, hN]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [b1, b1_dag, b2, b2_dag, E00, E01, E10, E11, rcomm]; nc_mat

-- ============================================================================
-- ARCHETYPE K₄: PARACOMPLEX RECOVERY & CHIRALITY VOLUME INVOLUTION (SECTION 7.3)
-- ============================================================================

/-- $\mathrm{Cl}(2, 2)$ generator $\Gamma_1 = b_1 + b_1^\dagger$ (Equation (7.36)). -/
@[simp] def Gam1 : Op4 B := b1 + b1_dag

/-- $\mathrm{Cl}(2, 2)$ generator $\Gamma_3 = b_1 - b_1^\dagger$ (Equation (7.36)). -/
@[simp] def Gam3 : Op4 B := b1 - b1_dag

/-- $\mathrm{Cl}(2, 2)$ generator $\Gamma_2 = b_2 + b_2^\dagger$ (Equation (7.36)). -/
@[simp] def Gam2 : Op4 B := b2 + b2_dag

/-- $\mathrm{Cl}(2, 2)$ generator $\Gamma_4 = b_2 - b_2^\dagger$ (Equation (7.36)). -/
@[simp] def Gam4 : Op4 B := b2 - b2_dag

/-- Recovered paracomplex structure on Plane 1: $I_{\mathrm{para}}^{(1)} = [b_1^\dagger, b_1] = \frac{1}{2}[\Gamma_1, \Gamma_3]$ (Eq. (3.9)). -/
@[simp] def I_rec1 : Op4 B := rcomm b1_dag b1

/-- Recovered paracomplex structure on Plane 2: $I_{\mathrm{para}}^{(2)} = [b_2^\dagger, b_2] = \frac{1}{2}[\Gamma_2, \Gamma_4]$ (Eq. (3.9)). -/
@[simp] def I_rec2 : Op4 B := rcomm b2_dag b2

/-- Chirality volume operator $R = \Gamma_1 \Gamma_3 \Gamma_2 \Gamma_4 = I_{\mathrm{rec}, 1} I_{\mathrm{rec}, 2}$ (Equation (3.3)). -/
@[simp] def R_vol : Op4 B := I_rec1 * I_rec2

/-- Two-matrix block evaluation of $I_{\mathrm{rec}, 1} = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$. -/
theorem i_rec1_eq : (I_rec1 : Op4 B) = ⟨1, 0, 0, -1⟩ := by
  simp only [I_rec1, b1, b1_dag, rcomm]; nc_mat

/-- Two-matrix block evaluation of $I_{\mathrm{rec}, 2} = \begin{pmatrix} E_z & 0 \\ 0 & E_z \end{pmatrix}$. -/
theorem i_rec2_eq : (I_rec2 : Op4 B) = ⟨Ez, 0, 0, Ez⟩ := by
  simp only [I_rec2, b2, b2_dag, E01, E10, Ez, rcomm]; nc_mat

/-- Two-matrix block evaluation of the chirality volume operator $R_{\mathrm{vol}} = \begin{pmatrix} E_z & 0 \\ 0 & -E_z \end{pmatrix}$. -/
theorem r_vol_eq : (R_vol : Op4 B) = ⟨Ez, 0, 0, -Ez⟩ := by
  rw [R_vol, i_rec1_eq, i_rec2_eq]
  simp only [Ez]; nc_mat

/--
**Archetype $\mathcal{K}_4$ (`archetype_K4_paracomplex_recovery_and_chirality_volume_involution`):**
Formalizes Section 3.1 (Eq. (3.3)), Section 3.3 (Eq. (3.9)), and Section 7.3 (Eq. (7.36)–(7.45)):
1. **Cl(2, 2) Signature:** `Γ₁² = 1`, `Γ₂² = 1`, `Γ₃² = -1`, `Γ₄² = -1`.
2. **Paracomplex Recovery from `[Γ, Γ]`:**
   `[Γ₁, Γ₃] = 2 • I_rec1` and `[Γ₂, Γ₄] = 2 • I_rec2`, with `I_rec1² = 1` and `I_rec2² = 1`.
3. **Eigenspace Separation of the Complementary MTN Subspaces `E⁺ = Span(b_i†)` and `E⁻ = Span(b_i)`:**
   `I_rec1 * b₁† = +b₁†`, `I_rec1 * b₁ = -b₁`, `I_rec2 * b₂† = +b₂†`, and `I_rec2 * b₂ = -b₂`.
4. **Volume Involution `R = I_rec1 * I_rec2` (Eq. (3.3)):**
   `R² = 1`, `{R, Γ_A} = 0` for all `A ∈ {1, 2, 3, 4}`, and `R` fixes both even pure spinors
   (`R * Ψ_vac = Ψ_vac` and `R * Ψ_top = Ψ_top`).
-/
theorem archetype_K4_paracomplex_recovery_and_chirality_volume_involution :
    (Gam1 : Op4 B) * Gam1 = 1 ∧
    (Gam2 : Op4 B) * Gam2 = 1 ∧
    (Gam3 : Op4 B) * Gam3 = -1 ∧
    (Gam4 : Op4 B) * Gam4 = -1 ∧
    rcomm (Gam1 : Op4 B) Gam3 = I_rec1 + I_rec1 ∧
    rcomm (Gam2 : Op4 B) Gam4 = I_rec2 + I_rec2 ∧
    (I_rec1 : Op4 B) * I_rec1 = 1 ∧
    (I_rec2 : Op4 B) * I_rec2 = 1 ∧
    (I_rec1 : Op4 B) * b1_dag = b1_dag ∧
    (I_rec1 : Op4 B) * b1     = -b1 ∧
    (I_rec2 : Op4 B) * b2_dag = b2_dag ∧
    (I_rec2 : Op4 B) * b2     = -b2 ∧
    (R_vol : Op4 B) * R_vol = 1 ∧
    racomm (R_vol : Op4 B) Gam1 = 0 ∧
    racomm (R_vol : Op4 B) Gam2 = 0 ∧
    racomm (R_vol : Op4 B) Gam3 = 0 ∧
    racomm (R_vol : Op4 B) Gam4 = 0 ∧
    (R_vol : Op4 B) * PsiVac = PsiVac ∧
    (R_vol : Op4 B) * PsiTop = PsiTop := by
  rw [i_rec1_eq, i_rec2_eq, r_vol_eq, psiVac_eq, psiTop_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · try simp only [Gam1, Gam2, Gam3, Gam4, b1, b1_dag, b2, b2_dag,
                   E00, E01, E10, E11, Ez, rcomm, racomm]
    nc_mat

/-- Explicit non-commutativity witness in `Op4 ℤ`: `b₁ * b₁† ≠ b₁† * b₁`. -/
theorem bhojaKrasnov_car_noncommutative :
    (b1 : Op4 ℤ) * (b1_dag : Op4 ℤ) ≠ (b1_dag : Op4 ℤ) * (b1 : Op4 ℤ) := by
  intro h
  have h11 : (((b1 : Op4 ℤ) * (b1_dag : Op4 ℤ)).a11).a11 =
      (((b1_dag : Op4 ℤ) * (b1 : Op4 ℤ)).a11).a11 := by rw [h]
  revert h11
  decide

end Mat2

end InfoGeometry.Canonical.BhojaKrasnovSpinorPolyformMixedParabolicPoset
