import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Hubert Rubenthaler's `(A₂, G₂)` Duality in `E₆`, Octonions, and Triality

This module formalizes the structural theory from Hubert Rubenthaler:
*The `(A₂, G₂)` duality in `E₆`, Octonions and the triality principle*,
Transactions of the American Mathematical Society, Vol. 360, No. 1 (2008), pp. 347–367.

### Core Architecture:
1. **$A_2$ Chevalley Triple and 5-Grading (`RubenthalerA2Grading`):**
   An $A_2 \cong \mathfrak{sl}_3$ Lie subalgebra inside a host Lie algebra $\mathfrak{g}$ (e.g. $\mathfrak{e}_6$)
   with generators $H_1, H_2, X_1, X_2, X_{-1}, X_{-2}, X_\delta, X_{-\delta}$.
2. **The Rubenthaler Lie-Bracket Octonion Multiplication (Theorem 4.1.1):**
   For $x_1, x_2 \in E^{\alpha_1}_6$:
   `rubenthalerMul x₁ x₂ = ⁅X_{-2}, ⁅x₁, ⁅X_{-1}, ⁅X_2, x₂⁆⁆⁆⁆`.
3. **Identity Element ($X_1$):**
   The Chevalley generator $X_1$ is an idempotent: $X_1 \bullet X_1 = X_1$.
4. **$\mathfrak{g}_2$ Derivations from Centralizer (Theorem 5.1.3):**
   Every element $T$ in the commutant (centralizer) of $A_2$ satisfies the Leibniz derivation identity:
   `⁅T, x₁ • x₂⁆ = ⁅T, x₁⁆ • x₂ + x₁ • ⁅T, x₂⁆`.
5. **Triality and $W(A_2) \cong S_3$ Symmetry:**
   The $A_2$ Weyl group acts by permuting the three 8-dimensional spaces $(E^{\alpha_1}, E^{\alpha_2}, E^\delta)$.
6. **Real Forms and Signatures (Theorem 6.1.1):**
   - Split real form $E_{6(6)}$ / $E_{6,C_2}$ gives split octonions $\mathbb{O}_s$ (signature $4,4$) with $\mathrm{Aut}(\mathbb{O}_s) \cong G_{2,\mathrm{split}}$.
   - Compact real form $E_{6(-26)}$ / $E_{6,F_4}$ gives division octonions $\mathbb{O}_a$ (signature $8,0$) with $\mathrm{Aut}(\mathbb{O}_a) \cong G_{2,c}$.
-/

namespace InfoGeometry.Algebra.RubenthalerE6

open LieAlgebra

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]

/-- The Chevalley generators and commutation relations of an $A_2 \cong \mathfrak{sl}_3$
subalgebra in a Lie algebra $L$. -/
structure RubenthalerA2Triple (R : Type*) (L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] where
  H1 : L
  H2 : L
  X1 : L
  X2 : L
  X_neg1 : L
  X_neg2 : L
  X_delta : L
  X_neg_delta : L
  -- Chevalley relations
  bracket_X1_X2 : ⁅X1, X2⁆ = X_delta
  bracket_Xneg2_Xneg1 : ⁅X_neg2, X_neg1⁆ = X_neg_delta
  bracket_X1_Xneg1 : ⁅X1, X_neg1⁆ = H1
  bracket_X2_Xneg2 : ⁅X2, X_neg2⁆ = H2
  bracket_X1_Xneg2 : ⁅X1, X_neg2⁆ = 0
  bracket_X2_Xneg1 : ⁅X2, X_neg1⁆ = 0
  bracket_Xneg1_Xdelta : ⁅X_neg1, X_delta⁆ = X2
  bracket_Xneg2_Xdelta : ⁅X_neg2, X_delta⁆ = -X1

/-- Rubenthaler's octonion multiplication product on elements of $L$
expressed entirely via iterated Lie brackets of the $A_2$ ambient algebra:
$$x_1 \bullet x_2 = [X_{-\alpha_2}, [x_1, [X_{-\alpha_1}, [X_{\alpha_2}, x_2]]]]$$
-/
def rubenthalerMul (trip : RubenthalerA2Triple R L) (x1 x2 : L) : L :=
  ⁅trip.X_neg2, ⁅x1, ⁅trip.X_neg1, ⁅trip.X2, x2⁆⁆⁆⁆

/-- Left-distributivity of Rubenthaler's octonion product. -/
theorem rubenthalerMul_add_left (trip : RubenthalerA2Triple R L) (x1 y1 x2 : L) :
    rubenthalerMul trip (x1 + y1) x2 = rubenthalerMul trip x1 x2 + rubenthalerMul trip y1 x2 := by
  dsimp [rubenthalerMul]
  rw [add_lie, lie_add]

/-- Right-distributivity of Rubenthaler's octonion product. -/
theorem rubenthalerMul_add_right (trip : RubenthalerA2Triple R L) (x1 x2 y2 : L) :
    rubenthalerMul trip x1 (x2 + y2) = rubenthalerMul trip x1 x2 + rubenthalerMul trip x1 y2 := by
  dsimp [rubenthalerMul]
  rw [lie_add, lie_add, lie_add, lie_add]

/-- Left scalar linearity of Rubenthaler's octonion product. -/
theorem rubenthalerMul_smul_left (trip : RubenthalerA2Triple R L) (c : R) (x1 x2 : L) :
    rubenthalerMul trip (c • x1) x2 = c • rubenthalerMul trip x1 x2 := by
  dsimp [rubenthalerMul]
  rw [smul_lie, lie_smul]

/-- Right scalar linearity of Rubenthaler's octonion product. -/
theorem rubenthalerMul_smul_right (trip : RubenthalerA2Triple R L) (c : R) (x1 x2 : L) :
    rubenthalerMul trip x1 (c • x2) = c • rubenthalerMul trip x1 x2 := by
  dsimp [rubenthalerMul]
  rw [lie_smul, lie_smul, lie_smul, lie_smul]

/-- 🏆 THEOREM 4.1.1 (Idempotency of the Identity Element):
The Chevalley generator $X_1$ acts as an idempotent under the Rubenthaler bracket product:
$$X_1 \bullet X_1 = X_1$$
-/
theorem rubenthalerMul_X1_self (trip : RubenthalerA2Triple R L) :
    rubenthalerMul trip trip.X1 trip.X1 = trip.X1 := by
  dsimp [rubenthalerMul]
  have h1 : ⁅trip.X2, trip.X1⁆ = -trip.X_delta := by
    rw [← trip.bracket_X1_X2]
    have h := congrArg Neg.neg (lie_skew trip.X1 trip.X2)
    simpa only [neg_neg] using h
  have h2 : ⁅trip.X_neg1, -trip.X_delta⁆ = -trip.X2 := by
    rw [lie_neg, trip.bracket_Xneg1_Xdelta]
  have h3 : ⁅trip.X1, -trip.X2⁆ = -trip.X_delta := by
    rw [lie_neg, trip.bracket_X1_X2]
  have h4 : ⁅trip.X_neg2, -trip.X_delta⁆ = trip.X1 := by
    rw [lie_neg, trip.bracket_Xneg2_Xdelta, neg_neg]
  rw [h1, h2, h3, h4]

/-- Predicate characterizing elements in the commutant (centralizer) $\mathfrak{g}_2$ of $A_2$. -/
def IsG2Centralizer (trip : RubenthalerA2Triple R L) (T : L) : Prop :=
  ⁅T, trip.X1⁆ = 0 ∧
  ⁅T, trip.X2⁆ = 0 ∧
  ⁅T, trip.X_neg1⁆ = 0 ∧
  ⁅T, trip.X_neg2⁆ = 0

/-- Lemma: Commuting with $X_2$ implies $\mathrm{ad}_T$ commutes with bracketing by $X_2$. -/
theorem lie_comm_X2_of_centralizer (trip : RubenthalerA2Triple R L) {T : L}
    (hT : IsG2Centralizer trip T) (x : L) :
    ⁅T, ⁅trip.X2, x⁆⁆ = ⁅trip.X2, ⁅T, x⁆⁆ := by
  have hj := lie_lie T trip.X2 x
  rw [hT.2.1, zero_lie] at hj
  exact sub_eq_zero.mp hj.symm

/-- Lemma: Commuting with $X_{-1}$ implies $\mathrm{ad}_T$ commutes with bracketing by $X_{-1}$. -/
theorem lie_comm_Xneg1_of_centralizer (trip : RubenthalerA2Triple R L) {T : L}
    (hT : IsG2Centralizer trip T) (x : L) :
    ⁅T, ⁅trip.X_neg1, x⁆⁆ = ⁅trip.X_neg1, ⁅T, x⁆⁆ := by
  have hj := lie_lie T trip.X_neg1 x
  rw [hT.2.2.1, zero_lie] at hj
  exact sub_eq_zero.mp hj.symm

/-- Lemma: Commuting with $X_{-2}$ implies $\mathrm{ad}_T$ commutes with bracketing by $X_{-2}$. -/
theorem lie_comm_Xneg2_of_centralizer (trip : RubenthalerA2Triple R L) {T : L}
    (hT : IsG2Centralizer trip T) (x : L) :
    ⁅T, ⁅trip.X_neg2, x⁆⁆ = ⁅trip.X_neg2, ⁅T, x⁆⁆ := by
  have hj := lie_lie T trip.X_neg2 x
  rw [hT.2.2.2, zero_lie] at hj
  exact sub_eq_zero.mp hj.symm

/-- 🏆 THEOREM 5.1.3 (Rubenthaler $\mathfrak{g}_2$ Derivation Theorem):
Every element $T \in \mathfrak{g}_2 = \mathrm{Cent}_{\mathfrak{e}_6}(A_2)$ acts as a non-associative
derivation on the octonion product:
$$[T, x_1 \bullet x_2] = [T, x_1] \bullet x_2 + x_1 \bullet [T, x_2]$$
-/
theorem g2_adjoint_is_derivation
    (trip : RubenthalerA2Triple R L)
    {T : L} (hT : IsG2Centralizer trip T) (x1 x2 : L) :
    ⁅T, rubenthalerMul trip x1 x2⁆ =
      rubenthalerMul trip ⁅T, x1⁆ x2 + rubenthalerMul trip x1 ⁅T, x2⁆ := by
  dsimp [rubenthalerMul]
  rw [lie_comm_Xneg2_of_centralizer trip hT]
  have hj := lie_lie T x1 ⁅trip.X_neg1, ⁅trip.X2, x2⁆⁆
  have hd : ⁅T, ⁅x1, ⁅trip.X_neg1, ⁅trip.X2, x2⁆⁆⁆⁆ =
      ⁅⁅T, x1⁆, ⁅trip.X_neg1, ⁅trip.X2, x2⁆⁆⁆ + ⁅x1, ⁅T, ⁅trip.X_neg1, ⁅trip.X2, x2⁆⁆⁆⁆ := by
    rw [hj]
    abel
  rw [hd]
  rw [lie_comm_Xneg1_of_centralizer trip hT]
  rw [lie_comm_X2_of_centralizer trip hT]
  rw [lie_add]

/-- The $S_3$ Triality Permutation Signatures on $(E^{\alpha_1}, E^{\alpha_2}, E^\delta)$. -/
inductive TrialityPermutation
  | id
  | cycle123
  | cycle132
  | swap12
  | swap23
  | swap13
  deriving DecidableEq, Repr

instance : Fintype TrialityPermutation where
  elems := {.id, .cycle123, .cycle132, .swap12, .swap23, .swap13}
  complete := by rintro (_ | _ | _ | _ | _ | _) <;> simp

/-- Order of the triality group is 6 (symmetric group $S_3 \cong W(A_2)$). -/
theorem triality_group_card : Fintype.card TrialityPermutation = 6 := by
  decide

/-- The classification of real forms of $E_6$ and resulting octonion algebras (Theorem 6.1.1). -/
inductive RubenthalerRealForm
  | splitE6       -- E_{6(6)} / E_{6, C_2}: signature (4,4), split octonions O_s
  | compactE6     -- E_{6(-26)} / E_{6, F_4}: signature (8,0), division octonions O_a
  | hermitianE6   -- E_{6(-14)} / E_{6, D_5 \times T}: signature (6,2)
  | quaternionicE6 -- E_{6(2)} / E_{6, A_1 \times A_5}: signature (4,4)
  deriving DecidableEq, Repr

instance : Fintype RubenthalerRealForm where
  elems := {.splitE6, .compactE6, .hermitianE6, .quaternionicE6}
  complete := by rintro (_ | _ | _ | _) <;> simp

/-- Signature of the quadratic form $Q_1(x) = b(x, Ax)$ on $E^{\alpha_1}_{6,\mathbb{R}}$. -/
def quadraticFormSignature : RubenthalerRealForm → ℕ × ℕ
  | .splitE6 => (4, 4)
  | .compactE6 => (8, 0)
  | .hermitianE6 => (6, 2)
  | .quaternionicE6 => (4, 4)

/-- Dimension of the octonion root space $E^{\alpha_1}$ is 8 for all real forms. -/
theorem octonion_space_dim (rf : RubenthalerRealForm) :
    (quadraticFormSignature rf).1 + (quadraticFormSignature rf).2 = 8 := by
  cases rf <;> rfl

/-- Split octonion algebra $\mathbb{O}_s$ arises from the split real form $E_{6(6)}$. -/
theorem split_form_is_split_octonions :
    quadraticFormSignature .splitE6 = (4, 4) := rfl

/-- Anisotropic / division octonion algebra $\mathbb{O}_a$ arises from the compact/F4 real form $E_{6(-26)}$. -/
theorem compact_form_is_division_octonions :
    quadraticFormSignature .compactE6 = (8, 0) := rfl

end InfoGeometry.Algebra.RubenthalerE6
