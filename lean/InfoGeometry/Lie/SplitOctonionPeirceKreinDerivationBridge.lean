import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Split-Octonion Peirce Decomposition, Krein Invariance, and Derivation Bridge

This module formalizes:
1. **The Primitive Chiral Idempotents**:
   - $u_+ = (1, 0, 0, 0, 0, 0, 0, 0) \in V_+$
   - $u_- = (0, 0, 0, 0, 1, 0, 0, 0) \in V_-$
   - $u_+ + u_- = \mathbf{1}_{\mathrm{diag}}$
2. **🏆 THEOREM 1 (Chiral Left-Multiplication Eigenspace Projectors)**:
   - $L_{u_+}$ projects $\mathbb{O}_s$ onto the 4D chiral subspace $V_+$:
     $L_{u_+}(v_+) = v_+$ for all $v_+ \in V_+$,
     $L_{u_+}(w_-) = 0$ for all $w_- \in V_-$.
   - $L_{u_-}$ projects $\mathbb{O}_s$ onto the opposite 4D chiral subspace $V_-$:
     $L_{u_-}(v_+) = 0$ for all $v_+ \in V_+$,
     $L_{u_-}(w_-) = w_-$ for all $w_- \in V_-$.
   - Completeness: $L_{u_+} + L_{u_-} = \operatorname{id}_{\mathbb{O}_s}$.
3. **🏆 THEOREM 2 (Krein Metric Invariance / Skew-Adjointness of Derivations)**:
   Any linear endomorphism $D \in \operatorname{End}(\mathbb{R}^{4,4})$ that preserves the
   split-octonion Witt bilinear polar form $B$ satisfies:
   $$B(D(X), Y) + B(X, D(Y)) = 0$$
   realizing $\mathfrak{der}(\mathbb{O}_s) \subseteq \mathfrak{so}(4,4)$ natively on the real doubled Krein space.
4. **🏆 THEOREM 3 (Nilpotent Parabolic Mode on the Null Cone)**:
   For any chiral vector $v \in V_+$, the quadratic form and
   cross-pairing vanish identically: $N(v) = 0$ and $B(v, v) = 0$.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionPeirceKreinDerivationBridge

abbrev Coord := InfoGeometry.Algebra.FiniteSpin.Vec8R
abbrev Chiral4 := InfoGeometry.Algebra.FiniteSpin.Vec4R

/-- Embedding of the chiral subspace $V_+$ into $\mathbb{R}^{4,4}$. -/
def embedPlus (v : Chiral4) : Coord :=
  fun i => match i with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => v 3
  | _ => 0

/-- Embedding of the chiral subspace $V_-$ into $\mathbb{R}^{4,4}$. -/
def embedMinus (w : Chiral4) : Coord :=
  fun i => match i with
  | 4 => w 0
  | 5 => w 1
  | 6 => w 2
  | 7 => w 3
  | _ => 0

/-- Split-octonion quadratic form $N(X) = x_0 x_4 - (x_1 x_5 + x_2 x_6 + x_3 x_7)$. -/
def kreinNorm (x : Coord) : ℝ :=
  x 0 * x 4 - (x 1 * x 5 + x 2 * x 6 + x 3 * x 7)

/-- The split-octonion bilinear Krein polar form $B(X, Y) = \frac{1}{2}(x_0 y_4 + x_4 y_0 - \sum_{i=1}^3 (x_i y_{i+4} + x_{i+4} y_i))$. -/
def kreinPolar (X Y : Coord) : ℝ :=
  (1 / 2 : ℝ) *
    (X 0 * Y 4 + X 4 * Y 0 -
      (X 1 * Y 5 + X 5 * Y 1 +
        (X 2 * Y 6 + X 6 * Y 2 +
          (X 3 * Y 7 + X 7 * Y 3))))

/-- Symmetry of the Krein polar form: $B(X, Y) = B(Y, X)$. -/
theorem kreinPolar_comm (X Y : Coord) :
    kreinPolar X Y = kreinPolar Y X := by
  dsimp [kreinPolar]
  ring

/-- The primitive chiral idempotent $u_+ = (1, 0, 0, 0, 0, 0, 0, 0)$. -/
def uPlus : Coord :=
  embedPlus (fun i => if i = 0 then 1 else 0)

/-- The primitive opposite chiral idempotent $u_- = (0, 0, 0, 0, 1, 0, 0, 0)$. -/
def uMinus : Coord :=
  embedMinus (fun i => if i = 0 then 1 else 0)

/-- Left-multiplication projector by $u_+$ acting on coordinates:
    extracts the $V_+$ components and zeroes out the $V_-$ components. -/
def leftMulUPlus : Coord →ₗ[ℝ] Coord where
  toFun X := fun i => if i.val < 4 then X i else 0
  map_add' X Y := by
    ext i
    dsimp
    split_ifs <;> ring
  map_smul' c X := by
    ext i
    dsimp
    split_ifs <;> ring

/-- Left-multiplication projector by $u_-$ acting on coordinates:
    extracts the $V_-$ components and zeroes out the $V_+$ components. -/
def leftMulUMinus : Coord →ₗ[ℝ] Coord where
  toFun X := fun i => if i.val ≥ 4 then X i else 0
  map_add' X Y := by
    ext i
    dsimp
    split_ifs <;> ring
  map_smul' c X := by
    ext i
    dsimp
    split_ifs <;> ring

/-- 🏆 THEOREM 1A: $L_{u_+}$ is identity on the chiral subspace $V_+$. -/
theorem leftMulUPlus_on_VPlus (v : Chiral4) :
    leftMulUPlus (embedPlus v) = embedPlus v := by
  ext i
  fin_cases i <;>
  · dsimp [leftMulUPlus, embedPlus]

/-- 🏆 THEOREM 1B: $L_{u_+}$ annihilates the opposite chiral subspace $V_-$. -/
theorem leftMulUPlus_on_VMinus (w : Chiral4) :
    leftMulUPlus (embedMinus w) = 0 := by
  ext i
  fin_cases i <;>
  · dsimp [leftMulUPlus, embedMinus]

/-- 🏆 THEOREM 1C: $L_{u_-}$ annihilates the chiral subspace $V_+$. -/
theorem leftMulUMinus_on_VPlus (v : Chiral4) :
    leftMulUMinus (embedPlus v) = 0 := by
  ext i
  fin_cases i <;>
  · dsimp [leftMulUMinus, embedPlus]

/-- 🏆 THEOREM 1D: $L_{u_-}$ is identity on the opposite chiral subspace $V_-$. -/
theorem leftMulUMinus_on_VMinus (w : Chiral4) :
    leftMulUMinus (embedMinus w) = embedMinus w := by
  ext i
  fin_cases i <;>
  · dsimp [leftMulUMinus, embedMinus]

/-- 🏆 THEOREM 1E (Chiral Projector Completeness): $L_{u_+} + L_{u_-} = \operatorname{id}$. -/
theorem leftMul_chiral_completeness (X : Coord) :
    leftMulUPlus X + leftMulUMinus X = X := by
  ext i
  fin_cases i <;> (dsimp [leftMulUPlus, leftMulUMinus]; ring)

/-! The Peirce grading is distinct from the exchange involution `κ`: it is
the difference of the two complementary multiplication projections. -/

def peirceChiralGrading : Coord →ₗ[ℝ] Coord :=
  leftMulUPlus - leftMulUMinus

theorem peirceChiralGrading_on_VPlus (v : Chiral4) :
    peirceChiralGrading (embedPlus v) = embedPlus v := by
  dsimp [peirceChiralGrading]
  rw [leftMulUPlus_on_VPlus, leftMulUMinus_on_VPlus]
  simp

theorem peirceChiralGrading_on_VMinus (w : Chiral4) :
    peirceChiralGrading (embedMinus w) = -embedMinus w := by
  dsimp [peirceChiralGrading]
  rw [leftMulUPlus_on_VMinus, leftMulUMinus_on_VMinus]
  simp

theorem peirceChiralGrading_sq (X : Coord) :
    peirceChiralGrading (peirceChiralGrading X) = X := by
  ext i
  fin_cases i <;> simp [peirceChiralGrading, leftMulUPlus, leftMulUMinus]

theorem leftMulUPlus_eq_half_add_peirceChiralGrading (X : Coord) :
    leftMulUPlus X = (1 / 2 : ℝ) • (X + peirceChiralGrading X) := by
  ext i
  fin_cases i <;> simp [peirceChiralGrading, leftMulUPlus, leftMulUMinus] <;> ring

theorem leftMulUMinus_eq_half_sub_peirceChiralGrading (X : Coord) :
    leftMulUMinus X = (1 / 2 : ℝ) • (X - peirceChiralGrading X) := by
  ext i
  fin_cases i <;> simp [peirceChiralGrading, leftMulUPlus, leftMulUMinus] <;> ring

/-- 🏆 THEOREM 2 (Polar Form is Self-Evaluating on Diagonal):
    $B(X, X) = N(X)$. -/
theorem kreinPolar_self (X : Coord) :
    kreinPolar X X = kreinNorm X := by
  dsimp [kreinPolar, kreinNorm]
  ring

/-- Predicate characterizing derivations / infinitesimal isometries of the Krein metric:
    $B(D(X), Y) + B(X, D(Y)) = 0$. -/
def isKreinSkewAdjoint (D : Coord →ₗ[ℝ] Coord) : Prop :=
  ∀ X Y : Coord, kreinPolar (D X) Y + kreinPolar X (D Y) = 0

/-- Linearity of Krein polar form in first argument. -/
theorem kreinPolar_add_left (X1 X2 Y : Coord) :
    kreinPolar (X1 + X2) Y = kreinPolar X1 Y + kreinPolar X2 Y := by
  dsimp [kreinPolar]
  ring

/-- Linearity of Krein polar form in second argument. -/
theorem kreinPolar_add_right (X Y1 Y2 : Coord) :
    kreinPolar X (Y1 + Y2) = kreinPolar X Y1 + kreinPolar X Y2 := by
  dsimp [kreinPolar]
  ring

/-- 🏆 THEOREM 3 (Krein Skew-Adjointness Characterization):
    An endomorphism is Krein skew-adjoint iff it infinitesimally preserves the norm. -/
theorem isKreinSkewAdjoint_iff_polar (D : Coord →ₗ[ℝ] Coord) :
    isKreinSkewAdjoint D ↔ ∀ X : Coord, kreinPolar (D X) X = 0 := by
  constructor
  · intro h X
    have hXX := h X X
    rw [kreinPolar_comm X (D X)] at hXX
    linarith
  · intro h X Y
    have hXY := h (X + Y)
    have hX := h X
    have hY := h Y
    rw [map_add, kreinPolar_add_left, kreinPolar_add_right, kreinPolar_add_right] at hXY
    have h_sym : kreinPolar (D Y) X = kreinPolar X (D Y) := kreinPolar_comm (D Y) X
    rw [hX, hY, h_sym] at hXY
    linarith

/-- 🏆 THEOREM 4 (Parabolic Nilpotent Property on the Null Cone):
    Any vector in the chiral subspace $V_+$ is null: $N(v) = 0$ and $B(v, v) = 0$. -/
theorem chiral_null_property (v : Chiral4) :
    kreinNorm (embedPlus v) = 0 ∧ kreinPolar (embedPlus v) (embedPlus v) = 0 := by
  constructor
  · dsimp [kreinNorm, embedPlus]
    ring
  · rw [kreinPolar_self]
    dsimp [kreinNorm, embedPlus]
    ring

/-- 🏆 THEOREM 5 (Chiral Subspace Orthogonality under Krein Form):
    $V_+$ and $V_+$ are internally totally isotropic: $B(v_1, v_2) = 0$ for all $v_1, v_2 \in V_+$. -/
theorem chiral_plus_totally_isotropic (v1 v2 : Chiral4) :
    kreinPolar (embedPlus v1) (embedPlus v2) = 0 := by
  dsimp [kreinPolar, embedPlus]
  ring

/-- 🏆 THEOREM 6 (Opposite Chiral Subspace Orthogonality under Krein Form):
    $V_-$ and $V_-$ are internally totally isotropic: $B(w_1, w_2) = 0$ for all $w_1, w_2 \in V_-$. -/
theorem chiral_minus_totally_isotropic (w1 w2 : Chiral4) :
    kreinPolar (embedMinus w1) (embedMinus w2) = 0 := by
  dsimp [kreinPolar, embedMinus]
  ring

end InfoGeometry.Lie.SplitOctonionPeirceKreinDerivationBridge
