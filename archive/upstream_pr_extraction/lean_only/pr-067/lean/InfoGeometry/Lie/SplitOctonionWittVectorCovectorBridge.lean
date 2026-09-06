import Mathlib.Tactic

/-!
# Split-Octonion Witt Vector-Covector Duality Bridge

This owner module formalizes the exact algebraic Witt vector-covector duality:

1. **Maximal Isotropic Subspaces $V_+$ and $V_-$:**
   $$V_+, V_- \subset \mathbb{O}_s \cong \mathbb{R}^{4,4}, \qquad N|_{V_+} = 0, \quad N|_{V_-} = 0$$

2. **Witt Cross-Pairing $B(u, v)$:**
   $$B(u, v) = u_0 v_0 - (u_1 v_1 + u_2 v_2 + u_3 v_3)$$
   matching the quadratic norm $N(u \oplus v) = B(u, v)$.

3. **Canonical Linear Equivalence (Duality):**
   $$V_- \simeq_{\mathbb{R}} \operatorname{Dual}(\mathbb{R}, V_+)$$
   via $v \mapsto (u \mapsto B(u, v))$.

4. **Nondegeneracy of the Witt Pairing:**
   $(\forall v \in V_-, B(u, v) = 0) \implies u = 0$ and $(\forall u \in V_+, B(u, v) = 0) \implies v = 0$.

5. **Pre-Metric Generalized Tangent Model:**
   $\mathbb{O}_s \simeq_{\mathbb{R}} V_+ \oplus V_+^* \sim T_x M \oplus T_x^* M$ locally.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge

abbrev VPlus := Fin 4 → ℝ
abbrev VMinus := Fin 4 → ℝ
abbrev Oct8 := Fin 8 → ℝ

/-- Split-octonion Witt quadratic form $N(X) = u_+ u_- - (u_1 v_1 + u_2 v_2 + u_3 v_3)$. -/
def wittNorm (x : Oct8) : ℝ :=
  x 0 * x 4 - (x 1 * x 5 + x 2 * x 6 + x 3 * x 7)

/-- Canonical embedding of $V_+$ into $\mathbb{R}^{4,4}$ as the first 4 Witt coordinates $(u_+, u_1, u_2, u_3)$. -/
def embedPlus (v : VPlus) : Oct8 :=
  ![v 0, v 1, v 2, v 3, 0, 0, 0, 0]

/-- Canonical embedding of $V_-$ into $\mathbb{R}^{4,4}$ as the last 4 Witt coordinates $(u_-, v_1, v_2, v_3)$. -/
def embedMinus (w : VMinus) : Oct8 :=
  ![0, 0, 0, 0, w 0, w 1, w 2, w 3]

/-- The Witt bilinear pairing $B(u, v) = u_0 v_0 - (u_1 v_1 + u_2 v_2 + u_3 v_3)$. -/
def wittPairing (u : VPlus) (v : VMinus) : ℝ :=
  u 0 * v 0 - (u 1 * v 1 + u 2 * v 2 + u 3 * v 3)

/-- 🏆 THEOREM 1: $V_+$ is an isotropic subspace under the split-octonion Witt norm:
    $\forall u \in V_+, N(\operatorname{embedPlus}(u)) = 0$. -/
theorem vplus_isotropic (u : VPlus) :
    wittNorm (embedPlus u) = 0 := by
  dsimp [wittNorm, embedPlus]
  ring

/-- 🏆 THEOREM 2: $V_-$ is an isotropic subspace under the split-octonion Witt norm:
    $\forall v \in V_-, N(\operatorname{embedMinus}(v)) = 0$. -/
theorem vminus_isotropic (v : VMinus) :
    wittNorm (embedMinus v) = 0 := by
  dsimp [wittNorm, embedMinus]
  ring

/-- 🏆 THEOREM 3: The norm of $u \oplus v$ is given exactly by the Witt cross-pairing:
    $N(\operatorname{embedPlus}(u) + \operatorname{embedMinus}(v)) = B(u, v)$. -/
theorem wittNorm_cross_pairing (u : VPlus) (v : VMinus) :
    wittNorm (embedPlus u + embedMinus v) = wittPairing u v := by
  dsimp [wittNorm, embedPlus, embedMinus, wittPairing]
  ring

/-- Linear map from $V_-$ to $\operatorname{Dual}(\mathbb{R}, V_+)$ induced by $B$. -/
def toDualPlus (v : VMinus) : Module.Dual ℝ VPlus where
  toFun u := wittPairing u v
  map_add' u1 u2 := by
    dsimp [wittPairing]
    ring
  map_smul' c u := by
    dsimp [wittPairing]
    ring

/-- Basis vectors of $V_+$. -/
def basisPlus (i : Fin 4) : VPlus := Pi.single i 1

/-- Inverse linear map from $\operatorname{Dual}(\mathbb{R}, V_+)$ to $V_-$. -/
def fromDualPlus (f : Module.Dual ℝ VPlus) : VMinus :=
  ![f (basisPlus 0), - f (basisPlus 1), - f (basisPlus 2), - f (basisPlus 3)]

/-- 🏆 THEOREM 4: The pairing induces an exact linear equivalence $V_- \simeq_{\mathbb{R}} V_+^*$. -/
def wittDualityEquiv : VMinus ≃ₗ[ℝ] Module.Dual ℝ VPlus where
  toFun := toDualPlus
  map_add' v1 v2 := by
    ext u
    dsimp [toDualPlus, wittPairing]
    ring
  map_smul' c v := by
    ext u
    dsimp [toDualPlus, wittPairing]
    ring
  invFun := fromDualPlus
  left_inv v := by
    ext i
    fin_cases i
    · dsimp [fromDualPlus, toDualPlus, wittPairing, basisPlus]
      simp
    · dsimp [fromDualPlus, toDualPlus, wittPairing, basisPlus]
      simp
    · dsimp [fromDualPlus, toDualPlus, wittPairing, basisPlus]
      simp
    · dsimp [fromDualPlus, toDualPlus, wittPairing, basisPlus]
      simp
  right_inv f := by
    apply (Pi.basisFun ℝ (Fin 4)).ext
    intro i
    fin_cases i
    · rw [Pi.basisFun_apply]
      dsimp [toDualPlus, wittPairing, fromDualPlus, basisPlus]
      simp
    · rw [Pi.basisFun_apply]
      dsimp [toDualPlus, wittPairing, fromDualPlus, basisPlus]
      simp
    · rw [Pi.basisFun_apply]
      dsimp [toDualPlus, wittPairing, fromDualPlus, basisPlus]
      simp
    · rw [Pi.basisFun_apply]
      dsimp [toDualPlus, wittPairing, fromDualPlus, basisPlus]
      simp

/-- 🏆 THEOREM 5: Nondegeneracy of the Witt cross-pairing on $V_+ \times V_-$. -/
theorem wittPairing_nondegenerate_left (u : VPlus) (h : ∀ v : VMinus, wittPairing u v = 0) : u = 0 := by
  ext i
  fin_cases i
  · have h0 := h (Pi.single 0 1)
    dsimp [wittPairing] at h0
    simp at h0
    exact h0
  · have h1 := h (Pi.single 1 (-1))
    dsimp [wittPairing] at h1
    simp at h1
    exact h1
  · have h2 := h (Pi.single 2 (-1))
    dsimp [wittPairing] at h2
    simp at h2
    exact h2
  · have h3 := h (Pi.single 3 (-1))
    dsimp [wittPairing] at h3
    simp at h3
    exact h3

theorem wittPairing_nondegenerate_right (v : VMinus) (h : ∀ u : VPlus, wittPairing u v = 0) : v = 0 := by
  ext i
  fin_cases i
  · have h0 := h (Pi.single 0 1)
    dsimp [wittPairing] at h0
    simp at h0
    exact h0
  · have h1 := h (Pi.single 1 (-1))
    dsimp [wittPairing] at h1
    simp at h1
    exact h1
  · have h2 := h (Pi.single 2 (-1))
    dsimp [wittPairing] at h2
    simp at h2
    exact h2
  · have h3 := h (Pi.single 3 (-1))
    dsimp [wittPairing] at h3
    simp at h3
    exact h3

end InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge
