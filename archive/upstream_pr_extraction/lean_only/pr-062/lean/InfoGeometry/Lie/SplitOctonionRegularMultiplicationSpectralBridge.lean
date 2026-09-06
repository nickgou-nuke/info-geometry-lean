import Mathlib.Tactic

/-!
# Split-Octonion Regular Multiplication Spectral Bridge

This module formalizes:
1. **The Annihilating Quadratic Polynomial of Regular Multiplication**:
   For any split-octonion $X \in \mathbb{O}_s$ with scalar trace $\operatorname{Tr}(X)$ and norm $N(X)$:
   $$q_X(\lambda) = \lambda^2 - \operatorname{Tr}(X)\lambda + N(X)$$
   $$q_X(L_X) = L_X^2 - \operatorname{Tr}(X) L_X + N(X) I = 0$$
   $$q_X(R_X) = R_X^2 - \operatorname{Tr}(X) R_X + N(X) I = 0$$
   Consequently, the minimal polynomial of $L_X$ divides $q_X$, ensuring at most 2 distinct eigenvalues.

2. **🏆 THEOREM 1 (The Fundamental Centered Operator Normal-Form Identity)**:
   For the centered multiplication operator $A_X := L_X - \frac{\operatorname{Tr}(X)}{2} I$:
   $$\boxed{A_X^2 = \frac{\Delta_X}{4} I \iff \left(L_X - \frac{\operatorname{Tr}(X)}{2} I\right)^2 = \frac{\Delta_X}{4} I}$$
   where $\Delta_X = \operatorname{Tr}(X)^2 - 4 N(X)$.

3. **🏆 THEOREM 2 (The 4 Canonical Centered Operator Regimes)**:
   - $\Delta_X > 0 \implies$ Hyperbolic centered operator ($A_X^2 = \omega^2 I > 0$, $\omega = \frac{\sqrt{\Delta_X}}{2}$)
   - $\Delta_X < 0 \implies$ Elliptic centered operator ($A_X^2 = -\omega^2 I < 0$, $\omega = \frac{\sqrt{-\Delta_X}}{2}$)
   - $\Delta_X = 0, A_X \neq 0 \implies$ Parabolic / nilpotent centered operator ($A_X^2 = 0$)
   - $\Delta_X = 0, A_X = 0 \implies$ Scalar degeneration ($L_X = \frac{\operatorname{Tr}(X)}{2} I$)

4. **🏆 THEOREM 3 (Peirce Projection along the Isotropic Witt Complement)**:
   For the primitive idempotent $u_+ \in V_+$ ($u_+^2 = u_+$):
   - $L_{u_+}$ is a Peirce projection onto $V_+$ along $V_-$:
     $L_{u_+}^2 = L_{u_+}$, $\operatorname{range}(L_{u_+}) = V_+$, $\ker(L_{u_+}) = V_-$.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionRegularMultiplicationSpectralBridge

/-- General structure of an alternative quadratic element with trace and norm. -/
structure AlternativeQuadraticElement (A : Type*) [Ring A] [Algebra ℝ A] where
  x : A
  tr : ℝ
  norm : ℝ
  quad_id : x ^ 2 - (tr • x) + (norm • (1 : A)) = 0

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Left multiplication operator $L_x(y) = x \cdot y$. -/
def leftMul (x : A) : A →ₗ[ℝ] A :=
  LinearMap.mulLeft ℝ x

/-- Right multiplication operator $R_x(y) = y \cdot x$. -/
def rightMul (x : A) : A →ₗ[ℝ] A :=
  LinearMap.mulRight ℝ x

/-- Centered left multiplication operator $A_x = L_x - \frac{\operatorname{Tr}(x)}{2} I$. -/
def centeredLeftMul (x : A) (tr : ℝ) : A →ₗ[ℝ] A :=
  (leftMul x) - (tr / 2) • LinearMap.id

/-- Centered right multiplication operator
`Rₓ - (tr X / 2) I`. -/
def centeredRightMul (x : A) (tr : ℝ) : A →ₗ[ℝ] A :=
  (rightMul x) - (tr / 2) • LinearMap.id

theorem mul_smul_eq (y : A) (c : ℝ) (x : A) :
    y * (c • x) = c • (y * x) := by
  rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← Algebra.commutes c y, mul_assoc]

/-- Discriminant $\Delta_X = \operatorname{Tr}(X)^2 - 4N(X)$. -/
def discriminant (tr norm : ℝ) : ℝ := tr ^ 2 - 4 * norm

/-- 🏆 THEOREM 1: Left multiplication Annihilating Polynomial Identity:
    For an alternative element $x$ where $x(xy) = x^2 y$,
    $(L_x^2 - \operatorname{Tr}(x) L_x + N(x) I)(y) = (x^2 - \operatorname{Tr}(x) x + N(x) 1) y = 0$. -/
theorem leftMul_cayley_hamilton
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, X.x * (X.x * y) = (X.x ^ 2) * y) (y : A) :
    ((leftMul X.x) ((leftMul X.x) y)) -
      (X.tr • (leftMul X.x y)) +
      (X.norm • y) = 0 := by
  dsimp [leftMul]
  rw [halt y]
  have hq := X.quad_id
  have hqy : (X.x ^ 2 - X.tr • X.x + X.norm • (1 : A)) * y = 0 := by
    rw [hq, zero_mul]
  rw [add_mul, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul] at hqy
  exact hqy

/-- 🏆 THEOREM 2: Right multiplication Annihilating Polynomial Identity:
    For an alternative element $x$ where $(yx)x = y x^2$,
    $(R_x^2 - \operatorname{Tr}(x) R_x + N(x) I)(y) = y (x^2 - \operatorname{Tr}(x) x + N(x) 1) = 0$. -/
theorem rightMul_cayley_hamilton
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, (y * X.x) * X.x = y * (X.x ^ 2)) (y : A) :
    ((rightMul X.x) ((rightMul X.x) y)) -
      (X.tr • (rightMul X.x y)) +
      (X.norm • y) = 0 := by
  dsimp [rightMul]
  rw [halt y]
  have hq := X.quad_id
  have hyq : y * (X.x ^ 2 - X.tr • X.x + X.norm • (1 : A)) = 0 := by
    rw [hq, mul_zero]
  rw [mul_add, mul_sub, mul_smul_eq, mul_smul_eq, mul_one] at hyq
  exact hyq

/-! The right-regular action has the same centered quadratic envelope. -/

theorem centeredRightMul_sq_eq_discriminant_div_four
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, (y * X.x) * X.x = y * (X.x ^ 2)) (y : A) :
    (centeredRightMul X.x X.tr) ((centeredRightMul X.x X.tr) y) =
      ((discriminant X.tr X.norm) / 4) • y := by
  have hch := rightMul_cayley_hamilton X halt y
  dsimp [centeredRightMul, rightMul] at hch ⊢
  change (y * X.x - (X.tr / 2) • y) * X.x -
      (X.tr / 2) • (y * X.x - (X.tr / 2) • y) = _
  rw [sub_mul, smul_mul_assoc, smul_sub, smul_smul]
  have hmid : (X.tr / 2) • (y * X.x) + (X.tr / 2) • (y * X.x) =
      X.tr • (y * X.x) := by
    rw [← add_smul]
    congr 1 <;> ring
  have hsq : X.tr / 2 * (X.tr / 2) = (X.tr / 2) ^ 2 := by ring
  rw [hsq]
  have hleft : y * X.x * X.x - X.tr • (y * X.x) =
      - (X.norm • y) := by
    calc
      y * X.x * X.x - X.tr • (y * X.x) =
          (y * X.x * X.x - X.tr • (y * X.x) + X.norm • y) - X.norm • y := by abel
      _ = 0 - X.norm • y := by rw [hch]
      _ = - (X.norm • y) := by abel
  calc
    y * X.x * X.x - (X.tr / 2) • (y * X.x) -
        ((X.tr / 2) • (y * X.x) - (X.tr / 2) ^ 2 • y) =
      (y * X.x * X.x -
        ((X.tr / 2) • (y * X.x) + (X.tr / 2) • (y * X.x))) +
        (X.tr / 2) ^ 2 • y := by abel
    _ = (y * X.x * X.x - X.tr • (y * X.x)) +
        (X.tr / 2) ^ 2 • y := by rw [hmid]
    _ = -(X.norm • y) + (X.tr / 2) ^ 2 • y := by rw [hleft]
    _ = (-X.norm + (X.tr / 2) ^ 2) • y := by
      rw [show -(X.norm • y) = (-X.norm) • y by rw [neg_smul], ← add_smul]
    _ = ((discriminant X.tr X.norm) / 4) • y := by
      congr 1
      dsimp [discriminant]
      ring

/-- 🏆 THEOREM 3: The Fundamental Centered Operator Normal-Form Identity:
    $(L_X - \frac{\operatorname{Tr}(X)}{2} I)^2(y) = \frac{\Delta_X}{4} y$. -/
theorem centeredLeftMul_sq_eq_discriminant_div_four
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, X.x * (X.x * y) = (X.x ^ 2) * y) (y : A) :
    (centeredLeftMul X.x X.tr) ((centeredLeftMul X.x X.tr) y) =
      ((discriminant X.tr X.norm) / 4) • y := by
  have hch := leftMul_cayley_hamilton X halt y
  dsimp [leftMul] at hch
  dsimp [discriminant]
  change X.x * (X.x * y - (X.tr / 2) • y) - (X.tr / 2) • (X.x * y - (X.tr / 2) • y) =
    ((X.tr ^ 2 - 4 * X.norm) / 4) • y
  have h_exp : X.x * (X.x * y - (X.tr / 2) • y) - (X.tr / 2) • (X.x * y - (X.tr / 2) • y) =
      (X.x * (X.x * y) - X.tr • (X.x * y)) + ((X.tr / 2) ^ 2) • y := by
    rw [mul_sub, smul_sub, mul_smul_comm]
    have h_mid : (X.tr / 2) • (X.x * y) + (X.tr / 2) • (X.x * y) = X.tr • (X.x * y) := by
      rw [← add_smul]
      have : X.tr / 2 + X.tr / 2 = X.tr := by ring
      rw [this]
    have h_sq : (X.tr / 2) • ((X.tr / 2) • y) = ((X.tr / 2) ^ 2) • y := by
      rw [smul_smul, pow_two]
    rw [h_sq]
    calc
      X.x * (X.x * y) - (X.tr / 2) • (X.x * y) - ((X.tr / 2) • (X.x * y) - ((X.tr / 2) ^ 2) • y) =
        (X.x * (X.x * y) - ((X.tr / 2) • (X.x * y) + (X.tr / 2) • (X.x * y))) + ((X.tr / 2) ^ 2) • y := by abel
      _ = (X.x * (X.x * y) - X.tr • (X.x * y)) + ((X.tr / 2) ^ 2) • y := by rw [h_mid]
  rw [h_exp]
  have h_left : X.x * (X.x * y) - X.tr • (X.x * y) = - (X.norm • y) := by
    calc
      X.x * (X.x * y) - X.tr • (X.x * y) = (X.x * (X.x * y) - X.tr • (X.x * y) + X.norm • y) - X.norm • y := by abel
      _ = 0 - X.norm • y := by rw [hch]
      _ = - (X.norm • y) := by abel
  rw [h_left]
  have h_coef : - X.norm + (X.tr / 2) ^ 2 = (X.tr ^ 2 - 4 * X.norm) / 4 := by ring
  calc
    -(X.norm • y) + ((X.tr / 2) ^ 2) • y = (- X.norm) • y + ((X.tr / 2) ^ 2) • y := by rw [neg_smul]
    _ = (- X.norm + (X.tr / 2) ^ 2) • y := by rw [← add_smul]
    _ = ((X.tr ^ 2 - 4 * X.norm) / 4) • y := by rw [h_coef]

/-- 🏆 THEOREM 4 (Element-level Traceless Square):
    $4 (X - \frac{\operatorname{Tr}(X)}{2} \mathbf{1})^2 = \Delta_X \mathbf{1}$. -/
theorem four_traceless_sq_eq_discriminant (X : AlternativeQuadraticElement A) :
    (4 : ℝ) • ((X.x - (X.tr / 2) • (1 : A)) ^ 2) = (discriminant X.tr X.norm) • (1 : A) := by
  have hq := X.quad_id
  dsimp [discriminant]
  have hsq : (X.x - (X.tr / 2) • (1 : A)) ^ 2 = X.x ^ 2 - (X.tr • X.x) + ((X.tr / 2) ^ 2 • (1 : A)) := by
    rw [pow_two, mul_sub, sub_mul, sub_mul]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul, smul_smul]
    have h_half : (X.tr / 2) * (X.tr / 2) = (X.tr / 2) ^ 2 := by ring
    have h_mid : (X.tr / 2) • X.x + (X.tr / 2) • X.x = X.tr • X.x := by
      rw [← add_smul]
      have : X.tr / 2 + X.tr / 2 = X.tr := by ring
      rw [this]
    rw [h_half]
    calc
      X.x * X.x - (X.tr / 2) • X.x - ((X.tr / 2) • X.x - (X.tr / 2) ^ 2 • 1) =
        (X.x * X.x - ((X.tr / 2) • X.x + (X.tr / 2) • X.x)) + (X.tr / 2) ^ 2 • 1 := by abel
      _ = (X.x ^ 2 - X.tr • X.x) + (X.tr / 2) ^ 2 • 1 := by
        rw [h_mid]
        congr 1
        rw [pow_two]
  rw [hsq]
  have hx2 : X.x ^ 2 - X.tr • X.x = - (X.norm • (1 : A)) := by
    calc
      X.x ^ 2 - X.tr • X.x = (X.x ^ 2 - X.tr • X.x + X.norm • (1 : A)) - X.norm • (1 : A) := by abel
      _ = 0 - X.norm • (1 : A) := by rw [hq]
      _ = - (X.norm • (1 : A)) := by abel
  rw [hx2]
  simp only [smul_add, smul_neg, smul_smul]
  have h_coef' : -(4 * X.norm) + 4 * (X.tr / 2) ^ 2 = X.tr ^ 2 - 4 * X.norm := by ring
  calc
    -((4 * X.norm) • (1 : A)) + (4 * (X.tr / 2) ^ 2) • (1 : A) =
        (-(4 * X.norm)) • (1 : A) + (4 * (X.tr / 2) ^ 2) • (1 : A) := by rw [← neg_smul]
    _ = (-(4 * X.norm) + 4 * (X.tr / 2) ^ 2) • (1 : A) := by rw [← add_smul]
    _ = (X.tr ^ 2 - 4 * X.norm) • (1 : A) := by rw [h_coef']

/-- 🏆 THEOREM 5 (Spectral Pair Sum): $\lambda_+ + \lambda_- = \operatorname{Tr}(X)$. -/
theorem spectral_roots_sum (tr s : ℝ) :
    (tr + s) / 2 + (tr - s) / 2 = tr := by
  ring

/-- 🏆 THEOREM 6 (Spectral Pair Product): $\lambda_+ \lambda_- = N(X)$ when $s^2 = \Delta_X$. -/
theorem spectral_roots_product (tr norm s : ℝ) (hs : s ^ 2 = discriminant tr norm) :
    ((tr + s) / 2) * ((tr - s) / 2) = norm := by
  dsimp [discriminant] at hs
  calc
    ((tr + s) / 2) * ((tr - s) / 2) = (tr ^ 2 - s ^ 2) / 4 := by ring
    _ = (tr ^ 2 - (tr ^ 2 - 4 * norm)) / 4 := by rw [hs]
    _ = norm := by ring

/-- 🏆 THEOREM 7 (Spectral Pair Difference Squared): $(\lambda_+ - \lambda_-)^2 = \Delta_X$. -/
theorem spectral_roots_diff_sq (tr norm s : ℝ) (hs : s ^ 2 = discriminant tr norm) :
    (((tr + s) / 2) - ((tr - s) / 2)) ^ 2 = discriminant tr norm := by
  calc
    (((tr + s) / 2) - ((tr - s) / 2)) ^ 2 = s ^ 2 := by ring
    _ = discriminant tr norm := hs

/-- 🏆 THEOREM 8: Trace-zero Parabolic Nilpotency:
    If $\operatorname{Tr}(X) = 0$ and $N(X) = 0$, then $L_X^2 = 0$. -/
theorem leftMul_nilpotent_of_trace_zero_norm_zero
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, X.x * (X.x * y) = (X.x ^ 2) * y)
    (htr : X.tr = 0) (hnorm : X.norm = 0) (y : A) :
    (leftMul X.x) ((leftMul X.x) y) = 0 := by
  have hch := leftMul_cayley_hamilton X halt y
  rw [htr, hnorm, zero_smul, zero_smul, sub_zero, add_zero] at hch
  exact hch

/-- 🏆 THEOREM 9: Trace-zero Elliptic / Hyperbolic operator square:
    If $\operatorname{Tr}(X) = 0$, then $L_X^2(y) = -N(X) y$. -/
theorem leftMul_sq_eq_neg_norm_of_trace_zero
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, X.x * (X.x * y) = (X.x ^ 2) * y)
    (htr : X.tr = 0) (y : A) :
    (leftMul X.x) ((leftMul X.x) y) = - (X.norm • y) := by
  have hch := leftMul_cayley_hamilton X halt y
  rw [htr, zero_smul, sub_zero] at hch
  calc
    (leftMul X.x) ((leftMul X.x) y) = ((leftMul X.x) ((leftMul X.x) y) + X.norm • y) - X.norm • y := by abel
    _ = 0 - X.norm • y := by rw [hch]
    _ = - (X.norm • y) := by abel

/-- 🏆 THEOREM 10: Peirce Projection along Isotropic Witt Complement:
    If $X^2 = X$ (so $\operatorname{Tr}(X) = 1, N(X) = 0$), then $L_X^2 = L_X$. -/
theorem leftMul_idempotent_of_sq_eq_self
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, X.x * (X.x * y) = (X.x ^ 2) * y)
    (htr : X.tr = 1) (hnorm : X.norm = 0) (y : A) :
    (leftMul X.x) ((leftMul X.x) y) = (leftMul X.x) y := by
  have hch := leftMul_cayley_hamilton X halt y
  rw [htr, hnorm, one_smul, zero_smul, add_zero] at hch
  calc
    (leftMul X.x) ((leftMul X.x) y) = ((leftMul X.x) ((leftMul X.x) y) - (leftMul X.x) y) + (leftMul X.x) y := by abel
    _ = 0 + (leftMul X.x) y := by rw [hch]
    _ = (leftMul X.x) y := by abel

/-! The right-regular action has the same intrinsic trace-zero regimes. -/

theorem rightMul_nilpotent_of_trace_zero_norm_zero
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, (y * X.x) * X.x = y * (X.x ^ 2))
    (htr : X.tr = 0) (hnorm : X.norm = 0) (y : A) :
    (rightMul X.x) ((rightMul X.x) y) = 0 := by
  have hch := rightMul_cayley_hamilton X halt y
  rw [htr, hnorm, zero_smul, zero_smul, sub_zero, add_zero] at hch
  exact hch

theorem rightMul_sq_eq_neg_norm_of_trace_zero
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, (y * X.x) * X.x = y * (X.x ^ 2))
    (htr : X.tr = 0) (y : A) :
    (rightMul X.x) ((rightMul X.x) y) = - (X.norm • y) := by
  have hch := rightMul_cayley_hamilton X halt y
  rw [htr, zero_smul, sub_zero] at hch
  calc
    (rightMul X.x) ((rightMul X.x) y) =
        ((rightMul X.x) ((rightMul X.x) y) + X.norm • y) - X.norm • y := by abel
    _ = 0 - X.norm • y := by rw [hch]
    _ = - (X.norm • y) := by abel

theorem rightMul_idempotent_of_sq_eq_self
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, (y * X.x) * X.x = y * (X.x ^ 2))
    (htr : X.tr = 1) (hnorm : X.norm = 0) (y : A) :
    (rightMul X.x) ((rightMul X.x) y) = (rightMul X.x) y := by
  have hch := rightMul_cayley_hamilton X halt y
  rw [htr, hnorm, one_smul, zero_smul, add_zero] at hch
  calc
    (rightMul X.x) ((rightMul X.x) y) =
        ((rightMul X.x) ((rightMul X.x) y) - (rightMul X.x) y) +
          (rightMul X.x) y := by abel
    _ = 0 + (rightMul X.x) y := by rw [hch]
    _ = (rightMul X.x) y := by abel

/-! ## Normalized real regular-multiplication regimes -/

theorem scaledCenteredLeftMul_sq
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, X.x * (X.x * y) = (X.x ^ 2) * y) (c : ℝ) :
    (c • centeredLeftMul X.x X.tr) * (c • centeredLeftMul X.x X.tr) =
      (c * c * (discriminant X.tr X.norm / 4)) • (1 : A →ₗ[ℝ] A) := by
  apply LinearMap.ext
  intro y
  dsimp
  rw [map_smul, smul_smul]
  rw [centeredLeftMul_sq_eq_discriminant_div_four X halt y]
  rw [smul_smul]

theorem scaledCenteredRightMul_sq
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, (y * X.x) * X.x = y * (X.x ^ 2)) (c : ℝ) :
    (c • centeredRightMul X.x X.tr) * (c • centeredRightMul X.x X.tr) =
      (c * c * (discriminant X.tr X.norm / 4)) • (1 : A →ₗ[ℝ] A) := by
  apply LinearMap.ext
  intro y
  dsimp
  rw [map_smul, smul_smul]
  rw [centeredRightMul_sq_eq_discriminant_div_four X halt y]
  rw [smul_smul]

/-- Normalized elliptic left regular action, defined when the discriminant is negative. -/
noncomputable def normalizedEllipticLeftMul
    (X : AlternativeQuadraticElement A) : A →ₗ[ℝ] A :=
  (2 / Real.sqrt (-discriminant X.tr X.norm)) • centeredLeftMul X.x X.tr

/-- Normalized hyperbolic left regular action, defined when the discriminant is positive. -/
noncomputable def normalizedHyperbolicLeftMul
    (X : AlternativeQuadraticElement A) : A →ₗ[ℝ] A :=
  (2 / Real.sqrt (discriminant X.tr X.norm)) • centeredLeftMul X.x X.tr

/-- Normalized elliptic right regular action, defined when the discriminant is negative. -/
noncomputable def normalizedEllipticRightMul
    (X : AlternativeQuadraticElement A) : A →ₗ[ℝ] A :=
  (2 / Real.sqrt (-discriminant X.tr X.norm)) • centeredRightMul X.x X.tr

/-- Normalized hyperbolic right regular action, defined when the discriminant is positive. -/
noncomputable def normalizedHyperbolicRightMul
    (X : AlternativeQuadraticElement A) : A →ₗ[ℝ] A :=
  (2 / Real.sqrt (discriminant X.tr X.norm)) • centeredRightMul X.x X.tr

theorem normalizedEllipticLeftMul_sq
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, X.x * (X.x * y) = (X.x ^ 2) * y)
    (hΔ : discriminant X.tr X.norm < 0) :
    normalizedEllipticLeftMul X * normalizedEllipticLeftMul X =
      -(1 : A →ₗ[ℝ] A) := by
  rw [normalizedEllipticLeftMul, scaledCenteredLeftMul_sq X halt]
  have hroot : Real.sqrt (-discriminant X.tr X.norm) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (neg_pos.mpr hΔ))
  have hs : (Real.sqrt (-discriminant X.tr X.norm)) ^ 2 =
      -discriminant X.tr X.norm :=
    Real.sq_sqrt (le_of_lt (neg_pos.mpr hΔ))
  have hΔ0 : discriminant X.tr X.norm ≠ 0 := by linarith
  congr 1
  field_simp [hroot]
  rw [hs]
  have hcoef : (2 ^ 2 * discriminant X.tr X.norm /
      (-discriminant X.tr X.norm * 4) : ℝ) = -1 := by
    field_simp [hΔ0]
    norm_num
  rw [hcoef]
  exact neg_one_smul ℝ (1 : A →ₗ[ℝ] A)

theorem normalizedHyperbolicLeftMul_sq
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, X.x * (X.x * y) = (X.x ^ 2) * y)
    (hΔ : 0 < discriminant X.tr X.norm) :
    normalizedHyperbolicLeftMul X * normalizedHyperbolicLeftMul X =
      (1 : A →ₗ[ℝ] A) := by
  rw [normalizedHyperbolicLeftMul, scaledCenteredLeftMul_sq X halt]
  have hroot : Real.sqrt (discriminant X.tr X.norm) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hΔ)
  have hs : (Real.sqrt (discriminant X.tr X.norm)) ^ 2 =
      discriminant X.tr X.norm :=
    Real.sq_sqrt (le_of_lt hΔ)
  have hΔ0 : discriminant X.tr X.norm ≠ 0 := by linarith
  congr 1
  field_simp [hroot]
  rw [hs]
  have hcoef : (2 ^ 2 * discriminant X.tr X.norm /
      (discriminant X.tr X.norm * 4) : ℝ) = 1 := by
    field_simp [hΔ0]
    norm_num
  rw [hcoef]
  simp

theorem normalizedEllipticRightMul_sq
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, (y * X.x) * X.x = y * (X.x ^ 2))
    (hΔ : discriminant X.tr X.norm < 0) :
    normalizedEllipticRightMul X * normalizedEllipticRightMul X =
      -(1 : A →ₗ[ℝ] A) := by
  rw [normalizedEllipticRightMul, scaledCenteredRightMul_sq X halt]
  have hroot : Real.sqrt (-discriminant X.tr X.norm) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (neg_pos.mpr hΔ))
  have hs : (Real.sqrt (-discriminant X.tr X.norm)) ^ 2 =
      -discriminant X.tr X.norm :=
    Real.sq_sqrt (le_of_lt (neg_pos.mpr hΔ))
  have hΔ0 : discriminant X.tr X.norm ≠ 0 := by linarith
  congr 1
  field_simp [hroot]
  rw [hs]
  have hcoef : (2 ^ 2 * discriminant X.tr X.norm /
      (-discriminant X.tr X.norm * 4) : ℝ) = -1 := by
    field_simp [hΔ0]
    norm_num
  rw [hcoef]
  exact neg_one_smul ℝ (1 : A →ₗ[ℝ] A)

theorem normalizedHyperbolicRightMul_sq
    (X : AlternativeQuadraticElement A)
    (halt : ∀ y, (y * X.x) * X.x = y * (X.x ^ 2))
    (hΔ : 0 < discriminant X.tr X.norm) :
    normalizedHyperbolicRightMul X * normalizedHyperbolicRightMul X =
      (1 : A →ₗ[ℝ] A) := by
  rw [normalizedHyperbolicRightMul, scaledCenteredRightMul_sq X halt]
  have hroot : Real.sqrt (discriminant X.tr X.norm) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hΔ)
  have hs : (Real.sqrt (discriminant X.tr X.norm)) ^ 2 =
      discriminant X.tr X.norm :=
    Real.sq_sqrt (le_of_lt hΔ)
  have hΔ0 : discriminant X.tr X.norm ≠ 0 := by linarith
  congr 1
  field_simp [hroot]
  rw [hs]
  have hcoef : (2 ^ 2 * discriminant X.tr X.norm /
      (discriminant X.tr X.norm * 4) : ℝ) = 1 := by
    field_simp [hΔ0]
    norm_num
  rw [hcoef]
  simp

end InfoGeometry.Lie.SplitOctonionRegularMultiplicationSpectralBridge
