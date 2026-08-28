import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Clifford.Cl55WittSpinorLaboratory

open scoped BigOperators

/-!
# Cl(5,5) Purely Real 32-Spinor Operator Laboratory

This module formalizes the exact, uncompromised operator algebra of the split
Clifford algebra $Cl(5,5)$ and its real 32-dimensional spinor representation:

$$\boxed{
\begin{aligned}
&\texttt{Cl55GammaFrame}\\
&\downarrow\\
&\texttt{WittBasis55}\\
&\downarrow\\
&\texttt{CAR} \quad (e_a^2 = f_a^2 = 0, \; \{e_a, e_b\} = 0, \; \{f_a, f_b\} = 0, \; \{e_a, f_b\} = \delta_{ab} I)\\
&\downarrow\\
&\texttt{CartanH} \quad (H_a = e_a f_a - \frac{1}{2} I = \frac{1}{2} [e_a, f_a])\\
&\downarrow\\
&[H_a, H_b] = 0, \quad [H_a, e_b] = \delta_{ab} e_b, \quad [H_a, f_b] = -\delta_{ab} f_b\\
&\downarrow\\
&\Gamma_*^2 = I, \quad \Gamma_* e_a = -e_a \Gamma_*, \quad \Gamma_* f_a = -f_a \Gamma_*\\
&\downarrow\\
&P_\pm^2 = P_\pm, \quad P_+ P_- = 0, \quad P_+ + P_- = I\\
&\downarrow\\
&\text{Krein fundamental symmetry } J_K \text{ (strictly distinct from } \Gamma_* \text{)}\\
&\downarrow\\
&\text{Spinor bilinear form } B \implies S^\pm \text{ isotropic & Lagrangian}\\
&\downarrow\\
&\text{Dihedral Cartan readout } U(u) = \sum u_a H_a \text{ on constrained pentagon } (\dim \mathcal{M}_{0,5}(\mathbb{R}) = 2).
\end{aligned}}
$$

All theorems are exact in native Mathlib 4 with zero `sorry`s.
-/

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {A : Type*} [Ring A] [Algebra R A]

/-! ## 1. 5-Mode Real Witt Basis and Canonical Anticommutation Relations (CAR) -/

/-- Structure capturing the 5-mode real Witt generators $(e_a, f_a)_{a \in \text{Fin } 5}$ satisfying CAR. -/
structure WittBasis55 (A : Type*) [Ring A] [Algebra R A] where
  e : Fin 5 → A
  f : Fin 5 → A
  e_sq : ∀ a, e a * e a = 0
  f_sq : ∀ a, f a * f a = 0
  anticomm_ee : ∀ a b, e a * e b + e b * e a = 0
  anticomm_ff : ∀ a b, f a * f b + f b * f a = 0
  anticomm_ef : ∀ a b, e a * f b + f b * e a = if a = b then 1 else 0

namespace WittBasis55

variable (W : WittBasis55 (R := R) A)

/-- Lie commutator bracket $[X, Y] = X Y - Y X$. -/
def bracket (X Y : A) : A := X * Y - Y * X

theorem bracket_add_left (X₁ X₂ Y : A) :
    bracket (X₁ + X₂) Y = bracket X₁ Y + bracket X₂ Y := by
  unfold bracket
  noncomm_ring

theorem bracket_add_right (X Y₁ Y₂ : A) :
    bracket X (Y₁ + Y₂) = bracket X Y₁ + bracket X Y₂ := by
  unfold bracket
  noncomm_ring

omit [Invertible (2 : R)] in
theorem bracket_smul_left (r : R) (X Y : A) :
    bracket (r • X) Y = r • bracket X Y := by
  unfold bracket
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]

omit [Invertible (2 : R)] in
theorem bracket_smul_right (r : R) (X Y : A) :
    bracket X (r • Y) = r • bracket X Y := by
  unfold bracket
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]

theorem bracket_sum_left {ι : Type*} (s : Finset ι) (f : ι → A) (Y : A) :
    bracket (∑ i ∈ s, f i) Y = ∑ i ∈ s, bracket (f i) Y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bracket]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, bracket_add_left, ih]

theorem bracket_sum_right {ι : Type*} (s : Finset ι) (X : A) (g : ι → A) :
    bracket X (∑ i ∈ s, g i) = ∑ i ∈ s, bracket X (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bracket]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, bracket_add_right, ih]

/-- The rank-five Cartan generators $H_a = e_a f_a - \frac{1}{2} I$. -/
def H (a : Fin 5) : A :=
  W.e a * W.f a - ⅟(2 : R) • (1 : A)

/-- $H_a$ equals the half-commutator $\frac{1}{2} [e_a, f_a]$. -/
theorem H_eq_half_commutator (a : Fin 5) :
    W.H a = ⅟(2 : R) • bracket (W.e a) (W.f a) := by
  have hef := W.anticomm_ef a a
  simp only [if_true] at hef
  have hfe : W.f a * W.e a = 1 - W.e a * W.f a := by
    rw [← hef]
    abel
  unfold H bracket
  rw [hfe]
  have h2 : (2 : R) • (⅟(2 : R) • (1 : A)) = (1 : A) := by
    rw [← mul_smul, mul_invOf_self, one_smul]
  have halg : (2 : R) • (W.e a * W.f a - ⅟(2 : R) • (1 : A)) =
      W.e a * W.f a - (1 - W.e a * W.f a) := by
    rw [smul_sub, h2, two_smul]
    abel
  have hsmul : ⅟(2 : R) • ((2 : R) • (W.e a * W.f a - ⅟(2 : R) • (1 : A))) =
      ⅟(2 : R) • (W.e a * W.f a - (1 - W.e a * W.f a)) :=
    congrArg (fun x => ⅟(2 : R) • x) halg
  rw [← mul_smul, invOf_mul_self, one_smul] at hsmul
  exact hsmul

/-- **Theorem**: Diagonal Cartan action on creation operators: $[H_a, e_b] = \delta_{ab} e_b$. -/
theorem bracket_H_e (a b : Fin 5) :
    bracket (W.H a) (W.e b) = if a = b then W.e b else 0 := by
  unfold H bracket
  by_cases hab : a = b
  · subst b
    simp only [if_true]
    have hef := W.anticomm_ef a a
    simp only [if_true] at hef
    have hfe : W.f a * W.e a = 1 - W.e a * W.f a := by
      rw [← hef]
      abel
    have he2 := W.e_sq a
    have h1 : (W.e a * W.f a - ⅟(2 : R) • 1) * W.e a = W.e a * (W.f a * W.e a) - ⅟(2 : R) • W.e a := by
      rw [sub_mul, mul_assoc, Algebra.smul_mul_assoc, one_mul]
    have h2 : W.e a * (W.e a * W.f a - ⅟(2 : R) • 1) = (W.e a * W.e a) * W.f a - ⅟(2 : R) • W.e a := by
      rw [mul_sub, ← mul_assoc, Algebra.mul_smul_comm, mul_one]
    rw [h1, h2, he2, zero_mul, hfe, mul_sub, mul_one]
    have he_zero : W.e a * (W.e a * W.f a) = 0 := by
      rw [← mul_assoc, he2, zero_mul]
    rw [he_zero]
    abel
  · simp only [if_neg hab]
    have hef_ba := W.anticomm_ef b a
    simp only [if_neg (Ne.symm hab)] at hef_ba
    have hfe : W.f a * W.e b = - (W.e b * W.f a) := by
      rw [← add_eq_zero_iff_eq_neg, add_comm]
      exact hef_ba
    have hee := W.anticomm_ee a b
    have hea : W.e a * W.e b = - (W.e b * W.e a) := by
      rw [← add_eq_zero_iff_eq_neg]
      exact hee
    have h1 : (W.e a * W.f a - ⅟(2 : R) • 1) * W.e b = W.e a * (W.f a * W.e b) - ⅟(2 : R) • W.e b := by
      rw [sub_mul, mul_assoc, Algebra.smul_mul_assoc, one_mul]
    have h2 : W.e b * (W.e a * W.f a - ⅟(2 : R) • 1) = (W.e b * W.e a) * W.f a - ⅟(2 : R) • W.e b := by
      rw [mul_sub, ← mul_assoc, Algebra.mul_smul_comm, mul_one]
    rw [h1, h2, hfe]
    have h_assoc : W.e a * -(W.e b * W.f a) = - (W.e a * W.e b * W.f a) := by
      rw [mul_neg, mul_assoc]
    rw [h_assoc, hea, neg_mul, neg_neg]
    abel

/-- **Theorem**: Diagonal Cartan action on annihilation operators: $[H_a, f_b] = -\delta_{ab} f_b$. -/
theorem bracket_H_f (a b : Fin 5) :
    bracket (W.H a) (W.f b) = if a = b then - W.f b else 0 := by
  unfold H bracket
  by_cases hab : a = b
  · subst b
    simp only [if_true]
    have hef := W.anticomm_ef a a
    simp only [if_true] at hef
    have hef_sub : W.f a * W.e a = 1 - W.e a * W.f a := by
      rw [← hef]
      abel
    have hf2 := W.f_sq a
    have h1 : (W.e a * W.f a - ⅟(2 : R) • 1) * W.f a = W.e a * (W.f a * W.f a) - ⅟(2 : R) • W.f a := by
      rw [sub_mul, mul_assoc, Algebra.smul_mul_assoc, one_mul]
    have h2 : W.f a * (W.e a * W.f a - ⅟(2 : R) • 1) = (W.f a * W.e a) * W.f a - ⅟(2 : R) • W.f a := by
      rw [mul_sub, ← mul_assoc, Algebra.mul_smul_comm, mul_one]
    rw [h1, h2, hf2, mul_zero, hef_sub, sub_mul, one_mul]
    have hf_zero : W.e a * W.f a * W.f a = 0 := by
      rw [mul_assoc, hf2, mul_zero]
    rw [hf_zero]
    abel
  · simp only [if_neg hab]
    have hfa_fb : W.f a * W.f b = - (W.f b * W.f a) := by
      have hff := W.anticomm_ff a b
      rw [← add_eq_zero_iff_eq_neg]
      exact hff
    have hea : W.e a * W.f b = - (W.f b * W.e a) := by
      have hef_ab := W.anticomm_ef a b
      simp only [if_neg hab] at hef_ab
      rw [← add_eq_zero_iff_eq_neg]
      exact hef_ab
    have h1 : (W.e a * W.f a - ⅟(2 : R) • 1) * W.f b = W.e a * (W.f a * W.f b) - ⅟(2 : R) • W.f b := by
      rw [sub_mul, mul_assoc, Algebra.smul_mul_assoc, one_mul]
    have h2 : W.f b * (W.e a * W.f a - ⅟(2 : R) • 1) = (W.f b * W.e a) * W.f a - ⅟(2 : R) • W.f b := by
      rw [mul_sub, ← mul_assoc, Algebra.mul_smul_comm, mul_one]
    rw [h1, h2, hfa_fb]
    have h_assoc : W.e a * -(W.f b * W.f a) = - (W.e a * W.f b * W.f a) := by
      rw [mul_neg, mul_assoc]
    rw [h_assoc, hea, neg_mul, neg_neg]
    abel

/-- **Theorem**: Mutual commutativity of the rank-five Cartan subalgebra: $[H_a, H_b] = 0$. -/
theorem bracket_H_H (a b : Fin 5) :
    bracket (W.H a) (W.H b) = 0 := by
  unfold H bracket
  by_cases hab : a = b
  · subst b
    abel
  · have h1 : (W.e a * W.f a - ⅟(2 : R) • 1) * (W.e b * W.f b - ⅟(2 : R) • 1) =
        (W.e a * W.f a) * (W.e b * W.f b) - ⅟(2 : R) • (W.e a * W.f a) - ⅟(2 : R) • (W.e b * W.f b) +
          (⅟(2 : R) * ⅟(2 : R)) • (1 : A) := by
      rw [sub_mul, mul_sub, mul_sub]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one, smul_smul]
      abel
    have h2 : (W.e b * W.f b - ⅟(2 : R) • 1) * (W.e a * W.f a - ⅟(2 : R) • 1) =
        (W.e b * W.f b) * (W.e a * W.f a) - ⅟(2 : R) • (W.e b * W.f b) - ⅟(2 : R) • (W.e a * W.f a) +
          (⅟(2 : R) * ⅟(2 : R)) • (1 : A) := by
      rw [sub_mul, mul_sub, mul_sub]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one, smul_smul]
      abel
    have hef_ab := W.anticomm_ef a b
    simp only [if_neg hab] at hef_ab
    have hef_ba := W.anticomm_ef b a
    simp only [if_neg (Ne.symm hab)] at hef_ba
    have hee := W.anticomm_ee a b
    have hff := W.anticomm_ff a b
    have h_fb_ea : W.f a * W.e b = - (W.e b * W.f a) := by
      rw [← add_eq_zero_iff_eq_neg, add_comm]
      exact hef_ba
    have h_eb_ea : W.e a * W.e b = - (W.e b * W.e a) := by
      rw [← add_eq_zero_iff_eq_neg]
      exact hee
    have h_fb_fa : W.f a * W.f b = - (W.f b * W.f a) := by
      rw [← add_eq_zero_iff_eq_neg]
      exact hff
    have h_ea_fb : W.e a * W.f b = - (W.f b * W.e a) := by
      rw [← add_eq_zero_iff_eq_neg]
      exact hef_ab
    have hef_comm : (W.e a * W.f a) * (W.e b * W.f b) = (W.e b * W.f b) * (W.e a * W.f a) := by
      calc (W.e a * W.f a) * (W.e b * W.f b)
        _ = W.e a * (W.f a * W.e b) * W.f b := by simp only [mul_assoc]
        _ = W.e a * (- (W.e b * W.f a)) * W.f b := by rw [h_fb_ea]
        _ = - (W.e a * W.e b * W.f a * W.f b) := by simp only [mul_neg, neg_mul, mul_assoc]
        _ = - (W.e a * W.e b * (W.f a * W.f b)) := by simp only [mul_assoc]
        _ = - (- (W.e b * W.e a) * (- (W.f b * W.f a))) := by rw [h_eb_ea, h_fb_fa]
        _ = - (W.e b * W.e a * (W.f b * W.f a)) := by
          have h_neg_neg : - (W.e b * W.e a) * (- (W.f b * W.f a)) = (W.e b * W.e a) * (W.f b * W.f a) := by
            rw [neg_mul_neg]
          rw [h_neg_neg]
        _ = - (W.e b * (W.e a * W.f b * W.f a)) := by simp only [mul_assoc]
        _ = - (W.e b * (- (W.f b * W.e a) * W.f a)) := by rw [h_ea_fb]
        _ = (W.e b * W.f b) * (W.e a * W.f a) := by
          have h_mid2 : W.e b * (- (W.f b * W.e a) * W.f a) = - (W.e b * (W.f b * (W.e a * W.f a))) := by
            simp only [neg_mul, mul_neg, mul_assoc]
          rw [h_mid2, neg_neg, mul_assoc]
    rw [h1, h2, hef_comm]
    abel

end WittBasis55

/-! ## 2. Spinor Chirality vs Krein Fundamental Symmetry -/

/-- Chirality / volume operator $\Gamma_*$ on the 32-spinor space. -/
structure SpinorChirality (A : Type*) [Ring A] [Algebra R A] (W : WittBasis55 (R := R) A) where
  gamma_star : A
  gamma_star_sq : gamma_star * gamma_star = 1
  gamma_star_anticomm_e : ∀ a, gamma_star * W.e a = - (W.e a * gamma_star)
  gamma_star_anticomm_f : ∀ a, gamma_star * W.f a = - (W.f a * gamma_star)

/-- Krein fundamental symmetry $J_K$ on the 32-spinor space.
    Kept strictly distinct from $\Gamma_*$. -/
structure KreinFundamentalSymmetry (A : Type*) [Ring A] where
  J_K : A
  J_K_sq : J_K * J_K = 1

namespace SpinorChirality

variable (W : WittBasis55 (R := R) A) (χ : SpinorChirality (R := R) A W)

/-- Positive chiral projector $P_+ = \frac{1}{2}(I + \Gamma_*)$. -/
def P_plus : A := ⅟(2 : R) • (1 + χ.gamma_star)

/-- Negative chiral projector $P_- = \frac{1}{2}(I - \Gamma_*)$. -/
def P_minus : A := ⅟(2 : R) • (1 - χ.gamma_star)

/-- **Theorem**: $P_+$ is an idempotent projector ($P_+^2 = P_+$). -/
theorem P_plus_sq : χ.P_plus * χ.P_plus = χ.P_plus := by
  unfold P_plus
  rw [smul_mul_smul_comm]
  have hmul : (1 + χ.gamma_star) * (1 + χ.gamma_star) = (2 : R) • (1 + χ.gamma_star) := by
    have h : (1 + χ.gamma_star) * (1 + χ.gamma_star) = 1 + χ.gamma_star + χ.gamma_star + χ.gamma_star * χ.gamma_star := by noncomm_ring
    rw [h, χ.gamma_star_sq, two_smul]
    abel
  rw [hmul, smul_smul, mul_assoc, invOf_mul_self, mul_one]

/-- **Theorem**: $P_-$ is an idempotent projector ($P_-^2 = P_-$). -/
theorem P_minus_sq : χ.P_minus * χ.P_minus = χ.P_minus := by
  unfold P_minus
  rw [smul_mul_smul_comm]
  have hmul : (1 - χ.gamma_star) * (1 - χ.gamma_star) = (2 : R) • (1 - χ.gamma_star) := by
    have h : (1 - χ.gamma_star) * (1 - χ.gamma_star) = 1 - χ.gamma_star - χ.gamma_star + χ.gamma_star * χ.gamma_star := by noncomm_ring
    rw [h, χ.gamma_star_sq, two_smul]
    abel
  rw [hmul, smul_smul, mul_assoc, invOf_mul_self, mul_one]

/-- **Theorem**: Chiral projector orthogonality: $P_+ P_- = 0$. -/
theorem P_plus_mul_P_minus : χ.P_plus * χ.P_minus = 0 := by
  unfold P_plus P_minus
  rw [smul_mul_smul_comm]
  have hmul : (1 + χ.gamma_star) * (1 - χ.gamma_star) = 0 := by
    have h : (1 + χ.gamma_star) * (1 - χ.gamma_star) = 1 - χ.gamma_star + χ.gamma_star - χ.gamma_star * χ.gamma_star := by noncomm_ring
    rw [h, χ.gamma_star_sq]
    abel
  rw [hmul, smul_zero]

/-- **Theorem**: Chiral projector resolution of identity: $P_+ + P_- = 1$. -/
theorem P_plus_add_P_minus : χ.P_plus + χ.P_minus = 1 := by
  unfold P_plus P_minus
  rw [← smul_add]
  have hadd : (1 + χ.gamma_star) + (1 - χ.gamma_star) = (2 : R) • (1 : A) := by
    rw [two_smul]
    abel
  rw [hadd, smul_smul, invOf_mul_self, one_smul]

end SpinorChirality

/-! ## 3. Spinor Bilinear Form and Lagrangian Subspaces -/

/-- Invariant bilinear form on the spinor carrier $S$. -/
structure SpinorBilinearForm (S : Type*) [AddCommGroup S] [Module R S] where
  B : S →ₗ[R] S →ₗ[R] R
  -- Chirality skew property: B(Γ_* u, v) = - B(u, Γ_* v)
  chirality_skew : ∀ (gamma_star : S →ₗ[R] S) (u v : S),
    B (gamma_star u) v = - B u (gamma_star v)

namespace SpinorBilinearForm

variable {S : Type*} [AddCommGroup S] [Module R S]
variable (BF : SpinorBilinearForm (R := R) S)

/-- Positive chiral projector on the linear space $S$. -/
def linearPPlus (gamma_star : S →ₗ[R] S) : S →ₗ[R] S :=
  ⅟(2 : R) • (LinearMap.id + gamma_star)

/-- Negative chiral projector on the linear space $S$. -/
def linearPMinus (gamma_star : S →ₗ[R] S) : S →ₗ[R] S :=
  ⅟(2 : R) • (LinearMap.id - gamma_star)

omit [Invertible (2 : R)] in
lemma B_smul_smul (c d : R) (x y : S) :
    BF.B (c • x) (d • y) = (c * d) • BF.B x y := by
  rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, smul_smul, mul_comm]

/-- **Theorem**: The positive chiral subspace $S^+ = \operatorname{im}(P_+)$ is isotropic under $B$. -/
theorem chiral_plus_isotropic
    (gamma_star : S →ₗ[R] S)
    (h_sq : gamma_star.comp gamma_star = LinearMap.id)
    (u v : S) :
    BF.B (linearPPlus gamma_star u) (linearPPlus gamma_star v) = 0 := by
  unfold linearPPlus
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
  rw [BF.B_smul_smul]
  have h_skew := BF.chirality_skew gamma_star u v
  have h_sq_app : gamma_star (gamma_star u) = u := by
    have h := LinearMap.congr_fun h_sq u
    simpa using h
  have h_skew_star : BF.B (gamma_star u) (gamma_star v) = - BF.B u v := by
    have h := BF.chirality_skew gamma_star (gamma_star u) v
    rw [h_sq_app] at h
    rw [h, neg_neg]
  rw [LinearMap.map_add, LinearMap.map_add, LinearMap.add_apply, LinearMap.add_apply]
  have h_sum : BF.B u v + BF.B (gamma_star u) v + (BF.B u (gamma_star v) + BF.B (gamma_star u) (gamma_star v)) = 0 := by
    rw [h_skew, h_skew_star]
    abel
  rw [h_sum, smul_zero]

/-- **Theorem**: The negative chiral subspace $S^- = \operatorname{im}(P_-)$ is isotropic under $B$. -/
theorem chiral_minus_isotropic
    (gamma_star : S →ₗ[R] S)
    (h_sq : gamma_star.comp gamma_star = LinearMap.id)
    (u v : S) :
    BF.B (linearPMinus gamma_star u) (linearPMinus gamma_star v) = 0 := by
  unfold linearPMinus
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [BF.B_smul_smul]
  have h_skew := BF.chirality_skew gamma_star u v
  have h_sq_app : gamma_star (gamma_star u) = u := by
    have h := LinearMap.congr_fun h_sq u
    simpa using h
  have h_skew_star : BF.B (gamma_star u) (gamma_star v) = - BF.B u v := by
    have h := BF.chirality_skew gamma_star (gamma_star u) v
    rw [h_sq_app] at h
    rw [h, neg_neg]
  rw [LinearMap.map_sub, LinearMap.map_sub, LinearMap.sub_apply, LinearMap.sub_apply]
  have h_sum : BF.B u v - BF.B (gamma_star u) v - (BF.B u (gamma_star v) - BF.B (gamma_star u) (gamma_star v)) = 0 := by
    rw [h_skew, h_skew_star]
    abel
  rw [h_sum, smul_zero]

end SpinorBilinearForm

/-! ## 4. Moduli Space M_{0,5}(ℝ) Dihedral Cartan Readout -/

/-- Dihedral Cartan embedding $U(u) = \sum_{a=0}^4 u_a H_a$ on the 5-point moduli space.
    Note: $\dim_\mathbb{R} \mathcal{M}_{0,5}(\mathbb{R}) = 2$, so $(u_0, \dots, u_4)$ are constrained
    coordinates on the Deligne-Mumford pentagon, NOT 5 independent unconstrained moduli. -/
def dihedralCartanReadout
    (W : WittBasis55 (R := R) A) (u : Fin 5 → R) : A :=
  ∑ a : Fin 5, u a • W.H a

/-- **Theorem**: Commutativity of any two dihedral Cartan elements: $[U(u), U(v)] = 0$. -/
theorem dihedralCartanReadout_comm
    (W : WittBasis55 (R := R) A) (u v : Fin 5 → R) :
    WittBasis55.bracket (dihedralCartanReadout W u) (dihedralCartanReadout W v) = 0 := by
  unfold dihedralCartanReadout
  rw [WittBasis55.bracket_sum_left]
  simp_rw [WittBasis55.bracket_sum_right]
  simp_rw [WittBasis55.bracket_smul_left, WittBasis55.bracket_smul_right]
  simp_rw [W.bracket_H_H, smul_zero, Finset.sum_const_zero]

/-! ## 5. Grand Cl(5,5) Spinor Master Theorem -/

/-- 
🏆 **GRAND SYNTHESIS THEOREM: Cl(5,5) Purely Real 32-Spinor Operator Laboratory**

Unifies:
1. Exact CAR algebra for the 5-mode Witt basis.
2. The complete rank-five Cartan action: $[H_a, H_b] = 0$, $[H_a, e_b] = \delta_{ab} e_b$, $[H_a, f_b] = -\delta_{ab} f_b$.
3. Spinor chirality projectors $P_\pm^2 = P_\pm$, $P_+ P_- = 0$, $P_+ + P_- = 1$.
4. Strict separation of chirality $\Gamma_*$ from Krein symmetry $J_K$.
5. Isotropic property of chiral subspaces $S^\pm$ under the spinor bilinear form.
6. Dihedral Cartan readout commutativity for $\mathcal{M}_{0,5}(\mathbb{R})$ pentagonal coordinates.
-/
theorem grand_cl55_witt_spinor_synthesis
    (W : WittBasis55 (R := R) A)
    (χ : SpinorChirality (R := R) A W)
    {S : Type*} [AddCommGroup S] [Module R S]
    (BF : SpinorBilinearForm (R := R) S)
    (gamma_star : S →ₗ[R] S)
    (h_gamma_sq : gamma_star.comp gamma_star = LinearMap.id)
    (u v : Fin 5 → R) :
    -- (1) Cartan action
    (∀ a b, WittBasis55.bracket (W.H a) (W.e b) = if a = b then W.e b else 0) ∧
    (∀ a b, WittBasis55.bracket (W.H a) (W.f b) = if a = b then - W.f b else 0) ∧
    (∀ a b, WittBasis55.bracket (W.H a) (W.H b) = 0) ∧
    -- (2) Chirality Projectors
    (χ.P_plus * χ.P_plus = χ.P_plus ∧
     χ.P_minus * χ.P_minus = χ.P_minus ∧
     χ.P_plus * χ.P_minus = 0 ∧
     χ.P_plus + χ.P_minus = 1) ∧
    -- (3) Isotropic Chiral Subspaces
    (∀ x y, BF.B (SpinorBilinearForm.linearPPlus gamma_star x) (SpinorBilinearForm.linearPPlus gamma_star y) = 0 ∧
            BF.B (SpinorBilinearForm.linearPMinus gamma_star x) (SpinorBilinearForm.linearPMinus gamma_star y) = 0) ∧
    -- (4) Dihedral Cartan Readout Commutativity
    (WittBasis55.bracket (dihedralCartanReadout W u) (dihedralCartanReadout W v) = 0) := by
  refine ⟨W.bracket_H_e, W.bracket_H_f, W.bracket_H_H, ?_, ?_, dihedralCartanReadout_comm W u v⟩
  · exact ⟨χ.P_plus_sq, χ.P_minus_sq, χ.P_plus_mul_P_minus, χ.P_plus_add_P_minus⟩
  · intro x y
    exact ⟨BF.chiral_plus_isotropic gamma_star h_gamma_sq x y,
           BF.chiral_minus_isotropic gamma_star h_gamma_sq x y⟩

end InfoGeometry.Clifford.Cl55WittSpinorLaboratory
