import Mathlib.Tactic
import InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit

/-!
# Chiral Hodge--Dirac Block Bridge on Doubled Real Krein Spaces

This module formalizes the exact chiral block decomposition of the Hodge--Dirac
operator on a **doubled real Krein space carrying an internal real complex structure**:

$$\mathcal{K}_{\mathbb{R}} = V_+ \oplus V_- \simeq V \oplus V^* \simeq \mathbb{R}^{n,n}$$

For split-octonions ($n = 4$), $\mathcal{K}_{\mathbb{R}} \simeq \mathbb{R}^{4,4}$; for the $\operatorname{Cl}(5,5)$
umbrella carrier, $\mathcal{K}_{\mathbb{R}}^{5,5} \simeq U \oplus U^*$.

### 1. Real Chiral Projector Architecture & Krein Symmetry
- For a real grading involution $\Gamma^2 = I$:
  $$P_+ = \frac{1}{2}(I + \Gamma), \qquad P_- = \frac{1}{2}(I - \Gamma)$$
- Projector orthogonality and completeness:
  $$P_+^2 = P_+, \quad P_-^2 = P_-, \quad P_+ P_- = P_- P_+ = 0, \quad P_+ + P_- = I$$
- Indefinite Krein fundamental symmetry:
  $$J = P_+ - P_- = \Gamma, \qquad J^2 = I$$
- Vacuum / zero-mode projector:
  $$P_0 = I - (P_+ + P_-) = 0$$

### 2. Chiral Cross-Sheet Arrows & Off-Diagonal Dirac Decomposition
- For an odd operator $\{\Gamma, D\} = 0$ ($\Gamma D = -D \Gamma$):
  $$D P_+ = P_- D, \qquad D P_- = P_+ D$$
- The real cross-sheet arrows $D_+ : V_+ \to V_-$ and $D_- : V_- \to V_+$:
  $$D_+ = P_- D P_+ = D P_+ = P_- D$$
  $$D_- = P_+ D P_- = D P_- = P_+ D$$
- Vanishing diagonal blocks:
  $$P_+ D P_+ = 0, \qquad P_- D P_- = 0$$
- Exact off-diagonal matrix decomposition:
  $$D = D_+ + D_- = \begin{pmatrix} 0 & D_- \\ D_+ & 0 \end{pmatrix}$$

### 3. Chiral Nilpotency & Laplacian Block Factorization
- Nilpotency from chiral typing:
  $$D_+^2 = 0, \qquad D_-^2 = 0$$
- Factorization of the even Hodge Laplacian $\Delta = D^2$:
  $$\Delta = D_- D_+ + D_+ D_- = \begin{pmatrix} D_- D_+ & 0 \\ 0 & D_+ D_- \end{pmatrix}$$
  $$\Delta_+ := P_+ \Delta P_+ = D_- D_+, \qquad \Delta_- := P_- \Delta P_- = D_+ D_-$$

### 4. Sheet Exchange / Mirror Involution $\kappa_{\mathrm{exch}}$
- In a doubled Witt polarization, the sheet exchange involution satisfies:
  $$\kappa_{\mathrm{exch}}^2 = I, \qquad \{\kappa_{\mathrm{exch}}, \Gamma\} = 0$$
- It interchanges the chiral projectors and cross-sheet arrows:
  $$\kappa_{\mathrm{exch}} P_\pm = P_\mp \kappa_{\mathrm{exch}}$$
  $$[\kappa_{\mathrm{exch}}, D] = 0 \implies \kappa_{\mathrm{exch}} D_\pm = D_\mp \kappa_{\mathrm{exch}}$$

### 5. Internal Real Complex / Hestenes Structure $K$
- Real operator $K$ with $K^2 = -I$ on the doubled real Krein carrier:
  $$[K, D] = 0 \implies (KD)^2 = -\Delta$$
  $$D^2 = +\Delta \quad \text{vs.} \quad (KD)^2 = -\Delta$$
- Chiral preservation vs. chiral swapping:
  - If $[K, \Gamma] = 0 \implies K D_\pm = D_\pm K$ (complex structure on each chiral half).
  - If $\{K, \Gamma\} = 0 \implies K D_\pm = D_\mp K$ (cross-sheet complex structure).
-/

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.ChiralHodgeDiracBlockBridge

open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

section GeneralAlgebraic

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {H : Type*} [AddCommGroup H] [Module R H]
variable (Γ D : Module.End R H)

/-- Positive chiral projector P₊ = ½ (I + Γ). -/
def chiralProjectorPlus (Γ : Module.End R H) : Module.End R H :=
  (⅟(2 : R)) • (1 + Γ)

/-- Negative chiral projector P₋ = ½ (I - Γ). -/
def chiralProjectorMinus (Γ : Module.End R H) : Module.End R H :=
  (⅟(2 : R)) • (1 - Γ)

/-- Vacuum / zero-mode projector P₀ = 1 - (P₊ + P₋). -/
def chiralProjectorZero (Γ : Module.End R H) : Module.End R H :=
  1 - (chiralProjectorPlus Γ + chiralProjectorMinus Γ)

/-- Fundamental Krein metric / involution J = P₊ - P₋. -/
def kreinFundamentalSymmetry (Γ : Module.End R H) : Module.End R H :=
  chiralProjectorPlus Γ - chiralProjectorMinus Γ

theorem chiralProjector_sum (Γ : Module.End R H) :
    chiralProjectorPlus Γ + chiralProjectorMinus Γ = 1 := by
  dsimp [chiralProjectorPlus, chiralProjectorMinus]
  rw [← smul_add]
  have h : (1 + Γ) + (1 - Γ) = (2 : R) • (1 : Module.End R H) := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.smul_apply, two_smul]
    abel
  rw [h, smul_smul, invOf_mul_self, one_smul]

theorem chiralProjectorZero_eq_zero (Γ : Module.End R H) :
    chiralProjectorZero Γ = 0 := by
  dsimp [chiralProjectorZero]
  rw [chiralProjector_sum Γ, sub_self]

theorem kreinFundamentalSymmetry_eq (Γ : Module.End R H) :
    kreinFundamentalSymmetry Γ = Γ := by
  dsimp [kreinFundamentalSymmetry, chiralProjectorPlus, chiralProjectorMinus]
  rw [← smul_sub]
  have h : (1 + Γ) - (1 - Γ) = (2 : R) • Γ := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.smul_apply, two_smul]
    abel
  rw [h, smul_smul, invOf_mul_self, one_smul]

theorem kreinFundamentalSymmetry_sq (hΓ : Γ * Γ = 1) :
    kreinFundamentalSymmetry Γ * kreinFundamentalSymmetry Γ = 1 := by
  rw [kreinFundamentalSymmetry_eq Γ]
  exact hΓ

theorem chiralProjectorPlus_sq (hΓ : Γ * Γ = 1) :
    chiralProjectorPlus Γ * chiralProjectorPlus Γ = chiralProjectorPlus Γ := by
  dsimp [chiralProjectorPlus]
  ext x
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.one_apply, map_smul, map_add]
  have hΓ_app : Γ (Γ x) = x := by
    have h : (Γ * Γ) x = (1 : Module.End R H) x := by rw [hΓ]
    exact h
  rw [hΓ_app]
  rw [← smul_add]
  have hsum : (x + Γ x) + (Γ x + x) = (2 : R) • (x + Γ x) := by
    simp only [two_smul]
    abel
  rw [hsum, smul_smul, smul_smul]
  have h_scalar : (⅟(2 : R) * ⅟(2 : R)) * (2 : R) = ⅟(2 : R) := by
    calc
      (⅟(2 : R) * ⅟(2 : R)) * (2 : R) = ⅟(2 : R) * (⅟(2 : R) * 2) := by ring
      _ = ⅟(2 : R) * 1 := by rw [invOf_mul_self]
      _ = ⅟(2 : R) := by ring
  rw [h_scalar]

theorem chiralProjectorMinus_sq (hΓ : Γ * Γ = 1) :
    chiralProjectorMinus Γ * chiralProjectorMinus Γ = chiralProjectorMinus Γ := by
  dsimp [chiralProjectorMinus]
  ext x
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply, map_smul, map_sub]
  have hΓ_app : Γ (Γ x) = x := by
    have h : (Γ * Γ) x = (1 : Module.End R H) x := by rw [hΓ]
    exact h
  rw [hΓ_app]
  rw [← smul_sub]
  have hsum : (x - Γ x) - (Γ x - x) = (2 : R) • (x - Γ x) := by
    simp only [two_smul]
    abel
  rw [hsum, smul_smul, smul_smul]
  have h_scalar : (⅟(2 : R) * ⅟(2 : R)) * (2 : R) = ⅟(2 : R) := by
    calc
      (⅟(2 : R) * ⅟(2 : R)) * (2 : R) = ⅟(2 : R) * (⅟(2 : R) * 2) := by ring
      _ = ⅟(2 : R) * 1 := by rw [invOf_mul_self]
      _ = ⅟(2 : R) := by ring
  rw [h_scalar]

theorem chiralProjector_orthogonal (hΓ : Γ * Γ = 1) :
    chiralProjectorPlus Γ * chiralProjectorMinus Γ = 0 ∧
    chiralProjectorMinus Γ * chiralProjectorPlus Γ = 0 := by
  constructor
  · dsimp [chiralProjectorPlus, chiralProjectorMinus]
    ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply, map_smul, map_add, map_sub]
    have hΓ_app : Γ (Γ x) = x := by
      have h : (Γ * Γ) x = (1 : Module.End R H) x := by rw [hΓ]
      exact h
    rw [hΓ_app]
    rw [← smul_sub]
    have hsum : (x + Γ x) - (Γ x + x) = 0 := by abel
    rw [hsum, smul_zero, smul_zero]
  · dsimp [chiralProjectorPlus, chiralProjectorMinus]
    ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply, map_smul, map_add, map_sub]
    have hΓ_app : Γ (Γ x) = x := by
      have h : (Γ * Γ) x = (1 : Module.End R H) x := by rw [hΓ]
      exact h
    rw [hΓ_app]
    rw [← smul_add]
    have hsum : (x - Γ x) + (Γ x - x) = 0 := by abel
    rw [hsum, smul_zero, smul_zero]

/-! ## Odd Commutation / Chiral Twisting -/

theorem dirac_comp_projectorPlus (hodd : Γ * D = - (D * Γ)) :
    D * chiralProjectorPlus Γ = chiralProjectorMinus Γ * D := by
  dsimp [chiralProjectorPlus, chiralProjectorMinus]
  ext x
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, map_sub]
  have hodd_app : Γ (D x) = - (D (Γ x)) := by
    have h : (Γ * D) x = (- (D * Γ)) x := by rw [hodd]
    exact h
  rw [hodd_app]
  have h_eq : D x + D (Γ x) = D x - -D (Γ x) := by simp only [sub_neg_eq_add]
  rw [h_eq]

theorem dirac_comp_projectorMinus (hodd : Γ * D = - (D * Γ)) :
    D * chiralProjectorMinus Γ = chiralProjectorPlus Γ * D := by
  dsimp [chiralProjectorPlus, chiralProjectorMinus]
  ext x
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, map_sub]
  have hodd_app : Γ (D x) = - (D (Γ x)) := by
    have h : (Γ * D) x = (- (D * Γ)) x := by rw [hodd]
    exact h
  rw [hodd_app]
  have h_eq : D x - D (Γ x) = D x + -D (Γ x) := by simp only [sub_eq_add_neg]
  rw [h_eq]

theorem projectorPlus_comp_dirac (hodd : Γ * D = - (D * Γ)) :
    chiralProjectorPlus Γ * D = D * chiralProjectorMinus Γ :=
  (dirac_comp_projectorMinus Γ D hodd).symm

theorem projectorMinus_comp_dirac (hodd : Γ * D = - (D * Γ)) :
    chiralProjectorMinus Γ * D = D * chiralProjectorPlus Γ :=
  (dirac_comp_projectorPlus Γ D hodd).symm

/-! ## Chiral Dirac Off-Diagonal Blocks -/

/-- D₊ : V₊ → V₋ defined as P₋ D P₊. -/
def chiralDiracPlus (D Γ : Module.End R H) : Module.End R H :=
  chiralProjectorMinus Γ * D * chiralProjectorPlus Γ

/-- D₋ : V₋ → V₊ defined as P₊ D P₋. -/
def chiralDiracMinus (D Γ : Module.End R H) : Module.End R H :=
  chiralProjectorPlus Γ * D * chiralProjectorMinus Γ

theorem chiralDiracPlus_eq (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    chiralDiracPlus D Γ = D * chiralProjectorPlus Γ ∧
    chiralDiracPlus D Γ = chiralProjectorMinus Γ * D := by
  constructor
  · unfold chiralDiracPlus
    calc
      chiralProjectorMinus Γ * D * chiralProjectorPlus Γ =
          (chiralProjectorMinus Γ * D) * chiralProjectorPlus Γ := rfl
      _ = (D * chiralProjectorPlus Γ) * chiralProjectorPlus Γ := by
        rw [← dirac_comp_projectorPlus Γ D hodd]
      _ = D * (chiralProjectorPlus Γ * chiralProjectorPlus Γ) := by rw [mul_assoc]
      _ = D * chiralProjectorPlus Γ := by rw [chiralProjectorPlus_sq Γ hΓ]
  · unfold chiralDiracPlus
    calc
      chiralProjectorMinus Γ * D * chiralProjectorPlus Γ =
          chiralProjectorMinus Γ * (D * chiralProjectorPlus Γ) := mul_assoc _ _ _
      _ = chiralProjectorMinus Γ * (chiralProjectorMinus Γ * D) := by
        rw [dirac_comp_projectorPlus Γ D hodd]
      _ = (chiralProjectorMinus Γ * chiralProjectorMinus Γ) * D := by rw [← mul_assoc]
      _ = chiralProjectorMinus Γ * D := by rw [chiralProjectorMinus_sq Γ hΓ]

theorem chiralDiracMinus_eq (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    chiralDiracMinus D Γ = D * chiralProjectorMinus Γ ∧
    chiralDiracMinus D Γ = chiralProjectorPlus Γ * D := by
  constructor
  · unfold chiralDiracMinus
    calc
      chiralProjectorPlus Γ * D * chiralProjectorMinus Γ =
          (chiralProjectorPlus Γ * D) * chiralProjectorMinus Γ := rfl
      _ = (D * chiralProjectorMinus Γ) * chiralProjectorMinus Γ := by
        rw [← dirac_comp_projectorMinus Γ D hodd]
      _ = D * (chiralProjectorMinus Γ * chiralProjectorMinus Γ) := by rw [mul_assoc]
      _ = D * chiralProjectorMinus Γ := by rw [chiralProjectorMinus_sq Γ hΓ]
  · unfold chiralDiracMinus
    calc
      chiralProjectorPlus Γ * D * chiralProjectorMinus Γ =
          chiralProjectorPlus Γ * (D * chiralProjectorMinus Γ) := mul_assoc _ _ _
      _ = chiralProjectorPlus Γ * (chiralProjectorPlus Γ * D) := by
        rw [dirac_comp_projectorMinus Γ D hodd]
      _ = (chiralProjectorPlus Γ * chiralProjectorPlus Γ) * D := by rw [← mul_assoc]
      _ = chiralProjectorPlus Γ * D := by rw [chiralProjectorPlus_sq Γ hΓ]

theorem chiralDirac_diagonal_plus_zero (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    chiralProjectorPlus Γ * D * chiralProjectorPlus Γ = 0 := by
  have h_orth := chiralProjector_orthogonal Γ hΓ
  calc
    chiralProjectorPlus Γ * D * chiralProjectorPlus Γ =
        chiralProjectorPlus Γ * (D * chiralProjectorPlus Γ) := mul_assoc _ _ _
    _ = chiralProjectorPlus Γ * (chiralProjectorMinus Γ * D) := by
      rw [dirac_comp_projectorPlus Γ D hodd]
    _ = (chiralProjectorPlus Γ * chiralProjectorMinus Γ) * D := by rw [← mul_assoc]
    _ = 0 * D := by rw [h_orth.1]
    _ = 0 := by rw [zero_mul]

theorem chiralDirac_diagonal_minus_zero (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    chiralProjectorMinus Γ * D * chiralProjectorMinus Γ = 0 := by
  have h_orth := chiralProjector_orthogonal Γ hΓ
  calc
    chiralProjectorMinus Γ * D * chiralProjectorMinus Γ =
        chiralProjectorMinus Γ * (D * chiralProjectorMinus Γ) := mul_assoc _ _ _
    _ = chiralProjectorMinus Γ * (chiralProjectorPlus Γ * D) := by
      rw [dirac_comp_projectorMinus Γ D hodd]
    _ = (chiralProjectorMinus Γ * chiralProjectorPlus Γ) * D := by rw [← mul_assoc]
    _ = 0 * D := by rw [h_orth.2]
    _ = 0 := by rw [zero_mul]

theorem chiralDirac_decomposition (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    D = chiralDiracPlus D Γ + chiralDiracMinus D Γ := by
  have h_plus := (chiralDiracPlus_eq Γ D hΓ hodd).1
  have h_minus := (chiralDiracMinus_eq Γ D hΓ hodd).1
  rw [h_plus, h_minus, ← mul_add]
  rw [chiralProjector_sum Γ, mul_one]

theorem chiralDiracPlus_sq_zero (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    chiralDiracPlus D Γ * chiralDiracPlus D Γ = 0 := by
  have h_plus1 := (chiralDiracPlus_eq Γ D hΓ hodd).1
  have h_plus2 := (chiralDiracPlus_eq Γ D hΓ hodd).2
  have h_orth := (chiralProjector_orthogonal Γ hΓ).1
  calc
    chiralDiracPlus D Γ * chiralDiracPlus D Γ =
        (D * chiralProjectorPlus Γ) * (chiralProjectorMinus Γ * D) := by
          congr 1
    _ = D * (chiralProjectorPlus Γ * chiralProjectorMinus Γ) * D := by
      simp only [mul_assoc]
    _ = D * 0 * D := by rw [h_orth]
    _ = 0 := by simp

theorem chiralDiracMinus_sq_zero (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    chiralDiracMinus D Γ * chiralDiracMinus D Γ = 0 := by
  have h_minus1 := (chiralDiracMinus_eq Γ D hΓ hodd).1
  have h_minus2 := (chiralDiracMinus_eq Γ D hΓ hodd).2
  have h_orth := (chiralProjector_orthogonal Γ hΓ).2
  calc
    chiralDiracMinus D Γ * chiralDiracMinus D Γ =
        (D * chiralProjectorMinus Γ) * (chiralProjectorPlus Γ * D) := by
          congr 1
    _ = D * (chiralProjectorMinus Γ * chiralProjectorPlus Γ) * D := by
      simp only [mul_assoc]
    _ = D * 0 * D := by rw [h_orth]
    _ = 0 := by simp

/-! ## Hodge Laplacian Factorization -/

theorem dirac_sq_eq_chiral_sum (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    D * D = chiralDiracMinus D Γ * chiralDiracPlus D Γ +
            chiralDiracPlus D Γ * chiralDiracMinus D Γ := by
  have hD := chiralDirac_decomposition Γ D hΓ hodd
  conv_lhs => rw [hD]
  simp only [add_mul, mul_add]
  rw [chiralDiracPlus_sq_zero Γ D hΓ hodd, chiralDiracMinus_sq_zero Γ D hΓ hodd]
  simp only [zero_add, add_zero]

theorem laplacian_plus_eq_minus_plus (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    chiralProjectorPlus Γ * (D * D) * chiralProjectorPlus Γ =
      chiralDiracMinus D Γ * chiralDiracPlus D Γ := by
  calc
    chiralProjectorPlus Γ * (D * D) * chiralProjectorPlus Γ =
        (chiralProjectorPlus Γ * D) * (D * chiralProjectorPlus Γ) := by
          simp only [mul_assoc]
    _ = chiralDiracMinus D Γ * chiralDiracPlus D Γ := by
      have h1 : chiralProjectorPlus Γ * D = chiralDiracMinus D Γ :=
        (chiralDiracMinus_eq Γ D hΓ hodd).2.symm
      have h2 : D * chiralProjectorPlus Γ = chiralDiracPlus D Γ :=
        (chiralDiracPlus_eq Γ D hΓ hodd).1.symm
      rw [h1, h2]

theorem laplacian_minus_eq_plus_minus (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    chiralProjectorMinus Γ * (D * D) * chiralProjectorMinus Γ =
      chiralDiracPlus D Γ * chiralDiracMinus D Γ := by
  calc
    chiralProjectorMinus Γ * (D * D) * chiralProjectorMinus Γ =
        (chiralProjectorMinus Γ * D) * (D * chiralProjectorMinus Γ) := by
          simp only [mul_assoc]
    _ = chiralDiracPlus D Γ * chiralDiracMinus D Γ := by
      have h1 : chiralProjectorMinus Γ * D = chiralDiracPlus D Γ :=
        (chiralDiracPlus_eq Γ D hΓ hodd).2.symm
      have h2 : D * chiralProjectorMinus Γ = chiralDiracMinus D Γ :=
        (chiralDiracMinus_eq Γ D hΓ hodd).1.symm
      rw [h1, h2]

theorem laplacian_diagonal_plus_minus_zero (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    chiralProjectorPlus Γ * (D * D) * chiralProjectorMinus Γ = 0 := by
  have h_orth := chiralProjector_orthogonal Γ hΓ
  calc
    chiralProjectorPlus Γ * (D * D) * chiralProjectorMinus Γ =
        (chiralProjectorPlus Γ * D) * (D * chiralProjectorMinus Γ) := by simp only [mul_assoc]
    _ = (D * chiralProjectorMinus Γ) * (chiralProjectorPlus Γ * D) := by
      rw [projectorPlus_comp_dirac Γ D hodd, dirac_comp_projectorMinus Γ D hodd]
    _ = D * (chiralProjectorMinus Γ * chiralProjectorPlus Γ) * D := by simp only [mul_assoc]
    _ = D * 0 * D := by rw [h_orth.2]
    _ = 0 := by simp

theorem laplacian_diagonal_minus_plus_zero (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    chiralProjectorMinus Γ * (D * D) * chiralProjectorPlus Γ = 0 := by
  have h_orth := chiralProjector_orthogonal Γ hΓ
  calc
    chiralProjectorMinus Γ * (D * D) * chiralProjectorPlus Γ =
        (chiralProjectorMinus Γ * D) * (D * chiralProjectorPlus Γ) := by simp only [mul_assoc]
    _ = (D * chiralProjectorPlus Γ) * (chiralProjectorMinus Γ * D) := by
      rw [projectorMinus_comp_dirac Γ D hodd, dirac_comp_projectorPlus Γ D hodd]
    _ = D * (chiralProjectorPlus Γ * chiralProjectorMinus Γ) * D := by simp only [mul_assoc]
    _ = D * 0 * D := by rw [h_orth.1]
    _ = 0 := by simp

theorem laplacian_chiral_block_decomposition (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    D * D = chiralProjectorPlus Γ * (D * D) * chiralProjectorPlus Γ +
            chiralProjectorMinus Γ * (D * D) * chiralProjectorMinus Γ := by
  rw [laplacian_plus_eq_minus_plus Γ D hΓ hodd, laplacian_minus_eq_plus_minus Γ D hΓ hodd]
  exact (dirac_sq_eq_chiral_sum Γ D hΓ hodd)

/-! ## Sheet Exchange / Mirror Involution $\kappa_{\mathrm{exch}}$ -/

theorem exchange_swaps_projectors (κ : Module.End R H)
    (hκ_anti_Γ : κ * Γ = - (Γ * κ)) :
    κ * chiralProjectorPlus Γ = chiralProjectorMinus Γ * κ ∧
    κ * chiralProjectorMinus Γ = chiralProjectorPlus Γ * κ := by
  constructor
  · dsimp [chiralProjectorPlus, chiralProjectorMinus]
    ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, map_sub]
    have hκ_app : κ (Γ x) = - (Γ (κ x)) := by
      have h : (κ * Γ) x = (- (Γ * κ)) x := by rw [hκ_anti_Γ]
      exact h
    rw [hκ_app]
    have h_eq : κ x + -Γ (κ x) = κ x - Γ (κ x) := by simp only [← sub_eq_add_neg]
    rw [h_eq]
  · dsimp [chiralProjectorPlus, chiralProjectorMinus]
    ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, map_sub]
    have hκ_app : κ (Γ x) = - (Γ (κ x)) := by
      have h : (κ * Γ) x = (- (Γ * κ)) x := by rw [hκ_anti_Γ]
      exact h
    rw [hκ_app]
    have h_eq : κ x - -Γ (κ x) = κ x + Γ (κ x) := by simp only [sub_neg_eq_add]
    rw [h_eq]

theorem exchange_swaps_chiral_dirac_blocks (κ : Module.End R H)
    (hκ_anti_Γ : κ * Γ = - (Γ * κ)) (hκ_comm_D : κ * D = D * κ)
    (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    κ * chiralDiracPlus D Γ = chiralDiracMinus D Γ * κ ∧
    κ * chiralDiracMinus D Γ = chiralDiracPlus D Γ * κ := by
  have h_proj := exchange_swaps_projectors Γ κ hκ_anti_Γ
  constructor
  · have hDplus := (chiralDiracPlus_eq Γ D hΓ hodd).1
    have hDminus := (chiralDiracMinus_eq Γ D hΓ hodd).1
    rw [hDplus, hDminus]
    calc
      κ * (D * chiralProjectorPlus Γ) = (κ * D) * chiralProjectorPlus Γ := by rw [mul_assoc]
      _ = (D * κ) * chiralProjectorPlus Γ := by rw [hκ_comm_D]
      _ = D * (κ * chiralProjectorPlus Γ) := by rw [mul_assoc]
      _ = D * (chiralProjectorMinus Γ * κ) := by rw [h_proj.1]
      _ = (D * chiralProjectorMinus Γ) * κ := by rw [← mul_assoc]
  · have hDplus := (chiralDiracPlus_eq Γ D hΓ hodd).1
    have hDminus := (chiralDiracMinus_eq Γ D hΓ hodd).1
    rw [hDplus, hDminus]
    calc
      κ * (D * chiralProjectorMinus Γ) = (κ * D) * chiralProjectorMinus Γ := by rw [mul_assoc]
      _ = (D * κ) * chiralProjectorMinus Γ := by rw [hκ_comm_D]
      _ = D * (κ * chiralProjectorMinus Γ) := by rw [mul_assoc]
      _ = D * (chiralProjectorPlus Γ * κ) := by rw [h_proj.2]
      _ = (D * chiralProjectorPlus Γ) * κ := by rw [← mul_assoc]

/-! ## Internal Real Complex / Hestenes Phase K -/

theorem hestenes_phase_dirac_sq_neg_laplacian (K : Module.End R H)
    (hK_sq : K * K = -1) (hK_comm_D : K * D = D * K) :
    (K * D) * (K * D) = - (D * D) := by
  calc
    (K * D) * (K * D) = K * (D * (K * D)) := by rw [mul_assoc]
    _ = K * ((D * K) * D) := by rw [mul_assoc]
    _ = K * ((K * D) * D) := by rw [hK_comm_D]
    _ = (K * K) * (D * D) := by noncomm_ring
    _ = (-1) * (D * D) := by rw [hK_sq]
    _ = - (D * D) := by rw [neg_one_mul]

theorem hestenes_phase_commutes_chiral_blocks (K : Module.End R H)
    (hK_comm_Γ : K * Γ = Γ * K) (hK_comm_D : K * D = D * K)
    (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    K * chiralDiracPlus D Γ = chiralDiracPlus D Γ * K ∧
    K * chiralDiracMinus D Γ = chiralDiracMinus D Γ * K := by
  have hKP_plus : K * chiralProjectorPlus Γ = chiralProjectorPlus Γ * K := by
    dsimp [chiralProjectorPlus]
    ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply, map_smul, map_add]
    have hK_app : K (Γ x) = Γ (K x) := by
      have h : (K * Γ) x = (Γ * K) x := by rw [hK_comm_Γ]
      exact h
    rw [hK_app]
  have hKP_minus : K * chiralProjectorMinus Γ = chiralProjectorMinus Γ * K := by
    dsimp [chiralProjectorMinus]
    ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_smul, map_sub]
    have hK_app : K (Γ x) = Γ (K x) := by
      have h : (K * Γ) x = (Γ * K) x := by rw [hK_comm_Γ]
      exact h
    rw [hK_app]
  constructor
  · have hDplus := (chiralDiracPlus_eq Γ D hΓ hodd).1
    rw [hDplus]
    calc
      K * (D * chiralProjectorPlus Γ) = (K * D) * chiralProjectorPlus Γ := by rw [mul_assoc]
      _ = (D * K) * chiralProjectorPlus Γ := by rw [hK_comm_D]
      _ = D * (K * chiralProjectorPlus Γ) := by rw [mul_assoc]
      _ = D * (chiralProjectorPlus Γ * K) := by rw [hKP_plus]
      _ = (D * chiralProjectorPlus Γ) * K := by rw [← mul_assoc]
  · have hDminus := (chiralDiracMinus_eq Γ D hΓ hodd).1
    rw [hDminus]
    calc
      K * (D * chiralProjectorMinus Γ) = (K * D) * chiralProjectorMinus Γ := by rw [mul_assoc]
      _ = (D * K) * chiralProjectorMinus Γ := by rw [hK_comm_D]
      _ = D * (K * chiralProjectorMinus Γ) := by rw [mul_assoc]
      _ = D * (chiralProjectorMinus Γ * K) := by rw [hKP_minus]
      _ = (D * chiralProjectorMinus Γ) * K := by rw [← mul_assoc]

theorem hestenes_phase_anticommutes_chiral_blocks (K : Module.End R H)
    (hK_anti_Γ : K * Γ = - (Γ * K)) (hK_comm_D : K * D = D * K)
    (hΓ : Γ * Γ = 1) (hodd : Γ * D = - (D * Γ)) :
    K * chiralDiracPlus D Γ = chiralDiracMinus D Γ * K ∧
    K * chiralDiracMinus D Γ = chiralDiracPlus D Γ * K := by
  have h_proj := exchange_swaps_projectors Γ K hK_anti_Γ
  constructor
  · have hDplus := (chiralDiracPlus_eq Γ D hΓ hodd).1
    have hDminus := (chiralDiracMinus_eq Γ D hΓ hodd).1
    rw [hDplus, hDminus]
    calc
      K * (D * chiralProjectorPlus Γ) = (K * D) * chiralProjectorPlus Γ := by rw [mul_assoc]
      _ = (D * K) * chiralProjectorPlus Γ := by rw [hK_comm_D]
      _ = D * (K * chiralProjectorPlus Γ) := by rw [mul_assoc]
      _ = D * (chiralProjectorMinus Γ * K) := by rw [h_proj.1]
      _ = (D * chiralProjectorMinus Γ) * K := by rw [← mul_assoc]
  · have hDplus := (chiralDiracPlus_eq Γ D hΓ hodd).1
    have hDminus := (chiralDiracMinus_eq Γ D hΓ hodd).1
    rw [hDplus, hDminus]
    calc
      K * (D * chiralProjectorMinus Γ) = (K * D) * chiralProjectorMinus Γ := by rw [mul_assoc]
      _ = (D * K) * chiralProjectorMinus Γ := by rw [hK_comm_D]
      _ = D * (K * chiralProjectorMinus Γ) := by rw [mul_assoc]
      _ = D * (chiralProjectorPlus Γ * K) := by rw [h_proj.2]
      _ = (D * chiralProjectorPlus Γ) * K := by rw [← mul_assoc]

end GeneralAlgebraic

/-! ## Concrete Realization on Single Exterior Algebra Carrier (Hodge Parity Grading) -/

section SingleExteriorRealization

variable (v : V3) (φ : Module.Dual ℝ V3)

theorem exteriorGrade3_sq :
    exteriorGrade3.toLinearMap * exteriorGrade3.toLinearMap = 1 := by
  apply LinearMap.ext
  intro x
  simpa [Module.End.mul_apply, Module.End.one_apply] using
    exteriorGrade3_involutive x

theorem exteriorGrade3_odd :
    exteriorGrade3.toLinearMap * exteriorHodgeDirac3 v φ =
      -(exteriorHodgeDirac3 v φ * exteriorGrade3.toLinearMap) := by
  apply LinearMap.ext
  intro x
  simpa [Module.End.mul_apply] using exteriorHodgeDirac3_odd v φ x

/-- Positive parity projector on exterior algebra P₊ = ½ (I + Γ). -/
def exteriorChiralPlus : Exterior3End :=
  chiralProjectorPlus exteriorGrade3.toLinearMap

/-- Negative parity projector on exterior algebra P₋ = ½ (I - Γ). -/
def exteriorChiralMinus : Exterior3End :=
  chiralProjectorMinus exteriorGrade3.toLinearMap

/-- Positive cross-sheet chiral Hodge-Dirac block D₊ = P₋ D P₊. -/
def exteriorChiralDiracPlus : Exterior3End :=
  chiralDiracPlus (exteriorHodgeDirac3 v φ) exteriorGrade3.toLinearMap

/-- Negative cross-sheet chiral Hodge-Dirac block D₋ = P₊ D P₋. -/
def exteriorChiralDiracMinus : Exterior3End :=
  chiralDiracMinus (exteriorHodgeDirac3 v φ) exteriorGrade3.toLinearMap

/-- Positive block of the Hodge Laplacian Δ₊ = P₊ Δ P₊. -/
def exteriorChiralLaplacianPlus : Exterior3End :=
  exteriorChiralPlus * exteriorHodgeLaplacian3 v φ * exteriorChiralPlus

/-- Negative block of the Hodge Laplacian Δ₋ = P₋ Δ P₋. -/
def exteriorChiralLaplacianMinus : Exterior3End :=
  exteriorChiralMinus * exteriorHodgeLaplacian3 v φ * exteriorChiralMinus

theorem exteriorChiralDiracPlus_eq :
    exteriorChiralDiracPlus v φ = exteriorHodgeDirac3 v φ * exteriorChiralPlus ∧
    exteriorChiralDiracPlus v φ = exteriorChiralMinus * exteriorHodgeDirac3 v φ :=
  chiralDiracPlus_eq exteriorGrade3.toLinearMap (exteriorHodgeDirac3 v φ)
    exteriorGrade3_sq (exteriorGrade3_odd v φ)

theorem exteriorChiralDiracMinus_eq :
    exteriorChiralDiracMinus v φ = exteriorHodgeDirac3 v φ * exteriorChiralMinus ∧
    exteriorChiralDiracMinus v φ = exteriorChiralPlus * exteriorHodgeDirac3 v φ :=
  chiralDiracMinus_eq exteriorGrade3.toLinearMap (exteriorHodgeDirac3 v φ)
    exteriorGrade3_sq (exteriorGrade3_odd v φ)

theorem exteriorChiralDiracPlus_sq_zero :
    exteriorChiralDiracPlus v φ * exteriorChiralDiracPlus v φ = 0 :=
  chiralDiracPlus_sq_zero exteriorGrade3.toLinearMap (exteriorHodgeDirac3 v φ)
    exteriorGrade3_sq (exteriorGrade3_odd v φ)

theorem exteriorChiralDiracMinus_sq_zero :
    exteriorChiralDiracMinus v φ * exteriorChiralDiracMinus v φ = 0 :=
  chiralDiracMinus_sq_zero exteriorGrade3.toLinearMap (exteriorHodgeDirac3 v φ)
    exteriorGrade3_sq (exteriorGrade3_odd v φ)

theorem exteriorChiralDirac_decomposition :
    exteriorHodgeDirac3 v φ = exteriorChiralDiracPlus v φ + exteriorChiralDiracMinus v φ :=
  chiralDirac_decomposition exteriorGrade3.toLinearMap (exteriorHodgeDirac3 v φ)
    exteriorGrade3_sq (exteriorGrade3_odd v φ)

theorem exteriorChiralLaplacianPlus_eq :
    exteriorChiralLaplacianPlus v φ =
      exteriorChiralDiracMinus v φ * exteriorChiralDiracPlus v φ := by
  dsimp [exteriorChiralLaplacianPlus, exteriorChiralPlus]
  have h_sq := exteriorHodgeDirac3_sq v φ
  rw [← h_sq]
  exact laplacian_plus_eq_minus_plus exteriorGrade3.toLinearMap
    (exteriorHodgeDirac3 v φ) exteriorGrade3_sq (exteriorGrade3_odd v φ)

theorem exteriorChiralLaplacianMinus_eq :
    exteriorChiralLaplacianMinus v φ =
      exteriorChiralDiracPlus v φ * exteriorChiralDiracMinus v φ := by
  dsimp [exteriorChiralLaplacianMinus, exteriorChiralMinus]
  have h_sq := exteriorHodgeDirac3_sq v φ
  rw [← h_sq]
  exact laplacian_minus_eq_plus_minus exteriorGrade3.toLinearMap
    (exteriorHodgeDirac3 v φ) exteriorGrade3_sq (exteriorGrade3_odd v φ)

theorem exteriorLaplacian_chiral_block_decomposition :
    exteriorHodgeLaplacian3 v φ =
      exteriorChiralLaplacianPlus v φ + exteriorChiralLaplacianMinus v φ := by
  have h_sq := exteriorHodgeDirac3_sq v φ
  have h_decomp := laplacian_chiral_block_decomposition exteriorGrade3.toLinearMap
    (exteriorHodgeDirac3 v φ) exteriorGrade3_sq (exteriorGrade3_odd v φ)
  rw [← h_sq]
  rw [h_decomp]
  dsimp [exteriorChiralLaplacianPlus, exteriorChiralLaplacianMinus,
    exteriorChiralPlus, exteriorChiralMinus]
  rw [h_sq]

end SingleExteriorRealization

/-! ## Concrete Realization on Doubled Exterior Carrier -/

section ConcreteRealization

variable (v : V3) (φ : Module.Dual ℝ V3)

def concreteChiralPlus : DoubledExterior3End :=
  chiralProjectorPlus concreteChirality3

def concreteChiralMinus : DoubledExterior3End :=
  chiralProjectorMinus concreteChirality3

def concreteChiralDiracPlus : DoubledExterior3End :=
  chiralDiracPlus (concreteDirac3 v φ) concreteChirality3

def concreteChiralDiracMinus : DoubledExterior3End :=
  chiralDiracMinus (concreteDirac3 v φ) concreteChirality3

theorem concreteChiralDiracPlus_sq_zero :
    concreteChiralDiracPlus v φ * concreteChiralDiracPlus v φ = 0 :=
  chiralDiracPlus_sq_zero concreteChirality3 (concreteDirac3 v φ)
    concreteChirality3_sq (concreteChirality3_odd v φ)

theorem concreteChiralDiracMinus_sq_zero :
    concreteChiralDiracMinus v φ * concreteChiralDiracMinus v φ = 0 :=
  chiralDiracMinus_sq_zero concreteChirality3 (concreteDirac3 v φ)
    concreteChirality3_sq (concreteChirality3_odd v φ)

theorem concreteChiralDirac_decomposition :
    concreteDirac3 v φ = concreteChiralDiracPlus v φ + concreteChiralDiracMinus v φ :=
  chiralDirac_decomposition concreteChirality3 (concreteDirac3 v φ)
    concreteChirality3_sq (concreteChirality3_odd v φ)

theorem concreteLaplacian_chiral_block_decomposition :
    concreteLaplacian3 v φ =
      concreteChiralPlus * concreteLaplacian3 v φ * concreteChiralPlus +
      concreteChiralMinus * concreteLaplacian3 v φ * concreteChiralMinus := by
  have h_sq := concreteDirac3_sq v φ
  have h_decomp := laplacian_chiral_block_decomposition concreteChirality3
    (concreteDirac3 v φ) concreteChirality3_sq (concreteChirality3_odd v φ)
  rw [← h_sq]
  exact h_decomp

theorem concreteHestenesPhase3_dirac_sq :
    (hestenesPhase3 * concreteDirac3 v φ) * (hestenesPhase3 * concreteDirac3 v φ) =
      - (concreteLaplacian3 v φ) := by
  have h := hestenes_phase_dirac_sq_neg_laplacian (concreteDirac3 v φ)
    hestenesPhase3 hestenesPhase3_sq (concreteDirac3_phase v φ)
  rw [← concreteDirac3_sq v φ]
  exact h

theorem concreteHestenesPhase3_commutes_chirality :
    hestenesPhase3 * concreteChirality3 = concreteChirality3 * hestenesPhase3 := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp [hestenesPhase3, concreteChirality3, doubledDiagonal]

theorem concreteHestenesPhase3_commutes_chiral_blocks :
    hestenesPhase3 * concreteChiralDiracPlus v φ =
      concreteChiralDiracPlus v φ * hestenesPhase3 ∧
    hestenesPhase3 * concreteChiralDiracMinus v φ =
      concreteChiralDiracMinus v φ * hestenesPhase3 :=
  hestenes_phase_commutes_chiral_blocks concreteChirality3 (concreteDirac3 v φ)
    hestenesPhase3 concreteHestenesPhase3_commutes_chirality
    (concreteDirac3_phase v φ)
    concreteChirality3_sq (concreteChirality3_odd v φ)

end ConcreteRealization

end InfoGeometry.Canonical.ChiralHodgeDiracBlockBridge
