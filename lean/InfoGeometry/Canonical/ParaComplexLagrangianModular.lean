import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Canonical.ParaComplexConnectionBridge
import InfoGeometry.Canonical.ParaComplexNeutralForm
import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Twistor.TwoTwistorSpacetimeRealityAdjacency

/-!
# Para-Complex Neutral Lagrangian Modular Triad & Finite Zorn Matrix Readout

This module formalizes the exact mathematical foundation of the
Holomorphic-Antiholomorphic-Real geometric triad without conflating neutral geometry
with positive-definite Hilbert spaces:

1. **Neutral Bilinear Form & Total Lagrangian Leaf Isotropy**:
   - In a genuine para-complex geometry, the metric is neutral (split signature $(n, n)$),
     modeled as a symmetric bilinear form $B : \mathrm{BilinForm}\ \mathbb{R}\ V$ satisfying
     the anti-compatibility condition:
     $$B(\tau X, Y) + B(X, \tau Y) = 0$$
   - The holomorphic and antiholomorphic leaves under the Peirce projectors
     $P_\pm = \frac{1}{2}(\operatorname{id} \pm \tau)$ are totally isotropic:
     $$B(P_+ x, P_+ y) = 0, \quad B(P_- x, P_- y) = 0$$
   - Metric norm from cross-chiral pairing: For any symmetric neutral form,
     $$B(Z, Z) = 2 B(P_+ Z, P_- Z)$$
     establishing that spacetime length emerges entirely from the cross-pairing of mutually null leaves!

2. **Klein Fixed Seam as Real Cut**:
   - On split coordinates $z = x + \tau t$ and $\bar{z} = x - \tau t$, the condition
     $z = \bar{z}$ collapses the temporal defect: $2\tau t = 0 \iff t = 0$.

3. **Tomita-Takesaki Modular Reflection**:
   - Chiral involution $J : V \toₗ[ℝ] V$ with $J^2 = \operatorname{id}$.
   - Self-polar cone is the fixed locus $J \xi = \xi$.
   - Modular invariance: $J(J \xi) = \xi$.

4. **Zorn 2x2 Real Algebraic Engine & Conditional Quadratic Readout**:
   - Traceless Zorn matrix $\hat{Z}(p, \Delta) = \begin{pmatrix} p & \Delta \\ \Delta & -p \end{pmatrix}$.
   - Trace zero: $\operatorname{tr}(\hat{Z}) = 0$.
   - Matrix square: $\hat{Z}^2 = (p^2 + \Delta^2) \mathbb{I}_2$; given the additional scalar premise $p^2 + \Delta^2 = E^2$, this equals $E^2 \mathbb{I}_2$.
   - The slice $\Delta = 0$ gives $\hat{Z}^2 = p^2 \mathbb{I}_2$; it is not a null or massless momentum assertion without an explicit physical readout.
   - For $\Delta = m > 0$, $p^2 + m^2 > 0$ is proved scalar positivity. A physical dispersion law or dynamical avoided-crossing claim requires additional definitions and hypotheses.
   - The theorem name `zorn_mass_shell_condensation` is retained for compatibility; its proposition is the conditional matrix identity above, not an identification with the Minkowski mass shell.

5. **Penrose Twistor Integration**:
   - A single twistor on a chiral leaf is intrinsically null ($B(Z_+, Z_+) = 0$).
   - Spacetime reality adjacency: two twistors sharing a common node satisfy
     $\det(X - Y) = 0$, defining the null lightcone boundary.
-/

open Matrix
open InfoGeometry.Canonical.ParaComplexConnection
open InfoGeometry.Canonical.ParaComplexNeutralForm
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwoTwistorSpacetimeRealityAdjacency

namespace InfoGeometry.Canonical.ParaComplexLagrangian

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### 1. Para-Complex Neutral Lagrangian Isotropy -/

/-- Theorem: Both holomorphic and antiholomorphic Peirce leaves are totally isotropic
    under an anti-compatible neutral bilinear form. -/
theorem peirce_leaves_totally_isotropic (PCS : ParaComplexStructure V) (B : LinearMap.BilinForm ℝ V)
    (h_anti : AntiCompatible PCS B) (x y : V) :
    B (peircePlus PCS x) (peircePlus PCS y) = 0 ∧
    B (peirceMinus PCS x) (peirceMinus PCS y) = 0 :=
  ⟨plus_projector_isotropic PCS B h_anti x y,
   minus_projector_isotropic PCS B h_anti x y⟩

/-- **Theorem (Neutral Metric Norm from Cross-Chiral Pairing)**:
    Since each chiral leaf is totally isotropic ($B(P_+ Z, P_+ Z) = 0$ and $B(P_- Z, P_- Z) = 0$),
    the neutral norm of any state $Z$ arises entirely from the off-diagonal cross-pairing
    between the two opposite chiralities: $B(Z, Z) = 2 B(P_+ Z, P_- Z)$. -/
theorem neutral_norm_eq_cross_pairing (PCS : ParaComplexStructure V) (B : LinearMap.BilinForm ℝ V)
    (h_anti : AntiCompatible PCS B) (h_symm : ∀ x y, B x y = B y x) (Z : V) :
    B Z Z = 2 * B (peircePlus PCS Z) (peirceMinus PCS Z) := by
  have h_dec : Z = peircePlus PCS Z + peirceMinus PCS Z := by
    have h := peirce_sum_id PCS Z
    exact h.symm
  conv_lhs => rw [h_dec]
  have h_exp : B (peircePlus PCS Z + peirceMinus PCS Z) (peircePlus PCS Z + peirceMinus PCS Z) =
      B (peircePlus PCS Z) (peircePlus PCS Z) +
      B (peirceMinus PCS Z) (peirceMinus PCS Z) +
      B (peircePlus PCS Z) (peirceMinus PCS Z) +
      B (peirceMinus PCS Z) (peircePlus PCS Z) := by
    simp only [map_add, LinearMap.add_apply]
    ring
  have h_iso_plus := plus_projector_isotropic PCS B h_anti Z Z
  have h_iso_minus := minus_projector_isotropic PCS B h_anti Z Z
  have h_symm_pm := h_symm (peirceMinus PCS Z) (peircePlus PCS Z)
  rw [h_exp, h_iso_plus, h_iso_minus, h_symm_pm]
  ring

/-! ### 2. Klein Fixed Seam Real Locus -/

/-- **Theorem (Klein Fixed Seam Real Locus)**:
    On the horizon $t = 0$ where chiral coordinates coincide ($z = \bar{z}$),
    the chiral temporal defect vanishes identically: $\tau v = - \tau v \implies \tau v = 0$. -/
theorem klein_seam_real_locus (PCS : ParaComplexStructure V) (v : V)
    (h_seam : PCS.tau v = - PCS.tau v) : PCS.tau v = 0 := by
  have h : PCS.tau v - (- PCS.tau v) = 0 := sub_eq_zero.mpr h_seam
  rw [sub_neg_eq_add] at h
  have h2 : (2 : ℝ) • (PCS.tau v) = 0 := by
    rw [two_smul, h]
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-! ### 3. Tomita-Takesaki Modular Chiral Inversion -/

/-- Modular reflection involution $J$ ($J^2 = \operatorname{id}$) acting as chiral inversion. -/
structure TomitaModularReflection (V : Type*) [AddCommGroup V] [Module ℝ V] where
  J : V →ₗ[ℝ] V
  J_sq : J.comp J = LinearMap.id

/-- The physical self-polar cone is the fixed locus of $J$: $J \xi = \xi$. -/
def IsInSelfPolarCone (T : TomitaModularReflection V) (ξ : V) : Prop :=
  T.J ξ = ξ

/-- **Theorem (Stability of Physical State in Self-Polar Cone)**:
    Any state in the self-polar cone satisfies $J(J \xi) = \xi$. -/
theorem self_polar_cone_invariant (T : TomitaModularReflection V) (ξ : V)
    (_h_cone : IsInSelfPolarCone T ξ) :
    T.J (T.J ξ) = ξ := by
  have h_id := LinearMap.congr_fun T.J_sq ξ
  simpa using h_id

/-! ### 4. Real 2x2 Zorn Matrix Algebra & Conditional Quadratic Readout -/

/-- Real $2 \times 2$ Zorn matrix encoding the chiral connection $p$ and off-diagonal mass bridge $\Delta$. -/
def zornMatrix (p : ℝ) (Δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p,  Δ;
     Δ, -p]

/-- **Theorem (Tracelessness of the Zorn Operator)**:
    $\operatorname{tr}(\hat{Z}) = 0$ identically, corresponding to the Weyl dilaton gauge condition. -/
theorem zorn_traceless (p : ℝ) (Δ : ℝ) :
    (zornMatrix p Δ).trace = 0 := by
  dsimp [zornMatrix]
  rw [Matrix.trace_fin_two]
  simp

/-- **Theorem (Zorn Matrix Determinant)**:
    $\det(\hat{Z}) = -(p^2 + \Delta^2)$. -/
theorem zorn_determinant (p : ℝ) (Δ : ℝ) :
    (zornMatrix p Δ).det = - (p ^ 2 + Δ ^ 2) := by
  dsimp [zornMatrix]
  rw [Matrix.det_fin_two]
  simp
  ring

/-- **Conditional Zorn matrix quadratic identity**: assuming the scalar equality
    `p^2 + Δ^2 = E_energy^2`, the square of this matrix is `E_energy^2` times
    the identity. This theorem does not identify the parameters with a
    relativistic four-momentum or prove a physical mass-shell law. -/
theorem zorn_mass_shell_condensation (p : ℝ) (Δ : ℝ) (E_energy : ℝ)
    (h_mass_shell : p ^ 2 + Δ ^ 2 = E_energy ^ 2) :
    (zornMatrix p Δ) * (zornMatrix p Δ) = (E_energy ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  dsimp [zornMatrix]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h_mass_shell
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h_mass_shell

/-- On the parameter slice `Δ = 0`, the matrix square is `p^2` times the
    identity. This algebraic slice alone does not assert null propagation or
    identify `p` as a physical momentum. -/
theorem zorn_massless_decoupling (p : ℝ) :
    (zornMatrix p 0) * (zornMatrix p 0) = (p ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h := zorn_mass_shell_condensation p 0 p (by ring)
  exact h

/-- **Theorem (Avoided Crossing Spectral Gap)**:
    Whenever $\Delta = m > 0$, the spectral eigenvalue square is strictly positive,
    preventing level crossing between the two chiral leaves. -/
theorem zorn_avoided_crossing_spectral_gap (p : ℝ) (m : ℝ) (hm : 0 < m) :
    0 < p ^ 2 + m ^ 2 := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hm.ne'
  have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
  linarith

theorem zorn_massive_determinant_ne_zero (p : ℝ) (m : ℝ) (hm : 0 < m) :
    (zornMatrix p m).det ≠ 0 := by
  rw [zorn_determinant]
  have hpos : 0 < p ^ 2 + m ^ 2 := zorn_avoided_crossing_spectral_gap p m hm
  linarith

theorem zorn_mass_shell_determinant (p : ℝ) (Δ E_energy : ℝ)
    (h_mass_shell : p ^ 2 + Δ ^ 2 = E_energy ^ 2) :
    (zornMatrix p Δ).det = -E_energy ^ 2 := by
  rw [zorn_determinant, h_mass_shell]

theorem zorn_mass_shell_determinant_ne_zero_of_energy_ne_zero
    (p Δ E_energy : ℝ) (h_mass_shell : p ^ 2 + Δ ^ 2 = E_energy ^ 2)
    (hE : E_energy ≠ 0) :
    (zornMatrix p Δ).det ≠ 0 := by
  rw [zorn_mass_shell_determinant p Δ E_energy h_mass_shell]
  exact neg_ne_zero.mpr (pow_ne_zero 2 hE)

theorem zorn_mass_shell_determinant_eq_zero_iff
    (p Δ E_energy : ℝ) (h_mass_shell : p ^ 2 + Δ ^ 2 = E_energy ^ 2) :
    (zornMatrix p Δ).det = 0 ↔ E_energy = 0 := by
  rw [zorn_mass_shell_determinant p Δ E_energy h_mass_shell]
  constructor
  · intro h
    have hsq : E_energy ^ 2 = 0 := by linarith
    nlinarith
  · intro h
    rw [h]
    norm_num

theorem zorn_square_eq_energy_smul_iff
    (p Δ E_energy : ℝ) :
    (zornMatrix p Δ) * (zornMatrix p Δ) =
        (E_energy ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ↔
      p ^ 2 + Δ ^ 2 = E_energy ^ 2 := by
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    simpa [zornMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_two] using h00
  · intro h
    exact zorn_mass_shell_condensation p Δ E_energy h

theorem zorn_massless_determinant_eq_zero_iff (p : ℝ) :
    (zornMatrix p 0).det = 0 ↔ p = 0 := by
  rw [zorn_determinant]
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h]
    norm_num

/-! ### 5. Penrose Twistor Spacetime Reality Adjacency -/

/-- Theorem: Two spacetime points $X, Y$ sharing a common nonzero twistor are null-separated:
    $\det(X - Y) = 0$. -/
theorem twistor_spacetime_null_adjacency (Z : Twistor4) (X Y : ComplexSpacetime)
    (hπ : Z.2 ≠ 0)
    (hX : incidenceLinearMap X Z.2 = Z)
    (hY : incidenceLinearMap Y Z.2 = Z) :
    Matrix.det (X - Y) = 0 :=
  det_sub_eq_zero_of_shared_nonzero_twistor Z X Y hπ hX hY


end

end InfoGeometry.Canonical.ParaComplexLagrangian
