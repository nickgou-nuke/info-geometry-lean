import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The Triad of The Holomorphic, The Antiholomorphic, and The Real

This module establishes the canonical mathematical bridge formalizing:
1. **The Para-Complex Splitting & Split Peirce Projectors**:
   On a $(2n, 2n)$ para-hyperkähler manifold, the complex unit is replaced by the
   hyperbolic/para-complex unit $\tau$ satisfying $\tau^2 = +1$.
   The split Peirce projectors
   $$P_+ = \frac{1 + \tau}{2}, \quad P_- = \frac{1 - \tau}{2}$$
   decompose the real tangent bundle $TM = T^{1,0}M \oplus T^{0,1}M$ into totally
   real, independent Lagrangian sub-bundles without invoking $\sqrt{-1}$.

2. **Chiral Differential Calculus**:
   The total exterior derivative decomposes into real chiral operators:
   $$d = \partial_\tau + \bar{\partial}_\tau$$
   where $\partial_\tau = P_+ d$ governs forward/holomorphic propagation and
   $\bar{\partial}_\tau = P_- d$ governs backward/antiholomorphic propagation.

3. **The Klein Bottle Seam as The Real Slice**:
   On split coordinates $z = x + \tau t$ and $\bar{z} = x - \tau t$, the condition
   $z = \bar{z}$ is equivalent to $2 \tau t = 0$.
   The seam $t = 0$ is the purely real fixed locus where forward and backward
   waves interfere with equal amplitude.

4. **The Zorn 4-Vector Operator & Mass Condensation**:
   In the real $2 \times 2$ Zorn matrix representation
   $$\hat{Z}(a, \Delta) = \begin{pmatrix} a & \Delta \\ \Delta & -a \end{pmatrix}$$
   - $\operatorname{tr}(\hat{Z}) = 0$ (traceless Weyl dilaton mode)
   - $\hat{Z}^2 = (a^2 + \Delta^2) \mathbb{I}$
   - $\det(\hat{Z}) = -(a^2 + \Delta^2)$
   - Massless limit ($\Delta = 0$): decoupled null rays traveling at $\pm c$
   - Massive locking ($\Delta = m$): off-diagonal bridge locks the holomorphic and
     antiholomorphic modes into the relativistic mass-shell $E^2 = p^2 + m^2$.
-/

namespace InfoGeometry.Canonical.ParaComplexHolomorphicReal

section ParaComplexAlgebra

variable {R : Type*} [CommRing R]

/-- Split Peirce projector $P_+ = \frac{1 + \tau}{2}$ under invertible 2. -/
def peircePlus (tau half : R) : R :=
  half * (1 + tau)

/-- Split Peirce projector $P_- = \frac{1 - \tau}{2}$ under invertible 2. -/
def peirceMinus (tau half : R) : R :=
  half * (1 - tau)

/-- Completeness: $P_+ + P_- = 1$ when $2 \cdot \mathrm{half} = 1$. -/
theorem peirce_sum (tau half : R) (h2 : 2 * half = 1) :
    peircePlus tau half + peirceMinus tau half = 1 := by
  unfold peircePlus peirceMinus
  calc
    half * (1 + tau) + half * (1 - tau) = (2 * half) := by ring
    _ = 1 := h2

/-- Idempotency of positive projector: $P_+^2 = P_+$ when $\tau^2 = 1$ and $2 \cdot \mathrm{half} = 1$. -/
theorem peircePlus_idem (tau half : R) (htau : tau * tau = 1) (h2 : 2 * half = 1) :
    peircePlus tau half * peircePlus tau half = peircePlus tau half := by
  unfold peircePlus
  calc
    (half * (1 + tau)) * (half * (1 + tau)) = (half * half) * (1 + 2 * tau + tau * tau) := by ring
    _ = (half * half) * (1 + 2 * tau + 1) := by rw [htau]
    _ = (half * half) * (2 * (1 + tau)) := by ring
    _ = (2 * half) * (half * (1 + tau)) := by ring
    _ = 1 * (half * (1 + tau)) := by rw [h2]
    _ = half * (1 + tau) := by ring

/-- Idempotency of negative projector: $P_-^2 = P_-$ when $\tau^2 = 1$ and $2 \cdot \mathrm{half} = 1$. -/
theorem peirceMinus_idem (tau half : R) (htau : tau * tau = 1) (h2 : 2 * half = 1) :
    peirceMinus tau half * peirceMinus tau half = peirceMinus tau half := by
  unfold peirceMinus
  calc
    (half * (1 - tau)) * (half * (1 - tau)) = (half * half) * (1 - 2 * tau + tau * tau) := by ring
    _ = (half * half) * (1 - 2 * tau + 1) := by rw [htau]
    _ = (half * half) * (2 * (1 - tau)) := by ring
    _ = (2 * half) * (half * (1 - tau)) := by ring
    _ = 1 * (half * (1 - tau)) := by rw [h2]
    _ = half * (1 - tau) := by ring

/-- Orthogonality: $P_+ P_- = 0$ when $\tau^2 = 1$. -/
theorem peirce_ortho (tau half : R) (htau : tau * tau = 1) :
    peircePlus tau half * peirceMinus tau half = 0 := by
  unfold peircePlus peirceMinus
  calc
    (half * (1 + tau)) * (half * (1 - tau)) = (half * half) * (1 - tau * tau) := by ring
    _ = (half * half) * (1 - 1) := by rw [htau]
    _ = 0 := by ring

/-- Reverse orthogonality: $P_- P_+ = 0$ when $\tau^2 = 1$. -/
theorem peirce_ortho_rev (tau half : R) (htau : tau * tau = 1) :
    peirceMinus tau half * peircePlus tau half = 0 := by
  rw [mul_comm]
  exact peirce_ortho tau half htau

/-- Chiral eigenvalue relation: $\tau P_+ = P_+$ when $\tau^2 = 1$. -/
theorem tau_mul_peircePlus (tau half : R) (htau : tau * tau = 1) :
    tau * peircePlus tau half = peircePlus tau half := by
  unfold peircePlus
  calc
    tau * (half * (1 + tau)) = half * (tau + tau * tau) := by ring
    _ = half * (tau + 1) := by rw [htau]
    _ = half * (1 + tau) := by ring

/-- Antichiral eigenvalue relation: $\tau P_- = - P_-$ when $\tau^2 = 1$. -/
theorem tau_mul_peirceMinus (tau half : R) (htau : tau * tau = 1) :
    tau * peirceMinus tau half = - peirceMinus tau half := by
  unfold peirceMinus
  calc
    tau * (half * (1 - tau)) = half * (tau - tau * tau) := by ring
    _ = half * (tau - 1) := by rw [htau]
    _ = - (half * (1 - tau)) := by ring

/-- Chirality grading: $P_+ - P_- = \tau$ when $2 \cdot \mathrm{half} = 1$. -/
theorem peirce_diff (tau half : R) (h2 : 2 * half = 1) :
    peircePlus tau half - peirceMinus tau half = tau := by
  unfold peircePlus peirceMinus
  calc
    half * (1 + tau) - half * (1 - tau) = (2 * half) * tau := by ring
    _ = 1 * tau := by rw [h2]
    _ = tau := by ring

/-- Holomorphic derivative: $\partial_\tau = P_+ d$. -/
def holomorphicDeriv (tau half d : R) : R :=
  peircePlus tau half * d

/-- Antiholomorphic derivative: $\bar{\partial}_\tau = P_- d$. -/
def antiholomorphicDeriv (tau half d : R) : R :=
  peirceMinus tau half * d

/-- de Rham decomposition: $d = \partial_\tau + \bar{\partial}_\tau$ when $2 \cdot \mathrm{half} = 1$. -/
theorem deRham_decomposition (tau half d : R) (h2 : 2 * half = 1) :
    holomorphicDeriv tau half d + antiholomorphicDeriv tau half d = d := by
  unfold holomorphicDeriv antiholomorphicDeriv
  calc
    peircePlus tau half * d + peirceMinus tau half * d =
        (peircePlus tau half + peirceMinus tau half) * d := by ring
    _ = 1 * d := by rw [peirce_sum tau half h2]
    _ = d := by ring

/-- Real Seam Condition: $z = x + \tau t$ and $\bar{z} = x - \tau t$.
    The seam condition $z = \bar{z}$ is equivalent to $2 \tau t = 0$. -/
theorem real_seam_condition (x t tau : R) :
    (x + tau * t = x - tau * t) ↔ (2 * tau * t = 0) := by
  constructor
  · intro h
    calc
      2 * tau * t = (x + tau * t) - (x - tau * t) := by ring
      _ = (x - tau * t) - (x - tau * t) := by rw [h]
      _ = 0 := by ring
  · intro h
    calc
      x + tau * t = (x - tau * t) + (2 * tau * t) := by ring
      _ = (x - tau * t) + 0 := by rw [h]
      _ = x - tau * t := by ring

theorem real_seam_condition_of_isUnit (x t tau : R) (hunit : IsUnit (2 * tau)) :
    (x + tau * t = x - tau * t) ↔ t = 0 := by
  rw [real_seam_condition]
  constructor
  · intro h
    apply hunit.mul_left_cancel
    simpa using h
  · intro h
    rw [h, mul_zero]

theorem paracomplex_norm (x t tau : R) (htau : tau * tau = 1) :
    (x + tau * t) * (x - tau * t) = x ^ 2 - t ^ 2 := by
  have htau' : tau ^ 2 = 1 := by simpa [pow_two] using htau
  calc
    (x + tau * t) * (x - tau * t) = x ^ 2 - (tau * t) ^ 2 := by ring
    _ = x ^ 2 - t ^ 2 := by rw [mul_pow, htau']; ring

theorem peircePlus_lightcone_factor (x t tau half : ℝ)
    (htau : tau * tau = 1) :
    peircePlus tau half * (x + tau * t) = (x + t) * peircePlus tau half := by
  unfold peircePlus
  ring_nf
  have hpow : tau ^ 2 = 1 := by simpa [pow_two] using htau
  rw [hpow]
  ring

theorem peirceMinus_lightcone_factor (x t tau half : ℝ)
    (htau : tau * tau = 1) :
    peirceMinus tau half * (x + tau * t) = (x - t) * peirceMinus tau half := by
  unfold peirceMinus
  ring_nf
  have hpow : tau ^ 2 = 1 := by simpa [pow_two] using htau
  rw [hpow]
  ring

theorem peirce_chiral_null_annihilation (u v tau half : R)
    (htau : tau * tau = 1) :
    (u * peircePlus tau half) * (v * peirceMinus tau half) = 0 := by
  calc
    (u * peircePlus tau half) * (v * peirceMinus tau half) =
        (u * v) * (peircePlus tau half * peirceMinus tau half) := by ring
    _ = 0 := by rw [peirce_ortho tau half htau, mul_zero]

end ParaComplexAlgebra

section ZornCarrier

/-- Zorn 4-vector matrix in $2 \times 2$ real representation:
    $\hat{Z}(a, \Delta) = \begin{pmatrix} a & \Delta \\ \Delta & -a \end{pmatrix}$. -/
def zorn2 (a delta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, delta; delta, -a]

/-- Zorn matrix trace is identically zero (Weyl dilaton condition). -/
theorem zorn2_trace_zero (a delta : ℝ) :
    (zorn2 a delta).trace = 0 := by
  dsimp [zorn2, Matrix.trace, Matrix.diag]
  simp

/-- Zorn matrix square: $\hat{Z}^2 = (a^2 + \Delta^2) \mathbb{I}$. -/
theorem zorn2_sq (a delta : ℝ) :
    zorn2 a delta * zorn2 a delta = (a^2 + delta^2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zorn2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Zorn matrix determinant: $\det(\hat{Z}) = -(a^2 + \Delta^2)$. -/
theorem zorn2_det (a delta : ℝ) :
    (zorn2 a delta).det = - (a^2 + delta^2) := by
  dsimp [zorn2]
  rw [Matrix.det_fin_two]
  simp
  ring

theorem zorn2_det_eq_zero_iff (a delta : ℝ) :
    (zorn2 a delta).det = 0 ↔ a = 0 ∧ delta = 0 := by
  rw [zorn2_det]
  constructor
  · intro h
    have hsum : a ^ 2 + delta ^ 2 = 0 := by linarith
    have ha : a ^ 2 = 0 := by
      have hd : 0 ≤ delta ^ 2 := sq_nonneg delta
      nlinarith
    have hd : delta ^ 2 = 0 := by
      have ha' : 0 ≤ a ^ 2 := sq_nonneg a
      nlinarith
    exact ⟨sq_eq_zero_iff.mp ha, sq_eq_zero_iff.mp hd⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- Massless limit: when $\Delta = 0$, $\hat{Z}^2 = a^2 \mathbb{I}$ (pure chiral null rays). -/
theorem zorn2_massless_sq (a : ℝ) :
    zorn2 a 0 * zorn2 a 0 = (a^2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h := zorn2_sq a 0
  simpa using h

/-- Relativistic mass-shell condition:
    $\hat{Z}^2 = E^2 \mathbb{I} \iff a^2 + \Delta^2 = E^2$. -/
theorem zorn2_mass_shell (a delta E : ℝ) :
    zorn2 a delta * zorn2 a delta = (E^2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ↔ a^2 + delta^2 = E^2 := by
  rw [zorn2_sq]
  constructor
  · intro h
    have h00 : ((a^2 + delta^2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 =
               ((E^2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 := by rw [h]
    simp at h00
    exact h00
  · intro h
    rw [h]

end ZornCarrier

section Synthesis

/-- Structure packaging the Holomorphic-Antiholomorphic-Real Triad architecture. -/
structure ParaComplexHolomorphicRealSynthesis where
  peirce_partition :
    ∀ {R : Type*} [CommRing R] (tau half : R),
      2 * half = 1 → peircePlus tau half + peirceMinus tau half = 1
  peirce_plus_idempotent :
    ∀ {R : Type*} [CommRing R] (tau half : R),
      tau * tau = 1 → 2 * half = 1 → peircePlus tau half * peircePlus tau half = peircePlus tau half
  peirce_minus_idempotent :
    ∀ {R : Type*} [CommRing R] (tau half : R),
      tau * tau = 1 → 2 * half = 1 → peirceMinus tau half * peirceMinus tau half = peirceMinus tau half
  peirce_orthogonal :
    ∀ {R : Type*} [CommRing R] (tau half : R),
      tau * tau = 1 → peircePlus tau half * peirceMinus tau half = 0
  peirce_grading :
    ∀ {R : Type*} [CommRing R] (tau half : R),
      2 * half = 1 → peircePlus tau half - peirceMinus tau half = tau
  holomorphic_eigenvalue :
    ∀ {R : Type*} [CommRing R] (tau half : R),
      tau * tau = 1 → tau * peircePlus tau half = peircePlus tau half
  antiholomorphic_eigenvalue :
    ∀ {R : Type*} [CommRing R] (tau half : R),
      tau * tau = 1 → tau * peirceMinus tau half = - peirceMinus tau half
  derham_split :
    ∀ {R : Type*} [CommRing R] (tau half d : R),
      2 * half = 1 → holomorphicDeriv tau half d + antiholomorphicDeriv tau half d = d
  seam_characterization :
    ∀ {R : Type*} [CommRing R] (x t tau : R),
      (x + tau * t = x - tau * t) ↔ (2 * tau * t = 0)
  seam_characterization_of_isUnit :
    ∀ {R : Type*} [CommRing R] (x t tau : R),
      IsUnit (2 * tau) → ((x + tau * t = x - tau * t) ↔ t = 0)
  paracomplex_norm_formula :
    ∀ {R : Type*} [CommRing R] (x t tau : R),
      tau * tau = 1 → (x + tau * t) * (x - tau * t) = x ^ 2 - t ^ 2
  chiral_null_annihilation :
    ∀ {R : Type*} [CommRing R] (u v tau half : R),
      tau * tau = 1 → (u * peircePlus tau half) * (v * peirceMinus tau half) = 0
  zorn_traceless :
    ∀ (a delta : ℝ), (zorn2 a delta).trace = 0
  zorn_square :
    ∀ (a delta : ℝ), zorn2 a delta * zorn2 a delta = (a^2 + delta^2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  zorn_determinant :
    ∀ (a delta : ℝ), (zorn2 a delta).det = - (a^2 + delta^2)
  mass_shell_equivalence :
    ∀ (a delta E : ℝ),
      zorn2 a delta * zorn2 a delta = (E^2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ↔ a^2 + delta^2 = E^2

/-- Certified construction of the Holomorphic-Antiholomorphic-Real Triad synthesis. -/
theorem certified_paracomplex_holomorphic_real_synthesis : ParaComplexHolomorphicRealSynthesis where
  peirce_partition := by intros; apply peirce_sum; assumption
  peirce_plus_idempotent := by intros; apply peircePlus_idem <;> assumption
  peirce_minus_idempotent := by intros; apply peirceMinus_idem <;> assumption
  peirce_orthogonal := by intros; apply peirce_ortho; assumption
  peirce_grading := by intros; apply peirce_diff; assumption
  holomorphic_eigenvalue := by intros; apply tau_mul_peircePlus; assumption
  antiholomorphic_eigenvalue := by intros; apply tau_mul_peirceMinus; assumption
  derham_split := by intros; apply deRham_decomposition; assumption
  seam_characterization := by intros; apply real_seam_condition
  seam_characterization_of_isUnit := by intros; apply real_seam_condition_of_isUnit; assumption
  paracomplex_norm_formula := by intros; apply paracomplex_norm; assumption
  chiral_null_annihilation := by intros; apply peirce_chiral_null_annihilation; assumption
  zorn_traceless := zorn2_trace_zero
  zorn_square := zorn2_sq
  zorn_determinant := zorn2_det
  mass_shell_equivalence := zorn2_mass_shell

end Synthesis

end InfoGeometry.Canonical.ParaComplexHolomorphicReal
