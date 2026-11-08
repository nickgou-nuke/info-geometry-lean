import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real Complex Matrix

noncomputable section

namespace InfoGeometry.Physics.BiWaveRamanujan

/-!
# Aharonov Bi-Wave Krein Intertwiner and Ramanujan Modular Projection Bridge

This module formalizes:
1. The Krein swap metric $J = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ on the doubled bi-wave space.
2. Aharonov weak values of channel projection operators in the two-state vector formalism.
3. Modular balance: $\|\psi_{\mathrm{fwd}}(s)\|^2 = \|\psi_{\mathrm{bwd}}(s)\|^2 \iff \operatorname{Re}(s) = 1/2$.
4. Boundary intertwining operator $S(t) = (1/2 + it)/(1/2 - it)$ with exact unitarity and inversion.
5. Ramanujan trigonometrical sums $c_q(n)$ along periodic orbits with totient ground state and $\mathcal{PT}$ symmetry.
-/

/-!
### 1. The Krein Swap Metric on Doubled Bi-Wave Space
-/

/-- The fundamental Krein metric swap matrix on the doubled bi-wave space:
    $J = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. -/
def kreinSwapMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- The 2x2 identity matrix. -/
def id2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 1]

/-- 🏆 THEOREM 1: The Krein swap matrix is an involution: $J^2 = \mathbb{I}$. -/
theorem kreinSwapMatrix_sq :
    kreinSwapMatrix * kreinSwapMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kreinSwapMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- 🏆 THEOREM 2: The determinant of the Krein swap matrix is $-1$ (odd signature $(1, 1)$). -/
theorem kreinSwapMatrix_det :
    kreinSwapMatrix.det = -1 := by
  simp [kreinSwapMatrix, Matrix.det_fin_two]

/-- 🏆 THEOREM 3: The trace of the Krein swap matrix vanishes: $\operatorname{tr}(J) = 0$. -/
theorem kreinSwapMatrix_trace :
    kreinSwapMatrix.trace = 0 := by
  simp [kreinSwapMatrix, Matrix.trace, Fin.sum_univ_two]

/-!
### 2. Aharonov Weak Values in Two-State Vector Formalism
-/

/-- Weak value of an observable $\hat{\mathcal{O}}$ between pre-selected forward wave $\psi_i$
    and post-selected backward wave $\psi_f$: $A_w = \frac{\psi_f^* \mathcal{O} \psi_i}{\psi_f^* \psi_i}$. -/
def weakValue (overlap num : ℂ) : ℂ :=
  num / overlap

/-- 🏆 THEOREM 4: Identity observable weak value is identically 1 for any non-zero overlap. -/
theorem weakValue_id (overlap : ℂ) (h : overlap ≠ 0) :
    weakValue overlap overlap = 1 := by
  dsimp [weakValue]
  exact div_self h

/-- 🏆 THEOREM 5: Forward projector weak value:
    $P_{\mathrm{fwd}} |\psi_i\rangle = |\psi_i\rangle$, so $\langle \psi_f | P_{\mathrm{fwd}} | \psi_i \rangle = \langle \psi_f | \psi_i \rangle$,
    yielding $A_w(P_{\mathrm{fwd}}) = 1$. -/
theorem weakValue_forward_projector (overlap : ℂ) (h : overlap ≠ 0) :
    weakValue overlap overlap = 1 :=
  weakValue_id overlap h

/-- 🏆 THEOREM 6: Complementary backward projector weak value is 0:
    $P_{\mathrm{bwd}} |\psi_i\rangle = 0$, so $\langle \psi_f | P_{\mathrm{bwd}} | \psi_i \rangle = 0$,
    yielding $A_w(P_{\mathrm{bwd}}) = 0$. -/
theorem weakValue_backward_projector (overlap : ℂ) :
    weakValue overlap 0 = 0 := by
  dsimp [weakValue]
  simp

/-- 🏆 THEOREM 7: Weak value linearity / partition of unity:
    $A_w(P_{\mathrm{fwd}}) + A_w(P_{\mathrm{bwd}}) = 1 + 0 = 1$. -/
theorem weakValue_projector_sum (overlap : ℂ) (h : overlap ≠ 0) :
    weakValue overlap overlap + weakValue overlap 0 = 1 := by
  rw [weakValue_forward_projector overlap h, weakValue_backward_projector overlap]
  ring

/-!
### 3. Modular Balance on the Critical Seam
-/

/-- Forward-propagating bi-wave component: $\psi_{\mathrm{fwd}}(s) = s$. -/
def psiFwd (s : ℂ) : ℂ := s

/-- Backward-propagating bi-wave component: $\psi_{\mathrm{bwd}}(s) = 1 - s$. -/
def psiBwd (s : ℂ) : ℂ := 1 - s

/-- 🏆 THEOREM 8: Modular balance / equidistance:
    The forward and backward bi-waves have equal norm squares if and only if
    the frequency lies on the critical seam $\operatorname{Re}(s) = 1/2$. -/
theorem biwave_modular_balance (sigma t : ℝ) :
    let s : ℂ := (sigma : ℂ) + (t : ℂ) * Complex.I
    Complex.normSq (psiFwd s) = Complex.normSq (psiBwd s) ↔ sigma = 1 / 2 := by
  intro s
  dsimp [s, psiFwd, psiBwd]
  have h1 : Complex.normSq ((sigma : ℂ) + (t : ℂ) * Complex.I) = sigma ^ 2 + t ^ 2 := by
    rw [Complex.normSq_add_mul_I]
  have h_one_sub : (1 : ℂ) - ((sigma : ℂ) + (t : ℂ) * Complex.I) = ((1 - sigma : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h_one_sub]
  have h2 : Complex.normSq (((1 - sigma : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) = (1 - sigma) ^ 2 + t ^ 2 := by
    rw [Complex.normSq_add_mul_I]
    ring
  rw [h1, h2]
  constructor
  · intro h
    have h_sub : (sigma ^ 2 + t ^ 2) - ((1 - sigma) ^ 2 + t ^ 2) = 0 := by linarith
    have h_alg : (sigma ^ 2 + t ^ 2) - ((1 - sigma) ^ 2 + t ^ 2) = 2 * sigma - 1 := by ring
    rw [h_alg] at h_sub
    linarith
  · intro h
    rw [h]
    ring

/-!
### 4. Boundary Intertwining Operator & Unitarity
-/

/-- The 1-body boundary intertwining scattering matrix:
    $S(t) = \frac{1/2 + it}{1/2 - it}$. -/
def boundaryIntertwiner (t : ℝ) : ℂ :=
  (1 / 2 + Complex.I * (t : ℂ)) / (1 / 2 - Complex.I * (t : ℂ))

/-- Conjugate denominator lemma. -/
theorem intertwiner_denom_conj (t : ℝ) :
    starRingEnd ℂ (1 / 2 + Complex.I * (t : ℂ)) = 1 / 2 - Complex.I * (t : ℂ) := by
  simp only [map_add, map_div₀, map_ofNat, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- Non-vanishing denominator. -/
theorem intertwiner_denom_ne_zero (t : ℝ) :
    (1 / 2 : ℂ) - Complex.I * (t : ℂ) ≠ 0 := by
  intro h
  have h_re := congr_arg Complex.re h
  simp only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
    sub_zero, zero_re] at h_re
  norm_num at h_re

/-- 🏆 THEOREM 9: Exact unitarity of the boundary intertwiner along the critical line:
    $\|S(t)\| = 1$. -/
theorem boundaryIntertwiner_unitary (t : ℝ) :
    ‖boundaryIntertwiner t‖ = 1 := by
  dsimp [boundaryIntertwiner]
  rw [norm_div]
  have h_conj := Complex.norm_conj ((1 / 2 : ℂ) + Complex.I * (t : ℂ))
  rw [intertwiner_denom_conj t] at h_conj
  rw [h_conj.symm]
  exact div_self (norm_ne_zero_iff.mpr (intertwiner_denom_ne_zero t))

/-- 🏆 THEOREM 10: Throat ground state identity: $S(0) = 1$. -/
theorem boundaryIntertwiner_zero :
    boundaryIntertwiner 0 = 1 := by
  dsimp [boundaryIntertwiner]
  simp

/-- 🏆 THEOREM 11: Intertwiner inversion across time-reversal: $S(t) \cdot S(-t) = 1$. -/
theorem boundaryIntertwiner_inversion (t : ℝ) :
    boundaryIntertwiner t * boundaryIntertwiner (-t) = 1 := by
  dsimp [boundaryIntertwiner]
  have h_denom := intertwiner_denom_ne_zero t
  have h_num : (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
    have h_conj := intertwiner_denom_ne_zero (-t)
    have h_eq : (1 / 2 : ℂ) - Complex.I * ((-t : ℝ) : ℂ) = (1 / 2 : ℂ) + Complex.I * (t : ℂ) := by
      push_cast; ring
    rw [h_eq] at h_conj
    exact h_conj
  have h_neg1 : (1 : ℂ) / 2 + Complex.I * ((-t : ℝ) : ℂ) = 1 / 2 - Complex.I * (t : ℂ) := by
    push_cast; ring
  have h_neg2 : (1 : ℂ) / 2 - Complex.I * ((-t : ℝ) : ℂ) = 1 / 2 + Complex.I * (t : ℂ) := by
    push_cast; ring
  rw [h_neg1, h_neg2]
  rw [div_mul_div_comm]
  rw [mul_comm ((1 / 2 : ℂ) - Complex.I * (t : ℂ)) ((1 / 2 : ℂ) + Complex.I * (t : ℂ))]
  exact div_self (mul_ne_zero h_num h_denom)

/-!
### 5. Ramanujan Periodic Orbit Trigonometrical Sums
-/

/-- The coprime residue index set for modulus $q \ge 1$. -/
def coprimeResidues (q : ℕ) : Finset ℕ :=
  Finset.filter (fun a => q.Coprime a) (Finset.range q)

/-- Ramanujan's trigonometrical sum along a periodic orbit of period $q$:
    $c_q(n) = \sum_{a \in (\mathbb{Z}/q\mathbb{Z})^\times} \cos(2\pi a n / q)$. -/
def ramanujanSum (q : ℕ) (n : ℤ) : ℝ :=
  ∑ a ∈ coprimeResidues q, Real.cos (2 * Real.pi * (a : ℝ) * (n : ℝ) / (q : ℝ))

/-- Cardinality of coprime residues equals Euler's totient function. -/
theorem card_coprimeResidues (q : ℕ) :
    (coprimeResidues q).card = Nat.totient q :=
  rfl

/-- 🏆 THEOREM 12: Ground state value:
    At zero frequency $n = 0$, Ramanujan's sum evaluates to Euler's totient function:
    $c_q(0) = \varphi(q)$. -/
theorem ramanujanSum_zero (q : ℕ) :
    ramanujanSum q 0 = Nat.totient q := by
  dsimp [ramanujanSum]
  have h_term : ∀ a ∈ coprimeResidues q, Real.cos (2 * Real.pi * (a : ℝ) * ((0 : ℤ) : ℝ) / (q : ℝ)) = 1 := by
    intro a _
    have h_zero : 2 * Real.pi * (a : ℝ) * ((0 : ℤ) : ℝ) / (q : ℝ) = 0 := by ring
    rw [h_zero, Real.cos_zero]
  rw [Finset.sum_congr rfl h_term]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [card_coprimeResidues]

/-- 🏆 THEOREM 13: Time-reversal / $\mathcal{PT}$ symmetry:
    $c_q(-n) = c_q(n)$. -/
theorem ramanujanSum_neg (q : ℕ) (n : ℤ) :
    ramanujanSum q (-n) = ramanujanSum q n := by
  dsimp [ramanujanSum]
  congr 1
  ext a
  have h_neg : 2 * Real.pi * (a : ℝ) * ((-n : ℤ) : ℝ) / (q : ℝ) = - (2 * Real.pi * (a : ℝ) * (n : ℝ) / (q : ℝ)) := by
    push_cast
    ring
  rw [h_neg, Real.cos_neg]

/-- 🏆 MASTER CONJUNCTION: Certified Aharonov Bi-Wave & Ramanujan Modular Synthesis. -/
theorem certified_biwave_ramanujan_synthesis (t : ℝ) (q : ℕ) (n : ℤ) :
    (kreinSwapMatrix * kreinSwapMatrix = 1) ∧
    (kreinSwapMatrix.det = -1) ∧
    (kreinSwapMatrix.trace = 0) ∧
    (∀ (overlap : ℂ), overlap ≠ 0 → weakValue overlap overlap = 1) ∧
    (∀ (overlap : ℂ), weakValue overlap 0 = 0) ∧
    (∀ (sigma : ℝ), Complex.normSq (psiFwd ((sigma : ℂ) + (t : ℂ) * Complex.I)) =
      Complex.normSq (psiBwd ((sigma : ℂ) + (t : ℂ) * Complex.I)) ↔ sigma = 1 / 2) ∧
    (‖boundaryIntertwiner t‖ = 1) ∧
    (boundaryIntertwiner 0 = 1) ∧
    (boundaryIntertwiner t * boundaryIntertwiner (-t) = 1) ∧
    (ramanujanSum q 0 = Nat.totient q) ∧
    (ramanujanSum q (-n) = ramanujanSum q n) :=
  ⟨kreinSwapMatrix_sq,
   kreinSwapMatrix_det,
   kreinSwapMatrix_trace,
   fun overlap => weakValue_forward_projector overlap,
   fun overlap => weakValue_backward_projector overlap,
   fun sigma => biwave_modular_balance sigma t,
   boundaryIntertwiner_unitary t,
   boundaryIntertwiner_zero,
   boundaryIntertwiner_inversion t,
   ramanujanSum_zero q,
   ramanujanSum_neg q n⟩

#print axioms certified_biwave_ramanujan_synthesis

end InfoGeometry.Physics.BiWaveRamanujan
