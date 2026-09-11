import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic
import InfoGeometry.Canonical.Sp56FreudenthalBlackHoleBridge

/-!
# 56D Sp(56, ℝ) DSZ Lattice Quantization & Non-Local Monodromy Twists

This module formalizes the canonical bridge connecting:
1. **The Discrete Dirac-Schwinger-Zwanziger (DSZ) Quantization Lattice $\Gamma_{\mathrm{DSZ}} \cong \mathbb{Z}^{28} \times \mathbb{Z}^{28}$**:
   The physical charge lattice of dyonic BPS states in $\mathcal{N}=8, d=4$ supergravity.
2. **The Integer DSZ Symplectic Pairing $\langle Q_1, Q_2 \rangle_{\mathrm{DSZ}} \in \mathbb{Z}$**:
   The exact topological intersection form $p_1 \cdot q_2 - q_1 \cdot p_2$.
3. **Continuous Phase Space Embedding**:
   $\iota : \Gamma_{\mathrm{DSZ}} \hookrightarrow \mathbb{R}^{56}$, preserving the continuous DSZ form:
   $\Omega_{56}(\iota(Q_1), \iota(Q_2)) = \langle Q_1, Q_2 \rangle_{\mathrm{DSZ}}$.
4. **Continuous Electromagnetic Duality Twists $T_\theta \in \mathrm{Sp}(56, \mathbb{R})$**:
   The continuous $\mathrm{SO}(2)$ group of duality rotations preserving $\Omega_{56}$ identically for all $\theta \in \mathbb{R}$.
5. **The Discrete Electric-Magnetic Exchange Involution $S = T_{\pi/2}$**:
   $S^2 = -\mathbb{I}_{56}$ (charge conjugation) and $S^4 = \mathbb{I}_{56}$, preserving both $\Gamma_{\mathrm{DSZ}}$ and the integer pairing.
6. **Parabolic Axion Monodromy Twists $T_k \in \mathrm{Sp}(56, \mathbb{Z})$**:
   Topological axion flux shifts $T_k(p, q) = (p + k q, q)$ around moduli singularities.
7. **The Fundamental $\mathrm{SL}(2, \mathbb{Z})$ Modular Presentation**:
   Strict proof of the braid relation $(S \circ T)^3 = \mathbb{I}_{56}$ and $S^4 = \mathbb{I}_{56}$ on the full 56D lattice.
-/

open Matrix Real Complex
open InfoGeometry.Canonical.Sp56FreudenthalBlackHoleBridge

namespace InfoGeometry.Canonical.Sp56DSZTwist

noncomputable section

abbrev Dim28 := Fin 28
abbrev R28 := Dim28 → ℝ
abbrev Z28 := Dim28 → ℤ

/-- A 56-dimensional integral black hole charge state $Q = (p, q) \in \mathbb{Z}^{28} \times \mathbb{Z}^{28}$
    on the Dirac-Schwinger-Zwanziger (DSZ) lattice $\Gamma_{\mathrm{DSZ}}$. -/
@[ext]
structure LatticeCharge56 where
  p : Z28
  q : Z28

/-- Discrete negation on the integral DSZ lattice. -/
def negLatticeCharge56 (Q : LatticeCharge56) : LatticeCharge56 where
  p := - Q.p
  q := - Q.q

instance : Neg LatticeCharge56 := ⟨negLatticeCharge56⟩

@[simp]
lemma negLatticeCharge56_p (Q : LatticeCharge56) : (-Q).p = - Q.p := rfl

@[simp]
lemma negLatticeCharge56_q (Q : LatticeCharge56) : (-Q).q = - Q.q := rfl

/-- Extensionality lemma for continuous 56D charge states from `Sp56FreudenthalBlackHoleBridge`. -/
@[ext]
theorem charge56_ext {Q₁ Q₂ : Charge56} (hp : Q₁.p = Q₂.p) (hq : Q₁.q = Q₂.q) : Q₁ = Q₂ := by
  cases Q₁; cases Q₂; congr

/-- Real embedding of an integral charge state into continuous phase space $\mathbb{R}^{56}$. -/
def toRealCharge56 (Q : LatticeCharge56) : Charge56 where
  p := fun i => (Q.p i : ℝ)
  q := fun i => (Q.q i : ℝ)

/-- The integer-valued DSZ symplectic pairing on the charge lattice:
    $$\langle Q_1, Q_2 \rangle_{\mathrm{DSZ}} = p_1 \cdot q_2 - q_1 \cdot p_2 \in \mathbb{Z}$$ -/
def dszPairing (Q₁ Q₂ : LatticeCharge56) : ℤ :=
  dotProduct Q₁.p Q₂.q - dotProduct Q₁.q Q₂.p

/-- 🏆 THEOREM: Skew-symmetry of the discrete DSZ pairing. -/
theorem dszPairing_skew (Q₁ Q₂ : LatticeCharge56) :
    dszPairing Q₁ Q₂ = - dszPairing Q₂ Q₁ := by
  dsimp [dszPairing]
  rw [dotProduct_comm Q₁.p Q₂.q, dotProduct_comm Q₁.q Q₂.p]
  ring

/-- 🏆 THEOREM: Vanishing on identical lattice charge states: $\langle Q, Q \rangle_{\mathrm{DSZ}} = 0$. -/
theorem dszPairing_self_zero (Q : LatticeCharge56) :
    dszPairing Q Q = 0 := by
  dsimp [dszPairing]
  rw [dotProduct_comm Q.p Q.q]
  ring

lemma dotProduct_toReal (x y : Z28) :
    dotProduct (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) = ((dotProduct x y : ℤ) : ℝ) := by
  dsimp [dotProduct]
  simp only [← Int.cast_mul, ← Int.cast_sum]

/-- 🏆 THEOREM: Exact compatibility between discrete and continuous DSZ pairings:
    $\Omega_{56}(\mathrm{toReal}(Q_1), \mathrm{toReal}(Q_2)) = \langle Q_1, Q_2 \rangle_{\mathrm{DSZ}}$. -/
theorem omega56_eq_dszPairing (Q₁ Q₂ : LatticeCharge56) :
    omega56 (toRealCharge56 Q₁) (toRealCharge56 Q₂) = (dszPairing Q₁ Q₂ : ℝ) := by
  dsimp [omega56, dszPairing, toRealCharge56]
  rw [dotProduct_toReal, dotProduct_toReal]
  push_cast
  rfl

/-- Non-local electromagnetic duality rotation by angle $\theta \in \mathbb{R}$:
    $$T_\theta(p, q) = (\cos\theta \cdot p + \sin\theta \cdot q, -\sin\theta \cdot p + \cos\theta \cdot q)$$ -/
def dualityTwist (theta : ℝ) (Q : Charge56) : Charge56 where
  p := fun i => Real.cos theta * Q.p i + Real.sin theta * Q.q i
  q := fun i => - Real.sin theta * Q.p i + Real.cos theta * Q.q i

/-- 🏆 THEOREM: The non-local duality twist preserves the DSZ symplectic form identically
    for ALL continuous angles $\theta \in \mathbb{R}$:
    $$\Omega_{56}(T_\theta(Q_1), T_\theta(Q_2)) = \Omega_{56}(Q_1, Q_2)$$ -/
theorem dualityTwist_preserves_omega56 (theta : ℝ) (Q₁ Q₂ : Charge56) :
    omega56 (dualityTwist theta Q₁) (dualityTwist theta Q₂) = omega56 Q₁ Q₂ := by
  dsimp [omega56, dualityTwist, dotProduct]
  have h_id : Real.cos theta ^ 2 + Real.sin theta ^ 2 = 1 := Real.cos_sq_add_sin_sq theta
  have h_sum : (∑ i : Dim28,
        (Real.cos theta * Q₁.p i + Real.sin theta * Q₁.q i) *
          (-Real.sin theta * Q₂.p i + Real.cos theta * Q₂.q i) -
      ∑ i : Dim28,
        (-Real.sin theta * Q₁.p i + Real.cos theta * Q₁.q i) *
          (Real.cos theta * Q₂.p i + Real.sin theta * Q₂.q i)) =
      ∑ i : Dim28, (Q₁.p i * Q₂.q i - Q₁.q i * Q₂.p i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      (Real.cos theta * Q₁.p i + Real.sin theta * Q₁.q i) *
          (-Real.sin theta * Q₂.p i + Real.cos theta * Q₂.q i) -
      (-Real.sin theta * Q₁.p i + Real.cos theta * Q₁.q i) *
          (Real.cos theta * Q₂.p i + Real.sin theta * Q₂.q i)
        = (Real.cos theta ^ 2 + Real.sin theta ^ 2) * (Q₁.p i * Q₂.q i - Q₁.q i * Q₂.p i) := by ring
      _ = 1 * (Q₁.p i * Q₂.q i - Q₁.q i * Q₂.p i) := by rw [h_id]
      _ = Q₁.p i * Q₂.q i - Q₁.q i * Q₂.p i := by ring
  rw [h_sum, Finset.sum_sub_distrib]

/-- 🏆 THEOREM: Duality twist by $\theta = 0$ is the identity: $T_0(Q) = Q$. -/
theorem dualityTwist_zero (Q : Charge56) :
    dualityTwist 0 Q = Q := by
  apply charge56_ext
  · ext i
    dsimp [dualityTwist]
    simp [Real.cos_zero, Real.sin_zero]
  · ext i
    dsimp [dualityTwist]
    simp [Real.cos_zero, Real.sin_zero]

/-- 🏆 THEOREM: Group composition of non-local twists:
    $T_{\theta_1}(T_{\theta_2}(Q)) = T_{\theta_1 + \theta_2}(Q)$. -/
theorem dualityTwist_add (theta1 theta2 : ℝ) (Q : Charge56) :
    dualityTwist theta1 (dualityTwist theta2 Q) = dualityTwist (theta1 + theta2) Q := by
  apply charge56_ext
  · ext i
    dsimp [dualityTwist]
    rw [Real.cos_add, Real.sin_add]
    ring
  · ext i
    dsimp [dualityTwist]
    rw [Real.cos_add, Real.sin_add]
    ring

/-- Discrete $\mathbb{Z}_4$ electric-magnetic exchange twist $S = T_{\pi/2}$ on continuous charges. -/
def emExchangeTwist (Q : Charge56) : Charge56 :=
  dualityTwist (π / 2) Q

/-- Explicit action of the electric-magnetic exchange twist: $S(p, q) = (q, -p)$. -/
theorem emExchangeTwist_apply (Q : Charge56) :
    emExchangeTwist Q = { p := Q.q, q := fun i => - Q.p i } := by
  apply charge56_ext
  · ext i
    dsimp [emExchangeTwist, dualityTwist]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  · ext i
    dsimp [emExchangeTwist, dualityTwist]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- 🏆 THEOREM: Two applications of $S$ yield charge conjugation:
    $S^2(p, q) = (-p, -q) = -Q$. -/
theorem emExchangeTwist_sq (Q : Charge56) :
    emExchangeTwist (emExchangeTwist Q) =
      { p := fun i => - Q.p i, q := fun i => - Q.q i } := by
  dsimp [emExchangeTwist]
  rw [dualityTwist_add]
  have h_pi : π / 2 + π / 2 = π := by ring
  rw [h_pi]
  apply charge56_ext
  · ext i
    dsimp [dualityTwist]
    simp [Real.cos_pi, Real.sin_pi]
  · ext i
    dsimp [dualityTwist]
    simp [Real.cos_pi, Real.sin_pi]

/-- 🏆 THEOREM: Four applications of $S$ recover the identity: $S^4(Q) = Q$. -/
theorem emExchangeTwist_pow_four (Q : Charge56) :
    emExchangeTwist (emExchangeTwist (emExchangeTwist (emExchangeTwist Q))) = Q := by
  dsimp [emExchangeTwist]
  rw [dualityTwist_add, dualityTwist_add, dualityTwist_add]
  have h_2pi : π / 2 + π / 2 + π / 2 + π / 2 = 2 * π := by ring
  rw [h_2pi]
  apply charge56_ext
  · ext i
    dsimp [dualityTwist]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  · ext i
    dsimp [dualityTwist]
    simp [Real.cos_two_pi, Real.sin_two_pi]

/-- Discrete $\mathbb{Z}_4$ electric-magnetic exchange on the integral DSZ lattice: $S(p, q) = (q, -p)$. -/
def latticeEMExchange (Q : LatticeCharge56) : LatticeCharge56 where
  p := Q.q
  q := - Q.p

/-- 🏆 THEOREM: Invariance of the discrete DSZ pairing under lattice electric-magnetic exchange. -/
theorem dszPairing_latticeEMExchange (Q₁ Q₂ : LatticeCharge56) :
    dszPairing (latticeEMExchange Q₁) (latticeEMExchange Q₂) = dszPairing Q₁ Q₂ := by
  dsimp [dszPairing, latticeEMExchange, dotProduct]
  have h_sum : (∑ i : Dim28, Q₁.q i * (- Q₂.p i) -
                ∑ i : Dim28, (- Q₁.p i) * Q₂.q i) =
               ∑ i : Dim28, (Q₁.p i * Q₂.q i - Q₁.q i * Q₂.p i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h_sum, Finset.sum_sub_distrib]

/-- 🏆 THEOREM: $S^2 = -\mathbb{I}$ on the integral DSZ lattice. -/
theorem latticeEMExchange_sq (Q : LatticeCharge56) :
    latticeEMExchange (latticeEMExchange Q) = - Q := by
  ext i <;> rfl

/-- 🏆 THEOREM: $S^4 = \mathbb{I}$ on the integral DSZ lattice. -/
theorem latticeEMExchange_pow_four (Q : LatticeCharge56) :
    latticeEMExchange (latticeEMExchange (latticeEMExchange (latticeEMExchange Q))) = Q := by
  ext i
  · dsimp [latticeEMExchange]
    simp
  · dsimp [latticeEMExchange]
    simp

/-- 🏆 THEOREM: Lattice electric-magnetic exchange intertwines with continuous $S = T_{\pi/2}$. -/
theorem toRealCharge56_latticeEMExchange (Q : LatticeCharge56) :
    toRealCharge56 (latticeEMExchange Q) = emExchangeTwist (toRealCharge56 Q) := by
  rw [emExchangeTwist_apply]
  apply charge56_ext
  · rfl
  · ext i
    dsimp [toRealCharge56, latticeEMExchange]
    push_cast
    rfl

/-- Discrete parabolic axion monodromy twist by $k \in \mathbb{Z}$ around moduli singularities:
    $T_k(p, q) = (p + k q, q)$. -/
def latticeAxionTwist (k : ℤ) (Q : LatticeCharge56) : LatticeCharge56 where
  p := fun i => Q.p i + k * Q.q i
  q := Q.q

/-- Continuous parabolic axion monodromy twist by $c \in \mathbb{R}$:
    $T_c(p, q) = (p + c q, q)$. -/
def axionTwist (c : ℝ) (Q : Charge56) : Charge56 where
  p := fun i => Q.p i + c * Q.q i
  q := Q.q

/-- 🏆 THEOREM: Invariance of the discrete DSZ pairing under integral axion monodromy shifts. -/
theorem dszPairing_latticeAxionTwist (k : ℤ) (Q₁ Q₂ : LatticeCharge56) :
    dszPairing (latticeAxionTwist k Q₁) (latticeAxionTwist k Q₂) = dszPairing Q₁ Q₂ := by
  dsimp [dszPairing, latticeAxionTwist, dotProduct]
  have h_sum : (∑ i : Dim28, (Q₁.p i + k * Q₁.q i) * Q₂.q i -
                ∑ i : Dim28, Q₁.q i * (Q₂.p i + k * Q₂.q i)) =
               ∑ i : Dim28, (Q₁.p i * Q₂.q i - Q₁.q i * Q₂.p i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h_sum, Finset.sum_sub_distrib]

/-- 🏆 THEOREM: Group composition of lattice axion monodromy twists: $T_k \circ T_m = T_{k+m}$. -/
theorem latticeAxionTwist_add (k m : ℤ) (Q : LatticeCharge56) :
    latticeAxionTwist k (latticeAxionTwist m Q) = latticeAxionTwist (k + m) Q := by
  ext i
  · dsimp [latticeAxionTwist]
    ring
  · rfl

/-- 🏆 THEOREM: Axion twist by 0 is the identity. -/
theorem latticeAxionTwist_zero (Q : LatticeCharge56) :
    latticeAxionTwist 0 Q = Q := by
  ext i
  · dsimp [latticeAxionTwist]
    ring
  · rfl

/-- 🏆 THEOREM: Symplectic invariance of continuous axion twists under $\Omega_{56}$. -/
theorem omega56_axionTwist (c : ℝ) (Q₁ Q₂ : Charge56) :
    omega56 (axionTwist c Q₁) (axionTwist c Q₂) = omega56 Q₁ Q₂ := by
  dsimp [omega56, axionTwist, dotProduct]
  have h_sum : (∑ i : Dim28, (Q₁.p i + c * Q₁.q i) * Q₂.q i -
                ∑ i : Dim28, Q₁.q i * (Q₂.p i + c * Q₂.q i)) =
               ∑ i : Dim28, (Q₁.p i * Q₂.q i - Q₁.q i * Q₂.p i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h_sum, Finset.sum_sub_distrib]

/-- 🏆 THEOREM: The fundamental modular relation $(S \circ T)^3 = \mathbb{I}$ of $\mathrm{SL}(2, \mathbb{Z})$
    holds identically on the discrete 56D DSZ quantization lattice $\Gamma_{\mathrm{DSZ}}$. -/
theorem modular_relation_st_cubed (Q : LatticeCharge56) :
    let ST := fun X => latticeEMExchange (latticeAxionTwist 1 X)
    ST (ST (ST Q)) = Q := by
  intro ST
  dsimp [ST, latticeEMExchange, latticeAxionTwist]
  ext i
  · dsimp
    ring
  · dsimp
    ring

/-- 🏆 MASTER SYNTHESIS: 56D Sp(56, ℝ) DSZ Lattice Quantization & Non-Local Monodromy Twists. -/
theorem certified_sp56_dsz_nonlocal_twist_synthesis
    (Q₁ Q₂ : LatticeCharge56) (theta : ℝ) (R : Charge56) (k : ℤ) :
    (dszPairing Q₁ Q₂ = - dszPairing Q₂ Q₁) ∧
    (dszPairing Q₁ Q₁ = 0) ∧
    (omega56 (toRealCharge56 Q₁) (toRealCharge56 Q₂) = (dszPairing Q₁ Q₂ : ℝ)) ∧
    (omega56 (dualityTwist theta R) (dualityTwist theta R) = omega56 R R) ∧
    (dualityTwist 0 R = R) ∧
    (latticeEMExchange (latticeEMExchange Q₁) = - Q₁) ∧
    (latticeEMExchange (latticeEMExchange (latticeEMExchange (latticeEMExchange Q₁))) = Q₁) ∧
    (dszPairing (latticeEMExchange Q₁) (latticeEMExchange Q₂) = dszPairing Q₁ Q₂) ∧
    (dszPairing (latticeAxionTwist k Q₁) (latticeAxionTwist k Q₂) = dszPairing Q₁ Q₂) ∧
    (let ST := fun X => latticeEMExchange (latticeAxionTwist 1 X); ST (ST (ST Q₁)) = Q₁) :=
  ⟨dszPairing_skew Q₁ Q₂,
   dszPairing_self_zero Q₁,
   omega56_eq_dszPairing Q₁ Q₂,
   dualityTwist_preserves_omega56 theta R R,
   dualityTwist_zero R,
   latticeEMExchange_sq Q₁,
   latticeEMExchange_pow_four Q₁,
   dszPairing_latticeEMExchange Q₁ Q₂,
   dszPairing_latticeAxionTwist k Q₁ Q₂,
   modular_relation_st_cubed Q₁⟩

end

end InfoGeometry.Canonical.Sp56DSZTwist
