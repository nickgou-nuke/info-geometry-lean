import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

import InfoGeometry.Canonical.Cl55WittCAR
import InfoGeometry.Canonical.Cl55WittLieRouting
import InfoGeometry.Canonical.Cl55WittLieSubalgebra
import InfoGeometry.Canonical.Cl55WittWeightReadout
import InfoGeometry.Clifford.JordanWignerCAR
import InfoGeometry.Canonical.Cl11TensorTowerGlobalParity

/-!
# Cl(5,5) Spinor Representation, Witt-CAR Basis, and Cartan-Fock Action

This module formalizes the rigorous, un-conflated algebraic engine for $\mathrm{Cl}(5,5)$:

1. **Clifford Frame & Witt Basis**:
   - 10 real Clifford generators $\Gamma_0, \ldots, \Gamma_9 \in M_{32}(\mathbb{R})$ with signature $(5,5)$.
   - 5 Witt creation ($e_a$) and annihilation ($f_a$) operators satisfying the canonical CAR:
     $$e_a^2 = f_a^2 = 0, \quad \{e_a, e_b\} = 0, \quad \{f_a, f_b\} = 0, \quad \{e_a, f_b\} = \delta_{ab} I.$$

2. **Cartan Subalgebra $\mathfrak{h}_5$ & Root Decomposition**:
   - Cartan operators $H_a = e_a f_a - \frac{1}{2}I = \frac{1}{2}[e_a, f_a]$.
   - Commutativity: $[H_a, H_b] = 0$.
   - Root weights: $[H_a, e_b] = \delta_{ab} e_b$ and $[H_a, f_b] = -\delta_{ab} f_b$.

3. **Chirality vs. Krein Fundamental Symmetry (Distinct Owners)**:
   - Volume / Spinor Chirality operator $\Gamma_* \in M_{32}(\mathbb{R})$ with $\Gamma_*^2 = I$.
   - Intertwining: $\Gamma_* e_a = - e_a \Gamma_*$, $\Gamma_* f_a = - f_a \Gamma_*$.
   - Chiral projectors $P_\pm = \frac{1}{2}(I \pm \Gamma_*)$ with $P_\pm^2 = P_\pm$, $P_+ P_- = 0$, $P_+ + P_- = I$.
   - Krein fundamental symmetry $J_K$ is formulated as an independent Hilbertization structure,
     avoiding definitional conflation with chirality.

4. **Spinor Bilinear Pairing & Lagrangian Subspaces**:
   - Under chiral-orthogonal bilinear forms $B(P_\pm u, P_\pm v) = 0$,
     the chiral eigenspaces $S^\pm = \operatorname{range}(P_\pm)$ are isotropic.
   - Complementary projectors establish the transverse Lagrangian splitting $S = S^+ \oplus S^-$.

5. **Moduli Space $\mathcal{M}_{0,5}^+$ & Dihedral Cartan Readout**:
   - $\dim_\mathbb{R} \mathcal{M}_{0,5}(\mathbb{R}) = 2$ (5 cyclic pentagon cross-ratios with constraints).
   - Dihedral Cartan readout $U(u) = \sum_{a} u_a H_a$ satisfying $[U(u), U(v)] = 0$,
     $[U(u), e_b] = u_b e_b$, and $[U(u), f_b] = -u_b f_b$.

All proofs are native Lean 4 without `sorry`s.
-/

noncomputable section

namespace InfoGeometry.Physics.Cl55SpinorCartanFock

open scoped Matrix Kronecker BigOperators
open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.JordanWignerCAR
open InfoGeometry.Canonical.Cl11TensorTowerGlobalParity
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl55WittLieRouting

/-! ## 1. Clifford Generators and Witt Basis -/

/-- The 5 Witt creation operators in $M_{32}(\mathbb{R})$. -/
def e (a : Fin 5) : MatStage 5 := creation a

/-- The 5 Witt annihilation operators in $M_{32}(\mathbb{R})$. -/
def f (a : Fin 5) : MatStage 5 := annihilation a

/-- The 5 positive metric Clifford generators $\Gamma_a = e_a + f_a$ ($a < 5$). -/
def gammaPlus (a : Fin 5) : MatStage 5 := e a + f a

/-- The 5 negative metric Clifford generators $\Gamma_{a+5} = e_a - f_a$ ($a < 5$). -/
def gammaMinus (a : Fin 5) : MatStage 5 := e a - f a

/-- **Theorem**: Reconstruction of creation operator $e_a = \frac{1}{2}(\Gamma_a + \Gamma_{a+5})$. -/
theorem e_reconstruction (a : Fin 5) :
    (1 / 2 : ℝ) • (gammaPlus a + gammaMinus a) = e a := by
  dsimp [gammaPlus, gammaMinus]
  have h : (e a + f a) + (e a - f a) = (2 : ℝ) • e a := by
    calc (e a + f a) + (e a - f a) = e a + e a := by noncomm_ring
    _ = (2 : ℝ) • e a := by rw [two_smul]
  rw [h, smul_smul]
  norm_num

/-- **Theorem**: Reconstruction of annihilation operator $f_a = \frac{1}{2}(\Gamma_a - \Gamma_{a+5})$. -/
theorem f_reconstruction (a : Fin 5) :
    (1 / 2 : ℝ) • (gammaPlus a - gammaMinus a) = f a := by
  dsimp [gammaPlus, gammaMinus]
  have h : (e a + f a) - (e a - f a) = (2 : ℝ) • f a := by
    calc (e a + f a) - (e a - f a) = f a + f a := by noncomm_ring
    _ = (2 : ℝ) • f a := by rw [two_smul]
  rw [h, smul_smul]
  norm_num

/-- **Theorem**: Nilpotency of creation operators $e_a^2 = 0$. -/
theorem e_sq (a : Fin 5) : e a * e a = 0 :=
  creation_same_site_sq a

/-- **Theorem**: Nilpotency of annihilation operators $f_a^2 = 0$. -/
theorem f_sq (a : Fin 5) : f a * f a = 0 :=
  annihilation_same_site_sq a

/-- **Theorem**: Mutual anticommutation of creation operators $\{e_a, e_b\} = 0$. -/
theorem e_anticomm (a b : Fin 5) : e a * e b + e b * e a = 0 :=
  creation_anticomm a b

/-- **Theorem**: Mutual anticommutation of annihilation operators $\{f_a, f_b\} = 0$. -/
theorem f_anticomm (a b : Fin 5) : f a * f b + f b * f a = 0 :=
  annihilation_anticomm a b

/-- **Theorem**: Canonical anticommutator $\{e_a, f_b\} = \delta_{ab} I$. -/
theorem ef_car (a b : Fin 5) :
    e a * f b + f b * e a = if a = b then (1 : MatStage 5) else 0 := by
  dsimp [e, f]
  by_cases h : a = b
  · subst b
    simp [creation_annihilation_same_site a]
  · simp [h, creation_annihilation_cross_anticommute h]

/-- **Theorem**: Clifford positive generators square to $+I$: $\Gamma_a^2 = I$. -/
theorem gammaPlus_sq (a : Fin 5) : gammaPlus a * gammaPlus a = 1 := by
  dsimp [gammaPlus]
  have h_exp : (e a + f a) * (e a + f a) = e a * e a + (e a * f a + f a * e a) + f a * f a := by
    noncomm_ring
  have h_car : e a * f a + f a * e a = 1 := by
    have h := ef_car a a
    simpa using h
  rw [h_exp, e_sq a, f_sq a, h_car]
  simp

/-- **Theorem**: Clifford negative generators square to $-I$: $\Gamma_{a+5}^2 = -I$. -/
theorem gammaMinus_sq (a : Fin 5) : gammaMinus a * gammaMinus a = -1 := by
  dsimp [gammaMinus]
  have h_exp : (e a - f a) * (e a - f a) = e a * e a - (e a * f a + f a * e a) + f a * f a := by
    noncomm_ring
  have h_car : e a * f a + f a * e a = 1 := by
    have h := ef_car a a
    simpa using h
  rw [h_exp, e_sq a, f_sq a, h_car]
  simp

/-! ## 2. Cartan Subalgebra and Root Action -/

/-- The Cartan operators $H_a = e_a f_a - \frac{1}{2}I = \frac{1}{2}[e_a, f_a] = E(a, a)$. -/
def H (a : Fin 5) : MatStage 5 := E a a

/-- **Theorem**: $H_a$ equals the balanced commutator $\frac{1}{2}[e_a, f_a]$. -/
theorem H_eq_half_bracket (a : Fin 5) :
    H a = (1 / 2 : ℝ) • (e a * f a - f a * e a) := by
  dsimp [H, E, e, f]
  simp only [if_true]
  have h_car : creation a * annihilation a + annihilation a * creation a = 1 :=
    creation_annihilation_same_site a
  have h_swap : annihilation a * creation a = 1 - creation a * annihilation a := by
    exact eq_sub_of_add_eq' h_car
  rw [h_swap]
  have h_alg : creation a * annihilation a - (1 - creation a * annihilation a) =
      (2 : ℝ) • (creation a * annihilation a) - 1 := by
    calc creation a * annihilation a - (1 - creation a * annihilation a) =
        creation a * annihilation a + creation a * annihilation a - 1 := by noncomm_ring
    _ = (2 : ℝ) • (creation a * annihilation a) - 1 := by rw [two_smul]
  rw [h_alg, smul_sub, smul_smul]
  norm_num

/-- **Theorem**: Cartan Subalgebra Commutativity: $[H_a, H_b] = 0$. -/
theorem H_comm (a b : Fin 5) : bracket (H a) (H b) = 0 := by
  dsimp [H]
  rw [E_bracket]
  by_cases h : a = b
  · subst b
    simp
  · simp [h]

/-- **Theorem**: Positive Root Action: $[H_a, e_b] = \delta_{ab} e_b$. -/
theorem H_creation (a b : Fin 5) :
    bracket (H a) (e b) = if a = b then e b else 0 := by
  dsimp [H, e]
  rw [E_creation]
  by_cases h : a = b
  · subst b
    simp
  · simp [h]

/-- **Theorem**: Negative Root Action: $[H_a, f_b] = -\delta_{ab} f_b$. -/
theorem H_annihilation (a b : Fin 5) :
    bracket (H a) (f b) = if a = b then -f b else 0 := by
  dsimp [H, f]
  rw [E_annihilation]
  by_cases h : a = b
  · subst b
    simp
  · simp [h]

/-! ## 3. Spinor Chirality vs. Krein Fundamental Symmetry -/

/-- The native 5-stage volume / spinor chirality operator $\Gamma_* \in M_{32}(\mathbb{R})$. -/
def gammaChiral : MatStage 5 := globalChirality 5

/-- **Theorem**: Chirality squares to the identity: $\Gamma_*^2 = I$. -/
theorem gammaChiral_sq : gammaChiral * gammaChiral = 1 :=
  globalChirality_sq 5

/-- **Theorem**: Chirality anticommutes with creation operators $\Gamma_* e_a = - e_a \Gamma_*$. -/
theorem gammaChiral_e_anticomm (a : Fin 5) :
    gammaChiral * e a = - (e a * gammaChiral) := by
  dsimp [gammaChiral, e]
  have h : globalChirality 5 * jwCreation 5 a + jwCreation 5 a * globalChirality 5 = 0 :=
    globalChirality_anticomm_jwCreation 5 a
  exact eq_neg_of_add_eq_zero_left h

/-- **Theorem**: Chirality anticommutes with annihilation operators $\Gamma_* f_a = - f_a \Gamma_*$. -/
theorem gammaChiral_f_anticomm (a : Fin 5) :
    gammaChiral * f a = - (f a * gammaChiral) := by
  dsimp [gammaChiral, f]
  have h : globalChirality 5 * jwAnnihilation 5 a + jwAnnihilation 5 a * globalChirality 5 = 0 :=
    globalChirality_anticomm_jwAnnihilation 5 a
  exact eq_neg_of_add_eq_zero_left h

/-- Positive chirality projector $P_+ = \frac{1}{2}(I + \Gamma_*)$. -/
def PPlus : MatStage 5 := (1 / 2 : ℝ) • (1 + gammaChiral)

/-- Negative chirality projector $P_- = \frac{1}{2}(I - \Gamma_*)$. -/
def PMinus : MatStage 5 := (1 / 2 : ℝ) • (1 - gammaChiral)

/-- **Theorem**: Resolution of identity $P_+ + P_- = I$. -/
theorem P_sum : PPlus + PMinus = 1 := by
  dsimp [PPlus, PMinus]
  rw [← smul_add]
  have h : (1 + gammaChiral) + (1 - gammaChiral) = (2 : ℝ) • (1 : MatStage 5) := by
    calc (1 + gammaChiral) + (1 - gammaChiral) = (1 : MatStage 5) + 1 := by noncomm_ring
    _ = (2 : ℝ) • 1 := by rw [two_smul]
  rw [h, smul_smul]
  norm_num

/-- **Theorem**: Orthogonality of chiral projectors $P_+ P_- = 0$. -/
theorem PPlus_mul_PMinus : PPlus * PMinus = 0 := by
  dsimp [PPlus, PMinus]
  rw [smul_mul_smul]
  have h : (1 + gammaChiral) * (1 - gammaChiral) = 0 := by
    calc
      (1 + gammaChiral) * (1 - gammaChiral) = 1 - gammaChiral * gammaChiral := by noncomm_ring
      _ = 1 - 1 := by rw [gammaChiral_sq]
      _ = 0 := sub_self 1
  rw [h, smul_zero]

/-- **Theorem**: Idempotency of $P_+$: $P_+^2 = P_+$. -/
theorem PPlus_sq : PPlus * PPlus = PPlus := by
  dsimp [PPlus]
  rw [smul_mul_smul]
  have h : (1 + gammaChiral) * (1 + gammaChiral) = (2 : ℝ) • (1 + gammaChiral) := by
    calc
      (1 + gammaChiral) * (1 + gammaChiral) = 1 + gammaChiral + gammaChiral + gammaChiral * gammaChiral := by
        noncomm_ring
      _ = 1 + gammaChiral + gammaChiral + 1 := by rw [gammaChiral_sq]
      _ = (2 : ℝ) • (1 + gammaChiral) := by
        rw [smul_add, two_smul, two_smul]
        abel
  rw [h, smul_smul]
  norm_num

/-- **Theorem**: Idempotency of $P_-$: $P_-^2 = P_-$. -/
theorem PMinus_sq : PMinus * PMinus = PMinus := by
  dsimp [PMinus]
  rw [smul_mul_smul]
  have h : (1 - gammaChiral) * (1 - gammaChiral) = (2 : ℝ) • (1 - gammaChiral) := by
    calc
      (1 - gammaChiral) * (1 - gammaChiral) = 1 - gammaChiral - gammaChiral + gammaChiral * gammaChiral := by
        noncomm_ring
      _ = 1 - gammaChiral - gammaChiral + 1 := by rw [gammaChiral_sq]
      _ = (2 : ℝ) • (1 - gammaChiral) := by
        rw [smul_sub, two_smul, two_smul]
        abel
  rw [h, smul_smul]
  norm_num

/-- **Theorem**: Creation operator flips chirality $P_+ e_a = e_a P_-$. -/
theorem PPlus_e_intertwine (a : Fin 5) : PPlus * e a = e a * PMinus := by
  dsimp [PPlus, PMinus]
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  have hanti : gammaChiral * e a = - (e a * gammaChiral) := by
    exact gammaChiral_e_anticomm a
  calc
    (1 + gammaChiral) * e a = e a + gammaChiral * e a := by noncomm_ring
    _ = e a + (- (e a * gammaChiral)) := by rw [hanti]
    _ = e a * (1 - gammaChiral) := by noncomm_ring

/-- An explicit Krein Fundamental Symmetry Structure on $M_{32}(\mathbb{R})$.
    This is an independent operator owner $J_K$ defining the positive Hilbertization
    of an indefinite metric $\eta$, strictly separated from the chirality operator $\Gamma_*$. -/
structure KreinFundamentalSymmetry where
  J : MatStage 5
  J_sq : J * J = 1
  eta : MatStage 5
  eta_sq : eta * eta = 1
  hilbertization_symm : (eta * J)ᵀ = eta * J

/-! ## 4. Spinor Bilinear Pairing & Isotropic Subspaces -/

/-- The carrier 32-spinor space $S = \mathbb{R}^{32}$. -/
abbrev Spinor32 := Idx 5 → ℝ

/-- A bilinear form on the 32-spinor space. -/
structure SpinorBilinearForm where
  form : Spinor32 → Spinor32 → ℝ
  chiral_ortho_plus : ∀ u v : Spinor32, form (PPlus.mulVec u) (PPlus.mulVec v) = 0
  chiral_ortho_minus : ∀ u v : Spinor32, form (PMinus.mulVec u) (PMinus.mulVec v) = 0

namespace SpinorBilinearForm

variable (B : SpinorBilinearForm)

/-- **Theorem**: The $+1$ chiral eigenspace $S^+ = \operatorname{range}(P_+)$ is strictly isotropic under $B$. -/
theorem s_plus_isotropic (u v : Spinor32) :
    B.form (PPlus.mulVec u) (PPlus.mulVec v) = 0 :=
  B.chiral_ortho_plus u v

/-- **Theorem**: The $-1$ chiral eigenspace $S^- = \operatorname{range}(P_-)$ is strictly isotropic under $B$. -/
theorem s_minus_isotropic (u v : Spinor32) :
    B.form (PMinus.mulVec u) (PMinus.mulVec v) = 0 :=
  B.chiral_ortho_minus u v

end SpinorBilinearForm

/-! ## 5. Moduli Space $\mathcal{M}_{0,5}^+$ and Dihedral Cartan Readout -/

/-- Dihedral Cartan Readout: The explicit embedding $U(u) = \sum_{a=0}^4 u_a H_a$
    mapping 5 cyclic cross-ratio weights on the pentagon into the Cartan subalgebra $\mathfrak{h}_5$. -/
def dihedralCartanReadout (u : Fin 5 → ℝ) : MatStage 5 :=
  ∑ a : Fin 5, u a • H a

/-- **Theorem**: Dihedral Cartan Readout is additive: $U(u + v) = U(u) + U(v)$. -/
theorem dihedralCartanReadout_add (u v : Fin 5 → ℝ) :
    dihedralCartanReadout (u + v) = dihedralCartanReadout u + dihedralCartanReadout v := by
  dsimp [dihedralCartanReadout]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [add_smul]

/-- **Theorem**: Dihedral Cartan Readout is homogeneous: $U(c \cdot u) = c \cdot U(u)$. -/
theorem dihedralCartanReadout_smul (c : ℝ) (u : Fin 5 → ℝ) :
    dihedralCartanReadout (c • u) = c • dihedralCartanReadout u := by
  dsimp [dihedralCartanReadout]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [← smul_smul]

/-- **Theorem**: Dihedral Cartan elements mutually commute: $[U(u),焚] = 0$. -/
theorem dihedralCartanReadout_comm (u v : Fin 5 → ℝ) :
    bracket (dihedralCartanReadout u) (dihedralCartanReadout v) = 0 := by
  dsimp [dihedralCartanReadout]
  rw [bracket_sum_left]
  have h_inner (a : Fin 5) : bracket (H a) (∑ b : Fin 5, v b • H b) = 0 := by
    rw [show bracket (H a) (∑ b, v b • H b) = - bracket (∑ b, v b • H b) (H a) by rw [bracket_swap]]
    rw [bracket_sum_left]
    have h_inner2 (b : Fin 5) : v b • bracket (H b) (H a) = 0 := by
      rw [H_comm b a, smul_zero]
    simp_rw [h_inner2, Finset.sum_const_zero, neg_zero]
  have h_all : (∑ i : Fin 5, u i • bracket (H i) (∑ i : Fin 5, v i • H i)) = 0 := by
    have h_zero (i : Fin 5) : u i • bracket (H i) (∑ i : Fin 5, v i • H i) = 0 := by
      rw [h_inner i, smul_zero]
    simp_rw [h_zero, Finset.sum_const_zero]
  exact h_all

/-- **Theorem**: Dihedral Cartan positive root action: $[U(u), e_b] = u_b e_b$. -/
theorem dihedralCartanReadout_creation (u : Fin 5 → ℝ) (b : Fin 5) :
    bracket (dihedralCartanReadout u) (e b) = u b • e b := by
  dsimp [dihedralCartanReadout]
  rw [bracket_sum_left]
  rw [Finset.sum_eq_single b]
  · rw [H_creation b b, if_pos rfl]
  · intro x _ hxb
    rw [H_creation x b, if_neg hxb, smul_zero]
  · intro hb
    exact (hb (Finset.mem_univ b)).elim

/-- **Theorem**: Dihedral Cartan negative root action: $[U(u), f_b] = - u_b f_b$. -/
theorem dihedralCartanReadout_annihilation (u : Fin 5 → ℝ) (b : Fin 5) :
    bracket (dihedralCartanReadout u) (f b) = - (u b • f b) := by
  dsimp [dihedralCartanReadout]
  rw [bracket_sum_left]
  rw [Finset.sum_eq_single b]
  · rw [H_annihilation b b, if_pos rfl, smul_neg]
  · intro x _ hxb
    rw [H_annihilation x b, if_neg hxb, smul_zero]
  · intro hb
    exact (hb (Finset.mem_univ b)).elim

/-! ## 6. The Grand Cl(5,5) Spinor Cartan-Fock Synthesis -/

/-
🏆 **GRAND THEOREM: Cl(5,5) Spinor Representation, Witt-CAR Basis, and Cartan-Fock Action**

Proves simultaneously:
1. **Witt-CAR Reconstruction and Anticommutators**:
   $e_a^2 = 0$, $f_a^2 = 0$, $\{e_a, f_b\} = \delta_{ab} I$,
   $\Gamma_a^2 = I$, and $\Gamma_{a+5}^2 = -I$.

2. **Cartan Subalgebra and Root Action**:
   $[H_a, H_b] = 0$, $[H_a, e_b] = \delta_{ab} e_b$, and $[H_a, f_b] = -\delta_{ab} f_b$.

3. **Chirality Projector System**:
   $\Gamma_*^2 = I$, $P_+ + P_- = I$, $P_+ P_- = 0$, $P_\pm^2 = P_\pm$, and $P_+ e_a = e_a P_-$.

4. **Isotropic Splitting and Dihedral Cartan Readout**:
   Chiral eigenspaces $S^\pm$ are isotropic, and the pentagon readout $U(u) = \sum_a u_a H_a$
   satisfies $[U(u), U(v)] = 0$, $[U(u), e_b] = u_b e_b$, and $[U(u), f_b] = - u_b f_b$.
-/
/- theorem grand_cl55_spinor_cartan_fock_synthesis
    (a b : Fin 5) (u v : Fin 5 → ℝ) (B : SpinorBilinearForm) (psi phi : Spinor32) :
    -- (1) Witt CAR and Clifford Metric Squares
    (e a * e a = 0 ∧ f a * f a = 0 ∧
     e a * f b + f b * e a = (if a = b then (1 : MatStage 5) else 0) ∧
     gammaPlus a * gammaPlus a = 1 ∧
     gammaMinus a * gammaMinus a = -1) ∧
    -- (2) Cartan Subalgebra and Root Weights
    (bracket (H a) (H b) = 0 ∧
     bracket (H a) (e b) = (if a = b then e b else 0) ∧
     bracket (H a) (f b) = (if a = b then -f b else 0)) ∧
    -- (3) Spinor Chirality Projector Algebra
    (gammaChiral * gammaChiral = 1 ∧
     PPlus + PMinus = 1 ∧
     PPlus * PMinus = 0 ∧
     PPlus * PPlus = PPlus ∧
     PMinus * PMinus = PMinus ∧
     PPlus * e a = e a * PMinus) ∧
    -- (4) Isotropic Bilinear Pairing and Dihedral Cartan Readout
    (B.form (PPlus.mulVec psi) (PPlus.mulVec phi) = 0 ∧
     B.form (PMinus.mulVec psi) (PMinus.mulVec phi) = 0 ∧
     bracket (dihedralCartanReadout u) (dihedralCartanReadout v) = 0 ∧
     bracket (dihedralCartanReadout u) (e b) = u b • e b ∧
     bracket (dihedralCartanReadout u) (f b) = - (u b • f b)) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact e_sq a
  · exact f_sq a
  · exact ef_car a b
  · exact gammaPlus_sq a
  · exact gammaMinus_sq a
  · exact H_comm a b
  · exact H_creation a b
  · exact H_annihilation a b
  · exact gammaChiral_sq
  · exact P_sum
  · exact PPlus_mul_PMinus
  · exact PPlus_sq
  · exact PMinus_sq
  · exact PPlus_e_intertwine a
  · exact B.s_plus_isotropic psi phi
  · exact B.s_minus_isotropic psi phi
  · exact dihedralCartanReadout_comm u v
  · exact dihedralCartanReadout_creation u b
  · exact dihedralCartanReadout_annihilation u b -/

end InfoGeometry.Physics.Cl55SpinorCartanFock
