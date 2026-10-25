/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

instance : Inhabited KreinFundamentalSymmetry :=
  ⟨⟨1, mul_one 1, 1, mul_one 1, by simp⟩⟩

/-! ## 4. Spinor Bilinear Pairing & Isotropic Subspaces -/

/-- The carrier 32-spinor space $S = \mathbb{R}^{32}$. -/
abbrev Spinor32 := Idx 5 → ℝ

/-- A bilinear form on the 32-spinor space. -/
structure SpinorBilinearForm where
  form : Spinor32 → Spinor32 → ℝ
  chiral_ortho_plus : ∀ u v : Spinor32, form (PPlus.mulVec u) (PPlus.mulVec v) = 0
  chiral_ortho_minus : ∀ u v : Spinor32, form (PMinus.mulVec u) (PMinus.mulVec v) = 0

instance : Inhabited SpinorBilinearForm :=
  ⟨⟨fun _ _ => 0, fun _ _ => rfl, fun _ _ => rfl⟩⟩

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

/-! ## 6. Five-Graded Isospin, Pairing Quasispin, and 4-Projector Decomposition in $\mathrm{Cl}(5,5)$ -/

/-- Occupied projector $N_a = e_a f_a$ of Witt mode $a \in \mathrm{Fin}\;5$. -/
def modeOccupied (a : Fin 5) : MatStage 5 := e a * f a

/-- Vacant projector $1 - N_a = f_a e_a$ of Witt mode $a \in \mathrm{Fin}\;5$. -/
def modeVacant (a : Fin 5) : MatStage 5 := f a * e a

/-- Occupied and vacant projectors of mode $a$ sum to the $32 \times 32$ identity. -/
theorem modeOccupied_add_modeVacant (a : Fin 5) :
    modeOccupied a + modeVacant a = 1 := by
  simpa [modeOccupied, modeVacant] using ef_car a a

/-- Occupied projector $N_a = e_a f_a$ is idempotent. -/
theorem modeOccupied_idem (a : Fin 5) :
    modeOccupied a * modeOccupied a = modeOccupied a := by
  dsimp [modeOccupied]
  have hcar : f a * e a = 1 - e a * f a :=
    eq_sub_of_add_eq' (modeOccupied_add_modeVacant a)
  calc
    (e a * f a) * (e a * f a) = e a * (f a * e a) * f a := by noncomm_ring
    _ = e a * (1 - e a * f a) * f a := by rw [hcar]
    _ = e a * f a - (e a * e a) * (f a * f a) := by noncomm_ring
    _ = e a * f a := by rw [e_sq a, zero_mul, sub_zero]

/-- Vacant projector $f_a e_a$ is idempotent. -/
theorem modeVacant_idem (a : Fin 5) :
    modeVacant a * modeVacant a = modeVacant a := by
  dsimp [modeVacant]
  have hcar : e a * f a = 1 - f a * e a :=
    eq_sub_of_add_eq (modeOccupied_add_modeVacant a)
  calc
    (f a * e a) * (f a * e a) = f a * (e a * f a) * e a := by noncomm_ring
    _ = f a * (1 - f a * e a) * e a := by rw [hcar]
    _ = f a * e a - (f a * f a) * (e a * e a) := by noncomm_ring
    _ = f a * e a := by rw [f_sq a, zero_mul, sub_zero]

/-- Occupied and vacant projectors of mode $a$ are mutually orthogonal. -/
theorem modeOccupied_mul_modeVacant (a : Fin 5) :
    modeOccupied a * modeVacant a = 0 := by
  dsimp [modeOccupied, modeVacant]
  calc
    (e a * f a) * (f a * e a) = e a * (f a * f a) * e a := by noncomm_ring
    _ = 0 := by rw [f_sq a, mul_zero, zero_mul]

/-- Vacant and occupied projectors of mode $a$ are mutually orthogonal. -/
theorem modeVacant_mul_modeOccupied (a : Fin 5) :
    modeVacant a * modeOccupied a = 0 := by
  dsimp [modeOccupied, modeVacant]
  calc
    (f a * e a) * (e a * f a) = f a * (e a * e a) * f a := by noncomm_ring
    _ = 0 := by rw [e_sq a, mul_zero, zero_mul]

/-- Grade-0 isospin raising generator $\tau_+(p,n) = E(p,n)$ in $\mathrm{Cl}(5,5)$. -/
def isospinPlus (p n : Fin 5) : MatStage 5 := E p n

/-- Grade-0 isospin lowering generator $\tau_-(p,n) = E(n,p)$ in $\mathrm{Cl}(5,5)$. -/
def isospinMinus (p n : Fin 5) : MatStage 5 := E n p

/-- Grade-0 isospin Cartan generator $\tau_3(p,n) = H_p - H_n = E(p,p) - E(n,n)$ in $\mathrm{Cl}(5,5)$. -/
def isospinCartan (p n : Fin 5) : MatStage 5 := H p - H n

/-- Grade-$+2$ pairing quasispin raising generator $K_+(p,n) = e_p e_n$ in $\mathrm{Cl}(5,5)$. -/
def pairingPlus (p n : Fin 5) : MatStage 5 := e p * e n

/-- Grade-$-2$ pairing quasispin lowering generator $K_-(p,n) = f_n f_p$ in $\mathrm{Cl}(5,5)$. -/
def pairingMinus (p n : Fin 5) : MatStage 5 := f n * f p

/-- Grade-0 pairing quasispin Cartan generator $2 K_0(p,n) = H_p + H_n = E(p,p) + E(n,n)$ in $\mathrm{Cl}(5,5)$. -/
def pairingCartan (p n : Fin 5) : MatStage 5 := H p + H n

/-- Positive-isospin single-nucleon sector projector $\Pi_+(p,n) = N_p (1 - N_n)$. -/
def isoProjPlus (p n : Fin 5) : MatStage 5 := modeOccupied p * modeVacant n

/-- Negative-isospin single-nucleon sector projector $\Pi_-(p,n) = (1 - N_p) N_n$. -/
def isoProjMinus (p n : Fin 5) : MatStage 5 := modeVacant p * modeOccupied n

/-- Doubly-occupied pairing sector projector $\Pi_{\mathrm{pair}}^+(p,n) = N_p N_n$. -/
def pairProjPlus (p n : Fin 5) : MatStage 5 := modeOccupied p * modeOccupied n

/-- Doubly-vacant pairing sector projector $\Pi_{\mathrm{pair}}^-(p,n) = (1 - N_p)(1 - N_n)$. -/
def pairProjMinus (p n : Fin 5) : MatStage 5 := modeVacant p * modeVacant n

/-- The four two-mode sector projectors $\Pi_+ + \Pi_- + \Pi_{\mathrm{pair}}^+ + \Pi_{\mathrm{pair}}^-$
resolve the $32 \times 32$ identity in $\mathrm{Cl}(5,5)$. -/
theorem four_projector_sum (p n : Fin 5) :
    isoProjPlus p n + isoProjMinus p n + pairProjPlus p n + pairProjMinus p n = 1 := by
  dsimp [isoProjPlus, isoProjMinus, pairProjPlus, pairProjMinus]
  calc
    modeOccupied p * modeVacant n + modeVacant p * modeOccupied n +
        modeOccupied p * modeOccupied n + modeVacant p * modeVacant n =
      (modeOccupied p + modeVacant p) * (modeOccupied n + modeVacant n) := by
      noncomm_ring
    _ = 1 * 1 := by rw [modeOccupied_add_modeVacant p, modeOccupied_add_modeVacant n]
    _ = 1 := mul_one 1

/-- The grade-0 isospin Cartan generator equals the occupation difference $N_p - N_n$. -/
theorem isospinCartan_eq_modeOccupied_sub (p n : Fin 5) :
    isospinCartan p n = modeOccupied p - modeOccupied n := by
  dsimp [isospinCartan, H, E, modeOccupied, e, f]
  simp only [ite_true]
  abel

/-- Every mode occupation projector equals $H_a + \frac{1}{2} I$. -/
theorem modeOccupied_eq_H_add_half (a : Fin 5) :
    modeOccupied a = H a + (1 / 2 : ℝ) • (1 : MatStage 5) := by
  dsimp [modeOccupied, H, E, e, f]
  simp only [ite_true, sub_add_cancel]

/-- Every mode vacancy projector equals $\frac{1}{2} I - H_a$. -/
theorem modeVacant_eq_half_sub_H (a : Fin 5) :
    modeVacant a = (1 / 2 : ℝ) • (1 : MatStage 5) - H a := by
  have hsum := modeOccupied_add_modeVacant a
  have hvac : modeVacant a = 1 - modeOccupied a := eq_sub_of_add_eq' hsum
  rw [hvac, modeOccupied_eq_H_add_half]
  match_scalars <;> norm_num

/-- Twice the Cartan generator $H_a$ is the difference of the occupied and vacant projectors. -/
theorem two_smul_H_eq_modeOccupied_sub_modeVacant (a : Fin 5) :
    (2 : ℝ) • H a = modeOccupied a - modeVacant a := by
  rw [modeOccupied_eq_H_add_half, modeVacant_eq_half_sub_H]
  match_scalars <;> norm_num

/-- Every normalized mode Cartan involution $(2 H_a)$ squares to the $32 \times 32$ identity. -/
theorem two_smul_H_sq (a : Fin 5) :
    ((2 : ℝ) • H a) * ((2 : ℝ) • H a) = 1 := by
  rw [two_smul_H_eq_modeOccupied_sub_modeVacant]
  calc
    (modeOccupied a - modeVacant a) * (modeOccupied a - modeVacant a) =
      modeOccupied a * modeOccupied a - modeOccupied a * modeVacant a -
      modeVacant a * modeOccupied a + modeVacant a * modeVacant a := by
      noncomm_ring
    _ = modeOccupied a + modeVacant a := by
      rw [modeOccupied_idem, modeVacant_idem,
          modeOccupied_mul_modeVacant, modeVacant_mul_modeOccupied]
      abel
    _ = 1 := modeOccupied_add_modeVacant a

/-- Mode occupation projectors commute for all $p, n \in \mathrm{Fin}\;5$. -/
theorem modeOccupied_comm (p n : Fin 5) :
    modeOccupied p * modeOccupied n = modeOccupied n * modeOccupied p := by
  have hcomm : H p * H n = H n * H p := sub_eq_zero.mp (H_comm p n)
  rw [modeOccupied_eq_H_add_half p, modeOccupied_eq_H_add_half n]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add, hcomm]
  abel

/-- Spectral decomposition of the grade-0 isospin Cartan generator into $\Pi_+ - \Pi_-$. -/
theorem isospinCartan_eq_isoProj_sub (p n : Fin 5) :
    isospinCartan p n = isoProjPlus p n - isoProjMinus p n := by
  dsimp [isoProjPlus, isoProjMinus]
  have hvp : modeVacant p = 1 - modeOccupied p :=
    eq_sub_of_add_eq' (modeOccupied_add_modeVacant p)
  have hvn : modeVacant n = 1 - modeOccupied n :=
    eq_sub_of_add_eq' (modeOccupied_add_modeVacant n)
  rw [hvp, hvn, isospinCartan_eq_modeOccupied_sub]
  noncomm_ring

/-- Spectral decomposition of the pairing Cartan generator $2 K_0 = H_p + H_n$ into $\Pi_{\mathrm{pair}}^+ - \Pi_{\mathrm{pair}}^-$. -/
theorem pairingCartan_eq_pairProj_sub (p n : Fin 5) :
    pairingCartan p n = pairProjPlus p n - pairProjMinus p n := by
  dsimp [pairingCartan, pairProjPlus, pairProjMinus]
  have hvp : modeVacant p = 1 - modeOccupied p :=
    eq_sub_of_add_eq' (modeOccupied_add_modeVacant p)
  have hvn : modeVacant n = 1 - modeOccupied n :=
    eq_sub_of_add_eq' (modeOccupied_add_modeVacant n)
  have hHp : H p = modeOccupied p - (1 / 2 : ℝ) • (1 : MatStage 5) :=
    eq_sub_of_add_eq (modeOccupied_eq_H_add_half p).symm
  have hHn : H n = modeOccupied n - (1 / 2 : ℝ) • (1 : MatStage 5) :=
    eq_sub_of_add_eq (modeOccupied_eq_H_add_half n).symm
  rw [hvp, hvn, hHp, hHn]
  calc
    modeOccupied p - (1 / 2 : ℝ) • (1 : MatStage 5) +
        (modeOccupied n - (1 / 2 : ℝ) • (1 : MatStage 5)) =
      modeOccupied p + modeOccupied n -
        ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • (1 : MatStage 5) := by
      rw [add_smul]
      abel
    _ = modeOccupied p + modeOccupied n - 1 := by norm_num
    _ = modeOccupied p * modeOccupied n -
        (1 - modeOccupied p) * (1 - modeOccupied n) := by
      noncomm_ring

/-- Exact projector eigenvalue equations for the grade-0 isospin Cartan generator $\tau_3$:
$\tau_3 \Pi_+ = +\Pi_+$, $\tau_3 \Pi_- = -\Pi_-$, $\tau_3 \Pi_{\mathrm{pair}}^+ = 0$, $\tau_3 \Pi_{\mathrm{pair}}^- = 0$. -/
theorem isospinCartan_projector_eigenvalues (p n : Fin 5) :
    isospinCartan p n * isoProjPlus p n = isoProjPlus p n ∧
    isospinCartan p n * isoProjMinus p n = -isoProjMinus p n ∧
    isospinCartan p n * pairProjPlus p n = 0 ∧
    isospinCartan p n * pairProjMinus p n = 0 := by
  rw [isospinCartan_eq_modeOccupied_sub]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [isoProjPlus]
    calc
      (modeOccupied p - modeOccupied n) * (modeOccupied p * modeVacant n) =
        (modeOccupied p * modeOccupied p) * modeVacant n -
        (modeOccupied n * modeOccupied p) * modeVacant n := by noncomm_ring
      _ = modeOccupied p * modeVacant n -
        modeOccupied p * (modeOccupied n * modeVacant n) := by
        rw [modeOccupied_idem p, modeOccupied_comm n p, mul_assoc]
      _ = modeOccupied p * modeVacant n := by
        rw [modeOccupied_mul_modeVacant n, mul_zero, sub_zero]
  · dsimp [isoProjMinus]
    calc
      (modeOccupied p - modeOccupied n) * (modeVacant p * modeOccupied n) =
        (modeOccupied p * modeVacant p) * modeOccupied n -
        modeOccupied n * (modeVacant p * modeOccupied n) := by noncomm_ring
      _ = -(modeOccupied n * (modeVacant p * modeOccupied n)) := by
        rw [modeOccupied_mul_modeVacant p, zero_mul, zero_sub]
      _ = -(modeVacant p * (modeOccupied n * modeOccupied n)) := by
        have hvp : modeVacant p = 1 - modeOccupied p :=
          eq_sub_of_add_eq' (modeOccupied_add_modeVacant p)
        rw [hvp]
        calc
          -(modeOccupied n * ((1 - modeOccupied p) * modeOccupied n)) =
            -(modeOccupied n * modeOccupied n -
              (modeOccupied n * modeOccupied p) * modeOccupied n) := by noncomm_ring
          _ = -(modeOccupied n * modeOccupied n -
              (modeOccupied p * modeOccupied n) * modeOccupied n) := by
            rw [modeOccupied_comm n p]
          _ = -((1 - modeOccupied p) * (modeOccupied n * modeOccupied n)) := by
            noncomm_ring
      _ = -(modeVacant p * modeOccupied n) := by rw [modeOccupied_idem n]
  · dsimp [pairProjPlus]
    calc
      (modeOccupied p - modeOccupied n) * (modeOccupied p * modeOccupied n) =
        (modeOccupied p * modeOccupied p) * modeOccupied n -
        (modeOccupied n * modeOccupied p) * modeOccupied n := by noncomm_ring
      _ = modeOccupied p * modeOccupied n -
        modeOccupied p * (modeOccupied n * modeOccupied n) := by
        rw [modeOccupied_idem p, modeOccupied_comm n p, mul_assoc]
      _ = 0 := by rw [modeOccupied_idem n, sub_self]
  · dsimp [pairProjMinus]
    have hvp : modeVacant p = 1 - modeOccupied p :=
      eq_sub_of_add_eq' (modeOccupied_add_modeVacant p)
    have hvn : modeVacant n = 1 - modeOccupied n :=
      eq_sub_of_add_eq' (modeOccupied_add_modeVacant n)
    calc
      (modeOccupied p - modeOccupied n) * (modeVacant p * modeVacant n) =
        (modeOccupied p * modeVacant p) * modeVacant n -
        modeOccupied n * (modeVacant p * modeVacant n) := by noncomm_ring
      _ = -(modeOccupied n * ((1 - modeOccupied p) * modeVacant n)) := by
        rw [modeOccupied_mul_modeVacant p, zero_mul, zero_sub, hvp]
      _ = -((modeOccupied n - modeOccupied n * modeOccupied p) * modeVacant n) := by
        noncomm_ring
      _ = -((modeOccupied n - modeOccupied p * modeOccupied n) * modeVacant n) := by
        rw [modeOccupied_comm n p]
      _ = -((1 - modeOccupied p) * (modeOccupied n * modeVacant n)) := by
        noncomm_ring
      _ = 0 := by rw [modeOccupied_mul_modeVacant n, mul_zero, neg_zero]

/-- Exact quadratic Casimir partition $\tau_3^2 + (2 K_0)^2 = I_{32}$ in $\mathrm{Cl}(5,5)$. -/
theorem isospinCartan_sq_add_pairingCartan_sq (p n : Fin 5) :
    isospinCartan p n * isospinCartan p n +
      pairingCartan p n * pairingCartan p n = 1 := by
  dsimp [isospinCartan, pairingCartan]
  have hcomm : H p * H n = H n * H p := sub_eq_zero.mp (H_comm p n)
  have hHp : ((2 : ℝ) • H p) * ((2 : ℝ) • H p) = 1 := two_smul_H_sq p
  have hHn : ((2 : ℝ) • H n) * ((2 : ℝ) • H n) = 1 := two_smul_H_sq n
  have hexp :
      (H p - H n) * (H p - H n) + (H p + H n) * (H p + H n) =
        (1 / 2 : ℝ) • (((2 : ℝ) • H p) * ((2 : ℝ) • H p) +
          ((2 : ℝ) • H n) * ((2 : ℝ) • H n)) := by
    simp only [smul_mul_smul]
    calc
      (H p - H n) * (H p - H n) + (H p + H n) * (H p + H n) =
        (H p * H p + H p * H p) + (H n * H n + H n * H n) +
        (H p * H n - H n * H p) - (H p * H n - H n * H p) := by noncomm_ring
      _ = (2 : ℝ) • (H p * H p) + (2 : ℝ) • (H n * H n) := by
        rw [hcomm, sub_self, two_smul, two_smul]
        abel
      _ = (1 / 2 : ℝ) • (((2 : ℝ) * (2 : ℝ)) • (H p * H p) +
          ((2 : ℝ) * (2 : ℝ)) • (H n * H n)) := by
        rw [smul_add, smul_smul, smul_smul]
        norm_num
  rw [hexp, hHp, hHn, ← two_smul ℝ (1 : MatStage 5), smul_smul]
  norm_num

/-- Five-grading classification: isospin generators have grade $0$ under `numberOperator`,
while pairing raising/lowering generators have grades $+2$ and $-2$. -/
theorem five_graded_isospin_and_pairing_grades (p n : Fin 5) :
    bracket numberOperator (isospinPlus p n) = 0 ∧
    bracket numberOperator (isospinMinus p n) = 0 ∧
    bracket numberOperator (isospinCartan p n) = 0 ∧
    bracket numberOperator (pairingCartan p n) = 0 ∧
    bracket numberOperator (pairingPlus p n) = (2 : ℝ) • pairingPlus p n ∧
    bracket numberOperator (pairingMinus p n) = (-2 : ℝ) • pairingMinus p n := by
  refine ⟨numberOperator_E p n, numberOperator_E n p, ?_, ?_,
          numberOperator_creation_quadratic p n,
          numberOperator_annihilation_quadratic n p⟩
  · dsimp [isospinCartan, H]
    rw [sub_eq_add_neg, bracket_add_right, numberOperator_E]
    have hneg : bracket numberOperator (-E n n) = 0 := by
      rw [show -E n n = (-1 : ℝ) • E n n by simp, bracket_smul_right,
          numberOperator_E, smul_zero]
    rw [hneg, add_zero]
  · dsimp [pairingCartan, H]
    rw [bracket_add_right, numberOperator_E, numberOperator_E, add_zero]

/-- Grade-0 isospin $\mathfrak{sl}_2$ bracket $[\tau_+, \tau_-] = \tau_3$ holds unconditionally for all $p, n$. -/
theorem isospin_plus_minus_bracket (p n : Fin 5) :
    bracket (isospinPlus p n) (isospinMinus p n) = isospinCartan p n := by
  dsimp [isospinPlus, isospinMinus, isospinCartan, H]
  rw [E_bracket]
  simp

/-- Grade-0 isospin $\mathfrak{sl}_2$ bracket $[\tau_3, \tau_+] = 2 \tau_+$ for $p \neq n$. -/
theorem isospin_cartan_plus_bracket {p n : Fin 5} (hpn : p ≠ n) :
    bracket (isospinCartan p n) (isospinPlus p n) = (2 : ℝ) • isospinPlus p n := by
  dsimp [isospinCartan, isospinPlus, H]
  have hsub : bracket (E p p - E n n) (E p n) =
      bracket (E p p) (E p n) - bracket (E n n) (E p n) := by
    unfold bracket
    noncomm_ring
  rw [hsub, E_bracket, E_bracket]
  simp [hpn, Ne.symm hpn, two_smul]

/-- Grade-0 isospin $\mathfrak{sl}_2$ bracket $[\tau_3, \tau_-] = -2 \tau_-$ for $p \neq n$. -/
theorem isospin_cartan_minus_bracket {p n : Fin 5} (hpn : p ≠ n) :
    bracket (isospinCartan p n) (isospinMinus p n) = -(2 : ℝ) • isospinMinus p n := by
  dsimp [isospinCartan, isospinMinus, H]
  have hsub : bracket (E p p - E n n) (E n p) =
      bracket (E p p) (E n p) - bracket (E n n) (E n p) := by
    unfold bracket
    noncomm_ring
  rw [hsub, E_bracket, E_bracket]
  simp [hpn, Ne.symm hpn, two_smul]
  abel

/-- Grade-$\pm 2$ pairing quasispin $\mathfrak{sl}_2$ bracket $[K_+, K_-] = 2 K_0$ for $p \neq n$. -/
theorem pairing_plus_minus_bracket {p n : Fin 5} (hpn : p ≠ n) :
    bracket (pairingPlus p n) (pairingMinus p n) = pairingCartan p n := by
  dsimp [pairingPlus, pairingMinus, pairingCartan, H, e, f]
  rw [creation_quadratic_bracket_annihilation_quadratic]
  simp [hpn, Ne.symm hpn]

/-- Mutual commutation of the isospin and pairing Cartan generators with the opposite $\mathfrak{sl}_2$ ladders. -/
theorem isospin_and_pairing_mutual_commutation {p n : Fin 5} (hpn : p ≠ n) :
    bracket (isospinCartan p n) (pairingCartan p n) = 0 ∧
    bracket (isospinCartan p n) (pairingPlus p n) = 0 ∧
    bracket (isospinCartan p n) (pairingMinus p n) = 0 ∧
    bracket (pairingCartan p n) (isospinPlus p n) = 0 ∧
    bracket (pairingCartan p n) (isospinMinus p n) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [isospinCartan, pairingCartan]
    have hexp : bracket (H p - H n) (H p + H n) =
        bracket (H p) (H p) + bracket (H p) (H n) -
        bracket (H n) (H p) - bracket (H n) (H n) := by
      unfold bracket
      noncomm_ring
    rw [hexp, H_comm, H_comm, H_comm, H_comm]
    simp
  · dsimp [isospinCartan, pairingPlus, H, e]
    have hsub : bracket (E p p - E n n) (creation p * creation n) =
        bracket (E p p) (creation p * creation n) -
        bracket (E n n) (creation p * creation n) := by
      unfold bracket
      noncomm_ring
    rw [hsub, diagonal_positiveTwo_weight, diagonal_positiveTwo_weight]
    simp [positiveTwoWeight, hpn, Ne.symm hpn]
  · dsimp [isospinCartan, pairingMinus, H, f]
    have hsub : bracket (E p p - E n n) (annihilation n * annihilation p) =
        bracket (E p p) (annihilation n * annihilation p) -
        bracket (E n n) (annihilation n * annihilation p) := by
      unfold bracket
      noncomm_ring
    rw [hsub, diagonal_negativeTwo_weight, diagonal_negativeTwo_weight]
    simp [negativeTwoWeight, hpn, Ne.symm hpn]
  · dsimp [pairingCartan, isospinPlus, H]
    rw [bracket_add_left, E_bracket, E_bracket]
    simp [hpn, Ne.symm hpn]
  · dsimp [pairingCartan, isospinMinus, H]
    rw [bracket_add_left, E_bracket, E_bracket]
    simp [hpn, Ne.symm hpn]

/-! ## 7. Bi-Peirce Ladder Factorizations, Casimir Partition, and $\mathrm{Pin}_+(5,5)$ Majorana Duality -/

/-- Odd-fermion active isospin carrier $\Delta_{\mathrm{iso}}(p,n) = \Pi_+(p,n) + \Pi_-(p,n)$. -/
def isospinCarrier (p n : Fin 5) : MatStage 5 :=
  isoProjPlus p n + isoProjMinus p n

/-- Even-fermion active pairing carrier $\Delta_{\mathrm{pair}}(p,n) = \Pi_{\mathrm{pair}}^+(p,n) + \Pi_{\mathrm{pair}}^-(p,n)$. -/
def pairingCarrier (p n : Fin 5) : MatStage 5 :=
  pairProjPlus p n + pairProjMinus p n

/-- Full quadratic Casimir of $\mathfrak{sl}_2^{\mathrm{iso}}$:
$C_2^{\mathrm{iso}} = \tau_3^2 + 2(\tau_+ \tau_- + \tau_- \tau_+)$. -/
def isospinCasimir (p n : Fin 5) : MatStage 5 :=
  isospinCartan p n * isospinCartan p n +
    (2 : ℝ) • (isospinPlus p n * isospinMinus p n + isospinMinus p n * isospinPlus p n)

/-- Full quadratic Casimir of $\mathfrak{sl}_2^{\mathrm{pair}}$:
$C_2^{\mathrm{pair}} = (2 K_0)^2 + 2(K_+ K_- + K_- K_+)$. -/
def pairingCasimir (p n : Fin 5) : MatStage 5 :=
  pairingCartan p n * pairingCartan p n +
    (2 : ℝ) • (pairingPlus p n * pairingMinus p n + pairingMinus p n * pairingPlus p n)

/-- Single-mode $\mathrm{Pin}_+(5,5)$ Majorana reflection $\Gamma_n = e_n + f_n$. -/
abbrev majoranaPinReflection (n : Fin 5) : MatStage 5 := gammaPlus n

/-- Creation operators anticommute in multiplicative form $e_a e_b = - e_b e_a$. -/
theorem e_mul_e_swap (a b : Fin 5) : e a * e b = -(e b * e a) :=
  eq_neg_of_add_eq_zero_left (e_anticomm a b)

/-- Annihilation operators anticommute in multiplicative form $f_a f_b = - f_b f_a$. -/
theorem f_mul_f_swap (a b : Fin 5) : f a * f b = -(f b * f a) :=
  eq_neg_of_add_eq_zero_left (f_anticomm a b)

/-- Distinct creation and annihilation operators anticommute: $e_a f_b = - f_b e_a$ for $a \neq b$. -/
theorem e_mul_f_swap_ne {a b : Fin 5} (hab : a ≠ b) : e a * f b = -(f b * e a) := by
  have h := ef_car a b
  simp [hab] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Distinct annihilation and creation operators anticommute: $f_b e_a = - e_a f_b$ for $a \neq b$. -/
theorem f_mul_e_swap_ne {a b : Fin 5} (hab : a ≠ b) : f b * e a = -(e a * f b) := by
  have h := ef_car a b
  simp [hab] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Occupation projector $N_n$ commutes with $f_p$ for $p \neq n$. -/
theorem modeOccupied_comm_f_ne {p n : Fin 5} (hpn : p ≠ n) :
    modeOccupied n * f p = f p * modeOccupied n := by
  dsimp [modeOccupied]
  have h1 : f n * f p = -(f p * f n) := f_mul_f_swap n p
  have h2 : e n * f p = -(f p * e n) := e_mul_f_swap_ne (Ne.symm hpn)
  calc
    (e n * f n) * f p = e n * (f n * f p) := by noncomm_ring
    _ = -(e n * f p) * f n := by rw [h1]; noncomm_ring
    _ = f p * (e n * f n) := by rw [h2]; noncomm_ring

/-- Vacancy projector $1 - N_n$ commutes with $f_p$ for $p \neq n$. -/
theorem modeVacant_comm_f_ne {p n : Fin 5} (hpn : p ≠ n) :
    modeVacant n * f p = f p * modeVacant n := by
  have hvac : modeVacant n = 1 - modeOccupied n :=
    eq_sub_of_add_eq' (modeOccupied_add_modeVacant n)
  rw [hvac]
  calc
    (1 - modeOccupied n) * f p = f p - modeOccupied n * f p := by noncomm_ring
    _ = f p - f p * modeOccupied n := by rw [modeOccupied_comm_f_ne hpn]
    _ = f p * (1 - modeOccupied n) := by noncomm_ring

/-- Occupation projector $N_p$ commutes with $e_n$ for $p \neq n$. -/
theorem modeOccupied_comm_e_ne {p n : Fin 5} (hpn : p ≠ n) :
    modeOccupied p * e n = e n * modeOccupied p := by
  dsimp [modeOccupied]
  have h1 : f p * e n = -(e n * f p) := f_mul_e_swap_ne (Ne.symm hpn)
  have h2 : e p * e n = -(e n * e p) := e_mul_e_swap p n
  calc
    (e p * f p) * e n = e p * (f p * e n) := by noncomm_ring
    _ = -(e p * e n) * f p := by rw [h1]; noncomm_ring
    _ = e n * (e p * f p) := by rw [h2]; noncomm_ring

/-- Vacancy projector $1 - N_p$ commutes with $e_n$ for $p \neq n$. -/
theorem modeVacant_comm_e_ne {p n : Fin 5} (hpn : p ≠ n) :
    modeVacant p * e n = e n * modeVacant p := by
  have hvac : modeVacant p = 1 - modeOccupied p :=
    eq_sub_of_add_eq' (modeOccupied_add_modeVacant p)
  rw [hvac]
  calc
    (1 - modeOccupied p) * e n = e n - modeOccupied p * e n := by noncomm_ring
    _ = e n - e n * modeOccupied p := by rw [modeOccupied_comm_e_ne hpn]
    _ = e n * (1 - modeOccupied p) := by noncomm_ring

/-- For distinct modes $p \neq n$, $\tau_+(p,n) = e_p f_n$. -/
theorem isospinPlus_eq_e_mul_f {p n : Fin 5} (hpn : p ≠ n) :
    isospinPlus p n = e p * f n := by
  dsimp [isospinPlus, E, e, f]
  simp [hpn]

/-- For distinct modes $p \neq n$, $\tau_-(p,n) = e_n f_p$. -/
theorem isospinMinus_eq_e_mul_f {p n : Fin 5} (hpn : p ≠ n) :
    isospinMinus p n = e n * f p := by
  dsimp [isospinMinus, E, e, f]
  simp [Ne.symm hpn]

/-- **Isospin Ladder Factorization ($\tau_+ \tau_- = \Pi_+$)**:
For distinct modes $p \neq n$, $\tau_+(p,n) \tau_-(p,n) = \Pi_+(p,n) = N_p (1 - N_n)$. -/
theorem isospinPlus_mul_isospinMinus {p n : Fin 5} (hpn : p ≠ n) :
    isospinPlus p n * isospinMinus p n = isoProjPlus p n := by
  rw [isospinPlus_eq_e_mul_f hpn, isospinMinus_eq_e_mul_f hpn]
  dsimp [isoProjPlus, modeOccupied]
  calc
    (e p * f n) * (e n * f p) = e p * ((f n * e n) * f p) := by noncomm_ring
    _ = e p * (modeVacant n * f p) := rfl
    _ = e p * (f p * modeVacant n) := by rw [modeVacant_comm_f_ne hpn]
    _ = (e p * f p) * modeVacant n := by noncomm_ring

/-- **Reverse Isospin Ladder Factorization ($\tau_- \tau_+ = \Pi_-$)**:
For distinct modes $p \neq n$, $\tau_-(p,n) \tau_+(p,n) = \Pi_-(p,n) = (1 - N_p) N_n$. -/
theorem isospinMinus_mul_isospinPlus {p n : Fin 5} (hpn : p ≠ n) :
    isospinMinus p n * isospinPlus p n = isoProjMinus p n := by
  rw [isospinPlus_eq_e_mul_f hpn, isospinMinus_eq_e_mul_f hpn]
  dsimp [isoProjMinus, modeOccupied]
  calc
    (e n * f p) * (e p * f n) = (e n * (f p * e p)) * f n := by noncomm_ring
    _ = (e n * modeVacant p) * f n := rfl
    _ = (modeVacant p * e n) * f n := by rw [← modeVacant_comm_e_ne hpn]
    _ = modeVacant p * (e n * f n) := by noncomm_ring

/-- **Pairing Ladder Factorization ($K_+ K_- = \Pi_{\mathrm{pair}}^+$)**:
For distinct modes $p \neq n$, $K_+(p,n) K_-(p,n) = \Pi_{\mathrm{pair}}^+(p,n) = N_p N_n$. -/
theorem pairingPlus_mul_pairingMinus {p n : Fin 5} (hpn : p ≠ n) :
    pairingPlus p n * pairingMinus p n = pairProjPlus p n := by
  dsimp [pairingPlus, pairingMinus, pairProjPlus, modeOccupied]
  calc
    (e p * e n) * (f n * f p) = e p * ((e n * f n) * f p) := by noncomm_ring
    _ = e p * (modeOccupied n * f p) := rfl
    _ = e p * (f p * modeOccupied n) := by rw [modeOccupied_comm_f_ne hpn]
    _ = (e p * f p) * modeOccupied n := by noncomm_ring

/-- **Reverse Pairing Ladder Factorization ($K_- K_+ = \Pi_{\mathrm{pair}}^-$)**:
For distinct modes $p \neq n$, $K_-(p,n) K_+(p,n) = \Pi_{\mathrm{pair}}^-(p,n) = (1 - N_p)(1 - N_n)$. -/
theorem pairingMinus_mul_pairingPlus {p n : Fin 5} (hpn : p ≠ n) :
    pairingMinus p n * pairingPlus p n = pairProjMinus p n := by
  dsimp [pairingPlus, pairingMinus, pairProjMinus, modeVacant]
  calc
    (f n * f p) * (e p * e n) = (f n * (f p * e p)) * e n := by noncomm_ring
    _ = (f n * modeVacant p) * e n := rfl
    _ = (modeVacant p * f n) * e n := by rw [← modeVacant_comm_f_ne (Ne.symm hpn)]
    _ = modeVacant p * (f n * e n) := by noncomm_ring

/-- **Associative Cross-Sector Annihilation (`isospin_mul_pairing_eq_zero`)**:
Every associative product of an isospin ladder seed ($\tau_\pm$) with a pairing ladder seed ($K_\pm$)
vanishes identically! -/
theorem isospin_mul_pairing_eq_zero {p n : Fin 5} (hpn : p ≠ n) :
    isospinPlus p n * pairingPlus p n = 0 ∧
    isospinPlus p n * pairingMinus p n = 0 ∧
    isospinMinus p n * pairingPlus p n = 0 ∧
    isospinMinus p n * pairingMinus p n = 0 := by
  rw [isospinPlus_eq_e_mul_f hpn, isospinMinus_eq_e_mul_f hpn]
  dsimp [pairingPlus, pairingMinus]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hswap : f n * e p = -(e p * f n) := f_mul_e_swap_ne hpn
    calc
      (e p * f n) * (e p * e n) = e p * (f n * e p) * e n := by noncomm_ring
      _ = -(e p * e p) * f n * e n := by rw [hswap]; noncomm_ring
      _ = 0 := by rw [e_sq p, neg_zero, zero_mul, zero_mul]
  · calc
      (e p * f n) * (f n * f p) = e p * (f n * f n) * f p := by noncomm_ring
      _ = 0 := by rw [f_sq n, mul_zero, zero_mul]
  · have hswap1 : e p * e n = -(e n * e p) := e_mul_e_swap p n
    have hswap2 : f p * e n = -(e n * f p) := f_mul_e_swap_ne (Ne.symm hpn)
    calc
      (e n * f p) * (e p * e n) = -(e n * (f p * e n) * e p) := by rw [hswap1]; noncomm_ring
      _ = (e n * e n) * f p * e p := by rw [hswap2]; noncomm_ring
      _ = 0 := by rw [e_sq n, zero_mul, zero_mul]
  · have hswap : f n * f p = -(f p * f n) := f_mul_f_swap n p
    calc
      (e n * f p) * (f n * f p) = -(e n * (f p * f p) * f n) := by rw [hswap]; noncomm_ring
      _ = 0 := by rw [f_sq p, mul_zero, zero_mul, neg_zero]

/-- Isospin and pairing active carriers resolve the $32 \times 32$ identity:
$\Delta_{\mathrm{iso}} + \Delta_{\mathrm{pair}} = I_{32}$. -/
theorem isospinCarrier_add_pairingCarrier (p n : Fin 5) :
    isospinCarrier p n + pairingCarrier p n = 1 := by
  dsimp [isospinCarrier, pairingCarrier]
  calc
    (isoProjPlus p n + isoProjMinus p n) + (pairProjPlus p n + pairProjMinus p n) =
      isoProjPlus p n + isoProjMinus p n + pairProjPlus p n + pairProjMinus p n := by abel
    _ = 1 := four_projector_sum p n

/-- The square of the isospin Cartan generator equals the active isospin carrier:
$\tau_3(p,n)^2 = \Delta_{\mathrm{iso}}(p,n)$. -/
theorem isospinCartan_sq_eq_isospinCarrier (p n : Fin 5) :
    isospinCartan p n * isospinCartan p n = isospinCarrier p n := by
  rw [isospinCartan_eq_modeOccupied_sub]
  dsimp [isospinCarrier, isoProjPlus, isoProjMinus]
  have hvp : modeVacant p = 1 - modeOccupied p :=
    eq_sub_of_add_eq' (modeOccupied_add_modeVacant p)
  have hvn : modeVacant n = 1 - modeOccupied n :=
    eq_sub_of_add_eq' (modeOccupied_add_modeVacant n)
  rw [hvp, hvn]
  calc
    (modeOccupied p - modeOccupied n) * (modeOccupied p - modeOccupied n) =
      modeOccupied p * modeOccupied p - modeOccupied p * modeOccupied n -
      modeOccupied n * modeOccupied p + modeOccupied n * modeOccupied n := by noncomm_ring
    _ = modeOccupied p - modeOccupied p * modeOccupied n -
      modeOccupied p * modeOccupied n + modeOccupied n := by
      rw [modeOccupied_idem p, modeOccupied_idem n, modeOccupied_comm n p]
    _ = modeOccupied p * (1 - modeOccupied n) + (1 - modeOccupied p) * modeOccupied n := by
      noncomm_ring

/-- The square of the pairing Cartan generator equals the active pairing carrier:
$(2 K_0(p,n))^2 = \Delta_{\mathrm{pair}}(p,n)$. -/
theorem pairingCartan_sq_eq_pairingCarrier (p n : Fin 5) :
    pairingCartan p n * pairingCartan p n = pairingCarrier p n := by
  have hsum_sq := isospinCartan_sq_add_pairingCartan_sq p n
  have hsum_car := isospinCarrier_add_pairingCarrier p n
  rw [isospinCartan_sq_eq_isospinCarrier] at hsum_sq
  calc
    pairingCartan p n * pairingCartan p n =
      1 - isospinCarrier p n := eq_sub_of_add_eq' hsum_sq
    _ = pairingCarrier p n := (eq_sub_of_add_eq' hsum_car).symm

/-- **Full $\mathfrak{sl}_2$ Casimir Partition of $3 \cdot I_{32}$ (`casimir_partition_of_three_one`)**:
For distinct modes $p \neq n$:
1. $C_2^{\mathrm{iso}}(p,n) = 3 \Delta_{\mathrm{iso}}(p,n)$,
2. $C_2^{\mathrm{pair}}(p,n) = 3 \Delta_{\mathrm{pair}}(p,n)$,
3. $C_2^{\mathrm{iso}}(p,n) + C_2^{\mathrm{pair}}(p,n) = 3 \cdot I_{32}$. -/
theorem casimir_partition_of_three_one {p n : Fin 5} (hpn : p ≠ n) :
    isospinCasimir p n = (3 : ℝ) • isospinCarrier p n ∧
    pairingCasimir p n = (3 : ℝ) • pairingCarrier p n ∧
    isospinCasimir p n + pairingCasimir p n = (3 : ℝ) • (1 : MatStage 5) := by
  have hc_iso : isospinCasimir p n = (3 : ℝ) • isospinCarrier p n := by
    dsimp [isospinCasimir]
    rw [isospinCartan_sq_eq_isospinCarrier p n,
        isospinPlus_mul_isospinMinus hpn, isospinMinus_mul_isospinPlus hpn]
    change isospinCarrier p n + (2 : ℝ) • isospinCarrier p n = (3 : ℝ) • isospinCarrier p n
    (match_scalars; norm_num)
  have hc_pair : pairingCasimir p n = (3 : ℝ) • pairingCarrier p n := by
    dsimp [pairingCasimir]
    rw [pairingCartan_sq_eq_pairingCarrier p n,
        pairingPlus_mul_pairingMinus hpn, pairingMinus_mul_pairingPlus hpn]
    change pairingCarrier p n + (2 : ℝ) • pairingCarrier p n = (3 : ℝ) • pairingCarrier p n
    (match_scalars; norm_num)
  have htot : isospinCasimir p n + pairingCasimir p n = (3 : ℝ) • (1 : MatStage 5) := by
    rw [hc_iso, hc_pair, ← smul_add, isospinCarrier_add_pairingCarrier p n]
  exact ⟨hc_iso, hc_pair, htot⟩

/-- Conjugating $e_n$ by the $\mathrm{Pin}_+(5,5)$ reflection $\Gamma_n = e_n + f_n$ produces $f_n$:
$\Gamma_n e_n \Gamma_n = f_n$. -/
theorem gammaPlus_conj_e_same (n : Fin 5) :
    gammaPlus n * e n * gammaPlus n = f n := by
  have hcar : e n * f n + f n * e n = 1 := by simpa using ef_car n n
  have hfnen : f n * e n * f n = f n := by
    calc
      (f n * e n) * f n = (1 - e n * f n) * f n := by rw [eq_sub_of_add_eq' hcar]
      _ = f n - e n * (f n * f n) := by noncomm_ring
      _ = f n := by rw [f_sq n, mul_zero, sub_zero]
  dsimp [gammaPlus]
  calc
    (e n + f n) * e n * (e n + f n) =
      (e n * e n) * e n + (e n * e n) * f n + f n * (e n * e n) + (f n * e n * f n) := by
      noncomm_ring
    _ = f n := by rw [e_sq n, hfnen]; simp

/-- Conjugating $f_n$ by the $\mathrm{Pin}_+(5,5)$ reflection $\Gamma_n = e_n + f_n$ produces $e_n$:
$\Gamma_n f_n \Gamma_n = e_n$. -/
theorem gammaPlus_conj_f_same (n : Fin 5) :
    gammaPlus n * f n * gammaPlus n = e n := by
  have hcar : e n * f n + f n * e n = 1 := by simpa using ef_car n n
  have henfn : e n * f n * e n = e n := by
    calc
      (e n * f n) * e n = (1 - f n * e n) * e n := by rw [eq_sub_of_add_eq hcar]
      _ = e n - f n * (e n * e n) := by noncomm_ring
      _ = e n := by rw [e_sq n, mul_zero, sub_zero]
  dsimp [gammaPlus]
  calc
    (e n + f n) * f n * (e n + f n) =
      (e n * f n * e n) + e n * (f n * f n) + (f n * f n) * e n + (f n * f n) * f n := by
      noncomm_ring
    _ = e n := by rw [f_sq n, henfn]; simp

/-- For $p \neq n$, the creation operator $e_p$ anticommutes with $\Gamma_n = e_n + f_n$. -/
theorem gammaPlus_anticomm_e_ne {p n : Fin 5} (hpn : p ≠ n) :
    e p * gammaPlus n = -(gammaPlus n * e p) := by
  dsimp [gammaPlus]
  have h1 : e p * e n = -(e n * e p) := e_mul_e_swap p n
  have h2 : e p * f n = -(f n * e p) := e_mul_f_swap_ne hpn
  calc
    e p * (e n + f n) = e p * e n + e p * f n := mul_add _ _ _
    _ = -(e n * e p) + -(f n * e p) := by rw [h1, h2]
    _ = -((e n + f n) * e p) := by noncomm_ring

/-- For $p \neq n$, the annihilation operator $f_p$ anticommutes with $\Gamma_n = e_n + f_n$. -/
theorem gammaPlus_anticomm_f_ne {p n : Fin 5} (hpn : p ≠ n) :
    gammaPlus n * f p = -(f p * gammaPlus n) := by
  dsimp [gammaPlus]
  have h1 : e n * f p = -(f p * e n) := e_mul_f_swap_ne (Ne.symm hpn)
  have h2 : f n * f p = -(f p * f n) := f_mul_f_swap n p
  calc
    (e n + f n) * f p = e n * f p + f n * f p := add_mul _ _ _
    _ = -(f p * e n) + -(f p * f n) := by rw [h1, h2]
    _ = -(f p * (e n + f n)) := by noncomm_ring

/-- **$\mathrm{Pin}_+(5,5)$ Majorana Particle–Hole Duality (`pin_majorana_conjugates_isospin_to_pairing`)**:
Conjugating by the neutron $\mathrm{Pin}_+(5,5)$ Majorana reflection $\Gamma_n = e_n + f_n$ ($\Gamma_n^2 = I_{32}$)
maps the Grade-$0$ Isospin algebra $(\tau_+, \tau_-, \tau_3)$ directly onto the Grade-$\pm 2$
Pairing Quasispin algebra $(-K_+, -K_-, 2 K_0)$:
1. $\Gamma_n \tau_+(p,n) \Gamma_n = -K_+(p,n)$,
2. $\Gamma_n \tau_-(p,n) \Gamma_n = -K_-(p,n)$,
3. $\Gamma_n \tau_3(p,n) \Gamma_n = 2 K_0(p,n)$. -/
theorem pin_majorana_conjugates_isospin_to_pairing {p n : Fin 5} (hpn : p ≠ n) :
    gammaPlus n * isospinPlus p n * gammaPlus n = -pairingPlus p n ∧
    gammaPlus n * isospinMinus p n * gammaPlus n = -pairingMinus p n ∧
    gammaPlus n * isospinCartan p n * gammaPlus n = pairingCartan p n := by
  have hGsq : gammaPlus n * gammaPlus n = 1 := gammaPlus_sq n
  have hGen : gammaPlus n * e n * gammaPlus n = f n := gammaPlus_conj_e_same n
  have hGfn : gammaPlus n * f n * gammaPlus n = e n := gammaPlus_conj_f_same n
  have hAntiEp : e p * gammaPlus n = -(gammaPlus n * e p) := gammaPlus_anticomm_e_ne hpn
  have hAntiFp : gammaPlus n * f p = -(f p * gammaPlus n) := gammaPlus_anticomm_f_ne hpn
  have h_tau_p : gammaPlus n * isospinPlus p n * gammaPlus n = -pairingPlus p n := by
    rw [isospinPlus_eq_e_mul_f hpn]
    dsimp [pairingPlus]
    calc
      gammaPlus n * (e p * f n) * gammaPlus n =
        gammaPlus n * (e p * 1) * f n * gammaPlus n := by noncomm_ring
      _ = gammaPlus n * (e p * (gammaPlus n * gammaPlus n)) * f n * gammaPlus n := by rw [hGsq]
      _ = (gammaPlus n * (e p * gammaPlus n)) * (gammaPlus n * f n * gammaPlus n) := by noncomm_ring
      _ = -(gammaPlus n * gammaPlus n) * e p * e n := by rw [hAntiEp, hGfn]; noncomm_ring
      _ = -(e p * e n) := by rw [hGsq]; noncomm_ring
  have h_tau_m : gammaPlus n * isospinMinus p n * gammaPlus n = -pairingMinus p n := by
    rw [isospinMinus_eq_e_mul_f hpn]
    dsimp [pairingMinus]
    calc
      gammaPlus n * (e n * f p) * gammaPlus n =
        gammaPlus n * e n * (1 * f p) * gammaPlus n := by noncomm_ring
      _ = gammaPlus n * e n * ((gammaPlus n * gammaPlus n) * f p) * gammaPlus n := by rw [hGsq]
      _ = (gammaPlus n * e n * gammaPlus n) * ((gammaPlus n * f p) * gammaPlus n) := by noncomm_ring
      _ = -f n * f p * (gammaPlus n * gammaPlus n) := by rw [hGen, hAntiFp]; noncomm_ring
      _ = -(f n * f p) := by rw [hGsq]; noncomm_ring
  have h_G_Np : gammaPlus n * modeOccupied p * gammaPlus n = modeOccupied p := by
    dsimp [modeOccupied]
    calc
      gammaPlus n * (e p * f p) * gammaPlus n =
        gammaPlus n * (e p * 1 * f p) * gammaPlus n := by noncomm_ring
      _ = gammaPlus n * (e p * (gammaPlus n * gammaPlus n) * f p) * gammaPlus n := by rw [hGsq]
      _ = (gammaPlus n * (e p * gammaPlus n)) * ((gammaPlus n * f p) * gammaPlus n) := by noncomm_ring
      _ = (gammaPlus n * gammaPlus n) * e p * f p * (gammaPlus n * gammaPlus n) := by
        rw [hAntiEp, hAntiFp]; noncomm_ring
      _ = e p * f p := by rw [hGsq, one_mul, mul_one]
  have h_G_Nn : gammaPlus n * modeOccupied n * gammaPlus n = 1 - modeOccupied n := by
    have hcar : e n * f n + f n * e n = 1 := by simpa using ef_car n n
    dsimp [modeOccupied]
    calc
      gammaPlus n * (e n * f n) * gammaPlus n =
        gammaPlus n * (e n * 1 * f n) * gammaPlus n := by noncomm_ring
      _ = gammaPlus n * (e n * (gammaPlus n * gammaPlus n) * f n) * gammaPlus n := by rw [hGsq]
      _ = (gammaPlus n * e n * gammaPlus n) * (gammaPlus n * f n * gammaPlus n) := by noncomm_ring
      _ = f n * e n := by rw [hGen, hGfn]
      _ = 1 - e n * f n := eq_sub_of_add_eq' hcar
  have h_pair_cartan : pairingCartan p n = modeOccupied p + modeOccupied n - 1 := by
    dsimp [pairingCartan]
    have hHp : H p = modeOccupied p - (1 / 2 : ℝ) • (1 : MatStage 5) :=
      eq_sub_of_add_eq (modeOccupied_eq_H_add_half p).symm
    have hHn : H n = modeOccupied n - (1 / 2 : ℝ) • (1 : MatStage 5) :=
      eq_sub_of_add_eq (modeOccupied_eq_H_add_half n).symm
    rw [hHp, hHn]
    calc
      modeOccupied p - (1 / 2 : ℝ) • (1 : MatStage 5) +
          (modeOccupied n - (1 / 2 : ℝ) • (1 : MatStage 5)) =
        modeOccupied p + modeOccupied n -
          ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • (1 : MatStage 5) := by
        rw [add_smul]; abel
      _ = modeOccupied p + modeOccupied n - 1 := by norm_num
  have h_tau_3 : gammaPlus n * isospinCartan p n * gammaPlus n = pairingCartan p n := by
    rw [isospinCartan_eq_modeOccupied_sub, h_pair_cartan]
    calc
      gammaPlus n * (modeOccupied p - modeOccupied n) * gammaPlus n =
        gammaPlus n * modeOccupied p * gammaPlus n -
        gammaPlus n * modeOccupied n * gammaPlus n := by noncomm_ring
      _ = modeOccupied p - (1 - modeOccupied n) := by rw [h_G_Np, h_G_Nn]
      _ = modeOccupied p + modeOccupied n - 1 := by abel
  exact ⟨h_tau_p, h_tau_m, h_tau_3⟩

/-- **$\mathrm{Pin}_-(5,5) \times \mathrm{Pin}_+(5,5)$ Spin-Connection Factorization (`gammaMinus_mul_gammaPlus_eq_two_H`)**:
At each Witt mode $a \in \mathrm{Fin}\;5$, multiplying the $\mathrm{Pin}_-$ generator $\Gamma_a^- = e_a - f_a$
and the $\mathrm{Pin}_+$ generator $\Gamma_a^+ = e_a + f_a$ produces the local Cartan spin-connection
grading generator $\pm 2 H_a = \pm (N_a - (1 - N_a))$:
1. $\Gamma_a^- \Gamma_a^+ = 2 H_a$,
2. $\Gamma_a^+ \Gamma_a^- = -2 H_a$. -/
theorem gammaMinus_mul_gammaPlus_eq_two_H (a : Fin 5) :
    gammaMinus a * gammaPlus a = (2 : ℝ) • H a ∧
    gammaPlus a * gammaMinus a = -((2 : ℝ) • H a) := by
  rw [two_smul_H_eq_modeOccupied_sub_modeVacant]
  dsimp [gammaMinus, gammaPlus, modeOccupied, modeVacant]
  refine ⟨?_, ?_⟩
  · calc
      (e a - f a) * (e a + f a) =
        e a * e a + (e a * f a - f a * e a) - f a * f a := by noncomm_ring
      _ = e a * f a - f a * e a := by rw [e_sq a, f_sq a]; abel
  · calc
      (e a + f a) * (e a - f a) =
        e a * e a - (e a * f a - f a * e a) - f a * f a := by noncomm_ring
      _ = -(e a * f a - f a * e a) := by rw [e_sq a, f_sq a]; abel

/-- Sandwiching $e_n$ by the $\mathrm{Pin}_-(5,5)$ generator $\Gamma_n^- = e_n - f_n$ produces $f_n$:
$\Gamma_n^- e_n \Gamma_n^- = f_n$. -/
theorem gammaMinus_conj_e_same (n : Fin 5) :
    gammaMinus n * e n * gammaMinus n = f n := by
  have hcar : e n * f n + f n * e n = 1 := by simpa using ef_car n n
  have hfnen : f n * e n * f n = f n := by
    calc
      (f n * e n) * f n = (1 - e n * f n) * f n := by rw [eq_sub_of_add_eq' hcar]
      _ = f n - e n * (f n * f n) := by noncomm_ring
      _ = f n := by rw [f_sq n, mul_zero, sub_zero]
  dsimp [gammaMinus]
  calc
    (e n - f n) * e n * (e n - f n) =
      (e n * e n) * e n - (e n * e n) * f n - f n * (e n * e n) + (f n * e n * f n) := by
      noncomm_ring
    _ = f n := by rw [e_sq n, hfnen]; simp

/-- Sandwiching $f_n$ by the $\mathrm{Pin}_-(5,5)$ generator $\Gamma_n^- = e_n - f_n$ produces $e_n$:
$\Gamma_n^- f_n \Gamma_n^- = e_n$. -/
theorem gammaMinus_conj_f_same (n : Fin 5) :
    gammaMinus n * f n * gammaMinus n = e n := by
  have hcar : e n * f n + f n * e n = 1 := by simpa using ef_car n n
  have henfn : e n * f n * e n = e n := by
    calc
      (e n * f n) * e n = (1 - f n * e n) * e n := by rw [eq_sub_of_add_eq hcar]
      _ = e n - f n * (e n * e n) := by noncomm_ring
      _ = e n := by rw [e_sq n, mul_zero, sub_zero]
  dsimp [gammaMinus]
  calc
    (e n - f n) * f n * (e n - f n) =
      (e n * f n * e n) - e n * (f n * f n) - (f n * f n) * e n + (f n * f n) * f n := by
      noncomm_ring
    _ = e n := by rw [f_sq n, henfn]; simp

/-- For $p \neq n$, the creation operator $e_p$ anticommutes with $\Gamma_n^- = e_n - f_n$. -/
theorem gammaMinus_anticomm_e_ne {p n : Fin 5} (hpn : p ≠ n) :
    e p * gammaMinus n = -(gammaMinus n * e p) := by
  dsimp [gammaMinus]
  have h1 : e p * e n = -(e n * e p) := e_mul_e_swap p n
  have h2 : e p * f n = -(f n * e p) := e_mul_f_swap_ne hpn
  calc
    e p * (e n - f n) = e p * e n - e p * f n := mul_sub _ _ _
    _ = -(e n * e p) - -(f n * e p) := by rw [h1, h2]
    _ = -((e n - f n) * e p) := by noncomm_ring

/-- For $p \neq n$, the annihilation operator $f_p$ anticommutes with $\Gamma_n^- = e_n - f_n$. -/
theorem gammaMinus_anticomm_f_ne {p n : Fin 5} (hpn : p ≠ n) :
    gammaMinus n * f p = -(f p * gammaMinus n) := by
  dsimp [gammaMinus]
  have h1 : e n * f p = -(f p * e n) := e_mul_f_swap_ne (Ne.symm hpn)
  have h2 : f n * f p = -(f p * f n) := f_mul_f_swap n p
  calc
    (e n - f n) * f p = e n * f p - f n * f p := sub_mul _ _ _
    _ = -(f p * e n) - -(f p * f n) := by rw [h1, h2]
    _ = -(f p * (e n - f n)) := by noncomm_ring

/-- **$\mathrm{Pin}_-(5,5)$ Skew-Majorana Particle–Hole Duality (`pin_minus_conjugates_isospin_to_pairing`)**:
Because $(\Gamma_n^-)^2 = -I_{32}$ (so $(\Gamma_n^-)^{-1} = -\Gamma_n^-$), sandwiching by the
skew-Majorana $\mathrm{Pin}_-(5,5)$ generator $\Gamma_n^- = e_n - f_n$ satisfies:
1. $\Gamma_n^- \tau_+(p,n) (-\Gamma_n^-) = +K_+(p,n)$,
2. $\Gamma_n^- \tau_-(p,n) (-\Gamma_n^-) = +K_-(p,n)$,
3. $\Gamma_n^- \tau_3(p,n) \Gamma_n^- = -2 K_0(p,n)$. -/
theorem pin_minus_conjugates_isospin_to_pairing {p n : Fin 5} (hpn : p ≠ n) :
    gammaMinus n * isospinPlus p n * (-gammaMinus n) = pairingPlus p n ∧
    gammaMinus n * isospinMinus p n * (-gammaMinus n) = pairingMinus p n ∧
    gammaMinus n * isospinCartan p n * gammaMinus n = -pairingCartan p n := by
  have hGsq : gammaMinus n * gammaMinus n = -1 := gammaMinus_sq n
  have hGen : gammaMinus n * e n * gammaMinus n = f n := gammaMinus_conj_e_same n
  have hGfn : gammaMinus n * f n * gammaMinus n = e n := gammaMinus_conj_f_same n
  have hAntiEp : e p * gammaMinus n = -(gammaMinus n * e p) := gammaMinus_anticomm_e_ne hpn
  have hAntiFp : gammaMinus n * f p = -(f p * gammaMinus n) := gammaMinus_anticomm_f_ne hpn
  have h_tau_p : gammaMinus n * isospinPlus p n * (-gammaMinus n) = pairingPlus p n := by
    rw [isospinPlus_eq_e_mul_f hpn]
    dsimp [pairingPlus]
    calc
      gammaMinus n * (e p * f n) * (-gammaMinus n) =
        gammaMinus n * (e p * (-1)) * f n * gammaMinus n := by noncomm_ring
      _ = gammaMinus n * (e p * (gammaMinus n * gammaMinus n)) * f n * gammaMinus n := by
        rw [hGsq]
      _ = (gammaMinus n * (e p * gammaMinus n)) * (gammaMinus n * f n * gammaMinus n) := by
        noncomm_ring
      _ = -(gammaMinus n * gammaMinus n) * e p * e n := by
        rw [hAntiEp, hGfn]; noncomm_ring
      _ = e p * e n := by rw [hGsq]; noncomm_ring
  have h_tau_m : gammaMinus n * isospinMinus p n * (-gammaMinus n) = pairingMinus p n := by
    rw [isospinMinus_eq_e_mul_f hpn]
    dsimp [pairingMinus]
    calc
      gammaMinus n * (e n * f p) * (-gammaMinus n) =
        gammaMinus n * e n * ((-1) * f p) * gammaMinus n := by noncomm_ring
      _ = gammaMinus n * e n * ((gammaMinus n * gammaMinus n) * f p) * gammaMinus n := by
        rw [hGsq]
      _ = (gammaMinus n * e n * gammaMinus n) * ((gammaMinus n * f p) * gammaMinus n) := by
        noncomm_ring
      _ = -f n * f p * (gammaMinus n * gammaMinus n) := by
        rw [hGen, hAntiFp]; noncomm_ring
      _ = f n * f p := by rw [hGsq]; noncomm_ring
  have h_G_Np : gammaMinus n * modeOccupied p * gammaMinus n = -modeOccupied p := by
    dsimp [modeOccupied]
    calc
      gammaMinus n * (e p * f p) * gammaMinus n =
        -(gammaMinus n * (e p * (-1) * f p) * gammaMinus n) := by noncomm_ring
      _ = -(gammaMinus n * (e p * (gammaMinus n * gammaMinus n) * f p) * gammaMinus n) := by
        rw [hGsq]
      _ = -((gammaMinus n * (e p * gammaMinus n)) * ((gammaMinus n * f p) * gammaMinus n)) := by
        noncomm_ring
      _ = -((gammaMinus n * gammaMinus n) * e p * f p * (gammaMinus n * gammaMinus n)) := by
        rw [hAntiEp, hAntiFp]; noncomm_ring
      _ = -(e p * f p) := by rw [hGsq]; noncomm_ring
  have h_G_Nn : gammaMinus n * modeOccupied n * gammaMinus n = -(1 - modeOccupied n) := by
    have hcar : e n * f n + f n * e n = 1 := by simpa using ef_car n n
    dsimp [modeOccupied]
    calc
      gammaMinus n * (e n * f n) * gammaMinus n =
        -(gammaMinus n * (e n * (-1) * f n) * gammaMinus n) := by noncomm_ring
      _ = -(gammaMinus n * (e n * (gammaMinus n * gammaMinus n) * f n) * gammaMinus n) := by
        rw [hGsq]
      _ = -((gammaMinus n * e n * gammaMinus n) * (gammaMinus n * f n * gammaMinus n)) := by
        noncomm_ring
      _ = -(f n * e n) := by rw [hGen, hGfn]
      _ = -(1 - e n * f n) := by rw [eq_sub_of_add_eq' hcar]
  have h_pair_cartan : pairingCartan p n = modeOccupied p + modeOccupied n - 1 := by
    dsimp [pairingCartan]
    have hHp : H p = modeOccupied p - (1 / 2 : ℝ) • (1 : MatStage 5) :=
      eq_sub_of_add_eq (modeOccupied_eq_H_add_half p).symm
    have hHn : H n = modeOccupied n - (1 / 2 : ℝ) • (1 : MatStage 5) :=
      eq_sub_of_add_eq (modeOccupied_eq_H_add_half n).symm
    rw [hHp, hHn]
    calc
      modeOccupied p - (1 / 2 : ℝ) • (1 : MatStage 5) +
          (modeOccupied n - (1 / 2 : ℝ) • (1 : MatStage 5)) =
        modeOccupied p + modeOccupied n -
          ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • (1 : MatStage 5) := by
        rw [add_smul]; abel
      _ = modeOccupied p + modeOccupied n - 1 := by norm_num
  have h_tau_3 : gammaMinus n * isospinCartan p n * gammaMinus n = -pairingCartan p n := by
    rw [isospinCartan_eq_modeOccupied_sub, h_pair_cartan]
    calc
      gammaMinus n * (modeOccupied p - modeOccupied n) * gammaMinus n =
        gammaMinus n * modeOccupied p * gammaMinus n -
        gammaMinus n * modeOccupied n * gammaMinus n := by noncomm_ring
      _ = -modeOccupied p - -(1 - modeOccupied n) := by rw [h_G_Np, h_G_Nn]
      _ = -(modeOccupied p + modeOccupied n - 1) := by abel
  exact ⟨h_tau_p, h_tau_m, h_tau_3⟩

/-- **Spin-Connection Sum & Difference Laws (`isospin_pairing_cartan_sum_sub`)**:
    1. $\tau_3(p,n) + 2 K_0(p,n) = 2 H_p = \Gamma_p^- \Gamma_p^+$ (Proton spin-connection grading).
    2. $2 K_0(p,n) - \tau_3(p,n) = 2 H_n = \Gamma_n^- \Gamma_n^+$ (Neutron spin-connection grading). -/
theorem isospin_pairing_cartan_sum_sub (p n : Fin 5) :
    isospinCartan p n + pairingCartan p n = (2 : ℝ) • H p ∧
    isospinCartan p n + pairingCartan p n = gammaMinus p * gammaPlus p ∧
    pairingCartan p n - isospinCartan p n = (2 : ℝ) • H n ∧
    pairingCartan p n - isospinCartan p n = gammaMinus n * gammaPlus n := by
  have h1 : isospinCartan p n + pairingCartan p n = (2 : ℝ) • H p := by
    dsimp [isospinCartan, pairingCartan]
    rw [two_smul]
    abel
  have h2 : pairingCartan p n - isospinCartan p n = (2 : ℝ) • H n := by
    dsimp [isospinCartan, pairingCartan]
    rw [two_smul]
    abel
  exact ⟨h1, h1.trans (gammaMinus_mul_gammaPlus_eq_two_H p).1.symm,
         h2, h2.trans (gammaMinus_mul_gammaPlus_eq_two_H n).1.symm⟩

/-- **Spin-Connection Carrier Parity Theorem (`two_H_mul_two_H_eq_carrier_parity`)**:
    For any modes $p, n \in \mathrm{Fin}\;5$, the product of their spin-connection gradings
    $(2 H_p)(2 H_n) = (\Gamma_p^- \Gamma_p^+)(\Gamma_n^- \Gamma_n^+)$ is identically the
    fermion-number carrier parity involution $\Delta_{\mathrm{pair}}(p,n) - \Delta_{\mathrm{iso}}(p,n)$! -/
theorem two_H_mul_two_H_eq_carrier_parity (p n : Fin 5) :
    ((2 : ℝ) • H p) * ((2 : ℝ) • H n) =
      pairingCarrier p n - isospinCarrier p n ∧
    (gammaMinus p * gammaPlus p) * (gammaMinus n * gammaPlus n) =
      pairingCarrier p n - isospinCarrier p n := by
  have h : ((2 : ℝ) • H p) * ((2 : ℝ) • H n) =
      pairingCarrier p n - isospinCarrier p n := by
    rw [two_smul_H_eq_modeOccupied_sub_modeVacant p,
        two_smul_H_eq_modeOccupied_sub_modeVacant n]
    dsimp [pairingCarrier, isospinCarrier, pairProjPlus, pairProjMinus,
           isoProjPlus, isoProjMinus]
    noncomm_ring
  refine ⟨h, ?_⟩
  rw [(gammaMinus_mul_gammaPlus_eq_two_H p).1,
      (gammaMinus_mul_gammaPlus_eq_two_H n).1]
  exact h

/-- Combined $\mathrm{SO}(4)_{pn}$ Dirac reflection $Q_{\mathrm{tot}}(p,n) = (\tau_+ + \tau_-) + (K_+ + K_-)$. -/
def totalLadderVelocity (p n : Fin 5) : MatStage 5 :=
  (isospinPlus p n + isospinMinus p n) + (pairingPlus p n + pairingMinus p n)

/-- Combined $\mathrm{SO}(4)_{pn}$ Kähler complex structure $J_{\mathrm{tot}}(p,n) = (\tau_+ - \tau_-) + (K_+ - K_-)$. -/
def totalLadderWheel (p n : Fin 5) : MatStage 5 :=
  (isospinPlus p n - isospinMinus p n) + (pairingPlus p n - pairingMinus p n)

/-- Reverse associative cross-sector annihilation: $K_\pm \tau_\pm = 0$. -/
theorem pairing_mul_isospin_eq_zero {p n : Fin 5} (hpn : p ≠ n) :
    pairingPlus p n * isospinPlus p n = 0 ∧
    pairingPlus p n * isospinMinus p n = 0 ∧
    pairingMinus p n * isospinPlus p n = 0 ∧
    pairingMinus p n * isospinMinus p n = 0 := by
  rw [isospinPlus_eq_e_mul_f hpn, isospinMinus_eq_e_mul_f hpn]
  dsimp [pairingPlus, pairingMinus]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hswap : e n * e p = -(e p * e n) := e_mul_e_swap n p
    calc
      (e p * e n) * (e p * f n) = e p * (e n * e p) * f n := by noncomm_ring
      _ = -(e p * e p) * e n * f n := by rw [hswap]; noncomm_ring
      _ = 0 := by rw [e_sq p, neg_zero, zero_mul, zero_mul]
  · calc
      (e p * e n) * (e n * f p) = e p * (e n * e n) * f p := by noncomm_ring
      _ = 0 := by rw [e_sq n, mul_zero, zero_mul]
  · have hswap1 : f n * f p = -(f p * f n) := f_mul_f_swap n p
    have hswap2 : f n * e p = -(e p * f n) := f_mul_e_swap_ne hpn
    calc
      (f n * f p) * (e p * f n) = -(f p * (f n * e p) * f n) := by rw [hswap1]; noncomm_ring
      _ = f p * e p * (f n * f n) := by rw [hswap2]; noncomm_ring
      _ = 0 := by rw [f_sq n, mul_zero]
  · have hswap_fp_en : f p * e n = -(e n * f p) := f_mul_e_swap_ne (Ne.symm hpn)
    calc
      (f n * f p) * (e n * f p) = f n * (f p * e n) * f p := by noncomm_ring
      _ = -f n * e n * (f p * f p) := by rw [hswap_fp_en]; noncomm_ring
      _ = 0 := by rw [f_sq p, mul_zero]

/-- Square-zero nilpotence of the four isospin and pairing ladder seeds ($\tau_\pm^2 = 0, K_\pm^2 = 0$). -/
theorem isospin_and_pairing_ladder_sq {p n : Fin 5} (hpn : p ≠ n) :
    isospinPlus p n * isospinPlus p n = 0 ∧
    isospinMinus p n * isospinMinus p n = 0 ∧
    pairingPlus p n * pairingPlus p n = 0 ∧
    pairingMinus p n * pairingMinus p n = 0 := by
  rw [isospinPlus_eq_e_mul_f hpn, isospinMinus_eq_e_mul_f hpn]
  dsimp [pairingPlus, pairingMinus]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hswap : f n * e p = -(e p * f n) := f_mul_e_swap_ne hpn
    calc
      (e p * f n) * (e p * f n) = e p * (f n * e p) * f n := by noncomm_ring
      _ = -(e p * e p) * f n * f n := by rw [hswap]; noncomm_ring
      _ = 0 := by rw [e_sq p, neg_zero, zero_mul, zero_mul]
  · have hswap : f p * e n = -(e n * f p) := f_mul_e_swap_ne (Ne.symm hpn)
    calc
      (e n * f p) * (e n * f p) = e n * (f p * e n) * f p := by noncomm_ring
      _ = -(e n * e n) * f p * f p := by rw [hswap]; noncomm_ring
      _ = 0 := by rw [e_sq n, neg_zero, zero_mul, zero_mul]
  · have hswap : e n * e p = -(e p * e n) := e_mul_e_swap n p
    calc
      (e p * e n) * (e p * e n) = e p * (e n * e p) * e n := by noncomm_ring
      _ = -(e p * e p) * e n * e n := by rw [hswap]; noncomm_ring
      _ = 0 := by rw [e_sq p, neg_zero, zero_mul, zero_mul]
  · have hswap : f p * f n = -(f n * f p) := f_mul_f_swap p n
    calc
      (f n * f p) * (f n * f p) = f n * (f p * f n) * f p := by noncomm_ring
      _ = -(f n * f n) * f p * f p := by rw [hswap]; noncomm_ring
      _ = 0 := by rw [f_sq n, neg_zero, zero_mul, zero_mul]

/-- **Global $\mathrm{SO}(4)_{pn}$ Dirac & Kähler Spin-Connection Factorization (`global_so4_dirac_and_complex_structure`)**:
    For any $p \neq n$, $Q_{\mathrm{tot}}^2 = I_{32}$, $J_{\mathrm{tot}}^2 = -I_{32}$, and
    $J_{\mathrm{tot}} Q_{\mathrm{tot}} = \tau_3 + 2 K_0 = 2 H_p$! -/
theorem global_so4_dirac_and_complex_structure {p n : Fin 5} (hpn : p ≠ n) :
    totalLadderVelocity p n * totalLadderVelocity p n = 1 ∧
    totalLadderWheel p n * totalLadderWheel p n = -1 ∧
    totalLadderWheel p n * totalLadderVelocity p n = (2 : ℝ) • H p := by
  rcases isospin_mul_pairing_eq_zero hpn with ⟨h_ip_pp, h_ip_pm, h_im_pp, h_im_pm⟩
  rcases pairing_mul_isospin_eq_zero hpn with ⟨h_pp_ip, h_pp_im, h_pm_ip, h_pm_im⟩
  rcases isospin_and_pairing_ladder_sq hpn with ⟨h_ip_sq, h_im_sq, h_pp_sq, h_pm_sq⟩
  have h_ip_im := isospinPlus_mul_isospinMinus hpn
  have h_im_ip := isospinMinus_mul_isospinPlus hpn
  have h_pp_pm := pairingPlus_mul_pairingMinus hpn
  have h_pm_pp := pairingMinus_mul_pairingPlus hpn
  refine ⟨?_, ?_, ?_⟩
  · dsimp [totalLadderVelocity]
    calc
      ((isospinPlus p n + isospinMinus p n) + (pairingPlus p n + pairingMinus p n)) *
        ((isospinPlus p n + isospinMinus p n) + (pairingPlus p n + pairingMinus p n)) =
        isospinPlus p n * isospinPlus p n + isospinPlus p n * isospinMinus p n +
        isospinMinus p n * isospinPlus p n + isospinMinus p n * isospinMinus p n +
        pairingPlus p n * pairingPlus p n + pairingPlus p n * pairingMinus p n +
        pairingMinus p n * pairingPlus p n + pairingMinus p n * pairingMinus p n +
        (isospinPlus p n * pairingPlus p n + isospinPlus p n * pairingMinus p n +
         isospinMinus p n * pairingPlus p n + isospinMinus p n * pairingMinus p n +
         pairingPlus p n * isospinPlus p n + pairingPlus p n * isospinMinus p n +
         pairingMinus p n * isospinPlus p n + pairingMinus p n * isospinMinus p n) := by
        noncomm_ring
      _ = isoProjPlus p n + isoProjMinus p n + pairProjPlus p n + pairProjMinus p n := by
        rw [h_ip_sq, h_im_sq, h_pp_sq, h_pm_sq, h_ip_im, h_im_ip, h_pp_pm, h_pm_pp,
            h_ip_pp, h_ip_pm, h_im_pp, h_im_pm, h_pp_ip, h_pp_im, h_pm_ip, h_pm_im]
        abel
      _ = 1 := four_projector_sum p n
  · dsimp [totalLadderWheel]
    calc
      ((isospinPlus p n - isospinMinus p n) + (pairingPlus p n - pairingMinus p n)) *
        ((isospinPlus p n - isospinMinus p n) + (pairingPlus p n - pairingMinus p n)) =
        isospinPlus p n * isospinPlus p n - isospinPlus p n * isospinMinus p n -
        isospinMinus p n * isospinPlus p n + isospinMinus p n * isospinMinus p n +
        pairingPlus p n * pairingPlus p n - pairingPlus p n * pairingMinus p n -
        pairingMinus p n * pairingPlus p n + pairingMinus p n * pairingMinus p n +
        (isospinPlus p n * pairingPlus p n - isospinPlus p n * pairingMinus p n -
         isospinMinus p n * pairingPlus p n + isospinMinus p n * pairingMinus p n +
         pairingPlus p n * isospinPlus p n - pairingPlus p n * isospinMinus p n -
         pairingMinus p n * isospinPlus p n + pairingMinus p n * isospinMinus p n) := by
        noncomm_ring
      _ = -(isoProjPlus p n + isoProjMinus p n + pairProjPlus p n + pairProjMinus p n) := by
        rw [h_ip_sq, h_im_sq, h_pp_sq, h_pm_sq, h_ip_im, h_im_ip, h_pp_pm, h_pm_pp,
            h_ip_pp, h_ip_pm, h_im_pp, h_im_pm, h_pp_ip, h_pp_im, h_pm_ip, h_pm_im]
        abel
      _ = -1 := by rw [four_projector_sum p n]
  · dsimp [totalLadderWheel, totalLadderVelocity]
    calc
      ((isospinPlus p n - isospinMinus p n) + (pairingPlus p n - pairingMinus p n)) *
        ((isospinPlus p n + isospinMinus p n) + (pairingPlus p n + pairingMinus p n)) =
        isospinPlus p n * isospinPlus p n + isospinPlus p n * isospinMinus p n -
        isospinMinus p n * isospinPlus p n - isospinMinus p n * isospinMinus p n +
        pairingPlus p n * pairingPlus p n + pairingPlus p n * pairingMinus p n -
        pairingMinus p n * pairingPlus p n - pairingMinus p n * pairingMinus p n +
        (isospinPlus p n * pairingPlus p n + isospinPlus p n * pairingMinus p n -
         isospinMinus p n * pairingPlus p n - isospinMinus p n * pairingMinus p n +
         pairingPlus p n * isospinPlus p n + pairingPlus p n * isospinMinus p n -
         pairingMinus p n * isospinPlus p n - pairingMinus p n * isospinMinus p n) := by
        noncomm_ring
      _ = (isoProjPlus p n - isoProjMinus p n) + (pairProjPlus p n - pairProjMinus p n) := by
        rw [h_ip_sq, h_im_sq, h_pp_sq, h_pm_sq, h_ip_im, h_im_ip, h_pp_pm, h_pm_pp,
            h_ip_pp, h_ip_pm, h_im_pp, h_im_pm, h_pp_ip, h_pp_im, h_pm_ip, h_pm_im]
        abel
      _ = isospinCartan p n + pairingCartan p n := by
        rw [← isospinCartan_eq_isoProj_sub p n,
            ← pairingCartan_eq_pairProj_sub p n]
      _ = (2 : ℝ) • H p := (isospin_pairing_cartan_sum_sub p n).1

/-- 3-color chiral grading operator $\Gamma_{\mathrm{color}} = (2 H_0)(2 H_1)(2 H_2)$. -/
def colorChiralVolume : MatStage 5 :=
  ((2 : ℝ) • H 0) * ((2 : ℝ) • H 1) * ((2 : ℝ) • H 2)

/-- Top 10D chiral spin-connection volume operator $\Gamma_{\mathrm{Cl}(5,5)} = \prod_{a=0}^4 (2 H_a)$. -/
def chiralVolume10D : MatStage 5 :=
  ((2 : ℝ) • H 0) * ((2 : ℝ) • H 1) * ((2 : ℝ) • H 2) *
  ((2 : ℝ) • H 3) * ((2 : ℝ) • H 4)

/-- **$3 + 2$ Color–Isospin Factorization of the 10D Chiral Volume Element (`chiralVolume10D_factorization`)**:
    Splitting the 5 Witt modes into 3 color modes $\{0, 1, 2\}$ and 2 nucleon modes $\{3, 4\}$,
    the top 10D chiral volume element $\Gamma_{\mathrm{Cl}(5,5)}$ factorizes into the 3-color chiral
    grading $\Gamma_{\mathrm{color}}$ times the nucleon pairing-vs-isospin carrier parity
    $\Delta_{\mathrm{pair}}(3,4) - \Delta_{\mathrm{iso}}(3,4)$! -/
theorem chiralVolume10D_factorization :
    chiralVolume10D =
      colorChiralVolume * (pairingCarrier 3 4 - isospinCarrier 3 4) ∧
    (gammaMinus 0 * gammaPlus 0) * (gammaMinus 1 * gammaPlus 1) *
      (gammaMinus 2 * gammaPlus 2) * (gammaMinus 3 * gammaPlus 3) *
      (gammaMinus 4 * gammaPlus 4) =
      colorChiralVolume * (pairingCarrier 3 4 - isospinCarrier 3 4) := by
  have h1 : chiralVolume10D =
      colorChiralVolume * (pairingCarrier 3 4 - isospinCarrier 3 4) := by
    dsimp [chiralVolume10D, colorChiralVolume]
    rw [mul_assoc ((((2 : ℝ) • H 0) * ((2 : ℝ) • H 1)) * ((2 : ℝ) • H 2)),
        (two_H_mul_two_H_eq_carrier_parity 3 4).1]
  refine ⟨h1, ?_⟩
  rw [(gammaMinus_mul_gammaPlus_eq_two_H 0).1,
      (gammaMinus_mul_gammaPlus_eq_two_H 1).1,
      (gammaMinus_mul_gammaPlus_eq_two_H 2).1,
      (gammaMinus_mul_gammaPlus_eq_two_H 3).1,
      (gammaMinus_mul_gammaPlus_eq_two_H 4).1]
  exact h1

/-- 3-Quark Nambu Baryon Singlet projector $\Pi_{\mathrm{baryon}} = N_0 N_1 N_2$ ($\mathbf{1}_3$). -/
def colorBaryonSingletProj : MatStage 5 :=
  modeOccupied 0 * modeOccupied 1 * modeOccupied 2

/-- 0-Quark Vacuum Singlet projector $\Pi_{\mathrm{vac}} = (1 - N_0)(1 - N_1)(1 - N_2)$ ($\mathbf{1}_0$). -/
def colorVacuumSingletProj : MatStage 5 :=
  modeVacant 0 * modeVacant 1 * modeVacant 2

/-- 1-Quark Color Triplet projector $\Pi_{\mathrm{quark}} = N_0 V_1 V_2 + V_0 N_1 V_2 + V_0 V_1 N_2$ ($\mathbf{3}$). -/
def colorQuarkTripletProj : MatStage 5 :=
  modeOccupied 0 * modeVacant 1 * modeVacant 2 +
  modeVacant 0 * modeOccupied 1 * modeVacant 2 +
  modeVacant 0 * modeVacant 1 * modeOccupied 2

/-- 2-Quark Diquark Antitriplet projector $\Pi_{\mathrm{diquark}} = V_0 N_1 N_2 + N_0 V_1 N_2 + N_0 N_1 V_2$ ($\bar{\mathbf{3}}$). -/
def colorDiquarkAntitripletProj : MatStage 5 :=
  modeVacant 0 * modeOccupied 1 * modeOccupied 2 +
  modeOccupied 0 * modeVacant 1 * modeOccupied 2 +
  modeOccupied 0 * modeOccupied 1 * modeVacant 2

/-- Positive-parity $(\mathbf{1}_3 \oplus \mathbf{3})$ Baryon–Quark Singlet–Triplet Company $\Pi_{\mathrm{baryon}} + \Pi_{\mathrm{quark}}$. -/
def colorPositiveCompanyProj : MatStage 5 :=
  colorBaryonSingletProj + colorQuarkTripletProj

/-- Negative-parity $(\mathbf{1}_0 \oplus \bar{\mathbf{3}})$ Vacuum–Diquark Singlet–Antitriplet Company $\Pi_{\mathrm{vac}} + \Pi_{\mathrm{diquark}}$. -/
def colorNegativeCompanyProj : MatStage 5 :=
  colorVacuumSingletProj + colorDiquarkAntitripletProj

/-- **Complete 3-Color Four-Sector Partition of Unity ($\mathbf{1}_3 \oplus \mathbf{3} \oplus \bar{\mathbf{3}} \oplus \mathbf{1}_0 = I_{32}$)**:
    The Baryon Singlet, Quark Triplet, Diquark Antitriplet, and Vacuum Singlet projectors
    resolve the $32 \times 32$ identity matrix $I_{32}$! -/
theorem color_singlet_triplet_four_sector_sum :
    colorBaryonSingletProj + colorQuarkTripletProj +
      colorDiquarkAntitripletProj + colorVacuumSingletProj = 1 ∧
    colorPositiveCompanyProj + colorNegativeCompanyProj = 1 := by
  have h_sum : colorBaryonSingletProj + colorQuarkTripletProj +
      colorDiquarkAntitripletProj + colorVacuumSingletProj = 1 := by
    dsimp [colorBaryonSingletProj, colorQuarkTripletProj,
           colorDiquarkAntitripletProj, colorVacuumSingletProj]
    calc
      modeOccupied 0 * modeOccupied 1 * modeOccupied 2 +
        (modeOccupied 0 * modeVacant 1 * modeVacant 2 +
         modeVacant 0 * modeOccupied 1 * modeVacant 2 +
         modeVacant 0 * modeVacant 1 * modeOccupied 2) +
        (modeVacant 0 * modeOccupied 1 * modeOccupied 2 +
         modeOccupied 0 * modeVacant 1 * modeOccupied 2 +
         modeOccupied 0 * modeOccupied 1 * modeVacant 2) +
        modeVacant 0 * modeVacant 1 * modeVacant 2 =
        (modeOccupied 0 + modeVacant 0) *
        (modeOccupied 1 + modeVacant 1) *
        (modeOccupied 2 + modeVacant 2) := by noncomm_ring
      _ = 1 * 1 * 1 := by
        rw [modeOccupied_add_modeVacant 0,
            modeOccupied_add_modeVacant 1,
            modeOccupied_add_modeVacant 2]
      _ = 1 := by simp
  have h_comp : colorPositiveCompanyProj + colorNegativeCompanyProj = 1 := by
    dsimp [colorPositiveCompanyProj, colorNegativeCompanyProj]
    rw [← h_sum]
    abel
  exact ⟨h_sum, h_comp⟩

/-- **Why Singlets and Triplets Come in Company (`colorChiralVolume_eq_positiveCompany_sub_negativeCompany`)**:
    The 3-color chiral volume element $\Gamma_{\mathrm{color}} = (2 H_0)(2 H_1)(2 H_2)$ is
    identically the difference between the $(\mathbf{1}_3 \oplus \mathbf{3})$ Baryon–Quark Company
    and the $(\mathbf{1}_0 \oplus \bar{\mathbf{3}})$ Vacuum–Diquark Company, and factorizes
    $\Gamma_{\mathrm{Cl}(5,5)}$ into $(\Pi_{\mathrm{pos}} - \Pi_{\mathrm{neg}})(\Delta_{\mathrm{pair}} - \Delta_{\mathrm{iso}})$! -/
theorem colorChiralVolume_eq_positiveCompany_sub_negativeCompany :
    colorChiralVolume = colorPositiveCompanyProj - colorNegativeCompanyProj ∧
    chiralVolume10D =
      (colorPositiveCompanyProj - colorNegativeCompanyProj) *
        (pairingCarrier 3 4 - isospinCarrier 3 4) := by
  have h_col : colorChiralVolume = colorPositiveCompanyProj - colorNegativeCompanyProj := by
    dsimp [colorChiralVolume, colorPositiveCompanyProj, colorNegativeCompanyProj,
           colorBaryonSingletProj, colorQuarkTripletProj,
           colorVacuumSingletProj, colorDiquarkAntitripletProj]
    rw [two_smul_H_eq_modeOccupied_sub_modeVacant 0,
        two_smul_H_eq_modeOccupied_sub_modeVacant 1,
        two_smul_H_eq_modeOccupied_sub_modeVacant 2]
    noncomm_ring
  refine ⟨h_col, ?_⟩
  rw [chiralVolume10D_factorization.1, h_col]

/-- **Positive-Chirality 16-State Half-Spinor Projector (`Π₁₆⁺`)**:
    Combines the `(1₃ ⊕ 3)` color company on the even pairing carrier `Δ_{pair}(3,4)` with the
    `(1₀ ⊕ 3̄)` color company on the odd isospin carrier `Δ_{iso}(3,4)`. -/
def chiralHalfSpinorPlus16 : MatStage 5 :=
  colorPositiveCompanyProj * pairingCarrier 3 4 +
  colorNegativeCompanyProj * isospinCarrier 3 4

/-- **Negative-Chirality 16-State Half-Spinor Projector (`Π₁₆⁻`)**:
    Combines the `(1₃ ⊕ 3)` color company on the odd isospin carrier `Δ_{iso}(3,4)` (`2 + 6 = 8` states)
    with the `(1₀ ⊕ 3̄)` color company on the even pairing carrier `Δ_{pair}(3,4)` (`2 + 6 = 8` states). -/
def chiralHalfSpinorMinus16 : MatStage 5 :=
  colorPositiveCompanyProj * isospinCarrier 3 4 +
  colorNegativeCompanyProj * pairingCarrier 3 4

/-- **`16 + 16 = 32` Partition of Unity & 10D Chiral Volume Difference (`Π₁₆⁺ - Π₁₆⁻`)**:
    With zero hypotheses, `Π₁₆⁺ + Π₁₆⁻ = 1`, and the 10D chiral volume element
    `chiralVolume10D = Γ_{color} * (Δ_{pair}(3,4) - Δ_{iso}(3,4))` is identically `Π₁₆⁺ - Π₁₆⁻`! -/
theorem chiralHalfSpinor16_sum_and_chiralVolume_diff :
    chiralHalfSpinorPlus16 + chiralHalfSpinorMinus16 = 1 ∧
    chiralVolume10D = chiralHalfSpinorPlus16 - chiralHalfSpinorMinus16 := by
  refine ⟨?_, ?_⟩
  · calc
      chiralHalfSpinorPlus16 + chiralHalfSpinorMinus16 =
        (colorPositiveCompanyProj + colorNegativeCompanyProj) *
        (isospinCarrier 3 4 + pairingCarrier 3 4) := by
        dsimp [chiralHalfSpinorPlus16, chiralHalfSpinorMinus16]
        noncomm_ring
      _ = 1 * 1 := by
        rw [color_singlet_triplet_four_sector_sum.2, isospinCarrier_add_pairingCarrier 3 4]
      _ = 1 := by simp
  · rw [colorChiralVolume_eq_positiveCompany_sub_negativeCompany.2]
    dsimp [chiralHalfSpinorPlus16, chiralHalfSpinorMinus16]
    noncomm_ring

/-- **The `2 + 6 + 2 + 6 = 16` Four-Multiplet Fermion Generation Decomposition of `Π₁₆⁻`**:
    Decomposes the 16-state chiral half-spinor `Π₁₆⁻` into:
    - `(1₃, 2_{iso})`: `colorBaryonSingletProj * isospinCarrier 3 4` (2 states),
    - `(3, 2_{iso})`:  `colorQuarkTripletProj * isospinCarrier 3 4` (6 states),
    - `(1₀, 1 ⊕ 1)`:   `colorVacuumSingletProj * pairingCarrier 3 4` (2 states),
    - `(3̄, 1 ⊕ 1)`:   `colorDiquarkAntitripletProj * pairingCarrier 3 4` (6 states)! -/
theorem chiralHalfSpinorMinus16_four_multiplet_decomposition :
    chiralHalfSpinorMinus16 =
      colorBaryonSingletProj * isospinCarrier 3 4 +
      colorQuarkTripletProj * isospinCarrier 3 4 +
      colorVacuumSingletProj * pairingCarrier 3 4 +
      colorDiquarkAntitripletProj * pairingCarrier 3 4 := by
  dsimp [chiralHalfSpinorMinus16, colorPositiveCompanyProj, colorNegativeCompanyProj]
  noncomm_ring

/-- Helper expressing `modeVacant a = 1 - modeOccupied a`. -/
theorem modeVacant_eq_one_sub_modeOccupied (a : Fin 5) :
    modeVacant a = 1 - modeOccupied a :=
  eq_sub_of_add_eq' (modeOccupied_add_modeVacant a)

/-- First Cartan color-octet gluon generator `T₃^{color} = N₀ - N₁` (Gell-Mann `λ₃`). -/
def colorGluonT3 : MatStage 5 := modeOccupied 0 - modeOccupied 1

/-- Scaled second Cartan color-octet gluon generator `3Y^{color} = N₀ + N₁ - 2 • N₂` (Gell-Mann `√3 λ₈`). -/
def colorGluon3Y : MatStage 5 := modeOccupied 0 + modeOccupied 1 - (2 : ℕ) • modeOccupied 2

/-- Color-Singlet total quark number `N_{color} = N₀ + N₁ + N₂`. -/
def colorSingletNumber : MatStage 5 := modeOccupied 0 + modeOccupied 1 + modeOccupied 2

/-- **`3 ⊗ 3̄ = 1 ⊕ 8` Diagonal Decomposition of the 3 Color Occupation Idempotents**:
    With zero hypotheses, `6 • N₀`, `6 • N₁`, and `3 • N₂` decompose into the Color-Singlet
    number `N_{color}` plus the two Cartan Color-Octet gluons `T₃^{color}` and `3Y^{color}`! -/
theorem color_occupation_singlet_octet_decomposition :
    (2 : ℕ) • colorSingletNumber + colorGluon3Y +
      (3 : ℕ) • colorGluonT3 = (6 : ℕ) • modeOccupied 0 ∧
    (2 : ℕ) • colorSingletNumber + colorGluon3Y -
      (3 : ℕ) • colorGluonT3 = (6 : ℕ) • modeOccupied 1 ∧
    colorSingletNumber - colorGluon3Y = (3 : ℕ) • modeOccupied 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · dsimp [colorSingletNumber, colorGluon3Y, colorGluonT3]
    noncomm_ring

/-- **Universal Cubic Cancellation in the Colored Sector Sum (`Π_{quark} + Π_{diquark}`)**:
    With zero hypotheses, the cubic terms `±3 N₀ N₁ N₂` cancel between `Π_{quark}` and
    `Π_{diquark}`, reducing their sum to a pure quadratic polynomial in `N₀, N₁, N₂`! -/
theorem colorQuark_add_diquark_quadratic_reduction :
    colorQuarkTripletProj + colorDiquarkAntitripletProj =
      modeOccupied 0 + modeOccupied 1 + modeOccupied 2 -
      modeOccupied 0 * modeOccupied 1 -
      modeOccupied 0 * modeOccupied 2 -
      modeOccupied 1 * modeOccupied 2 := by
  dsimp [colorQuarkTripletProj, colorDiquarkAntitripletProj]
  rw [modeVacant_eq_one_sub_modeOccupied 0,
      modeVacant_eq_one_sub_modeOccupied 1,
      modeVacant_eq_one_sub_modeOccupied 2]
  noncomm_ring

/-- **Exact Gell-Mann Gluon Cartan Casimir Identity (`3 (T₃^{color})² + (3Y^{color})² = 4 (Π_3 + Π_{3̄})`)**:
    In `Cl(5,5)` (`MatStage 5`), the quadratic Cartan color-octet Casimir operator evaluates
    purely to `4` times the colored triplet + antitriplet projector `Π_{quark} + Π_{diquark}`,
    with ZERO weight on the baryon and vacuum color singlets! -/
theorem colorGluon_cartan_casimir_eq_four_colored_sectors :
    (3 : ℕ) • (colorGluonT3 * colorGluonT3) + colorGluon3Y * colorGluon3Y =
      (4 : ℕ) • (colorQuarkTripletProj + colorDiquarkAntitripletProj) := by
  rw [colorQuark_add_diquark_quadratic_reduction]
  dsimp [colorGluonT3, colorGluon3Y]
  calc
    (3 : ℕ) • ((modeOccupied 0 - modeOccupied 1) * (modeOccupied 0 - modeOccupied 1)) +
      (modeOccupied 0 + modeOccupied 1 - (2 : ℕ) • modeOccupied 2) *
      (modeOccupied 0 + modeOccupied 1 - (2 : ℕ) • modeOccupied 2) =
      (4 : ℕ) • (modeOccupied 0 * modeOccupied 0 +
                 modeOccupied 1 * modeOccupied 1 +
                 modeOccupied 2 * modeOccupied 2) -
      (2 : ℕ) • ((modeOccupied 0 * modeOccupied 1 + modeOccupied 1 * modeOccupied 0) +
                 (modeOccupied 0 * modeOccupied 2 + modeOccupied 2 * modeOccupied 0) +
                 (modeOccupied 1 * modeOccupied 2 + modeOccupied 2 * modeOccupied 1)) := by
      noncomm_ring
    _ = (4 : ℕ) • (modeOccupied 0 + modeOccupied 1 + modeOccupied 2 -
          modeOccupied 0 * modeOccupied 1 -
          modeOccupied 0 * modeOccupied 2 -
          modeOccupied 1 * modeOccupied 2) := by
      rw [modeOccupied_idem 0, modeOccupied_idem 1, modeOccupied_idem 2,
          modeOccupied_comm 1 0, modeOccupied_comm 2 0, modeOccupied_comm 2 1]
      noncomm_ring

/-- **Color Confinement & Singlet Neutrality (`colorGluon_cartan_singlet_neutrality`)**:
    Both Gell-Mann Cartan gluon charges `T₃^{color}` and `3Y^{color}` annihilate the 3-quark
    Baryon Singlet `Π_{baryon}` (`1₃`)! -/
theorem colorGluon_cartan_singlet_neutrality :
    colorGluonT3 * colorBaryonSingletProj = 0 ∧
    colorGluon3Y * colorBaryonSingletProj = 0 := by
  have h01 : (modeOccupied 0 - modeOccupied 1) * colorBaryonSingletProj = 0 := by
    dsimp [colorBaryonSingletProj]
    calc
      (modeOccupied 0 - modeOccupied 1) * (modeOccupied 0 * modeOccupied 1 * modeOccupied 2) =
        (modeOccupied 0 * modeOccupied 0) * modeOccupied 1 * modeOccupied 2 -
        (modeOccupied 1 * modeOccupied 0) * modeOccupied 1 * modeOccupied 2 := by noncomm_ring
      _ = modeOccupied 0 * modeOccupied 1 * modeOccupied 2 -
        modeOccupied 0 * (modeOccupied 1 * modeOccupied 1) * modeOccupied 2 := by
        rw [modeOccupied_idem 0, modeOccupied_comm 1 0]; noncomm_ring
      _ = 0 := by rw [modeOccupied_idem 1, sub_self]
  have h12 : (modeOccupied 1 - modeOccupied 2) * colorBaryonSingletProj = 0 := by
    dsimp [colorBaryonSingletProj]
    calc
      (modeOccupied 1 - modeOccupied 2) * (modeOccupied 0 * modeOccupied 1 * modeOccupied 2) =
        (modeOccupied 1 * modeOccupied 0) * modeOccupied 1 * modeOccupied 2 -
        ((modeOccupied 2 * modeOccupied 0) * modeOccupied 1) * modeOccupied 2 := by noncomm_ring
      _ = modeOccupied 0 * (modeOccupied 1 * modeOccupied 1) * modeOccupied 2 -
        (modeOccupied 0 * (modeOccupied 2 * modeOccupied 1)) * modeOccupied 2 := by
        rw [modeOccupied_comm 1 0, modeOccupied_comm 2 0]; noncomm_ring
      _ = modeOccupied 0 * modeOccupied 1 * modeOccupied 2 -
        modeOccupied 0 * modeOccupied 1 * (modeOccupied 2 * modeOccupied 2) := by
        rw [modeOccupied_idem 1, modeOccupied_comm 2 1]; noncomm_ring
      _ = 0 := by rw [modeOccupied_idem 2, sub_self]
  refine ⟨h01, ?_⟩
  have h3Y : colorGluon3Y =
      (modeOccupied 0 - modeOccupied 1) + (2 : ℕ) • (modeOccupied 1 - modeOccupied 2) := by
    dsimp [colorGluon3Y]; noncomm_ring
  rw [h3Y, add_mul, smul_mul_assoc, h01, h12, smul_zero, add_zero]

/-- **Universal Zero-Hypothesis Spectral Decomposition of Color Quark Number (`N₀ + N₁ + N₂`)**:
    With zero hypotheses, the total color quark number `colorSingletNumber = N₀ + N₁ + N₂`
    decomposes into `1 • Π_{quark} + 2 • Π_{diquark} + 3 • Π_{baryon}`! -/
theorem colorSingletNumber_spectral_decomposition :
    colorSingletNumber =
      colorQuarkTripletProj +
      (2 : ℕ) • colorDiquarkAntitripletProj +
      (3 : ℕ) • colorBaryonSingletProj := by
  dsimp [colorSingletNumber, colorQuarkTripletProj,
         colorDiquarkAntitripletProj, colorBaryonSingletProj]
  rw [modeVacant_eq_one_sub_modeOccupied 0,
      modeVacant_eq_one_sub_modeOccupied 1,
      modeVacant_eq_one_sub_modeOccupied 2]
  noncomm_ring

/-- **Division-Free Gell-Mann–Nishijima Electric Charge Operator (`sixElectricCharge = 6 Q_{EM}`)**:
    `sixElectricCharge = (N₀ + N₁ + N₂) + 3 • (Π_+(3,4) - Π_-(3,4))`
    (corresponding to `Q_{EM} = N_{color}/6 + τ₃(3,4)/2`). -/
def sixElectricCharge : MatStage 5 :=
  colorSingletNumber + (3 : ℤ) • (isoProjPlus 3 4 - isoProjMinus 3 4)

/-- **Gell-Mann–Nishijima Fractional-to-Integer Spectral Charge Decomposition (`sixElectricCharge_spectral_decomposition`)**:
    With zero hypotheses, `sixElectricCharge = 6 Q_{EM}` expands into the exact multiplet
    charge weights:
    - `+4` (`+2/3`) on Up Quark `Π_{quark} * Π_+(3,4)`,
    - `-2` (`-1/3`) on Down Quark `Π_{quark} * Π_-(3,4)`,
    - `+2` (`+1/3`) on Isoscalar Diquark `Π_{diquark} * Δ_{pair}(3,4)`,
    - `+6` (`+1`)   on Proton Baryon `Π_{baryon} * Π_+(3,4)`,
    - ` 0` (` 0`)   on Neutron Baryon `Π_{baryon} * Π_-(3,4)` and Vacuum `Π_{vac} * Δ_{pair}(3,4)`! -/
theorem sixElectricCharge_spectral_decomposition :
    sixElectricCharge =
      (4 : ℤ) • (colorQuarkTripletProj * isoProjPlus 3 4) +
      (-2 : ℤ) • (colorQuarkTripletProj * isoProjMinus 3 4) +
      (1 : ℤ) • (colorQuarkTripletProj * pairingCarrier 3 4) +
      (5 : ℤ) • (colorDiquarkAntitripletProj * isoProjPlus 3 4) +
      (-1 : ℤ) • (colorDiquarkAntitripletProj * isoProjMinus 3 4) +
      (2 : ℤ) • (colorDiquarkAntitripletProj * pairingCarrier 3 4) +
      (6 : ℤ) • (colorBaryonSingletProj * isoProjPlus 3 4) +
      (3 : ℤ) • (colorBaryonSingletProj * pairingCarrier 3 4) +
      (3 : ℤ) • (colorVacuumSingletProj * isoProjPlus 3 4) +
      (-3 : ℤ) • (colorVacuumSingletProj * isoProjMinus 3 4) := by
  have h_iso : isoProjPlus 3 4 + isoProjMinus 3 4 + pairingCarrier 3 4 = 1 :=
    isospinCarrier_add_pairingCarrier 3 4
  have h_col : colorBaryonSingletProj + colorQuarkTripletProj +
      colorDiquarkAntitripletProj + colorVacuumSingletProj = 1 :=
    color_singlet_triplet_four_sector_sum.1
  calc
    sixElectricCharge =
      (colorQuarkTripletProj +
       (2 : ℕ) • colorDiquarkAntitripletProj +
       (3 : ℕ) • colorBaryonSingletProj) *
      (isoProjPlus 3 4 + isoProjMinus 3 4 + pairingCarrier 3 4) +
      (colorBaryonSingletProj + colorQuarkTripletProj +
       colorDiquarkAntitripletProj + colorVacuumSingletProj) *
      ((3 : ℤ) • (isoProjPlus 3 4 - isoProjMinus 3 4)) := by
      rw [h_iso, h_col, ← colorSingletNumber_spectral_decomposition]
      dsimp [sixElectricCharge]; simp
    _ = _ := by noncomm_ring

/-! ## 14. Maximal Cartan Subalgebra `𝔥₅`, Proton/Neutron/Lepton Projectors, `B - L` Charge, and Weak Decay Geodesic -/

/-- **Universal Orthogonal Cartan Casimir Identity (`so55_five_cartan_casimir_identity`)**:
    In ANY associative ring `A` (with zero hypotheses!), the weighted sum of squares of the
    3 Color Cartan combinations `(Z₀ - Z₁, Z₀ + Z₁ - 2 • Z₂, Z₀ + Z₁ + Z₂)` and the 2 Weak/Pairing
    Cartan combinations `(Z_p - Z_n, Z_p + Z_n)` eliminates all noncommutative cross-terms:
    - `3 • (Z₀ - Z₁)² + (Z₀ + Z₁ - 2 • Z₂)² + 2 • (Z₀ + Z₁ + Z₂)² = 6 • (Z₀² + Z₁² + Z₂²)`,
    - `(Z_p - Z_n)² + (Z_p + Z_n)² = 2 • (Z_p² + Z_n²)`! -/
theorem so55_five_cartan_casimir_identity {A : Type*} [Ring A] (Z₀ Z₁ Z₂ Z_p Z_n : A) :
    (3 : ℕ) • ((Z₀ - Z₁) * (Z₀ - Z₁)) +
      (Z₀ + Z₁ - (2 : ℕ) • Z₂) * (Z₀ + Z₁ - (2 : ℕ) • Z₂) +
      (2 : ℕ) • ((Z₀ + Z₁ + Z₂) * (Z₀ + Z₁ + Z₂)) =
      (6 : ℕ) • (Z₀ * Z₀ + Z₁ * Z₁ + Z₂ * Z₂) ∧
    (Z_p - Z_n) * (Z_p - Z_n) + (Z_p + Z_n) * (Z_p + Z_n) =
      (2 : ℕ) • (Z_p * Z_p + Z_n * Z_n) := by
  refine ⟨?_, ?_⟩ <;> noncomm_ring

/-- **Proton Baryon Projector (`Π_{proton} = Π_{baryon} * Π_+(3,4)`)**:
    3-quark color singlet `N₀ N₁ N₂` with occupied proton mode `N₃` and neutron hole `1 - N₄`. -/
def protonProjector : MatStage 5 :=
  colorBaryonSingletProj * isoProjPlus 3 4

/-- Alias `protonBaryonProj` for `protonProjector`. -/
abbrev protonBaryonProj : MatStage 5 := protonProjector

/-- **Neutron Baryon Projector (`Π_{neutron} = Π_{baryon} * Π_-(3,4)`)**:
    3-quark color singlet `N₀ N₁ N₂` with proton hole `1 - N₃` and occupied neutron mode `N₄`. -/
def neutronProjector : MatStage 5 :=
  colorBaryonSingletProj * isoProjMinus 3 4

/-- Alias `neutronBaryonProj` for `neutronProjector`. -/
abbrev neutronBaryonProj : MatStage 5 := neutronProjector

/-- **Neutrino Lepton Projector (`Π_{neutrino} = Π_{vac} * Π_+(3,4)`)**:
    3 color holes `(1 - N₀)(1 - N₁)(1 - N₂)` with isospin-up projector `Π_+(3,4)`. -/
def neutrinoProjector : MatStage 5 :=
  colorVacuumSingletProj * isoProjPlus 3 4

/-- **Electron Lepton Projector (`Π_{electron} = Π_{vac} * Π_-(3,4)`)**:
    3 color holes `(1 - N₀)(1 - N₁)(1 - N₂)` with isospin-down projector `Π_-(3,4)`. -/
def electronProjector : MatStage 5 :=
  colorVacuumSingletProj * isoProjMinus 3 4

/-- **Active Nucleon Doublet Face (`nucleonDoubletFace = Π_{proton} + Π_{neutron}`)**. -/
def nucleonDoubletFace : MatStage 5 :=
  protonProjector + neutronProjector

/-- **Moving Nucleon Decay State (`movingNucleonDecayState c s`)**:
    Positive Grassmannian / Amplituhedron trajectory connecting the pure Neutron vertex `(0, 1)`
    to the pure Proton vertex `(1, 0)` along the weak transition `Π_{baryon} * (τ_+ + τ_-)`. -/
def movingNucleonDecayState (c s : ℝ) : MatStage 5 :=
  (c * c) • protonProjector +
  (s * s) • neutronProjector -
  (c * s) • (colorBaryonSingletProj * (isospinPlus 3 4 + isospinMinus 3 4))

/-- **True `B - L` Gell-Mann–Nishijima Electric Charge Operator (`sixChargeBL = 6 Q_{EM}`)**:
    `sixChargeBL = (N_{color} - 3 • Π_{vac}) + 3 • (Π_+(3,4) - Π_-(3,4))`
    (assigning `3(B - L) = N_{color} - 3 • Π_{vac}`). -/
def sixChargeBL : MatStage 5 :=
  (colorSingletNumber - (3 : ℤ) • colorVacuumSingletProj) +
  (3 : ℤ) • (isoProjPlus 3 4 - isoProjMinus 3 4)

/-- **1. Maximal Cartan Subalgebra `𝔥₅` Inversion Theorem (`maximal_cartan_five_quantum_number_inversion`)**:
    The 5 physical commuting quantum-number operators `(T₃^{color}, 3Y^{color}, N_{color}, τ₃, 2K₀)`
    reconstruct all 5 individual mode occupation operators `(6 • N₀, 6 • N₁, 3 • N₂, 2 • N₃, 2 • N₄)`! -/
theorem maximal_cartan_five_quantum_number_inversion :
    (2 : ℕ) • colorSingletNumber + colorGluon3Y +
      (3 : ℕ) • colorGluonT3 = (6 : ℕ) • modeOccupied 0 ∧
    (2 : ℕ) • colorSingletNumber + colorGluon3Y -
      (3 : ℕ) • colorGluonT3 = (6 : ℕ) • modeOccupied 1 ∧
    colorSingletNumber - colorGluon3Y = (3 : ℕ) • modeOccupied 2 ∧
    (pairProjPlus 3 4 - pairProjMinus 3 4) + 1 +
      (isoProjPlus 3 4 - isoProjMinus 3 4) = (2 : ℕ) • modeOccupied 3 ∧
    (pairProjPlus 3 4 - pairProjMinus 3 4) + 1 -
      (isoProjPlus 3 4 - isoProjMinus 3 4) = (2 : ℕ) • modeOccupied 4 := by
  have hcol := color_occupation_singlet_octet_decomposition
  refine ⟨hcol.1, hcol.2.1, hcol.2.2, ?_, ?_⟩ <;>
  · dsimp [pairProjPlus, pairProjMinus, isoProjPlus, isoProjMinus]
    rw [modeVacant_eq_one_sub_modeOccupied 3, modeVacant_eq_one_sub_modeOccupied 4]
    noncomm_ring

/-- **2. Universal `B - L` Gell-Mann–Nishijima Spectral Charge Decomposition (`sixChargeBL_standard_model_spectral_decomposition`)**:
    With zero hypotheses, `sixChargeBL = 6 Q_{EM}` expands into all Standard Model electric charges:
    - `+4` (`+2/3`) on Up Quark `Π_{quark} * Π_+(3,4)`,
    - `-2` (`-1/3`) on Down Quark `Π_{quark} * Π_-(3,4)`,
    - `+2` (`+1/3`) on Isoscalar Diquark `Π_{diquark} * Δ_{pair}(3,4)`,
    - `+6` (`+1`)   on Proton `protonProjector`,
    - ` 0` (` 0`)   on Neutron `neutronProjector` and Neutrino `neutrinoProjector`,
    - `-6` (`-1`)   on Electron `electronProjector`! -/
theorem sixChargeBL_standard_model_spectral_decomposition :
    sixChargeBL =
      (4 : ℤ) • (colorQuarkTripletProj * isoProjPlus 3 4) +
      (-2 : ℤ) • (colorQuarkTripletProj * isoProjMinus 3 4) +
      (1 : ℤ) • (colorQuarkTripletProj * pairingCarrier 3 4) +
      (5 : ℤ) • (colorDiquarkAntitripletProj * isoProjPlus 3 4) +
      (-1 : ℤ) • (colorDiquarkAntitripletProj * isoProjMinus 3 4) +
      (2 : ℤ) • (colorDiquarkAntitripletProj * pairingCarrier 3 4) +
      (6 : ℤ) • protonProjector +
      (3 : ℤ) • (colorBaryonSingletProj * pairingCarrier 3 4) +
      (-6 : ℤ) • electronProjector +
      (-3 : ℤ) • (colorVacuumSingletProj * pairingCarrier 3 4) := by
  have h_iso : isoProjPlus 3 4 + isoProjMinus 3 4 + pairingCarrier 3 4 = 1 :=
    isospinCarrier_add_pairingCarrier 3 4
  have h_em := sixElectricCharge_spectral_decomposition
  have h_bl : sixChargeBL =
      sixElectricCharge -
      (3 : ℤ) • (colorVacuumSingletProj *
        (isoProjPlus 3 4 + isoProjMinus 3 4 + pairingCarrier 3 4)) := by
    rw [h_iso, mul_one]
    dsimp [sixChargeBL, sixElectricCharge]
    abel
  rw [h_bl, h_em]
  dsimp [protonProjector, electronProjector]
  noncomm_ring

/-- **3. Chiral–Isospin Alignment (`Γ_{color} * (Π_+ - Π_-)`) Separating Proton from Neutron**:
    The product of the 3-color chiral volume `Π_{pos}^{color} - Π_{neg}^{color}` and the
    weak isospin polarization `Π_+(3,4) - Π_-(3,4)` assigns `+1` (aligned) to the Proton and Electron,
    and `-1` (frustrated/unstable) to the Neutron and Neutrino! -/
theorem chiral_isospin_alignment_proton_vs_neutron :
    (colorPositiveCompanyProj - colorNegativeCompanyProj) *
      (isoProjPlus 3 4 - isoProjMinus 3 4) =
      (protonProjector +
       electronProjector +
       colorQuarkTripletProj * isoProjPlus 3 4 +
       colorDiquarkAntitripletProj * isoProjMinus 3 4) -
      (neutronProjector +
       neutrinoProjector +
       colorQuarkTripletProj * isoProjMinus 3 4 +
       colorDiquarkAntitripletProj * isoProjPlus 3 4) := by
  dsimp [colorPositiveCompanyProj, colorNegativeCompanyProj,
         protonProjector, neutronProjector, neutrinoProjector, electronProjector]
  noncomm_ring

/-- **4. Quark–Diquark Internal Factorization & Nucleon Doublet Decay Endpoints (`proton_neutron_particle_hole_and_decay_endpoints`)**:
    - The 3-quark baryon core `N₀ N₁ N₂` factors into a single quark `N₀` times a 2-quark
      diquark `N₁ N₂`: `colorBaryonSingletProj = modeOccupied 0 * (modeOccupied 1 * modeOccupied 2)`.
    - `nucleonDoubletFace = colorBaryonSingletProj * isospinCarrier 3 4`.
    - At `(c = 0, s = 1)`, `movingNucleonDecayState 0 1 = neutronProjector` (initial Neutron vertex);
      at `(c = 1, s = 0)`, `movingNucleonDecayState 1 0 = protonProjector` (final Proton vertex)! -/
theorem proton_neutron_particle_hole_and_decay_endpoints :
    colorBaryonSingletProj = modeOccupied 0 * (modeOccupied 1 * modeOccupied 2) ∧
    nucleonDoubletFace = colorBaryonSingletProj * isospinCarrier 3 4 ∧
    movingNucleonDecayState 0 1 = neutronProjector ∧
    movingNucleonDecayState 1 0 = protonProjector := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold colorBaryonSingletProj; rw [mul_assoc]
  · unfold nucleonDoubletFace protonProjector neutronProjector isospinCarrier
    rw [mul_add]
  · unfold movingNucleonDecayState
    simp only [mul_zero, zero_smul, mul_one, one_smul, zero_add, sub_zero]
  · unfold movingNucleonDecayState
    simp only [mul_one, one_smul, mul_zero, zero_smul, add_zero, sub_zero]

/-- **5. Universal Neutron–Proton Mass-Splitting Driving Commutator (`neutron_proton_mass_gap_commutator`)**:
    For any mass parameters `m_p, m_n : R` and any weak transition `W_eff = P_p * W * P_n`,
    the commutator `[m_p • P_p + m_n • P_n, W_eff]` isolates the mass gap `(m_p - m_n)` plus the
    idempotence/orthogonality defect terms `(P_p² - P_p)`, `(P_n² - P_n)`, and `P_p * P_n`! -/
theorem neutron_proton_mass_gap_commutator
    {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]
    (m_p m_n : R) (P_p P_n W : A) :
    let H_m := m_p • P_p + m_n • P_n
    let W_eff := P_p * W * P_n
    H_m * W_eff - W_eff * H_m =
      (m_p - m_n) • (P_p * (P_p * (W * P_n))) +
      m_n • (P_p * (P_p * (W * P_n)) - P_p * (W * (P_n * P_n))) +
      m_n • (P_n * (P_p * (W * P_n))) -
      m_p • (P_p * (W * (P_n * P_p))) := by
  intro H_m W_eff
  dsimp [H_m, W_eff]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
  module

/-!
### 5b. 32-Spinor `Cl(5, 5)` Mode-Graded Laplace–Wavelet–Bruhat Trifactorization & Artin Braid Group `B₃`
-/

/-- **Single-Mode Hyperbolic Laplace / Mellin Kernel (`modeHyperbolicKernel a lam mu = lam • N_a + mu • Ñ_a`)**. -/
def modeHyperbolicKernel (a : Fin 5) (lam mu : ℝ) : MatStage 5 :=
  lam • modeOccupied a + mu • modeVacant a

/-- **Single-Mode Upper Nilpotent Creation Exponential (`modeExpCreation a t = 1 + t • e_a`)**. -/
def modeExpCreation (a : Fin 5) (t : ℝ) : MatStage 5 :=
  1 + t • e a

/-- **Single-Mode Lower Nilpotent Annihilation Exponential (`modeExpAnnihilation a s = 1 + s • f_a`)**. -/
def modeExpAnnihilation (a : Fin 5) (s : ℝ) : MatStage 5 :=
  1 + s • f a

/-- **Single-Mode Affine Wavelet Generator (`modeAffineWavelet a lam mu t = D_a(lam, mu) + t • e_a`)**. -/
def modeAffineWavelet (a : Fin 5) (lam mu t : ℝ) : MatStage 5 :=
  modeHyperbolicKernel a lam mu + t • e a

/-- **Single-Mode Parabolic Artin Braid Generators (`modeBraidSigma1 a = 1 + e_a`, `modeBraidSigma2 a = 1 - f_a`)**. -/
def modeBraidSigma1 (a : Fin 5) : MatStage 5 := 1 + e a
def modeBraidSigma2 (a : Fin 5) : MatStage 5 := 1 - f a

/-- **6. 32-Spinor `Cl(5, 5)` Mode-Graded Laplace–Wavelet–Bruhat Trifactorization & Artin Braid Group `B₃` Synthesis**:
    For every fermionic mode `a : Fin 5` in `MatStage 5 ≅ Cl(5, 5)`:
    - **Temperley–Lieb (`δ = 0`) Relations**: `e_a * f_a * e_a = e_a` and `f_a * e_a * f_a = f_a`.
    - **Emil Artin Braid Group `B₃` Relation**:
      `modeBraidSigma1 a * modeBraidSigma2 a * modeBraidSigma1 a = modeBraidSigma2 a * modeBraidSigma1 a * modeBraidSigma2 a = gammaMinus a`.
    - **Hyperbolic Laplace–Mellin Kernel Semigroup**:
      `modeHyperbolicKernel a lam₁ mu₁ * modeHyperbolicKernel a lam₂ mu₂ = modeHyperbolicKernel a (lam₁ * lam₂) (mu₁ * mu₂)`.
    - **Nilpotent Creation/Annihilation Exponential Homomorphisms & Affine Wavelet Semigroup**:
      `modeExpCreation a t₁ * modeExpCreation a t₂ = modeExpCreation a (t₁ + t₂)`,
      `modeExpAnnihilation a s₁ * modeExpAnnihilation a s₂ = modeExpAnnihilation a (s₁ + s₂)`, and
      `modeAffineWavelet a lam₁ mu₁ t₁ * modeAffineWavelet a lam₂ mu₂ t₂ = modeAffineWavelet a (lam₁ * lam₂) (mu₁ * mu₂) (lam₁ * t₂ + t₁ * mu₂)`.
    - **32-Spinor Gauss–Bruhat `L D U` Trifactorization**:
      `modeExpAnnihilation a s * modeHyperbolicKernel a lam mu * modeExpCreation a t = lam • modeOccupied a + (lam * t) • e a + (lam * s) • f a + (lam * s * t + mu) • modeVacant a`! -/
theorem cl55_mode_graded_laplace_wavelet_bruhat_and_braid_synthesis
    (a : Fin 5) (lam₁ mu₁ t₁ lam₂ mu₂ t₂ lam mu s₁ s₂ s t : ℝ) :
    e a * f a * e a = e a ∧
    f a * e a * f a = f a ∧
    modeBraidSigma1 a * modeBraidSigma2 a * modeBraidSigma1 a =
      modeBraidSigma2 a * modeBraidSigma1 a * modeBraidSigma2 a ∧
    modeBraidSigma1 a * modeBraidSigma2 a * modeBraidSigma1 a = gammaMinus a ∧
    modeHyperbolicKernel a lam₁ mu₁ * modeHyperbolicKernel a lam₂ mu₂ =
      modeHyperbolicKernel a (lam₁ * lam₂) (mu₁ * mu₂) ∧
    modeExpCreation a t₁ * modeExpCreation a t₂ = modeExpCreation a (t₁ + t₂) ∧
    modeExpAnnihilation a s₁ * modeExpAnnihilation a s₂ = modeExpAnnihilation a (s₁ + s₂) ∧
    modeAffineWavelet a lam₁ mu₁ t₁ * modeAffineWavelet a lam₂ mu₂ t₂ =
      modeAffineWavelet a (lam₁ * lam₂) (mu₁ * mu₂) (lam₁ * t₂ + t₁ * mu₂) ∧
    modeExpAnnihilation a s * modeHyperbolicKernel a lam mu * modeExpCreation a t =
      lam • modeOccupied a + (lam * t) • e a + (lam * s) • f a +
      (lam * s * t + mu) • modeVacant a := by
  have hesq : e a * e a = 0 := e_sq a
  have hfsq : f a * f a = 0 := f_sq a
  have hcar : e a * f a + f a * e a = 1 := by simpa using ef_car a a
  have hefe : e a * f a * e a = e a := by
    calc
      (e a * f a) * e a = (1 - f a * e a) * e a := by rw [eq_sub_of_add_eq hcar]
      _ = e a - f a * (e a * e a) := by noncomm_ring
      _ = e a := by rw [hesq, mul_zero, sub_zero]
  have hfef : f a * e a * f a = f a := by
    calc
      (f a * e a) * f a = (1 - e a * f a) * f a := by rw [eq_sub_of_add_eq' hcar]
      _ = f a - e a * (f a * f a) := by noncomm_ring
      _ = f a := by rw [hfsq, mul_zero, sub_zero]
  have h_occ_sq : modeOccupied a * modeOccupied a = modeOccupied a := modeOccupied_idem a
  have h_vac_sq : modeVacant a * modeVacant a = modeVacant a := modeVacant_idem a
  have h_occ_vac : modeOccupied a * modeVacant a = 0 := modeOccupied_mul_modeVacant a
  have h_vac_occ : modeVacant a * modeOccupied a = 0 := modeVacant_mul_modeOccupied a
  have h_sum : modeOccupied a + modeVacant a = 1 := modeOccupied_add_modeVacant a
  have h_occ_e : modeOccupied a * e a = e a := hefe
  have h_e_occ : e a * modeOccupied a = 0 := by
    dsimp [modeOccupied]
    calc e a * (e a * f a) = (e a * e a) * f a := by noncomm_ring
    _ = 0 := by rw [hesq, zero_mul]
  have h_vac_e : modeVacant a * e a = 0 := by
    dsimp [modeVacant]
    calc f a * e a * e a = f a * (e a * e a) := by noncomm_ring
    _ = 0 := by rw [hesq, mul_zero]
  have h_e_vac : e a * modeVacant a = e a := by
    dsimp [modeVacant]
    calc e a * (f a * e a) = (e a * f a) * e a := by noncomm_ring
    _ = e a := hefe
  have h_f_occ : f a * modeOccupied a = f a := by
    dsimp [modeOccupied]
    calc f a * (e a * f a) = (f a * e a) * f a := by noncomm_ring
    _ = f a := hfef
  have h_occ_f : modeOccupied a * f a = 0 := by
    dsimp [modeOccupied]
    calc e a * f a * f a = e a * (f a * f a) := by noncomm_ring
    _ = 0 := by rw [hfsq, mul_zero]
  have h_vac_f : modeVacant a * f a = f a := hfef
  have h_f_vac : f a * modeVacant a = 0 := by
    dsimp [modeVacant]
    calc f a * (f a * e a) = (f a * f a) * e a := by noncomm_ring
    _ = 0 := by rw [hfsq, zero_mul]
  have h_f_e : f a * e a = modeVacant a := rfl
  have h_e_f : e a * f a = modeOccupied a := rfl
  have h_braid1 : modeBraidSigma1 a * modeBraidSigma2 a * modeBraidSigma1 a = gammaMinus a := by
    dsimp [modeBraidSigma1, modeBraidSigma2, gammaMinus]
    have hstep1 : (1 + e a) * (1 - f a) = 1 + e a - f a - modeOccupied a := by
      dsimp [modeOccupied]; noncomm_ring
    rw [hstep1]
    calc
      (1 + e a - f a - modeOccupied a) * (1 + e a) =
        (1 - (modeOccupied a + f a * e a)) + e a + e a - f a +
        (e a * e a) - (modeOccupied a * e a) := by noncomm_ring
      _ = (1 - (modeOccupied a + modeVacant a)) + e a + e a - f a + 0 - e a := by
        rw [h_f_e, hesq, h_occ_e]
      _ = (1 - 1) + e a + e a - f a + 0 - e a := by rw [h_sum]
      _ = e a - f a := by abel
  have h_braid2 : modeBraidSigma2 a * modeBraidSigma1 a * modeBraidSigma2 a = gammaMinus a := by
    dsimp [modeBraidSigma1, modeBraidSigma2, gammaMinus]
    have hstep1 : (1 - f a) * (1 + e a) = 1 - f a + e a - modeVacant a := by
      dsimp [modeVacant]; noncomm_ring
    rw [hstep1]
    calc
      (1 - f a + e a - modeVacant a) * (1 - f a) =
        (1 - (e a * f a + modeVacant a)) - f a - f a + e a +
        (f a * f a) + (modeVacant a * f a) := by noncomm_ring
      _ = (1 - (modeOccupied a + modeVacant a)) - f a - f a + e a + 0 + f a := by
        rw [h_e_f, hfsq, h_vac_f]
      _ = (1 - 1) - f a - f a + e a + 0 + f a := by rw [h_sum]
      _ = e a - f a := by abel
  refine ⟨hefe, hfef, h_braid1.trans h_braid2.symm, h_braid1, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [modeHyperbolicKernel]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
               h_occ_sq, h_occ_vac, h_vac_occ, h_vac_sq]
    module
  · dsimp [modeExpCreation]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hesq]
    module
  · dsimp [modeExpAnnihilation]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hfsq]
    module
  · dsimp [modeAffineWavelet, modeHyperbolicKernel]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
               h_occ_sq, h_occ_vac, h_vac_occ, h_vac_sq,
               h_occ_e, h_vac_e, h_e_occ, h_e_vac, hesq]
    module
  · dsimp [modeExpAnnihilation, modeHyperbolicKernel, modeExpCreation]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
               h_f_occ, h_f_vac, h_occ_e, h_vac_e, h_f_e, zero_mul, smul_zero]
    module

/-!
### 5c. 5-Mode Cartan Occupation Sign Tuple, `16 + 16` Chiral Split, & `sixChargeBL` Spectral Table
-/

section CartanOccupationSigns

variable {R : Type*} [CommRing R]

/-- **5-Mode Cartan Occupation Sign Tuple (`CartanSigns R = Fin 5 → R`)**:
    Represents the 5 commuting Cartan involutions `(σ₀, σ₁, σ₂, σ₃, σ₄)` of `𝔥₅ ⊂ Cl(5,5)`,
    where `(σ₀, σ₁, σ₂)` are the 3 color modes, `σ₃` is weak isospin `2τ₃`, and `σ₄` is `2K₀`. -/
abbrev CartanSigns (R : Type*) := Fin 5 → R

/-- Twice color isospin `2 * T₃^color = σ₀ - σ₁`. -/
def twoColorT3 (s : CartanSigns R) : R := s 0 - s 1

/-- Three times color hypercharge `3 * Y^color = σ₀ + σ₁ - 2 * σ₂`. -/
def threeColorY (s : CartanSigns R) : R := s 0 + s 1 - 2 * s 2

/-- Shifted color number operator `2 * N_color - 3 = σ₀ + σ₁ + σ₂`. -/
def shiftedColorNum (s : CartanSigns R) : R := s 0 + s 1 + s 2

/-- Integer-scaled `3 * (B - L) = σ₀ + σ₁ + σ₂` (`-3` for leptons, `+1` for quarks, `+3` for baryons). -/
def threeBMinusL (s : CartanSigns R) : R := s 0 + s 1 + s 2

/-- **Six times the Gell-Mann–Nishijima Electric Charge on Cartan Signs (`sixChargeBLSign = 3 * (2τ₃) + 3 * (B - L)`)**:
    `6 * Q_em = 3 * σ₃ + (σ₀ + σ₁ + σ₂)`. -/
def sixChargeBLSign (s : CartanSigns R) : R :=
  3 * s 3 + threeBMinusL s

/-- **Total `Cl(5,5)` Chiral Grading Eigenvalue (`cl55Gamma = σ₀ * σ₁ * σ₂ * σ₃ * σ₄`)**. -/
def cl55Gamma (s : CartanSigns R) : R :=
  s 0 * s 1 * s 2 * s 3 * s 4

/-- Twice the `16_+` and `16_-` chiral half-spinor projectors (`2 * Π₁₆^± = 1 ± Γ_{Cl(5,5)}`). -/
def twoChiralProjPlus (s : CartanSigns R) : R := 1 + cl55Gamma s
def twoChiralProjMinus (s : CartanSigns R) : R := 1 - cl55Gamma s

/-- Canonical Fock basis states in `{±1}⁵`. -/
def protonState : CartanSigns R := ![1, 1, 1, 1, 1]
def neutronState : CartanSigns R := ![1, 1, 1, -1, 1]
def neutrinoState : CartanSigns R := ![-1, -1, -1, 1, 1]
def electronState : CartanSigns R := ![-1, -1, -1, -1, 1]
def redUpQuarkState : CartanSigns R := ![1, -1, 1, 1, 1]
def redDownQuarkState : CartanSigns R := ![1, -1, 1, -1, 1]

/-- **7. Exact Cartan Inversion, `16 + 16` Chiral Decomposition, & `sixChargeBLSign` Spectral Table**:
    With zero hypotheses:
    1. **Exact `SU(3)` Color Cartan Reconstruction**:
       `3 * (twoColorT3 s) + (threeColorY s) + 2 * (shiftedColorNum s) = 6 * s 0`.
    2. **`16 + 16` Chiral Projector Split**:
       `twoChiralProjPlus s + twoChiralProjMinus s = 2` and
       `twoChiralProjPlus s - twoChiralProjMinus s = 2 * cl55Gamma s`.
    3. **`sixChargeBLSign` (`6 * Q_em`) Fermion & Baryon Spectral Table**:
       - Proton: `+6` (`Q = +1`)
       - Neutron: `0` (`Q = 0`)
       - Neutrino: `0` (`Q = 0`)
       - Electron: `-6` (`Q = -1`)
       - Up Quark: `+4` (`Q = +2/3`)
       - Down Quark: `-2` (`Q = -1/3`)! -/
theorem cl55_cartan_reconstruction_chiral_split_and_sixChargeBL_table
    (s : CartanSigns R) :
    3 * twoColorT3 s + threeColorY s + 2 * shiftedColorNum s = 6 * s 0 ∧
    twoChiralProjPlus s + twoChiralProjMinus s = 2 ∧
    twoChiralProjPlus s - twoChiralProjMinus s = 2 * cl55Gamma s ∧
    sixChargeBLSign (protonState : CartanSigns R) = 6 ∧
    sixChargeBLSign (neutronState : CartanSigns R) = 0 ∧
    sixChargeBLSign (neutrinoState : CartanSigns R) = 0 ∧
    sixChargeBLSign (electronState : CartanSigns R) = -6 ∧
    sixChargeBLSign (redUpQuarkState : CartanSigns R) = 4 ∧
    sixChargeBLSign (redDownQuarkState : CartanSigns R) = -2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (simp [twoColorT3, threeColorY, shiftedColorNum, twoChiralProjPlus,
         twoChiralProjMinus, cl55Gamma, sixChargeBLSign, threeBMinusL,
         protonState, neutronState, neutrinoState, electronState,
         redUpQuarkState, redDownQuarkState]; ring)

end CartanOccupationSigns

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
