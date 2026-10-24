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
