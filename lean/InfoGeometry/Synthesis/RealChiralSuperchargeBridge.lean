/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis
import InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis
import InfoGeometry.Canonical.SplitOctonionClifford33Soldering
import InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
import InfoGeometry.Clifford.Cl55ChiralSectorPredicateBridge

/-!
## Finite matrix examples and native Cl(5,5) null-spinor facts

This file separates finite matrix-unit examples from the native Clifford
spinor model. The matrix-unit operators and the block permutation below are
not identified with Clifford supercharges or a Clifford rotor. Their square
zero properties do not depend on the lightcone hypothesis, and the trace
identity below is not a BRST cohomology theorem.

The native `Cl(5,5)` section at the end proves that a null Witt vector acts
nilpotently on the real spinor representation and exchanges its two volume
eigenspaces. No intertwiner from the finite matrix-unit examples to that
native representation is claimed.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.RealChiralSuperchargeBridge

open scoped Matrix BigOperators
open Matrix
open InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis
open InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.SpinorRep

/-!
## Section 1: finite grading labels and Koszul sign calculations
-/

/-- Seven labels with doubled integer weights. This is a finite grading-label
type only; no bracket or representation structure is attached to it here. -/
inductive SuperKKTDegree : Type
  | deg_neg_2 : SuperKKTDegree
  | deg_neg_1 : SuperKKTDegree
  | deg_neg_half : SuperKKTDegree
  | deg_zero : SuperKKTDegree
  | deg_pos_half : SuperKKTDegree
  | deg_pos_1 : SuperKKTDegree
  | deg_pos_2 : SuperKKTDegree
  deriving DecidableEq, Repr

instance : Inhabited SuperKKTDegree :=
  ⟨SuperKKTDegree.deg_zero⟩

/-- Non-default chiral supercharge degree witness $\mathfrak{g}_{-1/2}$ (`T17`). -/
def canonicalSuperKKTDegreeWitness : SuperKKTDegree :=
  SuperKKTDegree.deg_neg_half

/-- `canonicalSuperKKTDegreeWitness` is strictly distinct from the default Grade-$0$ degree (`T17`). -/
theorem canonicalSuperKKTDegreeWitness_ne_default :
    canonicalSuperKKTDegreeWitness ≠ (default : SuperKKTDegree) := by
  intro h
  cases h

/-- Integer-doubled dilation weight $2 \cdot \mathrm{deg}(d) \in \{-4, -2, -1, 0, +1, +2, +4\}$
under the dilatation bivector $D = \frac{1}{2} e_0 e_1 \in \mathrm{Cl}(1,1)$. -/
def superKKTTwiceWeight : SuperKKTDegree → ℤ
  | SuperKKTDegree.deg_neg_2 => -4
  | SuperKKTDegree.deg_neg_1 => -2
  | SuperKKTDegree.deg_neg_half => -1
  | SuperKKTDegree.deg_zero => 0
  | SuperKKTDegree.deg_pos_half => 1
  | SuperKKTDegree.deg_pos_1 => 2
  | SuperKKTDegree.deg_pos_2 => 4

/-- Involutive Super-Andreev grade reflection exchanging causal ($-$) and retrocausal ($+$)
sectors across the Grade-$0$ Levi horizon. -/
def superKKTDual : SuperKKTDegree → SuperKKTDegree
  | SuperKKTDegree.deg_neg_2 => SuperKKTDegree.deg_pos_2
  | SuperKKTDegree.deg_neg_1 => SuperKKTDegree.deg_pos_1
  | SuperKKTDegree.deg_neg_half => SuperKKTDegree.deg_pos_half
  | SuperKKTDegree.deg_zero => SuperKKTDegree.deg_zero
  | SuperKKTDegree.deg_pos_half => SuperKKTDegree.deg_neg_half
  | SuperKKTDegree.deg_pos_1 => SuperKKTDegree.deg_neg_1
  | SuperKKTDegree.deg_pos_2 => SuperKKTDegree.deg_neg_2

/-- $\mathbb{Z}_2 \times \mathbb{Z}_2$ Koszul bigrading $\mathbf{g} = (\deg_e, \deg_c)$
where $\deg_e \in \mathrm{Fin}\, 2$ is spinor fermionicity ($0$ = boson, $1$ = fermion)
and $\deg_c \in \mathrm{Fin}\, 2$ is color triality parity ($0$ = singlet, $1$ = triplet). -/
@[ext]
structure KoszulGrading where
  /-- Spinor fermionicity degree $\deg_e \in \{0, 1\}$. -/
  deg_e : Fin 2
  /-- Color triality parity degree $\deg_c \in \{0, 1\}$. -/
  deg_c : Fin 2
  deriving DecidableEq, Repr

instance : Inhabited KoszulGrading :=
  ⟨⟨0, 0⟩⟩

/-- Canonical non-default quark supercharge grading witness $(1, 1) \in \mathbb{Z}_2 \times \mathbb{Z}_2$ (`T17`). -/
def canonicalQuarkKoszulGrading : KoszulGrading :=
  ⟨1, 1⟩

/-- Canonical lepton supercharge grading $(1, 0) \in \mathbb{Z}_2 \times \mathbb{Z}_2$. -/
def canonicalLeptonKoszulGrading : KoszulGrading :=
  ⟨1, 0⟩

/-- `canonicalQuarkKoszulGrading` is strictly distinct from the default vacuum grading `(0, 0)` (`T17`). -/
theorem canonicalQuarkKoszulGrading_ne_default :
    canonicalQuarkKoszulGrading ≠ (default : KoszulGrading) := by
  intro h
  have h1 : canonicalQuarkKoszulGrading.deg_e = (default : KoszulGrading).deg_e :=
    congrArg KoszulGrading.deg_e h
  revert h1
  decide

/-- Koszul–Rittenberg sign factor $\varepsilon(g_1, g_2) = (-1)^{(e_1 e_2 + c_1 c_2) \bmod 2}$. -/
def koszulSign (g₁ g₂ : KoszulGrading) : ℝ :=
  (-1 : ℝ) ^ ((g₁.deg_e.val * g₂.deg_e.val + g₁.deg_c.val * g₂.deg_c.val) % 2)

/-- **Theorem 1.1 (`superKKT_ladder_and_koszul_parastatistics_laws`)**:
1. **Super-KKT Reflection Duality**:
   `superKKTDual` is an involution (`superKKTDual (superKKTDual d) = d`) that negates the
   dilation weight (`superKKTTwiceWeight (superKKTDual d) = -superKKTTwiceWeight d`).
2. **Lepton–Quark Anticommutation & Quark–Quark Parastatistical Commutation**:
   - A lepton chiral supercharge $(1, 0)$ and a quark chiral supercharge $(1, 1)$ anticommute:
     `koszulSign canonicalLeptonKoszulGrading canonicalQuarkKoszulGrading = -1`.
   - Two quark chiral supercharges $(1, 1)$ commute parastatistically:
     `koszulSign canonicalQuarkKoszulGrading canonicalQuarkKoszulGrading = 1`.
3. **Diquark Vector Cross-Product Closure ($\mathbf{3} \times \mathbf{3} \to \bar{\mathbf{3}}$)**:
   For any quark triplet vectors $u, v \in \mathbb{R}^3$, their Zorn cross product is
   antisymmetric (`vec3Cross u v = -vec3Cross v u`) and orthogonal to each factor
   (`vec3Dot u (vec3Cross u v) = 0`), closing symmetrically into the anti-quark sector $\bar{\mathbf{3}}$. -/
theorem superKKT_ladder_and_koszul_parastatistics_laws
    (d : SuperKKTDegree) (u v : Fin 3 → ℝ) :
    (superKKTDual (superKKTDual d) = d ∧
     superKKTTwiceWeight (superKKTDual d) = -superKKTTwiceWeight d) ∧
    (koszulSign canonicalLeptonKoszulGrading canonicalQuarkKoszulGrading = -1 ∧
     koszulSign canonicalQuarkKoszulGrading canonicalQuarkKoszulGrading = 1) ∧
    (vec3Cross u v = -vec3Cross v u ∧
     vec3Dot u (vec3Cross u v) = 0) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · cases d <;> rfl
  · cases d <;> rfl
  · dsimp [koszulSign, canonicalLeptonKoszulGrading, canonicalQuarkKoszulGrading]
    norm_num
  · dsimp [koszulSign, canonicalQuarkKoszulGrading]
    norm_num
  · ext i
    fin_cases i <;>
      (dsimp [vec3Cross]; ring)
  · dsimp [vec3Dot, vec3Cross]
    ring

/-!
## Section 2: finite matrix-unit witnesses and block permutation
-/

/-- Positive Majorana–Weyl half-spinor index embedding $\mathrm{Fin}\, 16 \hookrightarrow \mathrm{Fin}\, 32$
mapping $\alpha \in \{0, \dots, 15\}$ to the forward chiral block $S^+ \subset \mathbb{R}^{32}$. -/
def chiralPlusIdx (α : Fin 16) : Fin 32 :=
  ⟨α.val, Nat.lt_trans α.isLt (by decide)⟩

/-- Negative Majorana–Weyl half-spinor index embedding $\mathrm{Fin}\, 16 \hookrightarrow \mathrm{Fin}\, 32$
mapping $\alpha \in \{0, \dots, 15\}$ to the backward chiral block $S^- \subset \mathbb{R}^{32}$. -/
def chiralMinusIdx (α : Fin 16) : Fin 32 :=
  ⟨α.val + 16, Nat.add_lt_add_right α.isLt 16⟩

/-- Every forward chiral index in $S^+$ is strictly distinct from every backward chiral index in $S^-$. -/
lemma chiralPlusIdx_ne_chiralMinusIdx (α β : Fin 16) :
    chiralPlusIdx α ≠ chiralMinusIdx β := by
  intro h
  have hval : (chiralPlusIdx α).val = (chiralMinusIdx β).val := congrArg Fin.val h
  dsimp [chiralPlusIdx, chiralMinusIdx] at hval
  have hlt : α.val < β.val + 16 :=
    Nat.lt_of_lt_of_le α.isLt (Nat.le_add_left 16 β.val)
  exact Nat.ne_of_lt hlt hval

/-- Chiral sheet-swap involution on $\mathrm{Fin}\, 32$ exchanging the positive half-spinor block
$0..15$ ($S^+$) and the negative half-spinor block $16..31$ ($S^-$). -/
def superAndreevSwap (i : Fin 32) : Fin 32 :=
  if h : i.val < 16 then
    ⟨i.val + 16, Nat.add_lt_add_right h 16⟩
  else
    ⟨i.val - 16, Nat.lt_of_le_of_lt (Nat.sub_le i.val 16) i.isLt⟩

/-- `superAndreevSwap` is an involution on $\mathrm{Fin}\, 32$. -/
lemma superAndreevSwap_involutive (i : Fin 32) :
    superAndreevSwap (superAndreevSwap i) = i := by
  by_cases h : i.val < 16
  · have h2 : ¬ (i.val + 16 < 16) := Nat.not_lt.mpr (Nat.le_add_left 16 i.val)
    simp only [superAndreevSwap, h, h2, ↓reduceDIte]
    ext
    exact Nat.add_sub_cancel i.val 16
  · have h_ge : 16 ≤ i.val := Nat.not_lt.mp h
    have h_lt32 : i.val < 16 + 16 := i.isLt
    have h2 : i.val - 16 < 16 := Nat.sub_lt_left_of_lt_add h_ge h_lt32
    simp only [superAndreevSwap, h, h2, ↓reduceDIte]
    ext
    exact Nat.sub_add_cancel h_ge

/-- `superAndreevSwap` maps the forward chiral index `chiralPlusIdx α` to `chiralMinusIdx α`. -/
lemma superAndreevSwap_chiralPlusIdx (α : Fin 16) :
    superAndreevSwap (chiralPlusIdx α) = chiralMinusIdx α := by
  simp only [superAndreevSwap, chiralPlusIdx, chiralMinusIdx, α.isLt, ↓reduceDIte]

/-- `superAndreevSwap` maps the backward chiral index `chiralMinusIdx α` to `chiralPlusIdx α`. -/
lemma superAndreevSwap_chiralMinusIdx (α : Fin 16) :
    superAndreevSwap (chiralMinusIdx α) = chiralPlusIdx α := by
  have h := superAndreevSwap_involutive (chiralPlusIdx α)
  rw [superAndreevSwap_chiralPlusIdx α] at h
  exact h

/-- Elementary $32 \times 32$ transition matrix $E_{p, q}$ with $1$ at entry $(p, q)$ and $0$ elsewhere. -/
def singleEntry32 (p q : Fin 32) : Matrix (Fin 32) (Fin 32) ℝ :=
  fun i j => if j = q then (if i = p then 1 else 0) else 0

/-- Permutation matrix of `superAndreevSwap`, exchanging the two 16-index
blocks. Its Clifford/rotor interpretation is not established here. -/
def superAndreevRotor : Matrix (Fin 32) (Fin 32) ℝ :=
  fun i j => if j = superAndreevSwap i then 1 else 0

/-- Matrix-unit witness from a positive-block index to its paired negative-block
index. It is not identified with a native `Cl(5,5)` supercharge. -/
def realSuperchargePlus (α : Fin 16) : Matrix (Fin 32) (Fin 32) ℝ :=
  singleEntry32 (chiralPlusIdx α) (chiralMinusIdx α)

/-- Reverse matrix-unit witness on `Fin 32`, independent of the native
Clifford spinor representation. -/
def realSuperchargeMinus (α : Fin 16) : Matrix (Fin 32) (Fin 32) ℝ :=
  singleEntry32 (chiralMinusIdx α) (chiralPlusIdx α)

/-- Left multiplication by `superAndreevRotor` permutes rows by `superAndreevSwap`. -/
lemma superAndreevRotor_mul_apply (M : Matrix (Fin 32) (Fin 32) ℝ) (i j : Fin 32) :
    (superAndreevRotor * M) i j = M (superAndreevSwap i) j := by
  dsimp [superAndreevRotor, Matrix.mul_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Right multiplication by `superAndreevRotorᵀ` permutes columns by `superAndreevSwap`. -/
lemma mul_superAndreevRotor_transpose_apply (M : Matrix (Fin 32) (Fin 32) ℝ) (i j : Fin 32) :
    (M * superAndreevRotorᵀ) i j = M i (superAndreevSwap j) := by
  dsimp [superAndreevRotor, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Product of two elementary transition matrices `singleEntry32 p₁ q₁` and `singleEntry32 p₂ q₂`
when `q₁ ≠ p₂` vanishes identically. -/
lemma singleEntry32_mul_of_ne (p₁ q₁ p₂ q₂ : Fin 32) (hne : q₁ ≠ p₂) :
    singleEntry32 p₁ q₁ * singleEntry32 p₂ q₂ = 0 := by
  ext i j
  dsimp [singleEntry32, Matrix.mul_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    hne, mul_zero, ite_self, Matrix.zero_apply]

/-- Product of two complementary elementary transition matrices `singleEntry32 p q` and
`singleEntry32 q p` evaluates to `1` at diagonal entry `(p, p)`. -/
lemma singleEntry32_mul_symm_diag (p q : Fin 32) :
    (singleEntry32 p q * singleEntry32 q p) p p = 1 := by
  dsimp [singleEntry32, Matrix.mul_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_one]

/-- Product of two complementary elementary transition matrices `singleEntry32 q p` and
`singleEntry32 p q` evaluates to `0` at entry `(p, p)` whenever `p ≠ q`. -/
lemma singleEntry32_mul_symm_offdiag (p q : Fin 32) (hne : p ≠ q) :
    (singleEntry32 q p * singleEntry32 p q) p p = 0 := by
  dsimp [singleEntry32, Matrix.mul_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hne]

/-- First $32 \times 32$ real chiral supercharge generator witness $Q_0^+ \in M_{32}(\mathbb{R})$ (`T16`). -/
def superchargeWitnessPlus0 : Matrix (Fin 32) (Fin 32) ℝ :=
  realSuperchargePlus 0

/-- Second $32 \times 32$ real chiral supercharge generator witness $Q_0^- \in M_{32}(\mathbb{R})$ (`T16`). -/
def superchargeWitnessMinus0 : Matrix (Fin 32) (Fin 32) ℝ :=
  realSuperchargeMinus 0

/-- Explicit non-commutativity witness on the $32 \times 32$ real spinor matrix carrier
`Matrix (Fin 32) (Fin 32) ℝ` (`T16`). -/
theorem superchargeWitnessPlus0_mul_superchargeWitnessMinus0_ne_comm :
    superchargeWitnessPlus0 * superchargeWitnessMinus0 ≠
      superchargeWitnessMinus0 * superchargeWitnessPlus0 := by
  intro h_comm
  have h00 :
      (superchargeWitnessPlus0 * superchargeWitnessMinus0) (chiralPlusIdx 0) (chiralPlusIdx 0) =
      (superchargeWitnessMinus0 * superchargeWitnessPlus0) (chiralPlusIdx 0) (chiralPlusIdx 0) :=
    congrArg (fun M : Matrix (Fin 32) (Fin 32) ℝ => M (chiralPlusIdx 0) (chiralPlusIdx 0)) h_comm
  dsimp [superchargeWitnessPlus0, superchargeWitnessMinus0,
    realSuperchargePlus, realSuperchargeMinus] at h00
  rw [singleEntry32_mul_symm_diag,
    singleEntry32_mul_symm_offdiag _ _ (chiralPlusIdx_ne_chiralMinusIdx 0 0)] at h00
  exact one_ne_zero h00

/-- **Finite permutation-matrix identity**:
Conjugation by the block-swap permutation matrix `superAndreevRotor` exchanges the two
matrix-unit witnesses. This is not asserted to be a Clifford rotor action:
$$\mathcal{R}_{\text{super}} \, Q_\alpha^+ \, \mathcal{R}_{\text{super}}^{\mathsf{T}} = Q_\alpha^-, \qquad
  \mathcal{R}_{\text{super}} \, Q_\alpha^- \, \mathcal{R}_{\text{super}}^{\mathsf{T}} = Q_\alpha^+.$$ -/
theorem super_andreev_chiral_transmutation (α : Fin 16) :
    superAndreevRotor * realSuperchargePlus α * superAndreevRotorᵀ =
      realSuperchargeMinus α ∧
    superAndreevRotor * realSuperchargeMinus α * superAndreevRotorᵀ =
      realSuperchargePlus α := by
  have h_swap_iff : ∀ x y : Fin 32, superAndreevSwap x = y ↔ x = superAndreevSwap y := by
    intro x y
    constructor
    · intro hxy
      rw [← hxy, superAndreevSwap_involutive]
    · intro hxy
      rw [hxy, superAndreevSwap_involutive]
  refine ⟨?_, ?_⟩
  · ext i j
    rw [mul_superAndreevRotor_transpose_apply, superAndreevRotor_mul_apply]
    dsimp [realSuperchargePlus, realSuperchargeMinus, singleEntry32]
    simp only [h_swap_iff, superAndreevSwap_chiralMinusIdx, superAndreevSwap_chiralPlusIdx]
  · ext i j
    rw [mul_superAndreevRotor_transpose_apply, superAndreevRotor_mul_apply]
    dsimp [realSuperchargePlus, realSuperchargeMinus, singleEntry32]
    simp only [h_swap_iff, superAndreevSwap_chiralPlusIdx, superAndreevSwap_chiralMinusIdx]

/-- Split-signature quadratic form $\eta_{5,5}(k) = \sum_{a=0}^4 (k_a^+)^2 - \sum_{a=0}^4 (k_a^-)^2$
on the 10-dimensional conformal lightcone carrier $\mathbb{R}^{5,5}$. -/
def splitConformalQuadratic10 (k_plus k_minus : Fin 5 → ℝ) : ℝ :=
  (∑ a : Fin 5, k_plus a ^ 2) - (∑ a : Fin 5, k_minus a ^ 2)

/-- This bundles independent facts about the matrix-unit witnesses: both square to zero,
scalar multiples remain square-zero, and the supplied null equation implies equality of
the two quadratic sums. The null equation is not used to derive matrix nilpotence or a
gamma-contracted supercharge relation. -/
theorem supercharge_nilpotent_on_lightcone
    (k_plus k_minus : Fin 5 → ℝ)
    (hk : splitConformalQuadratic10 k_plus k_minus = 0)
    (α : Fin 16) (c : ℝ) :
    realSuperchargePlus α * realSuperchargePlus α = 0 ∧
    realSuperchargeMinus α * realSuperchargeMinus α = 0 ∧
    (c • realSuperchargePlus α) * (c • realSuperchargePlus α) = 0 ∧
    (∑ a : Fin 5, k_plus a ^ 2) = (∑ a : Fin 5, k_minus a ^ 2) := by
  have h_plus_sq : realSuperchargePlus α * realSuperchargePlus α = 0 :=
    singleEntry32_mul_of_ne (chiralPlusIdx α) (chiralMinusIdx α)
      (chiralPlusIdx α) (chiralMinusIdx α) (Ne.symm (chiralPlusIdx_ne_chiralMinusIdx α α))
  have h_minus_sq : realSuperchargeMinus α * realSuperchargeMinus α = 0 :=
    singleEntry32_mul_of_ne (chiralMinusIdx α) (chiralPlusIdx α)
      (chiralMinusIdx α) (chiralPlusIdx α) (chiralPlusIdx_ne_chiralMinusIdx α α)
  refine ⟨h_plus_sq, h_minus_sq, ?_, sub_eq_zero.mp hk⟩
  rw [Matrix.smul_mul, Matrix.mul_smul, h_plus_sq, smul_zero, smul_zero]

/-!
## Section 3: matrix trace and common-logit-shift identities
-/

/-- Anticommutator expression formed from a matrix-unit witness and an
arbitrary matrix. No differential-complex structure is asserted. -/
def chiralBrstDifferential32 (α : Fin 16) (X : Matrix (Fin 32) (Fin 32) ℝ) :
    Matrix (Fin 32) (Fin 32) ℝ :=
  realSuperchargePlus α * X + X * realSuperchargePlus α

/-- Ordinary matrix commutator. -/
def brstCoboundary32 (Q M : Matrix (Fin 32) (Fin 32) ℝ) :
    Matrix (Fin 32) (Fin 32) ℝ :=
  Q * M - M * Q

/-- BRST-deformed Souriau–Massieu log-partition (free entropy) potential
$$\Phi_{\text{BRST}}(s, B) = \ln \left(\sum_{j=0}^{m-1} \exp\bigl(s_j + \operatorname{Tr}(B)\bigr)\right)$$
perturbed by a 32-dimensional spinor-space operator fluctuation $B \in M_{32}(\mathbb{R})$. -/
def brstDeformedSouriauPotential {m : ℕ} (s : Fin m → ℝ)
    (B : Matrix (Fin 32) (Fin 32) ℝ) : ℝ :=
  Real.log (∑ j : Fin m, Real.exp (s j + B.trace))

/-- BRST-deformed Boltzmann–Gibbs attention weight
$$A_{\text{BRST}, i}(s, B) = \frac{\exp(s_i + \operatorname{Tr}(B))}{\sum_j \exp(s_j + \operatorname{Tr}(B))}.$$ -/
def brstDeformedSouriauWeight {m : ℕ} (s : Fin m → ℝ)
    (B : Matrix (Fin 32) (Fin 32) ℝ) (i : Fin m) : ℝ :=
  Real.exp (s i + B.trace) / ∑ j : Fin m, Real.exp (s j + B.trace)

/-- Finite matrix identities: a square-zero matrix commutes with its own
anticommutator expression `Q * X + X * Q`; matrix commutators have trace zero;
and a common scalar shift of all logits leaves the Souriau potential, weights,
and moment map unchanged. These statements do not establish a BRST complex or
cohomology invariance. -/
theorem koszul_brst_cohomology_souriau_massieu_invariance
    {m : ℕ} (s v : Fin m → ℝ) (i : Fin m)
    (α : Fin 16) (Q M X : Matrix (Fin 32) (Fin 32) ℝ) :
    let B := brstCoboundary32 Q M
    (realSuperchargePlus α * chiralBrstDifferential32 α X -
       chiralBrstDifferential32 α X * realSuperchargePlus α = 0) ∧
    B.trace = 0 ∧
    brstDeformedSouriauPotential s B = souriauMassieuPotential s ∧
    brstDeformedSouriauWeight s B i = souriauAttentionWeight s i ∧
    (∑ j : Fin m, brstDeformedSouriauWeight s B j * v j) =
      souriauMomentMap s v := by
  intro B
  have hQ_sq : realSuperchargePlus α * realSuperchargePlus α = 0 :=
    singleEntry32_mul_of_ne (chiralPlusIdx α) (chiralMinusIdx α)
      (chiralPlusIdx α) (chiralMinusIdx α) (Ne.symm (chiralPlusIdx_ne_chiralMinusIdx α α))
  have h_brst_sq :
      realSuperchargePlus α * chiralBrstDifferential32 α X -
        chiralBrstDifferential32 α X * realSuperchargePlus α = 0 := by
    dsimp [chiralBrstDifferential32]
    calc
      realSuperchargePlus α * (realSuperchargePlus α * X + X * realSuperchargePlus α) -
          (realSuperchargePlus α * X + X * realSuperchargePlus α) * realSuperchargePlus α
          = (realSuperchargePlus α * realSuperchargePlus α) * X +
              realSuperchargePlus α * X * realSuperchargePlus α -
              (realSuperchargePlus α * X * realSuperchargePlus α +
                X * (realSuperchargePlus α * realSuperchargePlus α)) := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 * X + realSuperchargePlus α * X * realSuperchargePlus α -
            (realSuperchargePlus α * X * realSuperchargePlus α + X * 0) := by
            rw [hQ_sq]
      _ = 0 := by simp
  have h_tr : B.trace = 0 := by
    dsimp [B, brstCoboundary32]
    rw [Matrix.trace_sub, Matrix.trace_mul_comm Q M, sub_self]
  refine ⟨h_brst_sq, h_tr, ?_, ?_, ?_⟩
  · dsimp [brstDeformedSouriauPotential, souriauMassieuPotential, gibbsPartitionSum]
    simp only [h_tr, add_zero]
  · dsimp [brstDeformedSouriauWeight, souriauAttentionWeight, gibbsPartitionSum]
    simp only [h_tr, add_zero]
  · dsimp [brstDeformedSouriauWeight, souriauMomentMap, souriauAttentionWeight,
      gibbsPartitionSum]
    simp only [h_tr, add_zero]

/-! ## Native Clifford facts (separate from the finite matrix-unit model)

The preceding finite matrix constructions are not identified with the native
Clifford spinor representation. The following lemmas state the native facts
directly, using the actual `Q55` null vectors and the volume-eigenspace
submodules owned by `Cl55ChiralSectorPredicateBridge`.
-/

/-- The native real spinor-matrix action of a vector in `V55`. -/
def nativeCl55VectorAction (a : V55) : SpinorMatrix 5 :=
  cl55SpinorAlgEquiv (ι55 a)

/-- A null Clifford vector acts by a square-zero operator in the native real
spinor representation. -/
theorem nativeCl55NullVectorAction_sq_zero
    (a : V55) (ha : Q55 a = 0) :
    nativeCl55VectorAction a * nativeCl55VectorAction a = 0 := by
  have hι : ι55 a * ι55 a = (Q55 a) • (1 : Cl55) := by
    rw [CliffordAlgebra.ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
  calc
    nativeCl55VectorAction a * nativeCl55VectorAction a =
        cl55SpinorAlgEquiv (ι55 a * ι55 a) := (map_mul _ _ _).symm
    _ = cl55SpinorAlgEquiv ((Q55 a) • (1 : Cl55)) := by rw [hι]
    _ = 0 := by rw [map_smul, ha]; simp

/-- Each native Witt null mode yields a square-zero real spinor operator. -/
theorem nativeCl55WittAction_sq_zero (i : Fin 5) :
    nativeCl55VectorAction (n_pair i) *
      nativeCl55VectorAction (n_pair i) = 0 :=
  nativeCl55NullVectorAction_sq_zero (n_pair i) (n_pair_null i)

/-- Native Clifford-vector action exchanges the two real volume eigenspaces. -/
theorem nativeCl55VectorAction_maps_plus_to_minus
    (a : V55) (v : SpinorSpace 5) (hv : chiralPlus v) :
    chiralMinus (Matrix.mulVec (nativeCl55VectorAction a) v) :=
  cl55_odd_generator_maps_plus_to_minus a v hv

/-- A Witt null mode is simultaneously square-zero and odd for the native
Cl(5,5) volume grading. -/
theorem nativeCl55WittAction_nilpotent_and_odd
    (i : Fin 5) (v : SpinorSpace 5) (hv : chiralPlus v) :
    nativeCl55VectorAction (n_pair i) *
        nativeCl55VectorAction (n_pair i) = 0 ∧
      chiralMinus (Matrix.mulVec (nativeCl55VectorAction (n_pair i)) v) :=
  ⟨nativeCl55WittAction_sq_zero i,
    nativeCl55VectorAction_maps_plus_to_minus (n_pair i) v hv⟩

end InfoGeometry.Synthesis.RealChiralSuperchargeBridge
