/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import InfoGeometry.Physics.NuclearRotationalBand

noncomputable section

open Matrix

namespace InfoGeometry.Nuclear.ChiralPRM

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-!
# Frauendorf Triaxial Particle-Rotor Model (PRM) & Nuclear Chirality Bridge

This module formalizes the exact algebraic structure of chiral doublet bands in triaxial nuclei:
1. **Triaxial Inertia Tensor**:
   Moments of inertia $(\mathcal{J}_s, \mathcal{J}_m, \mathcal{J}_l)$ with intermediate-axis dominance
   $\mathcal{J}_m > \mathcal{J}_s, \mathcal{J}_l$ generating a stable aplanar chiral frame.
2. **Chiral Doublet Matrix Model**:
   In the left/right handed basis $\{|L\rangle, |R\rangle\}$, the total PRM Hamiltonian is
   $\mathcal{H}_{\text{PRM}} = \begin{pmatrix} E_{\text{diag}} & -\Delta \\ -\Delta & E_{\text{diag}} \end{pmatrix}$,
   where $\Delta = \langle L | \mathcal{H}_{\text{PRM}} | R \rangle$ is the quantum tunneling matrix element.
3. **Chiral Parity Projectors**:
   $P_\pm = \frac{1}{2}(1 \pm \sigma_1)$ with $P_\pm^2 = P_\pm, P_+ P_- = 0, P_+ + P_- = 1$.
4. **Energy Splitting & Static Degeneracy**:
   $E_\pm = E_{\text{diag}} \mp \Delta \implies \Delta E(I) = E_- - E_+ = 2\Delta$.
   When the chiral geometry is rigidly stable ($\Delta = 0$), $E_+ = E_- = E_{\text{diag}}$ (exact spontaneous chiral symmetry breaking).

All proofs are complete in native Mathlib 4 with 0 `sorry`s.
-/

/-! ### 1. Triaxial Moments of Inertia -/

/-- Hydrodynamic moments of inertia for a triaxial nucleus with intermediate-axis dominance. -/
structure TriaxialMoments where
  J_s : ℝ  -- Short axis
  J_m : ℝ  -- Intermediate axis (dominant moment of inertia)
  J_l : ℝ  -- Long axis
  pos_s : 0 < J_s
  pos_m : 0 < J_m
  pos_l : 0 < J_l
  intermediate_dominant : J_s < J_m ∧ J_l < J_m

/-! ### 2. Chiral Doublet State & Energy Splitting -/

/-- Chiral doublet state parameters in the $\{|L\rangle, |R\rangle\}$ basis. -/
structure ChiralDoubletState where
  E_diag : ℝ  -- Diagonal rotational core energy
  Delta : ℝ   -- Tunneling matrix element between left- and right-handed orientations

/-- Positive parity chiral band energy: $E_+ = E_{\text{diag}} - \Delta$. -/
def energyPlus (state : ChiralDoubletState) : ℝ :=
  state.E_diag - state.Delta

/-- Negative parity chiral band energy: $E_- = E_{\text{diag}} + \Delta$. -/
def energyMinus (state : ChiralDoubletState) : ℝ :=
  state.E_diag + state.Delta

/-- **THE CHIRAL DOUBLET ENERGY SPLITTING THEOREM**:
    $\Delta E(I) = E_-(I) - E_+(I) = 2\Delta$. -/
theorem chiral_doublet_energy_splitting (state : ChiralDoubletState) :
  energyMinus state - energyPlus state = 2 * state.Delta := by
  dsimp [energyMinus, energyPlus]
  ring

/-- The physical (nonnegative) gap is independent of the sign convention for
the off-diagonal tunnelling matrix element. -/
theorem chiral_doublet_absolute_gap (state : ChiralDoubletState) :
    |energyMinus state - energyPlus state| = 2 * |state.Delta| := by
  rw [chiral_doublet_energy_splitting]
  rw [abs_mul]
  norm_num

/-- **THE CHIRAL STATIC DEGENERACY THEOREM**:
    In the rigid limit with zero tunneling ($\Delta = 0$), the doublet bands are strictly degenerate:
    $E_+ = E_- = E_{\text{diag}}$. -/
theorem chiral_static_degeneracy (state : ChiralDoubletState) (h_tunnel : state.Delta = 0) :
    energyPlus state = energyMinus state := by
  dsimp [energyPlus, energyMinus]
  rw [h_tunnel]
  ring

/-! ### 3. Matrix Model & Fundamental Peirce Projectors -/

/-- The $2\times 2$ PRM Hamiltonian in the $\{|L\rangle, |R\rangle\}$ basis. -/
def prmMatrix (state : ChiralDoubletState) : M2R :=
  !![state.E_diag, -state.Delta; -state.Delta, state.E_diag]

/-- The chiral flip operator $\mathcal{A} = \sigma_1$ exchanging $|L\rangle \leftrightarrow |R\rangle$. -/
def chiralFlip : M2R := !![0, 1; 1, 0]

/-- Positive parity Peirce projector $P_+ = \frac{1}{2}(1 + \sigma_1)$. -/
def peircePlus : M2R := !![1/2, 1/2; 1/2, 1/2]

/-- Negative parity Peirce projector $P_- = \frac{1}{2}(1 - \sigma_1)$. -/
def peirceMinus : M2R := !![1/2, -1/2; -1/2, 1/2]

/-- **Theorem**: Chiral flip involution: $\mathcal{A}^2 = 1$. -/
theorem chiralFlip_sq : chiralFlip * chiralFlip = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiralFlip]

/-- **Theorem**: $P_+$ is idempotent: $P_+^2 = P_+$. -/
theorem peircePlus_sq : peircePlus * peircePlus = peircePlus := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [peircePlus]; ring)

/-- **Theorem**: $P_-$ is idempotent: $P_-^2 = P_-$. -/
theorem peirceMinus_sq : peirceMinus * peirceMinus = peirceMinus := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [peirceMinus]; ring)

/-- **Theorem**: $P_+$ and $P_-$ are orthogonal: $P_+ P_- = 0$. -/
theorem peirce_orthogonal : peircePlus * peirceMinus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [peircePlus, peirceMinus]; ring)

/-- **Theorem**: Completeness of chiral Peirce decomposition: $P_+ + P_- = 1$. -/
theorem peirce_completeness : peircePlus + peirceMinus = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [peircePlus, peirceMinus]; ring)

/-- The chiral doublet Hamiltonian has the Peirce spectral normal form. -/
theorem prmMatrix_peirce_spectral_decomposition (state : ChiralDoubletState) :
    prmMatrix state = energyPlus state • peircePlus + energyMinus state • peirceMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [prmMatrix, energyPlus, energyMinus, peircePlus, peirceMinus]
  <;> ring

/-- **Theorem**: Characteristic determinant of the chiral doublet matrix:
    $\det(\mathcal{H}_{\text{PRM}} - E I_2) = (E - E_+)(E - E_-)$. -/
theorem prm_determinant_eq (state : ChiralDoubletState) (E : ℝ) :
    det (prmMatrix state - E • (1 : M2R)) = (E - energyPlus state) * (E - energyMinus state) := by
  dsimp [prmMatrix, energyPlus, energyMinus]
  simp [det_fin_two]
  ring

/-! ### 4. Intrinsic K-Projection, Signature Inversion, Peierls--Yoccoz Restoration & D2 Projector -/

section IntrinsicSignatureAndPeierlsYoccoz

open InfoGeometry.Physics.NuclearRotationalBand
open scoped BigOperators

/-- `(2I + 1)`-dimensional intrinsic/laboratory integer-spin rotor space `Fin (2 * I + 1) → ℂ`. -/
abbrev RotorSpace (I : ℕ) := SpinSpace (2 * I)

/-- Matrix algebra `Matrix (Fin (2 * I + 1)) (Fin (2 * I + 1)) ℂ` on `RotorSpace I`. -/
abbrev RotorMat (I : ℕ) := Matrix (Fin (2 * I + 1)) (Fin (2 * I + 1)) ℂ

/-- Intrinsic basis ket `|I, K⟩` indexed by `k : Fin (2 * I + 1)` with `K = I - k`. -/
def bodyKet (I : ℕ) (k : Fin (2 * I + 1)) : RotorSpace I :=
  spinKet (2 * I) k

/-- Intrinsic axial angular momentum projection `K = I - k ∈ {-I, ..., I}`. -/
def bodyKValue (I : ℕ) (k : Fin (2 * I + 1)) : ℤ :=
  (I : ℤ) - (k.val : ℤ)

/-- Reflected index corresponding to `-K` (`k ↦ 2I - k`). -/
def negKIndex (I : ℕ) (k : Fin (2 * I + 1)) : Fin (2 * I + 1) :=
  ⟨2 * I - k.val, by omega⟩

@[simp] theorem negKIndex_involutive (I : ℕ) (k : Fin (2 * I + 1)) :
    negKIndex I (negKIndex I k) = k := by
  ext
  simp [negKIndex]
  omega

theorem bodyKValue_negKIndex (I : ℕ) (k : Fin (2 * I + 1)) :
    bodyKValue I (negKIndex I k) = -bodyKValue I k := by
  unfold bodyKValue negKIndex
  have hk : k.val ≤ 2 * I := by omega
  rw [Nat.cast_sub hk]
  push_cast
  ring

/-- Index corresponding to `K = 0` (`k = I`). -/
def kZeroIndex (I : ℕ) : Fin (2 * I + 1) :=
  ⟨I, Nat.lt_succ_of_le (by omega)⟩

@[simp] theorem bodyKValue_kZeroIndex (I : ℕ) :
    bodyKValue I (kZeroIndex I) = 0 := by
  simp [bodyKValue, kZeroIndex]

@[simp] theorem negKIndex_kZeroIndex (I : ℕ) :
    negKIndex I (kZeroIndex I) = kZeroIndex I := by
  ext; simp [negKIndex, kZeroIndex]; omega

/-- Intrinsic body-frame projection operator `J_3^{\text{body}}`. -/
def bodyJ3 (I : ℕ) : Module.End ℂ (RotorSpace I) :=
  spinZ (2 * I)

theorem bodyJ3_ket (I : ℕ) (k : Fin (2 * I + 1)) :
    bodyJ3 I (bodyKet I k) = (bodyKValue I k : ℂ) • bodyKet I k := by
  have h := spinZ_ket (2 * I) k
  change bodyJ3 I (bodyKet I k) = spinMValue (2 * I) k • bodyKet I k at h
  rw [h]
  congr 1
  unfold spinMValue bodyKValue
  push_cast
  ring

/-- Signature inversion operator `R_x(π)` sending `|I, K⟩ ↦ (-1)^{I - K} |I, -K⟩`. -/
def signatureInversionOp (I : ℕ) : Module.End ℂ (RotorSpace I) where
  toFun ψ k := ((-1 : ℂ) ^ (2 * I - k.val)) * ψ (negKIndex I k)
  map_add' ψ φ := by ext k; simp [mul_add]
  map_smul' a ψ := by ext k; simp; ring

theorem signatureInversionOp_ket (I : ℕ) (k : Fin (2 * I + 1)) :
    signatureInversionOp I (bodyKet I k) =
      ((-1 : ℂ) ^ k.val) • bodyKet I (negKIndex I k) := by
  ext j
  by_cases hj : j = negKIndex I k
  · subst hj
    have hpow : 2 * I - (negKIndex I k).val = k.val := by
      simp [negKIndex]; omega
    simp [signatureInversionOp, bodyKet, spinKet, hpow]
  · have hne : negKIndex I j ≠ k := by
      intro heq
      apply hj
      calc
        j = negKIndex I (negKIndex I j) := (negKIndex_involutive I j).symm
        _ = negKIndex I k := by rw [heq]
    simp [signatureInversionOp, bodyKet, spinKet, hj, hne]

/-- For integer spin `I`, `R_x(π)^2 = 1`. -/
theorem signatureInversionOp_sq (I : ℕ) :
    signatureInversionOp I * signatureInversionOp I = 1 := by
  apply LinearMap.ext; intro ψ; ext k
  simp only [Module.End.mul_apply, signatureInversionOp, LinearMap.coe_mk, AddHom.coe_mk,
    negKIndex_involutive, Module.End.one_apply]
  have hk : (negKIndex I k).val = 2 * I - k.val := rfl
  have hsum : (2 * I - k.val) + (2 * I - (2 * I - k.val)) = 2 * I := by omega
  rw [← mul_assoc, ← pow_add, hk, hsum, pow_mul]
  norm_num

theorem signatureInversionOp_anticomm_bodyJ3 (I : ℕ) :
    signatureInversionOp I * bodyJ3 I = -(bodyJ3 I * signatureInversionOp I) := by
  apply LinearMap.ext; intro ψ; ext k
  simp only [Module.End.mul_apply, LinearMap.neg_apply, Pi.neg_apply, signatureInversionOp,
    bodyJ3, spinZ, LinearMap.coe_mk, AddHom.coe_mk, spinMValue, negKIndex]
  have hk : k.val ≤ 2 * I := by omega
  rw [Nat.cast_sub hk]
  push_cast
  ring

/-- Signature projector `(1 / 2)(1 + r R_x(π))` for signature eigenvalue `r = ±1`. -/
def signatureProjector (I : ℕ) (r : ℤ) : Module.End ℂ (RotorSpace I) :=
  (1 / 2 : ℂ) • (1 + (r : ℂ) • signatureInversionOp I)

/-- Signature-symmetrized state `|I, K, r⟩ = (1/2)(|I, K⟩ + r (-1)^{I-K} |I, -K⟩)`. -/
def signatureSymmetrizedKet (I : ℕ) (k : Fin (2 * I + 1)) (r : ℤ) : RotorSpace I :=
  signatureProjector I r (bodyKet I k)

theorem signatureProjector_idempotent (I : ℕ) {r : ℤ} (hr : r = 1 ∨ r = -1) :
    signatureProjector I r * signatureProjector I r = signatureProjector I r := by
  have hr2 : (r : ℂ) * (r : ℂ) = 1 := by rcases hr with rfl | rfl <;> norm_num
  apply LinearMap.ext; intro ψ
  have hsq : signatureInversionOp I (signatureInversionOp I ψ) = ψ := by
    simpa [Module.End.mul_apply] using
      congrArg (fun op : Module.End ℂ (RotorSpace I) => op ψ) (signatureInversionOp_sq I)
  dsimp [signatureProjector]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.one_apply, map_add, map_smul, hsq]
  calc
    (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (ψ + (r : ℂ) • signatureInversionOp I ψ) +
        (r : ℂ) • ((1 / 2 : ℂ) • (signatureInversionOp I ψ + (r : ℂ) • ψ)))
        = (1 / 4 : ℂ) • ψ + (1 / 4 : ℂ) • (((r : ℂ) * (r : ℂ)) • ψ) +
            (1 / 2 : ℂ) • ((r : ℂ) • signatureInversionOp I ψ) := by module
    _ = (1 / 2 : ℂ) • (ψ + (r : ℂ) • signatureInversionOp I ψ) := by
          rw [hr2, one_smul]; module

theorem signatureProjector_ortho (I : ℕ) :
    signatureProjector I 1 * signatureProjector I (-1) = 0 := by
  apply LinearMap.ext; intro ψ
  have hsq : signatureInversionOp I (signatureInversionOp I ψ) = ψ := by
    simpa [Module.End.mul_apply] using
      congrArg (fun op : Module.End ℂ (RotorSpace I) => op ψ) (signatureInversionOp_sq I)
  dsimp [signatureProjector]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.one_apply, LinearMap.zero_apply, map_add, map_smul, hsq]
  module

theorem signatureProjector_sum (I : ℕ) :
    signatureProjector I 1 + signatureProjector I (-1) = 1 := by
  apply LinearMap.ext; intro ψ
  change signatureProjector I 1 ψ + signatureProjector I (-1) ψ = ψ
  dsimp [signatureProjector]
  push_cast
  module

theorem signatureSymmetrizedKet_eigen (I : ℕ) (k : Fin (2 * I + 1)) {r : ℤ}
    (hr : r = 1 ∨ r = -1) :
    signatureInversionOp I (signatureSymmetrizedKet I k r) =
      (r : ℂ) • signatureSymmetrizedKet I k r := by
  have hr2 : (r : ℂ) * (r : ℂ) = 1 := by rcases hr with rfl | rfl <;> norm_num
  have hsq : signatureInversionOp I (signatureInversionOp I (bodyKet I k)) = bodyKet I k := by
    simpa [Module.End.mul_apply] using
      congrArg (fun op : Module.End ℂ (RotorSpace I) => op (bodyKet I k))
        (signatureInversionOp_sq I)
  dsimp [signatureSymmetrizedKet, signatureProjector]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, map_smul,
    map_add, hsq]
  calc
    (1 / 2 : ℂ) • (signatureInversionOp I (bodyKet I k) + (r : ℂ) • bodyKet I k)
        = (1 / 2 : ℂ) • (((r : ℂ) * (r : ℂ)) • signatureInversionOp I (bodyKet I k) +
            (r : ℂ) • bodyKet I k) := by rw [hr2, one_smul]
    _ = (r : ℂ) • ((1 / 2 : ℂ) • (bodyKet I k + (r : ℂ) • signatureInversionOp I (bodyKet I k))) := by
          module

/-- **K = 0 Signature Selection Rule**:
A `K = 0` signature-symmetrized state with signature `r ∈ {+1, -1}` vanishes identically
if and only if `r ≠ (-1)^I` (so `r = +1` allows even `I` only and `r = -1` allows odd `I` only). -/
theorem signatureSymmetrizedKet_kZero_vanishes_iff (I : ℕ) {r : ℤ} (hr : r = 1 ∨ r = -1) :
    signatureSymmetrizedKet I (kZeroIndex I) r = 0 ↔ r ≠ (-1 : ℤ) ^ I := by
  have hRx : signatureInversionOp I (bodyKet I (kZeroIndex I)) =
      ((-1 : ℂ) ^ I) • bodyKet I (kZeroIndex I) := by
    rw [signatureInversionOp_ket, negKIndex_kZeroIndex]
    rfl
  have hket : signatureSymmetrizedKet I (kZeroIndex I) r =
      ((1 + (r : ℂ) * (-1 : ℂ) ^ I) / 2) • bodyKet I (kZeroIndex I) := by
    dsimp [signatureSymmetrizedKet, signatureProjector]
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, hRx]
    module
  have hkne : bodyKet I (kZeroIndex I) ≠ 0 := by
    intro h
    have hv := congrFun h (kZeroIndex I)
    simp [bodyKet, spinKet] at hv
  rw [hket, smul_eq_zero]
  have h1 : (((1 + (r : ℂ) * (-1 : ℂ) ^ I) / 2) = 0 ↔ r ≠ (-1 : ℤ) ^ I) := by
    rcases Nat.even_or_odd' I with ⟨m, rfl | rfl⟩
    · have hp1 : (-1 : ℂ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
      have hp2 : (-1 : ℤ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
      rw [hp1, hp2]
      rcases hr with rfl | rfl <;> norm_num
    · have hp1 : (-1 : ℂ) ^ (2 * m + 1) = -1 := by rw [pow_add, pow_mul]; norm_num
      have hp2 : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_add, pow_mul]; norm_num
      rw [hp1, hp2]
      rcases hr with rfl | rfl <;> norm_num
  constructor
  · rintro (hz | hbot)
    · exact h1.mp hz
    · exact absurd hbot hkne
  · intro hne
    exact Or.inl (h1.mpr hne)

/-- Peierls--Yoccoz angular-momentum restoration matrix unit `P^I_{MK}` on `RotorMat I`. -/
def peierlsYoccozOp (I : ℕ) (m k : Fin (2 * I + 1)) : RotorMat I :=
  Matrix.single m k 1

/-- Matrix representation of `J_3` (`bodyJ3` / lab `J_3`) on `RotorMat I`. -/
def bodyJ3Matrix (I : ℕ) : RotorMat I :=
  Matrix.diagonal (fun k => (bodyKValue I k : ℂ))

theorem peierlsYoccozOp_mul (I : ℕ) (m k k' l : Fin (2 * I + 1)) :
    peierlsYoccozOp I m k * peierlsYoccozOp I k' l =
      if k = k' then peierlsYoccozOp I m l else 0 := by
  ext i j
  by_cases hkk' : k = k'
  · subst hkk'
    simp only [peierlsYoccozOp, Matrix.mul_apply, Matrix.single, ↓reduceIte]
    rw [Finset.sum_eq_single k]
    · by_cases him : m = i <;> by_cases hlj : l = j <;> simp [him, hlj]
    · intro b _ hbk
      simp [hbk.symm]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  · simp only [peierlsYoccozOp, Matrix.mul_apply, Matrix.single, hkk', ↓reduceIte,
      Matrix.zero_apply]
    refine Finset.sum_eq_zero ?_
    intro b _
    by_cases hbk : k = b
    · subst hbk; simp [Ne.symm hkk']
    · simp [hbk]

theorem peierlsYoccozOp_conjTranspose (I : ℕ) (m k : Fin (2 * I + 1)) :
    (peierlsYoccozOp I m k)ᴴ = peierlsYoccozOp I k m := by
  ext i j
  by_cases h1 : i = k <;> by_cases h2 : j = m <;>
    simp [peierlsYoccozOp, Matrix.conjTranspose_apply, Matrix.single, h1, h2, and_comm]

theorem peierlsYoccozOp_sum_diag (I : ℕ) :
    (∑ k : Fin (2 * I + 1), peierlsYoccozOp I k k) = 1 := by
  ext i j
  simp only [Matrix.sum_apply, peierlsYoccozOp, Matrix.single, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi; simp [hbi]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · rw [if_neg hij]
    refine Finset.sum_eq_zero ?_
    intro b _
    by_cases hbi : b = i
    · subst hbi; simp [hij]
    · simp [hbi]

theorem bodyJ3Matrix_mul_peierlsYoccozOp (I : ℕ) (m k : Fin (2 * I + 1)) :
    bodyJ3Matrix I * peierlsYoccozOp I m k =
      (bodyKValue I m : ℂ) • peierlsYoccozOp I m k := by
  ext i j
  simp only [bodyJ3Matrix, peierlsYoccozOp, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.single]
  rw [Finset.sum_eq_single i]
  · by_cases him : m = i <;> by_cases hkj : k = j <;> simp [him, hkj]
  · intro b _ hbi; simp [Ne.symm hbi]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem peierlsYoccozOp_mul_bodyJ3Matrix (I : ℕ) (m k : Fin (2 * I + 1)) :
    peierlsYoccozOp I m k * bodyJ3Matrix I =
      (bodyKValue I k : ℂ) • peierlsYoccozOp I m k := by
  ext i j
  simp only [bodyJ3Matrix, peierlsYoccozOp, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.single]
  rw [Finset.sum_eq_single j]
  · by_cases him : m = i <;> by_cases hkj : k = j <;> simp [him, hkj]
  · intro b _ hbj; simp [hbj]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem bodyJ3_eq_toLin_bodyJ3Matrix (I : ℕ) :
    bodyJ3 I = Matrix.toLin' (bodyJ3Matrix I) := by
  apply LinearMap.ext; intro ψ; ext i
  simp only [bodyJ3, spinZ, LinearMap.coe_mk, AddHom.coe_mk, spinMValue,
    Matrix.toLin'_apply, bodyJ3Matrix, Matrix.mulVec_diagonal]
  congr 1
  unfold bodyKValue
  push_cast
  ring

theorem peierlsYoccozOp_restores_lab_body_and_casimir (I : ℕ) (m k : Fin (2 * I + 1))
    (ψ : RotorSpace I) :
    let P := Matrix.toLin' (peierlsYoccozOp I m k)
    bodyJ3 I (P ψ) = (bodyKValue I m : ℂ) • P ψ ∧
    P (bodyJ3 I ψ) = (bodyKValue I k : ℂ) • P ψ ∧
    spinCasimirOp (2 * I) (P ψ) = ((I : ℂ) * ((I : ℂ) + 1)) • P ψ := by
  intro P
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (fun M : RotorMat I => Matrix.toLin' M ψ)
      (bodyJ3Matrix_mul_peierlsYoccozOp I m k)
    simpa [P, bodyJ3_eq_toLin_bodyJ3Matrix, Matrix.toLin'_mul, Module.End.mul_apply] using h
  · have h := congrArg (fun M : RotorMat I => Matrix.toLin' M ψ)
      (peierlsYoccozOp_mul_bodyJ3Matrix I m k)
    simpa [P, bodyJ3_eq_toLin_bodyJ3Matrix, Matrix.toLin'_mul, Module.End.mul_apply] using h
  · have hc := congrArg (fun op : Module.End ℂ (RotorSpace I) => op (P ψ))
      (spinCasimirOp_integer_eq_scalar I)
    simpa using hc

/-- Finite `D_2` `z`-axis `π`-rotation `R_z(π) |I, K⟩ = (-1)^K |I, K⟩`. -/
def rotationZPiOp (I : ℕ) : Module.End ℂ (RotorSpace I) where
  toFun ψ k := (if (I + k.val) % 2 = 0 then (1 : ℂ) else -1) * ψ k
  map_add' ψ φ := by ext k; simp [mul_add]
  map_smul' a ψ := by ext k; simp

/-- Finite `D_2` `y`-axis `π`-rotation `R_y(π) = R_z(π) * R_x(π)`. -/
def rotationYPiOp (I : ℕ) : Module.End ℂ (RotorSpace I) :=
  rotationZPiOp I * signatureInversionOp I

theorem rotationZPiOp_sq (I : ℕ) :
    rotationZPiOp I * rotationZPiOp I = 1 := by
  apply LinearMap.ext; intro ψ; ext k
  by_cases h : (I + k.val) % 2 = 0 <;>
    simp [Module.End.mul_apply, rotationZPiOp, h]

theorem rotationZPiOp_comm_signatureInversionOp (I : ℕ) :
    rotationZPiOp I * signatureInversionOp I = signatureInversionOp I * rotationZPiOp I := by
  apply LinearMap.ext; intro ψ; ext k
  have hmod : (I + (negKIndex I k).val) % 2 = (I + k.val) % 2 := by
    simp [negKIndex]
    omega
  by_cases h : (I + k.val) % 2 = 0 <;>
    simp [Module.End.mul_apply, rotationZPiOp, signatureInversionOp, h, hmod]

theorem rotationYPiOp_sq (I : ℕ) :
    rotationYPiOp I * rotationYPiOp I = 1 := by
  unfold rotationYPiOp
  calc
    rotationZPiOp I * signatureInversionOp I * (rotationZPiOp I * signatureInversionOp I)
        = (rotationZPiOp I * rotationZPiOp I) *
            (signatureInversionOp I * signatureInversionOp I) := by
          calc
            rotationZPiOp I * signatureInversionOp I * (rotationZPiOp I * signatureInversionOp I)
                = rotationZPiOp I * (signatureInversionOp I * rotationZPiOp I) *
                    signatureInversionOp I := by noncomm_ring
            _ = rotationZPiOp I * (rotationZPiOp I * signatureInversionOp I) *
                    signatureInversionOp I := by
                  rw [← rotationZPiOp_comm_signatureInversionOp]
            _ = (rotationZPiOp I * rotationZPiOp I) *
                    (signatureInversionOp I * signatureInversionOp I) := by noncomm_ring
    _ = 1 := by rw [rotationZPiOp_sq, signatureInversionOp_sq, mul_one]

/-- Explicit finite `D_2` symmetry-group projector
`P_{D_2}(r_x, r_z) = (1/4)(1 + r_x R_x(π) + r_z R_z(π) + r_x r_z R_y(π))`. -/
def d2Projector (I : ℕ) (rx rz : ℤ) : Module.End ℂ (RotorSpace I) :=
  (1 / 4 : ℂ) • (1 + (rx : ℂ) • signatureInversionOp I +
    (rz : ℂ) • rotationZPiOp I + ((rx * rz : ℤ) : ℂ) • rotationYPiOp I)

theorem d2Projector_eq_product (I : ℕ) (rx rz : ℤ) :
    d2Projector I rx rz =
      signatureProjector I rx * ((1 / 2 : ℂ) • (1 + (rz : ℂ) • rotationZPiOp I)) := by
  apply LinearMap.ext; intro ψ
  have hcomm : signatureInversionOp I (rotationZPiOp I ψ) =
      rotationZPiOp I (signatureInversionOp I ψ) := by
    simpa [Module.End.mul_apply] using
      (congrArg (fun op : Module.End ℂ (RotorSpace I) => op ψ)
        (rotationZPiOp_comm_signatureInversionOp I)).symm
  dsimp [d2Projector, signatureProjector, rotationYPiOp]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.one_apply, map_add, map_smul, hcomm, Int.cast_mul]
  module

theorem d2Projector_idempotent (I : ℕ) {rx rz : ℤ}
    (hrx : rx = 1 ∨ rx = -1) (hrz : rz = 1 ∨ rz = -1) :
    d2Projector I rx rz * d2Projector I rx rz = d2Projector I rx rz := by
  have hrz2 : (rz : ℂ) * (rz : ℂ) = 1 := by rcases hrz with rfl | rfl <;> norm_num
  let pz := (1 / 2 : ℂ) • (1 + (rz : ℂ) • rotationZPiOp I)
  have hpz_idem : pz * pz = pz := by
    apply LinearMap.ext; intro ψ
    have hsq : rotationZPiOp I (rotationZPiOp I ψ) = ψ := by
      simpa [Module.End.mul_apply] using
        congrArg (fun op : Module.End ℂ (RotorSpace I) => op ψ) (rotationZPiOp_sq I)
    dsimp [pz]
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply, map_add, map_smul, hsq]
    calc
      (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (ψ + (rz : ℂ) • rotationZPiOp I ψ) +
          (rz : ℂ) • ((1 / 2 : ℂ) • (rotationZPiOp I ψ + (rz : ℂ) • ψ)))
          = (1 / 4 : ℂ) • ψ + (1 / 4 : ℂ) • (((rz : ℂ) * (rz : ℂ)) • ψ) +
              (1 / 2 : ℂ) • ((rz : ℂ) • rotationZPiOp I ψ) := by module
      _ = (1 / 2 : ℂ) • (ψ + (rz : ℂ) • rotationZPiOp I ψ) := by rw [hrz2, one_smul]; module
  have hcomm_p : signatureProjector I rx * pz = pz * signatureProjector I rx := by
    apply LinearMap.ext; intro ψ
    have hcomm : signatureInversionOp I (rotationZPiOp I ψ) =
        rotationZPiOp I (signatureInversionOp I ψ) := by
      simpa [Module.End.mul_apply] using
        (congrArg (fun op : Module.End ℂ (RotorSpace I) => op ψ)
          (rotationZPiOp_comm_signatureInversionOp I)).symm
    dsimp [signatureProjector, pz]
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply, map_add, map_smul, hcomm]
    module
  rw [d2Projector_eq_product]
  change (signatureProjector I rx * pz) * (signatureProjector I rx * pz) =
    signatureProjector I rx * pz
  calc
    (signatureProjector I rx * pz) * (signatureProjector I rx * pz)
        = signatureProjector I rx * (pz * signatureProjector I rx) * pz := by noncomm_ring
    _ = (signatureProjector I rx * signatureProjector I rx) * (pz * pz) := by
          rw [← hcomm_p]; noncomm_ring
    _ = signatureProjector I rx * pz := by
          rw [signatureProjector_idempotent I hrx, hpz_idem]

theorem d2Projector_completeness (I : ℕ) :
    d2Projector I 1 1 + d2Projector I 1 (-1) +
      d2Projector I (-1) 1 + d2Projector I (-1) (-1) = 1 := by
  dsimp [d2Projector]
  push_cast
  module

theorem d2Projector_kZero_vanishes (I : ℕ) {rx rz : ℤ}
    (hrx : rx = 1 ∨ rx = -1) (hrz : rz = 1 ∨ rz = -1)
    (hforbid : ¬ (rz = 1 ∧ rx = (-1 : ℤ) ^ I)) :
    d2Projector I rx rz (bodyKet I (kZeroIndex I)) = 0 := by
  have hRz : rotationZPiOp I (bodyKet I (kZeroIndex I)) = bodyKet I (kZeroIndex I) := by
    ext j
    by_cases hj : j = kZeroIndex I
    · subst hj
      have hmod : (I + (kZeroIndex I).val) % 2 = 0 := by simp [kZeroIndex]; omega
      simp [rotationZPiOp, hmod, bodyKet]
    · by_cases hm : (I + j.val) % 2 = 0 <;> simp [rotationZPiOp, bodyKet, spinKet, hj, hm]
  have hfact := congrArg (fun op : Module.End ℂ (RotorSpace I) => op (bodyKet I (kZeroIndex I)))
    (d2Projector_eq_product I rx rz)
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.one_apply, hRz] at hfact
  by_cases hrz1 : rz = 1
  · subst hrz1
    have hrxne : rx ≠ (-1 : ℤ) ^ I := fun h => hforbid ⟨rfl, h⟩
    have hvan := (signatureSymmetrizedKet_kZero_vanishes_iff I hrx).mpr hrxne
    change signatureProjector I rx (bodyKet I (kZeroIndex I)) = 0 at hvan
    rw [hfact]
    have hsmul : (1 / 2 : ℂ) • (bodyKet I (kZeroIndex I) + ((1 : ℤ) : ℂ) • bodyKet I (kZeroIndex I)) =
        bodyKet I (kZeroIndex I) := by push_cast; module
    rw [hsmul, hvan]
  · have hrzm1 : rz = -1 := by rcases hrz with rfl | rfl <;> tauto
    subst hrzm1
    have hzero : (1 / 2 : ℂ) • (bodyKet I (kZeroIndex I) +
        ((-1 : ℤ) : ℂ) • bodyKet I (kZeroIndex I)) = 0 := by
      push_cast; module
    rw [hfact, hzero, map_zero]

/-! ### 5. Triaxial Rotor Hamiltonian, D2 Invariance & Chiral Triad Inversion -/

/-- Triaxial asymmetric-rotor Hamiltonian
`H_rot = J_x^2 / (2 J_s) + J_y^2 / (2 J_m) + J_z^2 / (2 J_l)` on `RotorSpace I`. -/
def triaxialRotorHamiltonian (tm : TriaxialMoments) (I : ℕ) :
    Module.End ℂ (RotorSpace I) :=
  ((1 / (2 * tm.J_s) : ℝ) : ℂ) • (spinX (2 * I) * spinX (2 * I)) +
  ((1 / (2 * tm.J_m) : ℝ) : ℂ) • (spinY (2 * I) * spinY (2 * I)) +
  ((1 / (2 * tm.J_l) : ℝ) : ℂ) • (spinZ (2 * I) * spinZ (2 * I))

theorem TriaxialMoments.inv_moment_intermediate_minimal (tm : TriaxialMoments) :
    1 / (2 * tm.J_m) < 1 / (2 * tm.J_s) ∧ 1 / (2 * tm.J_m) < 1 / (2 * tm.J_l) := by
  have h2s : 0 < 2 * tm.J_s := by linarith [tm.pos_s]
  have h2l : 0 < 2 * tm.J_l := by linarith [tm.pos_l]
  have h2m : 0 < 2 * tm.J_m := by linarith [tm.pos_m]
  exact ⟨one_div_lt_one_div_of_lt h2s (by linarith [tm.intermediate_dominant.1]),
    one_div_lt_one_div_of_lt h2l (by linarith [tm.intermediate_dominant.2])⟩

private theorem signatureInversionOp_mul_spinPlus (I : ℕ) :
    signatureInversionOp I * spinPlus (2 * I) = -(spinMinus (2 * I) * signatureInversionOp I) := by
  apply LinearMap.ext; intro ψ; ext k
  by_cases hk0 : 0 < k.val
  · have hnk_lt : (negKIndex I k).val < 2 * I := by dsimp [negKIndex]; omega
    have hidx : (⟨(negKIndex I k).val + 1, by omega⟩ : Fin (2 * I + 1)) =
        negKIndex I ⟨k.val - 1, by omega⟩ := by
      ext; dsimp [negKIndex]; omega
    have hcoeff : spinPlusCoeff (2 * I) (negKIndex I k).val = spinMinusCoeff (2 * I) k.val := by
      have hk1 : k.val = (k.val - 1) + 1 := (Nat.sub_add_cancel hk0).symm
      rw [hk1, ← spinPlusCoeff_eq_spinMinusCoeff_succ]
      unfold spinPlusCoeff
      congr 2
      simp only [negKIndex]
      have hk1' : k.val ≤ 2 * I := by omega
      have hk2 : 1 ≤ k.val := hk0
      rw [Nat.cast_sub hk1', Nat.cast_sub hk2]
      push_cast; ring
    have hsign : (-1 : ℂ) ^ (2 * I - k.val) = -((-1 : ℂ) ^ (2 * I - (k.val - 1))) := by
      have hk1 : 2 * I - (k.val - 1) = (2 * I - k.val) + 1 := by omega
      rw [hk1, pow_succ]; ring
    simp only [Module.End.mul_apply, LinearMap.neg_apply, Pi.neg_apply, signatureInversionOp,
      spinPlus, spinMinus, hk0, hnk_lt, ↓reduceDIte, LinearMap.coe_mk, AddHom.coe_mk, hidx,
      hcoeff]
    rw [hsign]; ring
  · have hk_eq : k.val = 0 := by omega
    have hnot : ¬ (negKIndex I k).val < 2 * I := by simp [negKIndex, hk_eq]
    simp only [Module.End.mul_apply, LinearMap.neg_apply, Pi.neg_apply, signatureInversionOp,
      spinPlus, spinMinus, hk0, hnot, ↓reduceDIte, LinearMap.coe_mk, AddHom.coe_mk,
      mul_zero, neg_zero]

private theorem signatureInversionOp_mul_spinMinus (I : ℕ) :
    signatureInversionOp I * spinMinus (2 * I) = -(spinPlus (2 * I) * signatureInversionOp I) := by
  have h := signatureInversionOp_mul_spinPlus I
  have hsq : ∀ v, signatureInversionOp I (signatureInversionOp I v) = v := by
    intro v
    simpa [Module.End.mul_apply] using
      congrArg (fun op : Module.End ℂ (RotorSpace I) => op v) (signatureInversionOp_sq I)
  have h1 : ∀ v, spinMinus (2 * I) (signatureInversionOp I v) =
      -(signatureInversionOp I (spinPlus (2 * I) v)) := by
    intro v
    have hv := congrArg (fun op : Module.End ℂ (RotorSpace I) => op v) h
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at hv
    have hv2 := congrArg Neg.neg hv
    simpa [neg_neg] using hv2.symm
  apply LinearMap.ext; intro ψ
  have h2 := h1 (signatureInversionOp I ψ)
  rw [hsq] at h2
  have h3 := congrArg (signatureInversionOp I) h2
  rw [map_neg, hsq] at h3
  simpa [Module.End.mul_apply, LinearMap.neg_apply] using h3

theorem signatureInversionOp_comm_spinX (I : ℕ) :
    signatureInversionOp I * spinX (2 * I) = -(spinX (2 * I) * signatureInversionOp I) := by
  unfold spinX
  rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
    signatureInversionOp_mul_spinPlus, signatureInversionOp_mul_spinMinus]
  module

theorem signatureInversionOp_comm_spinY (I : ℕ) :
    signatureInversionOp I * spinY (2 * I) = spinY (2 * I) * signatureInversionOp I := by
  unfold spinY
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul,
    signatureInversionOp_mul_spinPlus, signatureInversionOp_mul_spinMinus]
  module

theorem signatureInversionOp_comm_triaxialRotorHamiltonian (tm : TriaxialMoments) (I : ℕ) :
    signatureInversionOp I * triaxialRotorHamiltonian tm I =
      triaxialRotorHamiltonian tm I * signatureInversionOp I := by
  have hxx : signatureInversionOp I * (spinX (2 * I) * spinX (2 * I)) =
      (spinX (2 * I) * spinX (2 * I)) * signatureInversionOp I := by
    apply LinearMap.ext; intro ψ
    have hx : ∀ v, signatureInversionOp I (spinX (2 * I) v) =
        -(spinX (2 * I) (signatureInversionOp I v)) := by
      intro v
      simpa [Module.End.mul_apply, LinearMap.neg_apply] using
        congrArg (fun op : Module.End ℂ (RotorSpace I) => op v) (signatureInversionOp_comm_spinX I)
    simp only [Module.End.mul_apply, hx, map_neg, neg_neg]
  have hyy : signatureInversionOp I * (spinY (2 * I) * spinY (2 * I)) =
      (spinY (2 * I) * spinY (2 * I)) * signatureInversionOp I := by
    apply LinearMap.ext; intro ψ
    have hy : ∀ v, signatureInversionOp I (spinY (2 * I) v) =
        spinY (2 * I) (signatureInversionOp I v) := by
      intro v
      simpa [Module.End.mul_apply] using
        congrArg (fun op : Module.End ℂ (RotorSpace I) => op v) (signatureInversionOp_comm_spinY I)
    simp only [Module.End.mul_apply, hy]
  have hzz : signatureInversionOp I * (spinZ (2 * I) * spinZ (2 * I)) =
      (spinZ (2 * I) * spinZ (2 * I)) * signatureInversionOp I := by
    apply LinearMap.ext; intro ψ
    have hz : ∀ v, signatureInversionOp I (spinZ (2 * I) v) =
        -(spinZ (2 * I) (signatureInversionOp I v)) := by
      intro v
      simpa [bodyJ3, Module.End.mul_apply, LinearMap.neg_apply] using
        congrArg (fun op : Module.End ℂ (RotorSpace I) => op v)
          (signatureInversionOp_anticomm_bodyJ3 I)
    simp only [Module.End.mul_apply, hz, map_neg, neg_neg]
  unfold triaxialRotorHamiltonian
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hxx, hyy, hzz]

/-- Three non-coplanar angular momentum vectors `(R, j_pi, j_nu)` forming a chiral triad. -/
structure ChiralAngularTriad where
  coreR : Fin 3 → ℝ
  protonJ : Fin 3 → ℝ
  neutronJ : Fin 3 → ℝ
  aplanar : Matrix.det !![coreR 0, coreR 1, coreR 2;
    protonJ 0, protonJ 1, protonJ 2;
    neutronJ 0, neutronJ 1, neutronJ 2] ≠ 0

/-- Chiral handedness volume `det(R, j_π, j_ν)` of the angular momentum triad. -/
def ChiralAngularTriad.handedness (T : ChiralAngularTriad) : ℝ :=
  Matrix.det !![T.coreR 0, T.coreR 1, T.coreR 2;
    T.protonJ 0, T.protonJ 1, T.protonJ 2;
    T.neutronJ 0, T.neutronJ 1, T.neutronJ 2]

private lemma det_neg_fin_three (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℝ) :
    -a0 * (-b1 * -c2 - -b2 * -c1) + -a1 * -(-b0 * -c2 - -b2 * -c0) +
        -a2 * (-b0 * -c1 - -b1 * -c0) =
      -(a0 * (b1 * c2 - b2 * c1) + a1 * -(b0 * c2 - b2 * c0) + a2 * (b0 * c1 - b1 * c0)) := by
  ring

/-- Time-reversal / triad inversion `(R, j_π, j_ν) ↦ (-R, -j_π, -j_ν)` exchanging
left- and right-handed chiral geometries (`|L⟩ ↔ |R⟩`). -/
def ChiralAngularTriad.invert (T : ChiralAngularTriad) : ChiralAngularTriad where
  coreR := -T.coreR
  protonJ := -T.protonJ
  neutronJ := -T.neutronJ
  aplanar := by
    have hneg : !![(-T.coreR) 0, (-T.coreR) 1, (-T.coreR) 2;
        (-T.protonJ) 0, (-T.protonJ) 1, (-T.protonJ) 2;
        (-T.neutronJ) 0, (-T.neutronJ) 1, (-T.neutronJ) 2] =
        -!![T.coreR 0, T.coreR 1, T.coreR 2;
          T.protonJ 0, T.protonJ 1, T.protonJ 2;
          T.neutronJ 0, T.neutronJ 1, T.neutronJ 2] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [hneg, Matrix.det_neg, Fintype.card_fin]
    norm_num
    exact T.aplanar

theorem ChiralAngularTriad.invert_handedness (T : ChiralAngularTriad) :
    T.invert.handedness = -T.handedness := by
  dsimp [ChiralAngularTriad.handedness, ChiralAngularTriad.invert]
  have hneg : !![-T.coreR 0, -T.coreR 1, -T.coreR 2;
      -T.protonJ 0, -T.protonJ 1, -T.protonJ 2;
      -T.neutronJ 0, -T.neutronJ 1, -T.neutronJ 2] =
      -!![T.coreR 0, T.coreR 1, T.coreR 2;
        T.protonJ 0, T.protonJ 1, T.protonJ 2;
        T.neutronJ 0, T.neutronJ 1, T.neutronJ 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hneg, Matrix.det_neg, Fintype.card_fin]
  norm_num

theorem ChiralAngularTriad.invert_involutive (T : ChiralAngularTriad) :
    T.invert.invert = T := by
  cases T
  simp [ChiralAngularTriad.invert]

/-- Mapping the two-state left/right chiral triad pair `(T, T.invert)` onto the `2 × 2` PRM
basis `{|L⟩, |R⟩}`, realizing triad inversion as `chiralFlip` (`σ₁`) and connecting the
triaxial PRM Hamiltonian `prmMatrix` to the Peirce chiral-parity projectors. -/
theorem chiral_triad_inversion_prm_bridge
    (T : ChiralAngularTriad) (state : ChiralDoubletState) :
    T.invert.handedness = -T.handedness ∧
    chiralFlip * prmMatrix state * chiralFlip = prmMatrix state ∧
    prmMatrix state * peircePlus = energyPlus state • peircePlus ∧
    prmMatrix state * peirceMinus = energyMinus state • peirceMinus := by
  refine ⟨T.invert_handedness, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [chiralFlip, prmMatrix]
  · rw [prmMatrix_peirce_spectral_decomposition, add_mul, smul_mul_assoc, smul_mul_assoc,
      peircePlus_sq, show peirceMinus * peircePlus = 0 from by
        ext i j; fin_cases i <;> fin_cases j <;> (simp [peirceMinus, peircePlus]; ring),
      smul_zero, add_zero]
  · rw [prmMatrix_peirce_spectral_decomposition, add_mul, smul_mul_assoc, smul_mul_assoc,
      peirce_orthogonal, peirceMinus_sq, smul_zero, zero_add]

end IntrinsicSignatureAndPeierlsYoccoz

end InfoGeometry.Nuclear.ChiralPRM
