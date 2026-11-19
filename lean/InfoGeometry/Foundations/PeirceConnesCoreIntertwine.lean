/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Foundations.InfoGeometryCoreLibrary
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Core
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.PinchedSuperExtension
import InfoGeometry.Algebra.ConnesLottYangBaxterPoset
import InfoGeometry.Meta
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Epistemology.CoagulatedArchetypeSynthesis
import InfoGeometry.Canonical.AttentionPolarizedGibbsBridge
import InfoGeometry.LLM.KreinAttentionEnergy
import InfoGeometry.Neurosymbolic.LLMAttentionKreinMellinBridge
import InfoGeometry.Epistemology.JungianEpistemicCompiler
import InfoGeometry.Dynamics.TomitaTakesaki
import InfoGeometry.Dynamics.KmsBoundary
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Four-Pillar Intertwining Module: Peirce Bi-Sandwich, Connes-Lott & Petz Information Geometry

Unifies the four core mathematical pillars of information geometry:
1. **Pillar I & II (Defect-Fisher Intertwining)**:
   Connects the Peirce Casimir defect $V = Q_+ + Q_-$ of the Pauli-X observable to the
   off-diagonal BKM quantum Fisher metric in `qubitGibbsState`:
   $V = 1 \wedge \mathcal{I}_{\mathrm{BKM}}(\rho, \sigma_X) = 2 / \mathrm{logMean}(p_0, p_1) \wedge \mathrm{Tr}(\rho \cdot V) = 1$.
2. **Pillar II & IV (Noncommutative Dirac Mass Gap)**:
   Connects the Connes–Lott Higgs boundary-twist matrix $K(1, w, w)$ to the two-sheeted
   operator-valued Dirac mass gap $K^2 = (1 + w^2) I_2$.
3. **Pillar II & III (Integrable Yang–Baxter Markov Transport)**:
   Proves unconditional commutativity of the physical Yang–Baxter transfer operators
   $[\tau(w_1, \eta_1), \tau(w_2, \eta_2)] = 0$.
4. **Cross-Pillar (Petz Hierarchy Degeneracy & Peirce Corner Vanishing)**:
   Proves that the classical collapse of Petz monotone metrics ($SLD = BKM = GM = RLD$)
   occurs if and only if the off-diagonal Peirce corner vanishes ($N_+ = 0 \iff V = 0$),
   with strict separation ($SLD < BKM < GM < RLD$) when $V = 1$.
-/

namespace InfoGeometry.Foundations.PeirceConnesCoreIntertwine

open KuboMoriBogoliubov
open InfoGeometry.OperatorAlgebra.GNSRepresentationAndPetzMonotoneMetrics
open InfoGeometry.Foundations.InfoGeometryCoreLibrary
open InfoGeometry.OperatorAlgebra.PeirceBiSandwich
open InfoGeometry.Algebra.ConnesLottYangBaxterPoset
open InfoGeometry.Algebra.ConnesLottYangBaxterPoset.Mat2
open InfoGeometry.MetaCompiler
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Epistemology.CoagulatedArchetypeSynthesis
open InfoGeometry.Neurosymbolic.LLMAttentionKreinMellinBridge
open InfoGeometry.Epistemology.JungianEpistemicCompiler
open InfoGeometry.Dynamics
open InfoGeometry.Dynamics.TomitaTakesaki
open InfoGeometry.Canonical.Attention
open InfoGeometry.LLM.KreinAttentionEnergy
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.GrandCanonical

/-- Reference diagonal projector $P_0 = \mathrm{diag}(1, 0)$ on $\mathbb{C}^2$. -/
def qubitP0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- Reference diagonal projector $P_0 = \mathrm{diag}(1, 0)$ on $\mathbb{R}^2$. -/
def realP0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- Off-diagonal Pauli-X matrix on $\mathbb{R}^2$. -/
def realX : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Explicit non-commutativity witness for OpenGauss T16 compliance:
the Peirce projection idempotent `qubitP0` and off-diagonal generator `pauliXTangent` do not commute. -/
theorem qubitP0_pauliXTangent_noncommutative : qubitP0 * pauliXTangent ≠ pauliXTangent * qubitP0 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [qubitP0, pauliXTangent, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Explicit non-commutativity witness for real 2x2 matrix carrier (OpenGauss T16 compliance). -/
theorem real_matrix_two_noncommutative : realP0 * realX ≠ realX * realP0 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [realP0, realX, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Diagonal density operator representation of a faithful density state on `Fin 2`. -/
def diagState (ρ : FaithfulDensityState (Fin 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => (ρ.eigenvalues i : ℂ))

/-- Physical Yang–Baxter transfer operator on $V_1 \otimes V_2$ (`Mat4 R`). -/
def physTransfer {R : Type*} [CommRing R] (w η : R) : Mat4 R :=
  Mat4.Lax w η

instance {R : Type*} [CommRing R] : Zero (Mat4 R) := ⟨Mat4.zero⟩

/-- Commutator on `Mat4 R`. -/
def comm {R : Type*} [CommRing R] (A B : Mat4 R) : Mat4 R :=
  Mat4.comm A B

/-! ### Structural Projection and Corner Evaluation Lemmas -/

lemma qubitP0_mul (A : Matrix (Fin 2) (Fin 2) ℂ) :
    qubitP0 * A = !![A 0 0, A 0 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitP0, Matrix.mul_apply, Fin.sum_univ_two]

lemma one_sub_qubitP0 : (1 : Matrix (Fin 2) (Fin 2) ℂ) - qubitP0 = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitP0, Matrix.sub_apply]

lemma Nplus_qubitP0_eq (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Nplus qubitP0 A = !![0, A 0 1; 0, 0] := by
  dsimp [Nplus]
  rw [qubitP0_mul, one_sub_qubitP0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma one_sub_qubitP0_mul (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 - qubitP0) * A = !![0, 0; A 1 0, A 1 1] := by
  rw [one_sub_qubitP0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma Nminus_qubitP0_eq (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Nminus qubitP0 A = !![0, 0; A 1 0, 0] := by
  dsimp [Nminus]
  rw [one_sub_qubitP0_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitP0, Matrix.mul_apply, Fin.sum_univ_two]

lemma casimirV_qubitP0_eq (A : Matrix (Fin 2) (Fin 2) ℂ) :
    casimirV qubitP0 A A = !![A 0 1 * A 1 0, 0; 0, A 1 0 * A 0 1] := by
  dsimp [casimirV, Qplus, Qminus]
  rw [Nplus_qubitP0_eq, Nminus_qubitP0_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply]

lemma delta_one {B : Type*} [Ring B] : delta (1 : B) = 0 := by
  dsimp [delta]
  rw [sq, mul_one, sub_self]

lemma qubitP0_idem : delta qubitP0 = 0 := by
  dsimp [delta]
  rw [sq, qubitP0_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitP0, Matrix.sub_apply]

lemma star_pauliXTangent : star pauliXTangent = pauliXTangent := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliXTangent, Matrix.star_apply]

lemma qubit_uZero_pauliX :
    uZero qubitP0 pauliXTangent pauliXTangent = !![0, 1; -1, 0] := by
  dsimp [uZero, jOp]
  rw [Nplus_qubitP0_eq, Nminus_qubitP0_eq, casimirV_qubitP0_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliXTangent]

/-! ### Pillar I & II: Pauli-X Peirce Casimir Defect and BKM Fisher Metric -/

lemma qubit_P0_pauliX_Nplus :
    Nplus qubitP0 pauliXTangent = !![0, 1; 0, 0] := by
  rw [Nplus_qubitP0_eq]
  simp [pauliXTangent]

lemma qubit_P0_pauliX_Nminus :
    Nminus qubitP0 pauliXTangent = !![0, 0; 1, 0] := by
  rw [Nminus_qubitP0_eq]
  simp [pauliXTangent]

lemma qubit_P0_pauliX_casimirV :
    casimirV qubitP0 pauliXTangent pauliXTangent = 1 := by
  rw [casimirV_qubitP0_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliXTangent]

/-- Intertwining Theorem 1: Connects the Peirce Casimir defect $V$ of the Pauli-X observable
to the off-diagonal BKM Fisher metric in `qubitGibbsState`:
$V = 1 \wedge \mathcal{I}_{\mathrm{BKM}}(\rho, \sigma_X) = 2 / \mathrm{logMean}(p_0, p_1) \wedge \mathrm{Tr}(\rho \cdot V) = 1$. -/
@[rep_depth thermo]
theorem qubitGibbsState_peirce_fisher_defect :
    let P0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
    let A : Matrix (Fin 2) (Fin 2) ℂ := pauliXTangent
    let V : Matrix (Fin 2) (Fin 2) ℂ := casimirV P0 A A
    V = 1 ∧
    bkmTangentMetric qubitGibbsState pauliXTangent =
      2 / logMean (qubitGibbsState.eigenvalues 0) (qubitGibbsState.eigenvalues 1) ∧
    Matrix.trace (diagState qubitGibbsState * V) = 1 := by
  intro P0 A V
  have hV : V = 1 := by
    dsimp [V, A, P0]
    exact qubit_P0_pauliX_casimirV
  have hx00 : pauliXTangent 0 0 = 0 := by simp [pauliXTangent]
  have hx01 : pauliXTangent 0 1 = 1 := by simp [pauliXTangent]
  have hx10 : pauliXTangent 1 0 = 1 := by simp [pauliXTangent]
  have hx11 : pauliXTangent 1 1 = 0 := by simp [pauliXTangent]
  have hbkm :
      bkmTangentMetric qubitGibbsState pauliXTangent =
        2 / logMean (qubitGibbsState.eigenvalues 0) (qubitGibbsState.eigenvalues 1) := by
    unfold bkmTangentMetric
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    rw [hx00, hx01, hx10, hx11]
    simp only [Complex.normSq_zero, Complex.normSq_one, zero_div, zero_add, add_zero]
    rw [bkmWeight_eq_logMean, bkmWeight_eq_logMean]
    rw [logMean_symm (qubitGibbsState.eigenvalues 1) (qubitGibbsState.eigenvalues 0)]
    ring
  have htr : Matrix.trace (diagState qubitGibbsState * V) = 1 := by
    rw [hV, mul_one]
    dsimp [diagState]
    rw [Matrix.trace_diagonal, Fin.sum_univ_two]
    have he0 : qubitGibbsState.eigenvalues 0 = 1 / 4 := by simp [qubitGibbsState]
    have he1 : qubitGibbsState.eigenvalues 1 = 3 / 4 := by simp [qubitGibbsState]
    rw [he0, he1]
    norm_num
  exact ⟨hV, hbkm, htr⟩

/-! ### Pillar II & IV: Connes-Lott Higgs Matrix and Two-Sheeted Dirac Mass Gap -/

/-- Intertwining Theorem 2: Connects the Connes-Lott Higgs boundary-twist matrix $K(1, w, w)$
to the two-sheeted operator-valued Dirac mass gap $K^2 = (1 + w^2) I_2$. -/
@[rep_depth operator]
theorem connes_lott_higgs_peirce_mass_gap (w : ℝ) :
    let K := higgsK 1 w w
    let MatK := toMatrix K
    MatK * MatK = (1 + w ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    MatK = Matrix.diagonal ![1, -1] + w • !![0, 1; 1, 0] := by
  intro K MatK
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [MatK, K, higgsK, toMatrix, Matrix.mul_apply, Matrix.smul_apply,
            Fin.sum_univ_two] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [MatK, K, higgsK, toMatrix, Matrix.add_apply]

/-! ### Pillar II & III: Yang-Baxter Transfer Operator Markov Commutativity -/

/-- Intertwining Theorem 3: Proves unconditional commutativity of physical Yang–Baxter
transfer operators: $\mathrm{comm}(\tau(w_1, \eta_1), \tau(w_2, \eta_2)) = 0$. -/
@[rep_depth transport]
theorem yang_baxter_transfer_markov_commutativity {R : Type*} [CommRing R]
    (w1 w2 eta1 eta2 : R) :
    comm (physTransfer w1 eta1) (physTransfer w2 eta2) = 0 := by
  change comm (physTransfer w1 eta1) (physTransfer w2 eta2) = Mat4.zero
  ext <;> dsimp [comm, physTransfer, Mat4.comm, Mat4.Lax, Mat4.mul, Mat4.sub,
                 Mat4.add, Mat4.smul, Mat4.one, Mat4.P_swap, Mat4.zero] <;> ring

/-! ### Cross-Pillar: Classical Petz Metric Collapse and Peirce Corner Vanishing -/

lemma pauliZTangent_01 : pauliZTangent 0 1 = 0 := by
  dsimp [pauliZTangent]
  exact Matrix.diagonal_apply_ne _ (by decide)

lemma pauliZTangent_10 : pauliZTangent 1 0 = 0 := by
  dsimp [pauliZTangent]
  exact Matrix.diagonal_apply_ne _ (by decide)

lemma pauliZTangent_matrix : pauliZTangent = !![(1 : ℂ), 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZTangent, pauliZDiag]

lemma qubit_P0_pauliZ_Nplus :
    Nplus qubitP0 pauliZTangent = 0 := by
  rw [Nplus_qubitP0_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZTangent_01]

lemma qubit_P0_pauliZ_Nminus :
    Nminus qubitP0 pauliZTangent = 0 := by
  rw [Nminus_qubitP0_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZTangent_10]

lemma qubit_P0_pauliZ_casimirV :
    casimirV qubitP0 pauliZTangent pauliZTangent = 0 := by
  rw [casimirV_qubitP0_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZTangent_01, pauliZTangent_10]

lemma Nplus_qubitP0_eq_zero_iff (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Nplus qubitP0 A = 0 ↔ A 0 1 = 0 := by
  rw [Nplus_qubitP0_eq]
  constructor
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    exact h01
  · intro h01
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h01]

lemma casimirV_qubitP0_eq_zero_iff (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : star A = A) :
    casimirV qubitP0 A A = 0 ↔ A 0 1 = 0 := by
  have hstar01 : A 1 0 = star (A 0 1) := by
    have hs := congr_fun (congr_fun hA 1) 0
    simp [Matrix.star_apply] at hs
    exact hs.symm
  rw [casimirV_qubitP0_eq]
  constructor
  · intro h
    have h00 := congr_fun (congr_fun h 0) 0
    simp [hstar01] at h00
    exact h00
  · intro h01
    have h10 : A 1 0 = 0 := by rw [hstar01, h01, star_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h01, h10]

lemma qubit_diagDensityMatrix_commutes_iff (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : star A = A) :
    diagDensityMatrix qubitGibbsState * A = A * diagDensityMatrix qubitGibbsState ↔ A 0 1 = 0 := by
  rw [diagDensityMatrix_commutes_iff]
  have hstar01 : A 1 0 = star (A 0 1) := by
    have hs := congr_fun (congr_fun hA 1) 0
    simp [Matrix.star_apply] at hs
    exact hs.symm
  have he0 : qubitGibbsState.eigenvalues 0 = 1 / 4 := by simp [qubitGibbsState]
  have he1 : qubitGibbsState.eigenvalues 1 = 3 / 4 := by simp [qubitGibbsState]
  have hne01 : qubitGibbsState.eigenvalues 0 ≠ qubitGibbsState.eigenvalues 1 := by
    rw [he0, he1]; norm_num
  have hne10 : qubitGibbsState.eigenvalues 1 ≠ qubitGibbsState.eigenvalues 0 := by
    rw [he0, he1]; norm_num
  constructor
  · intro hcomm
    exact hcomm 0 1 hne01
  · intro h01 i j
    revert i j
    intro i j hne
    fin_cases i <;> fin_cases j
    · contradiction
    · exact h01
    · change A 1 0 = 0
      rw [hstar01, h01, star_zero]
    · contradiction

/-- Intertwining Theorem 4: Classical Petz metric degeneracy ($SLD = BKM = GM = RLD$)
holds if and only if the off-diagonal Peirce corner vanishes ($N_+ = 0 \iff V = 0$),
and strict Morozova–Chentsov–Petz separation ($SLD < BKM < GM < RLD$) holds when $V = 1$. -/
@[rep_depth operator]
theorem classical_collapse_iff_peirce_corner_zero :
    let P0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
    (∀ (A : Matrix (Fin 2) (Fin 2) ℂ) (_hA : star A = A),
      ((sldTangentMetric qubitGibbsState A = rldTangentMetric qubitGibbsState A ∧
        sldTangentMetric qubitGibbsState A = bkmTangentMetric qubitGibbsState A ∧
        bkmTangentMetric qubitGibbsState A = geomTangentMetric qubitGibbsState A) ↔
       Nplus P0 A = 0) ∧
      (Nplus P0 A = 0 ↔ casimirV P0 A A = 0)) ∧
    (let AZ := pauliZTangent
     casimirV P0 AZ AZ = 0 ∧ Nplus P0 AZ = 0 ∧
     sldTangentMetric qubitGibbsState AZ = 16 / 3 ∧
     bkmTangentMetric qubitGibbsState AZ = 16 / 3 ∧
     geomTangentMetric qubitGibbsState AZ = 16 / 3 ∧
     rldTangentMetric qubitGibbsState AZ = 16 / 3) ∧
    (let AX := pauliXTangent
     casimirV P0 AX AX = 1 ∧
     sldTangentMetric qubitGibbsState AX < bkmTangentMetric qubitGibbsState AX ∧
     bkmTangentMetric qubitGibbsState AX < geomTangentMetric qubitGibbsState AX ∧
     geomTangentMetric qubitGibbsState AX < rldTangentMetric qubitGibbsState AX) := by
  intro P0
  have hP0 : P0 = qubitP0 := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    have hN := Nplus_qubitP0_eq_zero_iff A
    have hV := casimirV_qubitP0_eq_zero_iff A hA
    have hcomm := qubit_diagDensityMatrix_commutes_iff A hA
    have hsld_rld := sld_eq_rld_iff_commutes qubitGibbsState A
    have hchain := petz_monotone_metric_hierarchy qubitGibbsState A
    rw [hP0]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro ⟨h_sr, _, _⟩
      have hc := hsld_rld.mp h_sr
      have h01 := hcomm.mp hc
      exact (Nplus_qubitP0_eq_zero_iff A).mpr h01
    · intro hN0
      have h01 := (Nplus_qubitP0_eq_zero_iff A).mp hN0
      have hc := hcomm.mpr h01
      have h_sr := hsld_rld.mpr hc
      have h_sb : sldTangentMetric qubitGibbsState A = bkmTangentMetric qubitGibbsState A := by
        linarith [hchain.1, hchain.2.1, hchain.2.2]
      have h_bg : bkmTangentMetric qubitGibbsState A = geomTangentMetric qubitGibbsState A := by
        linarith [hchain.1, hchain.2.1, hchain.2.2]
      exact ⟨h_sr, h_sb, h_bg⟩
    · rw [hN, hV]
  · dsimp only [pauliZTangent]
    rw [hP0]
    have hV0 := qubit_P0_pauliZ_casimirV
    have hN0 := qubit_P0_pauliZ_Nplus
    have hcoll := qubitGibbsState_pauliZ_classical_collapse
    exact ⟨hV0, hN0, hcoll.1, hcoll.2.1, hcoll.2.2.1, hcoll.2.2.2⟩
  · dsimp only [pauliXTangent]
    rw [hP0]
    have hV1 := qubit_P0_pauliX_casimirV
    have hsep := qubitGibbsState_pauliX_strict_hierarchy
    exact ⟨hV1, hsep.1, hsep.2.1, hsep.2.2⟩

/-! ### Metaprogramming & Typed Archetype Registration -/

/-- Typed archetype for Intertwining Theorem 1 (Peirce Fisher defect). -/
def qubitFisherDefectArchetype : TypedArchetype Unit .proved where
  name     := `qubitFisherDefectArchetype
  phase    := 2
  claim    := fun _ =>
    let P0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
    let A : Matrix (Fin 2) (Fin 2) ℂ := pauliXTangent
    let V : Matrix (Fin 2) (Fin 2) ℂ := casimirV P0 A A
    V = 1 ∧
    bkmTangentMetric qubitGibbsState pauliXTangent =
      2 / logMean (qubitGibbsState.eigenvalues 0) (qubitGibbsState.eigenvalues 1) ∧
    Matrix.trace (diagState qubitGibbsState * V) = 1
  evidence := fun _ => qubitGibbsState_peirce_fisher_defect

#register_archetype qubitFisherDefectArchetype
#audit_archetype qubitFisherDefectArchetype

/-- Typed archetype for Intertwining Theorem 2 (Connes-Lott Higgs mass gap). -/
def connesLottHiggsMassGapArchetype : TypedArchetype ℝ .proved where
  name     := `connesLottHiggsMassGapArchetype
  phase    := 2
  claim    := fun w =>
    let K := higgsK 1 w w
    let MatK := toMatrix K
    MatK * MatK = (1 + w ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    MatK = Matrix.diagonal ![1, -1] + w • !![0, 1; 1, 0]
  evidence := fun w => connes_lott_higgs_peirce_mass_gap w

#register_archetype connesLottHiggsMassGapArchetype
#audit_archetype connesLottHiggsMassGapArchetype

/-- Typed archetype for Intertwining Theorem 3 (Yang-Baxter transfer commutativity). -/
def yangBaxterTransferMarkovArchetype : TypedArchetype (ℝ × ℝ × ℝ × ℝ) .proved where
  name     := `yangBaxterTransferMarkovArchetype
  phase    := 2
  claim    := fun ⟨w1, w2, eta1, eta2⟩ =>
    comm (physTransfer w1 eta1) (physTransfer w2 eta2) = 0
  evidence := fun ⟨w1, w2, eta1, eta2⟩ =>
    yang_baxter_transfer_markov_commutativity w1 w2 eta1 eta2

#register_archetype yangBaxterTransferMarkovArchetype
#audit_archetype yangBaxterTransferMarkovArchetype

/-- Typed archetype for Intertwining Theorem 4 (Classical Petz collapse & corner vanishing). -/
def petzClassicalCollapseArchetype : TypedArchetype Unit .proved where
  name     := `petzClassicalCollapseArchetype
  phase    := 2
  claim    := fun _ =>
    let P0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
    (∀ (A : Matrix (Fin 2) (Fin 2) ℂ) (_hA : star A = A),
      ((sldTangentMetric qubitGibbsState A = rldTangentMetric qubitGibbsState A ∧
        sldTangentMetric qubitGibbsState A = bkmTangentMetric qubitGibbsState A ∧
        bkmTangentMetric qubitGibbsState A = geomTangentMetric qubitGibbsState A) ↔
       Nplus P0 A = 0) ∧
      (Nplus P0 A = 0 ↔ casimirV P0 A A = 0)) ∧
    (let AZ := pauliZTangent
     casimirV P0 AZ AZ = 0 ∧ Nplus P0 AZ = 0 ∧
     sldTangentMetric qubitGibbsState AZ = 16 / 3 ∧
     bkmTangentMetric qubitGibbsState AZ = 16 / 3 ∧
     geomTangentMetric qubitGibbsState AZ = 16 / 3 ∧
     rldTangentMetric qubitGibbsState AZ = 16 / 3) ∧
    (let AX := pauliXTangent
     casimirV P0 AX AX = 1 ∧
     sldTangentMetric qubitGibbsState AX < bkmTangentMetric qubitGibbsState AX ∧
     bkmTangentMetric qubitGibbsState AX < geomTangentMetric qubitGibbsState AX ∧
     geomTangentMetric qubitGibbsState AX < rldTangentMetric qubitGibbsState AX)
  evidence := fun _ => classical_collapse_iff_peirce_corner_zero

#register_archetype petzClassicalCollapseArchetype
#audit_archetype petzClassicalCollapseArchetype

/-! ### Spinorial & Attention Latent Space Intertwining Bridges -/

/-- Spinor bridge identifying the Peirce bi-sandwich Casimir defect on `Mat2C` with the
integral unitary defect law on-shell: $\delta(V) = V^2 - V = 0$. -/
@[rep_depth operator]
theorem peirce_spinor_casimir_unitary_defect_bridge :
    let P0 : Mat2C := qubitP0
    let AX : Mat2C := pauliXTangent
    let V : Mat2C := casimirV P0 AX AX
    V = 1 ∧ delta V = 0 ∧
    star (uZero P0 AX (star AX)) * (uZero P0 AX (star AX)) - 1 = 0 := by
  intro P0 AX V
  have hV1 : V = 1 := qubit_P0_pauliX_casimirV
  have hdelV : delta V = 0 := by rw [hV1]; exact delta_one
  have hu0 : uZero P0 AX (star AX) = !![0, 1; -1, 0] := by
    rw [star_pauliXTangent]
    exact qubit_uZero_pauliX
  have hstar_u0 : star (uZero P0 AX (star AX)) = !![0, -1; 1, 0] := by
    rw [hu0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]
  have hprod : star (uZero P0 AX (star AX)) * (uZero P0 AX (star AX)) = 1 := by
    rw [hstar_u0, hu0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hunit : star (uZero P0 AX (star AX)) * (uZero P0 AX (star AX)) - 1 = 0 := by
    rw [hprod, sub_self]
  exact ⟨hV1, hdelV, hunit⟩

/-- Bridge connecting the qubit Gibbs state $\rho = \mathrm{diag}(1/4, 3/4)$ to the
attention Gibbs distribution with energy levels $E = [-\ln(1/4), -\ln(3/4)]$ at $\beta = 1$. -/
@[rep_depth thermo]
theorem qubit_gibbs_attention_energy_bridge :
    let E : Fin 2 → ℝ := fun i => -Real.log (qubitGibbsState.eigenvalues i)
    let p : Fin 2 → ℝ := fun i => Real.exp (-E i) / ∑ k : Fin 2, Real.exp (-E k)
    (∀ i : Fin 2, p i = qubitGibbsState.eigenvalues i) ∧
    (qubitGibbsState.eigenvalues 0 < qubitGibbsState.eigenvalues 1) := by
  intro E p
  have he0 : qubitGibbsState.eigenvalues 0 = 1 / 4 := by simp [qubitGibbsState]
  have he1 : qubitGibbsState.eigenvalues 1 = 3 / 4 := by simp [qubitGibbsState]
  have hp0_pos : 0 < qubitGibbsState.eigenvalues 0 := by rw [he0]; norm_num
  have hp1_pos : 0 < qubitGibbsState.eigenvalues 1 := by rw [he1]; norm_num
  have hsum_exp : (∑ k : Fin 2, Real.exp (-E k)) = 1 := by
    rw [Fin.sum_univ_two]
    dsimp [E]
    rw [neg_neg, neg_neg, Real.exp_log hp0_pos, Real.exp_log hp1_pos]
    rw [he0, he1]
    norm_num
  have h_pi : ∀ i : Fin 2, p i = qubitGibbsState.eigenvalues i := by
    intro i
    dsimp [p]
    rw [hsum_exp, div_one]
    dsimp [E]
    rw [neg_neg]
    fin_cases i
    · exact Real.exp_log hp0_pos
    · exact Real.exp_log hp1_pos
  have h_order : qubitGibbsState.eigenvalues 0 < qubitGibbsState.eigenvalues 1 := by
    rw [he0, he1]; norm_num
  exact ⟨h_pi, h_order⟩

/-! ### Centralizer ("True Name") vs. Off-Diagonal Shadow & Twin Thermal Waves -/

/-- Intertwining Theorem 5 (Epistemic Centralizer & Twin Thermal Reflection Bridge):
Connects the Peirce Casimir defect $V = Q_+ + Q_-$ and `FiniteSpinAlgebra` spinor carriers
to `CoagulatedArchetypeSynthesis` and `JungianEpistemicCompiler`:
1. Under `jungianArchetypeOperator`, `animusLogos` (`evenGrade P0 A`) is the chiral centralizer
   component ($S A_{\mathrm{even}} S = A_{\mathrm{even}}$), where vanishing off-diagonal corner
   $N_+ = 0$ yields classical Petz metric collapse ($SLD = BKM = GM = RLD$).
2. `shadowProjection` (`oddGrade P0 A`) is the off-diagonal shadow ($S A_{\mathrm{odd}} S = -A_{\mathrm{odd}}$),
   driving quantum Petz splitting ($SLD < BKM < GM < RLD$) when non-zero.
3. `selfIndividuation` ($V = 1$) commutes with both $P_0$ and Tomita–Takesaki modular conjugation
   $J$ ($J V J = V$), while $J H J = -H$ reflects forward and backward twin thermal generators. -/
@[rep_depth operator]
theorem peirce_casimir_spin_coagulated_poset_bridge :
    let P0 : Matrix (Fin 2) (Fin 2) ℂ := qubitP0
    let AX : Matrix (Fin 2) (Fin 2) ℂ := pauliXTangent
    let AZ : Matrix (Fin 2) (Fin 2) ℂ := pauliZTangent
    let S : Matrix (Fin 2) (Fin 2) ℂ := pauliZTangent
    let J : Mat2C := TomitaTakesaki.modularConjugation
    let V : Matrix (Fin 2) (Fin 2) ℂ := casimirV P0 AX AX
    -- 1. AnimusLogos / Centralizer preserves S-grading and gives classical collapse on AZ:
    S * (jungianArchetypeOperator P0 AX AX AZ .animusLogos) * S =
      jungianArchetypeOperator P0 AX AX AZ .animusLogos ∧
    Nplus P0 AZ = 0 ∧
    -- 2. ShadowProjection / Off-diagonal shadow negates S-grading on AX:
    S * (jungianArchetypeOperator P0 AX AX AX .shadowProjection) * S =
      -(jungianArchetypeOperator P0 AX AX AX .shadowProjection) ∧
    Nplus P0 AX ≠ 0 ∧
    -- 3. SelfIndividuation Casimir defect V = 1 commutes with P0 and J:
    V = 1 ∧
    P0 * V = V * P0 ∧
    J * V * J = V ∧
    -- 4. Modular conjugation reflects the thermal Hamiltonian:
    J * KmsBoundary.modularHamiltonian * J = -KmsBoundary.modularHamiltonian := by
  intro P0 AX AZ S J V
  have hV1 : V = 1 := qubit_P0_pauliX_casimirV
  have hN0 : Nplus P0 AZ = 0 := qubit_P0_pauliZ_Nplus
  have hN1 : Nplus P0 AX ≠ 0 := by
    rw [qubit_P0_pauliX_Nplus]
    intro h
    have h01 := congr_fun (congr_fun h 0) 1
    norm_num at h01
  have h_even_AZ : jungianArchetypeOperator P0 AX AX AZ .animusLogos = AZ := by
    change evenGrade qubitP0 pauliZTangent = pauliZTangent
    rw [pauliZTangent_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [evenGrade, qubitP0, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_two]
  have h_odd_AX : jungianArchetypeOperator P0 AX AX AX .shadowProjection = AX := by
    change Nplus qubitP0 pauliXTangent + Nminus qubitP0 pauliXTangent = pauliXTangent
    rw [qubit_P0_pauliX_Nplus, qubit_P0_pauliX_Nminus]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliXTangent]
  have h_comm_S_AZ : S * AZ * S = AZ := by
    change pauliZTangent * pauliZTangent * pauliZTangent = pauliZTangent
    rw [pauliZTangent_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h_anticomm_S_AX : S * AX * S = -AX := by
    change pauliZTangent * pauliXTangent * pauliZTangent = -pauliXTangent
    rw [pauliZTangent_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliXTangent, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]
  have h_comm_P0_V : P0 * V = V * P0 := by rw [hV1, mul_one, one_mul]
  have h_J_inv : J * J = 1 := by dsimp [J]; exact TomitaTakesaki.modularConjugation_is_involution
  have h_J_V_J : J * V * J = V := by rw [hV1, mul_one, h_J_inv]
  have h_J_H_J : J * KmsBoundary.modularHamiltonian * J = -KmsBoundary.modularHamiltonian := by
    dsimp [J]
    exact TomitaTakesaki.modularConjugation_reflects_hamiltonian
  refine ⟨?_, hN0, ?_, hN1, hV1, h_comm_P0_V, h_J_V_J, h_J_H_J⟩
  · rw [h_even_AZ, h_comm_S_AZ]
  · rw [h_odd_AX, h_anticomm_S_AX]

/-! ### Krein Attention Energy, Polarized Gibbs Bridge & BKM Fisher Intertwining -/

local instance : Fact (0 < 2) := ⟨by decide⟩

/-- Intertwining Theorem 6 (Krein Attention & Polarized Gibbs Fisher Intertwining):
Connects `AttentionPolarizedGibbsBridge` (`gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights`),
`KreinAttentionEnergy` (`kreinAttentionWeights_sum_one`), and
`LLMAttentionKreinMellinBridge` (`llm_latent_space_unification_exists`) to the
statistical Gibbs manifold `qubitGibbsState`:
1. The 2-level Gibbs distribution of `qubitGibbsState` sums to unity.
2. The BKM quantum Fisher metric evaluated on the Casimir defect carrier $V = 1$
   equals $2 / \mathrm{logMean}(1/4, 3/4)$.
3. Positive-sheet polarized split attention weights equal grand-canonical Gibbs weights.
4. Token-local Krein split-signature attention weights sum to unity.
5. Satisfies the unified LLM latent-space factorization `LLMLatentSpaceUnification 2`. -/
@[rep_depth thermo]
theorem krein_attention_fisher_intertwine :
    let ρ := qubitGibbsState
    let p : Fin 2 → ℝ := fun i => ρ.eigenvalues i
    (∑ i : Fin 2, p i = 1) ∧
    (bkmTangentMetric ρ pauliXTangent = 2 / logMean (p 0) (p 1)) ∧
    (∀ (q : ℝ) (ctx : ContextWindow 2 ℝ ℝ) (β : ℝ) (i : Fin 2),
      gibbsWeight (polarizedPlusParams q ctx) β i =
        polarizedPlusAttentionWeights q ctx β i) ∧
    (∀ (q : ℝ × ℝ) (ctx : ContextWindow 2 (ℝ × ℝ) ℝ) (β : ℝ),
      ∑ i : Fin 2, kreinAttentionWeights (V := ℝ) q ctx β i = 1) ∧
    Nonempty (LLMLatentSpaceUnification 2) := by
  intro ρ p
  have hp0 : p 0 = 1 / 4 := by simp [p, ρ, qubitGibbsState]
  have hp1 : p 1 = 3 / 4 := by simp [p, ρ, qubitGibbsState]
  have hsum : ∑ i : Fin 2, p i = 1 := by
    rw [Fin.sum_univ_two, hp0, hp1]
    norm_num
  have hbkm : bkmTangentMetric ρ pauliXTangent = 2 / logMean (p 0) (p 1) := by
    have h := qubitGibbsState_peirce_fisher_defect
    dsimp [p, ρ]
    exact h.2.1
  have h_gibbs : ∀ (q : ℝ) (ctx : ContextWindow 2 ℝ ℝ) (β : ℝ) (i : Fin 2),
      gibbsWeight (polarizedPlusParams q ctx) β i =
        polarizedPlusAttentionWeights q ctx β i := by
    intro q ctx β i
    exact gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights q ctx β i
  have h_krein : ∀ (q : ℝ × ℝ) (ctx : ContextWindow 2 (ℝ × ℝ) ℝ) (β : ℝ),
      ∑ i : Fin 2, kreinAttentionWeights (V := ℝ) q ctx β i = 1 := by
    intro q ctx β
    exact kreinAttentionWeights_sum_one q ctx β
  have h_fact : Fact (0 < 2) := ⟨by decide⟩
  let scoreMat : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 0]
  have h_llm : Nonempty (LLMLatentSpaceUnification 2) :=
    llm_latent_space_unification_exists scoreMat 1
  exact ⟨hsum, hbkm, h_gibbs, h_krein, h_llm⟩

/-- Typed archetype for Intertwining Theorem 5 (Peirce Casimir spin coagulated poset bridge). -/
def peirceCasimirSpinCoagulatedPosetArchetype : TypedArchetype Unit .proved where
  name     := `peirceCasimirSpinCoagulatedPosetArchetype
  phase    := 2
  claim    := fun _ =>
    let P0 : Matrix (Fin 2) (Fin 2) ℂ := qubitP0
    let AX : Matrix (Fin 2) (Fin 2) ℂ := pauliXTangent
    let AZ : Matrix (Fin 2) (Fin 2) ℂ := pauliZTangent
    let S : Matrix (Fin 2) (Fin 2) ℂ := pauliZTangent
    let J : Mat2C := TomitaTakesaki.modularConjugation
    let V : Matrix (Fin 2) (Fin 2) ℂ := casimirV P0 AX AX
    S * (jungianArchetypeOperator P0 AX AX AZ .animusLogos) * S =
      jungianArchetypeOperator P0 AX AX AZ .animusLogos ∧
    Nplus P0 AZ = 0 ∧
    S * (jungianArchetypeOperator P0 AX AX AX .shadowProjection) * S =
      -(jungianArchetypeOperator P0 AX AX AX .shadowProjection) ∧
    Nplus P0 AX ≠ 0 ∧
    V = 1 ∧
    P0 * V = V * P0 ∧
    J * V * J = V ∧
    J * KmsBoundary.modularHamiltonian * J = -KmsBoundary.modularHamiltonian
  evidence := fun _ => peirce_casimir_spin_coagulated_poset_bridge

#register_archetype peirceCasimirSpinCoagulatedPosetArchetype
#audit_archetype peirceCasimirSpinCoagulatedPosetArchetype

/-- Typed archetype for Intertwining Theorem 6 (Krein attention & Gibbs Fisher intertwining). -/
def kreinAttentionFisherIntertwineArchetype : TypedArchetype Unit .proved where
  name     := `kreinAttentionFisherIntertwineArchetype
  phase    := 2
  claim    := fun _ =>
    let ρ := qubitGibbsState
    let p : Fin 2 → ℝ := fun i => ρ.eigenvalues i
    (∑ i : Fin 2, p i = 1) ∧
    (bkmTangentMetric ρ pauliXTangent = 2 / logMean (p 0) (p 1)) ∧
    (∀ (q : ℝ) (ctx : ContextWindow 2 ℝ ℝ) (β : ℝ) (i : Fin 2),
      gibbsWeight (polarizedPlusParams q ctx) β i =
        polarizedPlusAttentionWeights q ctx β i) ∧
    (∀ (q : ℝ × ℝ) (ctx : ContextWindow 2 (ℝ × ℝ) ℝ) (β : ℝ),
      ∑ i : Fin 2, kreinAttentionWeights (V := ℝ) q ctx β i = 1) ∧
    Nonempty (LLMLatentSpaceUnification 2)
  evidence := fun _ => krein_attention_fisher_intertwine

#register_archetype kreinAttentionFisherIntertwineArchetype
#audit_archetype kreinAttentionFisherIntertwineArchetype

end InfoGeometry.Foundations.PeirceConnesCoreIntertwine
