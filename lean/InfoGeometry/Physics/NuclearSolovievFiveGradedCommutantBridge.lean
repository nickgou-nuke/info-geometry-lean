/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearGradedBathCommutant
import InfoGeometry.Physics.NuclearQuasiparticleCARBridge
import InfoGeometry.Physics.NuclearPhononRPAAlgebra
import InfoGeometry.Physics.NuclearSolovievStateProjection
import InfoGeometry.Physics.SolovievFiniteSecularEigenproblem
import InfoGeometry.Physics.NuclearFeshbachReduction
import InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression

noncomputable section
namespace InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge

open Matrix
open scoped Matrix
open InfoGeometry.Physics.NuclearGradedBathCommutant
open InfoGeometry.Physics.NuclearQuasiparticleCAR
open InfoGeometry.Physics.NuclearPhononRPA
open InfoGeometry.Physics.NuclearSolovievStateProjection
open InfoGeometry.Physics.SolovievQPNMEigenproblem
open InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression

variable {ιq ιph A : Type*} [DecidableEq ιq] [DecidableEq ιph]
  [Ring A] [Algebra ℝ A]

structure SolovievFiveGradedRealization
    (grade : ℤ → Submodule ℝ A)
    (M : ThermalQuasiparticleModel grade)
    (sys : CoupledQuasiparticlePhononSystem ιq ιph A) where
  qpMode : ιq
  phononMode : ιph
  qpModes : Finset ιq
  phononModes : Finset ιph
  qpMode_mem : qpMode ∈ qpModes
  phononMode_mem : phononMode ∈ phononModes
  qpSpectrum : ιq → ℝ
  phononSpectrum : ιph → ℝ
  qpCreation : QuasiparticleCreation grade M
  qpCreation_eq : qpCreation.op = sys.car.adag qpMode
  phononCreation_mem_bath : sys.rpa.Qdag phononMode ∈ M.bath
  H_qp_eq : M.H_qp = sys.car.freeQuasiparticleHamiltonian qpModes qpSpectrum
  H_bath_eq : M.H_bath = sys.rpa.harmonicPhononHamiltonian phononModes phononSpectrum
  rep : A →ₐ[ℝ] FullHamiltonian
  channel : TwoSpinorChannel
  represented_total_symmetric : (rep M.totalHamiltonian)ᵀ = rep M.totalHamiltonian

namespace SolovievFiveGradedRealization
variable {grade : ℤ → Submodule ℝ A} {M : ThermalQuasiparticleModel grade}
  {sys : CoupledQuasiparticlePhononSystem ιq ιph A}
variable (R : SolovievFiveGradedRealization grade M sys)

theorem qpCreation_mem_gradedBathCommutant :
    R.qpCreation.op ∈ gradedBathCommutant grade M.bath 1 :=
  R.qpCreation.mem_gradedBathCommutant

theorem car_adag_mem_bathCommutant :
    sys.car.adag R.qpMode ∈ bathCommutant M.bath := by
  rw [← R.qpCreation_eq]
  exact R.qpCreation.mem_commutant

theorem car_adag_mem_grade_one : sys.car.adag R.qpMode ∈ grade 1 := by
  rw [← R.qpCreation_eq]
  exact R.qpCreation.grade_one

theorem qpCreation_mul_phononCreation :
    R.qpCreation.op * sys.rpa.Qdag R.phononMode =
      sys.rpa.Qdag R.phononMode * R.qpCreation.op := by
  exact ((mem_bathCommutant_iff M.bath R.qpCreation.op).mp
    R.qpCreation.mem_commutant _ R.phononCreation_mem_bath).symm

theorem qpCreation_phononCreation_comm_eq_zero :
    NuclearPhononRPA.comm R.qpCreation.op (sys.rpa.Qdag R.phononMode) = 0 := by
  unfold NuclearPhononRPA.comm
  rw [R.qpCreation_mul_phononCreation, sub_self]

theorem bath_does_not_drive_bare_qp :
    ⁅M.H_bath, R.qpCreation.op⁆ = 0 :=
  bath_bracket_quasiparticle_eq_zero M R.qpCreation

end SolovievFiveGradedRealization

/-- **No-Go Theorem**: `SolovievFiveGradedRealization` is uninhabited because it simultaneously
demands an exact `PhononRPA ιph A` algebra (with `phononMode : ιph`) and an algebra homomorphism
`rep : A →ₐ[ℝ] FullHamiltonian` into the finite `32 × 32` real matrix algebra `MatStage 5`,
contradicting `NuclearPhononRPA.no_finite_matrix_phononRPA`. -/
theorem solovievFiveGradedRealization_isEmpty
    {grade : ℤ → Submodule ℝ A}
    {M : ThermalQuasiparticleModel grade}
    {sys : CoupledQuasiparticlePhononSystem ιq ιph A} :
    IsEmpty (SolovievFiveGradedRealization grade M sys) := by
  refine ⟨fun R => ?_⟩
  have : Nonempty ιph := ⟨R.phononMode⟩
  have hpos : 0 < 2 ^ 5 := by
    rw [← InfoGeometry.Clifford.TowerMatrix.idx_card_pow_two 5]
    exact Fintype.card_pos
  let φ : A →ₐ[ℝ] Matrix (Fin (2 ^ 5)) (Fin (2 ^ 5)) ℝ :=
    (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).toAlgHom.comp R.rep
  let rpaMat : PhononRPA ιph (Matrix (Fin (2 ^ 5)) (Fin (2 ^ 5)) ℝ) :=
    { Q := fun i => φ (sys.rpa.Q i)
      Qdag := fun i => φ (sys.rpa.Qdag i)
      comm_Q_Q := fun i j => by
        have h := sys.rpa.comm_Q_Q i j
        dsimp [NuclearPhononRPA.comm] at h ⊢
        calc
          φ (sys.rpa.Q i) * φ (sys.rpa.Q j) - φ (sys.rpa.Q j) * φ (sys.rpa.Q i)
              = φ (sys.rpa.Q i * sys.rpa.Q j - sys.rpa.Q j * sys.rpa.Q i) := by
                rw [map_sub, map_mul, map_mul]
          _ = φ 0 := by rw [h]
          _ = 0 := map_zero φ
      comm_Qdag_Qdag := fun i j => by
        have h := sys.rpa.comm_Qdag_Qdag i j
        dsimp [NuclearPhononRPA.comm] at h ⊢
        calc
          φ (sys.rpa.Qdag i) * φ (sys.rpa.Qdag j) - φ (sys.rpa.Qdag j) * φ (sys.rpa.Qdag i)
              = φ (sys.rpa.Qdag i * sys.rpa.Qdag j - sys.rpa.Qdag j * sys.rpa.Qdag i) := by
                rw [map_sub, map_mul, map_mul]
          _ = φ 0 := by rw [h]
          _ = 0 := map_zero φ
      comm_Q_Qdag := fun i j => by
        have h := sys.rpa.comm_Q_Qdag i j
        dsimp [NuclearPhononRPA.comm] at h ⊢
        calc
          φ (sys.rpa.Q i) * φ (sys.rpa.Qdag j) - φ (sys.rpa.Qdag j) * φ (sys.rpa.Q i)
              = φ (sys.rpa.Q i * sys.rpa.Qdag j - sys.rpa.Qdag j * sys.rpa.Q i) := by
                rw [map_sub, map_mul, map_mul]
          _ = φ (if i = j then 1 else 0) := by rw [h]
          _ = if i = j then 1 else 0 := by
            split_ifs
            · exact map_one φ
            · exact map_zero φ }
  exact (no_finite_matrix_phononRPA (ι := ιph) (K := ℝ) (2 ^ 5) hpos).false rpaMat

/-! ## Connecting `rep` and `channel` to Two-Channel QPNM Compression, `SO(2)` Rotation, & Feshbach Reduction -/

/-- `SO(2)` rotation of an orthonormal `TwoSpinorChannel`. -/
def rotatedChannel (C : TwoSpinorChannel) (θ : ℝ) : TwoSpinorChannel where
  bare := Real.cos θ • C.bare - Real.sin θ • C.dressed
  dressed := Real.sin θ • C.bare + Real.cos θ • C.dressed
  bare_norm := by
    have h1 := C.bare_norm
    have h2 := C.dressed_norm
    have h12 := C.bare_dressed_orthogonal
    have h21 : C.dressed ⬝ᵥ C.bare = 0 := by rw [dotProduct_comm]; exact h12
    have hpyth := Real.cos_sq_add_sin_sq θ
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, h1, h2, h12, h21]
    nlinarith [hpyth]
  dressed_norm := by
    have h1 := C.bare_norm
    have h2 := C.dressed_norm
    have h12 := C.bare_dressed_orthogonal
    have h21 : C.dressed ⬝ᵥ C.bare = 0 := by rw [dotProduct_comm]; exact h12
    have hpyth := Real.cos_sq_add_sin_sq θ
    simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, h1, h2, h12, h21]
    nlinarith [hpyth]
  bare_dressed_orthogonal := by
    have h1 := C.bare_norm
    have h2 := C.dressed_norm
    have h12 := C.bare_dressed_orthogonal
    have h21 : C.dressed ⬝ᵥ C.bare = 0 := by rw [dotProduct_comm]; exact h12
    simp only [dotProduct_add, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, h1, h2, h12, h21]
    ring

theorem channel_coupling_eq_reverseCoupling_of_symmetric (C : TwoSpinorChannel)
    {H : FullHamiltonian} (hH : Hᵀ = H) :
    C.coupling H = C.reverseCoupling H := by
  dsimp [TwoSpinorChannel.coupling, TwoSpinorChannel.reverseCoupling,
    TwoSpinorChannel.matrixElement]
  calc
    C.bare ⬝ᵥ (H *ᵥ C.dressed) = (H *ᵥ C.dressed) ⬝ᵥ C.bare := dotProduct_comm _ _
    _ = (Hᵀ *ᵥ C.dressed) ⬝ᵥ C.bare := by rw [hH]
    _ = (C.dressed ᵥ* H) ⬝ᵥ C.bare := by rw [Matrix.mulVec_transpose]
    _ = C.dressed ⬝ᵥ (H *ᵥ C.bare) := (Matrix.dotProduct_mulVec C.dressed H C.bare).symm

theorem channel_projectedHamiltonian_eq_qpnm_of_symmetric (C : TwoSpinorChannel)
    {H : FullHamiltonian} (hH : Hᵀ = H) :
    C.projectedHamiltonian H =
      qpnmMatrix (C.qpEnergy H) (C.dressedEnergy H - C.qpEnergy H) (C.coupling H) := by
  have hrev := channel_coupling_eq_reverseCoupling_of_symmetric C hH
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qpnmMatrix, hrev]

theorem channel_projectedHamiltonian_eq_block_of_symmetric (C : TwoSpinorChannel)
    {H : FullHamiltonian} (hH : Hᵀ = H) :
    C.projectedHamiltonian H =
      SolovievFiniteSecularEigenproblem.blockHamiltonian
        (C.qpEnergy H) (C.dressedEnergy H) (C.coupling H) := by
  have hrev := channel_coupling_eq_reverseCoupling_of_symmetric C hH
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SolovievFiniteSecularEigenproblem.blockHamiltonian, hrev]

theorem rotatedChannel_projectedHamiltonian (C : TwoSpinorChannel) (H : FullHamiltonian)
    (θ : ℝ) :
    (rotatedChannel C θ).projectedHamiltonian H =
      rotU θ * C.projectedHamiltonian H * (rotU θ)ᵀ := by
  have h00 : (rotatedChannel C θ).qpEnergy H =
      (Real.cos θ) ^ 2 * C.qpEnergy H -
        Real.cos θ * Real.sin θ * (C.coupling H + C.reverseCoupling H) +
        (Real.sin θ) ^ 2 * C.dressedEnergy H := by
    dsimp [TwoSpinorChannel.qpEnergy, TwoSpinorChannel.coupling,
      TwoSpinorChannel.reverseCoupling, TwoSpinorChannel.dressedEnergy,
      TwoSpinorChannel.matrixElement, rotatedChannel]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have h01 : (rotatedChannel C θ).coupling H =
      Real.cos θ * Real.sin θ * C.qpEnergy H +
        (Real.cos θ) ^ 2 * C.coupling H -
        (Real.sin θ) ^ 2 * C.reverseCoupling H -
        Real.sin θ * Real.cos θ * C.dressedEnergy H := by
    dsimp [TwoSpinorChannel.qpEnergy, TwoSpinorChannel.coupling,
      TwoSpinorChannel.reverseCoupling, TwoSpinorChannel.dressedEnergy,
      TwoSpinorChannel.matrixElement, rotatedChannel]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul,
      dotProduct_add, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have h10 : (rotatedChannel C θ).reverseCoupling H =
      Real.sin θ * Real.cos θ * C.qpEnergy H -
        (Real.sin θ) ^ 2 * C.coupling H +
        (Real.cos θ) ^ 2 * C.reverseCoupling H -
        Real.cos θ * Real.sin θ * C.dressedEnergy H := by
    dsimp [TwoSpinorChannel.qpEnergy, TwoSpinorChannel.coupling,
      TwoSpinorChannel.reverseCoupling, TwoSpinorChannel.dressedEnergy,
      TwoSpinorChannel.matrixElement, rotatedChannel]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul,
      dotProduct_sub, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have h11 : (rotatedChannel C θ).dressedEnergy H =
      (Real.sin θ) ^ 2 * C.qpEnergy H +
        Real.sin θ * Real.cos θ * (C.coupling H + C.reverseCoupling H) +
        (Real.cos θ) ^ 2 * C.dressedEnergy H := by
    dsimp [TwoSpinorChannel.qpEnergy, TwoSpinorChannel.coupling,
      TwoSpinorChannel.reverseCoupling, TwoSpinorChannel.dressedEnergy,
      TwoSpinorChannel.matrixElement, rotatedChannel]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  ext i j
  fin_cases i <;> fin_cases j
  · simp [h00, rotU, TwoSpinorChannel.projectedHamiltonian, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  · simp [h01, rotU, TwoSpinorChannel.projectedHamiltonian, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  · simp [h10, rotU, TwoSpinorChannel.projectedHamiltonian, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  · simp [h11, rotU, TwoSpinorChannel.projectedHamiltonian, Matrix.mul_apply,
      Fin.sum_univ_two]; ring

/-- Two-spinor projected `2 × 2` Hamiltonian for any `32 × 32` operator `H_rep : FullHamiltonian`. -/
def projectedTotal (channel : TwoSpinorChannel) (H_rep : FullHamiltonian) :
    SolovievHamiltonian :=
  channel.projectedHamiltonian H_rep

theorem projectedTotal_decomposition
    (H_qp H_bath H_int : FullHamiltonian) (g : ℝ)
    (channel : TwoSpinorChannel) :
    projectedTotal channel (H_qp + H_bath + g • H_int) =
      projectedTotal channel H_qp +
        projectedTotal channel H_bath +
        g • projectedTotal channel H_int := by
  dsimp [projectedTotal]
  rw [channel.projectedHamiltonian_add, channel.projectedHamiltonian_add,
    channel.projectedHamiltonian_smul]

theorem projectedTotal_eq_qpnm
    (H_rep : FullHamiltonian) (hSym : H_repᵀ = H_rep)
    (channel : TwoSpinorChannel) :
    projectedTotal channel H_rep =
      qpnmMatrix
        (channel.qpEnergy H_rep)
        (channel.dressedEnergy H_rep - channel.qpEnergy H_rep)
        (channel.coupling H_rep) :=
  channel_projectedHamiltonian_eq_qpnm_of_symmetric channel hSym

theorem projectedTotal_rotated_eq_dressedQPNM
    (H_rep : FullHamiltonian) (hSym : H_repᵀ = H_rep)
    (channel : TwoSpinorChannel) (θ : ℝ) :
    projectedTotal (rotatedChannel channel θ) H_rep =
      dressedQPNM
        (channel.qpEnergy H_rep)
        (channel.dressedEnergy H_rep - channel.qpEnergy H_rep)
        (channel.coupling H_rep) θ := by
  dsimp [projectedTotal]
  rw [rotatedChannel_projectedHamiltonian,
    channel_projectedHamiltonian_eq_qpnm_of_symmetric channel hSym]
  rfl

theorem projectedTotal_dressed_weights
    (H_rep : FullHamiltonian) (hSym : H_repᵀ = H_rep)
    (channel : TwoSpinorChannel) (θ : ℝ) :
    let Eqp := channel.qpEnergy H_rep
    let omega := channel.dressedEnergy H_rep - Eqp
    let V := channel.coupling H_rep
    (rotatedChannel channel θ).qpEnergy H_rep = dressedE1 Eqp omega V θ ∧
      (rotatedChannel channel θ).dressedEnergy H_rep = dressedE2 Eqp omega V θ ∧
      (rotatedChannel channel θ).coupling H_rep = dressedV omega V θ ∧
      (projectedTotal (rotatedChannel channel θ) H_rep).trace =
        Eqp + channel.dressedEnergy H_rep ∧
      (projectedTotal (rotatedChannel channel θ) H_rep).det =
        Eqp * channel.dressedEnergy H_rep - V ^ 2 := by
  dsimp
  have hmat := projectedTotal_rotated_eq_dressedQPNM H_rep hSym channel θ
  rw [dressedQPNM_eq] at hmat
  have h00 : (rotatedChannel channel θ).qpEnergy H_rep =
      dressedE1 (channel.qpEnergy H_rep)
        (channel.dressedEnergy H_rep - channel.qpEnergy H_rep)
        (channel.coupling H_rep) θ := by
    have := congrFun (congrFun hmat 0) 0
    simpa [projectedTotal] using this
  have h11 : (rotatedChannel channel θ).dressedEnergy H_rep =
      dressedE2 (channel.qpEnergy H_rep)
        (channel.dressedEnergy H_rep - channel.qpEnergy H_rep)
        (channel.coupling H_rep) θ := by
    have := congrFun (congrFun hmat 1) 1
    simpa [projectedTotal] using this
  have h01 : (rotatedChannel channel θ).coupling H_rep =
      dressedV
        (channel.dressedEnergy H_rep - channel.qpEnergy H_rep)
        (channel.coupling H_rep) θ := by
    have := congrFun (congrFun hmat 0) 1
    simpa [projectedTotal] using this
  have htr : (projectedTotal (rotatedChannel channel θ) H_rep).trace =
      channel.qpEnergy H_rep + channel.dressedEnergy H_rep := by
    rw [projectedTotal_rotated_eq_dressedQPNM H_rep hSym channel θ, dressedQPNM_trace]
    ring
  have hdet : (projectedTotal (rotatedChannel channel θ) H_rep).det =
      channel.qpEnergy H_rep * channel.dressedEnergy H_rep -
        (channel.coupling H_rep) ^ 2 := by
    rw [projectedTotal_rotated_eq_dressedQPNM H_rep hSym channel θ, dressedQPNM_det]
    ring
  exact ⟨h00, h11, h01, htr, hdet⟩

/-- Exact Feshbach elimination on the represented two-spinor projected Hamiltonian. -/
theorem projectedTotal_feshbach_reduction
    (H_rep : FullHamiltonian) (hSym : H_repᵀ = H_rep)
    (channel : TwoSpinorChannel) (E : ℝ)
    (hE : channel.dressedEnergy H_rep - E ≠ 0)
    (ψ : Fin 2 → ℝ) :
    (projectedTotal channel H_rep).mulVec ψ = E • ψ ↔
      (channel.qpEnergy H_rep -
          (channel.coupling H_rep) ^ 2 / (channel.dressedEnergy H_rep - E)) * ψ 0 =
          E * ψ 0 ∧
        ψ 1 = -(channel.coupling H_rep * ψ 0) / (channel.dressedEnergy H_rep - E) := by
  dsimp [projectedTotal]
  rw [channel_projectedHamiltonian_eq_block_of_symmetric channel hSym]
  exact NuclearFeshbachReduction.two_channel_feshbach
    (channel.qpEnergy H_rep)
    (channel.dressedEnergy H_rep)
    (channel.coupling H_rep) E hE ψ

/-- At the Schur decoupling angle, the rotated channel decouples cleanly and Feshbach elimination
has zero coupling shift. -/
theorem projectedTotal_decoupled_at_schur_angle
    (H_rep : FullHamiltonian) (hSym : H_repᵀ = H_rep)
    (channel : TwoSpinorChannel) (θ E : ℝ)
    (hdec : channel.coupling H_rep * Real.cos (2 * θ) =
      ((channel.dressedEnergy H_rep - channel.qpEnergy H_rep) / 2) * Real.sin (2 * θ))
    (hE : (rotatedChannel channel θ).dressedEnergy H_rep - E ≠ 0)
    (ψ : Fin 2 → ℝ) :
    (rotatedChannel channel θ).coupling H_rep = 0 ∧
      ((projectedTotal (rotatedChannel channel θ) H_rep).mulVec ψ = E • ψ ↔
        (rotatedChannel channel θ).qpEnergy H_rep * ψ 0 = E * ψ 0 ∧
          ψ 1 = 0) := by
  have hweights := projectedTotal_dressed_weights H_rep hSym channel θ
  have hc0 : (rotatedChannel channel θ).coupling H_rep = 0 := by
    rw [hweights.2.2.1, dressedV_eq_zero_iff]
    exact hdec
  refine ⟨hc0, ?_⟩
  have hsym : projectedTotal (rotatedChannel channel θ) H_rep =
      SolovievFiniteSecularEigenproblem.blockHamiltonian
        ((rotatedChannel channel θ).qpEnergy H_rep)
        ((rotatedChannel channel θ).dressedEnergy H_rep)
        ((rotatedChannel channel θ).coupling H_rep) :=
    channel_projectedHamiltonian_eq_block_of_symmetric (rotatedChannel channel θ) hSym
  rw [hsym, hc0]
  have hfesh := NuclearFeshbachReduction.two_channel_feshbach
    ((rotatedChannel channel θ).qpEnergy H_rep)
    ((rotatedChannel channel θ).dressedEnergy H_rep)
    0 E hE ψ
  change SolovievFiniteSecularEigenproblem.isEigenpair
    (SolovievFiniteSecularEigenproblem.blockHamiltonian
      ((rotatedChannel channel θ).qpEnergy H_rep)
      ((rotatedChannel channel θ).dressedEnergy H_rep) 0) ψ E ↔ _
  rw [hfesh]
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero, zero_mul, neg_zero]

/-! ## Concrete `MatStage 5` Non-Vacuity Witness -/

/-- First binary tensor-stage basis index in `Idx 5` for the concrete `MatStage 5` witness. -/
def witnessIdx0 : InfoGeometry.Clifford.TowerMatrix.Idx 5 :=
  (((((default, (0 : Fin 2)), (0 : Fin 2)), (0 : Fin 2)), (0 : Fin 2)), (0 : Fin 2))

/-- Second distinct binary tensor-stage basis index in `Idx 5` for the concrete `MatStage 5` witness. -/
def witnessIdx1 : InfoGeometry.Clifford.TowerMatrix.Idx 5 :=
  (((((default, (0 : Fin 2)), (0 : Fin 2)), (0 : Fin 2)), (0 : Fin 2)), (1 : Fin 2))

theorem witnessIdx0_ne_witnessIdx1 : witnessIdx0 ≠ witnessIdx1 := by
  intro h
  have h1 := congrArg Prod.snd h
  dsimp [witnessIdx0, witnessIdx1] at h1
  exact absurd h1 (by decide)

/-- Concrete orthonormal `TwoSpinorChannel` in `Spinor32` (`Idx 5 → ℝ`). -/
def witnessChannel : TwoSpinorChannel where
  bare := Pi.single witnessIdx0 (1 : ℝ)
  dressed := Pi.single witnessIdx1 (1 : ℝ)
  bare_norm := by
    simp [dotProduct, Pi.single_apply]
  dressed_norm := by
    simp [dotProduct, Pi.single_apply]
  bare_dressed_orthogonal := by
    simp [dotProduct, Pi.single_apply, witnessIdx0_ne_witnessIdx1.symm]

/-- Concrete symmetric quasiparticle term in `MatStage 5`. -/
def witnessH_qp : FullHamiltonian :=
  Matrix.of fun a b => if a = witnessIdx0 ∧ b = witnessIdx0 then 1 else 0

/-- Concrete symmetric bath term in `MatStage 5`. -/
def witnessH_bath : FullHamiltonian :=
  Matrix.of fun a b => if a = witnessIdx1 ∧ b = witnessIdx1 then 3 else 0

/-- Concrete symmetric interaction term in `MatStage 5`. -/
def witnessH_int : FullHamiltonian :=
  Matrix.of fun a b =>
    if (a = witnessIdx0 ∧ b = witnessIdx1) ∨ (a = witnessIdx1 ∧ b = witnessIdx0) then 1 else 0

/-- Concrete symmetric `32 × 32` total Hamiltonian `H_rep = H_qp + H_bath + 1 • H_int` in `MatStage 5`. -/
def witnessH_rep : FullHamiltonian :=
  witnessH_qp + witnessH_bath + (1 : ℝ) • witnessH_int

theorem witnessH_rep_symmetric : witnessH_repᵀ = witnessH_rep := by
  ext a b
  simp only [witnessH_rep, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [witnessH_qp, witnessH_bath, witnessH_int, Matrix.transpose_apply, Matrix.of_apply]
  congr 1
  · congr 1
    · simp [and_comm]
    · simp [and_comm]
  · congr 1
    simp [and_comm, or_comm]

/-- **Non-Vacuity `MatStage 5` Witness Theorem**: constructs an explicit symmetric
`H_rep : FullHamiltonian`, explicit orthonormal `channel : TwoSpinorChannel`, and Schur angle
`θ = π / 8`, `E = 0` satisfying every hypothesis of `projectedTotal_decomposition`,
`projectedTotal_eq_qpnm`, `projectedTotal_rotated_eq_dressedQPNM`,
`projectedTotal_dressed_weights`, `projectedTotal_feshbach_reduction`, and
`projectedTotal_decoupled_at_schur_angle`. -/
theorem projectedTotal_nonvacuous_matStage5_witness :
    ∃ (H_rep : FullHamiltonian) (channel : TwoSpinorChannel) (θ E : ℝ),
      H_repᵀ = H_rep ∧
      projectedTotal channel H_rep = !![1, 1; 1, 3] ∧
      channel.dressedEnergy H_rep - E ≠ 0 ∧
      channel.coupling H_rep * Real.cos (2 * θ) =
        ((channel.dressedEnergy H_rep - channel.qpEnergy H_rep) / 2) * Real.sin (2 * θ) ∧
      (rotatedChannel channel θ).dressedEnergy H_rep - E ≠ 0 ∧
      (rotatedChannel channel θ).coupling H_rep = 0 ∧
      ∀ ψ : Fin 2 → ℝ,
        ((projectedTotal (rotatedChannel channel θ) H_rep).mulVec ψ = E • ψ ↔
          (rotatedChannel channel θ).qpEnergy H_rep * ψ 0 = E * ψ 0 ∧ ψ 1 = 0) := by
  have hme : ∀ (i j : InfoGeometry.Clifford.TowerMatrix.Idx 5) (M : FullHamiltonian),
      witnessChannel.matrixElement (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) M = M i j := by
    intro i j M
    simp [TwoSpinorChannel.matrixElement, dotProduct, Matrix.mulVec, Pi.single_apply]
  have hqp : witnessChannel.qpEnergy witnessH_rep = 1 := by
    change witnessChannel.matrixElement (Pi.single witnessIdx0 1) (Pi.single witnessIdx0 1)
      witnessH_rep = 1
    rw [hme]
    simp [witnessH_rep, witnessH_qp, witnessH_bath, witnessH_int, witnessIdx0_ne_witnessIdx1]
  have hdressed : witnessChannel.dressedEnergy witnessH_rep = 3 := by
    change witnessChannel.matrixElement (Pi.single witnessIdx1 1) (Pi.single witnessIdx1 1)
      witnessH_rep = 3
    rw [hme]
    simp [witnessH_rep, witnessH_qp, witnessH_bath, witnessH_int,
      witnessIdx0_ne_witnessIdx1.symm]
  have hcoup : witnessChannel.coupling witnessH_rep = 1 := by
    change witnessChannel.matrixElement (Pi.single witnessIdx0 1) (Pi.single witnessIdx1 1)
      witnessH_rep = 1
    rw [hme]
    simp [witnessH_rep, witnessH_qp, witnessH_bath, witnessH_int,
      witnessIdx0_ne_witnessIdx1, witnessIdx0_ne_witnessIdx1.symm]
  have hproj : projectedTotal witnessChannel witnessH_rep = !![1, 1; 1, 3] := by
    rw [projectedTotal_eq_qpnm witnessH_rep witnessH_rep_symmetric witnessChannel,
      hqp, hdressed, hcoup]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [qpnmMatrix]
  have hE0 : witnessChannel.dressedEnergy witnessH_rep - 0 ≠ 0 := by
    rw [hdressed]
    norm_num
  have hdec : witnessChannel.coupling witnessH_rep * Real.cos (2 * (Real.pi / 8)) =
      ((witnessChannel.dressedEnergy witnessH_rep -
        witnessChannel.qpEnergy witnessH_rep) / 2) * Real.sin (2 * (Real.pi / 8)) := by
    rw [hqp, hdressed, hcoup]
    have h2 : (2 : ℝ) * (Real.pi / 8) = Real.pi / 4 := by ring
    rw [h2, Real.cos_pi_div_four, Real.sin_pi_div_four]
    ring
  have hweights :=
    projectedTotal_dressed_weights witnessH_rep witnessH_rep_symmetric witnessChannel (Real.pi / 8)
  have hErot : (rotatedChannel witnessChannel (Real.pi / 8)).dressedEnergy witnessH_rep - 0 ≠ 0 := by
    have h2 : (2 : ℝ) * (Real.pi / 8) = Real.pi / 4 := by ring
    have hd := hweights.2.1
    dsimp [dressedE2, dressedBdGXi] at hd
    rw [hqp, hdressed, hcoup, h2, Real.cos_pi_div_four, Real.sin_pi_div_four] at hd
    have hval : (rotatedChannel witnessChannel (Real.pi / 8)).dressedEnergy witnessH_rep =
        2 + Real.sqrt 2 := by
      linarith
    rw [hval, sub_zero]
    have hsq : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith
  refine ⟨witnessH_rep, witnessChannel, Real.pi / 8, 0,
    witnessH_rep_symmetric, hproj, hE0, hdec, hErot, ?_⟩
  have hschur := fun ψ =>
    projectedTotal_decoupled_at_schur_angle witnessH_rep witnessH_rep_symmetric witnessChannel
      (Real.pi / 8) 0 hdec hErot ψ
  exact ⟨(hschur 0).1, fun ψ => (hschur ψ).2⟩

end InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge
