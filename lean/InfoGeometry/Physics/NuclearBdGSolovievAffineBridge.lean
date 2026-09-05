import Mathlib
import InfoGeometry.Physics.NuclearBdGTwoLevelExact
import InfoGeometry.Physics.NuclearSolovievCompression
import InfoGeometry.Physics.SolovievQuasiparticlePhononEigenproblem

/-!
# Exact affine and compression bridge from BdG to Soloviev blocks

A real Soloviev QPNM matrix is not identified with a BdG Hamiltonian.  Its
canonical finite relation to one is the affine decomposition

`H_QPNM = (E_qp + ω/2) I + H_BdG(-ω/2,V)`.

The scalar term changes all energies equally; the traceless BdG block controls
the splitting.  Combining this identity with the explicit common-carrier
compression gives a theorem-level BdG-energy-plus-phonon realization of the
finite Soloviev matrix.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearBdGSolovievAffineBridge

open Matrix
open InfoGeometry.Physics.NuclearBdGTwoLevelExact
open InfoGeometry.Physics.NuclearSolovievCompression
open InfoGeometry.Physics.SolovievQPNMEigenproblem

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Scalar center of the two Soloviev channels. -/
def solovievCenter (Eqp omega : ℝ) : ℝ :=
  Eqp + omega / 2

/-- Traceless longitudinal BdG coordinate associated with the channel offset. -/
def solovievBdGCoordinate (omega : ℝ) : ℝ :=
  -omega / 2

/-- Exact affine decomposition of the QPNM block. -/
theorem qpnm_eq_center_add_bdg (Eqp omega V : ℝ) :
    qpnmMatrix Eqp omega V =
      solovievCenter Eqp omega • (1 : M2R) +
        bdgBlock (solovievBdGCoordinate omega) V := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qpnmMatrix, solovievCenter, solovievBdGCoordinate,
      bdgBlock] <;>
    ring

/-- The centered QPNM block is exactly the traceless BdG block. -/
theorem qpnm_centered_eq_bdg (Eqp omega V : ℝ) :
    qpnmMatrix Eqp omega V -
        solovievCenter Eqp omega • (1 : M2R) =
      bdgBlock (solovievBdGCoordinate omega) V := by
  rw [qpnm_eq_center_add_bdg]
  abel

/-- Centered square law. -/
theorem qpnm_centered_sq (Eqp omega V : ℝ) :
    (qpnmMatrix Eqp omega V -
        solovievCenter Eqp omega • (1 : M2R)) *
      (qpnmMatrix Eqp omega V -
        solovievCenter Eqp omega • (1 : M2R)) =
      ((solovievBdGCoordinate omega) ^ 2 + V ^ 2) • (1 : M2R) := by
  rw [qpnm_centered_eq_bdg, bdgBlock_sq]

/-- Positive half-gap. -/
def solovievHalfGap (omega V : ℝ) : ℝ :=
  bdgEnergy (solovievBdGCoordinate omega) V

/-- The upper affine BdG spectral value is a root of the QPNM determinant. -/
theorem qpnm_upper_bdg_root (Eqp omega V : ℝ) :
    det (secularMatrix Eqp omega V
      (solovievCenter Eqp omega + solovievHalfGap omega V)) = 0 := by
  rw [secular_determinant_eq]
  have hE := bdgEnergy_sq (solovievBdGCoordinate omega) V
  simp only [solovievCenter, solovievHalfGap,
    solovievBdGCoordinate] at hE ⊢
  nlinarith

/-- The lower affine BdG spectral value is a root of the QPNM determinant. -/
theorem qpnm_lower_bdg_root (Eqp omega V : ℝ) :
    det (secularMatrix Eqp omega V
      (solovievCenter Eqp omega - solovievHalfGap omega V)) = 0 := by
  rw [secular_determinant_eq]
  have hE := bdgEnergy_sq (solovievBdGCoordinate omega) V
  simp only [solovievCenter, solovievHalfGap,
    solovievBdGCoordinate] at hE ⊢
  nlinarith

/-- The two affine spectral roots are separated by twice the BdG energy. -/
theorem qpnm_bdg_root_gap (Eqp omega V : ℝ) :
    (solovievCenter Eqp omega + solovievHalfGap omega V) -
      (solovievCenter Eqp omega - solovievHalfGap omega V) =
        2 * solovievHalfGap omega V := by
  ring

/-- Use a BdG quasiparticle energy as the one-quasiparticle entry of the full
CAR--phonon Hamiltonian. -/
def bdgSolovievHamiltonian
    (ξ Δ omega V : ℝ) :
    InfoGeometry.Physics.NuclearCARPhononCommonCarrier.Operator :=
  fullQPNMHamiltonian (bdgEnergy ξ Δ) omega V

/-- Corresponding finite Soloviev block. -/
def bdgSolovievBlock (ξ Δ omega V : ℝ) : M2R :=
  qpnmMatrix (bdgEnergy ξ Δ) omega V

/-- Exact common-carrier compression of the BdG-energy Soloviev extension. -/
theorem bdgSoloviev_compression
    (ξ Δ omega V C D : ℝ) :
    modelReadout
        (bdgSolovievHamiltonian ξ Δ omega V (modelEmbed ![C, D])) =
      mulVec (bdgSolovievBlock ξ Δ omega V) ![C, D] := by
  simpa [bdgSolovievHamiltonian, bdgSolovievBlock,
    compressedAction] using
    compressedAction_eq_qpnm_mulVec
      (bdgEnergy ξ Δ) omega V C D

/-- The compressed block itself has the exact affine BdG decomposition. -/
theorem bdgSolovievBlock_affine (ξ Δ omega V : ℝ) :
    bdgSolovievBlock ξ Δ omega V =
      solovievCenter (bdgEnergy ξ Δ) omega • (1 : M2R) +
        bdgBlock (solovievBdGCoordinate omega) V := by
  exact qpnm_eq_center_add_bdg (bdgEnergy ξ Δ) omega V

/-- Compact exact bridge packet. -/
theorem bdg_soloviev_affine_compression_packet
    (ξ Δ omega V C D : ℝ) :
    qpnmMatrix (bdgEnergy ξ Δ) omega V =
        solovievCenter (bdgEnergy ξ Δ) omega • (1 : M2R) +
          bdgBlock (solovievBdGCoordinate omega) V ∧
      det (secularMatrix (bdgEnergy ξ Δ) omega V
        (solovievCenter (bdgEnergy ξ Δ) omega +
          solovievHalfGap omega V)) = 0 ∧
      modelReadout
          (bdgSolovievHamiltonian ξ Δ omega V (modelEmbed ![C, D])) =
        mulVec (bdgSolovievBlock ξ Δ omega V) ![C, D] := by
  exact ⟨qpnm_eq_center_add_bdg _ _ _,
    qpnm_upper_bdg_root _ _ _,
    bdgSoloviev_compression ξ Δ omega V C D⟩

end InfoGeometry.Physics.NuclearBdGSolovievAffineBridge
