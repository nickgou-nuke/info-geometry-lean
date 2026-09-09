import InfoGeometry.Optics.FiniteJonesModel
import InfoGeometry.Clifford.DiracPauliGamma
import InfoGeometry.Physics.PoincarePauliLubanskiAlgebraBridge
import InfoGeometry.Physics.PauliLubanskiFiniteBridge

/-!
# Jones projectors to finite Clifford/Lorentz/Pauli--Lubanski data

This is a theorem-honest finite bridge.  The Jones projectors and Dirac
matrices remain in their native carriers; the bridge records the projector
laws, the native Clifford anticommutator and Lorentz-generator convention,
and the independent finite Pauli--Lubanski/Casimir identities.  It does not
assert an unproved matrix embedding of `2 × 2` Jones matrices into the Dirac
carrier.
-/

noncomputable section

namespace InfoGeometry.Physics.JonesCliffordLorentzPauliLubanskiBridge

open InfoGeometry.Optics.FiniteJonesModel
open InfoGeometry.Clifford.DiracPauliGamma
open InfoGeometry.Physics.PoincarePauliLubanskiAlgebraBridge
open InfoGeometry.Physics.PauliLubanskiFiniteBridge
open InfoGeometry.Physics.LorentzBoostMinkowski
open InfoGeometry.Physics.ZornMatrixSU3

theorem jones_projector_packet :
    sProjector * sProjector = sProjector ∧
      pProjector * pProjector = pProjector ∧
      sProjector * pProjector = 0 ∧
      pProjector * sProjector = 0 ∧
      sProjector + pProjector = 1 := by
  exact ⟨sProjector_idem, pProjector_idem, sProjector_mul_pProjector,
    pProjector_mul_sProjector, sProjector_add_pProjector⟩

/-! ## The explicit finite carrier lift

The lift below is intentionally only the block-diagonal embedding of the two
native Jones channel projectors.  It supplies the missing finite carrier map
without identifying arbitrary optical matrices with Dirac operators.
-/

def jonesSDirac : DiracMatrix :=
  !![(1 : ℂ), 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 0]

def jonesPDirac : DiracMatrix :=
  !![(0 : ℂ), 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 1]

def diagJonesDirac (a b : ℂ) : DiracMatrix :=
  !![a, 0, 0, 0;
     0, b, 0, 0;
     0, 0, a, 0;
     0, 0, 0, b]

theorem diagJonesDirac_top_block (a b : ℂ) :
    (fun i j : Fin 2 =>
      diagJonesDirac a b (Fin.castAdd 2 i) (Fin.castAdd 2 j)) =
      diagJones a b := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagJonesDirac, diagJones]

theorem diagJonesDirac_mul (a b c d : ℂ) :
    diagJonesDirac a b * diagJonesDirac c d =
      diagJonesDirac (a * c) (b * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagJonesDirac, Matrix.mul_apply, Fin.sum_univ_succ]

theorem diagJonesDirac_one :
    diagJonesDirac 1 1 = (1 : DiracMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagJonesDirac]

theorem jones_projectors_are_diagonal_lifts :
    jonesSDirac = diagJonesDirac 1 0 ∧
      jonesPDirac = diagJonesDirac 0 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [jonesSDirac, jonesPDirac, diagJonesDirac]

theorem jonesSDirac_idem : jonesSDirac * jonesSDirac = jonesSDirac := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jonesSDirac, Matrix.mul_apply, Fin.sum_univ_succ]

theorem jonesPDirac_idem : jonesPDirac * jonesPDirac = jonesPDirac := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jonesPDirac, Matrix.mul_apply, Fin.sum_univ_succ]

theorem jonesDirac_projectors_orthogonal :
    jonesSDirac * jonesPDirac = 0 ∧ jonesPDirac * jonesSDirac = 0 := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [jonesSDirac, jonesPDirac, Matrix.mul_apply, Fin.sum_univ_succ]

/-! ## The two-strand Casimir polynomial in the Jones channel projector -/

def twoStrandCasimir (M : ℂ) : DiracMatrix :=
  (-2 * M ^ 2) • ((1 : DiracMatrix) - jonesSDirac)

theorem twoStrandCasimir_on_singlet (M : ℂ) :
    twoStrandCasimir M * jonesSDirac = 0 := by
  rw [twoStrandCasimir, Algebra.smul_mul_assoc, sub_mul, one_mul,
    jonesSDirac_idem, sub_self]
  simp

theorem twoStrandCasimir_on_triplet (M : ℂ) :
    twoStrandCasimir M * jonesPDirac =
      (-2 * M ^ 2) • jonesPDirac := by
  rw [twoStrandCasimir, Algebra.smul_mul_assoc, sub_mul, one_mul,
    jonesDirac_projectors_orthogonal.1, sub_zero]

theorem jonesDirac_projectors_complete :
    jonesSDirac + jonesPDirac = (1 : DiracMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jonesSDirac, jonesPDirac]

theorem jonesSDirac_top_block :
    (fun i j : Fin 2 => jonesSDirac (Fin.castAdd 2 i) (Fin.castAdd 2 j)) = sProjector := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [jonesSDirac, sProjector, diagJones]

theorem jonesPDirac_top_block :
    (fun i j : Fin 2 => jonesPDirac (Fin.castAdd 2 i) (Fin.castAdd 2 j)) = pProjector := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [jonesPDirac, pProjector, diagJones]

theorem native_clifford_pauli_packet (μ ν : Fin 4) :
    gamma μ * gamma ν + gamma ν * gamma μ =
      (2 * eta μ ν) • (1 : DiracMatrix) := by
  exact gamma_anticomm μ ν

/-! ## Spatial Pauli generators as Clifford bivectors -/

def pauliGenerator (a : Fin 3) : DiracMatrix :=
  match a with
  | 0 => Complex.I • (gamma 2 * gamma 3)
  | 1 => Complex.I • (gamma 3 * gamma 1)
  | _ => Complex.I • (gamma 1 * gamma 2)

theorem pauliGenerator_sq (a : Fin 3) :
    pauliGenerator a * pauliGenerator a = (1 : DiracMatrix) := by
  fin_cases a <;>
    dsimp [pauliGenerator, gamma]
  all_goals
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [gamma0, gamma1, gamma2, gamma3, Matrix.mul_apply,
        Fin.sum_univ_succ] <;> ring

theorem lorentz_generator_convention (μ ν : Fin 4) :
    gamma μ * gamma ν - gamma ν * gamma μ =
      (-4 * Complex.I) • lorentzGenerator μ ν := by
  exact commutator_eq_neg_four_i_lorentzGenerator μ ν

theorem pauli_lubanski_finite_packet (D : LorentzBivectorDatum) :
    minkowskiPair D.momentum (pauliLubanski D) = 0 ∧
      minkowskiSq (pauliLubanski D) =
        minkowskiPair (pauliLubanski D) (pauliLubanski D) := by
  exact ⟨pauliLubanski_orthogonal D, pauliLubanski_square_is_second_casimir D⟩

theorem rest_frame_casimir_packet (m s : ℝ) (J K : SpatialVector)
    (hJ : ZornMatrixSU3.dotProduct J J = s * (s + 1)) :
    minkowskiPair
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩)
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩) =
      -m ^ 2 * s * (s + 1) := by
  exact pauliLubanski_rest_frame_massive_casimir m s J K hJ

end InfoGeometry.Physics.JonesCliffordLorentzPauliLubanskiBridge
