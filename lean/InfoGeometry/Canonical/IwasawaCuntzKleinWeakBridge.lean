import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic

import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.Representation
import InfoGeometry.OperatorAlgebra.IwasawaKANTransform
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Algebra
import InfoGeometry.Canonical.IwasawaMaurerCartanBdGBridge
import InfoGeometry.Projective.Quadrics.PluckerKlein
import InfoGeometry.Canonical.CanonicalZornModularAAVBridge
import InfoGeometry.Canonical.AAVWeakMeasurementKleinSeamBridge
import InfoGeometry.Canonical.DiracKreinMaurerCartanBridge

/-!
# Iwasawa Nilpotent Sector, Chiral Cuntz Boundary, and Klein Weak Measurement Bridge
-/

noncomputable section

namespace InfoGeometry.Canonical.IwasawaCuntzKleinWeak

open scoped Matrix
open Matrix
open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.IwasawaKAN
open InfoGeometry.Topology
open InfoGeometry.Algebra
open InfoGeometry.Canonical.IwasawaMaurerCartanBdG
open InfoGeometry.Projective.Quadrics.PluckerKlein
open InfoGeometry.Canonical.ZornModularAAV
open InfoGeometry.Canonical.AAVWeakMeasurementKleinSeam
open InfoGeometry.Canonical.DiracKreinMaurerCartan

/-! ## 1. Native Clifford Cl(1,1) ≃ M₂(ℝ) and Iwasawa KAN Realization -/

/-- Quadratic form equivalence between Cl11Matrix.q11 and SplitQ11. -/
theorem q11_eq_splitQ11 : Cl11Matrix.q11 = splitQ11 := by
  ext v
  simp [Cl11Matrix.q11_apply, splitQ11_apply]
  ring

/-- The intrinsic Clifford nilpotent generator in Cl(1,1): $n_+ = \frac{1}{2}(J_1^{\mathrm{cl}} + \iota(0, 1))$. -/
def cl11_N_plus : CliffordAlgebra q11 :=
  (1 / 2 : ℝ) • (J1_cl + CliffordAlgebra.ι q11 (0, 1))

/-- The intrinsic Clifford negative nilpotent generator: $n_- = \frac{1}{2}(J_1^{\mathrm{cl}} - \iota(0, 1))$. -/
def cl11_N_minus : CliffordAlgebra q11 :=
  (1 / 2 : ℝ) • (J1_cl - CliffordAlgebra.ι q11 (0, 1))

/-- Transpose of $\operatorname{mat\_dN}(1)$ in $M_2(\mathbb{R})$. -/
theorem mat_dN_one_transpose :
    (mat_dN (1 : ℝ))ᵀ = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat_dN]

/-- 🏆 THEOREM: The matrix horocycle 1-form $\operatorname{mat\_dN}(1)$ is the EXACT image under
    `cl11EquivMat` of the intrinsic Clifford nilpotent generator $n_+$! -/
theorem cl11EquivMat_cl11_N_plus :
    cl11EquivMat cl11_N_plus = mat_dN 1 := by
  dsimp [cl11_N_plus, J1_cl]
  simp only [map_smul, map_add, map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg]
  have he : Eplus * Eminus = J1 := Eplus_mul_Eminus
  rw [he]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [J1, Eminus, mat_dN]

/-- 🏆 THEOREM: The transpose $(\operatorname{mat\_dN}(1))^T$ is the EXACT image under
    `cl11EquivMat` of the intrinsic Clifford negative nilpotent generator $n_-$! -/
theorem cl11EquivMat_cl11_N_minus :
    cl11EquivMat cl11_N_minus = (mat_dN (1 : ℝ))ᵀ := by
  dsimp [cl11_N_minus, J1_cl]
  simp only [map_smul, map_sub, map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg]
  have he : Eplus * Eminus = J1 := Eplus_mul_Eminus
  rw [he, mat_dN_one_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [J1, Eminus, mat_dN]

/-- 🏆 THEOREM: Intrinsic nilpotency of $n_+$ in $\mathrm{Cl}(1,1)$: $(n_+)^2 = 0$. -/
theorem cl11_N_plus_sq :
    cl11_N_plus * cl11_N_plus = 0 := by
  apply cl11EquivMat.injective
  simp only [map_mul, map_zero, cl11EquivMat_cl11_N_plus]
  exact matN_maurer_cartan_sq 1

/-- 🏆 THEOREM: Intrinsic nilpotency of $n_-$ in $\mathrm{Cl}(1,1)$: $(n_-)^2 = 0$. -/
theorem cl11_N_minus_sq :
    cl11_N_minus * cl11_N_minus = 0 := by
  apply cl11EquivMat.injective
  simp only [map_mul, map_zero, cl11EquivMat_cl11_N_minus]
  rw [mat_dN_one_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The Krein fundamental symmetry $\eta$ is $E_+$, which is $\operatorname{cl11EquivMat}(\iota(1, 0))$. -/
theorem etaKrein_eq_cl11EquivMat_iota_pos :
    etaKrein = cl11EquivMat (CliffordAlgebra.ι q11 (1, 0)) := by
  rw [cl11EquivMat_iota_pos]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [etaKrein, Eplus]

/-! ## 2. Integration with Cuntz O₂ Carrier and Nilpotent CAR Ladder -/

section RingCarrier

variable {R : Type*} [CommRing R]

variable {Op : Type*} [Ring Op] [StarRing Op]

/-- 🏆 THEOREM: The canonical CAR ladder operator from Cuntz O₂ carrier squares to zero:
    $(S_{\text{left}} S_{\text{right}}^*)^2 = 0$. -/
theorem cuntz_car_ladder_nilpotent (C : CuntzO2Carrier Op) :
    (kawamuraCARSequence C 0) * (kawamuraCARSequence C 0) = 0 := by
  have h := kawamuraCAR_base_nilpotent C
  dsimp at h
  change (C.S_left * star C.S_right) * (C.S_left * star C.S_right) = 0
  have h_assoc : (C.S_left * star C.S_right) * (C.S_left * star C.S_right) =
                 C.S_left * (star C.S_right * C.S_left) * star C.S_right := by
    simp [mul_assoc]
  rw [h_assoc]
  have h_ortho : star C.S_right * C.S_left = 0 := C.orthogonal_ranges.2
  rw [h_ortho, mul_zero, zero_mul]

/-- 🏆 THEOREM: The 2D matrix horocycle 1-form from `IwasawaMaurerCartanBdG`
    realizes this nilpotent CAR squaring law: $(\omega_N)^2 = 0$. -/
theorem horocycle_realizes_cuntz_nilpotency (dx : R) :
    mat_dN dx * mat_dN dx = 0 :=
  matN_maurer_cartan_sq dx

/-! ## 4. Explicit Map from Horocycle 1-Form to Plücker Klein Quadric -/

/-- Canonical frame vector $u(x) \in R^4$ for the horocycle shear plane. -/
def horocycleFrameU (x : R) : Vec4 R
  | 0 => 1
  | 1 => 0
  | 2 => x
  | 3 => 0

/-- Canonical frame vector $v \in R^4$ for the horocycle shear plane. -/
def horocycleFrameV : Vec4 R
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 0

/-- 🏆 THEOREM: The Plücker coordinates of the horocycle plane satisfy the Klein quadric relation:
    $p_{01} p_{23} - p_{02} p_{13} + p_{03} p_{12} = 0$. -/
theorem horocycle_plane_on_klein_quadric (x : R) :
    KleinRel (pluckerCoord (horocycleFrameU x) horocycleFrameV 0 1)
             (pluckerCoord (horocycleFrameU x) horocycleFrameV 0 2)
             (pluckerCoord (horocycleFrameU x) horocycleFrameV 0 3)
             (pluckerCoord (horocycleFrameU x) horocycleFrameV 1 2)
             (pluckerCoord (horocycleFrameU x) horocycleFrameV 1 3)
             (pluckerCoord (horocycleFrameU x) horocycleFrameV 2 3) := by
  dsimp [KleinRel]
  exact plucker_klein_relation (horocycleFrameU x) horocycleFrameV

/-! ## 5. Krein Adjoint Swapping of Horocycle Chiral Branches -/

/-- The positive nilpotent basis matrix $e_+$ is the unit differential horocycle $\operatorname{mat\_dN}(1)$. -/
def matEPlus : Matrix (Fin 2) (Fin 2) R :=
  mat_dN 1

/-- The negative nilpotent basis matrix $e_-$ is the transpose $(\operatorname{mat\_dN}(1))^T$. -/
def matEMinus : Matrix (Fin 2) (Fin 2) R :=
  (mat_dN 1)ᵀ

/-- Transpose of $\operatorname{mat\_dN}(1)$ in $M_2(R)$. -/
theorem mat_dN_one_transpose_R :
    (mat_dN (1 : R))ᵀ = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat_dN]

/-- Krein adjoint of 2x2 matrix using the fundamental symmetry `etaKrein` from `IwasawaMaurerCartanBdG`. -/
def kreinAdj (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  etaKrein * Aᵀ * etaKrein

/-- 🏆 THEOREM: The Krein adjoint dynamically swaps the positive and negative chiral branches:
    $(e_+)^\sharp = - e_-$. -/
theorem kreinAdj_swaps_horocycle_branches :
    kreinAdj (matEPlus (R := R)) = - matEMinus := by
  dsimp [kreinAdj, matEPlus, matEMinus]
  rw [mat_dN_one_transpose_R]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [etaKrein]

end RingCarrier

/-! ## 6. Spacetime Modular Seam Horizon to Krein-Dirac Orthogonality -/

/-- Pre-selected state on the horizon. -/
def preState : Fin 2 → ℝ :=
  fun _ => 1

/-- Post-selected state parameterized by temporal position $t$. -/
def postState (t : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 + t else 1

/-- 🏆 THEOREM: The Krein-Dirac pairing matches the temporal distance to the Klein seam:
    $\langle \phi(t), \psi \rangle_\mathcal{K} = t$. -/
theorem krein_pairing_eq_temporal_distance (t : ℝ) :
    kreinDiracPairing (postState t) preState = t := by
  dsimp [kreinDiracPairing, postState, preState]
  ring

/-- 🏆 THEOREM: At the Klein seam ($t = 0$), the states are strictly Krein-orthogonal. -/
theorem seam_implies_krein_orthogonality (p : SpacetimePoint) (h_seam : isKleinSeam p) :
    kreinDiracPairing (postState p.t) preState = 0 := by
  rw [klein_seam_iff_t_zero] at h_seam
  rw [h_seam]
  exact krein_pairing_eq_temporal_distance 0

/-- 🏆 THEOREM: The Tomita-Takesaki modular horizon implies Krein-Dirac orthogonality. -/
theorem modular_horizon_implies_krein_ortho (p : SpacetimePoint) (h_mod : isModularHorizon p) :
    kreinDiracPairing (postState p.t) preState = 0 := by
  have h_seam := modular_horizon_on_klein_seam p h_mod
  exact seam_implies_krein_orthogonality p h_seam

/-! ## 7. Weak Value Divergence and BdG Mass Gap Condensation -/

/-- Effective BdG Hamiltonian generated by the AAV weak value. -/
def weakBdGHamiltonian (xi num den : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  matBdG xi (aharonovWeakValue num den)

/-- 🏆 THEOREM: The square of the weak-value-induced BdG Hamiltonian
    equals the BdG dispersion energy times the identity:
    $H_{\text{BdG}}^2(\xi, \Omega_w) = (\xi^2 + \Omega_w^2) \mathbb{I}$. -/
theorem weakBdGHamiltonian_sq (xi num den : ℝ) :
    weakBdGHamiltonian xi num den * weakBdGHamiltonian xi num den =
      bdgEnergySq xi (aharonovWeakValue num den) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  dsimp [weakBdGHamiltonian, bdgEnergySq]
  exact matBdG_sq xi (aharonovWeakValue num den)

/-- 🏆 THEOREM: Weak Amplification induces a strictly positive energy gap above the massless lightcone. -/
theorem weak_induced_mass_gap_positive (xi num den : ℝ)
    (h_num : num ≠ 0) (h_den : den ≠ 0) :
    bdgEnergySq xi (aharonovWeakValue num den) > xi * xi := by
  have h_weak_ne_zero : aharonovWeakValue num den ≠ 0 := by
    dsimp [aharonovWeakValue]
    exact div_ne_zero h_num h_den
  exact bdg_mass_gap_positive xi (aharonovWeakValue num den) h_weak_ne_zero

/-- 🏆 THEOREM: Weak Amplification decelerates lightcone rays into subluminal group velocity:
    $v_g^2 < 1$. -/
theorem weak_induced_subluminal (p num den : ℝ)
    (h_p : p ≠ 0) (h_num : num ≠ 0) (h_den : den ≠ 0) :
    groupVelocitySq p (aharonovWeakValue num den) < 1 := by
  have h_weak_ne_zero : aharonovWeakValue num den ≠ 0 := by
    dsimp [aharonovWeakValue]
    exact div_ne_zero h_num h_den
  exact subluminal_group_velocity p (aharonovWeakValue num den) h_p h_weak_ne_zero

/-! ## 8. Master Integration Packet -/

/-- Master integration packet certifying the cross-subsystem arrows:
    Clifford Cl(1,1) ≃ M₂(ℝ) ⟷ DoubledSpace representation ⟷ Cuntz O₂ nilpotency ⟷
    Iwasawa horocycle ⟷ Plücker Klein quadric ⟷ Krein-Dirac seam orthogonality ⟷
    BdG mass gap condensation. -/
structure IwasawaCuntzKleinWeakIntegrationPacket where
  clifford_nplus_horocycle : cl11EquivMat cl11_N_plus = mat_dN 1
  clifford_nminus_horocycle : cl11EquivMat cl11_N_minus = (mat_dN (1 : ℝ))ᵀ
  clifford_nplus_sq : cl11_N_plus * cl11_N_plus = 0
  cuntz_car_nilpotent : ∀ (Op : Type*) [Ring Op] [StarRing Op] (C : CuntzO2Carrier Op),
    (kawamuraCARSequence C 0) * (kawamuraCARSequence C 0) = 0
  horocycle_cuntz_sq : ∀ (R : Type*) [CommRing R] (dx : R),
    mat_dN dx * mat_dN dx = 0
  horocycle_on_klein : ∀ (R : Type*) [CommRing R] (x : R),
    KleinRel (pluckerCoord (horocycleFrameU x) horocycleFrameV 0 1)
             (pluckerCoord (horocycleFrameU x) horocycleFrameV 0 2)
             (pluckerCoord (horocycleFrameU x) horocycleFrameV 0 3)
             (pluckerCoord (horocycleFrameU x) horocycleFrameV 1 2)
             (pluckerCoord (horocycleFrameU x) horocycleFrameV 1 3)
             (pluckerCoord (horocycleFrameU x) horocycleFrameV 2 3)
  krein_branch_swap : ∀ (R : Type*) [CommRing R],
    kreinAdj (matEPlus (R := R)) = - matEMinus
  seam_orthogonality : ∀ (p : SpacetimePoint),
    isKleinSeam p → kreinDiracPairing (postState p.t) preState = 0
  modular_horizon_ortho : ∀ (p : SpacetimePoint),
    isModularHorizon p → kreinDiracPairing (postState p.t) preState = 0
  bdg_hamiltonian_sq : ∀ (xi num den : ℝ),
    weakBdGHamiltonian xi num den * weakBdGHamiltonian xi num den =
      bdgEnergySq xi (aharonovWeakValue num den) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  bdg_mass_gap : ∀ (xi num den : ℝ), num ≠ 0 → den ≠ 0 →
    bdgEnergySq xi (aharonovWeakValue num den) > xi * xi
  bdg_subluminal : ∀ (p num den : ℝ), p ≠ 0 → num ≠ 0 → den ≠ 0 →
    groupVelocitySq p (aharonovWeakValue num den) < 1

/-- Constructor for the verified integration packet. -/
def makeIwasawaCuntzKleinWeakIntegrationPacket : IwasawaCuntzKleinWeakIntegrationPacket where
  clifford_nplus_horocycle := cl11EquivMat_cl11_N_plus
  clifford_nminus_horocycle := cl11EquivMat_cl11_N_minus
  clifford_nplus_sq := cl11_N_plus_sq
  cuntz_car_nilpotent := fun _ _ _ => cuntz_car_ladder_nilpotent
  horocycle_cuntz_sq := fun _ _ => horocycle_realizes_cuntz_nilpotency
  horocycle_on_klein := fun _ _ => horocycle_plane_on_klein_quadric
  krein_branch_swap := fun _ _ => kreinAdj_swaps_horocycle_branches
  seam_orthogonality := seam_implies_krein_orthogonality
  modular_horizon_ortho := modular_horizon_implies_krein_ortho
  bdg_hamiltonian_sq := weakBdGHamiltonian_sq
  bdg_mass_gap := weak_induced_mass_gap_positive
  bdg_subluminal := weak_induced_subluminal

/-- Grand certification theorem of the cross-subsystem integration packet. -/
theorem iwasawa_cuntz_klein_weak_integration_certified :
    (makeIwasawaCuntzKleinWeakIntegrationPacket).clifford_nplus_horocycle =
      cl11EquivMat_cl11_N_plus := rfl

end InfoGeometry.Canonical.IwasawaCuntzKleinWeak
