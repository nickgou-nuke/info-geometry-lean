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
# Clifford nilpotents, Plücker coordinates, and a split-pairing model

The Clifford-to-matrix map is an algebra equivalence. The frame and weak-value
Hamiltonian below are explicit model choices. Their identities do not construct
a Cuntz representation, modular evolution, or a condensation mechanism.
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

/-- The matrix horocycle 1-form $\operatorname{mat\_dN}(1)$ is the EXACT image under
    `cl11EquivMat` of the intrinsic Clifford nilpotent generator $n_+$! -/
theorem cl11EquivMat_cl11_N_plus :
    cl11EquivMat cl11_N_plus = mat_dN 1 := by
  dsimp [cl11_N_plus, J1_cl]
  simp only [map_smul, map_add, map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg]
  have he : Eplus * Eminus = J1 := Eplus_mul_Eminus
  rw [he]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [J1, Eminus, mat_dN]

/-- The transpose $(\operatorname{mat\_dN}(1))^T$ is the EXACT image under
    `cl11EquivMat` of the intrinsic Clifford negative nilpotent generator $n_-$! -/
theorem cl11EquivMat_cl11_N_minus :
    cl11EquivMat cl11_N_minus = (mat_dN (1 : ℝ))ᵀ := by
  dsimp [cl11_N_minus, J1_cl]
  simp only [map_smul, map_sub, map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg]
  have he : Eplus * Eminus = J1 := Eplus_mul_Eminus
  rw [he, mat_dN_one_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [J1, Eminus, mat_dN]

/-- Intrinsic nilpotency of $n_+$ in $\mathrm{Cl}(1,1)$: $(n_+)^2 = 0$. -/
theorem cl11_N_plus_sq :
    cl11_N_plus * cl11_N_plus = 0 := by
  apply cl11EquivMat.injective
  simp only [map_mul, map_zero, cl11EquivMat_cl11_N_plus]
  exact matN_maurer_cartan_sq 1

/-- Intrinsic nilpotency of $n_-$ in $\mathrm{Cl}(1,1)$: $(n_-)^2 = 0$. -/
theorem cl11_N_minus_sq :
    cl11_N_minus * cl11_N_minus = 0 := by
  apply cl11EquivMat.injective
  simp only [map_mul, map_zero, cl11EquivMat_cl11_N_minus]
  rw [mat_dN_one_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The normalized Clifford generators satisfy the mixed CAR relation. -/
theorem cl11_N_anticomm :
    cl11_N_plus * cl11_N_minus + cl11_N_minus * cl11_N_plus = 1 := by
  apply cl11EquivMat.injective
  simp only [map_add, map_mul, map_one, cl11EquivMat_cl11_N_plus,
    cl11EquivMat_cl11_N_minus]
  rw [mat_dN_one_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mat_dN, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Krein fundamental symmetry $\eta$ is $E_+$, which is $\operatorname{cl11EquivMat}(\iota(1, 0))$. -/
theorem etaKrein_eq_cl11EquivMat_iota_pos :
    etaKrein = cl11EquivMat (CliffordAlgebra.ι q11 (1, 0)) := by
  rw [cl11EquivMat_iota_pos]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [etaKrein, Eplus]

/-! ## 2. Integration with Cuntz O₂ Carrier and Nilpotent CAR Ladder -/

section RingCarrier

variable {R : Type*} [CommRing R]

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

/-- The Plücker coordinates of the horocycle plane satisfy the Klein quadric relation:
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

/-- Adjoint for the split bilinear form with matrix `etaKrein`.
Over the reals this is the Krein adjoint; a complex Hermitian form would
require conjugate transpose instead of transpose. -/
def kreinAdj (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  etaKrein * Aᵀ * etaKrein

/-- The split bilinear adjoint exchanges the two nilpotent matrices with a minus sign:
    $(e_+)^\sharp = - e_-$. -/
theorem kreinAdj_swaps_horocycle_branches :
    kreinAdj (matEPlus (R := R)) = - matEMinus := by
  dsimp [kreinAdj, matEPlus, matEMinus]
  rw [mat_dN_one_transpose_R]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [etaKrein]

end RingCarrier

/-! ## 6. Orthogonality in the parameterized split-pairing model -/

/-- Constant pre-selected vector for the split-pairing model. -/
def preState : Fin 2 → ℝ :=
  fun _ => 1

/-- Post-selected vector with real parameter $t$. -/
def postState (t : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 + t else 1

/-- The chosen vectors have split pairing equal to their parameter:
    $\langle \phi(t), \psi \rangle_\mathcal{K} = t$. -/
theorem krein_pairing_eq_temporal_distance (t : ℝ) :
    kreinDiracPairing (postState t) preState = t := by
  dsimp [kreinDiracPairing, postState, preState]
  ring

/-- The predicate `isKleinSeam` forces zero pairing for these vectors. -/
theorem seam_implies_krein_orthogonality (p : SpacetimePoint) (h_seam : isKleinSeam p) :
    kreinDiracPairing (postState p.t) preState = 0 := by
  rw [klein_seam_iff_t_zero] at h_seam
  rw [h_seam]
  exact krein_pairing_eq_temporal_distance 0

/-- The coordinate predicate `isModularHorizon` forces zero pairing.
This statement uses the predicate defined in `AAVWeakMeasurementKleinSeam`;
it does not construct Tomita–Takesaki modular data. -/
theorem modular_horizon_implies_krein_ortho (p : SpacetimePoint) (h_mod : isModularHorizon p) :
    kreinDiracPairing (postState p.t) preState = 0 := by
  have h_seam := modular_horizon_on_klein_seam p h_mod
  exact seam_implies_krein_orthogonality p h_seam

/-! ## 7. BdG identities after choosing the weak ratio as the gap parameter -/

/-- BdG matrix with its gap parameter defined to be the AAV ratio. -/
def weakBdGHamiltonian (xi num den : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  matBdG xi (aharonovWeakValue num den)

/-- The square of the weak-value-induced BdG Hamiltonian
    equals the BdG dispersion energy times the identity:
    $H_{\text{BdG}}^2(\xi, \Omega_w) = (\xi^2 + \Omega_w^2) \mathbb{I}$. -/
theorem weakBdGHamiltonian_sq (xi num den : ℝ) :
    weakBdGHamiltonian xi num den * weakBdGHamiltonian xi num den =
      bdgEnergySq xi (aharonovWeakValue num den) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  dsimp [weakBdGHamiltonian, bdgEnergySq]
  exact matBdG_sq xi (aharonovWeakValue num den)

/-- A nonzero numerator and denominator give a strictly positive squared-gap contribution
in the chosen BdG model. -/
theorem weak_induced_mass_gap_positive (xi num den : ℝ)
    (h_num : num ≠ 0) (h_den : den ≠ 0) :
    bdgEnergySq xi (aharonovWeakValue num den) > xi * xi := by
  have h_weak_ne_zero : aharonovWeakValue num den ≠ 0 := by
    dsimp [aharonovWeakValue]
    exact div_ne_zero h_num h_den
  exact bdg_mass_gap_positive xi (aharonovWeakValue num den) h_weak_ne_zero

/-- For the chosen nonzero gap and momentum, the defined squared velocity satisfies:
    $v_g^2 < 1$. -/
theorem weak_induced_subluminal (p num den : ℝ)
    (h_p : p ≠ 0) (h_num : num ≠ 0) (h_den : den ≠ 0) :
    groupVelocitySq p (aharonovWeakValue num den) < 1 := by
  have h_weak_ne_zero : aharonovWeakValue num den ≠ 0 := by
    dsimp [aharonovWeakValue]
    exact div_ne_zero h_num h_den
  exact subluminal_group_velocity p (aharonovWeakValue num den) h_p h_weak_ne_zero

end InfoGeometry.Canonical.IwasawaCuntzKleinWeak
