/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CARMajoranaFiniteBridge
import InfoGeometry.Canonical.KitaevDiracBoundaryProjector
import InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative
import InfoGeometry.Algebra.ChiralZornCARAndSchurBridge

/-! Explicit complex intertwiner from the native real skew chain coefficient
matrix to the native BdG matrix. Its real image is fixed by charge conjugation.
-/
noncomputable section
namespace InfoGeometry.Canonical.KitaevMajoranaNambu
open Matrix CARMajoranaFiniteBridge ConcreteKitaevBdGMatrix
open MajoranaPfaffian4 KitaevChainMajoranaZeroModes
open InfoGeometry.Algebra.GogberashviliNilpotentCARBridge
open InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative

/-! Matrix units witness noncommutativity of the actual edge chiral carrier. -/
def edgeChiralE01 : Matrix (Fin 2) (Fin 2) ChainOp :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

def edgeChiralE10 : Matrix (Fin 2) (Fin 2) ChainOp :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

theorem edgeChiralMatrix_noncommutative_witness :
    edgeChiralE01 * edgeChiralE10 ≠ edgeChiralE10 * edgeChiralE01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ChainOp => M 0 0) h
  have hOne : (1 : ChainOp) = 0 := by
    simpa [edgeChiralE01, edgeChiralE10, Matrix.mul_apply, Fin.sum_univ_two] using h00
  exact one_ne_zero hOne

/-! ## Majorana-derived edge modes and chiral supercharges -/

def edgeHamiltonian (t : ℝ) : ChainOp :=
  kitaevSweetSpotHamiltonian 2 (t • (1 : ChainOp)) twoSiteMajorana

def edgeLeftMajorana : ChainOp := twoSiteMajorana 0

def edgeRightMajorana : ChainOp := twoSiteMajorana 3

def edgePhasedRightMajorana : ChainOp := Complex.I • edgeRightMajorana

/-- The isotropic modes are formed from the endpoint Majorana zero modes. -/
def edgeAnnihilation : ChainOp :=
  GPlus (K := ℂ) edgeLeftMajorana edgePhasedRightMajorana

def edgeCreation : ChainOp :=
  GMinus (K := ℂ) edgeLeftMajorana edgePhasedRightMajorana

theorem edge_endpoint_majoranas_commute (t : ℝ) :
    edgeHamiltonian t * edgeLeftMajorana = edgeLeftMajorana * edgeHamiltonian t ∧
    edgeHamiltonian t * edgeRightMajorana = edgeRightMajorana * edgeHamiltonian t := by
  have h := car_to_chain_to_pfaffian t
  dsimp only at h
  exact ⟨sub_eq_zero.mp h.2.2.1, sub_eq_zero.mp h.2.2.2.1⟩

private theorem edgeLeftMajorana_sq : edgeLeftMajorana * edgeLeftMajorana = 1 := by
  apply smul_right_injective (M := ChainOp) (by norm_num : (2 : ℂ) ≠ 0)
  simpa [edgeLeftMajorana, two_smul, show (2 : ChainOp) = 1 + 1 by norm_num] using
    twoSiteMajorana_car (0 : Fin 4) (0 : Fin 4)

private theorem edgeRightMajorana_sq : edgeRightMajorana * edgeRightMajorana = 1 := by
  apply smul_right_injective (M := ChainOp) (by norm_num : (2 : ℂ) ≠ 0)
  simpa [edgeRightMajorana, two_smul, show (2 : ChainOp) = 1 + 1 by norm_num] using
    twoSiteMajorana_car (3 : Fin 4) (3 : Fin 4)

private theorem edgeEndpoints_anticommute :
    edgeLeftMajorana * edgeRightMajorana +
      edgeRightMajorana * edgeLeftMajorana = 0 := by
  simpa [edgeLeftMajorana, edgeRightMajorana] using
    twoSiteMajorana_car (0 : Fin 4) (3 : Fin 4)

private theorem edgePhasedRightMajorana_sq :
    edgePhasedRightMajorana * edgePhasedRightMajorana = -1 := by
  rw [edgePhasedRightMajorana, smul_mul_smul, edgeRightMajorana_sq]
  simp [Complex.I_sq]

private theorem edgeLeft_phasedRight_anticommute :
    edgeLeftMajorana * edgePhasedRightMajorana +
      edgePhasedRightMajorana * edgeLeftMajorana = 0 := by
  rw [edgePhasedRightMajorana, mul_smul_comm, smul_mul_assoc, ← smul_add,
    edgeEndpoints_anticommute, smul_zero]

/-- Majorana CAR, together with the endpoint square and phase relations, proves
nilpotence and the normalized creation-annihilation anticommutator. -/
theorem edgeAnnihilation_creation_CAR :
    edgeAnnihilation * edgeAnnihilation = 0 ∧
    edgeCreation * edgeCreation = 0 ∧
    edgeAnnihilation * edgeCreation + edgeCreation * edgeAnnihilation = 1 := by
  have hcross : edgePhasedRightMajorana * edgeLeftMajorana =
      -(edgeLeftMajorana * edgePhasedRightMajorana) :=
    eq_neg_of_add_eq_zero_right edgeLeft_phasedRight_anticommute
  have hJ : edgeLeftMajorana * edgePhasedRightMajorana =
      edgeLeftMajorana * edgePhasedRightMajorana := rfl
  exact ⟨GPlus_square_zero _ _ edgeLeftMajorana_sq edgePhasedRightMajorana_sq
      edgeLeft_phasedRight_anticommute,
    GMinus_square_zero _ _ edgeLeftMajorana_sq edgePhasedRightMajorana_sq
      edgeLeft_phasedRight_anticommute,
    GPlus_GMinus_CAR (by norm_num) edgeLeftMajorana edgePhasedRightMajorana
      (edgeLeftMajorana * edgePhasedRightMajorana) edgeLeftMajorana_sq
      edgePhasedRightMajorana_sq hcross hJ⟩

/-- The isotropic edge modes are conserved because each is a linear combination
of the two endpoint Majorana zero modes. -/
theorem edgeHamiltonian_commutes_with_edge_modes (t : ℝ) :
    edgeHamiltonian t * edgeAnnihilation = edgeAnnihilation * edgeHamiltonian t ∧
    edgeHamiltonian t * edgeCreation = edgeCreation * edgeHamiltonian t := by
  rcases edge_endpoint_majoranas_commute t with ⟨h0, h3⟩
  have h0c : edgeLeftMajorana * edgeHamiltonian t =
      edgeHamiltonian t * edgeLeftMajorana := h0.symm
  have hjc : edgePhasedRightMajorana * edgeHamiltonian t =
      edgeHamiltonian t * edgePhasedRightMajorana := by
    rw [edgePhasedRightMajorana, smul_mul_assoc, mul_smul_comm, h3.symm]
  have hsum : (edgeLeftMajorana + edgePhasedRightMajorana) * edgeHamiltonian t =
      edgeHamiltonian t * (edgeLeftMajorana + edgePhasedRightMajorana) := by
    rw [add_mul, mul_add, h0c, hjc]
  have hdiff : (edgeLeftMajorana - edgePhasedRightMajorana) * edgeHamiltonian t =
      edgeHamiltonian t * (edgeLeftMajorana - edgePhasedRightMajorana) := by
    rw [sub_mul, mul_sub, h0c, hjc]
  have hplus : edgeAnnihilation * edgeHamiltonian t =
      edgeHamiltonian t * edgeAnnihilation := by
    unfold edgeAnnihilation GPlus
    rw [Algebra.smul_def]
    calc
      ((algebraMap ℂ ChainOp) (2⁻¹ : ℂ) *
          (edgeLeftMajorana + edgePhasedRightMajorana)) * edgeHamiltonian t =
          (algebraMap ℂ ChainOp) (2⁻¹ : ℂ) *
            ((edgeLeftMajorana + edgePhasedRightMajorana) * edgeHamiltonian t) := by
              simp only [mul_assoc]
      _ = (algebraMap ℂ ChainOp) (2⁻¹ : ℂ) *
          (edgeHamiltonian t * (edgeLeftMajorana + edgePhasedRightMajorana)) := by rw [hsum]
      _ = edgeHamiltonian t * ((algebraMap ℂ ChainOp) (2⁻¹ : ℂ) *
          (edgeLeftMajorana + edgePhasedRightMajorana)) := by
            calc
              _ = ((algebraMap ℂ ChainOp) (2⁻¹ : ℂ) * edgeHamiltonian t) *
                  (edgeLeftMajorana + edgePhasedRightMajorana) := by simp only [mul_assoc]
              _ = (edgeHamiltonian t * (algebraMap ℂ ChainOp) (2⁻¹ : ℂ)) *
                  (edgeLeftMajorana + edgePhasedRightMajorana) := by
                    rw [Algebra.commutes (2⁻¹ : ℂ) (edgeHamiltonian t)]
              _ = _ := by simp only [mul_assoc]
  have hminus : edgeCreation * edgeHamiltonian t =
      edgeHamiltonian t * edgeCreation := by
    unfold edgeCreation GMinus
    rw [Algebra.smul_def]
    calc
      ((algebraMap ℂ ChainOp) (2⁻¹ : ℂ) *
          (edgeLeftMajorana - edgePhasedRightMajorana)) * edgeHamiltonian t =
          (algebraMap ℂ ChainOp) (2⁻¹ : ℂ) *
            ((edgeLeftMajorana - edgePhasedRightMajorana) * edgeHamiltonian t) := by
              simp only [mul_assoc]
      _ = (algebraMap ℂ ChainOp) (2⁻¹ : ℂ) *
          (edgeHamiltonian t * (edgeLeftMajorana - edgePhasedRightMajorana)) := by rw [hdiff]
      _ = edgeHamiltonian t * ((algebraMap ℂ ChainOp) (2⁻¹ : ℂ) *
          (edgeLeftMajorana - edgePhasedRightMajorana)) := by
            calc
              _ = ((algebraMap ℂ ChainOp) (2⁻¹ : ℂ) * edgeHamiltonian t) *
                  (edgeLeftMajorana - edgePhasedRightMajorana) := by simp only [mul_assoc]
              _ = (edgeHamiltonian t * (algebraMap ℂ ChainOp) (2⁻¹ : ℂ)) *
                  (edgeLeftMajorana - edgePhasedRightMajorana) := by
                    rw [Algebra.commutes (2⁻¹ : ℂ) (edgeHamiltonian t)]
              _ = _ := by simp only [mul_assoc]
  exact ⟨hplus.symm, hminus.symm⟩

abbrev EdgeChiralMatrix := Matrix (Fin 2) (Fin 2) ChainOp

def edgeQPlus : EdgeChiralMatrix := qPlus edgeAnnihilation

def edgeQMinus : EdgeChiralMatrix := qMinus edgeCreation

@[simp] theorem edgeQPlus_sq : edgeQPlus * edgeQPlus = 0 := qPlus_sq _

@[simp] theorem edgeQMinus_sq : edgeQMinus * edgeQMinus = 0 := qMinus_sq _

def edgeChiralParity : Matrix (Fin 2) (Fin 2) ChainOp := gamma

theorem edgeChiralParity_anticommutes_supercharges :
    edgeChiralParity * edgeQPlus = -(edgeQPlus * edgeChiralParity) ∧
    edgeChiralParity * edgeQMinus = -(edgeQMinus * edgeChiralParity) := by
  exact ⟨gamma_qPlus_anticomm edgeAnnihilation,
    gamma_qMinus_anticomm edgeCreation⟩

def edgeHamiltonianChiralLift (t : ℝ) : EdgeChiralMatrix :=
  !![edgeHamiltonian t, 0; 0, edgeHamiltonian t]

/-- The physical Hamiltonian commutes with the chiral supercharges since each
matrix entry reduces to conservation of the Majorana-derived edge mode. -/
theorem edgeHamiltonianChiralLift_commutes_supercharges (t : ℝ) :
    edgeHamiltonianChiralLift t * edgeQPlus = edgeQPlus * edgeHamiltonianChiralLift t ∧
    edgeHamiltonianChiralLift t * edgeQMinus = edgeQMinus * edgeHamiltonianChiralLift t := by
  rcases edgeHamiltonian_commutes_with_edge_modes t with ⟨ha, hc⟩
  constructor <;> (ext i j; fin_cases i <;> fin_cases j <;>
    simp [edgeHamiltonianChiralLift, edgeQPlus, edgeQMinus, qPlus, qMinus,
      Matrix.mul_apply, Fin.sum_univ_two, ha, hc])

def nambuMatrix : Mat4C :=
  !![Complex.I, 1, 0, 0; 0, 0, -Complex.I, 1;
     -Complex.I, 1, 0, 0; 0, 0, Complex.I, 1]

def nambuInverse : Mat4C :=
  !![-Complex.I/2, 0, Complex.I/2, 0; 1/2, 0, 1/2, 0;
     0, Complex.I/2, 0, -Complex.I/2; 0, 1/2, 0, 1/2]

theorem nambuInverse_mul : nambuInverse * nambuMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nambuInverse, nambuMatrix, mul_apply, Fin.sum_univ_four,
      Complex.I_sq, Matrix.one_apply] <;> ring_nf <;> norm_num [Complex.I_sq]

theorem nambuMatrix_mul_inverse : nambuMatrix * nambuInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nambuInverse, nambuMatrix, mul_apply, Fin.sum_univ_four,
      Complex.I_sq, Matrix.one_apply] <;> ring_nf <;> norm_num [Complex.I_sq]

theorem sweetSpot_nambu_intertwiner (t : ℝ) :
    kitaevSweetSpot4 t * nambuMatrix = Complex.I •
      (nambuMatrix * (sweetSpotKernel t).omega.map (algebraMap ℝ ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kitaevSweetSpot4, nambuMatrix, sweetSpotKernel, matchingKernel,
      skewMatrix4, mul_apply, Fin.sum_univ_four, vecMul, dotProduct,
      Matrix.map_apply] <;> ring_nf <;> simp [Complex.I_sq]

def nambuSpinor (v : Fin 4 → ℝ) : Vec4C := nambuMatrix *ᵥ (fun i => (v i : ℂ))

theorem nambuSpinor_charge_fixed (v : Fin 4 → ℝ) :
    particleHole4 *ᵥ star (nambuSpinor v) = nambuSpinor v := by
  ext i
  fin_cases i <;>
    simp [nambuSpinor, nambuMatrix, particleHole4, mulVec, dotProduct,
      Fin.sum_univ_four]

theorem sweetSpot_nambu_action (t : ℝ) (v : Fin 4 → ℝ) :
    kitaevSweetSpot4 t *ᵥ nambuSpinor v =
      Complex.I • nambuSpinor ((sweetSpotKernel t).omega *ᵥ v) := by
  unfold nambuSpinor
  rw [mulVec_mulVec, sweetSpot_nambu_intertwiner, smul_mulVec,
    ← mulVec_mulVec]
  congr 1
  congr 1
  funext i
  exact (RingHom.map_mulVec (algebraMap ℝ ℂ) (sweetSpotKernel t).omega v i).symm

theorem nambuSpinor_eq_zero_iff (v : Fin 4 → ℝ) : nambuSpinor v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hv := congrArg (fun w => nambuInverse *ᵥ w) h
    simp only [nambuSpinor, mulVec_mulVec, nambuInverse_mul, one_mulVec,
      mulVec_zero] at hv
    ext i
    have hi := congrFun hv i
    change (v i : ℂ) = 0 at hi
    change v i = 0
    exact_mod_cast hi
  · intro h
    subst v
    change nambuMatrix *ᵥ (0 : Vec4C) = 0
    exact mulVec_zero _

theorem sweetSpot_nambu_kernel_iff (t : ℝ) (v : Fin 4 → ℝ) :
    kitaevSweetSpot4 t *ᵥ nambuSpinor v = 0 ↔ (sweetSpotKernel t).omega *ᵥ v = 0 := by
  rw [sweetSpot_nambu_action, smul_eq_zero]
  simp only [Complex.I_ne_zero, false_or, nambuSpinor_eq_zero_iff]

/-- The boundary Dirac projector retains precisely the endpoint coefficients. -/
theorem boundary_projector_nambu (v : Vec4C) :
    boundaryDiracProjector *ᵥ (nambuMatrix *ᵥ v) =
      nambuMatrix *ᵥ ![v 0, 0, 0, v 3] := by
  rw [boundaryDiracProjector_explicit]
  ext i
  fin_cases i <;>
    simp [nambuMatrix, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem conserved_chain_iff_nambu_kernel (t : ℝ) (v : Fin 4 → ℝ) :
    let H := kitaevSweetSpotHamiltonian 2 (t • (1 : ChainOp)) twoSiteMajorana
    H * Fintype.linearCombination ℝ twoSiteMajorana v -
      Fintype.linearCombination ℝ twoSiteMajorana v * H = 0 ↔
        kitaevSweetSpot4 t *ᵥ nambuSpinor v = 0 := by
  exact (sweetSpot_chain_commutator_eq_zero_iff t v).trans
    (sweetSpot_nambu_kernel_iff t v).symm

end InfoGeometry.Canonical.KitaevMajoranaNambu
