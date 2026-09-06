import proofs.CantorBoundaryCuntzFamily
import proofs.ArtinMonodromyPin55
import proofs.UHFInductiveColimit

noncomputable section

namespace MobiusCantorTKKClosure

open CantorBoundaryCuntzFamily
open UHFInductiveColimit
open ArtinMonodromyPin55

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

def mobiusJ (z : ℂ) : ℂ := z⁻¹

def mobiusGamma (z : ℂ) : ℂ := -z

theorem mobiusJ_involutive (z : ℂ) :
    mobiusJ (mobiusJ z) = z := by
  simp [mobiusJ, inv_inv]

theorem mobiusGamma_involutive (z : ℂ) :
    mobiusGamma (mobiusGamma z) = z := by
  simp [mobiusGamma]

theorem mobiusJ_gamma_commute (z : ℂ) :
    mobiusJ (mobiusGamma z) = mobiusGamma (mobiusJ z) := by
  simp [mobiusJ, mobiusGamma]

theorem mobiusGammaJ_involutive (z : ℂ) :
    mobiusGamma (mobiusJ (mobiusGamma (mobiusJ z))) = z := by
  simp [mobiusJ, mobiusGamma, inv_inv]

theorem cantor_head_tail_self_similarity (b : C4Boundary) :
    prependN (headN b) (tailN b) = b :=
  prependN_headN_tailN b

theorem cantor_prepend_head_tail (i : Fin 4) (b : C4Boundary) :
    headN (prependN i b) = i ∧ tailN (prependN i b) = b := by
  exact ⟨headN_prependN i b, tailN_prependN i b⟩

theorem cantor_cuntz_branch_orthogonality (i j : Fin 4) :
    cuntzT i * cuntzS j =
      if i = j then (1 : C4Functions →ₗ[ℂ] C4Functions) else 0 :=
  cuntz_ortho i j

theorem cantor_cuntz_branch_partition :
    (∑ i : Fin 4, cuntzS i * cuntzT i) =
      (1 : C4Functions →ₗ[ℂ] C4Functions) :=
  cuntz_partition

theorem cantor_cut_fractal_step (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f :=
  cylinder_compatible_succ n f

theorem tkk_centralizer_atom_sq (z : CentralizerAtom) :
    centralizerValue z * centralizerValue z = (1 : ArtinMonodromyPin55.M2C) :=
  centralizer_atom_sq z

theorem tkk_negative_root_closes (A : ArtinMonodromyPin55.M2C) (n : ℕ)
    (h : A ^ n = -(1 : ArtinMonodromyPin55.M2C)) :
    A ^ (2 * n) = (1 : ArtinMonodromyPin55.M2C) :=
  negative_centralizer_root_closes A n h

theorem tkk_pin55_anomaly_zero :
    Clifford55AnomalyOSP.anomalyIndex 5 5 = 0 :=
  Clifford55AnomalyOSP.anomalyIndex_55_zero

theorem mobius_cantor_tkk_closure_synthesis
    (z : ℂ) (b : C4Boundary) (i j : Fin 4)
    (n : ℕ) (f : DiagAlg n) :
    mobiusJ (mobiusJ z) = z ∧
    mobiusGamma (mobiusGamma z) = z ∧
    mobiusJ (mobiusGamma z) = mobiusGamma (mobiusJ z) ∧
    prependN (headN b) (tailN b) = b ∧
    headN (prependN i b) = i ∧
    tailN (prependN i b) = b ∧
    cuntzT i * cuntzS j =
      (if i = j then (1 : C4Functions →ₗ[ℂ] C4Functions) else 0) ∧
    (∑ k : Fin 4, cuntzS k * cuntzT k) =
      (1 : C4Functions →ₗ[ℂ] C4Functions) ∧
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f ∧
    (∀ c : CentralizerAtom,
      centralizerValue c * centralizerValue c = (1 : ArtinMonodromyPin55.M2C)) ∧
    Clifford55AnomalyOSP.anomalyIndex 5 5 = 0 := by
  exact ⟨mobiusJ_involutive z,
    mobiusGamma_involutive z,
    mobiusJ_gamma_commute z,
    cantor_head_tail_self_similarity b,
    headN_prependN i b,
    tailN_prependN i b,
    cantor_cuntz_branch_orthogonality i j,
    cantor_cuntz_branch_partition,
    cantor_cut_fractal_step n f,
    tkk_centralizer_atom_sq,
    tkk_pin55_anomaly_zero⟩

/-! ## Cartan Decomposition and TKK Projectors -/

/-- The Cartan involution $J$ on the TKK algebra. -/
def tkkInvolution (J : M2C) : Prop := J * J = (1 : M2C)

/-- The symmetric (right-handed/causal) Cartan projector $P_+ = (I + J)/2$. -/
def P_plus (J : M2C) : M2C := (1/2 : ℂ) • ((1 : M2C) + J)

/-- The antisymmetric (left-handed/anticausal) Cartan projector $P_- = (I - J)/2$. -/
def P_minus (J : M2C) : M2C := (1/2 : ℂ) • ((1 : M2C) - J)

/-- The sum of the Cartan projectors reconstructs the identity operator. -/
theorem cartan_projectors_sum_to_id (J : M2C) :
    P_plus J + P_minus J = (1 : M2C) := by
  dsimp [P_plus, P_minus]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] <;> ring

/-- The Cartan projectors are orthogonal: $P_+ P_- = 0$. -/
theorem cartan_projectors_orthogonal (J : M2C) (hJ : tkkInvolution J) :
    P_plus J * P_minus J = 0 := by
  dsimp [P_plus, P_minus, tkkInvolution] at *
  have H1 : (1 / 2 : ℂ) • (1 + J) * ((1 / 2 : ℂ) • (1 - J)) = (1 / 4 : ℂ) • (1 - J * J) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two] <;> ring
  rw [H1, hJ, sub_self, smul_zero]

/-- $P_+$ is idempotent: $P_+^2 = P_+$. -/
theorem cartan_projector_plus_idempotent (J : M2C) (hJ : tkkInvolution J) :
    P_plus J * P_plus J = P_plus J := by
  dsimp [P_plus, tkkInvolution] at *
  have H1 : (1 / 2 : ℂ) • (1 + J) * ((1 / 2 : ℂ) • (1 + J)) = (1 / 4 : ℂ) • (1 + J + J + J * J) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Fin.sum_univ_two] <;> ring
  rw [H1, hJ]
  have H2 : (1 / 4 : ℂ) • (1 + J + J + 1) = (1 / 2 : ℂ) • (1 + J) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.smul_apply] <;> ring
  rw [H2]

/-- $P_-$ is idempotent: $P_-^2 = P_-$. -/
theorem cartan_projector_minus_idempotent (J : M2C) (hJ : tkkInvolution J) :
    P_minus J * P_minus J = P_minus J := by
  dsimp [P_minus, tkkInvolution] at *
  have H1 : (1 / 2 : ℂ) • (1 - J) * ((1 / 2 : ℂ) • (1 - J)) = (1 / 4 : ℂ) • (1 - J - J + J * J) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Fin.sum_univ_two] <;> ring
  rw [H1, hJ]
  have H2 : (1 / 4 : ℂ) • (1 - J - J + 1) = (1 / 2 : ℂ) • (1 - J) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply] <;> ring
  rw [H2]

/-- $P_+$ projects onto the +1 eigenspace of the Cartan involution $J$. -/
theorem cartan_involution_eigen_plus (J : M2C) (hJ : tkkInvolution J) :
    J * P_plus J = P_plus J := by
  dsimp [P_plus, tkkInvolution] at *
  have H1 : J * ((1 / 2 : ℂ) • (1 + J)) = (1 / 2 : ℂ) • (J + J * J) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Fin.sum_univ_two] <;> ring
  rw [H1, hJ]
  have H2 : (1 / 2 : ℂ) • (J + 1) = (1 / 2 : ℂ) • (1 + J) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply] <;> ring
  rw [H2]

/-- $P_-$ projects onto the -1 eigenspace of the Cartan involution $J$. -/
theorem cartan_involution_eigen_minus (J : M2C) (hJ : tkkInvolution J) :
    J * P_minus J = -P_minus J := by
  dsimp [P_minus, tkkInvolution] at *
  have H1 : J * ((1 / 2 : ℂ) • (1 - J)) = (1 / 2 : ℂ) • (J - J * J) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two] <;> ring
  rw [H1, hJ]
  have H2 : (1 / 2 : ℂ) • (J - 1) = -((1 / 2 : ℂ) • (1 - J)) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply] <;> ring
  rw [H2]

end MobiusCantorTKKClosure

end noncomputable section
