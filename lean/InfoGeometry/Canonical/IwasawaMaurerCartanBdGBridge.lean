import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Canonical.IwasawaMaurerCartanBdG

open Matrix

variable {R : Type*} [CommRing R]

/-! ## 1. Abstract Iwasawa Maurer-Cartan Form Expansion -/

section AbstractRing

variable {A : Type*} [Ring A]

/-- The composite inverse element: (k a n)⁻¹ = n⁻¹ a⁻¹ k⁻¹. -/
theorem iwasawa_inv_mul (k a n k_inv a_inv n_inv : A)
    (hk : k_inv * k = 1) (ha : a_inv * a = 1) (hn : n_inv * n = 1) :
    (n_inv * a_inv * k_inv) * (k * a * n) = 1 := by
  calc (n_inv * a_inv * k_inv) * (k * a * n)
    _ = n_inv * a_inv * (k_inv * k) * a * n := by simp only [mul_assoc]
    _ = n_inv * a_inv * 1 * a * n := by rw [hk]
    _ = n_inv * (a_inv * a) * n := by simp only [mul_assoc, mul_one]
    _ = n_inv * 1 * n := by rw [ha]
    _ = n_inv * n := by rw [mul_one]
    _ = 1 := hn

/-- 🏆 THEOREM: Iwasawa KAN Maurer-Cartan 1-Form Decomposition:
    g⁻¹ dg = n⁻¹ a⁻¹ (k⁻¹ dk) a n + n⁻¹ (a⁻¹ da) n + n⁻¹ dn. -/
theorem iwasawa_maurer_cartan_expansion
    (k a n k_inv a_inv n_inv dk da dn : A)
    (hk : k_inv * k = 1) (ha : a_inv * a = 1) :
    let g_inv := n_inv * a_inv * k_inv
    let dg := dk * a * n + k * da * n + k * a * dn
    g_inv * dg =
      n_inv * a_inv * (k_inv * dk) * a * n +
      n_inv * (a_inv * da) * n +
      n_inv * dn := by
  intro g_inv dg
  dsimp [g_inv, dg]
  have h1 : (n_inv * a_inv * k_inv) * (dk * a * n) = n_inv * a_inv * (k_inv * dk) * a * n := by
    simp only [mul_assoc]
  have h2 : (n_inv * a_inv * k_inv) * (k * da * n) = n_inv * (a_inv * da) * n := by
    calc (n_inv * a_inv * k_inv) * (k * da * n)
      _ = n_inv * a_inv * (k_inv * k) * da * n := by simp only [mul_assoc]
      _ = n_inv * a_inv * 1 * da * n := by rw [hk]
      _ = n_inv * (a_inv * da) * n := by simp only [mul_assoc, mul_one]
  have h3 : (n_inv * a_inv * k_inv) * (k * a * dn) = n_inv * dn := by
    calc (n_inv * a_inv * k_inv) * (k * a * dn)
      _ = n_inv * a_inv * (k_inv * k) * a * dn := by simp only [mul_assoc]
      _ = n_inv * a_inv * 1 * a * dn := by rw [hk]
      _ = n_inv * (a_inv * a) * dn := by simp only [mul_assoc, mul_one]
      _ = n_inv * 1 * dn := by rw [ha]
      _ = n_inv * dn := by rw [mul_one]
  calc (n_inv * a_inv * k_inv) * (dk * a * n + k * da * n + k * a * dn)
    _ = (n_inv * a_inv * k_inv) * (dk * a * n) +
        (n_inv * a_inv * k_inv) * (k * da * n) +
        (n_inv * a_inv * k_inv) * (k * a * dn) := by
        simp only [mul_add]
    _ = n_inv * a_inv * (k_inv * dk) * a * n +
        n_inv * (a_inv * da) * n +
        n_inv * dn := by rw [h1, h2, h3]

end AbstractRing

/-! ## 2. Explicit Matrix Realization of KAN Components & 1-Forms in M₂(R) -/

/-- Krein fundamental symmetry η = diag(1, -1). -/
def etaKrein : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, -1]

/-- Nilpotent horocycle matrix N(x) = !![1, x; 0, 1]. -/
def matN (x : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, x; 0, 1]

/-- Inverse nilpotent horocycle matrix N(-x) = !![1, -x; 0, 1]. -/
def matN_inv (x : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, -x; 0, 1]

/-- Nilpotent differential 1-form dN(dx) = !![0, dx; 0, 0]. -/
def mat_dN (dx : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, dx; 0, 0]

/-- N⁻¹ * N = 1. -/
theorem matN_mul_inv (x : R) : matN_inv x * matN x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matN, matN_inv]

/-- 🏆 THEOREM: The nilpotent Maurer-Cartan form ω_N = N⁻¹ dN = !![0, dx; 0, 0]. -/
theorem matN_maurer_cartan (x dx : R) :
    matN_inv x * mat_dN dx = mat_dN dx := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matN_inv, mat_dN]

/-- 🏆 THEOREM: Nilpotency of the horocycle Maurer-Cartan form: (N⁻¹ dN)² = 0. -/
theorem matN_maurer_cartan_sq (dx : R) :
    mat_dN dx * mat_dN dx = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat_dN]

/-- Trace of the nilpotent Maurer-Cartan form vanishes: Tr(N⁻¹ dN) = 0. -/
theorem matN_maurer_cartan_trace (dx : R) :
    Matrix.trace (mat_dN dx) = 0 := by
  simp [mat_dN, Matrix.trace, Fin.sum_univ_two]

/-- Split torus A(a₁, a₂) = !![a₁, 0; 0, a₂]. -/
def matA (a₁ a₂ : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a₁, 0; 0, a₂]

/-- Inverse split torus. -/
def matA_inv (a₁_inv a₂_inv : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a₁_inv, 0; 0, a₂_inv]

/-- Differential of split torus: dA = !![da₁, 0; 0, da₂]. -/
def mat_dA (da₁ da₂ : R) : Matrix (Fin 2) (Fin 2) R :=
  !![da₁, 0; 0, da₂]

/-- Abelian Maurer-Cartan form ω_A = A⁻¹ dA = !![a₁⁻¹ da₁, 0; 0, a₂⁻¹ da₂]. -/
theorem matA_maurer_cartan (a₁_inv a₂_inv da₁ da₂ : R) :
    matA_inv a₁_inv a₂_inv * mat_dA da₁ da₂ = !![a₁_inv * da₁, 0; 0, a₂_inv * da₂] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matA_inv, mat_dA]

/-- Trace of the abelian Maurer-Cartan form: Tr(A⁻¹ dA) = a₁⁻¹ da₁ + a₂⁻¹ da₂ = d(log det A). -/
theorem matA_maurer_cartan_trace (a₁_inv a₂_inv da₁ da₂ : R) :
    Matrix.trace (matA_inv a₁_inv a₂_inv * mat_dA da₁ da₂) = a₁_inv * da₁ + a₂_inv * da₂ := by
  rw [matA_maurer_cartan]
  simp [Matrix.trace, Fin.sum_univ_two]

/-! ## 3. Krein-Unitary & Euclidean Lie Algebra Conditions -/

/-- Krein-unitary / Lorentz boost generator in Lie algebra u(K): !![0, b; b, 0]. -/
def matBoost_gen (b : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, b; b, 0]

/-- Transpose of the boost generator is symmetric. -/
theorem matBoost_gen_transpose (b : R) : (matBoost_gen b)ᵀ = matBoost_gen b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matBoost_gen]

/-- 🏆 THEOREM: Krein Lie algebra invariance: ω_B satisfies ω_Bᵀ η + η ω_B = 0. -/
theorem matBoost_krein_lie_condition (b : R) :
    (matBoost_gen b)ᵀ * etaKrein + etaKrein * (matBoost_gen b) = 0 := by
  rw [matBoost_gen_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matBoost_gen, etaKrein]

/-- Trace of the boost generator vanishes: Tr(ω_B) = 0. -/
theorem matBoost_gen_trace (b : R) :
    Matrix.trace (matBoost_gen b) = 0 := by
  simp [matBoost_gen, Matrix.trace, Fin.sum_univ_two]

/-- Skew-symmetric compact generator in Lie algebra so(2): !![0, -w; w, 0]. -/
def matK_gen (w : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, -w; w, 0]

/-- Transpose of the compact generator. -/
theorem matK_gen_transpose (w : R) : (matK_gen w)ᵀ = !![0, w; -w, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matK_gen]

/-- 🏆 THEOREM: Euclidean Lie algebra skew-symmetry: ω_Kᵀ + ω_K = 0. -/
theorem matK_euclidean_skew (w : R) :
    (matK_gen w)ᵀ + matK_gen w = 0 := by
  rw [matK_gen_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matK_gen]

/-- Trace of the compact generator vanishes: Tr(ω_K) = 0. -/
theorem matK_gen_trace (w : R) :
    Matrix.trace (matK_gen w) = 0 := by
  simp [matK_gen, Matrix.trace, Fin.sum_univ_two]

/-! ## 4. Krein-Dirac Scalar Overlap & Weak Value Amplification -/

/-- Split bilinear pairing on two coordinates. Over `ℝ` this is the real
Krein pairing; over `ℂ` a Hermitian pairing additionally needs conjugation. -/
def kreinDiracPairing (phi psi : Fin 2 → R) : R :=
  phi 0 * psi 0 - phi 1 * psi 1

/-- The transpose conjugated by the existing fundamental symmetry is adjoint
to the existing split bilinear pairing. -/
theorem kreinDiracPairing_mulVec
    (M : Matrix (Fin 2) (Fin 2) R) (phi psi : Fin 2 → R) :
    kreinDiracPairing (M.mulVec phi) psi =
      kreinDiracPairing phi ((etaKrein * Mᵀ * etaKrein).mulVec psi) := by
  simp [kreinDiracPairing, etaKrein, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul]
  ring

/-- The split pairing separates vectors, including over rings with zero divisors. -/
theorem kreinDiracPairing_separates_right (u v : Fin 2 → R) :
    (∀ phi, kreinDiracPairing phi u = kreinDiracPairing phi v) ↔ u = v := by
  constructor
  · intro h
    have h0 := h ![1, 0]
    have h1 := h ![0, 1]
    simp only [kreinDiracPairing, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul, zero_mul, sub_zero, zero_sub, neg_inj] at h0 h1
    funext i
    fin_cases i
    · exact h0
    · exact h1
  · rintro rfl phi
    rfl

/-- Matrix element of operator Ω under Krein metric: ⟨ϕ, Ω ψ⟩_η. -/
def kreinMatrixElement (phi : Fin 2 → R) (Omega : Matrix (Fin 2) (Fin 2) R) (psi : Fin 2 → R) : R :=
  kreinDiracPairing phi (Matrix.mulVec Omega psi)

/-- 🏆 THEOREM: When states are Krein-orthogonal (⟨ϕ, ψ⟩_η = 0), the weak value denominator vanishes. -/
theorem krein_horizon_orthogonality (phi psi : Fin 2 → R)
    (h_ortho : phi 0 * psi 0 = phi 1 * psi 1) :
    kreinDiracPairing phi psi = 0 := by
  dsimp [kreinDiracPairing]
  rw [h_ortho, sub_self]

/-- In a field, weak value amplification: if ⟨ϕ, Ω ψ⟩_η = μ ≠ 0 and ⟨ϕ, ψ⟩_η = ε ≠ 0,
    then Ω_w * ε = μ. -/
theorem weak_value_scaling {K : Type*} [Field K] (mu eps : K) (h_eps : eps ≠ 0) :
    let weak_val := mu / eps
    weak_val * eps = mu := by
  intro weak_val
  dsimp [weak_val]
  exact div_mul_cancel₀ mu h_eps

/-! ## 5. Bogoliubov-de Gennes Quasiparticle Hamiltonian & Mass Gap -/

/-- Bogoliubov-de Gennes (BdG) Hamiltonian matrix:
    H_BdG(ξ, Δ) = !![ξ, Δ; Δ, -ξ]. -/
def matBdG (xi delta : R) : Matrix (Fin 2) (Fin 2) R :=
  !![xi, delta; delta, -xi]

/-- 🏆 THEOREM: BdG Hamiltonian is traceless: Tr(H_BdG) = 0. -/
theorem matBdG_trace (xi delta : R) :
    Matrix.trace (matBdG xi delta) = 0 := by
  simp [matBdG, Matrix.trace, Fin.sum_univ_two]

/-- 🏆 THEOREM: The BdG square satisfies H_BdG² = (ξ² + Δ²) 1. -/
theorem matBdG_sq (xi delta : R) :
    matBdG xi delta * matBdG xi delta = (xi * xi + delta * delta) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matBdG, smul_eq_mul] <;>
    ring

/-- 🏆 THEOREM: The secular determinant of the BdG Hamiltonian is -(ξ² + Δ²). -/
theorem matBdG_det (xi delta : R) :
    (matBdG xi delta).det = - (xi * xi + delta * delta) := by
  simp [matBdG, Matrix.det_fin_two]
  ring

/-- Pauli velocity operator along z: σ_z = !![1, 0; 0, -1]. -/
def sigmaZ : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, -1]

/-- 🏆 THEOREM: Zitterbewegung Commutator:
    The commutator [σ_z, H_BdG] = 2Δ !![0, 1; -1, 0] is non-zero whenever Δ ≠ 0. -/
theorem zitterbewegung_bdg_commutator (xi delta : R) :
    sigmaZ * matBdG xi delta - matBdG xi delta * sigmaZ =
      (delta + delta) • !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [sigmaZ, matBdG, smul_eq_mul]
  · simp [sigmaZ, matBdG, smul_eq_mul]
  · simp [sigmaZ, matBdG, smul_eq_mul]; ring
  · simp [sigmaZ, matBdG, smul_eq_mul]

/-- In ℝ, the squared quasiparticle energy E² = ξ² + Δ² is bounded below
    by the mass gap square: E² ≥ Δ². -/
theorem bdg_energy_gap_bound (xi delta : ℝ) :
    delta * delta ≤ xi * xi + delta * delta := by
  have h_sq : 0 ≤ xi * xi := mul_self_nonneg xi
  linarith

/-! ## 6. Grand Synthesis Packet -/

structure IwasawaMaurerCartanBdGPacket (R : Type*) [CommRing R] where
  maurer_cartan_nilpotent_sq : ∀ dx : R, mat_dN dx * mat_dN dx = 0
  maurer_cartan_nilpotent_tr : ∀ dx : R, Matrix.trace (mat_dN dx) = 0
  maurer_cartan_abelian_tr : ∀ a1_inv a2_inv da1 da2 : R,
    Matrix.trace (matA_inv a1_inv a2_inv * mat_dA da1 da2) = a1_inv * da1 + a2_inv * da2
  krein_boost_lie_condition : ∀ b : R,
    (matBoost_gen b)ᵀ * etaKrein + etaKrein * (matBoost_gen b) = 0
  euclidean_rot_skew : ∀ w : R,
    (matK_gen w)ᵀ + matK_gen w = 0
  bdg_tr_zero : ∀ xi delta : R, Matrix.trace (matBdG xi delta) = 0
  bdg_sq_gap : ∀ xi delta : R,
    matBdG xi delta * matBdG xi delta = (xi * xi + delta * delta) • (1 : Matrix (Fin 2) (Fin 2) R)
  bdg_det_gap : ∀ xi delta : R,
    (matBdG xi delta).det = - (xi * xi + delta * delta)
  zitterbewegung_comm : ∀ xi delta : R,
    sigmaZ * matBdG xi delta - matBdG xi delta * sigmaZ =
      (delta + delta) • !![0, 1; -1, 0]

def makeIwasawaMaurerCartanBdGPacket (R : Type*) [CommRing R] :
    IwasawaMaurerCartanBdGPacket R where
  maurer_cartan_nilpotent_sq := matN_maurer_cartan_sq
  maurer_cartan_nilpotent_tr := matN_maurer_cartan_trace
  maurer_cartan_abelian_tr := matA_maurer_cartan_trace
  krein_boost_lie_condition := matBoost_krein_lie_condition
  euclidean_rot_skew := matK_euclidean_skew
  bdg_tr_zero := matBdG_trace
  bdg_sq_gap := matBdG_sq
  bdg_det_gap := matBdG_det
  zitterbewegung_comm := zitterbewegung_bdg_commutator

theorem iwasawa_maurer_cartan_bdg_certified :
    Matrix.trace (matBdG (1 : ℝ) 2) = 0 :=
  (makeIwasawaMaurerCartanBdGPacket ℝ).bdg_tr_zero 1 2

end InfoGeometry.Canonical.IwasawaMaurerCartanBdG
