import Mathlib
import proofs.Clifford55

noncomputable section

namespace HestenesKreinBdGPrecision

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev NambuBlockR := Matrix (Fin 2) (Fin 2) M2R

/-! ## Real `2 × 2` Krein/Hestenes atom -/

def η : M2R := !![1, 0; 0, -1]

def Jmod : M2R := !![0, 1; 1, 0]

def Kcpx : M2R := !![0, -1; 1, 0]

def kreinInner (u v : Fin 2 → ℝ) : ℝ := u 0 * v 0 - u 1 * v 1

def e1 : M2R := Jmod

def e2 : M2R := Kcpx

def P_R : M2R := !![1, 0; 0, 0]

def P_L : M2R := !![0, 0; 0, 1]

@[simp] theorem η_sq : η * η = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [η, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem Jmod_sq : Jmod * Jmod = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Jmod, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem Kcpx_sq : Kcpx * Kcpx = -(1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Kcpx, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem e1_sq : e1 * e1 = (1 : M2R) := Jmod_sq

@[simp] theorem e2_sq : e2 * e2 = -(1 : M2R) := Kcpx_sq

@[simp] theorem e1_anticomm_e2 : e1 * e2 + e2 * e1 = (0 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e1, e2, Jmod, Kcpx, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem volume_element_eq_eta : e1 * e2 = η := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e1, e2, Jmod, Kcpx, η, Matrix.mul_apply, Fin.sum_univ_two]

/-- Krein adjoint for the real two-sheet metric `η = diag(1,-1)`.
Entrywise this is `η Aᵀ η`. -/
def kreinAdjoint (A : M2R) : M2R := !![A 0 0, -A 1 0; -A 0 1, A 1 1]

@[simp] theorem kreinAdjoint_involutive (A : M2R) :
    kreinAdjoint (kreinAdjoint A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kreinAdjoint]

@[simp] theorem P_R_sq : P_R * P_R = P_R := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P_R, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem P_L_sq : P_L * P_L = P_L := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P_L, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem P_R_mul_P_L : P_R * P_L = (0 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P_R, P_L, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem P_L_mul_P_R : P_L * P_R = (0 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P_R, P_L, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem P_R_add_P_L : P_R + P_L = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P_R, P_L]

@[simp] theorem Jmod_swaps_PL : Jmod * P_L * Jmod = P_R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Jmod, P_L, P_R, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem Jmod_swaps_PR : Jmod * P_R * Jmod = P_L := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Jmod, P_L, P_R, Matrix.mul_apply, Fin.sum_univ_two]

/-- Block-diagonal/R-L preserving part. -/
def dblock (A : M2R) : M2R := !![A 0 0, 0; 0, A 1 1]

/-- Off-block/R-L coupling part. -/
def offblock (A : M2R) : M2R := !![0, A 0 1; A 1 0, 0]

@[simp] theorem dblock_add_offblock (A : M2R) : dblock A + offblock A = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dblock, offblock]

/-- Hestenes/Dirac mass term: real off-sheet modular coupling. -/
def diracMassCoupling (m : ℝ) : M2R := m • Jmod

@[simp] theorem diracMassCoupling_is_offblock (m : ℝ) :
    dblock (diracMassCoupling m) = 0 ∧ offblock (diracMassCoupling m) = diracMassCoupling m := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [dblock, offblock, diracMassCoupling, Jmod]

/-! ## Nambu--Gorkov / BdG degree doubling -/

def Gamma0 : NambuBlockR := !![η, 0; 0, -η]

def JTom : NambuBlockR := !![0, Jmod; Jmod, 0]

def ParticleProjector : NambuBlockR := !![(1 : M2R), 0; 0, 0]

def HoleProjector : NambuBlockR := !![0, 0; 0, (1 : M2R)]

@[simp] theorem Gamma0_sq : Gamma0 * Gamma0 = (1 : NambuBlockR) := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [Gamma0, η, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem JTom_sq : JTom * JTom = (1 : NambuBlockR) := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [JTom, Jmod, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem JTom_swaps_particle_hole :
    JTom * ParticleProjector * JTom = HoleProjector := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [JTom, ParticleProjector, HoleProjector, Jmod, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem JTom_swaps_hole_particle :
    JTom * HoleProjector * JTom = ParticleProjector := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [JTom, ParticleProjector, HoleProjector, Jmod, Matrix.mul_apply, Fin.sum_univ_two]

def h0 (p m : ℝ) : M2R := !![p, m; m, -p]

def singletDelta (Δ : ℝ) : M2R := !![0, Δ; -Δ, 0]

/-- BdG/Nambu block: diagonal Hamiltonian with Krein-adjoint pairing. -/
def bdgBlock (H Δ : M2R) : NambuBlockR := !![H, Δ; kreinAdjoint Δ, -kreinAdjoint H]

def bdgHamiltonian (p m Δ : ℝ) : NambuBlockR := bdgBlock (h0 p m) (singletDelta Δ)

/-- Block Krein adjoint on the Nambu doubled space. -/
def nambuKreinAdjoint (B : NambuBlockR) : NambuBlockR := fun i j => kreinAdjoint (B j i)

@[simp] theorem nambuKreinAdjoint_involutive (B : NambuBlockR) :
    nambuKreinAdjoint (nambuKreinAdjoint B) = B := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> simp [nambuKreinAdjoint]

@[simp] theorem bdgBlock_offdiag_pairing (H Δ : M2R) :
    (bdgBlock H Δ) 0 1 = Δ ∧ (bdgBlock H Δ) 1 0 = kreinAdjoint Δ := by
  simp [bdgBlock]

@[simp] theorem bdgBlock_diagonal_dirac_adjoint (H Δ : M2R) :
    (bdgBlock H Δ) 0 0 = H ∧ (bdgBlock H Δ) 1 1 = -kreinAdjoint H := by
  simp [bdgBlock]

@[simp] theorem h0_decomposes_kinetic_mass (p m : ℝ) :
    dblock (h0 p m) = !![p, 0; 0, -p] ∧ offblock (h0 p m) = !![0, m; m, 0] := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [h0, dblock, offblock]

@[simp] theorem singletDelta_is_offblock (Δ : ℝ) :
    dblock (singletDelta Δ) = 0 ∧ offblock (singletDelta Δ) = singletDelta Δ := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [singletDelta, dblock, offblock]

/-! ## Real CAR atom and finite CCR obstruction -/

def annR : M2R := !![0, 1; 0, 0]

def creR : M2R := !![0, 0; 1, 0]

def antiComm (A B : M2R) : M2R := A * B + B * A

def comm (A B : M2R) : M2R := A * B - B * A

structure CARPair where
  ann : M2R
  cre : M2R
  ann_sq : ann * ann = 0
  cre_sq : cre * cre = 0
  anti : antiComm ann cre = 1

theorem annR_sq : annR * annR = (0 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [annR, Matrix.mul_apply, Fin.sum_univ_two]

theorem creR_sq : creR * creR = (0 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [creR, Matrix.mul_apply, Fin.sum_univ_two]

theorem annR_creR_CAR : antiComm annR creR = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [antiComm, annR, creR, Matrix.mul_apply, Fin.sum_univ_two]

def realCARPair : CARPair where
  ann := annR
  cre := creR
  ann_sq := annR_sq
  cre_sq := creR_sq
  anti := annR_creR_CAR

/-- Finite matrices cannot realize `[q,p]=1`: trace of every commutator vanishes. -/
theorem finite_CCR_trace_obstruction (Q P : M2R) :
    Matrix.trace (comm Q P) = 0 := by
  unfold comm
  rw [Matrix.trace_sub, Matrix.trace_mul_comm Q P]
  simp

/-! ## Supergraded real super-Lie interface -/

inductive Parity where
  | even
  | odd
  deriving DecidableEq, Repr

def parityMul : Parity → Parity → Parity
  | Parity.even, q => q
  | Parity.odd, Parity.even => Parity.odd
  | Parity.odd, Parity.odd => Parity.even

def superBracket (p q : Parity) (A B : M2R) : M2R :=
  match p, q with
  | Parity.odd, Parity.odd => A * B + B * A
  | _, _ => A * B - B * A

@[simp] theorem superBracket_odd_odd (A B : M2R) :
    superBracket Parity.odd Parity.odd A B = antiComm A B := rfl

@[simp] theorem superBracket_even_left (q : Parity) (A B : M2R) :
    superBracket Parity.even q A B = comm A B := by
  cases q <;> rfl

/-- Compact theorem: the requested finite layer is a precise theorem package. -/
theorem hestenes_krein_bdg_supergraded_synthesis (m : ℝ) :
    η * η = (1 : M2R) ∧
    Jmod * Jmod = (1 : M2R) ∧
    Kcpx * Kcpx = -(1 : M2R) ∧
    e1 * e2 = η ∧
    e1 * e2 + e2 * e1 = (0 : M2R) ∧
    P_R + P_L = (1 : M2R) ∧
    Jmod * P_L * Jmod = P_R ∧
    P_R * P_L = (0 : M2R) ∧
    Gamma0 * Gamma0 = (1 : NambuBlockR) ∧
    JTom * JTom = (1 : NambuBlockR) ∧
    dblock (diracMassCoupling m) = 0 ∧
    offblock (diracMassCoupling m) = diracMassCoupling m ∧
    antiComm annR creR = (1 : M2R) ∧
    (∀ Q P : M2R, Matrix.trace (comm Q P) = 0) := by
  exact ⟨η_sq, Jmod_sq, Kcpx_sq, volume_element_eq_eta, e1_anticomm_e2,
    P_R_add_P_L, Jmod_swaps_PL, P_R_mul_P_L, Gamma0_sq, JTom_sq,
    (diracMassCoupling_is_offblock m).1, (diracMassCoupling_is_offblock m).2,
    annR_creR_CAR, finite_CCR_trace_obstruction⟩

/-! ## Weyl CCR completion interface -/

abbrev R2 := Fin 2 → ℝ

/-- Canonical real symplectic form on the two-generator CCR test plane. -/
def canonicalSigma (u v : R2) : ℝ := u 0 * v 1 - u 1 * v 0

@[simp] theorem canonicalSigma_self (u : R2) : canonicalSigma u u = 0 := by
  unfold canonicalSigma
  ring

@[simp] theorem canonicalSigma_skew (u v : R2) :
    canonicalSigma v u = -canonicalSigma u v := by
  unfold canonicalSigma
  ring

/-- Weyl phase for a real symplectic form. -/
def weylPhase {V : Type*} (σ : V → V → ℝ) (u v : V) : ℂ :=
  Complex.exp (-(Complex.I / 2) * (σ u v : ℂ))

/-- Abstract Weyl CCR completion layer.

This is deliberately an interface, not a finite matrix representation. The
finite Hestenes--Krein--BdG core proves that exact CCR cannot live inside
`M₂(ℝ)` by the trace obstruction. A `WeylSystem` records the correct
completion target: bounded Weyl generators over a real symplectic space. -/
structure WeylSystem (V A : Type*) [AddCommGroup V] [One A] [Mul A] [Star A] [SMul ℂ A] where
  sigma : V → V → ℝ
  sigma_skew : ∀ u v : V, sigma v u = -sigma u v
  W : V → A
  W_zero : W 0 = 1
  W_neg : ∀ u : V, W (-u) = star (W u)
  W_mul : ∀ u v : V, W u * W v = weylPhase sigma u v • W (u + v)

namespace WeylSystem

variable {V A : Type*} [AddCommGroup V] [One A] [Mul A] [Star A] [SMul ℂ A]

@[simp] theorem zero_relation (𝓦 : WeylSystem V A) : 𝓦.W 0 = 1 := 𝓦.W_zero

@[simp] theorem adjoint_relation (𝓦 : WeylSystem V A) (u : V) :
    𝓦.W (-u) = star (𝓦.W u) :=
  𝓦.W_neg u

theorem multiplication_relation (𝓦 : WeylSystem V A) (u v : V) :
    𝓦.W u * 𝓦.W v = weylPhase 𝓦.sigma u v • 𝓦.W (u + v) :=
  𝓦.W_mul u v

theorem skew_phase_input (𝓦 : WeylSystem V A) (u v : V) :
    𝓦.sigma v u = -𝓦.sigma u v :=
  𝓦.sigma_skew u v

end WeylSystem

/-- A Weyl completion and the finite CAR core coexist without contradiction:
the finite core supplies exact CAR and an obstruction theorem, while the Weyl
system supplies the abstract CCR completion relations. -/
theorem car_core_weyl_completion_boundary
    {V A : Type*} [AddCommGroup V] [One A] [Mul A] [Star A] [SMul ℂ A]
    (𝓦 : WeylSystem V A) :
    antiComm annR creR = (1 : M2R) ∧
    (∀ Q P : M2R, Matrix.trace (comm Q P) = 0) ∧
    𝓦.W 0 = 1 ∧
    (∀ u v : V, 𝓦.W u * 𝓦.W v = weylPhase 𝓦.sigma u v • 𝓦.W (u + v)) := by
  exact ⟨annR_creR_CAR, finite_CCR_trace_obstruction, 𝓦.W_zero, 𝓦.W_mul⟩

/-- The canonical two-generator CCR test plane has the expected skew form. -/
theorem canonical_R2_symplectic_certificate :
    (∀ u : R2, canonicalSigma u u = 0) ∧
    (∀ u v : R2, canonicalSigma v u = -canonicalSigma u v) := by
  exact ⟨canonicalSigma_self, canonicalSigma_skew⟩

/-! ## Split `(5,5)` supertrace compensation in a `32 = 16 + 16` spinor block -/

abbrev M16R := Matrix (Fin 16) (Fin 16) ℝ
abbrev M32SplitR := Matrix (Fin 2) (Fin 2) M16R

/-- The finite spinor grading block for the balanced `Cl(5,5)` representation:
sixteen positive and sixteen negative spinor states. -/
def Gamma32 : M32SplitR := !![(1 : M16R), 0; 0, -(1 : M16R)]

/-- Block trace for the `16 + 16` split matrix model of `M₃₂(ℝ)`. -/
def blockTrace32 (A : M32SplitR) : ℝ := Matrix.trace (A 0 0) + Matrix.trace (A 1 1)

/-- Supertrace weighted by the balanced `(5,5)` spinor grading. -/
def superTrace32 (A : M32SplitR) : ℝ := blockTrace32 (Gamma32 * A)

@[simp] theorem Gamma32_sq : Gamma32 * Gamma32 = (1 : M32SplitR) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gamma32, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem blockTrace32_one : blockTrace32 (1 : M32SplitR) = 32 := by
  norm_num [blockTrace32, Matrix.trace]

@[simp] theorem blockTrace32_Gamma32 : blockTrace32 Gamma32 = 0 := by
  norm_num [blockTrace32, Gamma32, Matrix.trace]

@[simp] theorem superTrace32_one : superTrace32 (1 : M32SplitR) = 0 := by
  simp [superTrace32]

/-- The balanced split signature compensates the identity trace under the
supertrace while ordinary finite matrix commutators still have zero ordinary
trace. -/
theorem cl55_supertrace_compensates_finite_trace_obstruction :
    superTrace32 (1 : M32SplitR) = 0 ∧
    blockTrace32 (1 : M32SplitR) = 32 ∧
    (∀ Q P : M2R, Matrix.trace (comm Q P) = 0) := by
  exact ⟨superTrace32_one, blockTrace32_one, finite_CCR_trace_obstruction⟩

/-- The existing `Clifford55.R_PT = R_P R_T` spine is the authoritative
`Cl(5,5)` volume element used by this finite split-spinor supertrace model. -/
def Gamma55Volume : Clifford55.Cl55 := Clifford55.R_PT

@[simp] theorem Gamma55Volume_eq_R_PT : Gamma55Volume = Clifford55.R_PT := rfl

/-- Bridge from the compiled `Clifford55.R_PT` volume element to the finite
`32 = 16 + 16` supertrace compensation certificate.  This theorem does not
claim that `Gamma32` is already a proved representation image of `R_PT`; it
records the verified bridge point: the Cl(5,5) volume spine is named, and the
balanced spinor grading has zero supertrace on the identity. -/
theorem cl55_R_PT_supertrace_compensation_bridge :
    Gamma55Volume = Clifford55.R_PT ∧
    Gamma32 * Gamma32 = (1 : M32SplitR) ∧
    superTrace32 (1 : M32SplitR) = 0 ∧
    blockTrace32 (1 : M32SplitR) = 32 ∧
    (∀ Q P : M2R, Matrix.trace (comm Q P) = 0) := by
  exact ⟨rfl, Gamma32_sq, superTrace32_one, blockTrace32_one,
    finite_CCR_trace_obstruction⟩

end HestenesKreinBdGPrecision

end noncomputable section
