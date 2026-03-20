import InfoGeometry.Quantum.RealMajoranaCategory
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option linter.unusedSectionVars false

namespace InfoGeometry.Quantum.ModularAnomaly

open InfoGeometry.Quantum.RealMajoranaCategory

/--
Topological refinement of the real-Majorana modular shadow.
Requires a normed carrier to support differential calculus on endomorphisms.
-/
structure TopologicalMajoranaShadow
    (X : RealMajoranaCore)
    [NormedAddCommGroup X] [NormedSpace ℝ X] where
  sigma : ℝ → X ≃L[ℝ] X
  sigma_zero : sigma 0 = ContinuousLinearEquiv.refl ℝ X
  sigma_add : ∀ t s, sigma (t + s) = (sigma t).trans (sigma s)
  J_conj_sigma :
    ∀ t x, X.J ((sigma t) x) = (sigma (-t)) (X.J x)

namespace TopologicalMajoranaShadow

variable {X : RealMajoranaCore}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

variable (M : TopologicalMajoranaShadow X)

/-- Continuous Connes cocycle shadow `u_t(U) = U⁻¹ σ_t U σ_{-t}`. -/
noncomputable def modularCocycle (U : X ≃L[ℝ] X) (t : ℝ) : X →L[ℝ] X :=
  (U.symm : X →L[ℝ] X).comp
    (((M.sigma t : X →L[ℝ] X).comp
      ((U : X →L[ℝ] X).comp (M.sigma (-t) : X →L[ℝ] X))))

/-- A symmetry is anomaly-free when the cocycle is identically the identity. -/
def IsAnomalyFree (U : X ≃L[ℝ] X) : Prop :=
  ∀ t : ℝ, modularCocycle M U t = ContinuousLinearMap.id ℝ X

/-- Infinitesimal anomaly generator at `t = 0`. -/
noncomputable def modularAnomalyGenerator (U : X ≃L[ℝ] X) : X →L[ℝ] X :=
  deriv (fun t => modularCocycle M U t) 0

lemma sigma_zero_clm : (M.sigma 0 : X →L[ℝ] X) = ContinuousLinearMap.id ℝ X := by
  simpa using congrArg (fun e : X ≃L[ℝ] X => (e : X →L[ℝ] X)) M.sigma_zero

lemma modularCocycle_zero (U : X ≃L[ℝ] X) :
    modularCocycle M U 0 = ContinuousLinearMap.id ℝ X := by
  ext x
  simp [modularCocycle, sigma_zero_clm (M := M)]

theorem hasDerivAt_modularCocycle_inner
    (U : X ≃L[ℝ] X)
    (σGen : X →L[ℝ] X)
  (hSigma : HasDerivAt (fun t => (M.sigma t : X →L[ℝ] X)) σGen 0)
  (hSigmaNeg : HasDerivAt (fun t => (M.sigma (-t) : X →L[ℝ] X)) (-σGen) 0) :
    HasDerivAt
      (fun t => (M.sigma t : X →L[ℝ] X).comp
        ((U : X →L[ℝ] X).comp (M.sigma (-t) : X →L[ℝ] X)))
      (σGen.comp (U : X →L[ℝ] X) - (U : X →L[ℝ] X).comp σGen)
      0 := by
  have hRight :
      HasDerivAt
        (fun t => (U : X →L[ℝ] X).comp (M.sigma (-t) : X →L[ℝ] X))
        ((U : X →L[ℝ] X).comp (-σGen))
        0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (U : X →L[ℝ] X)).clm_comp hSigmaNeg
  have hComp := hSigma.clm_comp hRight
  simpa [sigma_zero_clm (M := M), sub_eq_add_neg, ContinuousLinearMap.comp_assoc] using hComp

section BridgeTheorem

variable (U : X ≃L[ℝ] X)
variable (σGen : X →L[ℝ] X)

/--
Bridge theorem: the modular anomaly generator equals the commutator shadow.
-/
theorem modularAnomalyGenerator_eq_commutator_shadow :
    (hSigma : HasDerivAt (fun t => (M.sigma t : X →L[ℝ] X)) σGen 0) →
    (hSigmaNeg : HasDerivAt (fun t => (M.sigma (-t) : X →L[ℝ] X)) (-σGen) 0) →
    M.modularAnomalyGenerator U =
      (U.symm : X →L[ℝ] X).comp
        (σGen.comp (U : X →L[ℝ] X) - (U : X →L[ℝ] X).comp σGen) := by
  intro hSigma hSigmaNeg
  unfold modularAnomalyGenerator
  have hInner :
      HasDerivAt
        (fun t => (M.sigma t : X →L[ℝ] X).comp
          ((U : X →L[ℝ] X).comp (M.sigma (-t) : X →L[ℝ] X)))
        (σGen.comp (U : X →L[ℝ] X) - (U : X →L[ℝ] X).comp σGen)
        0 :=
    hasDerivAt_modularCocycle_inner (M := M) U σGen hSigma hSigmaNeg
  have hFull :
      HasDerivAt
        (fun t => modularCocycle M U t)
        ((U.symm : X →L[ℝ] X).comp
          (σGen.comp (U : X →L[ℝ] X) - (U : X →L[ℝ] X).comp σGen))
        0 := by
    simpa [modularCocycle] using
      (hasDerivAt_const (0 : ℝ) (U.symm : X →L[ℝ] X)).clm_comp hInner
  simpa using hFull.deriv

end BridgeTheorem

end TopologicalMajoranaShadow

namespace Cl11Shadow

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Xc" => (cl11DoubledCore E)

noncomputable local instance : NormedAddCommGroup Xc := by
  change NormedAddCommGroup (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

noncomputable local instance : NormedSpace ℝ Xc := by
  change NormedSpace ℝ (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

noncomputable local instance : CompleteSpace Xc := by
  change CompleteSpace (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

noncomputable local instance : CompleteSpace (Xc →L[ℝ] Xc) := by
  infer_instance

noncomputable abbrev IdCLM : Xc →L[ℝ] Xc :=
  ContinuousLinearMap.id ℝ Xc

/-- Hyperbolic shadow flow generated by an involution `epsCLM`. -/
noncomputable def sigmaMap (epsCLM : Xc →L[ℝ] Xc) (t : ℝ) : Xc →L[ℝ] Xc :=
  (((Real.cosh t : ℝ) • (IdCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc)
    + ((Real.sinh t : ℝ) • (epsCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))

lemma hasDerivAt_sigmaMap_zero (epsCLM : Xc →L[ℝ] Xc) :
    HasDerivAt (fun t => sigmaMap epsCLM t) epsCLM 0 := by
  have h1 : HasDerivAt
      (fun t : ℝ => ((Real.cosh t : ℝ) • (IdCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))
      (((Real.sinh 0 : ℝ) • (IdCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))
      0 := by
    simpa using (Real.hasDerivAt_cosh 0).smul_const (IdCLM : Xc →L[ℝ] Xc)
  have h2 : HasDerivAt
      (fun t : ℝ => ((Real.sinh t : ℝ) • (epsCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))
      (((Real.cosh 0 : ℝ) • (epsCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))
      0 := by
    simpa using (Real.hasDerivAt_sinh 0).smul_const (epsCLM : Xc →L[ℝ] Xc)
  simpa [sigmaMap, Real.sinh_zero, Real.cosh_zero, zero_smul, one_smul, zero_add] using h1.add h2

lemma hasDerivAt_sigmaMap_neg_zero (epsCLM : Xc →L[ℝ] Xc) :
    HasDerivAt (fun t => sigmaMap epsCLM (-t)) (-epsCLM) 0 := by
  have heq : (fun t : ℝ => sigmaMap epsCLM (-t))
      = fun t => (Real.cosh t) • IdCLM + (-Real.sinh t) • epsCLM := by
    ext t
    simp [sigmaMap, Real.cosh_neg, Real.sinh_neg, neg_smul]
  rw [heq]
  have h1 : HasDerivAt
      (fun t : ℝ => ((Real.cosh t : ℝ) • (IdCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))
      (((Real.sinh 0 : ℝ) • (IdCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))
      0 := by
    simpa using (Real.hasDerivAt_cosh 0).smul_const (IdCLM : Xc →L[ℝ] Xc)
  have h2 : HasDerivAt (fun t : ℝ => -Real.sinh t) (-1) 0 := by
    simpa using (Real.hasDerivAt_sinh 0).neg
  have h2' : HasDerivAt (fun t : ℝ => (-Real.sinh t) • epsCLM) ((-1 : ℝ) • epsCLM) 0 := by
    simpa using h2.smul_const (epsCLM : Xc →L[ℝ] Xc)
  simpa [Real.sinh_zero, Real.cosh_zero, zero_smul, one_smul, zero_add, neg_smul] using h1.add h2'

/--
Concrete bridge wiring: if a shadow's flow realizes `sigmaMap epsCLM`,
its modular anomaly generator is the expected commutator shadow with `epsCLM`.
-/
theorem modularAnomalyGenerator_eq_concrete_commutator_shadow
    (M : TopologicalMajoranaShadow Xc)
    (epsCLM : Xc →L[ℝ] Xc)
    (hSigmaMap : ∀ t : ℝ, (M.sigma t : Xc →L[ℝ] Xc) = sigmaMap epsCLM t)
    (U : Xc ≃L[ℝ] Xc) :
    M.modularAnomalyGenerator U =
      (U.symm : Xc →L[ℝ] Xc).comp
        (epsCLM.comp (U : Xc →L[ℝ] Xc) - (U : Xc →L[ℝ] Xc).comp epsCLM) := by
  apply TopologicalMajoranaShadow.modularAnomalyGenerator_eq_commutator_shadow
    (M := M) (U := U) (σGen := epsCLM)
  · simpa [hSigmaMap] using hasDerivAt_sigmaMap_zero epsCLM
  · simpa [hSigmaMap] using hasDerivAt_sigmaMap_neg_zero epsCLM

end Cl11Shadow

namespace Lattice

variable {N : ℕ}

/-- Constant scalar block on `Fin N`. -/
def scalarBlock (r : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun _ => r

lemma scalarBlock_eq_smul_one (r : ℝ) :
    scalarBlock (N := N) r = r • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  simpa [scalarBlock] using (Matrix.smul_one_eq_diagonal (m := Fin N) r).symm

noncomputable def constInvertible (r : ℝ) [Invertible r] : Invertible (fun _ : Fin N => r) where
  invOf := fun _ => ⅟r
  invOf_mul_self := by
    funext i
    simp
  mul_invOf_self := by
    funext i
    simp

noncomputable def scalarBlockInvertible (r : ℝ) [Invertible r] :
    Invertible (scalarBlock (N := N) r) := by
  letI := constInvertible (N := N) r
  simpa [scalarBlock] using (Matrix.diagonalInvertible (fun _ : Fin N => r))


/--
The finite-dimensional chiral grading operator ε.
On `Fin N ⊕ Fin N`, it acts as `+1` on the left movers and `-1` on the right movers.
-/
def epsMatrix : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks
    (1 : Matrix (Fin N) (Fin N) ℝ)
    (0 : Matrix (Fin N) (Fin N) ℝ)
    (0 : Matrix (Fin N) (Fin N) ℝ)
    (-(1 : Matrix (Fin N) (Fin N) ℝ))

/--
A lattice Bogoliubov transformation preserves CAR iff it is orthogonal in dimension `2N`.
-/
def IsBogoliubov (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) : Prop :=
  U * Matrix.transpose U = 1 ∧ Matrix.transpose U * U = 1

/-- Finite-dimensional anomaly generator `[ε, U]`. -/
def latticeAnomalyCommutator
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  epsMatrix * U - U * epsMatrix

/-- Block components of `U = [A B; C D]`. -/
def blockA (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.toBlocks₁₁ U

def blockB (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.toBlocks₁₂ U

def blockC (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.toBlocks₂₁ U

def blockD (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.toBlocks₂₂ U

lemma matrix_eq_fromBlocks (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) :
    U = Matrix.fromBlocks (blockA U) (blockB U) (blockC U) (blockD U) := by
  exact Matrix.ext_iff_blocks.mpr ⟨rfl, rfl, rfl, rfl⟩

/--
Block form of the chiral commutator:
`[ε,U] = [0, 2B; -2C, 0]`.
-/
theorem latticeAnomalyCommutator_eq_blocks
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) :
    latticeAnomalyCommutator U =
      Matrix.fromBlocks
        (0 : Matrix (Fin N) (Fin N) ℝ)
        ((2 : ℝ) • blockB U)
        ((-2 : ℝ) • blockC U)
        (0 : Matrix (Fin N) (Fin N) ℝ) := by
  unfold latticeAnomalyCommutator epsMatrix
  rw [matrix_eq_fromBlocks U]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks_multiply, sub_eq_add_neg, two_smul, blockA, blockB, blockC, blockD]

/--
Anomaly-free iff the off-diagonal Bogoliubov blocks vanish.
-/
theorem latticeAnomalyCommutator_eq_zero_iff_blocks_zero
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) :
    latticeAnomalyCommutator U = 0 ↔ blockB U = 0 ∧ blockC U = 0 := by
  constructor
  · intro hAnomaly
    have hComm :
        Matrix.fromBlocks
            (0 : Matrix (Fin N) (Fin N) ℝ)
            ((2 : ℝ) • blockB U)
            ((-2 : ℝ) • blockC U)
            (0 : Matrix (Fin N) (Fin N) ℝ)
          = (0 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) := by
      rw [← latticeAnomalyCommutator_eq_blocks]
      exact hAnomaly
    have hB : blockB U = 0 := by
      ext i j
      have hij := congrArg
        (fun M : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ => M (Sum.inl i) (Sum.inr j))
        hComm
      change (2 : ℝ) * blockB U i j = 0 at hij
      exact (mul_eq_zero.mp hij).resolve_left two_ne_zero
    have hC : blockC U = 0 := by
      ext i j
      have hij := congrArg
        (fun M : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ => M (Sum.inr i) (Sum.inl j))
        hComm
      change (-2 : ℝ) * blockC U i j = 0 at hij
      have h2 : (2 : ℝ) * blockC U i j = 0 := by linarith [hij]
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
    exact ⟨hB, hC⟩
  · rintro ⟨hB, hC⟩
    rw [latticeAnomalyCommutator_eq_blocks, hB, hC]
    simp

/--
`(1,1)` orthogonality block from `Uᵀ U = 1`:
`Aᵀ A + Cᵀ C = 1`.
-/
lemma bogoliubov_ortho_blocks_11
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ)
    (hU : IsBogoliubov U) :
  Matrix.transpose (blockA U) * blockA U + Matrix.transpose (blockC U) * blockC U = 1 := by
  have h11 :
      Matrix.toBlocks₁₁ (Matrix.transpose U * U)
        = Matrix.toBlocks₁₁ (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) :=
    congrArg
      (fun M : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ => Matrix.toBlocks₁₁ M)
      hU.right
  rw [matrix_eq_fromBlocks U] at h11
  have h11' :
      Matrix.transpose (blockA U) * blockA U + Matrix.transpose (blockC U) * blockC U
        = Matrix.toBlocks₁₁ (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) := by
    simpa [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, blockA, blockB, blockC, blockD,
      Matrix.toBlocks_fromBlocks₁₁] using h11
  have hOne :
      Matrix.toBlocks₁₁ (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ)
        = (1 : Matrix (Fin N) (Fin N) ℝ) := by
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  exact h11'.trans hOne

/--
In the anomaly-free case, the `A` block is orthogonal.
-/
theorem anomaly_free_blockA_is_orthogonal
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ)
    (hU : IsBogoliubov U)
    (hAnomaly : latticeAnomalyCommutator U = 0) :
  Matrix.transpose (blockA U) * blockA U = 1 := by
  have h11 := bogoliubov_ortho_blocks_11 U hU
  have hCzero : blockC U = 0 :=
    (latticeAnomalyCommutator_eq_zero_iff_blocks_zero U).mp hAnomaly |>.right
  rw [hCzero] at h11
  simpa [Matrix.transpose_zero, Matrix.zero_mul, add_zero] using h11

/--
Concrete lattice hyperbolic boost shadow on `Fin N ⊕ Fin N`.
This mixes the two chiral sectors with `sinh t` off-diagonal blocks.
-/
noncomputable def sigmaMatrix (t : ℝ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks
    (scalarBlock (N := N) (Real.cosh t))
    (scalarBlock (N := N) (Real.sinh t))
    (scalarBlock (N := N) (Real.sinh t))
    (scalarBlock (N := N) (Real.cosh t))

@[simp] theorem blockA_sigmaMatrix (t : ℝ) :
    blockA (sigmaMatrix (N := N) t) = scalarBlock (N := N) (Real.cosh t) := by
  simp [sigmaMatrix, blockA]

@[simp] theorem blockB_sigmaMatrix (t : ℝ) :
    blockB (sigmaMatrix (N := N) t) = scalarBlock (N := N) (Real.sinh t) := by
  simp [sigmaMatrix, blockB]

@[simp] theorem blockC_sigmaMatrix (t : ℝ) :
    blockC (sigmaMatrix (N := N) t) = scalarBlock (N := N) (Real.sinh t) := by
  simp [sigmaMatrix, blockC]

@[simp] theorem blockD_sigmaMatrix (t : ℝ) :
    blockD (sigmaMatrix (N := N) t) = scalarBlock (N := N) (Real.cosh t) := by
  simp [sigmaMatrix, blockD]

theorem latticeAnomalyCommutator_sigmaMatrix
    (t : ℝ) :
    latticeAnomalyCommutator (sigmaMatrix (N := N) t) =
      Matrix.fromBlocks
        (0 : Matrix (Fin N) (Fin N) ℝ)
        (scalarBlock (N := N) ((2 : ℝ) * Real.sinh t))
        (scalarBlock (N := N) ((-2 : ℝ) * Real.sinh t))
        (0 : Matrix (Fin N) (Fin N) ℝ) := by
  rw [latticeAnomalyCommutator_eq_blocks]
  ext i j <;> cases i <;> cases j <;>
    simp [scalarBlock, two_smul] <;> ring_nf

/-- Finite-dimensional Witten index extracted from the anomaly-free `A` block. -/
def wittenIndex (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) : ℝ :=
  Matrix.det (blockA U)

theorem wittenIndex_sigmaMatrix (t : ℝ) :
    wittenIndex (sigmaMatrix (N := N) t) = Real.cosh t ^ N := by
  simp [wittenIndex, scalarBlock, Matrix.det_diagonal]

theorem wittenIndex_sigmaMatrix_eq_one_iff
    {t : ℝ} (hN : N ≠ 0) :
    wittenIndex (sigmaMatrix (N := N) t) = 1 ↔ t = 0 := by
  constructor
  · intro hW
    by_contra ht
    rw [wittenIndex_sigmaMatrix] at hW
    have hlt : 1 < Real.cosh t := Real.one_lt_cosh.mpr ht
    have hp : 1 < Real.cosh t ^ N := one_lt_pow₀ hlt hN
    exact (lt_irrefl 1) (hW ▸ hp)
  · intro ht
    subst ht
    simp [wittenIndex_sigmaMatrix]

theorem det_sigmaMatrix (t : ℝ) :
    Matrix.det (sigmaMatrix (N := N) t) = 1 := by
  let c : ℝ := Real.cosh t
  let s : ℝ := Real.sinh t
  have hcz : c ≠ 0 := by positivity
  letI : Invertible c := invertibleOfNonzero hcz
  letI : Invertible (scalarBlock (N := N) c) := by
    exact scalarBlockInvertible (N := N) c
  have hSchur :
      scalarBlock (N := N) c
        - scalarBlock (N := N) s * ⅟(scalarBlock (N := N) c) * scalarBlock (N := N) s
        = scalarBlock (N := N) (⅟c) := by
    have hInv : ⅟(scalarBlock (N := N) c) = Matrix.diagonal (fun _ : Fin N => ⅟c) := by
      letI := constInvertible (N := N) c
      letI : Invertible (Matrix.diagonal fun _ : Fin N => c) := by
        simpa [scalarBlock] using
          (show Invertible (scalarBlock (N := N) c) from inferInstance)
      simpa [scalarBlock] using (Matrix.invOf_diagonal_eq (v := fun _ : Fin N => c))
    rw [hInv]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hScalar : c - s * c⁻¹ * s = c⁻¹ := by
        field_simp [hcz]
        nlinarith [Real.cosh_sq_sub_sinh_sq t]
      simp [scalarBlock, hScalar]
    · simp [scalarBlock, hij]
  calc
    Matrix.det (sigmaMatrix (N := N) t)
        = Matrix.det (scalarBlock (N := N) c) *
            Matrix.det
              (scalarBlock (N := N) c
                - scalarBlock (N := N) s * ⅟(scalarBlock (N := N) c) * scalarBlock (N := N) s) := by
          rw [sigmaMatrix, Matrix.det_fromBlocks₂₂]
    _ = Matrix.det (scalarBlock (N := N) c) * Matrix.det (scalarBlock (N := N) (⅟c)) := by
          rw [hSchur]
    _ = c ^ N * (⅟c) ^ N := by
          simp [scalarBlock, Matrix.det_diagonal]
    _ = (c * ⅟c) ^ N := by
          rw [mul_pow]
    _ = 1 := by
          simp [hcz]

noncomputable instance sigmaMatrix_blockD_invertible (t : ℝ) :
    Invertible (blockD (sigmaMatrix (N := N) t)) := by
  let c : ℝ := Real.cosh t
  have hcz : c ≠ 0 := by positivity
  letI : Invertible c := invertibleOfNonzero hcz
  simpa [blockD, sigmaMatrix, c] using (scalarBlockInvertible (N := N) c)

/-- Berezinian-style Schur-complement index around the bottom-right block. -/
noncomputable def berezinianIndex
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ)
    [Invertible (blockD U)] : ℝ :=
  Matrix.det (blockD U) *
    Matrix.det (blockA U - blockB U * ⅟(blockD U) * blockC U)

theorem berezinianIndex_eq_det
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ)
    [Invertible (blockD U)] :
    berezinianIndex (N := N) U = Matrix.det U := by
  calc
    berezinianIndex (N := N) U
      = Matrix.det (blockD U) * Matrix.det (blockA U - blockB U * ⅟(blockD U) * blockC U) := rfl
    _ = Matrix.det (Matrix.fromBlocks (blockA U) (blockB U) (blockC U) (blockD U)) := by
      symm
      exact Matrix.det_fromBlocks₂₂ (A := blockA U) (B := blockB U) (C := blockC U) (D := blockD U)
    _ = Matrix.det U := by
      simpa using congrArg Matrix.det (matrix_eq_fromBlocks U).symm

theorem berezinianIndex_sigmaMatrix (t : ℝ) :
    berezinianIndex (N := N) (sigmaMatrix (N := N) t) = 1 := by
  rw [berezinianIndex_eq_det]
  exact det_sigmaMatrix (N := N) t

/-- Topological parity index of the lattice modular flow. -/
theorem invariant_parity_index (t : ℝ) :
    Matrix.det (sigmaMatrix (N := N) t) = 1 :=
  det_sigmaMatrix (N := N) t

/--
Thermal Berezinian deformation scalar from the Schur complement ratio.
This captures the non-cancelled chiral weighting.
-/
noncomputable def thermalBerezinianEval (t : ℝ) : ℝ :=
  ((Real.cosh t - (Real.sinh t) ^ 2 / Real.cosh t) ^ N) /
    (Real.cosh t ^ N)

/--
Real-power normal form of the thermal Berezinian deformation:
`((cosh - sinh^2/cosh)^N)/(cosh^N) = cosh^(-2N)`.
-/
theorem thermal_berezinian_index (t : ℝ) :
    thermalBerezinianEval (N := N) t = (Real.cosh t) ^ (-2 * (N : ℝ)) := by
  unfold thermalBerezinianEval
  have hpos : 0 < Real.cosh t := Real.cosh_pos t
  have hschur : Real.cosh t - (Real.sinh t) ^ 2 / Real.cosh t = 1 / Real.cosh t := by
    have hcz : Real.cosh t ≠ 0 := ne_of_gt hpos
    field_simp [hcz]
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  rw [hschur]
  rw [← Real.rpow_natCast (1 / Real.cosh t) N, ← Real.rpow_natCast (Real.cosh t) N]
  rw [one_div, Real.inv_rpow hpos.le]
  have hneg : ((Real.cosh t) ^ (N : ℝ))⁻¹ = (Real.cosh t) ^ (-(N : ℝ)) := by
    simpa using (Real.rpow_neg hpos.le (N : ℝ)).symm
  rw [hneg]
  rw [← Real.rpow_sub hpos (-(N : ℝ)) (N : ℝ)]
  congr 1
  ring

end Lattice

end InfoGeometry.Quantum.ModularAnomaly
