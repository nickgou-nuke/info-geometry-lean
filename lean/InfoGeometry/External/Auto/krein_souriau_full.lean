import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import InfoGeometry.Algebra.FiniteSpinAlgebra
open Matrix
open Real

/-! # Finite Krein Matrix Identities and a Gaussian Log-Partition Model

This module proves concrete identities for 2×2 real matrices, an inner-product
pairing, and the Hessian of the scalar model `Z(β) = exp(β²/2)`. The records
`MomentMapData` and `NonequilibriumQuantumThermodynamicsData` only package
fields; they do not construct the corresponding geometric structures.

The affine scalar cocycle below is an explicit model. The repository has
separate owners for observable metriplectic, Onsager, and quantum Cramér–Rao
results; this file does not duplicate those theorem interfaces. No general
Souriau coadjoint cocycle or modular commutant theorem is claimed here.
References to the literature are motivation, not evidence that those theories
have been formalized by these declarations.
-/

noncomputable section

namespace KreinSouriauFull

/-══════════════════════════════════════════════════════════════════════
   BLOCK 1: MODULAR/KREIN OPERATOR ALGEBRA
   ═════════════════════════════════════════════════════════════════════-/

/-- Complex structure J_cpx: J_cpx² = -I (real representation of i) -/
def J_cpx : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

theorem J_cpx_sq_neg_I : J_cpx * J_cpx = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_cpx]

/-- Krein metric η_kr = diag(1, -1): the indefinite inner product -/
def η_kr : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

theorem η_kr_sq_I : η_kr * η_kr = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [η_kr]

/-- J_cpx is η_kr-skew: η_kr·J_cpx·η_kr = -J_cpx -/
theorem J_η_skew : η_kr * J_cpx * η_kr = -J_cpx := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_cpx, η_kr]

/-- Modular conjugation Jm: Jm² = I (the Tomita-Takesaki J) -/
def Jm : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem Jm_sq_I : Jm * Jm = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jm]

/-- Jm exchanges algebra and commutant: Jm·J_cpx·Jm = -J_cpx -/
theorem Jm_commutant : Jm * J_cpx * Jm = -J_cpx := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_cpx, Jm]

/-- The commutant 𝒜' is obtained by conjugating with Jm -/
def commutant (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Jm * A * Jm

/-- Diagonal implementer for the finite-dimensional modular action. -/
def modularImplementer (K t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-Complex.I * (K : ℂ) * (t : ℂ)), 0;
    0, Complex.exp (Complex.I * (K : ℂ) * (t : ℂ))]

/-- The inverse diagonal implementer. -/
def modularImplementerInv (K t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (Complex.I * (K : ℂ) * (t : ℂ)), 0;
    0, Complex.exp (-Complex.I * (K : ℂ) * (t : ℂ))]

/-- Finite-dimensional modular conjugation on the noncommutative matrix
    algebra. The opposite phases make this action nontrivial on off-diagonal
    observables. -/
def modularFlow (K t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :=
  modularImplementer K t * A * modularImplementerInv K t

/-- The implementers are two-sided inverses, so the conjugation preserves
    products. -/
theorem modularFlow_mul (K t : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    modularFlow K t (A * B) = modularFlow K t A * modularFlow K t B := by
  have hleft : modularImplementerInv K t * modularImplementer K t = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [modularImplementer, modularImplementerInv, Matrix.mul_apply,
        ← Complex.exp_add]
  unfold modularFlow
  calc
    modularImplementer K t * (A * B) * modularImplementerInv K t =
        modularImplementer K t * A *
          (modularImplementerInv K t * modularImplementer K t) * B *
            modularImplementerInv K t := by rw [hleft]; simp only [mul_one, mul_assoc]
    _ = (modularImplementer K t * A * modularImplementerInv K t) *
          (modularImplementer K t * B * modularImplementerInv K t) := by
            simp only [mul_assoc]

/-- The flow acts on an off-diagonal matrix unit by a relative phase, so the
    matrix model retains the noncommutative action that scalar conjugation
    erased. -/
theorem modularFlow_upperMatrixUnit (K t : ℝ) :
    modularFlow K t (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) =
      !![0, Complex.exp (-2 * Complex.I * (K : ℂ) * (t : ℂ)); 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [modularFlow, modularImplementer, modularImplementerInv,
    Matrix.mul_apply, ← Complex.exp_add]
  all_goals ring_nf

/-- In this concrete real model, `Jm` is self-adjoint and involutive, as a
    Krein fundamental symmetry must be. -/
theorem fundamental_symmetry : Jm.transpose = Jm ∧
    Jm * Jm = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp [Jm], Jm_sq_I⟩

/-══════════════════════════════════════════════════════════════════════
   BLOCK 2: SOURIAU LIE GROUP THERMODYNAMICS
   ═════════════════════════════════════════════════════════════════════-/

/-- Bare moment-map-shaped data only. A genuine moment map needs a dual target
    and compatibility with a specified group action and symplectic form. -/
structure MomentMapData (M 𝔤 : Type) where
  value : M → 𝔤

/-- Generalized inverse temperature β ∈ 𝔤 as a thermodynamic covector -/
structure ThermodynamicCovector (𝔤 : Type) [AddCommGroup 𝔤] where
  β : 𝔤   -- inverse temperature (component)
  μ : 𝔤   -- chemical potential (component)
  ω : 𝔤   -- angular velocity / rotation (component)

/-- A Gaussian cumulant-generating model `Z(β) = exp(β²/2)`. This definition
    alone does not construct an integral or a Souriau partition function. -/
def partitionFn (β : ℝ) : ℝ := Real.exp (β^2/2)

/-- Log partition determines the cumulant generating function -/
theorem log_partition_eq (β : ℝ) : Real.log (partitionFn β) = β^2/2 := by
  dsimp [partitionFn]
  rw [Real.log_exp]

/- The general Souriau coadjoint cocycle remains open here: this scalar carrier
   has no coadjoint action or moment-map equivariance data. The following is a
   genuine cocycle for one explicit affine representation of the additive
   group `ℝ`. -/

/-- The scalar representation of the additive group `ℝ` by multiplication
    with `exp g`. -/
def exponentialScalarAction (g x : ℝ) : ℝ := Real.exp g * x

/-- The affine one-cocycle `g ↦ exp(g) - 1` for `exponentialScalarAction`. -/
def exponentialAffineCocycle (g : ℝ) : ℝ := Real.exp g - 1

/-- Cocycle law for `g ↦ exp(g) - 1` under the exponential scalar action. -/
theorem exponentialAffineCocycle_add (g h : ℝ) :
    exponentialAffineCocycle (g + h) =
      exponentialAffineCocycle g +
        exponentialScalarAction g (exponentialAffineCocycle h) := by
  rw [exponentialAffineCocycle, exponentialAffineCocycle,
    exponentialAffineCocycle, exponentialScalarAction, Real.exp_add]
  ring

/-- The Gibbs state as a function of the thermodynamic covector -/
def gibbsState (J_M β : ℝ) : ℝ := Real.exp (-J_M * β) / partitionFn β

/-- Optional dual-pairing realization used in Souriau: 
    with an inner product on `𝔤`, we can identify a covector direction
    with a vector `β : 𝔤` and evaluate it by
    `⟨β, J_M(x)⟩`.
-/
def souriauDualPairing {𝔤 : Type} [NormedAddCommGroup 𝔤] [InnerProductSpace ℝ 𝔤] :
    𝔤 → 𝔤 → ℝ :=
  fun β J => ((innerSL ℝ) β) J

def souriauPairingEnergy {M 𝔤 : Type} [NormedAddCommGroup 𝔤]
    [InnerProductSpace ℝ 𝔤] (J_M : M → 𝔤) (β : 𝔤) (x : M) : ℝ :=
  souriauDualPairing (𝔤 := 𝔤) β (J_M x)

/-- The Souriau pairing in this inner-product model obeys the norm bound
    supplied by Cauchy–Schwarz. This does not assert existence of a moment
    map or a group action. -/
theorem souriauPairingEnergy_norm_bound {M 𝔤 : Type} [NormedAddCommGroup 𝔤]
    [InnerProductSpace ℝ 𝔤] (J_M : M → 𝔤) (β : 𝔤) (x : M) :
    |souriauPairingEnergy (J_M := J_M) β x| ≤ ‖β‖ * ‖J_M x‖ := by
  simpa [souriauPairingEnergy, souriauDualPairing, innerSL_apply_apply,
    Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) β (J_M x))

/-══════════════════════════════════════════════════════════════════════
   BLOCK 3: INFORMATION GEOMETRY AND METRIPLECTIC DYNAMICS
   ═════════════════════════════════════════════════════════════════════-/

/-- The one-dimensional Hessian of the chosen log-partition model. -/
noncomputable def fisherMetric (β : ℝ) : ℝ :=
  deriv (fun b : ℝ => deriv (fun x : ℝ => Real.log (partitionFn x)) b) β

/-- In this Gaussian model the Hessian, hence Fisher information, is one. -/
theorem fisherMetric_eq_one (β : ℝ) : fisherMetric β = 1 := by
  have hlog : (fun x : ℝ => Real.log (partitionFn x)) =
      (fun x => x ^ 2 / 2) := by
    funext x
    exact log_partition_eq x
  have hfirst : (fun b : ℝ => deriv (fun x : ℝ => Real.log (partitionFn x)) b) =
      (fun b => b) := by
    funext b
    rw [hlog]
    have hrewrite : (fun x : ℝ => x ^ 2 / 2) =
        (fun x => (1 / 2 : ℝ) * x ^ 2) := by
      funext x
      ring
    rw [hrewrite]
    rw [deriv_const_mul_field, deriv_pow_field]
    simp only [Nat.reduceSub, pow_one]
    calc (1 / 2 : ℝ) * (2 * b) = ((1 / 2 : ℝ) * 2) * b := by ring
      _ = 1 * b := by rw [show (1 / 2 : ℝ) * 2 = 1 by norm_num]
      _ = b := one_mul b
  rw [fisherMetric, hfirst]
  simp

/-══════════════════════════════════════════════════════════════════════
   THE UNIFIED FORMULA
   ═════════════════════════════════════════════════════════════════════-/

/-- A container for the component data used in a nonequilibrium model. It
    imposes no action, symplectic, commutant, or bracket compatibility laws. -/
structure NonequilibriumQuantumThermodynamicsData where
  -- Block 1: Modular/Krein
  A : Type                    -- 𝒜: visible algebra
  J_op : A → A                -- J: complex structure
  A' : Type                   -- 𝒜': commutant (ghost algebra)
  K_mod : ℝ                   -- K: modular Hamiltonian
  
  -- Block 2: Souriau
  G : Type                    -- G: Lie symmetry group
  M : Type                    -- M: symplectic manifold
  β_vec : ThermodynamicCovector ℝ  -- β: thermodynamic covector
  
  -- Block 3: Fisher-metriplectic
  g_F : ℝ → ℝ                -- g_F: Fisher metric
  ω_symp : Type               -- ω: symplectic form
  poisson : (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ  -- {,}: Poisson bracket
  metric : (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ   -- (,): metric bracket

#check J_cpx_sq_neg_I
#check η_kr_sq_I
#check J_η_skew
#check Jm_sq_I
#check Jm_commutant
#check commutant
#check modularFlow
#check MomentMapData
#check ThermodynamicCovector
#check partitionFn
#check log_partition_eq
#check gibbsState
#check fisherMetric
#check fisherMetric_eq_one
#check NonequilibriumQuantumThermodynamicsData

end KreinSouriauFull
