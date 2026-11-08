import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
import InfoGeometry.OperatorAlgebra.CuntzCanonicalGaugeGNSState

/-!
# Cantor-Bernoulli Word-Pair Tomita Shadow

This file records the finite word-pair shadow of the Step 5c/d target.
It defines combinatorial word-pair involutions and scalar modular coefficients;
it does **not** construct a completed GNS Hilbert space, an anti-linear operator
on an `Lp`/GNS quotient, a closed Tomita operator, or a von Neumann modular
automorphism group.  Those analytic/operatorial constructions remain open.

On the finite word-pair index one has:

$$\boxed{S_0 (S_u S_v^\dagger \Omega_\varphi) = S_v S_u^\dagger \Omega_\varphi}$$
$$\boxed{\Delta (S_u S_v^\dagger \Omega_\varphi) = 2^{-(|u| - |v|)} (S_u S_v^\dagger \Omega_\varphi)}$$
The displayed identities below are scalar/index-level identities only; no
operator equality on the concrete canonical gauge GNS carrier is asserted.

## Key Verified Finite Theorems:
1. `tomitaInvolution_sq`: the word-pair swap is involutive.
2. `tomitaInvolution_vacuum`, `_generator`, and `_projector`: the corresponding
   finite labels are fixed or swapped as stated.
3. `modularEigenvalue_pos` and the named eigenvalue lemmas: positivity and
   numerical values of the scalar coefficient attached to a word pair.
4. `modularConjugationFactor_involution`: the scalar scale factors multiply to
   one after swapping the pair.
5. `modularFlowCoeff_norm`, `_generator`, and `_imag_generator`: scalar complex
   phase/weight calculations.  They are not a proof of a Hilbert-space modular
   flow or of a KMS identity.
-/

noncomputable section

open Complex
open scoped BigOperators Topology Real

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliGNSModularTomitaBridge

/-- A word-pair index representing the operator monomial $S_u S_v^\dagger \in \mathcal{A}_0$. -/
structure WordPair where
  u : List Bool
  v : List Bool
deriving DecidableEq, Repr

/-- The vacuum vector corresponds to the empty word pair $(\emptyset, \emptyset)$. -/
def vacuumPair : WordPair := ⟨[], []⟩

/-- The single generator $S_b$ corresponds to $([b], \emptyset)$. -/
def generatorPair (b : Bool) : WordPair := ⟨[b], []⟩

/-- The single adjoint generator $S_b^\dagger$ corresponds to $(\emptyset, [b])$. -/
def adjointGeneratorPair (b : Bool) : WordPair := ⟨[], [b]⟩

/-- The cylinder projector $P_w = S_w S_w^\dagger$ corresponds to $(w, w)$. -/
def projectorPair (w : List Bool) : WordPair := ⟨w, w⟩

/-!
### 1. The Tomita Involution S₀ on Word Pairs
-/

/-- The Tomita anti-linear involution on word basis elements: $S_0(S_u S_v^\dagger \Omega) = S_v S_u^\dagger \Omega$. -/
def tomitaInvolution (p : WordPair) : WordPair :=
  ⟨p.v, p.u⟩

/-- $S_0^2 = I$ on the word basis. -/
@[simp] theorem tomitaInvolution_sq (p : WordPair) :
    tomitaInvolution (tomitaInvolution p) = p := by
  dsimp [tomitaInvolution]

/-- $S_0$ fixes the vacuum vector: $S_0 \Omega = \Omega$. -/
@[simp] theorem tomitaInvolution_vacuum :
    tomitaInvolution vacuumPair = vacuumPair := rfl

/-- $S_0$ maps generators to adjoints: $S_0(S_b) = S_b^\dagger$. -/
theorem tomitaInvolution_generator (b : Bool) :
    tomitaInvolution (generatorPair b) = adjointGeneratorPair b := rfl

/-- $S_0$ fixes all diagonal projection operators: $S_0(P_w) = P_w$. -/
theorem tomitaInvolution_projector (w : List Bool) :
    tomitaInvolution (projectorPair w) = projectorPair w := rfl

/-!
### 2. The Modular Operator Δ
-/

/-- The modular eigenvalue $\Delta(u, v) = 2^{-(|u| - |v|)}$. -/
def modularEigenvalue (p : WordPair) : ℝ :=
  (2 : ℝ) ^ (-((p.u.length : ℝ) - (p.v.length : ℝ)))

/-- The modular eigenvalues are strictly positive. -/
theorem modularEigenvalue_pos (p : WordPair) :
    0 < modularEigenvalue p := by
  dsimp [modularEigenvalue]
  positivity

/-- The modular operator fixes the vacuum: $\Delta \Omega = \Omega$. -/
@[simp] theorem modularEigenvalue_vacuum :
    modularEigenvalue vacuumPair = 1 := by
  dsimp [modularEigenvalue, vacuumPair]
  simp

/-- The modular operator fixes all cylinder projectors: $\Delta(P_w) = P_w$. -/
@[simp] theorem modularEigenvalue_projector (w : List Bool) :
    modularEigenvalue (projectorPair w) = 1 := by
  dsimp [modularEigenvalue, projectorPair]
  simp

/-- On single generators $S_b$: $\Delta(S_b) = 1/2$. -/
theorem modularEigenvalue_generator (b : Bool) :
    modularEigenvalue (generatorPair b) = 1 / 2 := by
  dsimp [modularEigenvalue, generatorPair]
  norm_num

/-- On adjoint generators $S_b^\dagger$: $\Delta(S_b^\dagger) = 2$. -/
theorem modularEigenvalue_adjointGenerator (b : Bool) :
    modularEigenvalue (adjointGeneratorPair b) = 2 := by
  dsimp [modularEigenvalue, adjointGeneratorPair]
  norm_num

/-!
### 3. The Modular Conjugation J = S₀ Δ^{-1/2}
-/

/-- The modular conjugation scale factor $2^{(|u| - |v|)/2}$. -/
def modularConjugationFactor (p : WordPair) : ℝ :=
  (2 : ℝ) ^ (((p.u.length : ℝ) - (p.v.length : ℝ)) / 2)

/-- Involutive property of the modular conjugation scale:
$2^{(|u|-|v|)/2} \cdot 2^{(|v|-|u|)/2} = 1$. -/
theorem modularConjugationFactor_involution (p : WordPair) :
    modularConjugationFactor p * modularConjugationFactor (tomitaInvolution p) = 1 := by
  dsimp [modularConjugationFactor, tomitaInvolution]
  rw [← Real.rpow_add two_pos]
  have hsum : ((p.u.length : ℝ) - (p.v.length : ℝ)) / 2 +
      ((p.v.length : ℝ) - (p.u.length : ℝ)) / 2 = 0 := by ring
  rw [hsum, Real.rpow_zero]

/-!
### 4. Modular Automorphism Flow σ_t^φ
-/

/-- Complex-time modular flow coefficient on word pairs:
$\sigma_z^\varphi(S_u S_v^\dagger) = 2^{-iz(|u| - |v|)} S_u S_v^\dagger$. -/
def modularFlowCoeff (z : ℂ) (p : WordPair) : ℂ :=
  Complex.exp (-(I * z * (((p.u.length : ℝ) : ℂ) - (((p.v.length : ℝ) : ℂ))) * (Real.log 2 : ℂ)))

/-! The coefficient-level flow has the expected additive group law.  This is
an identity on finite word-pair labels, not yet a statement about a completed
Tomita modular automorphism group. -/

@[simp] theorem modularFlowCoeff_zero (p : WordPair) :
    modularFlowCoeff 0 p = 1 := by
  simp [modularFlowCoeff]

theorem modularFlowCoeff_add (z w : ℂ) (p : WordPair) :
    modularFlowCoeff (z + w) p =
      modularFlowCoeff z p * modularFlowCoeff w p := by
  dsimp [modularFlowCoeff]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- For real time $t \in \mathbb{R}$, the flow is isometric / unitary: $\|\sigma_t^\varphi\| = 1$. -/
theorem modularFlowCoeff_norm (t : ℝ) (p : WordPair) :
    ‖modularFlowCoeff (t : ℂ) p‖ = 1 := by
  dsimp [modularFlowCoeff]
  rw [Complex.norm_exp]
  have h_zero : (-(I * (t : ℂ) * (((p.u.length : ℝ) : ℂ) - (((p.v.length : ℝ) : ℂ))) * (Real.log 2 : ℂ))).re = 0 := by
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, neg_re, sub_re, sub_im,
      zero_mul, mul_zero, zero_add, sub_self]
    ring
  change Real.exp (-(I * (t : ℂ) * (((p.u.length : ℝ) : ℂ) - (((p.v.length : ℝ) : ℂ))) * (Real.log 2 : ℂ))).re = 1
  rw [h_zero, Real.exp_zero]

/-- The modular flow scales single generators by $2^{-it}$: $\sigma_t^\varphi(S_b) = 2^{-it} S_b$. -/
theorem modularFlowCoeff_generator (t : ℝ) (b : Bool) :
    modularFlowCoeff (t : ℂ) (generatorPair b) =
      Complex.exp (-(I * (t : ℂ) * (Real.log 2 : ℂ))) := by
  dsimp [modularFlowCoeff, generatorPair, List.length]
  ring_nf

/-- At imaginary time $z = -i$, $\sigma_{-i}^\varphi(S_b) = 1/2 S_b = 2^{-\beta} S_b$ at $\beta = 1$. -/
theorem modularFlowCoeff_imag_generator (b : Bool) :
    modularFlowCoeff (-I) (generatorPair b) = 1 / 2 := by
  have hII : I * -I = (1 : ℂ) := by
    calc I * -I = -(I * I) := by ring
    _ = -(-1) := by rw [Complex.I_mul_I]
    _ = 1 := by ring
  have hlen : ((([b] : List Bool).length : ℝ) : ℂ) - (((([] : List Bool).length : ℝ) : ℂ)) = 1 := by
    show (((1 : ℕ) : ℝ) : ℂ) - (((0 : ℕ) : ℝ) : ℂ) = 1
    norm_num
  have h_exp : -(I * -I * (((([b] : List Bool).length : ℝ) : ℂ) - (((([] : List Bool).length : ℝ) : ℂ))) * (Real.log 2 : ℂ)) =
      Complex.ofReal (- Real.log 2) := by
    rw [hlen, mul_one]
    have h2 : -(I * -I * (Real.log 2 : ℂ)) = - (Real.log 2 : ℂ) := by
      calc -(I * -I * (Real.log 2 : ℂ)) = -((I * -I) * (Real.log 2 : ℂ)) := by ring
      _ = -(1 * (Real.log 2 : ℂ)) := by rw [hII]
      _ = - (Real.log 2 : ℂ) := by ring
    rw [h2]
    exact (Complex.ofReal_neg (Real.log 2)).symm
  change Complex.exp (-(I * -I * (((([b] : List Bool).length : ℝ) : ℂ) - (((([] : List Bool).length : ℝ) : ℂ))) * (Real.log 2 : ℂ))) = 1 / 2
  rw [h_exp]
  rw [← Complex.ofReal_exp (- Real.log 2)]
  rw [Real.exp_neg, Real.exp_log two_pos]
  push_cast
  norm_num

end InfoGeometry.OperatorAlgebra.CantorBernoulliGNSModularTomitaBridge
