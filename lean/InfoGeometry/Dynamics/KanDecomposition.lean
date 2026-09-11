import InfoGeometry.Clifford.ModularCftBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.OpSignatureBridge
import InfoGeometry.OptimalTransport.EntropyGradientFlow
import Mathlib.Tactic

noncomputable section

/-!
# KanDecomposition

Finite-dimensional `K A N` coordinate compass for the `2 × 2` complex matrix
envelope used by the LCFT, Bregman, and parabolic-flow bridge modules.

This module does not assert the analytic uniqueness theorem for the global
Iwasawa decomposition.  It records the concrete component matrices and proves
the exact coordinate readouts of their product:

* `K`: elliptic rotation sector, `Op² = -1`;
* `A`: hyperbolic dilation/boost sector, `Op² = 1`;
* `N`: parabolic nilpotent shear sector, `Op² = 0`.
-/

namespace InfoGeometry.Dynamics.KanDecomposition

open Matrix
open InfoGeometry.Clifford.ModularCftBridge
open InfoGeometry.Clifford.OpSignatureBridge
open InfoGeometry.Codes.MajoranaStabilizerThreshold
open InfoGeometry.OptimalTransport.EntropyGradientFlow

/-! ## KAN component labels -/

/-- The three named Iwasawa component lanes. -/
inductive KanComponent where
  | K
  | A
  | N
deriving DecidableEq, Repr

/-- Signature lane selected by a `KAN` component. -/
def KanComponent.signature : KanComponent → OpSignature
  | .K => .elliptic
  | .A => .hyperbolic
  | .N => .parabolic

@[simp] theorem KanComponent.signature_K :
    KanComponent.signature KanComponent.K = OpSignature.elliptic := rfl

@[simp] theorem KanComponent.signature_A :
    KanComponent.signature KanComponent.A = OpSignature.hyperbolic := rfl

@[simp] theorem KanComponent.signature_N :
    KanComponent.signature KanComponent.N = OpSignature.parabolic := rfl

/-- The KAN label selects the corresponding hypercomplex square law. -/
theorem KanComponent.signature_hypercomplex_square (C : KanComponent) :
    toHypercomplexModel C.signature * toHypercomplexModel C.signature =
      opSignatureScalar C.signature • (1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) := by
  simp

@[simp] theorem KanComponent.K_hypercomplex_square :
    toHypercomplexModel (KanComponent.signature KanComponent.K) *
        toHypercomplexModel (KanComponent.signature KanComponent.K) =
      -((1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2)) := by
  exact InfoGeometry.Algebra.HypercomplexTriad.I_sq

@[simp] theorem KanComponent.A_hypercomplex_square :
    toHypercomplexModel (KanComponent.signature KanComponent.A) *
        toHypercomplexModel (KanComponent.signature KanComponent.A) =
      (1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) := by
  exact InfoGeometry.Algebra.HypercomplexTriad.E_sq

@[simp] theorem KanComponent.N_hypercomplex_square :
    toHypercomplexModel (KanComponent.signature KanComponent.N) *
        toHypercomplexModel (KanComponent.signature KanComponent.N) =
      (0 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) := by
  exact InfoGeometry.Algebra.HypercomplexTriad.N_sq

/-! ## Concrete component matrices -/

/--
Compact elliptic component: the rotation block.  Over `ℂ` this is the complex
extension of the usual `SO(2)` chart.
-/
def componentK (θ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.cos θ, -Complex.sin θ; Complex.sin θ, Complex.cos θ]

/-- Abelian hyperbolic component: diagonal dilation / modular-boost block. -/
def componentA (lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp lam, 0; 0, Complex.exp (-lam)]

/--
Nilpotent parabolic component: the already verified Bregman / LCFT unipotent
shear.  This is the `N` lane of the compass.
-/
def componentN (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  bregmanProxStep t

/-- Product chart `K(θ) A(λ) N(t)`. -/
def kanProduct (θ lam t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  componentK θ * componentA lam * componentN t

/-! ## Parabolic `N` sector -/

/-- Coordinate form of the parabolic `N` component. -/
theorem componentN_eq (t : ℂ) :
    componentN t = !![1, t; 0, 1] := by
  simp [componentN, bregmanProxStep, errorFlowStep, lcftParabolicFlowStep_eq]

/-- The `N` component composes by adding its shear parameters. -/
theorem componentN_composition (t₁ t₂ : ℂ) :
    componentN t₁ * componentN t₂ = componentN (t₁ + t₂) := by
  exact bregman_prox_composition t₁ t₂

/-- Powers of the `N` component accumulate shear linearly. -/
theorem componentN_pow (t : ℂ) (n : ℕ) :
    componentN t ^ n = componentN ((n : ℂ) * t) := by
  simpa [componentN, bregmanProxStep] using bregman_prox_induction t n

/-- The unit `N` component is the standard modular `T` generator. -/
theorem componentN_one_eq_modularT :
    componentN 1 = modularT := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [componentN_eq, modularT]

/-! ## Determinant-one KAN sector -/

/-- The elliptic `K` component lies in the determinant-one sector. -/
theorem componentK_det_eq_one (θ : ℂ) :
    (componentK θ).det = 1 := by
  simp [componentK, Matrix.det_fin_two]
  rw [← sq, ← sq, Complex.cos_sq_add_sin_sq]

/-- The hyperbolic `A` component lies in the determinant-one sector. -/
theorem componentA_det_eq_one (lam : ℂ) :
    (componentA lam).det = 1 := by
  simp [componentA, Matrix.det_fin_two, ← Complex.exp_add]

/-- The parabolic `N` component lies in the determinant-one sector. -/
theorem componentN_det_eq_one (t : ℂ) :
    (componentN t).det = 1 := by
  rw [componentN_eq]
  simp [Matrix.det_fin_two]

/-- The concrete `K A N` chart stays inside the determinant-one sector. -/
theorem kanProduct_det_eq_one (θ lam t : ℂ) :
    (kanProduct θ lam t).det = 1 := by
  rw [kanProduct, Matrix.det_mul, Matrix.det_mul]
  simp [componentK_det_eq_one, componentA_det_eq_one, componentN_det_eq_one]

/-! ## KAN product coordinate readout -/

theorem kan_product_00 (θ lam t : ℂ) :
    (kanProduct θ lam t) 0 0 = Complex.cos θ * Complex.exp lam := by
  simp [kanProduct, componentK, componentA, componentN_eq, Matrix.mul_apply]

/--
The lower-left coordinate of `K A N` is independent of the parabolic parameter;
it reads the elliptic/hyperbolic compass sector directly.
-/
theorem kan_product_10 (θ lam t : ℂ) :
    (kanProduct θ lam t) 1 0 = Complex.sin θ * Complex.exp lam := by
  simp [kanProduct, componentK, componentA, componentN_eq, Matrix.mul_apply]

theorem kan_product_01 (θ lam t : ℂ) :
    (kanProduct θ lam t) 0 1 =
      Complex.cos θ * Complex.exp lam * t -
        Complex.sin θ * Complex.exp (-lam) := by
  simp [kanProduct, componentK, componentA, componentN_eq, Matrix.mul_apply]
  ring

theorem kan_product_11 (θ lam t : ℂ) :
    (kanProduct θ lam t) 1 1 =
      Complex.sin θ * Complex.exp lam * t +
        Complex.cos θ * Complex.exp (-lam) := by
  simp [kanProduct, componentK, componentA, componentN_eq, Matrix.mul_apply]

/-- Full coordinate matrix form of the `K A N` chart. -/
theorem kan_product_form (θ lam t : ℂ) :
    kanProduct θ lam t =
      !![Complex.cos θ * Complex.exp lam,
          Complex.cos θ * Complex.exp lam * t -
            Complex.sin θ * Complex.exp (-lam);
        Complex.sin θ * Complex.exp lam,
          Complex.sin θ * Complex.exp lam * t +
            Complex.cos θ * Complex.exp (-lam)] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact kan_product_00 θ lam t
  · exact kan_product_01 θ lam t
  · exact kan_product_10 θ lam t
  · exact kan_product_11 θ lam t

end InfoGeometry.Dynamics.KanDecomposition
