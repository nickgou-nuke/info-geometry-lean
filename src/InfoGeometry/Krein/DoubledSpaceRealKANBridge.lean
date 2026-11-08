import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import InfoGeometry.Dynamics.KanDecomposition
import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

/-!
# Real KAN Decomposition and Doubled Space Matrix Action Bridge

This module formalizes the real Iwasawa KAN chart on $M_2(\mathbb{R})$ and its
faithful intertwining with the doubled-carrier action `ρclock`:

$$KAN_{\mathbb{C}} \xleftarrow{\text{complexification}} KAN_{\mathbb{R}} \xrightarrow{\rho_{\text{clock}}} \operatorname{End}(E \oplus E)$$

## Key Constructions:

1. **Real KAN Components ($M_2(\mathbb{R})$)**:
   - `componentKReal θ = !![cos θ, -sin θ; sin θ, cos θ]`
   - `componentAReal lam = !![exp lam, 0; 0, exp (-lam)]`
   - `componentNReal t = !![1, t; 0, 1]`
   - `kanProductReal θ lam t = componentKReal θ * componentAReal lam * componentNReal t`

2. **Scalar Complexification Theorem**:
   `Matrix.map (kanProductReal θ lam t) Complex.ofReal = kanProduct θ lam t`

3. **Doubled Space Intertwining**:
   - `ρclock (kanProductReal θ lam t) = ρclock(K) ∘ ρclock(A) ∘ ρclock(N)`
   - `ρclockAlg (kanProductReal θ lam t) = ρclockAlg(K) * ρclockAlg(A) * ρclockAlg(N)`

4. **Explicit Sector Actions on Doubled Vectors $(x, \xi) \in E \oplus E$**:
   - Elliptic Rotation: $(x, \xi) \mapsto (\cos \theta \cdot x - \sin \theta \cdot \xi, \sin \theta \cdot x + \cos \theta \cdot \xi)$
   - Hyperbolic Dilation: $(x, \xi) \mapsto (e^\lambda \cdot x, e^{-\lambda} \cdot \xi)$
   - Parabolic Shear: $(x, \xi) \mapsto (x + t \cdot \xi, \xi)$

All proofs are complete with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Krein.DoubledSpaceRealKANBridge

open Matrix
open InfoGeometry.Dynamics.KanDecomposition
open InfoGeometry.Krein
open InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

/-! ## 1. Real KAN Components in $M_2(\mathbb{R})$ -/

/-- Compact elliptic rotation component in $M_2(\mathbb{R})$. -/
def componentKReal (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- Abelian hyperbolic dilation component in $M_2(\mathbb{R})$. -/
def componentAReal (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp lam, 0; 0, Real.exp (-lam)]

/-- Nilpotent parabolic shear component in $M_2(\mathbb{R})$. -/
def componentNReal (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, t; 0, 1]

/-- Real KAN product chart in $M_2(\mathbb{R})$. -/
def kanProductReal (θ lam t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  componentKReal θ * componentAReal lam * componentNReal t

/-- Exact coordinate expansion of the real KAN product matrix. -/
theorem kanProductReal_eq (θ lam t : ℝ) :
    kanProductReal θ lam t =
      !![Real.cos θ * Real.exp lam,
          Real.cos θ * Real.exp lam * t - Real.sin θ * Real.exp (-lam);
         Real.sin θ * Real.exp lam,
          Real.sin θ * Real.exp lam * t + Real.cos θ * Real.exp (-lam)] := by
  dsimp [kanProductReal, componentKReal, componentAReal, componentNReal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

/-! ## 2. Complexification Bridge Theorem -/

/-- 🏆 THEOREM: The complexification of `kanProductReal` exactly coincides with `kanProduct`. -/
theorem kanProduct_complexification (θ lam t : ℝ) :
    Matrix.map (kanProductReal θ lam t) (fun r => (r : ℂ)) =
      kanProduct (θ : ℂ) (lam : ℂ) (t : ℂ) := by
  rw [kanProductReal_eq, kan_product_form]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_exp, Complex.ofReal_neg]

/-! ## 3. Doubled Space Intertwining Theorems -/

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]

/-- 🏆 THEOREM: Multiplicative intertwining of the real KAN flow on the doubled carrier. -/
theorem ρclock_kanProductReal (θ lam t : ℝ) :
    ρclock (E := E) (kanProductReal θ lam t) =
      (ρclock (E := E) (componentKReal θ)).comp
        ((ρclock (E := E) (componentAReal lam)).comp
          (ρclock (E := E) (componentNReal t))) := by
  dsimp [kanProductReal]
  rw [ρclock_mul, ρclock_mul, ContinuousLinearMap.comp_assoc]

/-- 🏆 THEOREM: `AlgHom` level factorization of the real KAN product. -/
theorem ρclockAlg_kanProductReal (θ lam t : ℝ) :
    ρclockAlg (E := E) (kanProductReal θ lam t) =
      ρclockAlg (E := E) (componentKReal θ) *
      ρclockAlg (E := E) (componentAReal lam) *
    ρclockAlg (E := E) (componentNReal t) := by
  have h := map_mul (ρclockAlg (E := E)) (componentKReal θ * componentAReal lam) (componentNReal t)
  have h2 := map_mul (ρclockAlg (E := E)) (componentKReal θ) (componentAReal lam)
  calc ρclockAlg (E := E) (kanProductReal θ lam t)
    _ = ρclockAlg (E := E) (componentKReal θ * componentAReal lam * componentNReal t) := rfl
    _ = ρclockAlg (E := E) (componentKReal θ * componentAReal lam) * ρclockAlg (E := E) (componentNReal t) := h
    _ = ρclockAlg (E := E) (componentKReal θ) * ρclockAlg (E := E) (componentAReal lam) * ρclockAlg (E := E) (componentNReal t) := by rw [h2]

/-! ## 4. Explicit Sector Action Readbacks -/

/-- Elliptic rotation action on doubled vectors. -/
theorem ρclock_componentKReal_apply (θ : ℝ) (x ξ : E) :
    ρclock (E := E) (componentKReal θ) (to_doubled x ξ) =
      to_doubled
        (Real.cos θ • x - Real.sin θ • ξ)
        (Real.sin θ • x + Real.cos θ • ξ) := by
  simp [componentKReal, sub_eq_add_neg, neg_smul]

/-- Hyperbolic dilation action on doubled vectors. -/
theorem ρclock_componentAReal_apply (lam : ℝ) (x ξ : E) :
    ρclock (E := E) (componentAReal lam) (to_doubled x ξ) =
      to_doubled
        (Real.exp lam • x)
        (Real.exp (-lam) • ξ) := by
  simp [componentAReal]

/-- Parabolic shear action on doubled vectors. -/
theorem ρclock_componentNReal_apply (t : ℝ) (x ξ : E) :
    ρclock (E := E) (componentNReal t) (to_doubled x ξ) =
      to_doubled
        (x + t • ξ)
        ξ := by
  simp [componentNReal]

/-- 🏆 THEOREM: Total composite action of `kanProductReal` on doubled vectors. -/
theorem ρclock_kanProductReal_apply (θ lam t : ℝ) (x ξ : E) :
    ρclock (E := E) (kanProductReal θ lam t) (to_doubled x ξ) =
      to_doubled
        ((Real.cos θ * Real.exp lam) • x +
         (Real.cos θ * Real.exp lam * t - Real.sin θ * Real.exp (-lam)) • ξ)
        ((Real.sin θ * Real.exp lam) • x +
         (Real.sin θ * Real.exp lam * t + Real.cos θ * Real.exp (-lam)) • ξ) := by
  simp [kanProductReal_eq]

end InfoGeometry.Krein.DoubledSpaceRealKANBridge
