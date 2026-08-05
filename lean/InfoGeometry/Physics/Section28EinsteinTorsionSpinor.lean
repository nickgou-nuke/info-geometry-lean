import Mathlib.Tactic

/-!
# Section 28 repaired: finite Einstein--torsion--spinor tensor socket

The source `section28.txt` sketches modified Einstein equations with torsion and
spinor coupling, but it overstates several analytic/geometric facts.  In
particular, the displayed algebraic Riemann-square stress tensor is not, by
itself, the Bach tensor, and a full variational/diffeomorphism proof requires
substantial smooth-manifold hypotheses not supplied there.

This file extracts theorem-safe finite content only.  It works with component
functions on `Fin 4` and proves:

* the standard symmetrized spinor-stress shadow is symmetric if the metric is;
* the algebraic torsion-square stress shadow is symmetric if its contracted
  quadratic part and the metric are symmetric;
* the same for a generic curvature-square algebraic stress shadow;
* the modified Einstein residual is symmetric when all supplied terms are;
* zero residual is definitionally equivalent to the componentwise modified
  Einstein equation.

No continuum variational theorem, Bianchi identity, Bach-tensor identity,
Dirac-equation theorem, or physical Einstein--Cartan field equation is asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.Section28EinsteinTorsionSpinor

/-- Four-dimensional finite index set used for component shadows. -/
abbrev Idx4 := Fin 4

/-- Rank-two tensor shadow. -/
abbrev Tensor2 := Idx4 → Idx4 → ℝ

/-- A rank-two tensor is symmetric in its two finite indices. -/
def Symmetric2 (A : Tensor2) : Prop :=
  ∀ μ ν : Idx4, A μ ν = A ν μ

/-- Symmetrized finite spinor-stress shadow from a raw bilinear `A` and trace scalar. -/
def spinorStressShadow (g A : Tensor2) (trA : ℝ) : Tensor2 :=
  fun μ ν => (1 / 4 : ℝ) * (A μ ν + A ν μ) - (1 / 4 : ℝ) * g μ ν * trA

/-- Algebraic torsion-square stress shadow from a contracted quadratic part `B`. -/
def torsionStressShadow (g B : Tensor2) (torsionNorm alpha2 : ℝ) : Tensor2 :=
  fun μ ν => 2 * alpha2 * (B μ ν - (1 / 4 : ℝ) * g μ ν * torsionNorm)

/--
Algebraic curvature-square stress shadow.

This is deliberately not named `Bach`: it is the displayed algebraic
Riemann-square stress pattern only.
-/
def curvatureSquareStressShadow (g C : Tensor2) (curvNorm alpha1 : ℝ) : Tensor2 :=
  fun μ ν => alpha1 * (2 * C μ ν - (1 / 2 : ℝ) * g μ ν * curvNorm)

/-- The symmetrized spinor-stress shadow is symmetric when the metric is symmetric. -/
theorem spinorStressShadow_symmetric {g A : Tensor2} {trA : ℝ}
    (hg : Symmetric2 g) :
    Symmetric2 (spinorStressShadow g A trA) := by
  intro μ ν
  unfold spinorStressShadow
  rw [hg μ ν]
  ring

/-- The torsion-square stress shadow is symmetric under symmetric inputs. -/
theorem torsionStressShadow_symmetric {g B : Tensor2} {torsionNorm alpha2 : ℝ}
    (hg : Symmetric2 g) (hB : Symmetric2 B) :
    Symmetric2 (torsionStressShadow g B torsionNorm alpha2) := by
  intro μ ν
  unfold torsionStressShadow
  rw [hg μ ν, hB μ ν]

/-- The curvature-square algebraic stress shadow is symmetric under symmetric inputs. -/
theorem curvatureSquareStressShadow_symmetric {g C : Tensor2} {curvNorm alpha1 : ℝ}
    (hg : Symmetric2 g) (hC : Symmetric2 C) :
    Symmetric2 (curvatureSquareStressShadow g C curvNorm alpha1) := by
  intro μ ν
  unfold curvatureSquareStressShadow
  rw [hg μ ν, hC μ ν]

/-- Modified Einstein residual in finite component form. -/
def modifiedEinsteinResidual
    (G g H spinorStress torsionStress : Tensor2) (Lambda alpha1 eightPiG : ℝ) : Tensor2 :=
  fun μ ν =>
    G μ ν + Lambda * g μ ν + alpha1 * H μ ν -
      eightPiG * (spinorStress μ ν + torsionStress μ ν)

/-- Componentwise modified Einstein equation: residual equals zero. -/
def ModifiedEinsteinEquation
    (G g H spinorStress torsionStress : Tensor2) (Lambda alpha1 eightPiG : ℝ) : Prop :=
  ∀ μ ν : Idx4,
    G μ ν + Lambda * g μ ν + alpha1 * H μ ν =
      eightPiG * (spinorStress μ ν + torsionStress μ ν)

/-- Zero residual is equivalent to the componentwise modified Einstein equation. -/
theorem modifiedEinsteinResidual_zero_iff
    (G g H spinorStress torsionStress : Tensor2) (Lambda alpha1 eightPiG : ℝ) :
    (∀ μ ν : Idx4,
      modifiedEinsteinResidual G g H spinorStress torsionStress Lambda alpha1 eightPiG μ ν = 0) ↔
      ModifiedEinsteinEquation G g H spinorStress torsionStress Lambda alpha1 eightPiG := by
  constructor
  · intro h μ ν
    have h0 := h μ ν
    unfold modifiedEinsteinResidual at h0
    have h1 :
        G μ ν + Lambda * g μ ν + alpha1 * H μ ν -
          eightPiG * (spinorStress μ ν + torsionStress μ ν) = 0 := h0
    linarith
  · intro h μ ν
    unfold modifiedEinsteinResidual
    have h0 := h μ ν
    linarith

/-- The finite modified Einstein residual is symmetric when all supplied terms are. -/
theorem modifiedEinsteinResidual_symmetric
    {G g H spinorStress torsionStress : Tensor2} {Lambda alpha1 eightPiG : ℝ}
    (hG : Symmetric2 G) (hg : Symmetric2 g) (hH : Symmetric2 H)
    (hψ : Symmetric2 spinorStress) (hT : Symmetric2 torsionStress) :
    Symmetric2 (modifiedEinsteinResidual G g H spinorStress torsionStress Lambda alpha1 eightPiG) := by
  intro μ ν
  unfold modifiedEinsteinResidual
  rw [hG μ ν, hg μ ν, hH μ ν, hψ μ ν, hT μ ν]

end InfoGeometry.Physics.Section28EinsteinTorsionSpinor

end noncomputable section
