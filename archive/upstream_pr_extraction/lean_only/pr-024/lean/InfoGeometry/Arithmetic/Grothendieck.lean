import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Analysis.BregmanAnalyticBound
import InfoGeometry.Analysis.RotorCocycleBregmanBridge
import DAG.AffineProjectiveClosure
import DAG.ChiralDiracAnticommutation

namespace InfoGeometry.Arithmetic.Grothendieck

open InfoGeometry.Arithmetic
open InfoGeometry.Analysis.BregmanAnalyticBound
open InfoGeometry.Analysis.RotorCocycleBregmanBridge

/-- The lower Dikin envelope is nonnegative on nonnegative radii. -/
theorem dikinOmega_nonneg_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ dikinOmega t :=
  InfoGeometry.Analysis.BregmanAnalyticBound.dikinOmega_nonneg_of_nonneg ht

/-- The upper Dikin envelope is nonnegative on its natural domain. -/
theorem dikinOmegaStar_nonneg_of_lt_one {t : ℝ} (ht : t < 1) :
    0 ≤ dikinOmegaStar t :=
  InfoGeometry.Analysis.BregmanAnalyticBound.dikinOmegaStar_nonneg_of_lt_one ht

/-- Prime multiplication flips the arithmetic parity. -/
theorem liouville_prime_mul (p n : ℕ+) (hp : Nat.Prime p.val) :
    BostConnesSystem.liouville (p * n) = -BostConnesSystem.liouville n :=
  BostConnesSystem.liouville_prime_mul p n hp n.property

/-- The finite Dirac operator anticommutes with the finite chiral grading. -/
theorem dirac_anticommutes_gamma {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℝ)
    (B2 : Matrix (Fin n1) (Fin n2) ℝ) :
    DAG.ChiralDiracAnticommutation.chiralGamma *
        DAG.ChiralDiracAnticommutation.diracOp B1 B2 +
      DAG.ChiralDiracAnticommutation.diracOp B1 B2 *
        DAG.ChiralDiracAnticommutation.chiralGamma = 0 :=
  DAG.ChiralDiracAnticommutation.dirac_anticommutes_gamma B1 B2

theorem grothendieck_finite_inputs {n0 n1 n2 : ℕ}
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (p q : ℕ+) (hp : Nat.Prime p.val)
    (B1 : Matrix (Fin n0) (Fin n1) ℝ)
    (B2 : Matrix (Fin n1) (Fin n2) ℝ) :
    0 ≤ dikinOmega t ∧
      0 ≤ dikinOmegaStar t ∧
      BostConnesSystem.liouville (p * q) = -BostConnesSystem.liouville q ∧
      (DAG.ChiralDiracAnticommutation.chiralGamma *
          DAG.ChiralDiracAnticommutation.diracOp B1 B2 +
        DAG.ChiralDiracAnticommutation.diracOp B1 B2 *
          DAG.ChiralDiracAnticommutation.chiralGamma = 0) := by
  constructor
  · exact dikinOmega_nonneg_of_nonneg ht0
  constructor
  · exact dikinOmegaStar_nonneg_of_lt_one ht1
  constructor
  · exact liouville_prime_mul p q hp
  · exact dirac_anticommutes_gamma B1 B2

def grothendieck_debt : String :=
  DAG.AffineProjectiveClosure.affine_projective_closure_debt

end InfoGeometry.Arithmetic.Grothendieck
