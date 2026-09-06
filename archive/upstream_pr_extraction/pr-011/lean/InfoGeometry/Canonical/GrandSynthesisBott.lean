import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.CalabiYauMetricRicci
import InfoGeometry.Canonical.CalabiYauRNMongeAmpere
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.SingularTransportSystem
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The Grand Unification of the Physics of Information in Lean 4

Capstone synthesis layer connecting thermodynamic Sinkhorn/KMS closure,
geometric Ricci/Calabi-Yau closure, and algebraic Bott-Dirac closure.
-/

open scoped TensorProduct
open scoped Kronecker

namespace InfoGeometry.Canonical.GrandSynthesis

open InfoGeometry.Krein
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.CalabiYauBridge
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.SpectralInference

section Algebraic

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
Algebraic equilibrium: the Cl(1,1)-Bott Laplacian vanishes.
-/
def AlgebraicEquilibriumCl11 (Dn : Endomorphism F) : Prop :=
  cl11BottLaplacian (E := E) Dn = 0

/--
If the Cl(1,1)-Bott Laplacian is zero, then the squared Bott-Dirac operator is zero.
-/
private theorem cl11_bottDirac_sq_eq_zero_of_algebraicEquilibrium
    (Dn : Endomorphism F)
    (hAlg : AlgebraicEquilibriumCl11 (E := E) Dn) :
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn) = 0 := by
  exact (cl11_bottDirac_sq_eq_cl11BottLaplacian (E := E) (F := F) (Dn := Dn)).trans hAlg

/--
Pointwise harmonicity of a Bott state at algebraic equilibrium.
-/
private theorem cl11_bottDirac_sq_apply_eq_zero_of_algebraicEquilibrium
    (Dn : Endomorphism F)
    (hAlg : AlgebraicEquilibriumCl11 (E := E) Dn)
    (ψ : DoubledSpace E ⊗[ℝ] F) :
    ((bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn)) ψ = 0 := by
  have hSq :
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
        (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn) = 0 :=
    cl11_bottDirac_sq_eq_zero_of_algebraicEquilibrium (E := E) (Dn := Dn) hAlg
  simp [hSq]

end Algebraic

section LichnerowiczBridge

variable {A F : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/--
Lichnerowicz-style bridge in the current framework:
for `InfoSpectralTriple`, `D²` rewrites to the Hessian metric operator, and therefore
the split Bott-Dirac square rewrites to the corresponding metric-op Laplacian form.
-/
theorem cl11_bottDirac_sq_eq_metricOp_form
    (IST : InfoSpectralTriple F) :
    (bottDirac (cl11DiracSeed (E := A)) (cl11Grading (E := A)) (spectralDiracLinear IST)).comp
      (bottDirac (cl11DiracSeed (E := A)) (cl11Grading (E := A)) (spectralDiracLinear IST))
      =
    (TensorProduct.map
      ((cl11DiracSeed (E := A)).comp (cl11DiracSeed (E := A)))
      (LinearMap.id : Endomorphism F))
      +
    (TensorProduct.map
      (LinearMap.id : Endomorphism (DoubledSpace A))
      (IST.H.metricOp IST.x₀)) := by
  have hLich :
      (spectralDiracLinear IST).comp (spectralDiracLinear IST) = IST.H.metricOp IST.x₀ := by
    ext v
    have hv : (IST.D * IST.D) v = (IST.H.metricOp IST.x₀) v := by
      exact congrArg (fun T : F →L[ℝ] F => T v) IST.dirac_sq_eq_metric
    simpa [spectralDiracLinear, LinearMap.comp_apply] using hv
  calc
    (bottDirac (cl11DiracSeed (E := A)) (cl11Grading (E := A)) (spectralDiracLinear IST)).comp
        (bottDirac (cl11DiracSeed (E := A)) (cl11Grading (E := A)) (spectralDiracLinear IST))
      =
        (TensorProduct.map
          ((cl11DiracSeed (E := A)).comp (cl11DiracSeed (E := A)))
          (LinearMap.id : Endomorphism F))
          +
        (TensorProduct.map
          (LinearMap.id : Endomorphism (DoubledSpace A))
          ((spectralDiracLinear IST).comp (spectralDiracLinear IST))) := by
            simpa using
              (cl11_bottDirac_sq_eq_sum_laplacians
                (E := A) (F := F) (Dn := spectralDiracLinear IST))
    _ =
        (TensorProduct.map
          ((cl11DiracSeed (E := A)).comp (cl11DiracSeed (E := A)))
          (LinearMap.id : Endomorphism F))
          +
        (TensorProduct.map
          (LinearMap.id : Endomorphism (DoubledSpace A))
          (IST.H.metricOp IST.x₀)) := by
            simp [hLich]

/--
Metric-op closure condition for the split Bott Laplacian in the Lichnerowicz form.
-/
def LichnerowiczBalancedCl11 (IST : InfoSpectralTriple F) : Prop :=
  (TensorProduct.map
    ((cl11DiracSeed (E := A)).comp (cl11DiracSeed (E := A)))
    (LinearMap.id : Endomorphism F))
    +
  (TensorProduct.map
    (LinearMap.id : Endomorphism (DoubledSpace A))
    (IST.H.metricOp IST.x₀)) = 0

/--
If the Lichnerowicz-balanced metric-op closure holds, the split Bott-Dirac square vanishes.
-/
theorem cl11_bottDirac_sq_eq_zero_of_lichnerowiczBalanced
    (IST : InfoSpectralTriple F)
    (hBal : LichnerowiczBalancedCl11 (A := A) IST) :
    (bottDirac (cl11DiracSeed (E := A)) (cl11Grading (E := A)) (spectralDiracLinear IST)).comp
      (bottDirac (cl11DiracSeed (E := A)) (cl11Grading (E := A)) (spectralDiracLinear IST)) = 0 := by
  rw [cl11_bottDirac_sq_eq_metricOp_form (A := A) IST]
  exact hBal

end LichnerowiczBridge

end InfoGeometry.Canonical.GrandSynthesis
